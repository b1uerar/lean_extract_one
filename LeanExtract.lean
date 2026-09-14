import Lean

open Lean Lean.Elab

namespace LeanExtract

structure Request where
  mode : String
  input : String
  moduleName : String
  theoremName : String
  result : String
  candidate : String := ""
  plan : String := ""
  logicalFile : String := ""
  setup : Option ModuleSetup := none
  deriving FromJson

structure CommandData where
  stx : Syntax
  env : Environment
  refs : NameSet := {}
  names : Array Name := #[]
  context : Array Nat := #[]
  scopes : Array Nat := #[]
  attributeTargets : NameSet := {}

instance [Inhabited Environment] : Inhabited CommandData :=
  ⟨{ stx := default, env := default }⟩

structure Analysis where
  source : String
  env : Environment
  commands : Array CommandData
  owners : Std.HashMap Name Nat
  scopeEnds : Std.HashMap Nat (Array Nat)

def getJson (j : Json) (key : String) : IO Json :=
  IO.ofExcept (j.getObjVal? key)

def getField [FromJson a] (j : Json) (key : String) : IO a :=
  IO.ofExcept (j.getObjValAs? a key)

def readJson (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

partial def syntaxRefs (env : Environment) (stx : Syntax) (refs : NameSet) : NameSet := Id.run do
  match stx with
  | .ident _ _ _ resolved =>
    let mut refs := refs
    for r in resolved do
      if let .decl n _ := r then refs := refs.insert n
    return refs
  | .node _ kind args =>
    let mut refs := refs.insert kind
    -- Syntax and macro registrations are dependencies even when expansion erases them.
    for entry in macroAttribute.getEntries env kind do
      refs := refs.insert entry.declName
    for (_, category) in (Parser.parserExtension.getState env).categories do
      if category.kinds.contains kind then refs := refs.insert category.declName
    return args.foldl (fun acc s => syntaxRefs env s acc) refs
  | _ => return refs

partial def treeRefs (env : Environment) (mctx : MetavarContext)
    (tree : InfoTree) (refs : NameSet) : NameSet := Id.run do
  match tree with
  | .context (.commandCtx ctx) t => return treeRefs ctx.env ctx.mctx t refs
  | .context _ t => return treeRefs env mctx t refs
  | .hole _ => return refs
  | .node info children =>
    let mut refs := refs
    match info with
    | .ofTermInfo i =>
      refs := refs.insert i.elaborator ++ (instantiateExprMVarsImp mctx i.expr).2.getUsedConstantsAsSet
    | .ofCommandInfo i => refs := refs.insert i.elaborator
    | .ofTacticInfo i =>
      refs := refs.insert i.elaborator
      -- Intermediate tactic assignments include dependencies erased from the final proof.
      for goal in i.goalsBefore do
        refs := refs ++ (instantiateExprMVarsImp i.mctxAfter (.mvar goal)).2.getUsedConstantsAsSet
    | .ofFieldInfo i => refs := refs.insert i.projName ++ i.val.getUsedConstantsAsSet
    | .ofMacroExpansionInfo i =>
      refs := syntaxRefs env i.output (syntaxRefs env i.stx refs)
    | .ofOptionInfo i => refs := refs.insert i.declName
    | _ => pure ()
    for t in children do refs := treeRefs env mctx t refs
    return refs

def isScopeCommand (stx : Syntax) : Bool :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end].contains stx.getKind

def isContextCommand (stx : Syntax) : Bool :=
  [``Parser.Command.variable, ``Parser.Command.universe, ``Parser.Command.open,
    ``Parser.Command.set_option, ``Parser.Command.include, ``Parser.Command.omit,
    ``Parser.Command.export].contains stx.getKind

def isDiagnostic (stx : Syntax) : Bool :=
  [``Parser.Command.check, ``Parser.Command.check_failure, ``Parser.Command.print,
    ``Parser.Command.printAxioms, ``Parser.Command.printEqns, ``Parser.Command.printSig,
    ``Parser.Command.synth, ``Parser.Command.version, ``Parser.Command.moduleDoc].contains stx.getKind

def isAttributeCommand (stx : Syntax) : Bool :=
  [``Parser.Command.attribute, ``Parser.Command.grindPattern, ``Parser.Command.export].contains stx.getKind

partial def hasKind (stx : Syntax) (kind : Name) : Bool :=
  stx.getKind == kind || stx.getArgs.any (hasKind · kind)

def hasUntrackedEffect (cmd : CommandData) : Bool :=
  cmd.stx.getKind == ``Parser.Command.initialize ||
  hasKind cmd.stx ``Parser.Command.eraseAttr ||
  (cmd.names.isEmpty && !isScopeCommand cmd.stx && !isContextCommand cmd.stx &&
    !isAttributeCommand cmd.stx && !isDiagnostic cmd.stx)

def attributeTargets (stx : Syntax) (state : Command.State) : NameSet := Id.run do
  let ids := if stx.getKind == ``Parser.Command.attribute then stx[4].getArgs
    else if stx.getKind == ``Parser.Command.export then stx[3].getArgs
    else if stx.getKind == ``Parser.Command.grindPattern then #[stx[2]] else #[]
  let scope := state.scopes.head!
  let mut refs := {}
  for id in ids do
    for (name, _) in ResolveName.resolveGlobalName state.env scope.opts scope.currNamespace scope.openDecls id.getId do
      refs := refs.insert name
  return refs

def referenceFormat (ctx : PPContext) (expr : Expr) : FormatWithInfos :=
  { fmt := .nil, infos := ({} : PrettyPrinter.InfoPerPos).insert 0 (.ofTermInfo {
      elaborator := .anonymous, stx := .missing, lctx := ctx.lctx,
      expectedType? := none, expr := (instantiateExprMVarsImp ctx.mctx expr).2 }) }

-- Decode structured trace payloads without parsing printed names or invoking delaborators.
def referenceContext (ctx : MessageDataContext) : PPContext :=
  { env := ppExt.setState ctx.env {
      ppExprWithInfos := fun ctx e => pure (referenceFormat ctx e)
      ppConstNameWithInfos := fun ctx n => pure (referenceFormat ctx (.const n []))
      ppTerm := fun _ _ => pure .nil
      ppLevel := fun _ _ => pure .nil
      ppGoal := fun _ _ => pure .nil }
    mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts.setBool `pp.raw false }

partial def messageRefs (msg : MessageData) (ctx : Option PPContext := none)
    (refs : NameSet := {}) : BaseIO NameSet := do
  match msg with
  | .withContext ctx msg => messageRefs msg (some (referenceContext ctx)) refs
  | .withNamingContext _ msg | .nest _ msg | .group msg | .tagged _ msg
  | .ofWidget _ msg => messageRefs msg ctx refs
  | .compose left right => messageRefs right ctx (← messageRefs left ctx refs)
  | .trace _ msg children =>
    let mut refs ← messageRefs msg ctx refs
    for child in children do refs ← messageRefs child ctx refs
    return refs
  | .ofLazy f _ =>
    let some msg := (← f ctx).get? MessageData | return refs
    messageRefs msg ctx refs
  | .ofFormatWithInfos fmt =>
    let mut refs := refs
    for (_, info) in fmt.infos do
      if let .ofTermInfo i := info then refs := refs ++ i.expr.getUsedConstantsAsSet
    return refs
  | _ => return refs

def reportMessages (messages : MessageLog) : IO Unit := do
  for msg in messages.toList do
    if msg.data.hasTag (· == `trace) then continue
    IO.eprintln (← msg.toString)

unsafe def analyze (req : Request) : IO Analysis := do
  let source ← IO.FS.readFile req.input
  let inputCtx := Parser.mkInputContext source (if req.logicalFile.isEmpty then req.input else req.logicalFile)
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let setup := req.setup.getD { name := req.moduleName.toName }
  let opts := (setup.options.toOptions).setBool `Elab.async false
  let opts := if req.mode == "extract" then opts.setBool `trace.Meta.Tactic.simp.rewrite true else opts
  for lib in setup.dynlibs do Lean.loadDynlib lib
  Lean.enableInitializersExecution
  -- Always derive imports from the source, including during verification.
  let (env, messages) ← processHeaderCore (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (HeaderSyntax.isModule header || setup.isModule) opts messages inputCtx
    (plugins := setup.plugins) (mainModule := req.moduleName.toName)
    (arts := setup.importArts)
  if messages.hasErrors then
    reportMessages messages
    throw (IO.userError "input header failed Lean checking")
  let _ : Inhabited Environment := ⟨env⟩
  let task ← Language.Lean.processCommands inputCtx parserState (Command.mkState env messages opts)
  let initial := task.get
  let snapshots := Language.toSnapshotTree initial
  let mut messages := messages
  for snapshot in snapshots.getAll do
    messages := messages ++ snapshot.diagnostics.msgLog
  reportMessages messages
  if messages.hasErrors then throw (IO.userError "file failed Lean checking")
  let mut snap := initial
  let mut commands := #[]
  let mut scopeOwners : Array Nat := #[]
  let mut contexts : Array (Array Nat) := #[#[]]
  let mut scopeEnds : Std.HashMap Nat (Array Nat) := {}
  repeat
    let state := snap.elabSnap.resultSnap.get.cmdState
    if !Parser.isTerminalCommand snap.stx then
      let refs := match snap.elabSnap.infoTreeSnap.get.infoTree? with
        | some tree => treeRefs state.env {} tree (syntaxRefs state.env snap.stx {})
        | none => syntaxRefs state.env snap.stx {}
      let i := commands.size
      let attrTargets := attributeTargets snap.stx state
      commands := commands.push {
        stx := snap.stx, env := state.env, refs := refs ++ attrTargets,
        context := contexts.flatten, scopes := scopeOwners, attributeTargets := attrTargets : CommandData }
      -- Scope depths come from execution, including dotted namespaces and custom commands.
      while contexts.size < state.scopes.length do
        contexts := contexts.push #[]
        scopeOwners := scopeOwners.push i
      while contexts.size > state.scopes.length do
        let owner := scopeOwners.back!
        scopeEnds := scopeEnds.insert owner ((scopeEnds[owner]?).getD #[] |>.push i)
        scopeOwners := scopeOwners.pop
        contexts := contexts.pop
      if isContextCommand snap.stx then
        contexts := contexts.modify (contexts.size - 1) (·.push i)
    if let some next := snap.nextCmdSnap? then snap := next.task.get else break
  for msg in messages.toList do
    if !msg.data.hasTag (· == `trace) then continue
    let pos := inputCtx.fileMap.ofPosition msg.pos
    let mut lo := 0
    let mut hi := commands.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if commands[mid]!.stx.getPos?.getD 0 <= pos then lo := mid + 1 else hi := mid
    if lo > 0 then
      let refs ← messageRefs msg.data
      commands := commands.modify (lo - 1) fun cmd => { cmd with refs := cmd.refs ++ refs }
  let finalEnv := snap.elabSnap.resultSnap.get.cmdState.env
  let mut owners : Std.HashMap Name Nat := {}
  -- The persistent map contains this file's constants; imported constants live in map1.
  -- Binary search snapshots to attribute generated constants without name heuristics.
  for (n, _) in finalEnv.constants.map₂.toList do
    if env.contains n then continue
    let mut lo := 0
    let mut hi := commands.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if commands[mid]!.env.contains n then hi := mid else lo := mid + 1
    if lo == commands.size then
      throw (IO.userError s!"cannot attribute local declaration {n} to source")
    owners := owners.insert n lo
    commands := commands.modify lo fun c => { c with names := c.names.push n }
  return { source, env := finalEnv, commands, owners, scopeEnds }

def resolveTarget (a : Analysis) (query : String) : IO Name := do
  let candidates := a.owners.toArray.map (·.1) |>.filter fun n =>
    match a.env.find? n with
    | some (.thmInfo _) => true
    | _ => false
  let exact := candidates.filter fun n =>
    n.toString == query || (privateToUserName n).toString == query
  let found := if !exact.isEmpty then exact else candidates.filter fun n =>
    match privateToUserName n with
    | .str _ leaf => leaf == query || (Name.str .anonymous leaf).toString == query
    | _ => false
  if found.size == 1 then return found[0]!
  if found.isEmpty then
    throw (IO.userError s!"no theorem named '{query}' is defined in the input file")
  let names := (found.map (·.toString)).qsort (· < ·)
  throw (IO.userError s!"ambiguous theorem '{query}'; candidates: {String.intercalate ", " names.toList}")

def selectCommands (a : Analysis) (target : Name) : Std.HashSet Nat := Id.run do
  let _ : Inhabited Environment := ⟨a.env⟩
  let mut selected : Std.HashSet Nat := {}
  let mut queue := #[a.owners[target]!]
  let mut attributes : Array Nat := #[]
  let mut untracked : Array Nat := #[]
  for i in [:a.commands.size] do
    let cmd := a.commands[i]!
    if isAttributeCommand cmd.stx then
      attributes := attributes.push i
    if hasUntrackedEffect cmd then
      -- Arbitrary environment mutations have no complete read trace in InfoTree.
      untracked := untracked.push i
  while !queue.isEmpty do
    let i := queue.back!
    queue := queue.pop
    if selected.contains i then continue
    selected := selected.insert i
    let cmd := a.commands[i]!
    queue := queue ++ cmd.scopes ++ (a.scopeEnds[i]?).getD #[]
    if isScopeCommand cmd.stx then continue
    queue := queue ++ cmd.context
    for j in untracked do
      if j < i then queue := queue.push j
    let mut refs := cmd.refs
    for n in cmd.names do
      if let some ci := a.env.find? n then refs := refs ++ ci.getUsedConstantsAsSet
    for n in refs do
      if let some owner := a.owners[n]? then queue := queue.push owner
    for j in attributes do
      if j < i && a.commands[j]!.attributeTargets.toArray.any refs.contains then
        queue := queue.push j
  return selected

def canonicalNames (a : Analysis) (origins : Array Nat) : Std.HashMap Name Name := Id.run do
  let mut names := {}
  for (n, i) in a.owners.toArray do
    let key := Name.str (Name.num `source origins[i]!) ((privateToUserName n).eraseMacroScopes.toString)
    names := names.insert n key
  return names

def nameKey (names : Std.HashMap Name Name) (n : Name) : String :=
  match names[n]? with
  | some key => s!"local:{key}"
  | none => s!"import:{n}"

partial def levelJson (params : List Name) : Level → Json
  | .zero => toJson (["zero"] : List String)
  | .succ l => toJson (#[toJson "succ", levelJson params l])
  | .max a b => toJson (#[toJson "max", levelJson params a, levelJson params b])
  | .imax a b => toJson (#[toJson "imax", levelJson params a, levelJson params b])
  | .param n => toJson (#[toJson "param", toJson (params.idxOf n)])
  | .mvar n => toJson (#[toJson "mvar", toJson n.name.toString])

partial def exprJson (names : Std.HashMap Name Name) (params : List Name) : Expr → Json
  | .bvar i => toJson (#[toJson "bvar", toJson i])
  | .fvar i => toJson (#[toJson "fvar", toJson i.name.toString])
  | .mvar i => toJson (#[toJson "mvar", toJson i.name.toString])
  | .sort l => toJson (#[toJson "sort", levelJson params l])
  | .const n ls => toJson (#[toJson "const", toJson (nameKey names n), toJson (ls.map (levelJson params))])
  | .app f x => toJson (#[toJson "app", exprJson names params f, exprJson names params x])
  | .lam _ t b bi => toJson (#[toJson "lam", toJson (reprStr bi), exprJson names params t, exprJson names params b])
  | .forallE _ t b bi => toJson (#[toJson "forall", toJson (reprStr bi), exprJson names params t, exprJson names params b])
  | .letE _ t v b nd => toJson (#[toJson "let", exprJson names params t, exprJson names params v, exprJson names params b, toJson nd])
  | .lit (.natVal n) => toJson (#[toJson "nat", toJson n])
  | .lit (.strVal s) => toJson (#[toJson "string", toJson s])
  | .mdata _ e => exprJson names params e
  | .proj n i e => toJson (#[toJson "proj", toJson (nameKey names n), toJson i, exprJson names params e])

def constantJson (names : Std.HashMap Name Name) (ci : ConstantInfo) : Json := Id.run do
  let mut fields := [("type", exprJson names ci.levelParams ci.type),
    ("levels", toJson ci.levelParams.length)]
  let (kind, value) := match ci with
    | .axiomInfo _ => ("axiom", none)
    | .defnInfo v => ("def", some v.value)
    | .thmInfo _ => ("theorem", none)
    | .opaqueInfo v => ("opaque", some v.value)
    | .quotInfo _ => ("quotient", none)
    | .inductInfo _ => ("inductive", none)
    | .ctorInfo _ => ("constructor", none)
    | .recInfo _ => ("recursor", none)
  fields := fields ++ [("kind", toJson kind)]
  if let some value := value then
    fields := fields ++ [("value", exprJson names ci.levelParams value)]
  match ci with
  | .inductInfo v =>
    fields := fields ++ [("ctors", toJson (v.ctors.map (nameKey names))),
      ("all", toJson (v.all.map (nameKey names))),
      ("params", toJson v.numParams), ("indices", toJson v.numIndices)]
  | .ctorInfo v =>
    fields := fields ++ [("index", toJson v.cidx), ("params", toJson v.numParams),
      ("fields", toJson v.numFields)]
  | .recInfo v =>
    fields := fields ++ [("rules", toJson (v.rules.map fun r =>
      Json.arr #[toJson (nameKey names r.ctor), toJson r.nfields, exprJson names ci.levelParams r.rhs]))]
  | _ => pure ()
  return Json.mkObj fields

def typeCertificate (a : Analysis) (target : Name) (names : Std.HashMap Name Name) : Json := Id.run do
  let root := (a.env.find? target).get!
  let mut queue := root.type.getUsedConstantsAsSet.toArray
  let mut seen : NameSet := {}
  let mut entries := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    if seen.contains n || !a.owners.contains n then continue
    seen := seen.insert n
    if let some ci := a.env.find? n then
      entries := entries.push (nameKey names n, constantJson names ci)
      queue := queue ++ ci.getUsedConstantsAsSet.toArray
  return Json.mkObj [
    ("target", toJson (nameKey names target)),
    ("type", exprJson names root.levelParams root.type),
    ("levels", toJson root.levelParams.length),
    ("dependencies", Json.mkObj entries.toList)]

def commandHasSorry (a : Analysis) (cmd : CommandData) : Bool :=
  cmd.names.any fun n => match a.env.find? n with
    | some ci => ci.getUsedConstantsAsSet.contains ``sorryAx
    | none => false

def commandRanges (a : Analysis) : IO (Array Syntax.Range) := do
  let rawMap := a.source.toFileMap
  let parserMap := a.source.crlfToLf.toFileMap
  a.commands.mapIdxM fun i cmd => do
    let some range := cmd.stx.getRange?
      | throw (IO.userError s!"command {i} has no source range")
    -- Lean parses normalized line endings. Translate its offsets back to raw bytes.
    return {
      start := rawMap.ofPosition (parserMap.toPosition range.start)
      stop := rawMap.ofPosition (parserMap.toPosition range.stop)
    }

def commentDepth (line : String) (depth : Nat) : Nat := Id.run do
  let mut chars := line.toList
  let mut depth := depth
  while !chars.isEmpty do
    match chars with
    | '/' :: '-' :: rest => depth := depth + 1; chars := rest
    | '-' :: '/' :: rest => depth := depth - 1; chars := rest
    | '-' :: '-' :: rest =>
      if depth == 0 then break
      chars := '-' :: rest
    | _ :: rest => chars := rest
    | [] => break
  return depth

-- Only gaps are compacted. Blank lines inside block comments remain verbatim.
def compactGap (gap : String) (atFileStart := false) : String := Id.run do
  let lines := gap.splitOn "\n" |>.toArray
  let mut output := ""
  let mut depth := 0
  let mut blankLines := 0
  for i in [:lines.size] do
    let line := lines[i]!
    let blank := depth == 0 && line.toList.all (fun c => c == ' ' || c == '\t' || c == '\r')
    -- The first fragment terminates the preceding command; the last may indent the next.
    let completeBlank := blank && (i > 0 || atFileStart) && i + 1 < lines.size
    if !completeBlank || blankLines < 2 then
      output := output ++ line
      if i + 1 < lines.size then output := output ++ "\n"
    blankLines := if completeBlank then blankLines + 1 else 0
    depth := commentDepth line depth
  return output

def extract (req : Request) (a : Analysis) : IO Unit := do
  let _ : Inhabited Environment := ⟨a.env⟩
  let target ← resolveTarget a req.theoremName
  let selected := selectCommands a target
  let origins := (Array.range a.commands.size).filter selected.contains
  let names := canonicalNames a (Array.range a.commands.size)
  let ranges ← commandRanges a
  let mut sourceCommands : Array String := #[]
  let mut output := ""
  let mut gap := ""
  let mut cursor : String.Pos.Raw := 0
  for i in [:a.commands.size] do
    let range := ranges[i]!
    if range.start < cursor || range.stop < range.start then
      throw (IO.userError "overlapping source command ranges")
    gap := gap ++ String.Pos.Raw.extract a.source cursor range.start
    if selected.contains i then
      let text := String.Pos.Raw.extract a.source range.start range.stop
      sourceCommands := sourceCommands.push text
      output := output ++ compactGap gap output.isEmpty ++ text
      gap := ""
    cursor := range.stop
  output := output ++ compactGap (gap ++ String.Pos.Raw.extract a.source cursor a.source.rawEndPos)
  IO.FS.writeFile req.candidate output
  let plan := Json.mkObj [
    ("origins", toJson origins),
    ("sourceCommands", toJson sourceCommands),
    ("conservativeCommands", toJson (origins.filter fun i =>
      isContextCommand a.commands[i]!.stx || hasUntrackedEffect a.commands[i]!)),
    ("certificate", typeCertificate a target names),
    ("sorry", toJson (origins.map fun i => commandHasSorry a a.commands[i]!)),
    ("keptCommands", toJson origins.size),
    ("removedCommands", toJson (a.commands.size - origins.size)),
    ("theorem", toJson (privateToUserName target).toString)]
  IO.FS.writeFile req.result plan.compress

def verify (req : Request) (a : Analysis) : IO Unit := do
  let _ : Inhabited Environment := ⟨a.env⟩
  let plan ← readJson req.plan
  let origins : Array Nat ← getField plan "origins"
  if a.commands.size != origins.size then
    throw (IO.userError "extraction changed command boundaries")
  let names := canonicalNames a origins
  let certificate ← getJson plan "certificate"
  let targetKey : String ← getField certificate "target"
  let found := a.owners.toArray.map (·.1) |>.filter fun n => nameKey names n == targetKey
  if found.size != 1 then throw (IO.userError "output does not define the original target uniquely")
  let target := found[0]!
  let some (.thmInfo ci) := a.env.find? target
    | throw (IO.userError "output target is not a theorem")
  let expectedType ← getJson certificate "type"
  let expectedLevels : Nat ← getField certificate "levels"
  if exprJson names ci.levelParams ci.type != expectedType || ci.levelParams.length != expectedLevels then
    throw (IO.userError "target theorem type changed after extraction")
  let dependencies ← getJson certificate "dependencies"
  let entries ← IO.ofExcept dependencies.getObj?
  let mut byKey : Std.HashMap String (Array Name) := {}
  for (n, _) in a.owners.toArray do
    let key := nameKey names n
    byKey := byKey.insert key ((byKey[key]?).getD #[] |>.push n)
  for (key, expected) in entries.toArray do
    let found := (byKey[key]?).getD #[]
    if found.size != 1 then
      throw (IO.userError s!"cannot uniquely match statement dependency {key}")
    let ci := (a.env.find? found[0]!).get!
    if constantJson names ci != expected then
      throw (IO.userError s!"statement dependency changed after extraction: {key}")
  let originalSorry : Array Bool ← getField plan "sorry"
  for i in [:a.commands.size] do
    if commandHasSorry a a.commands[i]! && !originalSorry[i]! then
      throw (IO.userError s!"extraction introduced sorry in command {origins[i]!}")
  let sourceCommands : Array String ← getField plan "sourceCommands"
  let ranges ← commandRanges a
  for i in [:a.commands.size] do
    let range := ranges[i]!
    if sourceCommands[i]? != some (String.Pos.Raw.extract a.source range.start range.stop) then
      throw (IO.userError s!"extraction changed original source in command {origins[i]!}")
  IO.FS.writeFile req.result (Json.mkObj [("verified", toJson true)]).compress

unsafe def run (args : List String) : IO UInt32 := do
  let [requestPath] := args | throw (IO.userError "expected one request JSON file")
  let req : Request ← IO.ofExcept (fromJson? (← readJson requestPath))
  Lean.initSearchPath (← Lean.findSysroot)
  let a ← analyze req
  match req.mode with
  | "extract" => extract req a
  | "verify" => verify req a
  | _ => throw (IO.userError s!"unknown mode: {req.mode}")
  return 0

end LeanExtract

unsafe def main (args : List String) : IO UInt32 := do
  try return ← LeanExtract.run args
  catch e =>
    IO.eprintln s!"lean-extract: {e}"
    return 1
