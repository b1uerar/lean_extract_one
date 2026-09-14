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

instance [Inhabited Environment] : Inhabited CommandData :=
  ⟨{ stx := default, env := default }⟩

structure Analysis where
  source : String
  env : Environment
  commands : Array CommandData
  owners : Std.HashMap Name Nat

def getJson (j : Json) (key : String) : IO Json :=
  IO.ofExcept (j.getObjVal? key)

def getField [FromJson a] (j : Json) (key : String) : IO a :=
  IO.ofExcept (j.getObjValAs? a key)

def readJson (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

partial def syntaxRefs (stx : Syntax) (refs : NameSet) : NameSet := Id.run do
  match stx with
  | .ident _ _ n resolved =>
    let mut refs := refs.insert n
    for r in resolved do
      if let .decl n _ := r then refs := refs.insert n
    return refs
  | .node _ _ args => return args.foldl (fun acc s => syntaxRefs s acc) refs
  | _ => return refs

partial def treeRefs (tree : InfoTree) (refs : NameSet) : NameSet := Id.run do
  match tree with
  | .context _ t => return treeRefs t refs
  | .hole _ => return refs
  | .node info children =>
    let mut refs := refs
    match info with
    | .ofTermInfo i => refs := refs ++ i.expr.getUsedConstantsAsSet
    | .ofFieldInfo i => refs := refs.insert i.projName ++ i.val.getUsedConstantsAsSet
    | .ofMacroExpansionInfo i => refs := syntaxRefs i.output refs
    | .ofOptionInfo i => refs := refs.insert i.declName
    | _ => pure ()
    for t in children do refs := treeRefs t refs
    return refs

def reportMessages (messages : MessageLog) : IO Unit := do
  for msg in messages.toList do
    IO.eprintln (← msg.toString)

unsafe def analyze (req : Request) : IO Analysis := do
  let source ← IO.FS.readFile req.input
  let inputCtx := Parser.mkInputContext source (if req.logicalFile.isEmpty then req.input else req.logicalFile)
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let setup := req.setup.getD { name := req.moduleName.toName }
  let opts := (setup.options.toOptions).setBool `Elab.async false
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
  repeat
    let state := snap.elabSnap.resultSnap.get.cmdState
    if !Parser.isTerminalCommand snap.stx then
      let refs := match snap.elabSnap.infoTreeSnap.get.infoTree? with
        | some tree => treeRefs tree (syntaxRefs snap.stx {})
        | none => syntaxRefs snap.stx {}
      commands := commands.push { stx := snap.stx, env := state.env, refs : CommandData }
    if let some next := snap.nextCmdSnap? then snap := next.task.get else break
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
  return { source, env := finalEnv, commands, owners }

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

partial def hasKind (stx : Syntax) (kind : Name) : Bool :=
  stx.getKind == kind || stx.getArgs.any (hasKind · kind)

partial def removable (stx : Syntax) : Bool :=
  if stx.getKind == ``Parser.Command.mutual then
    stx[1].getArgs.all removable
  else
    stx.getKind == ``Parser.Command.declaration &&
      !(hasKind stx ``Parser.Term.attributes) &&
      !(hasKind stx ``Parser.Command.instance) &&
      !(hasKind stx ``Parser.Command.classInductive) &&
      !(hasKind stx ``Parser.Command.classTk) &&
      !(hasKind stx ``Parser.Command.derivingClasses)

def selectCommands (a : Analysis) (target : Name) : Std.HashSet Nat := Id.run do
  let _ : Inhabited Environment := ⟨a.env⟩
  let mut selected : Std.HashSet Nat := {}
  let mut queue := #[a.owners[target]!]
  for i in [:a.commands.size] do
    if !removable a.commands[i]!.stx then queue := queue.push i
  -- Unresolved syntax identifiers are matched conservatively by suffix. This also
  -- covers attribute arguments and quoted names that produce no TermInfo.
  let mut suffixes : Std.HashMap Name (Array Nat) := {}
  for (n, i) in a.owners.toArray do
    let parts := (privateToUserName n).components
    for j in [:parts.length] do
      let suffix := (parts.drop j).foldl Name.append .anonymous
      suffixes := suffixes.insert suffix ((suffixes[suffix]?).getD #[] |>.push i)
  while !queue.isEmpty do
    let i := queue.back!
    queue := queue.pop
    if selected.contains i then continue
    selected := selected.insert i
    let cmd := a.commands[i]!
    let mut refs := cmd.refs
    for n in cmd.names do
      if let some ci := a.env.find? n then refs := refs ++ ci.getUsedConstantsAsSet
    for n in refs do
      if let some owner := a.owners[n]? then queue := queue.push owner
      for owner in (suffixes[privateToUserName n |>.eraseMacroScopes]?).getD #[] do
        -- Source references cannot resolve to ordinary declarations appearing later.
        if owner <= i then queue := queue.push owner
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

def extract (req : Request) (a : Analysis) : IO Unit := do
  let _ : Inhabited Environment := ⟨a.env⟩
  let target ← resolveTarget a req.theoremName
  let selected := selectCommands a target
  let origins := (Array.range a.commands.size).filter selected.contains
  let names := canonicalNames a (Array.range a.commands.size)
  let mut output := ""
  let mut cursor : String.Pos.Raw := 0
  let rawMap := a.source.toFileMap
  let parserMap := a.source.crlfToLf.toFileMap
  for i in [:a.commands.size] do
    let some range := a.commands[i]!.stx.getRange?
      | throw (IO.userError s!"command {i} has no source range")
    -- Lean parses normalized line endings. Translate its offsets back to raw bytes.
    let range : Syntax.Range := {
      start := rawMap.ofPosition (parserMap.toPosition range.start)
      stop := rawMap.ofPosition (parserMap.toPosition range.stop)
    }
    if range.start < cursor || range.stop < range.start then
      throw (IO.userError "overlapping source command ranges")
    -- Delete only command bytes. Inter-command whitespace and ordinary comments stay intact.
    output := output ++ String.Pos.Raw.extract a.source cursor range.start
    if selected.contains i then
      output := output ++ String.Pos.Raw.extract a.source range.start range.stop
    cursor := range.stop
  output := output ++ String.Pos.Raw.extract a.source cursor a.source.rawEndPos
  IO.FS.writeFile req.candidate output
  let plan := Json.mkObj [
    ("origins", toJson origins),
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
