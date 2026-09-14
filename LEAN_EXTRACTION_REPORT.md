# Lean 4 单定理依赖语句抽取评估

结论：**建议以 `leagent/lean-extract` 为主要基础，按需借用 `lean-graph` 的依赖查询和声明归属判断。两个项目都有实质帮助，但当前都不能直接完成“保留原证明，只抽取所需语句，生成可编译的新 Lean 文件”。**

本报告按你的描述，以“抽取目标文件内的依赖，外部库继续通过 `import` 使用”为首版目标。若还要把其他文件的依赖源码合并进来，需要额外处理跨模块作用域和私有名称。这里的“依赖”包括定理陈述和原证明；仅提取陈述依赖或把证明替换成 `sorry` 都不算完成。

评估基于当前目录源码，而非只依据 README。版本为 `leagent@87dc16bef0cd`、`lean-graph@3bf57c70f032`。文末说明实际运行的验证范围。

## 1. 能直接帮到实现的部分

| 所需能力 | 可复用实现 | 对你的工具的实际用途 |
|---|---|---|
| 读取目标文件的真实 Lean 环境 | `leagent` 的 `Frontend.elaborateFile` | 返回 elaboration 后的 `Environment`、完整源码、按文件顺序排列的命令 `Syntax`、`InfoTree` 和错误标记。可以作为“输入文件路径”的入口。 |
| 定位目标定理 | `DeclClosure.resolveTarget` | 支持完整名称和私有声明的显示名称，遇到歧义报错。用于直接处理当前文件时需适配模块归属判断；按位置选定理还要增加位置映射入口。 |
| 追踪直接和传递依赖 | `CollectCommon.collectPremisesFrom`、`collectPremises` | 从定理类型和证明中的常量出发继续遍历，可以传入自定义 `owned` 谓词限制抽取范围。 |
| 区分陈述依赖和证明依赖 | `collectStatementPremises`、`DeclClosure.computeClosure` | 可以标注每条依赖的来源，调试漏提取时有用。保留原证明时应取完整闭包。 |
| 找回完整声明源码 | `SourceSyntax.buildDeclSourceMap`、`sliceTrimmed` | 从 Lean 语法节点的范围切出原文，保留属性、修饰符、签名和证明。适用于 `structure`、`inductive`，不必尝试从 pretty-print 的类型重新拼源码。 |
| 记录基本作用域 | `CorpusManifest.buildScopeMap` | 记录声明所在命名空间及当时有效的 `namespace`、`section`、`open`、`variable`、`universe`、`set_option`。可用于重建作用域或决定保留哪些上下文命令。 |
| 校验源码切片和编辑范围 | `LeanReassemble.Rewrite.planEdits`、`validateEdits`、`applyEdits` | 校验名称、模块、位置和证明文本，拒绝错配及重叠编辑；可借用其检查方法实现声明删除。当前编辑器主要针对定理，需要扩展到其他命令。 |
| 检查证明是否含 `sorry` | `Corpus.Verify.verifyConst` | 通过 `Lean.collectAxioms` 检查目标及其传递依赖中的 `sorryAx`。生成文件编译成功以后仍应做这项检查。 |
| 查询声明依赖和所属模块 | `lean-graph` 的 `Name.transitivelyUsedConstants`、`Name.requiredModules` | 提供较小的 `CoreM` 查询接口，适合补充外部依赖模块信息，无须生成整个项目的大图。 |
| 辅助常量对应到原始声明 | `lean-graph` 的 `getParentDeclaration` | 构造器归到归纳类型；其他部分辅助声明根据源码选择位置判断父声明。可作为归属映射的补充规则。 |

主要代码入口：

- [Frontend.elaborateFile](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/Frontend.lean:101)
- [resolveTarget 与 computeClosure](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/DeclClosure/Cone.lean:141)
- [依赖遍历与范围谓词](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/CollectCommon.lean:145)
- [完整声明源码提取](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/SourceSyntax.lean:265)
- [作用域记录](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/CorpusManifest.lean:300)
- [源码编辑校验](/home/wwb/codes/lean_extract/leagent/reassemble/LeanReassemble/Rewrite.lean:192)
- [sorry 检查](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/Verify.lean:77)
- [声明及模块依赖查询](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Imports/RequiredModules.lean:34)
- [辅助声明归属判断](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Graph/FilterCommon.lean:119)

其中 `buildScopeMap` 是私有函数，现有公开入口是 [SourceMaps.of](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/CorpusManifest.lean:841)。如果只借用这一小部分，需要调整函数可见性或提取成独立模块。表中的代码并非全部都能在包外直接调用。

## 2. `leagent` 已做到哪里

它已有 `--decl <Name>` 流程：先导入编译后的模块，解析目标名称并计算依赖闭包，再只对涉及的源文件做 elaboration，最后输出该目标的 JSONL 记录。多个目标可以共享一次文件处理。具体驱动见 [DeclClosure.run](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/DeclClosure.lean:44)。

对你的工具有用的输出字段包括：

| 字段 | 应如何使用 |
|---|---|
| `name`、`module`、`file`、源码行列 | 定位声明及原始文件。内部仍应保存 raw Lean `Name`，避免私有名称去修饰后冲突。 |
| `decl_source` | 生成源码的首选文本。它比 `signature` 与 `body` 拼接更完整。 |
| `decl_namespace`、`scope_prelude` | 重建基本作用域。注意 `scope_prelude` 已含命名空间开启语句，不能再重复包一层相同命名空间。 |
| `deps`、`premises`、`closure_role` | 分别提供直接依赖、传递依赖和该声明相对目标的角色。 |
| `file_imports` | 原文件的直接导入模块，适合作为首版保留 imports 的参考。需要保留导入修饰符时仍应读取原始 header。 |
| `metadata.json` 的 `assemblyOrder` | 为跨记录输出提供参考顺序。单文件抽取优先保持原始命令顺序。 |
| `dropped.json` | 检查闭包中哪些常量未生成源码记录，避免误把记录集合当成完整源码集合。 |

字段定义见 [ConstRecord](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/Records.lean:19)，闭包筛选和输出见 [projectClosure](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/DeclClosure/Emit.lean:190)。

现成 CLI 的边界与单文件入口不同。`--modules` 按**定义模块的前缀**划定所属范围，通常覆盖一组项目文件，不是“只保留某个文件中的声明”。`--decl` 还要求目标已经出现在所导入的 `.olean` 环境里；没有被指定根模块导入的文件中的目标会找不到。因此首版工具更适合调用 `Frontend.elaborateFile` 处理输入文件，再在所得环境中运行依赖遍历。外部 imports 的 `.olean` 仍需准备好。

这里需要一处明确适配：刚由当前文件生成的常量没有 imported module index，`getModuleIdxFor?` 返回 `none`。现有 `resolveTarget` 会把这种目标判为没有定义模块，`isOwnedByRoots` 也会将其排除。因此不能把 frontend 环境直接交给这两个函数原样使用。应把确认属于当前文件的常量归到输入文件的模块，并向 `collectPremises` 传入文件级 `owned` 谓词。`CollectCommon.isUserConstant` 已使用这一 local/imported 区分，可参考其实现；遍历时仍需保留本地编译器辅助常量。

`statement` 标记也不代表数学上最小的假设集合。它只改变遍历起点：从目标类型出发，后续仍展开被访问声明的类型和定义体。

## 3. 不能把现有 reassemble 当作抽取器

`materialize-units` 的主要用途是生成证明任务。通常它保留目标的整个原始模块，把目标证明替换成 `by sorry`，并通过共享的 `.olean` 缓存提供 imports。它没有把闭包记录拼成一个仅含依赖声明的 Lean 文件，也没有把跨模块依赖源码展开到该文件中。

当前实现还与 README 有一处直接相关的差异：**`materialize-units --proofs keep` 会跳过 keep 目标；所有目标都是 keep 时，最终因没有任务而报错。** 所以不能按 README 的示例，把它当成保留证明的单文件生成命令。代码见 [keep 分支](/home/wwb/codes/lean_extract/leagent/reassemble/LeanReassemble/Materialize.lean:720) 和 [空任务检查](/home/wwb/codes/lean_extract/leagent/reassemble/LeanReassemble/Materialize.lean:872)。

真正值得借用的是其中的范围校验、源码改写和生成后编译验证。`rewrite-file --proofs keep`、仓库整体保留证明的路径可以作为参考状态，但仍不执行依赖裁剪。手动用 manifest 删除邻近定理也不能替代抽取算法：它不会自动决定所需语句，也没有覆盖定义、记号和作用域命令。

## 4. `lean-graph` 应怎样使用

优先考虑它的单声明查询函数，尤其是 `Name.transitivelyUsedConstants`。这个函数直接使用 `ConstantInfo.getUsedConstantsAsSet`，比先导出整张图再筛选更适合你的单目标任务。需要限制为当前文件时，可借用遍历方式并加入范围谓词；`leagent` 的版本已经支持传入该谓词。

`rawUnifiedGraph` 也有参考价值，但**当前 raw 图不能直接作为完整源码重建的唯一依赖依据**：

- 它通过 `rawSigEdges info` 读取 `info.type`，再通过 `valueDeps` 读取定义体。对于 `structure Box where field : Hidden`，`Box` 自身的类型通常只有 `Type`，字段类型在构造器 `Box.mk` 中。如果目标只引用 `Box`，图里有 `Box.mk` 节点也不等于存在 `Box → Box.mk` 的遍历边。必须补上声明族关系，或改用 Lean 的 `ConstantInfo.getUsedConstantsAsSet`。
- `valueDeps` 的兜底分支调用 `info.value?`，没有开启 `allowOpaque := true`，因此不能一般性地覆盖 opaque 定义体。它针对 `irreducible_def` 查找同名 `_def` 定理的处理是特例，不能替代通用 opaque 支持。
- readable 图还会过滤节点、把依赖转向父声明、跨过被过滤节点，并加入文档引用等边。这些是展示规则，不能直接用来决定要删除哪些源码。

相关实现见 [rawUnifiedGraph](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Graph/Unified.lean:159)、[rawSigEdges](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Graph/TypeDeps.lean:75)、[valueDeps](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Graph/ProofDeps.lean:35)。

当前 CLI 的 `--mode unified` 默认调用 raw 图，只有加 `--readable` 才走可读图，见 [MainGraph](/home/wwb/codes/lean_extract/lean-graph/MainGraph.lean:104)。README 中关于默认过滤的描述不能直接套用到这个提交。

模块依赖函数适合给出 import 候选。`#min_imports` 明确不追踪 tactic 和 syntax，因此不能保证建议的 imports 足够重新编译原证明，见 [MinImports](/home/wwb/codes/lean_extract/lean-graph/LeanGraph/Tools/MinImports.lean:27)。首版保留原 import header，之后再通过重新编译尝试删除冗余 import，比较稳妥。

## 5. 实现工具仍需补齐的核心

### 从常量依赖到源码命令依赖

一条 Lean 命令可以生成许多常量。例如 `inductive` 生成类型、构造器和递归器，`deriving` 会生成实例，`where` 会生成辅助声明。必须建立“raw 常量名 → 所属顶层源码命令”的映射，按命令选择和去重。

保留一个命令后，还要检查该命令生成的其他声明及其源码所需上下文，继续补齐依赖，直到选择集合不再变化。不能只提取目标最初引用的那几个常量。`mutual ... end` 要作为完整命令组保留；`assemblyOrder` 只是容忍环的 DFS 输出，跳过回边不能把相互递归声明变成可以逐条拼接的源码。见 [topoOrder](/home/wwb/codes/lean_extract/leagent/lean-extract/Corpus/DeclClosure/Emit.lean:34)。

`getParentDeclaration` 可提供一部分映射规则，但不能覆盖任意用户自定义命令和宏。完整实现应结合源码范围、命令 elaboration 前后的新增声明，以及 Lean 的结构体、构造器、投影等元数据。

`leagent` 会丢弃构造器、投影、编译器辅助常量，以及部分没有 `decl_source` 的记录。这不一定是漏源码，因为保留所属原始命令通常会重新生成它们。但 `dropped.json` 只是诊断，并没有证明所有被丢弃项都能重新生成。`--strict-closure` 会把任何丢弃都视为错误，也不能代替源码完整性验证。

### 补齐证明项里看不见的依赖

`scope_prelude` 已经解决一部分上下文记录，但 `buildScopeMap` 当前只收集前述几类命令。局部记号、自定义 tactic、独立的 `attribute [simp]`、`attribute [instance]`、`include`、`omit`、单独的 `deriving instance` 等仍需要处理。

例如下面的证明最后可以只是反身性证明，但要原样保留其源码，就必须保留 `local notation` 和 `macro`：

```lean
structure Box where
  n : Nat

local notation "BOX" => Box
macro "finish_here" : tactic => `(tactic| rfl)

theorem target (x : BOX) : x = x := by finish_here
```

同样，`simp only [extraLemma]` 中没有最终贡献到证明项的显式参数，仍可能是原 tactic 脚本解析和 elaboration 所需的名称。常量闭包可以提供初始候选集合，不能独自给出“原源码可重放”的完整条件。

适合首版的做法是保守保留目标之前相关作用域中的非声明命令，按语法节点逐步尝试删除，每次都重新编译并检查目标。这样得到的是经过验证的裁剪结果，不应宣称全局最小。以后再利用 `InfoTree` 中的名称解析信息减少保守保留的内容。

### 保留原有顺序和语义

单文件模式下按原始顺序输出所选命令，保留作用域的开启、结束和属性生效顺序，避免把 `scope_prelude` 对每条声明重复执行。命名空间、变量和选项不是可以随意排序的依赖节点。

若扩展为跨文件内联，`privateNames` 只能帮助识别冲突，不能自动解决冲突。不同模块中同名的私有声明、合并后泄漏的 notation 和属性状态，都需要名称改写或作用域隔离。首版保留外部 imports 可以避开这部分实现工作。

## 6. 推荐的首版流程

1. 输入 Lake 项目路径、Lean 文件路径和定理全名。使用目标项目匹配的 Lean 工具链及搜索路径。
2. 调用 `Frontend.elaborateFile` 处理文件，检查错误并定位目标，建立命令范围和声明归属索引。无需先把目标文件加入某个根模块的导入树。
3. 调用 `collectPremises`，以“当前输入文件定义的常量”为所属范围，收集目标陈述和原证明的传递依赖。外部依赖通过原 imports 提供。
4. 把依赖映射到完整源码命令，保留所属的 `mutual`、`where`、归纳类型等命令组，补齐命令组引入的依赖及作用域。
5. 按原顺序写入新文件。保留原始证明和 import header，保守保留所需非声明命令，再通过编译检查逐步裁剪。
6. 在只提供既定 imports 的新 Lean 环境中编译输出，确认目标确实由输出文件定义、类型符合原目标，且没有新增 `sorryAx` 或替代原证明的新公理。不要通过导入原目标模块让缺失声明被悄悄补上。

完整闭包包括原来证明引用的辅助定理及其证明。若后续允许改写原证明，`Corpus.ReverseElab` 生成并检查 tactic 脚本的能力可以降低对原 tactic 环境的依赖，但它可能失败，而且现有检查发生在原环境中。迁移到新文件后仍需重新验证；首版没有必要引入这条分支。

建议优先复用 `Frontend`、`CollectCommon`、`SourceSyntax` 和作用域记录，新增一个按源码命令裁剪的输出模块。直接把 `decl_source` 按 `assemblyOrder` 串联，或直接套用 `materialize-units`，都缺少上述关键步骤。

## 7. 验证范围与版本约束

两个项目的固定工具链不同：`leagent` 为 Lean `v4.33.0`，`lean-graph` 为 `v4.29.0`。本机没有这两个精确版本，也没有这两个项目的构建缓存。本次没有运行两项目固定版本的完整构建或端到端 CLI，不把 README 的成功案例当成本机验证结果。

本次使用本机已安装的 Lean `v4.34.0-rc1`，将 `leagent` 的原始 `Corpus/CollectCommon.lean` 和 `Corpus/SourceSyntax.lean` 编译到临时目录，并运行小例子。验证结果为：

| 检查 | 结果 |
|---|---|
| 目标引用辅助定理，辅助定理引用定义 | 完整闭包含辅助定理和定义，排除无关定理。 |
| 同一目标的陈述闭包 | 包含陈述中的定义，排除仅供证明使用的辅助定理。 |
| 目标仅通过参数类型引用结构体，字段类型又是另一个结构体 | `collectPremises` 经构造器找到字段类型，说明不能只根据“结构体自身类型是 Type”就认定该函数漏依赖。 |
| 比较结构体自身的类型表达式与常量级依赖 API | 类型表达式没有构造器边，常量级 API 包含构造器；支持前面对 raw 图构造方式的限制判断。 |
| opaque 的定义体访问 | 默认 `value?` 不返回其定义体，`ConstantInfo.getUsedConstantsAsSet` 能包含定义体依赖。 |
| 对带 `@[simp]` 的定理使用语法范围切片 | 完整属性和证明文本得到保留，声明源码映射成功建立。 |

这些检查验证了局部函数和 Lean API 行为，不代表两项目整体兼容 `v4.34.0-rc1`。raw 图与 `materialize-units --proofs keep` 的结论还分别依据本地实现逐行核查，未运行其完整 CLI。临时验证材料位于 `/tmp/lean-extract-review.rTaG3o/`，两个项目的源码均未修改。

实际集成时应先统一到目标项目的 Lean 版本，再移植需要的小模块。`.olean` 和使用 Lean 内部 API 的工具需要与该版本匹配。无需为了实现单文件抽取，同时引入两个项目的完整命令行和图导出流程。
