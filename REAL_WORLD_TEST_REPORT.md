# 上游长文件提取测试

## 空行整理后的复测

2026-09-14，在完成命令选择后，将命令之间连续的空行压缩到最多两行，再执行原有输出验证。保留命令的陈述、证明和内部空行逐字保留，块注释内部的空行不变，沿用 LF 或 CRLF 换行格式。

| 案例 | 输入行数 | 整理前输出行数 | 整理后输出行数 | 输出非空行数 | 整理后输出字节 |
| --- | ---: | ---: | ---: | ---: | ---: |
| HashMap | 2,999 | 1,278 | 119 | 56 | 1,970 |
| TreeMap | 4,187 | 1,794 | 103 | 46 | 1,408 |
| List | 1,245 | 690 | 84 | 50 | 2,131 |
| Finset | 911 | 442 | 123 | 77 | 3,196 |
| Trigonometric | 1,262 | 734 | 230 | 159 | 7,045 |

本轮仍使用同一组目标。空行整理不改变依赖选择或类型核对范围，下方语义审查指出的两处漏洞仍未修复。新增测试覆盖文件开头和结尾的连续空行、删除命令后合并出的空行、含空格的空行、LF/CRLF、嵌套块注释及证明内部空行的原文保留。

五个案例均通过完整输入检查、提取器当前的编译与一致性检查、保留命令原文核对及独立 Lean 编译。与整理前输出逐行比较，五份文件的全部非空行均相同。三项针对性回归测试也通过，其中空行整理测试分别运行 LF 和 CRLF 输入。

新生成的示例文件和验证日志保存在 [空行整理复测结果](.real-world/results/20260914T111522.277567Z/results.json)。下方较大的行数与字节数属于空行整理前的历史记录。

## 手工语义审查

2026-09-14，逐段对照了 HashMap、List 和三角函数三个提取结果，并增加两个针对验证边界的反例。结论是：三个真实案例未发现目标语义变化，但当前验证器确实会放行另外两种语义变化，不能把 `type verified` 当作完整的语义保证。本次只做审查和保存反例，没有修改提取算法。

### P1：输入分析改变了待比较的类型基准

[LeanExtract.lean:172](/home/wwb/codes/lean_extract/LeanExtract.lean:172) 在分析输入时额外设置 `trace.Meta.Tactic.simp.rewrite=true`。自定义 elaborator 可以读取这个选项；由此得到的类型未必是原文件在正常配置下的类型。

反例见 [trace-baseline/Input.lean](.real-world/manual-audit/trace-baseline/Input.lean)。`ambientType` 在模块 `Input` 且 rewrite trace 关闭时返回 `Bool`，其他情况下返回 `Nat`。实际结果如下：

| 检查步骤 | 目标类型 |
| --- | --- |
| 在源文件目录执行 `lean Input.lean` | `forall (x : Bool), x = x` |
| 提取器分析输入，额外启用 trace | `forall (x : Nat), x = x` |
| 提取后的 `Output.lean`，正常配置 | `forall (x : Nat), x = x` |

CLI 退出码为 0，报告 `kept 2 commands, removed 1; type verified` 并写出了输出。审查器在不添加 trace 选项的情况下重新分析两份文件，得到 `sameType=false`、`sameStatementCertificate=false`，见 [原始结果](.real-world/manual-audit/trace-baseline/audit.json)。保留的源代码字节和作用域完全一致，所以原文核对也无法发现这种变化。

修复方向是让比较基准来自原配置下的执行。执行追踪不能通过改变用户 metaprogram 可观察的选项来取得一个不同的基准，再用这个基准验证输出。

### P1：仅供证明使用的定义发生变化而未被核对

[LeanExtract.lean:365](/home/wwb/codes/lean_extract/LeanExtract.lean:365) 只从 `root.type` 收集一致性检查的依赖，证明中使用的定义可能不在证书中。与此同时，`env.contains` 等元编程环境读取没有被完整追踪。

反例见 [proof-dependency/Input.lean](.real-world/manual-audit/proof-dependency/Input.lean)：

```lean
import Lean
def marker : Nat := 0
elab "observedValue" : term => do
  let env <- Lean.getEnv
  return Lean.mkNatLit (if env.contains `marker then 1 else 2)
def used : Nat := observedValue
theorem target : True := by
  have _ : used = used := rfl
  trivial
```

提取器删除了 `marker`，保留了 `observedValue`、`used` 和 `target` 的原文。但重新 elaboration 后，`used` 的值从 `1` 变成 `2`。CLI 仍以退出码 0 报告 `kept 3 commands, removed 2; type verified`。

[原始结果](.real-world/manual-audit/proof-dependency/audit.json) 显示 `used.sameValue=false`，目标类型、陈述证书和归一化后的目标证明项却都相同。这个例子不仅说明陈述类型检查不够，也说明仅比较目标证明项本身不能发现所有间接变化。

修复方向是补足环境读取依赖，并核对证明执行依赖中的相关定义。暂时无法追踪的元编程读取不能直接当作无依赖而删除。

### 三个真实案例的对照

| 案例 | 手工检查内容 | 结果 |
| --- | --- | --- |
| `Std.HashMap.getElem!_map'` | 完整参数、`pmap` 中的成员证明、`mem_iff_isSome_getElem?`、两个不同 section 中的 `m` | 原文、类型、证明项和原有作用域一致 |
| `List.foldl_assoc_comm_cons` | 两个局部记号、结合性与交换性实例、`rw` 的三个参数；前面 `include hf` 的作用域已结束 | 原文、类型、证明项和原有作用域一致 |
| `Real.cos_pi_div_five` | `Real.pi` 的 choice 定义、存在性引理、二次方程辅助定理、`CosDivSq` section 和完整证明 | 原文、类型、证明项和原有作用域一致；`Real.pi` 定义体一致 |

补充检查由 [Inspect.lean](.real-world/manual-audit/Inspect.lean) 和 [audit.py](.real-world/manual-audit/audit.py) 执行。它使用原项目选项，不添加 rewrite trace；先逐字匹配每条保留命令及原顺序，再核对作用域和 elaboration 结果。表达式比较沿用现有结构编码，忽略绑定变量名称和元数据，规范化本文件的私有名称。因此表中的证明项一致是指此规范化后的结构一致，不是序列化字节完全相同。

机器记录分别保存在 [HashMap](.real-world/manual-audit/hashmap/audit.json)、[List](.real-world/manual-audit/list/audit.json) 和 [三角函数](.real-world/manual-audit/trigonometric/audit.json)。这只是三个目标的抽查，没有检查全部保留辅助定理的证明项。

还发现一个非语义问题：普通注释仍原样留在删除位置。例如 HashMap 输出中，原来描述另一条引理的 `The following lemma becomes a simp lemma ...` 出现在 `mem_iff_isSome_getElem?` 之前，容易被误读为描述该引理。它不影响 Lean 类型或编译，但输出注释的归属感已经变化。

复跑审查可执行 `python3 .real-world/manual-audit/audit.py hashmap`，其他案例名为 `list`、`trigonometric`、`proof-dependency` 和 `trace-baseline`。反例输出可用常规 CLI 加 `--force` 重新生成。脚本、反例和详细日志保存在本机被 Git 忽略的 `.real-world/manual-audit/` 中。审查的 worker SHA-256 为 `5fabe487b5bf53370d00738c2935372b17c8960f5f744081f46cd31309541ab1`，与下方长文件复测使用的版本相同。

## 执行依赖提取后的复测

2026-09-14，改用单次 elaboration 的引用、宏展开、tactic 中间状态和 simplifier rewrite trace 收集依赖后，重新测试同一组 5 个目标。全部通过完整输入检查、提取器的输出编译、目标类型及相关定义一致性检查、保留命令原文核对，以及独立 Lean 编译。

删除决策不调用编译器试删。每次 CLI 提取只运行一次输入分析和一次输出验证；下表的独立 Lean 检查是测试脚本的额外验收步骤。

| 案例 | 旧版保留命令 | 本轮保留命令 | 旧版输出字节 | 本轮输出字节 | 本轮非空行 | 提取耗时 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| HashMap | 323 | 15 | 55,671 | 3,129 | 56 | 14.585 秒 |
| TreeMap | 376 | 16 | 62,706 | 3,099 | 46 | 13.633 秒 |
| List | 186 | 19 | 19,930 | 2,737 | 50 | 25.950 秒 |
| Finset | 147 | 31 | 24,736 | 3,515 | 77 | 22.844 秒 |
| Trigonometric | 170 | 45 | 25,559 | 7,549 | 159 | 34.111 秒 |

例如 HashMap 只保留目标 `getElem!_map'`、所需引理 `mem_iff_isSome_getElem?` 及原有上下文。未使用的带属性声明、实例和 `grind_pattern` 不再成为保留根节点。本轮尚未整理命令间空白，因此总行数不能直接代表剩余代码量。

本轮耗时为本机单次测量，期间同时运行了回归测试，不用于证明性能提升。执行记录、源码与实现 SHA-256、输出文件及独立检查日志见 [本轮结果](.real-world/results/20260914T103303.174938Z/results.json)。这 5 个案例不能证明对任意 metaprogram 都能得到完整的执行依赖；上下文与未知环境读取的边界见 [提取规则](README.md#提取规则)。

## 首轮记录

2026-09-14，在 Lean 4.26.0 下测试了两个公开仓库的 5 个文件，每个文件选择一个定理。完整输入共 10,604 行。5 个案例均通过原文件检查、提取器内部的编译与类型核对，以及另一个 Lean 进程的输出编译检查。

本轮没有修改提取算法或输入源码，新增了上游测试脚本及运行记录。以下结论仅覆盖选定的 5 个目标，不代表对整个标准库或 Mathlib 的逐定理验证。

## 源码与目标

源码从 GitHub 获取，保留原证明及版权注释。版本固定为：

- Lean：`leanprover/lean4` 的 `v4.26.0`，提交 `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`。下载的标准库文件与本机该工具链附带的源码逐字节一致。
- Mathlib：`leanprover-community/mathlib4` 的 `v4.26.0`，提交 `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`。测试结束后其 Git 工作区无源码改动。

| 上游文件 | 目标定理 | 涉及的情况 |
| --- | --- | --- |
| [Std/Data/HashMap/Lemmas.lean](https://github.com/leanprover/lean4/blob/d8204c9fd894f91bbb2cdfec5912ec8196fd8562/src/Std/Data/HashMap/Lemmas.lean#L2941) | `Std.HashMap.getElem!_map'` | 参数化类型、实例、下标记号及本文件引理引用 |
| [Std/Data/TreeMap/Lemmas.lean](https://github.com/leanprover/lean4/blob/d8204c9fd894f91bbb2cdfec5912ec8196fd8562/src/Std/Data/TreeMap/Lemmas.lean#L3663) | `Std.TreeMap.equiv_iff_toList_eq` | 本文件私有辅助定理 `equiv_iff_equiv` |
| [Mathlib/Data/List/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/List/Basic.lean#L941) | `List.foldl_assoc_comm_cons` | 局部记号、作用域变量和交换性实例 |
| [Mathlib/Data/Finset/Card.lean](https://github.com/leanprover-community/mathlib4/blob/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Finset/Card.lean#L766) | `Finset.card_eq_four` | `card_eq_three` 等本文件依赖链及 `grind` |
| [Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean#L850) | `Real.cos_pi_div_five` | 本文件的 π 定义、辅助定理、`norm_num`、`linarith`、`positivity` |

## 结果

“提取耗时”是 CLI 的完整运行时间，包含工具内部验证；不包含环境下载、单独的原文件检查及最后的独立输出检查。数据为本机单次运行的墙钟时间，不是统计性能基准。

| 案例 | 输入行数 | 输出行数 | 输入/输出字节 | 保留/删除命令数 | 提取耗时 | 独立检查 |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| HashMap | 2,999 | 2,181 | 120,105 / 55,671 | 323 / 299 | 16.937 秒 | 通过 |
| TreeMap | 4,187 | 2,890 | 158,501 / 62,706 | 376 / 506 | 15.035 秒 | 通过 |
| List | 1,245 | 914 | 46,180 / 19,930 | 186 / 146 | 26.500 秒 | 通过 |
| Finset | 911 | 746 | 37,558 / 24,736 | 147 / 57 | 25.349 秒 | 通过 |
| Trigonometric | 1,262 | 1,055 | 46,700 / 25,559 | 170 / 139 | 35.412 秒 | 通过 |

输出仍较长，符合已选择的保守策略：带属性的声明、实例及上下文会保留，命令间空白也不会重新排版。例如 TreeMap 的非空行从 3,303 行减少到 1,501 行，而包含空白的总行数从 4,187 行减少到 2,890 行。

## 检查配置

首次直接检查重命名后的标准库文件时，Lean 报告 `module` 实验选项未启用。上游 Std 模块会自动启用该选项，独立文件需要显式指定 `-Dexperimental.module=true`。补齐同等配置后，完整输入和输出都通过检查。

Mathlib 首轮提取的 3 个案例都通过了工具内部验证，但直接对库目录外的输出运行 `lake lean` 时，同样因 `module` 选项失败。原因是 Mathlib 的库级配置不会自动应用到库目录之外的文件。

随后将独立检查调整为 `lake env lean --setup output.setup.json Extracted.lean`。该配置通过 `lake setup-file` 从原输入模块获取，只修改模块名，保留原选项、依赖产物及插件。脚本同时检查配置中不包含原目标模块的导入产物。按此配置重新运行的 3 个案例全部通过，最后的独立输出检查日志均为空，退出码均为 0。

这一调整没有修改 imports、陈述或证明；它落实了“在原项目环境和配置下检查”的约定。输出放到另一个库目录或项目时，仍需准备对应配置。

## 证据与复跑

- [标准库结果及命令](/home/wwb/codes/lean_extract/.real-world/results/std-configured/results.json)
- [Mathlib 结果及命令](/home/wwb/codes/lean_extract/.real-world/results/mathlib-configured/results.json)
- [标准库首次配置失败记录](/home/wwb/codes/lean_extract/.real-world/results/std-initial/results.json)
- [Mathlib 首次外部文件配置失败记录](/home/wwb/codes/lean_extract/.real-world/results/mathlib-initial/results.json)

每个结果目录保留 `original.log`、`extract.log`、`output.log` 和生成的 `Extracted.lean`。Mathlib 案例另有 `output.setup.json`。JSON 记录了源码 URL、提交、源码与输出的 SHA-256、执行命令、退出码及耗时。

生成文件：

- [HashMap 输出](/home/wwb/codes/lean_extract/.real-world/results/std-configured/hashmap/Extracted.lean)
- [TreeMap 输出](/home/wwb/codes/lean_extract/.real-world/results/std-configured/treemap/Extracted.lean)
- [List 输出](/home/wwb/codes/lean_extract/.real-world/results/mathlib-configured/list/Extracted.lean)
- [Finset 输出](/home/wwb/codes/lean_extract/.real-world/results/mathlib-configured/finset/Extracted.lean)
- [Trigonometric 输出](/home/wwb/codes/lean_extract/.real-world/results/mathlib-configured/trigonometric/Extracted.lean)

本机的源码和依赖已准备好，可直接复跑：

```bash
python3 tests/real_world.py --suite all
```

脚本为每次运行创建新的结果目录。其他机器的环境准备步骤见 [README.md](/home/wwb/codes/lean_extract/README.md)。
