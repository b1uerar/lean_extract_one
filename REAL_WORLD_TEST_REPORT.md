# 上游长文件提取测试

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
