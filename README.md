# lean-extract

从一个 Lean 文件中提取指定定理及其本文件依赖，保留原陈述和原证明，输出新的 Lean 文件。首版已针对 Lean 4.26.0 编写，运行测试见下文。

## 使用

需要 Python 3.10 或更新版本，以及 Lean 4.26.0。无需安装 Python 第三方包，也不依赖 leagent。

```bash
./lean-extract Input.lean --theorem MyNamespace.target --output Extracted.lean
```

指定 Lean 可执行文件和 Lake 项目：

```bash
./lean-extract /path/to/project/Example.lean \
  --theorem Example.target \
  --output /path/to/project/Extracted.lean \
  --lean /path/to/toolchain/bin/lean \
  --project /path/to/project
```

- `--theorem` 接受完整名称或无歧义的短名称，包括私有定理。名称歧义时列出候选。目标必须在输入文件内定义。
- `--lean` 指定 Lean 可执行文件。省略时在输入文件所属项目中解析默认 Lean 工具链。
- `--project` 指定含 `lakefile.toml` 或 `lakefile.lean` 的目录。省略时从输入文件向上寻找项目。
- `--output` 必填。输出目录须已存在。只有验证成功后才写入输出。
- `--force` 允许替换已有输出，但不允许覆盖输入或写入符号链接。

项目模式使用所选 Lean 自带的 Lake，通过 `lake setup-file` 获取模块选项、imports 构建产物及插件，并通过 `lake env` 获取搜索路径。Lake 可能编译尚未构建的 imports 或生成项目缓存。指定 Lean 必须与项目依赖兼容。没有 Lake 项目时使用所选 Lean 与当前 `LEAN_PATH`。

其他 Lean 版本会显示未经验证的提示。工具依赖 Lean 内部 API，因此不能保证任意版本兼容。

## 提取规则

1. 对整个输入文件执行 Lean 检查。允许原有 `sorry` 警告；任意位置出现错误都会终止。
2. 从目标的类型和证明出发，递归收集本文件常量依赖。外部声明只通过原 imports 提供，不展开源码。
3. 根据逐条命令处理后的环境，将常量映射回源码命令。保留命令时也补齐该命令生成的其他声明的依赖，包括构造器、投影和辅助定义。
4. 收集 Lean 的名称引用信息和语法标识符，补充未出现在最终证明项中的源码依赖。例如 `simp only [extraLemma]` 中未被实际使用的引理仍会保留。
5. 保守保留上下文命令、带属性的声明、实例、宏以及无法可靠分类的命令，并补齐它们的本文件依赖。不反复尝试删除上下文，不承诺输出最小化。
6. 按原文件的字节范围删除未选中的完整命令。保留语句顺序、imports、原证明、语句内注释及文档注释。命令之间的普通注释和空白保守保留，所以输出可能存在空行。
7. 在另一个 Lean 进程中重新检查输出。该进程只加载原 imports，不导入原目标文件。

一条命令中的多个变量、`mutual` 块以及 `where` 辅助声明不会被拆开。上下文的保守策略可能连带留下无关声明，尤其是存在属性、实例、自定义命令或诊断命令时。无法通过检查时明确失败，不通过复制完整输入或改写证明来兜底。

## 类型核对

核对目标定理的内部类型表达式及宇宙参数，并检查陈述直接或间接依赖的本文件声明。对于这些依赖，比较其类型，以及定义和 `opaque` 的定义体；不要求定理证明项完全一致。

比较时按原源码命令匹配本地声明，处理私有名称中的模块名变化，忽略绑定变量名称和表达式元数据。比较不依赖 pretty printer，也不会因为两个不同定义打印成同一个名称就认为类型一致。

这是保守的结构比较，并非任意两个 Lean 环境之间的定义等价判定。如果宏生成的名称无法唯一匹配，或重新处理产生了结构不同的类型，会报告失败。验证也会拒绝原先不含 `sorry` 的保留命令新产生 `sorry`。

## 示例与测试

```bash
./lean-extract tests/fixtures/Basic.lean \
  --theorem Example.target --output /tmp/ExtractedBasic.lean

python3 -m unittest discover -s tests -v
```

测试使用实际 Lean 进程，覆盖传递依赖、完整证明、`sorry`、变量与命名空间、记号和宏、属性与实例、私有声明、结构体、`opaque`、`mutual`、`where`、原文保留、错误输入、名称歧义、Lake 项目和类型变更拒绝。可通过 `TEST_LEAN=/path/to/lean` 选择测试工具链。

### 上游长文件测试

已完成的案例和运行记录见 [上游长文件测试报告](REAL_WORLD_TEST_REPORT.md)。

`tests/real_world.py` 对固定版本的 Lean 标准库及 Mathlib 文件运行测试。每个案例先检查完整输入，再调用提取工具，最后通过单独的 Lean 命令检查输出。源码来源、SHA-256、执行命令、耗时及日志保存在 `.real-world/results/`，不加入默认单元测试。

标准库案例会从 GitHub 下载源码，并与所选工具链附带的源码逐字节核对：

```bash
python3 tests/real_world.py --suite std
```

Mathlib 案例使用 `v4.26.0`，脚本会核对其完整提交号。首次运行需准备源码及对应缓存：

```bash
git clone --depth 1 --branch v4.26.0 \
  https://github.com/leanprover-community/mathlib4.git .real-world/mathlib4
lake -d .real-world/mathlib4 exe cache get \
  Mathlib/Data/List/Basic.lean Mathlib/Data/Finset/Card.lean \
  Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean
python3 tests/real_world.py --suite mathlib
```

可用 `--case hashmap` 等参数只运行一个案例，用 `--lean /path/to/lean` 指定工具链。标准库源码使用 `module`，其独立检查命令显式设置 `-Dexperimental.module=true`，与上游 Std 模块的构建配置一致。

Mathlib 原文件通过 `lake lean` 检查。输出位于库目录之外，因此独立复查通过 `lean --setup` 显式沿用输入模块的完整 Lake 配置，配置文件也保存在测试结果目录。直接对库目录外的输出运行 `lake lean`，可能会丢失库级选项，例如 `experimental.module`。

## 实现文件

- `lean_extract.py`：命令行参数、工具链与项目环境、进程隔离及验证后写入。
- `LeanExtract.lean`：Lean frontend、常量依赖闭包、源码命令映射、切片和类型核对。
- `tests/`：端到端测试与示例输入。

依赖遍历和按语法范围切片的做法参考了仓库中的 `leagent/lean-extract/Corpus/CollectCommon.lean` 和 `SourceSyntax.lean`。工具单独实现，不引入 leagent 的其他流程。
