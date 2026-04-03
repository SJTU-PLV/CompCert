# AI Repair Pipeline

这个流水线把现有编译器和一个外部 LLM 工具串起来，执行下面的闭环：

1. `C -> Rust`
2. `rustc` 编译
3. 如果编译失败，调用 LLM 修复 Rust
4. 编译成功后，让 LLM 生成简单测试用例
5. 编译并运行原始 C 与修复后的 Rust，做差分测试
6. 如果行为不一致，再调用 LLM 修复
7. 成功则结束；多轮失败则输出明确状态

## 新增脚本

- [ai_repair_pipeline.py](/Users/yaodongdong/WorkPlace/project/Compcert/ai_repair_pipeline.py)

## 输出状态

- `SUCCESS`
- `FAIL_TRANSLATION`
- `FAIL_COMPILE`
- `FAIL_C_BASELINE`
- `FAIL_MISMATCH`

运行结束后会在工作目录生成：

- `report.json`
- `logs/`
- `test_cases.json`
- 生成的 `.rs` 文件

## 基本用法

```bash
python3 ai_repair_pipeline.py test/c/c2rust/test.c
```

如果不配置 LLM，脚本仍会：

- 先执行翻译
- 尝试直接编译 Rust
- 生成一个默认空输入测试用例
- 对 C/Rust 做一次基础差分测试

但不会自动修复代码。

## 推荐后端

推荐直接接 **Aider**。

原因：

- 它原生支持单次脚本模式
- 支持 `--message-file`
- 支持只把指定文件加入会话
- 官方明确支持把编译/测试命令接进修复循环

官方文档：

- 安装：<https://aider.chat/docs/install.html>
- 脚本模式：<https://aider.chat/docs/scripting.html>
- 编译/测试闭环：<https://aider.chat/docs/usage/lint-test.html>

仓库里也准备了一个 DeepSeek 模板：

- [.env.aider.deepseek.example](/Users/yaodongdong/WorkPlace/project/Compcert/.env.aider.deepseek.example)
- [run_aider_deepseek.sh](/Users/yaodongdong/WorkPlace/project/Compcert/scripts/run_aider_deepseek.sh)

## 接外部 LLM

### 方式 1：直接使用 Aider

先安装 Aider。官方推荐用隔离环境安装，例如：

```bash
python -m pip install aider-install
aider-install
```

或者：

```bash
python -m pip install uv
uv tool install --force --python python3.12 aider-chat@latest
```

然后配置你的模型环境变量，例如 OpenAI 兼容接口：

```bash
cp .env.aider.deepseek.example .env.aider.deepseek
# 然后编辑 .env.aider.deepseek
```

默认模板内容是：

```bash
OPENAI_API_BASE=https://api.deepseek.com
OPENAI_API_KEY=your_deepseek_api_key_here
AIDER_BIN=/Users/yaodongdong/.local/bin/aider
AIDER_MODEL=openai/deepseek-chat
```

单独启动 Aider 可以用：

```bash
bash scripts/run_aider_deepseek.sh
```

接着运行：

```bash
python3 ai_repair_pipeline.py test.c \
  --llm-backend aider \
  --workspace test/ai_pipeline_run/test_case
```

当 `--llm-backend aider` 启用时，脚本会默认读取仓库根目录的 `.env.aider.deepseek`，自动使用里面的：

- `OPENAI_API_BASE`
- `OPENAI_API_KEY`
- `AIDER_BIN`
- `AIDER_MODEL`

如果你想换文件，也可以手动指定：

```bash
python3 ai_repair_pipeline.py test.c \
  --llm-backend aider \
  --aider-env-file .env.aider.deepseek \
  --workspace test/ai_pipeline_run/test_case
```

如果你要让 Aider 也能改 runtime 文件，可以加：

```bash
--editable-file runtime/ptr.rs --editable-file runtime/callback.rs
```

也可以透传额外参数给 Aider，例如：

```bash
--aider-arg=--no-stream
```

### 方式 2：接任意外部 agent

脚本也支持通过 `--llm-command-template` 接任意外部 agent。模板会收到这些已转义占位符：

- `{phase}`
- `{workspace}`
- `{prompt_file}`
- `{c_file}`
- `{rust_file}`
- `{test_spec_file}`
- `{target_files}`

你可以把它接到任何“读取 prompt 并直接修改文件”的工具。

推荐让外部工具：

- 在 `compile_repair` 和 `mismatch_repair` 阶段编辑生成的 Rust 文件
- 在 `test_generation` 阶段只编辑 `test_cases.json`

## 可编辑文件

默认只允许 LLM 修改生成的 Rust 文件。

如果你希望它也能动 runtime 包装层，可以加：

```bash
--editable-file runtime/ptr.rs --editable-file runtime/callback.rs
```

## 一个典型工作流

```bash
python3 ai_repair_pipeline.py test/c/c2rust/test.c \
  --workspace test/ai_pipeline_run/test_case \
  --max-compile-repairs 5 \
  --max-mismatch-repairs 3 \
  --editable-file runtime/ptr.rs
```

## 测试规范格式

`test_cases.json` 采用下面的 JSON 结构：

```json
{
  "cases": [
    {
      "name": "default",
      "args": [],
      "stdin": "",
      "timeout": 5.0
    }
  ]
}
```

每个 case 会分别运行 C 与 Rust，并比较：

- exit code
- stdout
- stderr

## 注意事项

- 这个流水线是“编译器外层编排”，不会修改你的 `ccomp` 主流程。
- 一旦启用 LLM 修复，最终 Rust 代码的正确性来源于“编译通过 + 差分测试通过”，而不是原始形式化翻译保证。
- 当前差分测试主要适合可执行程序。如果后续要支持函数级翻译，可以再扩展自动生成 driver/harness 的逻辑。
