# CCF 论文大纲（outline）

Clight→Rustlight：面向安全指针语义的经过验证的 C→Rust 翻译

# 1. 引言（Introduction）

- 背景与动机：C 生态中大量遗留代码需要迁移到内存安全的 Rust；但 C 指针语义与 Rust 所有权/借用模型差异巨大，现有工程化迁移缺少形式化保证。
- 问题：如何在保持可用性的同时，给出语义上可信的 C→Rust 翻译，尤其是指针、数组、结构体、void*、回调与变参等“棘手”部分。
- 我们的思路：以 CompCert 的 Clight 为源，设计 Rustlight 作为目标中间语言；提出基于 Ptr<T> 的统一指针抽象与打印策略；为关键 libc 函数生成安全封装；在 Coq 中刻画语义与证明思路。
- 贡献（概述）：
  1) 提出并实现一种适配 Rust 的 C 指针抽象（Ptr<T> 模型）及其算法化翻译规则（见 algorithm.txt）。
  2) 在 Coq 中刻画 Clight→Rustlight 的核心语义与保序思路（Rustlight.v、Clight2Rustlight.v）。
  3) 工程化打印与 FFI 封装（PrintRustlight.ml、PrintRustsyntax.ml），覆盖回调与变参；对初始化与数组进行健壮化处理。
  4) 在多组基准（sha3、qsort、perlin、lists 等）上验证可用性，展示与 C 版本一致的功能与性能趋势。

# 2. 背景（Background）

- Clight 与 CompCert：语义化的 C 子集、内存模型与指针操作。
- Rust 与 Rustlight：所有权/借用、指针/切片抽象，为什么需要 Rustlight 作为验证友好的目标语言。
- C 指针难点：指针算术、别名、void*/char*、函数指针与回调、变参、字符串/全局初始化。
- 现有迁移与验证工作简述：CompCert/Verified Compilation、RustBelt、c2rust、CBMC/Kani 等。

# 3. 系统概览（Overview）

- 架构：Clight2Rustlight.v 作为主要 pass；Rustlight.v 刻画目标语义；打印器（PrintRustlight.ml、PrintRustsyntax.ml）生成可编译 Rust；运行时（runtime/ptr.rs、runtime/callback.rs）承接指针/FFI 行为。
- 可信边界与信任根：Coq 规范与证明、OCaml 打印器与运行时、libc 绑定；何处需要可信假设（例如外部库语义）。
- 端到端流程：C 源→Clight→Rustlight→Rust 源→rustc；支持选项与产物（-drustlight、可选封装）。

# 4. 核心算法（Algorithm）

## 4.1 指针抽象与内存视图

- Ptr<T> 统一抽象：所有权(Heap/Borrowed/Null)、位移 offset、可选边界 len；load/store/offset/as_ptr/cast 等原语。
- 数组/多维数组：Ptr<[T;N]>::row 返回行首元素的 Ptr<T>；数组元素读写的规则。
- 指针算术与比较：用 offset 替代 Oadd/Osub；is_null 统一处理 NULL 比较。

## 4.2 Clight→Rustlight 规则（algorithm.txt 摘要）

- 变量、表达式与 place：将 *p 转换为 p.load(0)；数组索引根据被索引对象（Ptr 或数组）分别规则化。
- 结构体与字段访问：(*p).f → (p.load(0)).f；字段初始化流的顺序消费与类型匹配。
- void*/char* 与强制转换：仅在 FFI 或内存操作边界做 unsafe cast；其余保持类型化 Ptr。
- 回调与变参：统一以 trampoline + 回调槽（CallbackSlot）桥接，variadic 中 f32→f64 升级、切片/数组转 raw 指针。
- 初始化与全局：字符串字面量作为 static mut [i8;N]；数组“提前收束”策略避免初始化越界串场。

## 4.3 与“分裂树”方案的比较

- 简化别名/生命周期的问题，将 C 指针“按使用点”落到 Ptr 抽象；
- 更贴近 Rust 实际编译器可接受的代码风格；
- 在保守性与可编译性之间的权衡（必要时插入 as/零填充/封装）。

# 5. 形式化与实现（Formalization & Implementation）

## 5.1 语义与规格

- Rustlight.v：类型系统与指针操作语义（offset/load/store/row），FFI 边界建模。
- Clight2Rustlight.v：转换关系与不变量；错误/未定义行为的处理策略。

## 5.2 证明思路

- 语义保序主定理（概述）：前向/后向模拟的选择与证明分解；
- 已完成与 Admitted 部分；证明工期与增量计划。

## 5.3 打印与运行时

- PrintRustlight.ml：表达式/语句打印、C 调用参数转换策略、qsort/bsearch/printf/scanf 封装生成；
- PrintRustsyntax.ml：结构体/数组/字符串初始化的消费算法，默认值与派生生成；
- runtime/ptr.rs 与 runtime/callback.rs 的接口与安全性讨论。

# 6. 评测（Evaluation）

## 6.1 实验设置

- 平台与工具链：opam/coq/menhir/rustc 版本；
- 数据集：sha3、qsort、perlin、lists、spectral、binarytrees、bisect、almabench、knucleotide 等。

## 6.2 正确性与兼容性

- 编译通过率与运行结果一致性（与 gcc 版对比）；
- 典型问题案例：sha3 初始化越界、qsort 回调、perlin 的数组读写、lists 的指针字段访问等；
- 消融实验：关闭/启用某些打印器修复开关对编译/运行的影响。

## 6.3 性能与开销

- 编译时开销（pass + 打印 + rustc）；
- 运行时开销（Ptr 抽象与封装带来的影响）；
- 讨论：优化空间（边界检查消除、零拷贝转换等）。

# 7. 相关工作（Related Work）

CompCert/Verified Compilation、TACAS/CAV 系列上的验证式编译工具链；RustBelt 与 Rust 语义；c2rust/翻译器；形式化 FFI；验证的内存模型与指针分析。

# 8. 讨论（Discussion）

- 可信边界与威胁：libc 语义假设、运行时 cast 的前提；
- C 未定义行为的保守处理；
- 对 Rust 借用检查的兼容性（生成代码不直接使用借用，而走 Ptr 抽象的利弊）；
- 对并发/原子/对齐/变参边角的扩展性；
- 工程化可维护性与可移植性。

# 9. 结论与展望（Conclusion）

- 总结：提出了面向安全指针语义的 C→Rust 经过验证的翻译框架，在若干基准上验证了可用性；
- 展望：补齐证明、扩大覆盖面（更多 libc/FFI 场景）、进一步优化生成代码质量，争取在 CCF-A 类会议上达成完整发布。

