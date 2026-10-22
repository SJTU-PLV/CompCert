from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile
import xml.etree.ElementTree as ET


SOURCE = Path(__file__).with_name("参考问答.docx")
TARGET = Path(__file__).with_name("毕业中期答辩问答.docx")

PARAGRAPHS = [
    "Q1：现有的 C2Rust、人工重构以及基于大语言模型的代码迁移工具已经能够把不少 C 程序转换为 Rust。本研究同样以 C 到 Rust 的迁移为目标，那么与这些已有工具相比，本质区别是什么？项目的创新点究竟在形式化方法层面，还是主要体现在工程适配和代码生成规则的补充？",
    "A1：这个问题关系到本研究的基本定位。本研究并不是把“能够生成 Rust 代码”本身作为主要创新，因为现有工具在语法转换和工程迁移方面已经具有较强能力。它们的共同局限是，转换结果通常依赖测试、人工审查或经验规则来建立可信度，很难说明源程序与目标程序在语言语义层面是否保持一致。本研究的切入点是以 CompCert 的 Clight 作为源语言，设计适合验证和代码生成的 Rustlight 中间语言，并在 Coq 中刻画 Clight 到 Rustlight 的转换关系及语义保序条件，使翻译规则能够进入可检查的形式化框架。针对 C 指针算术、数组、结构体、空指针、void 指针、回调和变参等难点，项目采用统一的 Ptr<T> 抽象，把 load、store、offset、cast 等行为显式化，再由打印器和运行时封装生成可由 rustc 编译的代码。因此，核心贡献是把 C 到 Rust 迁移从经验式源码改写推进到“中间语言设计、翻译规则、语义论证和可执行代码生成”相衔接的体系。工程实现并非与理论工作割裂：打印器、运行时库以及典型案例修复用于检验形式化抽象能否落到真实 Rust 工具链中。不过中期阶段仍需实事求是地说明，部分证明和边界特性尚未补齐，因此目前更准确的表述是已经建立了经过验证翻译的主体框架和关键机制，而不是宣称已经覆盖完整 C 语言或实现端到端的完全证明。",
    "Q2：项目使用 Ptr<T> 统一承接 C 的指针语义，但 Rust 的安全性通常来自所有权、借用和生命周期检查。如果生成代码主要依赖自定义指针运行时，甚至在 FFI 和类型转换边界仍需使用 unsafe，那么这种方法是否只是把 C 的不安全操作包装了一层？所谓“安全指针语义”和形式化可信性应当如何界定？",
    "A2：这里需要区分三个层面的安全性。第一层是翻译的语义可信性，即在明确的前置条件下，源程序在 Clight 中的可观察行为能够由 Rustlight 程序保持，这是 Coq 形式化工作的主要目标。第二层是生成代码的类型和内存操作边界。Ptr<T> 并不等于把任意裸指针直接伪装成安全引用，它把所有权来源、空值、偏移和可选边界等信息集中到统一接口中，使解引用、写入、行访问和类型转换不再散落在生成代码各处，从而便于约束、审计和建立证明不变量。第三层才是 Rust 编译器能够静态保证的安全性。当前方案为了忠实表达 C 的别名、指针算术、回调和 libc 交互，仍然保留必要的 unsafe 与运行时假设，因此不能把它等同于完全使用 Rust 借用系统重写后的 safe Rust。项目的可信边界包括 Coq 中的语言语义和转换实现、OCaml 打印器、Ptr<T> 与回调运行时、rustc 以及所调用外部库的行为；其中打印器和运行时仍需要通过代码审查、测试和后续规格化来缩小信任基。也就是说，本研究的价值不是声称消除了所有不安全操作，而是把原来隐含、分散且难以验证的 C 指针行为收敛为少量显式原语，并明确哪些性质由形式化证明保障、哪些依赖运行时检查、哪些属于 FFI 假设。下一阶段将继续补齐关键原语的语义对应证明，并统计生成代码中的 unsafe 分布与触发原因，以量化可信边界是否真正得到收缩。",
    "Q3：当前项目已经加入大语言模型修复和差分测试流水线，在 Rust 编译失败或 C、Rust 行为不一致时自动修改生成代码。但大语言模型的修改本身没有形式化保证，而差分测试也只能覆盖有限输入。这是否会破坏经过验证编译器的可信链？中期之后如何评价系统的正确性、覆盖能力和实际可用性？",
    "A3：大语言模型修复不会被纳入形式化可信链，而是作为编译器外层的工程化补充，两者的保证等级必须明确区分。未经模型修改的路径是 C 经 Clight、Rustlight 和打印器生成 Rust，其目标是通过语义保序证明建立可信性；一旦启用模型修复，最终结果的依据就变为“能够编译并通过当前差分测试”，不能继续沿用原始形式化保证。现有流水线因此记录翻译失败、编译失败、C 基线失败和行为不一致等明确状态，并保存日志、测试用例及报告，目的是让模型修改可追溯，而不是用测试冒充证明。差分测试目前比较退出码、标准输出和标准错误，适合具有可执行入口的程序，但对函数级语义、未被测试覆盖的输入、内存安全和 C 未定义行为仍不充分。下一阶段的评价将分层进行：首先统计基准程序的翻译成功率、Rust 编译通过率及 C/Rust 运行结果一致率；其次围绕指针、数组、结构体、回调、变参和初始化等关键特性建立分类测试，结合边界输入与失败案例分析覆盖薄弱点；再次分别报告“纯编译器输出”和“经模型修复输出”的结果，避免混淆保证来源；最后继续补齐语义证明，并对运行时开销、生成代码中的 unsafe 比例以及模型修复轮次进行量化。这样的评价方式能够同时回答理论正确性和工程可用性，但不会把有限测试结果夸大为对所有程序、所有输入的正确性证明。",
]

# 参考文档的三个回答各预留了两个正文段落。当前回答保持为连续段落，
# 第二个预留段落置空，以完整继承模板的页面与段落格式。
TEMPLATE_PARAGRAPHS = [
    PARAGRAPHS[0], PARAGRAPHS[1], "",
    PARAGRAPHS[2], PARAGRAPHS[3], "",
    PARAGRAPHS[4], PARAGRAPHS[5], "",
]


def main() -> None:
    with ZipFile(SOURCE, "r") as src:
        document = src.read("word/document.xml")
        root = ET.fromstring(document)
        ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
        body = root.find("w:body", ns)
        paragraphs = [
            paragraph
            for paragraph in body.findall("w:p", ns)
            if paragraph.findall(".//w:t", ns)
            and any((node.text or "").strip() for node in paragraph.findall(".//w:t", ns))
        ]
        if len(paragraphs) != len(TEMPLATE_PARAGRAPHS):
            raise RuntimeError(f"模板正文段落数为 {len(paragraphs)}，预期为 {len(TEMPLATE_PARAGRAPHS)}")

        for paragraph, replacement in zip(paragraphs, TEMPLATE_PARAGRAPHS):
            text_nodes = paragraph.findall(".//w:t", ns)
            if not text_nodes:
                raise RuntimeError("模板中存在无文本正文段落")
            text_nodes[0].text = replacement
            for node in text_nodes[1:]:
                node.text = ""

        updated = ET.tostring(root, encoding="utf-8", xml_declaration=True)
        with ZipFile(TARGET, "w", ZIP_DEFLATED) as dst:
            for item in src.infolist():
                payload = updated if item.filename == "word/document.xml" else src.read(item.filename)
                dst.writestr(item, payload)

    print(TARGET)


if __name__ == "__main__":
    main()
