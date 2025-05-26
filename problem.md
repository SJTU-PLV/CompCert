# 项目流程

目前已完成： c语言 -> clight -> rustlight

目标: c语言 -> clight -> rustlight __->__ Asm

## 不同的编译链的选择
### rustlight -> Asm（直接转）
这个步骤需要的工作量太多，目前还没有开始实现。

但是可以考虑使用编译链：c语言 -> clight -> rustlight -> rust，然后使用rust编译器再到Asm。

目前想这么做，但从rust到Asm的这一段步骤使用的是编译器，因此没有使用形式化证明。但好处是好实现并且测试方便，而且避免了clight和rust反复转换的一系列问题（下一节介绍）。

### c语言 -> clight -> rustlight -> clight -> Asm
由于以前的工作已经完成了rustlight到clight再到Asm的全部流程，目前优先考虑使用如上编译链来完成。

但是，rustlight里面有很多东西是clight中没有的，比如从clight到rustlight的过程中，引入了Pparen,这种表达式在clight中并不存在。同时，rustlight中有着clight中没有的数据类型，比如数组切片（slice）。