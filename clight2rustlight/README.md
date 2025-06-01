# 项目流程

目前已完成： c语言 -> clight -> rustlight

目标: c语言 -> clight -> rustlight __->__ Asm

## 不同的编译链的选择
### rustlight -> Asm（直接转）
这个步骤需要的工作量太多，目前还没有开始实现。

但是可以考虑使用编译链：c语言 -> clight -> rustlight -> rust，然后使用rust编译器再到Asm。

已经大致实现，但从rust到Asm的这一段步骤使用的是编译器，因此没有使用形式化证明。但好处是好实现并且测试方便，而且避免了clight和rust反复转换的一系列问题（下一节介绍）。

### c语言 -> clight -> rustlight -> clight -> Asm
由于以前的工作已经完成了rustlight到clight再到Asm的全部流程，目前优先考虑使用如上编译链来完成。

但是，rustlight里面有很多东西是clight中没有的，比如从clight到rustlight的过程中，引入了Pparen,这种表达式在clight中并不存在。同时，rustlight中有着clight中没有的数据类型，比如数组切片（slice）。未来会逐渐支持这些类型，表达式或者是语句的转换。

目前大部分c代码已经可以通过这个编译链成功编译出可执行文件。__但需注意：__  若使用macos，当使用math.h文件，需要在其前面加上#define _Float16 double或者#define _Float16 float。因为编译链目前不支持这种类型。

## 核心文件：Clight2Rustlight.v
这个文件负责将clight中间代码转换为rustlight中间代码。
具体使用函数transl_program，在这个函数中我记录了所有产生的必要的临时id，并将其记录进对应rustlight函数的fvar。值得注意的是，为了通过clightgen对malloc和free的检测，若程序中没有malloc和free的全局id，则我会将其加入。其它地方就和别的中间代码转换逻辑类似，使用辅助函数transl_def来转换每一个全局定义。这里定义这个辅助函数而不用通用的程序转换函数是因为，我想记录main函数的id，因为main函数需要特殊处理。

transl_program间接使用了transl_function，这个函数和其它中间代码转换的transl_function最大的不同就是这里对main函数进行特殊处理。c语言中，main函数返回类型是int，但rust中main函数没有返回值，这里做出修改，改动返回值并且删除最后的return 0，同时应该在clightgen中加入相反逻辑，保证rust也将main函数转换为正确的rust中的main函数。其它需要注意的是，rustlight没有fn_temps,因此在这里将clight的fn_vars和fn_temps和新加入的必要临时变量gen_trail都转换为rustlight的fn_vars。

接下来是transl_stmt,这个函数目前还不支持switch语句，但以后会考虑加入。其它值得一提的是，这里的函数调用和返回语句都会生成一个必要的临时变量，在rustlight中称为place表达式，它是一个左值，用来保存函数返回值和作为临时变量返回。之所以必要，是因为框架中中间语言rustlight的Scall和Sreturn都必须要拥有一个place表达式。

最后就是要把clight的表达式转换为rustlight中的place或者pexpr两种表达式了。这里值得注意的是，为了支持clight中的指针运算的转换，我将a[1],即clight中的*（a+1）转换为rustlight中的place表达式PparenPparenthesize。具体定义如下
```
PparenPparenthesize: ident -> type -> list ((int * type) * 
    (ident * type) * (binary_operation * type) * pmark) -> place
```
我将clight的二元表达式，转换成了波兰表达式（前缀算法），这样就可以方便地将*（a+1）转换成rust中的*b.as_mut_ptr().offset(1)。至于更复杂的，b[((a+c+2)|2)<<3]被转换成*b.as_mut_ptr().offset(((((a+c)+2)|2)<<3))。然后，我在clightgen中将这种波兰表达式又还原成了clight的中缀表达式。