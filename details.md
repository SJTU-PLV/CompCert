最终解决方案总结
### 问题1（类型转换问题，尤其是bool和int之间的类型转换）
问题分析
test.c 的问题：有真正的 bool 类型变量 a，需要正确的 bool/int 转换
perlin.c 的问题：C 的 _Bool 类型（IBool）被用作整数，在不同上下文中类型标记不一致
关键修复
1. PrintRustsyntax.ml - 统一 IBool 的类型名称：
```
let name_inttype_for_var sz sg =
  match sz, sg with
  | Ctypes.IBool, _ -> "i32"  (* C 的 _Bool 可以作为整数使用 *)
  | _ -> name_inttype sz sg
```
2. PrintRustlight.ml - 智能处理 bool/int 转换：
bool → bool: 直接赋值
int → bool: 使用 != 0 （Rust 不允许 i32 as bool）
bool → int: 使用 as i32
int → int: 使用 as <type>
3. 增强比较表达式识别：递归识别通过 cast 和括号包裹的比较表达式