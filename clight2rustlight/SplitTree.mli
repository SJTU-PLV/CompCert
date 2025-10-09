open! Camlcoq
open! Rustlight

type ident = AST.ident

(**
 * 处理 C 指针运算, 例如 `new_ptr = base_ptr + offset`。
 *
 * @param base_ptr_id  C 语言中基数组/指针的标识符。
 * @param new_ptr_id   被赋值的新的 C 指针的标识符。
 * @param c_offset     从基指针开始的字节偏移量。
 * @param array_size   基数组的总大小（以字节为单位），仅在首次操作此基指针时需要。
 * @return             一个 Rustlight.statement，它是一系列 `split_at_mut` 调用。
 * 此函数还会将 `new_ptr_id` 到新的 Rust 临时变量的映射关系
 * 记录在内部状态中，以备后续赋值。
 *)
val find_and_split : ident -> ident -> Z.t -> Z.t -> statement

(**
 * 为在语句中被访问的变量刷新待定的赋值。
 *
 * 在翻译任何可能访问数组的 Clight 语句之前，应调用此函数。
 * 它会检查 `vars` 列表中的每个变量是否是指向受管理的数组的指针。
 * 如果是，它将生成所有待定的赋值语句（例如 `a = _5; b = _6;`），
 * 然后销毁相应的 split tree，因为数组即将被直接访问，分裂出的切片无效了。
 *
 * @param vars 语句中出现的所有变量的列表。
 * @return     一个 Rustlight.statement，它是一系列赋值语句，如果无需刷新则为 Sskip。
 *)
(* val flush_and_destroy_for_vars : ident list -> statement *)

val flush_assignments_for_vars : ident list -> statement

(**
 * 检查一个 C 变量是否是当前被 SplitTree 管理的基指针。
 *)
val is_base_ptr_managed : ident -> bool

(**
 * 为对基指针的直接访问（如 `abcd[10]`）解析出正确的切片变量和相对偏移量。
 * @return (新的切片变量名, 新的相对偏移量)
 *)
val resolve_direct_access : ident -> Z.t -> (ident * Z.t)