fn cycle<'a, 'b, 'c, 'd>()
    where 'a: 'b, 'c: 'a, 'b: 'd, 'd: 'a
{
    return;
}

fn chain<'a, 'b, 'c>(x: &'a i32, y: &'b i32)
    where 'a: 'c, 'b: 'a
{
    return;
}

fn main() {
    return;
}
