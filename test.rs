struct Test ;
struct Test {
  u32 a;
  u32 b;
};

unsafe extern "C" { fn __compcert_va_int32(_ : &mut  [std::ffi::c_void]) -> u32; }
unsafe extern "C" { fn __compcert_va_int64(_ : &mut  [std::ffi::c_void]) -> u64; }
unsafe extern "C" { fn __compcert_va_float64(_ : &mut  [std::ffi::c_void]) -> f64; }
unsafe extern "C" { fn __compcert_va_composite(_ : &mut  [std::ffi::c_void], _ : u64) -> &mut  [std::ffi::c_void]; }
unsafe extern "C" { fn __compcert_i64_dtos(_ : f64) -> i64; }
unsafe extern "C" { fn __compcert_i64_dtou(_ : f64) -> u64; }
unsafe extern "C" { fn __compcert_i64_stod(_ : i64) -> f64; }
unsafe extern "C" { fn __compcert_i64_utod(_ : u64) -> f64; }
unsafe extern "C" { fn __compcert_i64_stof(_ : i64) -> f32; }
unsafe extern "C" { fn __compcert_i64_utof(_ : u64) -> f32; }
unsafe extern "C" { fn __compcert_i64_sdiv(_ : i64, _ : i64) -> i64; }
unsafe extern "C" { fn __compcert_i64_udiv(_ : u64, _ : u64) -> u64; }
unsafe extern "C" { fn __compcert_i64_smod(_ : i64, _ : i64) -> i64; }
unsafe extern "C" { fn __compcert_i64_umod(_ : u64, _ : u64) -> u64; }
unsafe extern "C" { fn __compcert_i64_shl(_ : i64, _ : i32) -> i64; }
unsafe extern "C" { fn __compcert_i64_shr(_ : u64, _ : i32) -> u64; }
unsafe extern "C" { fn __compcert_i64_sar(_ : i64, _ : i32) -> i64; }
unsafe extern "C" { fn __compcert_i64_smulh(_ : i64, _ : i64) -> i64; }
unsafe extern "C" { fn __compcert_i64_umulh(_ : u64, _ : u64) -> u64; }
unsafe extern "C" { fn __builtin_debug(_ : i32, ...); }
unsafe extern "C" { fn printf(_ : &mut  [i8], ...) -> i32; }
const __stringlit_1 : [i8;4] = [    b'%' as i8,
    b'd' as i8,
    b'\n' as i8,
    b'\0' as i8
];

fn main()
{
  
   let mut t : &mut  [struct Test];
   let mut _128 : &mut  [std::ffi::c_void];
   let mut _10002 : i32 /*this is unit */;
   let mut _10001 : i32 /*this is unit */;
   let mut _10000 : i32 /*this is unit */;
   _128 = malloc(::core::mem::size_of::<struct Test>() as u64);
   t = (_128 as &mut  [struct Test]);
   t.a = 1;
   t.b = 2;
   _10000 = printf(__stringlit_1.as_ptr() as &mut  [i8], t.a);
   _10001 = printf(__stringlit_1.as_ptr() as &mut  [i8], t.b);
   _10002 = free(t as &mut  [std::ffi::c_void]);
}


