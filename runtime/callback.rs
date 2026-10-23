use crate::ptr::Ptr;
use std::cell::UnsafeCell;
use std::ffi::c_void;

pub struct CallbackSlot<T> {
    slot: UnsafeCell<Option<T>>,
}

impl<T> CallbackSlot<T> {
    pub const fn new() -> Self {
        CallbackSlot {
            slot: UnsafeCell::new(None),
        }
    }

    pub unsafe fn with_callback<F, R>(&self, cb: T, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let slot = self.slot.get();
        let prev = (*slot).take();
        *slot = Some(cb);
        let result = f();
        *slot = prev;
        result
    }

    pub unsafe fn current(&self) -> Option<T>
    where
        T: Clone,
    {
        (*self.slot.get()).clone()
    }
}

unsafe impl<T: Send> Sync for CallbackSlot<T> {}

pub type VoidComparator = extern "C" fn(Ptr<c_void>, Ptr<c_void>) -> i32;

pub static VOID_COMPARATOR_SLOT: CallbackSlot<VoidComparator> = CallbackSlot::new();

pub extern "C" fn void_comparator_trampoline(a: *const c_void, b: *const c_void) -> i32 {
    unsafe {
        match VOID_COMPARATOR_SLOT.current() {
        | Some(cb) => {
            let pa = Ptr::from_raw_parts(a as *mut c_void, 1);
            let pb = Ptr::from_raw_parts(b as *mut c_void, 1);
            cb(pa, pb)
          }
        | None => 0,
        }
    }
}

pub unsafe fn with_void_comparator<F, R>(cb: VoidComparator, f: F) -> R
where
    F: FnOnce() -> R,
{
    VOID_COMPARATOR_SLOT.with_callback(cb, f)
}
