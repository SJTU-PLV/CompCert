#![allow(dead_code)]
use std::cell::RefCell;
use std::convert::TryFrom;
use std::mem::{self, MaybeUninit};
use std::ptr::{self, NonNull};
use std::rc::Rc;

pub type CPtr<T> = *mut T;
pub type CConstPtr<T> = *const T;

pub enum PtrOwner<T> {
    Heap(Rc<RefCell<Box<[T]>>>),
    Borrowed {
        base: NonNull<T>,
        len: usize,
        borrow_flag: Rc<RefCell<()>>,
    },
    Null,
}

pub struct Ptr<T> {
    owner: PtrOwner<T>,
    offset: isize,
    len: Option<usize>,
}

impl<T> PartialEq for Ptr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl<T> Eq for Ptr<T> {}

impl<T> Clone for PtrOwner<T> {
    fn clone(&self) -> Self {
        match self {
            PtrOwner::Heap(rc) => PtrOwner::Heap(rc.clone()),
            PtrOwner::Borrowed {
                base,
                len,
                borrow_flag,
            } => PtrOwner::Borrowed {
                base: *base,
                len: *len,
                borrow_flag: borrow_flag.clone(),
            },
            PtrOwner::Null => PtrOwner::Null,
        }
    }
}

impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        Ptr {
            owner: self.owner.clone(),
            offset: self.offset,
            len: self.len,
        }
    }
}

pub trait ArrayPtrOps<T> {
    fn load(&self, idx: usize) -> T
    where
        T: Copy;
    fn store(&mut self, idx: usize, val: T);
}

impl<T: Copy, const N: usize> ArrayPtrOps<T> for [T; N] {
    fn load(&self, idx: usize) -> T {
        self[idx]
    }

    fn store(&mut self, idx: usize, val: T) {
        self[idx] = val;
    }
}

impl<T> Ptr<T> {
    pub const fn null() -> Self {
        Ptr {
            owner: PtrOwner::Null,
            offset: 0,
            len: Some(0),
        }
    }

    pub fn alloc(n: usize) -> Self
    where
        T: Default + Clone,
    {
        let b = vec![T::default(); n].into_boxed_slice();
        Ptr {
            owner: PtrOwner::Heap(Rc::new(RefCell::new(b))),
            offset: 0,
            len: Some(n),
        }
    }

    pub fn from_ref(slice: &mut [T]) -> Self {
        let len = slice.len();
        let base = NonNull::new(slice.as_mut_ptr()).expect("slice pointer");
        Ptr {
            owner: PtrOwner::Borrowed {
                base,
                len,
                borrow_flag: Rc::new(RefCell::new(())),
            },
            offset: 0,
            len: Some(len),
        }
    }

    pub fn from_ref_const(slice: &[T]) -> Self {
        let len = slice.len();
        let base = unsafe { NonNull::new_unchecked(slice.as_ptr() as *mut T) };
        Ptr {
            owner: PtrOwner::Borrowed {
                base,
                len,
                borrow_flag: Rc::new(RefCell::new(())),
            },
            offset: 0,
            len: Some(len),
        }
    }

    pub fn from_mut(value: &mut T) -> Self {
        let slice = std::slice::from_mut(value);
        Self::from_ref(slice)
    }

    pub fn from_raw_parts(ptr: *mut T, len: usize) -> Self {
        match NonNull::new(ptr) {
            Some(base) => Ptr {
                owner: PtrOwner::Borrowed {
                    base,
                    len,
                    borrow_flag: Rc::new(RefCell::new(())),
                },
                offset: 0,
                len: Some(len),
            },
            None => Ptr::null(),
        }
    }

    pub fn from_c_ptr(ptr: CPtr<T>, len: usize) -> Self {
        Self::from_raw_parts(ptr, len)
    }

    pub fn from_c_const_ptr(ptr: CConstPtr<T>, len: usize) -> Self {
        Self::from_raw_parts(ptr as *mut T, len)
    }

    fn actual_index(&self, idx: usize) -> usize {
        let idx_isize = isize::try_from(idx).expect("index overflow");
        let actual = self
            .offset
            .checked_add(idx_isize)
            .expect("pointer offset overflow");
        assert!(actual >= 0, "pointer index before allocation start");
        let len = self.len.expect("missing length information for bounds check");
        assert!(
            (actual as usize) < len,
            "pointer index out of bounds: idx={} actual={} len={} offset={}",
            idx,
            actual,
            len,
            self.offset
        );
        actual as usize
    }

    fn signed_index(&self, idx: usize) -> isize {
        let idx_isize = isize::try_from(idx).expect("index overflow");
        self.offset
            .checked_add(idx_isize)
            .expect("pointer offset overflow")
    }

    pub fn is_null(&self) -> bool {
        matches!(self.owner, PtrOwner::Null)
    }

    pub fn add(&self, k: usize) -> Self {
        self.offset(k as isize)
    }

    pub fn offset(&self, delta: isize) -> Self {
        let new_offset = self
            .offset
            .checked_add(delta)
            .expect("pointer offset overflow");
        Ptr {
            owner: self.owner.clone(),
            offset: new_offset,
            len: self.len,
        }
    }

    pub fn store(&self, idx: usize, val: T) {
        match &self.owner {
            PtrOwner::Heap(rc) => {
                let actual = self.actual_index(idx);
                let mut borrowed = rc.borrow_mut();
                borrowed[actual] = val;
            }
            PtrOwner::Borrowed {
                base,
                len,
                borrow_flag,
            } => {
                let _guard = borrow_flag.borrow_mut();
                let signed = self.signed_index(idx);
                assert!(signed >= 0, "pointer index before allocation start");
                let bound_len = self.len.unwrap_or(*len);
                assert!(
                    (signed as usize) < bound_len,
                    "pointer index out of bounds: idx={} actual={} len={} offset={}",
                    idx,
                    signed,
                    bound_len,
                    self.offset
                );
                unsafe {
                    let slot = base.as_ptr().offset(signed);
                    ptr::write(slot, val);
                }
            }
            PtrOwner::Null => panic!("store through NULL ptr"),
        }
    }

    pub fn load(&self, idx: usize) -> T
    where
        T: Clone,
    {
        match &self.owner {
            PtrOwner::Heap(rc) => {
                let actual = self.actual_index(idx);
                let borrowed = rc.borrow();
                borrowed[actual].clone()
            }
            PtrOwner::Borrowed {
                base,
                len,
                borrow_flag,
            } => {
                let _guard = borrow_flag.borrow();
                let signed = self.signed_index(idx);
                assert!(signed >= 0, "pointer index before allocation start");
                let bound_len = self.len.unwrap_or(*len);
                assert!(
                    (signed as usize) < bound_len,
                    "pointer index out of bounds: idx={} actual={} len={} offset={}",
                    idx,
                    signed,
                    bound_len,
                    self.offset
                );
                unsafe { (*base.as_ptr().offset(signed)).clone() }
            }
            PtrOwner::Null => {
                eprintln!(
                    "[ptr] null load @ idx={}, offset={}, len={:?}\nbacktrace:\n{:?}",
                    idx,
                    self.offset,
                    self.len,
                    std::backtrace::Backtrace::force_capture()
                );
                panic!("load through NULL ptr")
            }
        }
    }

    pub fn with_ref<R>(&self, idx: usize, f: impl FnOnce(&T) -> R) -> R {
        match &self.owner {
            PtrOwner::Heap(rc) => {
                let actual = self.actual_index(idx);
                let borrowed = rc.borrow();
                f(&borrowed[actual])
            }
            PtrOwner::Borrowed {
                base,
                len,
                borrow_flag,
            } => {
                let _guard = borrow_flag.borrow();
                let signed = self.signed_index(idx);
                assert!(signed >= 0, "pointer index before allocation start");
                let bound_len = self.len.unwrap_or(*len);
                assert!(
                    (signed as usize) < bound_len,
                    "pointer index out of bounds: idx={} actual={} len={} offset={}",
                    idx,
                    signed,
                    bound_len,
                    self.offset
                );
                unsafe { f(&*base.as_ptr().offset(signed)) }
            }
            PtrOwner::Null => {
                eprintln!(
                    "[ptr] null load @ idx={}, offset={}, len={:?}\nbacktrace:\n{:?}",
                    idx,
                    self.offset,
                    self.len,
                    std::backtrace::Backtrace::force_capture()
                );
                panic!("load through NULL ptr")
            }
        }
    }

    pub fn with_mut<R>(&self, idx: usize, f: impl FnOnce(&mut T) -> R) -> R {
        match &self.owner {
            PtrOwner::Heap(rc) => {
                let actual = self.actual_index(idx);
                let mut borrowed = rc.borrow_mut();
                f(&mut borrowed[actual])
            }
            PtrOwner::Borrowed {
                base,
                len,
                borrow_flag,
            } => {
                let _guard = borrow_flag.borrow_mut();
                let signed = self.signed_index(idx);
                assert!(signed >= 0, "pointer index before allocation start");
                let bound_len = self.len.unwrap_or(*len);
                assert!(
                    (signed as usize) < bound_len,
                    "pointer index out of bounds: idx={} actual={} len={} offset={}",
                    idx,
                    signed,
                    bound_len,
                    self.offset
                );
                unsafe { f(&mut *base.as_ptr().offset(signed)) }
            }
            PtrOwner::Null => panic!("store through NULL ptr"),
        }
    }

    pub fn free(&mut self) {
        match &self.owner {
            PtrOwner::Heap(_) => {
                self.owner = PtrOwner::Null;
                self.offset = 0;
                self.len = Some(0);
            }
            PtrOwner::Borrowed { .. } => panic!("free on borrowed pointer"),
            PtrOwner::Null => {}
        }
    }

    pub fn as_ptr(&self) -> *const T {
        match &self.owner {
            PtrOwner::Heap(rc) => {
                let len = self.len.expect("missing length information for bounds check");
                assert!(self.offset >= 0, "negative offset raw pointer");
                assert!(
                    (self.offset as usize) < len,
                    "pointer offset out of bounds: offset={} len={}",
                    self.offset,
                    len
                );
                let borrowed = rc.borrow();
                unsafe { borrowed.as_ptr().add(self.offset as usize) }
            }
            PtrOwner::Borrowed { base, len, .. } => {
                let bound_len = self.len.unwrap_or(*len);
                assert!(self.offset >= 0, "negative offset raw pointer");
                assert!(
                    (self.offset as usize) < bound_len,
                    "pointer offset out of bounds: offset={} len={}",
                    self.offset,
                    bound_len
                );
                unsafe { base.as_ptr().add(self.offset as usize) }
            }
            PtrOwner::Null => std::ptr::null(),
        }
    }

    pub fn as_mut_ptr(&self) -> *mut T {
        self.as_ptr() as *mut T
    }

    pub fn c_ptr(&self) -> CPtr<T> {
        self.as_mut_ptr()
    }

    pub fn c_const_ptr(&self) -> CConstPtr<T> {
        self.as_ptr()
    }

    pub fn len(&self) -> Option<usize> {
        self.len.map(|total| {
            if self.offset >= 0 {
                total.saturating_sub(self.offset as usize)
            } else {
                total.saturating_add((-self.offset) as usize)
            }
        })
    }

    /// The translator uses this to implement C-style pointer casts.
    ///
    /// Note: this is only sound if `U` is layout-compatible with `T` for all
    /// subsequent loads/stores performed through the resulting pointer.
    pub fn cast<U>(&self) -> Ptr<U> {
        unsafe { mem::transmute(self.clone()) }
    }
}

impl<T, const N: usize> Ptr<[T; N]> {
    pub fn row(&self, idx: usize) -> Ptr<T> {
        if let PtrOwner::Null = self.owner {
            return Ptr::null();
        }
        let actual = self.actual_index(idx);
        let base_ptr: *mut T = match &self.owner {
            PtrOwner::Heap(rc) => {
                let borrowed = rc.borrow();
                let row_ptr = unsafe { borrowed.as_ptr().add(actual) as *mut [T; N] };
                let elem_ptr = unsafe { (*row_ptr).as_ptr() as *mut T };
                elem_ptr
            }
            PtrOwner::Borrowed { base, .. } => unsafe {
                let row_ptr = base.as_ptr().add(actual);
                (*row_ptr).as_ptr() as *mut T
            },
            PtrOwner::Null => std::ptr::null_mut(),
        };
        match NonNull::new(base_ptr) {
            Some(non_null) => Ptr {
                owner: PtrOwner::Borrowed {
                    base: non_null,
                    len: N,
                    borrow_flag: Rc::new(RefCell::new(())),
                },
                offset: 0,
                len: Some(N),
            },
            None => Ptr::null(),
        }
    }
}

impl<T> Default for Ptr<T> {
    fn default() -> Self {
        Ptr::null()
    }
}

pub trait ArrayPtrExt<T> {
    fn offset(&mut self, delta: isize) -> Ptr<T>;
}

impl<T, const N: usize> ArrayPtrExt<T> for [T; N] {
    fn offset(&mut self, delta: isize) -> Ptr<T> {
        Ptr::from_ref(&mut self[..]).offset(delta)
    }
}

pub trait ArrayPtrCastExt {
    fn cast<U>(&self) -> Ptr<U>;
}

impl<T, const N: usize> ArrayPtrCastExt for [T; N] {
    fn cast<U>(&self) -> Ptr<U> {
        Ptr::from_raw_parts(self.as_ptr() as *mut U, N)
    }
}

pub fn array_default<T: Default, const N: usize>() -> [T; N] {
    let mut data: [MaybeUninit<T>; N] =
        unsafe { MaybeUninit::uninit().assume_init() };
    let mut i = 0;
    while i < N {
        data[i] = MaybeUninit::new(T::default());
        i += 1;
    }
    unsafe { ptr::read((&data as *const _ as *const [T; N])) }
}
