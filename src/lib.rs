//! AtomicStampedPtr

#![feature(asm)]

use std::cell::UnsafeCell;
use std::default::Default;

/// Main class
#[derive(Debug)]
pub struct AtomicStampedPtr<T> {
    p: UnsafeCell<PtrContainer<T>>,
}

unsafe impl<T> Send for AtomicStampedPtr<T> {}
unsafe impl<T> Sync for AtomicStampedPtr<T> {}

impl<T> std::cmp::PartialEq for AtomicStampedPtr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.p.get() == other.p.get()
    }
}

/// Helper class
#[derive(Debug)]
struct PtrContainer<T> {
    ptr: *mut T,
    version: usize,
}

impl<T> std::cmp::PartialEq for PtrContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr && self.version == other.version
    }
}

impl<T> PtrContainer<T> {
    fn new(ptr: *mut T, version: usize) -> Self {
        PtrContainer {
            ptr: ptr,
            version: version,
        }
    }

    fn successor(&self) -> usize {
        if self.version == std::usize::MAX {
            0
        } else {
            self.version + 1
        }
    }
}

impl<T> Default for PtrContainer<T> {
    fn default() -> Self {
        PtrContainer::new(std::ptr::null_mut(), 0)
    }
}

#[cfg(target_arch = "x86_64")]
fn cas_ptr<T>(src: *mut PtrContainer<T>, cmp: &mut PtrContainer<T>, with: PtrContainer<T>) -> bool {
    let result: bool;
    unsafe {
        asm!("
                lock cmpxchg16b $1
                setz $0
            "
             : "=q"(result), "+*m"(src), "+{rdx}"(cmp.version), "+{rax}"(cmp.ptr)
             : "{rcx}"(with.version), "{rbx}"(with.ptr)
             : "memory" "cc"
        );
    }
    result
}
 
impl<T> Default for AtomicStampedPtr<T> {
    fn default() -> Self {
        AtomicStampedPtr::new(std::ptr::null_mut())
    }
}

impl<T> AtomicStampedPtr<T> {
    /// Constructor
    pub fn new(p: *mut T) -> Self {
        AtomicStampedPtr {
            p: UnsafeCell::new(PtrContainer::new(p, 0)),
        }
    }

    /// Load inner ptr atomiclly
    /// 
    /// # Examples
    /// 
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// let p = Box::into_raw(Box::new(6));
    /// let a = AtomicStampedPtr::new(p);
    /// let b = unsafe { Box::from_raw(a.load()) };
    /// assert_eq!(*b, 6);
    /// ```
    pub fn load(&self) -> *mut T {
        let mut dummy = PtrContainer::default();
        cas_ptr(self.p.get(), &mut dummy, PtrContainer::default());
        dummy.ptr
    }

    /// Store a ptr into AtomicStampedPtr and set version to 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// let a = AtomicStampedPtr::default();
    /// let p = Box::into_raw(Box::new(233));
    /// a.store(p);
    /// let b = unsafe { Box::from_raw(a.load()) };
    /// assert_eq!(*b, 233);
    /// ```
    pub fn store(&self, ptr: *mut T) {
        self.swap(ptr);
    }

    /// Store a ptr into AtomicStampedPtr and return the old one.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// // FIXME: panic if delete this:
    /// assert_eq!(std::mem::size_of::<AtomicStampedPtr<i32>>(), 16);
    ///
    /// let p1 = Box::into_raw(Box::new(1));
    /// let p2 = Box::into_raw(Box::new(2));
    /// let a = AtomicStampedPtr::new(p1);
    /// let b1 = unsafe { Box::from_raw(a.swap(p2)) };
    /// let b2 = unsafe { Box::from_raw(a.load()) };
    /// assert_eq!(*b1, 1);
    /// assert_eq!(*b2, 2);
    /// ```  
    pub fn swap(&self, ptr: *mut T) -> *mut T {
        let mut current = PtrContainer::default();
        let mut successor = current.successor();
        while !cas_ptr(self.p.get(), &mut current, PtrContainer::new(ptr, successor)) {
            successor = current.successor();
        }
        current.ptr
    }

    /// Store a ptr into AtomicStampedPtr and return current value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was update.
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// // FIXME: panic if delete this:
    /// assert_eq!(std::mem::size_of::<AtomicStampedPtr<i32>>(), 16);
    ///
    /// let p1 = Box::into_raw(Box::new(1));
    /// let p2 = Box::into_raw(Box::new(2));
    /// let a = AtomicStampedPtr::new(p1);
    /// let b = AtomicStampedPtr::new(p1);
    /// let b1 = unsafe { Box::from_raw(a.compare_and_swap(&b, p2)) };
    /// let b2 = unsafe { Box::from_raw(a.load()) };
    /// assert_eq!(*b1, 1);
    /// assert_eq!(*b2, 2);
    /// ```
    pub fn compare_and_swap(&self, current: &AtomicStampedPtr<T>, ptr: *mut T) -> *mut T {
        let raw_ptr = current.p.get();
        let mut current = unsafe { PtrContainer::new((*raw_ptr).ptr, (*raw_ptr).version) };
        let relief = PtrContainer::new(ptr, current.successor());
        cas_ptr(self.p.get(), &mut current, relief);
        current.ptr
    }
}

#[cfg(test)]
mod tests {
    use super::{PtrContainer, AtomicStampedPtr, cas_ptr};
    use std::mem;
    #[test]
    fn test_cas_failure() {
        let a = PtrContainer{ptr: 233 as *mut i32, version: 0};
        let mut b = PtrContainer::<i32>::default();
        let c = PtrContainer::default();
        assert_eq!(cas_ptr(unsafe{mem::transmute(&a)}, &mut b, c), false);
        assert_eq!(a, b);
    }

    #[test]
    fn test_load() {
        let n = 5;
        let p = unsafe { mem::transmute(&n) };
        let a: AtomicStampedPtr<i32> = AtomicStampedPtr::new(p);
        assert_eq!(a.load(), p);
    }
}
