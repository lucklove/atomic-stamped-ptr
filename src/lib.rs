//! AtomicStampedPtr

#![feature(asm)]
#![feature(test)]

extern crate test;

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
    /// let p = Box::into_raw(Box::new(0));
    /// let a = AtomicStampedPtr::new(p);
    /// assert_eq!(a.load(), (p, 0));
    /// ```
    pub fn load(&self) -> (*mut T, usize) {
        let mut current = PtrContainer::default();
        cas_ptr(self.p.get(), &mut current, PtrContainer::default());
        (current.ptr, current.version)
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
    /// assert_eq!(a.load(), (p, 1));
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
    /// let p1 = Box::into_raw(Box::new(1));
    /// let p2 = Box::into_raw(Box::new(2));
    /// let a = AtomicStampedPtr::new(p1);
    /// assert_eq!(a.swap(p2), p1);
    /// assert_eq!(a.load(), (p2, 1));
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
    /// let p1 = Box::into_raw(Box::new(1));
    /// let p2 = Box::into_raw(Box::new(2));
    /// let a = AtomicStampedPtr::new(p1);
    /// assert_eq!(a.compare_and_swap((p1, 0), p2), (p1, 0));
    /// assert_eq!(a.load(), (p2, 1));
    /// ```
    pub fn compare_and_swap(&self, current: (*mut T, usize), ptr: *mut T) -> (*mut T, usize) {
        let mut current = PtrContainer::new(current.0, current.1);
        let relief = PtrContainer::new(ptr, current.successor());
        cas_ptr(self.p.get(), &mut current, relief);
        (current.ptr, current.version)
    }

    /// Stores a value into AtomicStampedPtr if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// let p = Box::into_raw(Box::new(0));
    /// let a = AtomicStampedPtr::new(p);
    /// assert_eq!(a.compare_exchange((p, 1), p), Err((p, 0)));
    /// assert_eq!(a.compare_exchange((p, 0), p), Ok((p, 0)));
    /// ```
    pub fn compare_exchange(&self, current: (*mut T, usize), ptr: *mut T) -> Result<(*mut T, usize), (*mut T, usize)> {
        let mut current = PtrContainer::new(current.0, current.1);
        let relief = PtrContainer::new(ptr, current.successor());
        if cas_ptr(self.p.get(), &mut current, relief) {
            Ok((current.ptr, current.version))
        } else {
            Err((current.ptr, current.version))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{PtrContainer, AtomicStampedPtr, cas_ptr};
    use std::mem;
    use std::marker::Sync;
    use std::sync::Arc;
    use test::Bencher;

    struct T(i32);
    unsafe impl Sync for T {}

    #[test]
    fn test_cas_failure() {
        let a = PtrContainer{ptr: 233 as *mut i32, version: 0};
        let mut b = PtrContainer::<i32>::default();
        let c = PtrContainer::default();
        assert_eq!(cas_ptr(unsafe{mem::transmute(&a)}, &mut b, c), false);
        assert_eq!(a, b);
    }

    #[test]
    fn test_swap() {
        let a = Arc::new(AtomicStampedPtr::new(0 as *mut T));
        let threads = (1..10).map(|x| {
            let a = a.clone();
            ::std::thread::spawn(move || {
                let mut p = a.swap(x as *mut T);
                while p as usize != x - 1 {
                    p = a.swap(p);
                }
            })
        }).collect::<Vec<_>>();

        for t in threads {
            t.join().unwrap();
        }
    }

    #[test]
    fn test_compare_exchange() {
        let a = Arc::new(AtomicStampedPtr::new(0 as *mut T));
        let threads = (0..1000).map(|_| {
            let a = a.clone();
            ::std::thread::spawn(move || {
                let mut v = 0;
                while let Err((_, e)) = a.compare_exchange((0 as *mut T, v), 0 as *mut T) {
                    v = e;
                }
            })
        }).collect::<Vec<_>>();

        for t in threads {
            t.join().unwrap();
        }

        assert_eq!(a.load(), (0 as *mut T, 1000));
    }

    #[bench]
    fn bench_compare_exchange(r: &mut Bencher) {
        let a = Arc::new(AtomicStampedPtr::new(0 as *mut T));
        r.iter(|| {
            let _ = a.compare_exchange((0 as *mut T, 0), 0 as *mut T);
        });
    }
}