extern crate atomic_stamped_ptr;

fn main() {
    use atomic_stamped_ptr::AtomicStampedPtr;

    let p1 = Box::into_raw(Box::new(1));
    let p2 = Box::into_raw(Box::new(2));
    let a = AtomicStampedPtr::new(p1);
    let b1 = unsafe { Box::from_raw(a.swap(p2)) };
    let b2 = unsafe { Box::from_raw(a.load()) };
    assert_eq!(*b1, 1);
    assert_eq!(*b2, 2);    
}
