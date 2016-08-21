AtomicPtr with stamp to avoid [ABA problem](https://en.wikipedia.org/wiki/ABA_problem)  
======================================================================================

## Usage

Put this in your `Cargo.toml`:

```toml
[dependencies]
atomic-stamped-ptr = "0.1.0"
```

And this in your crate root:

```rust
extern crate atomic_stamped_ptr;
```

## Getting Started

#### Store pointer into AtomicStampedPtr atomicity:

```rust
let a = AtomicStampedPtr::new(ptr);
```

Or

```rust
a.store(ptr);
```

#### Get pointer and version from AtomicStampedPtr atomicity:
```
let (ptr, version) = a.load();
```

#### Swap pointer with AtomicStampedPtr atomicity:
```
let new_ptr = a.swap(ptr);
```

#### Compare and swap:
```
let (p, v) = a.compare_and_swap((ptr, version), new_ptr);
if (p, v) == (ptr, version) {
    // Success
} else {
    // Failure
}
```

#### Comapre and exchange:
```
if let Ok((p, v)) == a.compare_exchange((ptr, version), new_ptr) {
    // Success
} else {
    // Failure
}
```
