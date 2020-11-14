# try-rwlock

`TryRwLock` is a lightweight readers-writer lock implemented with atomics that does not support
blocking.

A readers-writer lock allows multiple readers or one writer to access it at a time.

## See Also

[`try-lock`](https://crates.io/crates/try-lock) and
[`try-mutex`](https://crates.io/crates/try-mutex) provide a similar function to this, but
implement mutexes not readers-writer locks.

License: MIT OR Apache-2.0
