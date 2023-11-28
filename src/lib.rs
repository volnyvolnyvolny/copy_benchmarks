/*
Copyright (C) 2023 Valentin Vasilev (3volny@gmail.com).
*/

/*
Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

#![doc = include_str!("../README.md")]
//#![feature(sized_type_properties)]

use std::mem::size_of;
use std::ptr;
use std::ptr::copy_nonoverlapping;
use std::slice;

/// # Reverse slice
///
/// Reverse slice `[p, p+count)`.
///
/// ## Safety
///
/// The specified range must be valid for reading and writing.
///
/// ## Example
///
/// ```text
///                 count = 7
/// [ 1  2  3  4  5  6  7  8  9 10 11]  // reverse slice
///            └─────────────────┘
/// [ 1  .  3 10  9  8  7  6  5  4 11]
/// ```
#[inline(always)]
pub unsafe fn reverse_slice<T>(p: *mut T, count: usize) {
    let slice = slice::from_raw_parts_mut(p, count);
    slice.reverse();
}

/// # Copy (overlapping)
///
/// Copy region `[src, src + count)` to `[dst, dst + count)` element by element.
///
/// Regions could overlap.
///
/// ## Safety
///
/// The specified range must be valid for reading and writing.
///
/// ## Examples
///
/// ```text
///      dst      src   count = 7
/// [ 1 :2  3  4 *A  B  C  D  E  F  G 12]  // copy -->
///      |        └────────|────────┘
///      └─────────────────┘
/// [ 1 :A  .  . *D  .  .  G  E  .  G 12]
/// ```
///
/// ```text
///      src      dst    count = 7
/// [ 1 *A  B  C :D  E  F  G 11 12 13 12]  // copy <--
///      └─────── |────────┘        |
///               └─────────────────┘
/// [ 1 *A  .  C :A  .  .  .  .  .  G 12]
/// ```
pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    #[inline(always)]
    unsafe fn _copy<T>(src: *const T, dst: *mut T, i: usize) {
        // SAFE: By precondition, `i` is in-bounds because it's below `count`
        let src = unsafe { src.add(i) };

        // SAFE: By precondition, `i` is in-bounds because it's below `count`
        let dst = unsafe { &mut *dst.add(i) };

        ptr::write(dst, ptr::read(src));
    }

    if src == dst {
        return;
    } else if src > dst {
        for i in 0..count {
            _copy(src, dst, i);
        }
    } else {
        for i in (0..count).rev() {
            _copy(src, dst, i);
        }
    }
}

/// # Copy (overlapping)
///
/// Copy region `[src, src + count)` to `[dst, dst + count)` byte by byte.
///
/// Regions could overlap.
///
/// ## Safety
///
/// The specified range must be valid for reading and writing.
pub unsafe fn byte_copy<T>(src: *const T, dst: *mut T, count: usize) {
    let src = src.cast::<u8>();
    let dst = dst.cast::<u8>();

    copy(src, dst, count * size_of::<T>());
}

/// # Copy (overlappihg)
///
/// Copy region `[src, src + count)` to `[dst, dst + count)` block by block.
///
/// Regions could overlap.
///
/// ## Safety
///
/// The specified range must be valid for reading and writing.
///
/// ## Example
///
/// ```text
///      src      dst    count = 13
/// [ 1 *A  B  C :D  E  F  G  H  I  J  K  L  M 15 16 17 18]  // copy block(3) <--
///      └─────── | ─────────────────────────┘        |
///               └───────────────────────────────────┘
/// [ 1  A  B  .  D  E  .  G  H  .  J  K  .  M  K  .  M 18]  // copy block
/// [ 1  .  .  .  .  E  .  G  H  .  J  H  .  .  .  .  M 18]  // copy block
/// [ 1  .  B  .  D  E  .  G  E  .  .  .  .  .  .  .  M 18]  // copy block
/// [ 1  .  B  .  D  B  .  .  .  .  .  .  .  .  .  .  M 18]  // copy rem(1)
/// [ 1 *A  B  C :A  .  .  .  .  .  .  .  .  .  .  .  M 18]
/// ```
pub unsafe fn block_copy<T>(src: *const T, dst: *mut T, count: usize) {
    let block_size = dst.offset_from(src).unsigned_abs();

    if src == dst {
        return;
    } else if block_size == 1 {
        copy(src, dst, count);
    } else if block_size > count {
        copy_nonoverlapping(src, dst, count);
    } else {
        let mut s = src;
        let mut d = dst;

        let rounds = count / block_size + 1;
        let rem = count % block_size;

        if src < dst {
            s = src.add(count);
            d = dst.add(count);

            for _ in 1..rounds {
                s = s.sub(block_size);
                d = d.sub(block_size);

                copy_nonoverlapping(s, d, block_size);
            }

            s = s.sub(rem);
            d = d.sub(rem);
            copy_nonoverlapping(s, d, rem);
        } else {
            for _ in 1..rounds {
                copy_nonoverlapping(s, d, block_size);

                s = s.add(block_size);
                d = d.add(block_size);
            }

            s = s.add(1);
            d = d.add(1);
            copy_nonoverlapping(s, d, rem);
        }
    }
}

/// # Shift left
///
/// Copy region `[mid, mid + count)` to `[mid - left, mid - left + count)`
/// element by element, via byte_copy or std::ptr::copy.
///
/// ## Safety
///
/// * The region `[mid       , mid        + count)` must be valid for reading;
/// * the region `[mid - left, mid - left + count)` must be valid for writing.
///
/// ## Example
///
/// ```text
///       <<mid, left = 1, count = 7
/// [ 1 :2 *A  B  C  D  E  F  G 10]
///         └─────────────────┘
/// [ 1 :A *B  .  .  .  .  G  G 10]
/// ```
pub unsafe fn shift_left<T>(left: usize, mid: *mut T, count: usize) {
    let start = mid.sub(left);

    if size_of::<T>() == size_of::<usize>() && count >= 15 {
        byte_copy(mid, start, count);
    } else if size_of::<T>() < 15 * size_of::<usize>() {
        copy(mid, start, count);
    } else {
        ptr::copy(mid, start, count);
    }
}

/// # Shift right
///
/// Copy region `[mid - count, mid)` to `[mid - count + right, mid + right)`
/// element by element, via byte_copy or std::ptr::copy.
///
/// ## Safety
///
/// * The region `[mid - count        , mid)` must be valid for reading;
/// * the region `[mid - count + right, mid + right)` must be valid for writing.
///
/// ## Example
///
/// ```text
///   count = 7
///      mid, right = 1>>
/// [ 1 *A :B  C  D  E  F  G 11 12]
///      └─────────────────┘
/// [ 1 *A :A  .  .  .  .  F  G 12]
/// ```
pub unsafe fn shift_right<T>(count: usize, mid: *mut T, right: usize) {
    let start = mid.sub(count);

    if size_of::<T>() == size_of::<usize>() && count >= 200 {
        byte_copy(start, start.add(right), count);
    } else if size_of::<T>() < 10 * size_of::<usize>() {
        copy(start, start.add(right), count);
    } else {
        byte_copy(start, start.add(right), count);
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    fn seq_multi<const N: usize>(size: usize) -> Vec<[usize; N]> {
        let mut v = vec![[0; N]; size];
        for i in 0..size {
            v[i] = [i + 1; N];
        }
        v
    }

    fn seq(size: usize) -> Vec<usize> {
        let mut v = vec![0; size];
        for i in 0..size {
            v[i] = i + 1;
        }
        v
    }

    fn prepare(len: usize, x: usize, y: usize) -> (Vec<usize>, (*mut usize, *mut usize)) {
        let mut v = seq(len);

        unsafe {
            let x = &v[..].as_mut_ptr().add(x - 1);
            let y = &v[..].as_mut_ptr().add(y - 1);

            (v, (x.clone(), y.clone()))
        }
    }

    #[test]
    fn copy_correct() {
        let (v, (src, dst)) = prepare(15, 4, 7);

        unsafe { copy(src, dst, 7) };

        let s = vec![1, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 9, 10, 14, 15];
        assert_eq!(v, s);

        let (v, (src, dst)) = prepare(15, 7, 4);

        unsafe { copy(src, dst, 6) };

        let s = vec![1, 2, 3, 7, 8, 9, 10, 11, 12, 10, 11, 12, 13, 14, 15];
        assert_eq!(v, s);
    }

    #[test]
    fn block_copy_correct() {
        let (v, (src, dst)) = prepare(15, 4, 7);

        unsafe { block_copy(src, dst, 7) };

        let s = vec![1, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 9, 10, 14, 15];
        assert_eq!(v, s);

        let (v, (src, dst)) = prepare(15, 7, 4);

        unsafe { block_copy(src, dst, 6) };

        let s = vec![1, 2, 3, 7, 8, 9, 10, 11, 12, 10, 11, 12, 13, 14, 15];
        assert_eq!(v, s);
    }

    #[test]
    fn byte_copy_correct() {
        let (v, (src, dst)) = prepare(15, 4, 7);

        unsafe { byte_copy(src, dst, 7) };

        let s = vec![1, 2, 3, 4, 5, 6, 4, 5, 6, 7, 8, 9, 10, 14, 15];
        assert_eq!(v, s);

        let (v, (src, dst)) = prepare(15, 7, 4);

        unsafe { byte_copy(src, dst, 6) };

        let s = vec![1, 2, 3, 7, 8, 9, 10, 11, 12, 10, 11, 12, 13, 14, 15];
        assert_eq!(v, s);
    }

    // Shifts:

    #[test]
    fn shift_left_correct() {
        let mut v = seq(15);
        let mut mid = *unsafe { &v[..].as_mut_ptr().add(3) };

        unsafe { shift_left(1, mid, 7) };

        assert_eq!(v, vec![1, 2, 4, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13, 14, 15]);

        mid = *unsafe { &v[..].as_mut_ptr().add(2) };

        unsafe { shift_left(1, mid, 7) };

        assert_eq!(v, vec![1, 4, 5, 6, 7, 8, 9, 10, 10, 10, 11, 12, 13, 14, 15]);

        v = seq(15);
        let mut mid = *unsafe { &v[..].as_mut_ptr().add(3) };

        unsafe { shift_left(1, mid, 7) };

        assert_eq!(v, vec![1, 2, 4, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13, 14, 15]);

        mid = *unsafe { &v[..].as_mut_ptr().add(2) };

        unsafe { shift_left(1, mid, 7) };

        assert_eq!(v, vec![1, 4, 5, 6, 7, 8, 9, 10, 10, 10, 11, 12, 13, 14, 15]);
    }

    #[test]
    fn shift_right_correct() {
        let mut v = seq(15);
        let mut src = *unsafe { &v[..].as_mut_ptr().add(3) };

        unsafe { shift_right(7, src.add(7), 1) };

        assert_eq!(v, vec![1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15]);

        src = *unsafe { &v[..].as_mut_ptr().add(4) };

        unsafe { shift_right(7, src.add(7), 1) };

        assert_eq!(v, vec![1, 2, 3, 4, 4, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15]);
    }

    #[test]
    fn shift_correct() {
        let mut v = seq_multi::<20>(15);
        let mut src = *unsafe { &v[..].as_mut_ptr().add(1) };

        unsafe { shift_left(1, src, 14) };

        assert_eq!(v[0..13], seq_multi::<20>(14)[1..14]);

        v = seq_multi::<20>(15);
        src = *&v[..].as_mut_ptr();

        unsafe { shift_right(14, src.add(14), 1) };
        assert_eq!(v[1..14], seq_multi::<20>(14)[0..13]);
    }
}
