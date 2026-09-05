use std::ptr::NonNull;

use super::Link;
use crate::Color;

/// Bridges a [`Link`] embedded inside a `Value` back to the containing
/// `Value`; the same job the Linux kernel's `container_of()` macro does for
/// a `struct rb_node`.
///
/// # Safety
///
/// Implementors must guarantee that [`Adapter::link_offset`] is the exact
/// byte offset, within `Self::Value`, of a field of type [`Link`], i.e. for
/// any pointer `v: NonNull<Self::Value>` that points at a live `Self::Value`,
/// `v.byte_add(Self::link_offset())` must point at a live `Link` embedded in
/// that same value. Prefer [`crate::intrusive_adapter!`] over implementing
/// this by hand.
pub unsafe trait Adapter {
    /// The struct that embeds a [`Link`].
    type Value;

    /// The byte offset of the embedded [`Link`] field within `Self::Value`.
    fn link_offset() -> usize;

    /// Converts a pointer to a `Value` into a pointer to its embedded
    /// `Link`.
    ///
    /// # Safety
    ///
    /// `value` must point at a live, properly aligned `Self::Value`.
    #[inline]
    unsafe fn get_link(value: NonNull<Self::Value>) -> NonNull<Link> {
        // SAFETY: the caller guarantees `value` is live and properly
        // aligned; the `Adapter` impl guarantees `link_offset()` is the true
        // byte offset of an embedded `Link` within it.
        unsafe { NonNull::new_unchecked(value.as_ptr().byte_add(Self::link_offset())).cast() }
    }

    /// Converts a pointer to an embedded `Link` back to a pointer to its
    /// containing `Value`. This is the `container_of()` direction.
    ///
    /// # Safety
    ///
    /// `link` must point at a `Link` embedded at `Self::link_offset()`
    /// inside a live, properly aligned `Self::Value`.
    #[inline]
    unsafe fn get_value(link: NonNull<Link>) -> NonNull<Self::Value> {
        // SAFETY: the caller guarantees `link` sits exactly `link_offset()`
        // bytes into a live `Self::Value`, so subtracting that offset
        // recovers the value's address.
        unsafe { NonNull::new_unchecked(link.as_ptr().byte_sub(Self::link_offset())).cast() }
    }

    // --- Tree navigation, at the `Value` level. ---
    //
    // These mirror `Node<K, V>`'s own `left()`/`right()`/`parent()`/etc.,
    // giving intrusive trees the same ergonomics without exposing `Link`'s
    // own (crate-internal) pointer-chasing primitives.

    /// `value`'s left child, if any.
    ///
    /// # Safety
    ///
    /// `value` must point at a live `Self::Value` that is (or, until this
    /// call returns, was) linked into a tree via this `Adapter`.
    #[inline]
    unsafe fn left(value: NonNull<Self::Value>) -> Option<NonNull<Self::Value>> {
        // SAFETY: delegated to the caller.
        unsafe { Link::left(Self::get_link(value)) }.map(|l| unsafe { Self::get_value(l) })
    }

    /// `value`'s right child, if any.
    ///
    /// # Safety
    ///
    /// Same contract as [`Adapter::left`].
    #[inline]
    unsafe fn right(value: NonNull<Self::Value>) -> Option<NonNull<Self::Value>> {
        // SAFETY: delegated to the caller.
        unsafe { Link::right(Self::get_link(value)) }.map(|l| unsafe { Self::get_value(l) })
    }

    /// `value`'s parent, if any (`None` at the root).
    ///
    /// # Safety
    ///
    /// Same contract as [`Adapter::left`].
    #[inline]
    unsafe fn parent(value: NonNull<Self::Value>) -> Option<NonNull<Self::Value>> {
        // SAFETY: delegated to the caller.
        unsafe { Link::parent(Self::get_link(value)) }.map(|l| unsafe { Self::get_value(l) })
    }

    /// `value`'s in-order successor, if any.
    ///
    /// # Safety
    ///
    /// Same contract as [`Adapter::left`].
    #[inline]
    unsafe fn next(value: NonNull<Self::Value>) -> Option<NonNull<Self::Value>> {
        // SAFETY: delegated to the caller.
        unsafe { Link::next(Self::get_link(value)) }.map(|l| unsafe { Self::get_value(l) })
    }

    /// `value`'s in-order predecessor, if any.
    ///
    /// # Safety
    ///
    /// Same contract as [`Adapter::left`].
    #[inline]
    unsafe fn prev(value: NonNull<Self::Value>) -> Option<NonNull<Self::Value>> {
        // SAFETY: delegated to the caller.
        unsafe { Link::prev(Self::get_link(value)) }.map(|l| unsafe { Self::get_value(l) })
    }

    /// Sets `value`'s color directly, without rebalancing.
    ///
    /// The one case a correct caller needs this for: the very first node
    /// inserted into an empty tree has no rebalancing to do, but still must
    /// be colored black (mirroring [`crate::Node`]'s own containers, which
    /// color a freshly leaked root black before ever calling
    /// [`crate::Root::insert`]).
    ///
    /// # Safety
    ///
    /// `value` must point at a live `Self::Value`.
    #[inline]
    unsafe fn set_color(value: NonNull<Self::Value>, color: Color) {
        // SAFETY: delegated to the caller.
        unsafe { Link::set_color(Self::get_link(value), color) }
    }
}

/// Generates a zero-sized [`Adapter`] type bound to one [`Link`] field of a
/// struct.
///
/// A struct may embed more than one `Link` (to belong to more than one
/// intrusive tree at once).
///
/// ```
/// use rougenoir::{intrusive::Link, intrusive_adapter};
///
/// struct MyObj {
///     link: Link,
///     value: i32,
/// }
///
/// intrusive_adapter!(MyObjAdapter = MyObj: link);
/// ```
///
/// The value type can be generic too.
///
/// ```
/// use rougenoir::{intrusive::Link, intrusive_adapter};
///
/// struct MyGenericObj<K, V> {
///     link: Link,
///     key: K,
///     value: V,
/// }
///
/// intrusive_adapter!(MyGenericObjAdapter<K, V> = MyGenericObj<K, V>: link);
/// ```
#[macro_export]
macro_rules! intrusive_adapter {
    ($(#[$attr:meta])* $vis:vis $name:ident = $value:ty : $field:ident) => {
        $(#[$attr])*
        $vis struct $name;

        // Fails to compile unless `$field` really has type `Link`.
        const _: fn(&$value) -> &$crate::intrusive::Link = |v| &v.$field;

        // SAFETY: the assertion above ensures `$field` is a genuine `Link`
        // field of `$value`; `core::mem::offset_of!` computes its true byte
        // offset within `$value`.
        unsafe impl $crate::intrusive::Adapter for $name {
            type Value = $value;

            #[inline]
            fn link_offset() -> usize {
                ::core::mem::offset_of!($value, $field)
            }
        }
    };

    ($(#[$attr:meta])* $vis:vis $name:ident<$($gen:ident),+ $(,)?> = $value:ty : $field:ident) => {
        $(#[$attr])*
        $vis struct $name<$($gen),+>(::core::marker::PhantomData<($($gen,)+)>);

        // SAFETY: the assertion inside `link_offset` below ensures `$field`
        // is a genuine `Link` field of `$value`; `core::mem::offset_of!`
        // computes its true byte offset within `$value`.
        unsafe impl<$($gen),+> $crate::intrusive::Adapter for $name<$($gen),+> {
            type Value = $value;

            #[inline]
            fn link_offset() -> usize {
                // Fails to compile unless `$field` really has type `Link`.
                // (Unlike the non-generic arm above, this can't be a
                // top-level `const _: ...` — free consts can't be generic —
                // so the check lives here, inside a function that already
                // is.)
                let _: fn(&$value) -> &$crate::intrusive::Link = |v| &v.$field;
                ::core::mem::offset_of!($value, $field)
            }
        }
    };
}

#[cfg(test)]
mod test {
    use std::ptr::NonNull;

    use super::*;

    #[allow(dead_code)]
    struct Employee {
        by_id: Link,
        by_name: Link,
        id: u32,
        name: &'static str,
    }

    intrusive_adapter!(ByIdAdapter = Employee: by_id);
    intrusive_adapter!(ByNameAdapter = Employee: by_name);

    #[test]
    fn round_trips_through_a_single_link_field() {
        let mut employee = Box::new(Employee {
            by_id: Link::new(),
            by_name: Link::new(),
            id: 1,
            name: "ada",
        });
        let ptr = NonNull::from(&mut *employee);

        // SAFETY: ptr points at a live Employee for the duration of this test.
        unsafe {
            let link = ByIdAdapter::get_link(ptr);
            assert_eq!(ByIdAdapter::get_value(link), ptr);
        }
    }

    #[test]
    fn distinguishes_multiple_link_fields_on_the_same_struct() {
        let mut employee = Box::new(Employee {
            by_id: Link::new(),
            by_name: Link::new(),
            id: 2,
            name: "bob",
        });
        let ptr = NonNull::from(&mut *employee);

        // SAFETY: ptr points at a live Employee for the duration of this test.
        unsafe {
            let id_link = ByIdAdapter::get_link(ptr);
            let name_link = ByNameAdapter::get_link(ptr);

            assert_ne!(id_link, name_link);
            assert_eq!(ByIdAdapter::get_value(id_link), ptr);
            assert_eq!(ByNameAdapter::get_value(name_link), ptr);
        }
    }

    #[test]
    fn link_offset_matches_field_layout() {
        assert_eq!(
            ByIdAdapter::link_offset(),
            std::mem::offset_of!(Employee, by_id)
        );
        assert_eq!(
            ByNameAdapter::link_offset(),
            std::mem::offset_of!(Employee, by_name)
        );
    }

    #[allow(dead_code)]
    struct Pair<K, V> {
        link: Link,
        key: K,
        value: V,
    }

    intrusive_adapter!(PairAdapter<K, V> = Pair<K, V>: link);

    #[test]
    fn generic_value_types_round_trip_too() {
        let mut pair = Box::new(Pair {
            link: Link::new(),
            key: 1u32,
            value: "one",
        });
        let ptr = NonNull::from(&mut *pair);

        assert_eq!(
            PairAdapter::<u32, &str>::link_offset(),
            std::mem::offset_of!(Pair<u32, &str>, link)
        );

        // SAFETY: ptr points at a live Pair<u32, &str> for the duration of
        // this test.
        unsafe {
            let link = PairAdapter::<u32, &str>::get_link(ptr);
            assert_eq!(PairAdapter::<u32, &str>::get_value(link), ptr);
        }
    }
}
