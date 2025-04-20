use std::ptr::NonNull;

use crate::{Color, Node};

/// # Safety
///
/// It leaks; use with dealloc_node.
pub unsafe fn leak_alloc_node<K, V>(key: K, value: V) -> Option<NonNull<Node<K, V>>>
where
    K: Ord,
{
    let mut node = Node::new(key, value);
    node.set_color(Color::Black);
    NonNull::new(Box::into_raw(Box::new(node)))
}

/// # Safety
///
/// It drops; use after alloc_node.
pub unsafe fn own_back<K, V>(current: *mut Node<K, V>) -> Box<Node<K, V>> {
    unsafe { Box::from_raw(current) }
}
