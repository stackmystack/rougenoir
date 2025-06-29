use crate::{Node, NodePtr};
use std::{marker::PhantomData, ptr::NonNull};

/// An iterator over shared references to `Node`s in in-order traversal.
pub struct NodeIter<'a, K, V> {
    current: NodePtr<K, V>,
    phantom: PhantomData<&'a Node<K, V>>,
}

/// An iterator over mutable references to `Node`s in in-order traversal.
pub struct NodeIterMut<'a, K, V> {
    current: NodePtr<K, V>,
    phantom: PhantomData<&'a mut Node<K, V>>,
}

impl<'a, K, V> Iterator for NodeIter<'a, K, V> {
    type Item = &'a Node<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        // Take the current `NonNull` pointer from `self.current`.
        // If `current` is `None`, the iteration is finished.
        let current_non_null = self.current.take()?;

        // SAFETY: `current_non_null` is guaranteed to be a valid `NonNull` pointer by the `NodeIter`'s
        // construction and prior `next` calls. We are about to create a shared reference `&'a Node<K, V>`.
        // The lifetime `'a` ensures that this reference is valid for as long as the iterator and its
        // underlying `Node` are valid.
        let current_node_ref = unsafe { current_non_null.as_ref() };

        // Calculate the next node in the sequence using `Node::next()`.
        // This operation only requires a shared reference to `current_node_ref`,
        // which we have, and does not modify the node.
        self.current = current_node_ref.next();

        // Return the shared reference to the current node.
        Some(current_node_ref)
    }
}

// Implement the `Iterator` trait for `NodeIterMut`.
impl<'a, K, V> Iterator for NodeIterMut<'a, K, V> {
    type Item = &'a mut Node<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut current_non_null = self.current.take()?;

        // To avoid aliasing issues when creating a mutable reference to `current_node_ref`,
        // we first calculate the `next` node's pointer by temporarily getting a shared
        // reference to the current node.
        // `Node::next()` only reads from the node's structure and its neighbors, so a
        // shared reference for this call is safe.
        // SAFETY: `current_non_null` is a valid `NonNull` pointer. We temporarily create
        // a shared reference to call `next()`. This is safe because `Node::next()` doesn't
        // modify the node, and we are not creating any mutable aliases at this point.
        let next_non_null = unsafe { current_non_null.as_ref() }.next();

        // Now, create the mutable reference to the `current` node to return.
        // SAFETY: `current_non_null` is a valid `NonNull` pointer, and we are now creating
        // a unique mutable reference (`&'a mut Node<K, V>`). This is the only mutable reference
        // to this specific node for its lifetime within this iterator step. `self.current`
        // has been `take()`n, ensuring no other mutable aliasing via the iterator's state.
        let current_node_mut_ref = unsafe { current_non_null.as_mut() };
        self.current = next_non_null;

        Some(current_node_mut_ref)
    }
}

impl<K, V> Node<K, V> {
    pub fn iter(&self) -> NodeIter<'_, K, V> {
        NodeIter {
            // SAFETY: trivial.
            current: Some(NonNull::from(self)),
            phantom: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> NodeIterMut<'_, K, V> {
        NodeIterMut {
            // SAFETY: trivial.
            current: Some(NonNull::from(self)),
            phantom: PhantomData,
        }
    }
}

impl<'a, K, V> IntoIterator for &'a Node<K, V> {
    type Item = &'a Node<K, V>;
    type IntoIter = NodeIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut Node<K, V> {
    type Item = &'a mut Node<K, V>;
    type IntoIter = NodeIterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Color;

    macro_rules! link {
        ($parent:expr, $child:expr) => {
            $parent.left = Some($child.into());
            $child.set_parent_and_color($parent, Color::Black);
        };
    }

    #[test]
    fn test_iter_single_node() {
        let node = Node::new(1, "value");
        let mut iter = node.iter();
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_mut_single_node() {
        let mut node = Node::new(1, "value");
        let mut iter_mut = node.iter_mut();
        assert!(iter_mut.next().is_some());
        assert!(iter_mut.next().is_none());
    }

    #[test]
    fn test_iter_with_parent_child() {
        let parent = &mut Node::new(10, "parent");
        let child = &mut Node::new(5, "child");

        link!(parent, child);

        let mut iter = child.iter();
        assert_eq!(iter.next().unwrap().key, 5);
        assert_eq!(iter.next().unwrap().key, 10);
        assert!(iter.next().is_none());
    }
}
