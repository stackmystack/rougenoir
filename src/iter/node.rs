use crate::{Node, NodePtr};
use std::{iter::FusedIterator, marker::PhantomData, ptr::NonNull};

/// An iterator over shared references to `Node`s in in-order traversal.
pub struct Iter<'a, K, V> {
    current: NodePtr<K, V>,
    phantom: PhantomData<&'a Node<K, V>>,
}

/// An iterator over mutable references to `Node`s in in-order traversal.
pub struct IterMut<'a, K, V> {
    current: NodePtr<K, V>,
    phantom: PhantomData<&'a mut Node<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = &'a Node<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let current = self.current?.as_ref();
            self.current = current.next();
            Some(self.current?.as_ref())
        }
    }
}

// Implement the `Iterator` trait for `NodeIterMut`.
impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = &'a mut Node<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let current = self.current?.as_ref();
            self.current = current.next();
            Some(self.current?.as_mut())
        }
    }
}

impl<K, V> Node<K, V> {
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            // SAFETY: trivial.
            current: Some(NonNull::from(self)),
            phantom: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            // SAFETY: trivial.
            current: Some(NonNull::from(self)),
            phantom: PhantomData,
        }
    }
}

impl<'a, K, V> IntoIterator for &'a Node<K, V> {
    type Item = &'a Node<K, V>;
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut Node<K, V> {
    type Item = &'a mut Node<K, V>;
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a Node<K, V>> {
        // SAFETY: If it's unwrapping, it's valid.
        unsafe {
            let current = self.current?.as_ref();
            self.current = current.prev();
            Some(self.current?.as_ref())
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a mut Node<K, V>> {
        // SAFETY: If it's unwrapping, it's valid.
        unsafe {
            let current = self.current?.as_mut();
            self.current = current.prev();
            Some(self.current?.as_mut())
        }
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}
impl<K, V> FusedIterator for IterMut<'_, K, V> {}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Color;

    // Helper macro to link nodes (parent to child) and set child's parent pointer.
    // The color doesn't matter for iterator tests, so we use them to mark direction.
    macro_rules! link {
        ($parent:expr, $child:expr, left) => {
            $parent.left = $child.into();
            $child.set_parent_and_color($parent, Color::Red);
        };
        ($parent:expr, $child:expr, right) => {
            $parent.right = $child.into();
            $child.set_parent_and_color($parent, Color::Black);
        };
        ($parent:expr, $left:expr, $right:expr) => {
            $parent.left = $left.into();
            $parent.right = $right.into();
            $left.set_parent_and_color($parent, Color::Red);
            $right.set_parent_and_color($parent, Color::Black);
        };
    }

    #[test]
    fn test_iter_single_node() {
        let node = Node::new(1, "value");
        let mut iter = node.iter();
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_single_node_rev() {
        let node = Node::new(1, "value");
        let mut iter = node.iter().rev();
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_mut_single_node() {
        let mut node = Node::new(1, "value");
        let mut iter_mut = node.iter_mut().rev();
        assert!(iter_mut.next().is_none());
        assert!(iter_mut.next().is_none());
    }

    #[test]
    fn test_iter_with_parent_child() {
        let mut parent = Node::new(10, "parent");
        let mut child = Node::new(5, "child");

        link!(&mut parent, &mut child, left);

        let mut iter = child.iter();
        assert_eq!(iter.next().unwrap().key, 10);
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_iter_complex_tree() {
        let mut n7 = Node::new(7, "root");
        let mut n3 = Node::new(3, "left_child_7");
        let mut n10 = Node::new(10, "right_child_7");
        let mut n1 = Node::new(1, "left_child_3");
        let mut n5 = Node::new(5, "right_child_3");
        let mut n12 = Node::new(12, "right_child_10");

        link!(&mut n10, &mut n12, right);
        link!(&mut n3, &mut n1, &mut n5);
        link!(&mut n7, &mut n3, &mut n10);

        let expected_order = vec![10, 12];
        let iter = n7.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![5, 7, 10, 12];
        let iter = n3.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![12];
        let iter = n10.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![3, 5, 7, 10, 12];
        let iter = n1.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![7, 10, 12];
        let iter = n5.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![];
        let iter = n12.iter();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_iter_mut_complex_tree() {
        let mut n7 = Node::new(7, "root");
        let mut n3 = Node::new(3, "left_child_7");
        let mut n10 = Node::new(10, "right_child_7");
        let mut n1 = Node::new(1, "left_child_3");
        let mut n5 = Node::new(5, "right_child_3");
        let mut n12 = Node::new(12, "right_child_10");

        link!(&mut n10, &mut n12, right);
        link!(&mut n3, &mut n1, &mut n5);
        link!(&mut n7, &mut n3, &mut n10);

        // Check the iterator on every single node.

        let expected_order = vec!["root", "root"];
        for node in n7.iter_mut() {
            node.value = "root";
        }
        let collected_values: Vec<&'static str> = n7.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n3", "n3", "n3", "n3"];
        for node in n3.iter_mut() {
            node.value = "n3";
        }
        let collected_values: Vec<&'static str> = n3.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n10"];
        for node in n10.iter_mut() {
            node.value = "n10";
        }
        let collected_values: Vec<&'static str> = n10.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n1", "n1", "n1", "n1", "n1"];
        for node in n1.iter_mut() {
            node.value = "n1";
        }
        let collected_values: Vec<&'static str> = n1.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n5", "n5", "n5"];
        for node in n5.iter_mut() {
            node.value = "n5";
        }
        let collected_values: Vec<&'static str> = n5.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order: Vec<&'static str> = vec![];
        for node in n12.iter_mut() {
            node.value = "n12";
        }
        let collected_values: Vec<&'static str> = n12.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        // Now the final state from the smallest

        let expected_order = vec!["n1", "n1", "n5", "n5", "n5"];
        let collected_values: Vec<&'static str> = n1.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_iter_complex_tree_rev() {
        let mut n7 = Node::new(7, "root");
        let mut n3 = Node::new(3, "left_child_7");
        let mut n10 = Node::new(10, "right_child_7");
        let mut n1 = Node::new(1, "left_child_3");
        let mut n5 = Node::new(5, "right_child_3");
        let mut n12 = Node::new(12, "right_child_10");

        link!(&mut n10, &mut n12, right);
        link!(&mut n3, &mut n1, &mut n5);
        link!(&mut n7, &mut n3, &mut n10);

        let expected_order = vec![5, 3, 1];
        let iter = n7.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![1];
        let iter = n3.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![7, 5, 3, 1];
        let iter = n10.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![];
        let iter = n1.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![3, 1];
        let iter = n5.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);

        let expected_order = vec![10, 7, 5, 3, 1];
        let iter = n12.iter().rev();
        let collected_keys: Vec<i32> = iter.map(|node| node.key).collect();
        assert_eq!(collected_keys, expected_order);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_iter_mut_complex_tree_rev() {
        let mut n7 = Node::new(7, "root");
        let mut n3 = Node::new(3, "left_child_7");
        let mut n10 = Node::new(10, "right_child_7");
        let mut n1 = Node::new(1, "left_child_3");
        let mut n5 = Node::new(5, "right_child_3");
        let mut n12 = Node::new(12, "right_child_10");

        link!(&mut n10, &mut n12, right);
        link!(&mut n3, &mut n1, &mut n5);
        link!(&mut n7, &mut n3, &mut n10);

        // Check the iterator on every single node.

        let expected_order = vec!["right_child_7", "right_child_10"];
        for node in n7.iter_mut().rev() {
            node.value = "root";
        }
        let collected_values: Vec<&'static str> = n7.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["root", "root", "right_child_7", "right_child_10"];
        for node in n3.iter_mut().rev() {
            node.value = "n3";
        }
        let collected_values: Vec<&'static str> = n3.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["right_child_10"];
        for node in n10.iter_mut().rev() {
            node.value = "n10";
        }
        let collected_values: Vec<&'static str> = n10.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n10", "n10", "n10", "right_child_7", "right_child_10"];
        for node in n1.iter_mut().rev() {
            node.value = "n1";
        }
        let collected_values: Vec<&'static str> = n1.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order = vec!["n10", "right_child_7", "right_child_10"];
        for node in n5.iter_mut().rev() {
            node.value = "n5";
        }
        let collected_values: Vec<&'static str> = n5.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        let expected_order: Vec<&'static str> = vec![];
        for node in n12.iter_mut().rev() {
            node.value = "n12";
        }
        let collected_values: Vec<&'static str> = n12.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);

        // Now the final state from the smallest

        let expected_order = vec!["n12", "n12", "n12", "n12", "right_child_10"];
        let collected_values: Vec<&'static str> = n1.iter().map(|node| node.value).collect();
        assert_eq!(collected_values, expected_order);
    }
}
