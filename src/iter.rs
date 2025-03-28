use std::ops::Index;

use crate::{Callbacks, Tree};

impl<K, V, C: Callbacks<Key = K, Value = V>> Index<&K> for Tree<K, V, C>
where
    K: Ord,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `Tree`.
    #[inline]
    fn index(&self, key: &K) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

#[cfg(test)]
mod test {
    use crate::Tree;
    use pretty_assertions::assert_eq;

    #[test]
    fn index_passes() {
        let mut tree = Tree::new();
        let forty_two = "forty two".to_string();
        tree.insert(42, forty_two.clone());
        assert_eq!(forty_two, tree[&42]);
    }

    #[test]
    #[should_panic]
    fn index_panics() {
        let tree: Tree<usize, ()> = Tree::new();
        assert_eq!((), tree[&42]);
    }
}
