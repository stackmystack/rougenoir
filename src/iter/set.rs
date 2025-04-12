use crate::{Callbacks, Set, Tree};

impl<T: Ord, C: Callbacks<Key = T, Value = ()> + Default> FromIterator<T> for Set<T, C> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Set<T, C> {
        let inputs: Vec<_> = iter.into_iter().collect();

        if inputs.is_empty() {
            return Set::with_callbacks(Default::default());
        }

        let mut tree = Tree::with_callbacks(Default::default());
        for k in inputs {
            tree.insert(k, ());
        }

        Self { tree }
    }
}
