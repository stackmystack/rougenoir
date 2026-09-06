use crate::{Set, Tree, TreeCallbacks, alloc::Allocator};

impl<T: Ord, C: TreeCallbacks<Key = T, Value = ()> + Default, A: Allocator + Default>
    FromIterator<T> for Set<T, C, A>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Set<T, C, A> {
        let inputs: Vec<_> = iter.into_iter().collect();

        let mut tree = Tree::with_callbacks_in(Default::default(), A::default());
        for k in inputs {
            tree.insert(k, ());
        }

        Self { tree }
    }
}
