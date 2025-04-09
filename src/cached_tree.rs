use crate::{CachedTree, Callbacks, Node, tree};

impl<K, V, C: Callbacks<Key = K, Value = V> + Default> CachedTree<K, V, C> {
    pub fn clear(&mut self) {
        self.leftmost = None;
        self.tree.clear();
    }
}

impl<K, V, C: Callbacks<Key = K, Value = V>> CachedTree<K, V, C> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        self.leftmost = unsafe { tree::alloc_node(key, value) };
        todo!()
    }
}
// impl<K: PartialEq + Ord, V, A: Augmenter<Key = K, Value = V>> RootOps for RootCached<K, V, A> {
//     type Key = K;
//     type Value = V;

//     fn root(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.root
//     }

//     fn set_root(&mut self, new: NodePtr<Self::Key, Self::Value>) {
//         self.root.root = new;
//     }

//     fn first(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.leftmost
//     }

//     fn last(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.last()
//     }

//     fn first_postorder(&self) -> NodePtr<Self::Key, Self::Value> {
//         self.root.first_postorder()
//     }

//     fn replace_node(
//         &mut self,
//         victim: NonNull<Node<Self::Key, Self::Value>>,
//         new: NonNull<Node<Self::Key, Self::Value>>,
//     ) {
//         if self.leftmost == victim.into() {
//             self.leftmost = new.into();
//         }
//         self.root.replace_node(victim, new);
//     }

//     fn insert(&mut self, node: NonNull<Node<Self::Key, Self::Value>>) {
//         self.leftmost = node.into();
//         self.root.insert(node);
//     }

//     fn erase(&mut self, node: NonNull<Node<Self::Key, Self::Value>>) {
//         if self.leftmost == node.into() {
//             self.leftmost = unsafe { node.as_ref() }.next();
//         }
//         self.root.erase(node);
//     }
// }
