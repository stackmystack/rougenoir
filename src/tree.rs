use std::marker::PhantomData;

use crate::{Augmenter, Node, Root};

#[derive(Debug)]
struct Tree<K: Ord, V, A: Augmenter> {
    root: Root<A>,
    phantom_k: PhantomData<K>,
    phantom_v: PhantomData<V>,
}

//#[derive(Debug)]
//struct Entry<K: Ord, V> {
//    node: Node,
//}
