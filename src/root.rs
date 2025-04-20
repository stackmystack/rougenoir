use std::ptr::{self, NonNull};

use super::{Color, Node, NodePtr, NodePtrExt, Root, TreeCallbacks};

impl<K, V, C: TreeCallbacks<Key = K, Value = V> + Default> Default for Root<K, V, C> {
    fn default() -> Self {
        Root::new(C::default())
    }
}

// Public
impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Root<K, V, C> {
    pub fn new(augmented: C) -> Self {
        Root {
            node: None,
            callbacks: augmented,
        }
    }

    pub fn erase(&mut self, node: NonNull<Node<K, V>>) {
        let rebalance = self.erase_augmented(node);
        if rebalance.is_some() {
            self.erase_color(rebalance);
        }
    }

    pub fn insert(&mut self, node: NonNull<Node<K, V>>) {
        let mut node: NodePtr<K, V> = node.into();
        let mut parent = node.red_parent();
        let mut gparent;
        let mut tmp;

        loop {
            /*
             * Loop invariant: node is red.
             */
            // TODO: unlikely hint, but it's nightly only.
            if parent.is_none() {
                /*
                 * The inserted node is root. Either this is the
                 * first node, or we recursed at Case 1 below and
                 * are no longer violating 4).
                 */
                node.set_parent_and_color(ptr::null_mut(), Color::Black);
                break;
            }

            /*
             * If there is a black parent, we are done.
             * Otherwise, take some corrective action as,
             * per 4), we don't want a red root or two
             * consecutive red nodes.
             */
            if parent.is_black() {
                break;
            }

            gparent = parent.red_parent();
            tmp = gparent.right();

            if parent != tmp {
                /* parent == gparent->rb_left */
                if tmp.is_red() {
                    /*
                     * Case 1 - node's uncle is red (color flips).
                     *
                     *       G            g
                     *      / \          / \
                     *     p   u  -->   P   U
                     *    /            /
                     *   n            n
                     *
                     * However, since g's parent might be red, and
                     * 4) does not allow this, we need to recurse
                     * at g.
                     */
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                    parent.set_parent_and_color(gparent.ptr(), Color::Black);
                    node = gparent;
                    parent = node.parent();
                    node.set_parent_and_color(parent.ptr(), Color::Red);
                    continue;
                }

                tmp = parent.right();
                if node == tmp {
                    /*
                     * Case 2 - node's uncle is black and node is
                     * the parent's right child (left rotate at parent).
                     *
                     *      G             G
                     *     / \           / \
                     *    p   U  -->    n   U
                     *     \           /
                     *      n         p
                     *
                     * This still leaves us in violation of 4), the
                     * continuation into Case 3 will fix that.
                     */
                    tmp = node.left();
                    parent.set_right(tmp);
                    node.set_left(parent);
                    if tmp.is_some() {
                        tmp.set_parent_and_color(parent.ptr(), Color::Black);
                    }
                    parent.set_parent_and_color(node.ptr(), Color::Red);
                    self.callbacks.rotate(parent, node);
                    parent = node;
                    tmp = node.right();
                }

                /*
                 * Case 3 - node's uncle is black and node is
                 * the parent's left child (right rotate at gparent).
                 *
                 *        G           P
                 *       / \         / \
                 *      p   U  -->  n   g
                 *     /                 \
                 *    n                   U
                 */
                gparent.set_left(tmp); /* == parent->rb_right */
                parent.set_right(gparent);
                if tmp.is_some() {
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                }
                self.rotate_set_parents(gparent, parent, Color::Red);
                self.callbacks.rotate(gparent, parent);
                break;
            } else {
                tmp = gparent.left();
                if tmp.is_red() {
                    /* Case 1 - color flips */
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                    parent.set_parent_and_color(gparent.ptr(), Color::Black);
                    node = gparent;
                    parent = node.parent();
                    node.set_parent_and_color(parent.ptr(), Color::Red);
                    continue;
                }

                tmp = parent.left();
                if node == tmp {
                    /* Case 2 - right rotate at parent */
                    tmp = node.right();
                    parent.set_left(tmp);
                    node.set_right(parent);
                    if tmp.is_some() {
                        tmp.set_parent_and_color(parent.ptr(), Color::Black);
                    }
                    parent.set_parent_and_color(node.ptr(), Color::Red);
                    self.callbacks.rotate(parent, node);
                    parent = node;
                    tmp = node.left();
                }

                /* Case 3 - left rotate at gparent */
                gparent.set_right(tmp); /* == parent->rb_left */
                parent.set_left(gparent);
                if tmp.is_some() {
                    tmp.set_parent_and_color(gparent.ptr(), Color::Black);
                }
                self.rotate_set_parents(gparent, parent, Color::Red);
                self.callbacks.rotate(gparent, parent);
                break;
            }
        }
    }
}

#[cfg(debug_assertions)]
impl<K, V, C> Root<K, V, C>
where
    K: std::fmt::Debug,
{
    #[allow(useless_ptr_null_checks)]
    pub fn validate(&self) -> bool {
        let mut current = self.first();
        let mut res = true;
        while let Some(c) = current {
            if c.as_ptr().is_null() {
                println!("Node {:?} is null", c);
                res = false;
                break;
            }
            let c = unsafe { c.as_ref() };
            println!("current node {:?}", c.key);
            let left = c.left;
            let right = c.right;
            if left.is_some() && left.parent() != current {
                println!(
                    "current({:?}) != left({:?}).parent; the parent is {:?}",
                    c.key,
                    left.and_then(|l| {
                        if l.as_ptr().is_null() {
                            None
                        } else {
                            Some(&unsafe { l.as_ref() }.key)
                        }
                    }),
                    left.parent().and_then(|p| {
                        if p.as_ptr().is_null() {
                            None
                        } else {
                            Some(&unsafe { p.as_ref() }.key)
                        }
                    })
                );
                res = false;
            }

            if right.is_some() && right.parent() != current {
                println!(
                    "current({:?}) != right({:?}).parent; the parent is {:?}",
                    c.key,
                    right.and_then(|r| {
                        if r.as_ptr().is_null() {
                            None
                        } else {
                            Some(&unsafe { r.as_ref() }.key)
                        }
                    }),
                    right.parent().and_then(|p| {
                        if p.as_ptr().is_null() {
                            None
                        } else {
                            Some(&unsafe { p.as_ref() }.key)
                        }
                    })
                );
                res = false;
            }
            if !res {
                return false;
            }
            current = c.next();
        }

        res
    }
}

impl<K, V, C> Root<K, V, C> {
    pub fn first(&self) -> NodePtr<K, V> {
        let mut n = self.node?;
        while let Some(left) = unsafe { n.as_ref() }.left {
            n = left;
        }
        Some(n)
    }

    pub fn first_postorder(&self) -> NodePtr<K, V> {
        let n = self.node?;
        unsafe { n.as_ref() }.left_deepest_node()
    }

    pub fn last(&self) -> NodePtr<K, V> {
        let mut n = self.node?;
        while let Some(right) = unsafe { n.as_ref() }.right {
            n = right;
        }
        Some(n)
    }

    pub fn replace_node(&mut self, mut victim: NonNull<Node<K, V>>, new: NonNull<Node<K, V>>) {
        let new: NodePtr<K, V> = new.into();
        let parent = unsafe { victim.as_ref() }.parent();
        {
            let victim = unsafe { victim.as_mut() };
            victim.left.set_parent(new.ptr());
            victim.right.set_parent(new.ptr());
        }
        self.change_child(victim.into(), new, parent);
    }
}

// Private

impl<K, V, C: TreeCallbacks<Key = K, Value = V>> Root<K, V, C> {
    #[inline]
    fn erase_augmented(&mut self, node: NonNull<Node<K, V>>) -> NodePtr<K, V> {
        let node = unsafe { node.as_ref() };
        let mut child = node.right;
        let mut tmp = node.left;
        let mut parent;
        let rebalance;
        let pc;

        if tmp.is_none() {
            /*
             * Case 1: node to erase has no more than 1 child (easy!)
             *
             * Note that if there is one child it must be red due to 5)
             * and node must be black due to 4). We adjust colors locally
             * so as to bypass __rb_erase_color() later on.
             */
            pc = node.parent_color;
            parent = Node::from_parent_color(pc);
            self.change_child(node.into(), child, parent);
            rebalance = if child.is_some() {
                child.set_parent_color(pc);
                None
            } else if Node::<K, V>::parent_color(pc) == Color::Black {
                parent
            } else {
                None
            };
            tmp = parent;
        } else if child.is_none() {
            /* Still case 1, but this time the child is node->rb_left */
            pc = node.parent_color;
            tmp.set_parent_color(pc);
            parent = Node::from_parent_color(pc);
            self.change_child(node.into(), tmp, parent);
            rebalance = None;
            tmp = parent;
        } else {
            let mut successor = child;
            let mut child2;

            tmp = child.left();
            if tmp.is_none() {
                /*
                 * Case 2: node's successor is its right child
                 *
                 *    (n)          (s)
                 *    / \          / \
                 *  (x) (s)  ->  (x) (c)
                 *        \
                 *        (c)
                 */
                parent = successor;
                child2 = successor.right();
                self.callbacks.copy(node.into(), successor);
            } else {
                /*
                 * Case 3: node's successor is leftmost under
                 * node's right child subtree
                 *
                 *    (n)          (s)
                 *    / \          / \
                 *  (x) (y)  ->  (x) (y)
                 *      /            /
                 *    (p)          (p)
                 *    /            /
                 *  (s)          (c)
                 *    \
                 *    (c)
                 */
                loop {
                    parent = successor;
                    successor = tmp;
                    tmp = tmp.left();
                    if tmp.is_none() {
                        break;
                    }
                }
                child2 = successor.right();
                parent.set_left(child2);
                successor.set_right(child);
                child.set_parent(successor.ptr());

                self.callbacks.copy(node.into(), successor);
                self.callbacks.propagate(parent, successor);
            }

            tmp = node.left;
            successor.set_left(tmp);
            tmp.set_parent(successor.ptr());

            pc = node.parent_color;
            tmp = Node::from_parent_color(pc);
            self.change_child(node.into(), successor, tmp);
            rebalance = if child2.is_some() {
                child2.set_parent_and_color(parent.ptr(), Color::Black);
                None
            } else if successor.is_black() {
                parent
            } else {
                None
            };
            successor.set_parent_color(pc);
            tmp = successor;
        }

        self.callbacks.propagate(tmp, None);
        rebalance
    }

    /// Inline version for rb_erase() use - we want to be able to inline
    /// and eliminate the [`DummyAugmenter::rotate`] callback there
    #[inline]
    fn erase_color(&mut self, mut parent: NodePtr<K, V>) {
        let mut node = None;
        let mut sibling;
        let mut tmp1;
        let mut tmp2;

        loop {
            /*
             * Loop invariants:
             * - node is black (or NULL on first iteration)
             * - node is not the root (parent is not NULL)
             * - All leaf paths going through parent and node have a
             *   black node count that is 1 lower than other leaf paths.
             */
            sibling = parent.right();
            if node != sibling {
                if sibling.is_red() {
                    /*
                     * Case 1 - left rotate at parent
                     *
                     *     P               S
                     *    / \             / \
                     *   N   s    -->    p   Sr
                     *      / \         / \
                     *     Sl  Sr      N   Sl
                     */
                    tmp1 = sibling.left();
                    parent.set_right(tmp1);
                    sibling.set_left(parent);
                    tmp1.set_parent_and_color(parent.ptr(), Color::Black);
                    self.rotate_set_parents(parent, sibling, Color::Red);
                    self.callbacks.rotate(parent, sibling);
                    sibling = tmp1;
                }
                tmp1 = sibling.right();
                if tmp1.is_black() {
                    tmp2 = sibling.left();
                    if tmp2.is_black() {
                        /*
                         * Case 2 - sibling color flip
                         * (p could be either color here)
                         *
                         *    (p)           (p)
                         *    / \           / \
                         *   N   S    -->  N   s
                         *      / \           / \
                         *     Sl  Sr        Sl  Sr
                         *
                         * This leaves us violating 5) which
                         * can be fixed by flipping p to black
                         * if it was red, or by recursing at p.
                         * p is red when coming from Case 1.
                         */
                        sibling.set_parent_and_color(parent.ptr(), Color::Red);
                        if parent.is_red() {
                            parent.set_color(Color::Black);
                        } else {
                            node = parent;
                            parent = parent.parent();
                            if parent.is_some() {
                                continue;
                            }
                        }
                        break;
                    }
                    /*
                     * Case 3 - right rotate at sibling
                     * (p could be either color here)
                     *
                     *   (p)           (p)
                     *   / \           / \
                     *  N   S    -->  N   sl
                     *     / \             \
                     *    sl  sr            S
                     *                       \
                     *                        sr
                     *
                     * Note: p might be red, and then both
                     * p and sl are red after rotation(which
                     * breaks property 4). This is fixed in
                     * Case 4 (in __rb_rotate_set_parents()
                     *         which set sl the color of p
                     *         and set p RB_BLACK)
                     *
                     *   (p)            (sl)
                     *   / \            /  \
                     *  N   sl   -->   P    S
                     *       \        /      \
                     *        S      N        sr
                     *         \
                     *          sr
                     */
                    tmp1 = tmp2.right();
                    sibling.set_left(tmp1);
                    tmp2.set_right(sibling);
                    parent.set_right(tmp2);
                    if tmp1.is_some() {
                        tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                    }
                    self.callbacks.rotate(sibling, tmp2);
                    tmp1 = sibling;
                    sibling = tmp2;
                }
                /*
                 * Case 4 - left rotate at parent + color flips
                 * (p and sl could be either color here.
                 *  After rotation, p becomes black, s acquires
                 *  p's color, and sl keeps its color)
                 *
                 *      (p)             (s)
                 *      / \             / \
                 *     N   S     -->   P   Sr
                 *        / \         / \
                 *      (sl) sr      N  (sl)
                 */
                tmp2 = sibling.left();
                parent.set_right(tmp2);
                sibling.set_left(parent);
                tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                if tmp2.is_some() {
                    tmp2.set_parent(parent.ptr());
                }
                self.rotate_set_parents(parent, sibling, Color::Black);
                self.callbacks.rotate(parent, sibling);
                break;
            } else {
                sibling = parent.left();
                if sibling.is_red() {
                    /* Case 1 - right rotate at parent */
                    tmp1 = sibling.right();
                    parent.set_left(tmp1);
                    sibling.set_right(parent);
                    tmp1.set_parent_and_color(parent.ptr(), Color::Black);
                    self.rotate_set_parents(parent, sibling, Color::Red);
                    self.callbacks.rotate(parent, sibling);
                    sibling = tmp1;
                }
                tmp1 = sibling.left();
                if tmp1.is_black() {
                    tmp2 = sibling.right();
                    if tmp2.is_black() {
                        /* Case 2 - sibling color flip */
                        sibling.set_parent_and_color(parent.ptr(), Color::Red);
                        if parent.is_red() {
                            parent.set_color(Color::Black);
                        } else {
                            node = parent;
                            parent = node.parent();
                            if parent.is_some() {
                                continue;
                            }
                        }
                        break;
                    }
                    /* Case 3 - left rotate at sibling */
                    tmp1 = tmp2.left();
                    sibling.set_right(tmp1);
                    tmp2.set_left(sibling);
                    parent.set_left(tmp2);
                    if tmp1.is_some() {
                        tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                    }
                    self.callbacks.rotate(sibling, tmp2);
                    tmp1 = sibling;
                    sibling = tmp2;
                }
                /* Case 4 - right rotate at parent + color flips */
                tmp2 = sibling.right();
                parent.set_left(tmp2);
                sibling.set_right(parent);
                tmp1.set_parent_and_color(sibling.ptr(), Color::Black);
                if tmp2.is_some() {
                    tmp2.set_parent(parent.ptr());
                }
                self.rotate_set_parents(parent, sibling, Color::Black);
                self.callbacks.rotate(parent, sibling);
                break;
            }
        }
    }
}

impl<K, V, C> Root<K, V, C> {
    fn change_child(&mut self, old: NodePtr<K, V>, new: NodePtr<K, V>, parent: NodePtr<K, V>) {
        if let Some(mut parent) = parent {
            let parent = unsafe { parent.as_mut() };
            if parent.left == old {
                parent.left = new;
            } else {
                parent.right = new;
            }
        } else {
            self.node = new;
        }
    }

    /// Helper function for rotations:
    /// - old's parent and color get assigned to new
    /// - old gets assigned new as a parent and 'color' as a color.
    #[inline]
    fn rotate_set_parents(&mut self, old: NodePtr<K, V>, new: NodePtr<K, V>, color: Color) {
        // TODO:  paramas should be NonNull.
        if old.is_some() {
            let old = unsafe { old.unwrap().as_mut() };
            let parent = old.parent();
            unsafe { new.unwrap().as_mut() }.parent_color = old.parent_color;
            old.set_parent_and_color(new.ptr(), color);
            self.change_child(old.into(), new, parent);
        }
    }
}
