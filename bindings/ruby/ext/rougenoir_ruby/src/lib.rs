use std::{cell::RefCell, cmp::Ordering};

use magnus::{
    gc::Marker, method, prelude::*, value::ReprValue, DataTypeFunctions, Error, Ruby, Value,
};
use rougenoir::Noop;

static METHOD_SPACESHIP: &str = "<=>";
static METHOD_CMP: &str = "rougenoir_cmp";

#[derive(Debug)]
struct TreeValue {
    value: Value,
}

#[derive(Debug)]
struct TreeKey {
    value: Value,
    method: &'static str,
}

impl TreeKey {
    fn cmp_method_of(v: Value) -> Option<&'static str> {
        [METHOD_SPACESHIP, METHOD_CMP]
            .into_iter()
            .find(|&m| v.respond_to(m, false).ok() == Some(true))
    }
}

impl PartialEq for TreeKey {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(std::cmp::Ordering::Equal)
    }
}

impl Eq for TreeKey {}

impl PartialOrd for TreeKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value
            .funcall(self.method, (other.value,))
            .map(|v: i64| v.cmp(&0))
            .ok()
    }
}

impl Ord for TreeKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).expect(&format!(
            "The comparison method `{}#{}` is not behaving like Ruby's spaceship operator `<=>`",
            self.value.class(),
            self.method
        ))
    }
}

#[derive(Default)]
struct Tree {
    inner: rougenoir::Tree<TreeKey, TreeValue, Noop<TreeKey, TreeValue>>,
}

// SAFETY: They're only constructed in ruby threads.
unsafe impl<'a> Send for TreeKey {}
unsafe impl<'a> Send for TreeValue {}

#[derive(Default, magnus::TypedData)]
#[magnus(class = "RougeNoir::Tree", free_immediately, mark, size)]
struct TreeMut {
    inner: RefCell<Tree>,
}

impl DataTypeFunctions for TreeMut {
    fn mark(&self, marker: &Marker) {
        for (k, v) in self.inner.borrow().inner.iter() {
            marker.mark(k.value);
            marker.mark(v.value);
        }
    }
}

impl TreeMut {
    fn initialize(&self) {}

    fn insert(&self, k: Value, v: Value) -> Result<Option<Value>, Error> {
        if let Some(method) = TreeKey::cmp_method_of(v) {
            let this = &mut self.inner.borrow_mut().inner;
            Ok(this
                .insert(TreeKey { value: k, method }, TreeValue { value: v })
                .map(|v| v.value))
        } else {
            let ruby = Ruby::get_with(v);
            Err(Error::new(
                ruby.exception_arg_error(),
                "RougeNoir::Tree accepts keys that respond to `{METHOD_SPACESHIP}` or `{METHOD_CMP}`",
            ))
        }
    }

    fn inspect(&self) {
        let this = &self.inner.borrow_mut().inner;
        println!("{{");
        for n in this.iter() {
            println!("  ({k}, {v})", k = n.0.value, v = n.1.value);
        }
        println!("}}");
    }
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    let rouge_noir = ruby.define_module("RougeNoir")?;
    let tree = rouge_noir.define_class("Tree", ruby.class_object())?;
    tree.define_alloc_func::<TreeMut>();
    tree.define_method("initialize", method!(TreeMut::initialize, 0))?;
    tree.define_method("insert", method!(TreeMut::insert, 2))?;
    tree.define_method("inspect", method!(TreeMut::inspect, 0))?;
    Ok(())
}
