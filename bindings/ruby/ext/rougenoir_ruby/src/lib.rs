use std::{cell::RefCell, cmp::Ordering};

use magnus::{
    gc::Marker, method, prelude::*, value::ReprValue, DataTypeFunctions, Error, Ruby, Value,
};
use rougenoir::Noop;

static METHOD_SPACESHIP: &str = "<=>";

#[derive(Debug)]
struct TreeValue {
    value: Value,
}

#[derive(Debug)]
struct TreeKey {
    value: Value,
}

impl TreeKey {
    fn is_comparable(v: Value) -> bool {
        v.respond_to(METHOD_SPACESHIP, false).is_ok()
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
            .funcall(METHOD_SPACESHIP, (other.value,))
            .map(|v: i64| v.cmp(&0))
            .ok()
    }
}

impl Ord for TreeKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let ruby = unsafe { Ruby::get_unchecked() };
        print!("{self:?}, {other:?} ",);
        let res = self.partial_cmp(other).unwrap();
        println!(" #{res:?}");
        res
    }
}

// SAFETY: They're only constructed in ruby threads.
unsafe impl<'a> Send for TreeKey {}
unsafe impl<'a> Send for TreeValue {}

#[derive(Default, magnus::TypedData)]
#[magnus(class = "RougeNoir::Tree", free_immediately, mark, size)]
struct TreeMut {
    inner: RefCell<rougenoir::Tree<TreeKey, TreeValue, Noop<TreeKey, TreeValue>>>,
}

impl DataTypeFunctions for TreeMut {
    fn mark(&self, marker: &Marker) {
        println!("GCCCCCCCCCCCCCCCCCCCCCCC");
        // NOTE: Should we clone the values and then call mark separately? Benchmarks, right?
        if let Ok(inner) = self.inner.try_borrow() {
            for (k, v) in inner.iter() {
                marker.mark(k.value);
                marker.mark(v.value);
            }
        }
    }
}

impl TreeMut {
    fn initialize(&self) {}

    fn insert(&self, k: Value, v: Value) -> Result<Option<Value>, Error> {
        if TreeKey::is_comparable(v) {
            let this = &mut self.inner.borrow_mut();
            let ruby = Ruby::get_with(v);
            // ruby.gc_disable();
            let res = this.insert(TreeKey { value: k }, TreeValue { value: v });
            // ruby.gc_enable();
            Ok(res.map(|v| v.value))
        } else {
            let ruby = Ruby::get_with(v);
            Err(Error::new(
                ruby.exception_arg_error(),
                "RougeNoir::Tree accepts keys that respond to `{METHOD_SPACESHIP}`",
            ))
        }
    }

    fn inspect(&self) {
        let this = &self.inner.borrow_mut();
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
