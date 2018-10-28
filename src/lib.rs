#![allow(dead_code)]
#![feature(box_into_raw_non_null)]
#![feature(box_syntax)]
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A doubly-linked list with owned nodes.
///
/// The `LinkedList` allows pushing and popping elements at either end
/// in constant time.
///
/// This is the same `LinkedList` used in `alloc`
pub struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: T,
}
impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }

    fn into_element(self: Box<Self>) -> T {
        self.element
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self::default()
    }
    /// Provides a cursor to the empty element
    pub fn cursor(&self, end: End) -> Cursor<T> {
        Cursor {
            list: self,
            current: None,
            end: Some(end),
        }
    }

    pub fn head(&self) -> Cursor<T> {
        let mut c = self.cursor(End::Head);
        c.move_next();
        c
    }

    pub fn tail(&self) -> Cursor<T> {
        let mut c = self.cursor(End::Tail);
        c.move_prev();
        c
    }

    /// Provides a cursor with mutable references and access to the list
    pub fn cursor_mut(&mut self, end: End) -> CursorMut<T> {
        let current_len = match end {
            End::Head => 0,
            End::Tail => self.len,
        };
        CursorMut {
            list: self,
            current: None,
            current_len,
            end: Some(end),
        }
    }

    pub fn head_mut(&mut self) -> CursorMut<T> {
        let mut c = self.cursor_mut(End::Head);
        c.move_next();
        c
    }

    pub fn tail_mut(&mut self) -> CursorMut<T> {
        let mut c = self.cursor_mut(End::Tail);
        c.move_prev();
        c
    }

    /* other list methods go here */
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        let mut c = self.head_mut();
        while c.pop().is_some() {}
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut t = f.debug_list();
        let mut c = self.head();
        while let Some(e) = c.current() {
            t.entry(&e);
            c.move_next();
        }

        t.finish()
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> LinkedList<T> {
        let mut list = LinkedList::new();
        {
            let mut cursor = list.cursor_mut(End::Tail);
            for item in iter {
                cursor.insert_before(item);
            }
        }
        list
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum End {
    Head,
    Tail,
}

/// An Immutable look into a `LinkedList` that can be moved back and forth
pub struct Cursor<'list, T: 'list> {
    current: Option<NonNull<Node<T>>>,
    list: &'list LinkedList<T>,
    end: Option<End>,
}

impl<'list, T> Cursor<'list, T> {
    fn next(&self) -> Option<NonNull<Node<T>>> {
        match self.end {
            None | Some(End::Head) => self
                .current
                .map_or(self.list.head, |node| unsafe { node.as_ref().next }),
            Some(End::Tail) => None,
        }
    }
    fn prev(&self) -> Option<NonNull<Node<T>>> {
        match self.end {
            None | Some(End::Tail) => self
                .current
                .map_or(self.list.tail, |node| unsafe { node.as_ref().prev }),
            Some(End::Head) => None,
        }
    }
    /// Move to the subsequent element of the list if it exists or the empty
    /// element
    pub fn move_next(&mut self) {
        self.current = self.next();
        self.end = if self.current.is_none() {
            Some(End::Tail)
        } else {
            None
        };
    }
    /// Move to the previous element of the list
    pub fn move_prev(&mut self) {
        self.current = self.prev();
        self.end = if self.current.is_none() {
            Some(End::Head)
        } else {
            None
        };
    }

    /// Get the current element
    pub fn current(&self) -> Option<&'list T> {
        self.current.map(|node| unsafe {
            // Need an unbound lifetime to get 'list
            let node = &*node.as_ptr();
            &node.element
        })
    }
    /// Get the following element
    pub fn peek_after(&self) -> Option<&'list T> {
        self.next().map(|next_node| unsafe {
            let next_node = &*next_node.as_ptr();
            &next_node.element
        })
    }
    /// Get the previous element
    pub fn peek_before(&self) -> Option<&'list T> {
        self.prev().map(|prev_node| unsafe {
            let prev_node = &*prev_node.as_ptr();
            &prev_node.element
        })
    }
}

/// A mutable view into a `LinkedList` that can be used to edit the collection
pub struct CursorMut<'list, T: 'list> {
    current: Option<NonNull<Node<T>>>,
    list: &'list mut LinkedList<T>,
    current_len: usize,
    end: Option<End>,
}

impl<'list, T> CursorMut<'list, T> {
    fn next(&self) -> Option<NonNull<Node<T>>> {
        match self.end {
            None | Some(End::Head) => self
                .current
                .map_or(self.list.head, |node| unsafe { node.as_ref().next }),
            Some(End::Tail) => None,
        }
    }
    fn prev(&self) -> Option<NonNull<Node<T>>> {
        match self.end {
            None | Some(End::Tail) => self
                .current
                .map_or(self.list.tail, |node| unsafe { node.as_ref().prev }),
            Some(End::Head) => None,
        }
    }

    // `current_len` is in the range 0...self.list.len at all times
    unsafe fn inc_len(&mut self) {
        self.current_len += 1;
    }
    unsafe fn dec_len(&mut self) {
        self.current_len -= 1;
    }

    /// Move to the subsequent element of the list if it exists or the empty
    /// element
    pub fn move_next(&mut self) {
        if self.current.is_some() {
            unsafe { self.inc_len() };
        }
        self.current = self.next();
        self.end = if self.current.is_none() {
            Some(End::Tail)
        } else {
            None
        };
    }
    /// Move to the previous element of the list
    pub fn move_prev(&mut self) {
        self.current = self.prev();
        self.end = if self.current.is_none() {
            Some(End::Head)
        } else {
            unsafe { self.dec_len() };
            None
        };
    }

    /// Get the current element
    pub fn current(&mut self) -> Option<&mut T> {
        self.current.map(|node| unsafe {
            // Need an unbound lifetime to get same lifetime as self
            let node = &mut *node.as_ptr();
            &mut node.element
        })
    }
    /// Get the next element
    pub fn peek_after(&mut self) -> Option<&mut T> {
        self.next().map(|next_node| unsafe {
            let next_node = &mut *next_node.as_ptr();
            &mut next_node.element
        })
    }
    /// Get the previous element
    pub fn peek_before(&self) -> Option<&mut T> {
        self.prev().map(|prev_node| unsafe {
            let prev_node = &mut *prev_node.as_ptr();
            &mut prev_node.element
        })
    }

    /// Get an immutable cursor at the current element
    pub fn as_cursor(&self) -> Cursor<T> {
        Cursor {
            current: self.current,
            list: self.list,
            end: self.end,
        }
    }

    // Now the list editing operations

    unsafe fn raw_insert_item(
        &mut self,
        item: T,
        prev: Option<NonNull<Node<T>>>,
        next: Option<NonNull<Node<T>>>,
    ) -> NonNull<Node<T>> {
        let mut node = box Node::new(item);
        node.prev = prev;
        node.next = next;
        let node = Box::into_raw_non_null(node);
        match prev {
            None => self.list.head = Some(node),
            Some(mut prev) => prev.as_mut().next = Some(node),
        }
        match next {
            None => self.list.tail = Some(node),
            Some(mut next) => next.as_mut().prev = Some(node),
        }
        node
    }

    fn insert_after_links(&self) -> (Option<NonNull<Node<T>>>, Option<NonNull<Node<T>>>) {
        match self.current {
            None => match self.end {
                None | Some(End::Head) => (None, self.list.head),
                Some(End::Tail) => (self.list.tail, None),
            },
            Some(current) => (Some(current), self.next()),
        }
    }

    fn insert_before_links(&self) -> (Option<NonNull<Node<T>>>, Option<NonNull<Node<T>>>) {
        match self.current {
            None => match self.end {
                None | Some(End::Head) => (None, self.list.head),
                Some(End::Tail) => (self.list.tail, None),
            },
            Some(current) => (self.prev(), Some(current)),
        }
    }

    /// Insert `item` after the cursor
    pub fn insert_after(&mut self, item: T) {
        self.list.len += 1;

        let (prev, next) = self.insert_after_links();

        unsafe {
            let node = self.raw_insert_item(item, prev, next);
            self.current = Some(node);
            self.end = None;
        }
        self.move_prev()
    }

    /// Insert `item` before the cursor
    pub fn insert_before(&mut self, item: T) {
        self.list.len += 1;

        let (prev, next) = self.insert_before_links();

        unsafe {
            let node = self.raw_insert_item(item, prev, next);
            self.current = Some(node);
            self.end = None;
        }
        self.move_next();
    }

    unsafe fn raw_insert_list(
        &mut self,
        mut head: NonNull<Node<T>>,
        mut tail: NonNull<Node<T>>,
        prev: Option<NonNull<Node<T>>>,
        next: Option<NonNull<Node<T>>>,
    ) {
        head.as_mut().prev = prev;
        tail.as_mut().next = next;
        match prev {
            None => self.list.head = Some(head),
            Some(mut prev) => prev.as_mut().next = Some(head),
        }
        match next {
            None => self.list.tail = Some(tail),
            Some(mut next) => next.as_mut().prev = Some(tail),
        }
    }

    /// Insert `list` between the current element and the next
    pub fn insert_list_after(&mut self, mut list: LinkedList<T>) {
        let (head, tail, len) = match (list.head.take(), list.tail.take()) {
            (Some(head), Some(tail)) => (head, tail, list.len),
            //splicing in an empty list should be a no-op
            (None, None) => return,
            _ => unreachable!(),
        };

        let (prev, next) = self.insert_after_links();

        self.list.len += len;

        unsafe {
            self.raw_insert_list(head, tail, prev, next);
            self.current = Some(head);
            self.end = None;
            self.inc_len();
        }
        self.move_prev();
    }

    /// Insert `list` between the previous element and current
    pub fn insert_list_before(&mut self, mut list: LinkedList<T>) {
        let (head, tail, len) = match (list.head.take(), list.tail.take()) {
            (Some(head), Some(tail)) => (head, tail, list.len),
            //splicing in an empty list should be a no-op
            (None, None) => return,
            _ => unreachable!(),
        };

        let (prev, next) = self.insert_before_links();

        self.list.len += list.len;

        unsafe {
            self.raw_insert_list(head, tail, prev, next);
            self.current = Some(head);
            self.end = None;
            self.current_len += len - 1;
        }
        self.move_next();
    }

    /// Remove and return the item following the cursor
    pub fn pop(&mut self) -> Option<T> {
        self.next().map(|node| unsafe {
            self.list.len -= 1;
            self.current_len %= self.list.len + 1;

            let node = Box::from_raw(node.as_ptr());
            match self.current {
                None => self.list.head = node.next,
                Some(mut prev) => prev.as_mut().next = node.next,
            }
            match node.next {
                None => self.list.tail = self.current,
                Some(mut next) => {
                    next.as_mut().prev = self.current;
                }
            }
            Node::into_element(node)
        })
    }
    /// Remove and return the item before the cursor
    pub fn pop_prev(&mut self) -> Option<T> {
        self.prev().map(|node| unsafe {
            self.list.len -= 1;
            self.dec_len();

            let node = Box::from_raw(node.as_ptr());
            match node.prev {
                None => self.list.head = self.current,
                Some(mut prev) => prev.as_mut().next = self.current,
            }
            match self.current {
                None => self.list.tail = node.prev,
                Some(mut next) => next.as_mut().prev = node.prev,
            }
            Node::into_element(node)
        })
    }

    fn split_at(self, mut current: NonNull<Node<T>>, split_len: usize) -> LinkedList<T> {
        let total_len = self.list.len;

        let next = unsafe { current.as_ref().next };

        if let Some(mut next) = next {
            let new_head = Some(next);
            let new_tail = self.list.tail.take();
            let new_len = total_len - split_len;

            let old_head = self.list.head;
            let old_tail = Some(current);
            let old_len = total_len - new_len;

            unsafe {
                current.as_mut().next = None;
                next.as_mut().prev = None;
            }

            self.list.head = old_head;
            self.list.tail = old_tail;
            self.list.len = old_len;

            LinkedList {
                head: new_head,
                tail: new_tail,
                len: new_len,
                marker: PhantomData,
            }
        } else {
            LinkedList::new()
        }
    }

    /// Split the list in two after the current element
    /// The returned list consists of all elements following but not including
    /// the current one.
    // note: consuming the cursor is not necessary here, but it makes sense
    // given the interface
    pub fn split_after(self) -> LinkedList<T> {
        use std::mem::replace;

        match self.current {
            None => match self.end {
                // not including empty element in head = all of the elements
                Some(End::Head) => replace(self.list, LinkedList::new()),
                // not including empty element in tail = none of the elements
                Some(End::Tail) => LinkedList::new(),
                // empty list = none of the elements
                None => LinkedList::new(),
            },

            Some(current) => {
                let split_len = self.current_len;
                self.split_at(current, split_len + 1)
            }
        }
    }

    /// Split the list in two before the current element
    /// The returned list consists of all elements following and including
    /// the current one.
    pub fn split_before(self) -> LinkedList<T> {
        use std::mem::replace;

        match self.current {
            None => match self.end {
                // including empty element in head = all of the elements
                Some(End::Head) => replace(self.list, LinkedList::new()),
                // including empty element in tail = none of the elements
                Some(End::Tail) => LinkedList::new(),
                // empty list = none of the elements
                None => LinkedList::new(),
            },
            Some(current) => match unsafe { current.as_ref().prev } {
                None => replace(self.list, LinkedList::new()),
                Some(prev) => {
                    let split_len = self.current_len;
                    self.split_at(prev, split_len)
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use std::iter::FromIterator;

    use super::{End, LinkedList};

    fn mut_cmp_iterator<T, I>(list: &mut LinkedList<T>, iter: I)
    where
        T: PartialEq + Debug,
        I: IntoIterator<Item = T> + Clone + Iterator + DoubleEndedIterator<Item = T>,
    {
        {
            let mut cursor = list.head_mut();
            for i in iter.clone() {
                let mut i = i;
                assert_eq!(cursor.current(), Some(&mut i));
                cursor.move_next();
            }
            assert_eq!(cursor.current(), None);
        }
        {
            let mut cursor = list.tail_mut();
            let iter = iter.rev();

            for i in iter {
                let mut i = i;
                assert_eq!(cursor.current(), Some(&mut i));
                cursor.move_prev();
            }
            assert_eq!(cursor.current(), None);
        }
    }

    fn cmp_iterator<T, I>(list: &LinkedList<T>, iter: I)
    where
        T: PartialEq + Debug,
        I: Iterator<Item = T>,
    {
        let v = iter.collect::<Vec<T>>();
        println!("cmp {:?} {:?}", list, v);

        {
            // test raw links
            let mut cursor = list.head();
            while let Some(current) = cursor.current {
                if let Some(next) = unsafe { current.as_ref().next } {
                    assert_eq!(unsafe { next.as_ref().prev }, Some(current));
                }
                cursor.move_next();
            }
        }
        {
            // test forwards iteration
            let mut cursor = list.head();
            for i in v.iter() {
                assert_eq!(cursor.current(), Some(i));
                cursor.move_next();
            }

            assert_eq!(cursor.current(), None);
        }
        {
            // test reverse iteration
            let mut cursor = list.tail();
            for i in v.iter().rev() {
                //println!("{:?}", cursor.current());
                assert_eq!(cursor.current(), Some(i));
                cursor.move_prev();
            }

            assert_eq!(cursor.current(), None);
        }
    }

    #[test]
    fn sanity_test() {
        println!("{:?}", &LinkedList::from_iter(0..10));
        cmp_iterator(&LinkedList::from_iter(0..10), 0..10);
        mut_cmp_iterator(&mut LinkedList::from_iter(0..10), 0..10);
    }
    #[test]
    fn reverse() {
        let list = LinkedList::from_iter(0..4);
        println!("{:?}", &list);
        let mut cursor = list.tail();
        for i in (0..4).rev() {
            assert_eq!(cursor.current(), Some(&i));
            cursor.move_prev();
        }
        cursor.move_prev();
        assert_eq!(cursor.current(), None);
    }
    #[test]
    fn peek_after() {
        let list = LinkedList::from_iter(3..6);
        let mut cursor = list.head();
        assert_eq!(cursor.peek_after(), Some(&4));
        assert_eq!(cursor.peek_before(), None);
        cursor.move_next();
        assert_eq!(cursor.peek_after(), Some(&5));
        assert_eq!(cursor.peek_before(), Some(&3));
        cursor.move_next();
        assert_eq!(cursor.peek_after(), None);
        assert_eq!(cursor.peek_before(), Some(&4));
    }
    #[test]
    fn split_len() {
        let mut list = LinkedList::from_iter(0..5);
        assert_eq!(list.len, 5);
        let list2 = {
            let mut cursor = list.head_mut();
            cursor.move_next();
            cursor.split_after()
        };
        assert_eq!(list.len, 2);
        assert_eq!(list2.len, 3);
    }

    /*
        [Node:2] <- [List] ->   [Node:0]
            None  <- [Node:0] -> [Node:1]
        [Node:0] -> [Node:1] -> [Node:2]
        [Node:1] -> [Node:2] ->  None
    
        [Node:0] <- [List] ->   [Node:0]
            None  <- [Node:0] ->  None
    
        test cases:
            [F] cursor before head:
                current = None, end = Head
            [B] cursor after tail:
                current = None, end = Tail
            [H] cursor has no prev:
                current = [Node:0], end = None
            [T] cursor has no next:
                current = [Node:2], end = None
            [G] general case:
                current = [Node:1], end = None
    
            [S] single element, neither prev nor next
                current = [Node:0], end = None
    
    */

    #[test]
    fn split_edge() {
        {
            let mut list = LinkedList::from_iter(0..5);
            let tail = {
                let mut c = list.head_mut();
                c.move_prev();
                c.split_after()
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, 0..0);
            cmp_iterator(&tail, 0..5);
        }
        {
            let mut list = LinkedList::from_iter(0..5);
            let tail = {
                let mut c = list.tail_mut();
                c.move_next();
                c.split_after()
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, 0..5);
            cmp_iterator(&tail, 0..0);
        }
        {
            let mut list = LinkedList::from_iter(0..5);
            let tail = {
                let mut c = list.head_mut();
                loop {
                    if c.current().is_some() {
                        c.move_next();
                    } else {
                        break;
                    }
                }
                c.split_after()
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, 0..5);
            cmp_iterator(&tail, 0..0);
        }
        {
            let mut list = LinkedList::from_iter(0..5);
            let tail = {
                let mut c = list.tail_mut();
                loop {
                    if c.current().is_some() {
                        c.move_prev();
                    } else {
                        break;
                    }
                }
                c.split_after()
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, 0..0);
            cmp_iterator(&tail, 0..5);
        }
    }

    #[test]
    fn split_after() {
        use std::ops::Range;
        type Rng = Range<isize>;
        fn test_split(elems: Rng, i: isize, left: Rng, right: Rng) {
            let mut list = LinkedList::from_iter(elems);

            print!("split_after {:?} at {}", list, i);
            let tail = {
                let mut c = if i >= 0 {
                    let mut c = list.head_mut();
                    for _ in 0..i {
                        c.move_next();
                    }
                    c
                } else {
                    let mut c = list.tail_mut();
                    for _ in i..-1 {
                        c.move_prev();
                    }
                    c
                };

                println!(" = {:?}", c.current());
                c.split_after()
            };

            println!("+++ {:?}, {:?}", list, tail);

            println!(
                "--- {:?}, {:?}",
                left.clone().collect::<Vec<isize>>(),
                right.clone().collect::<Vec<isize>>()
            );
            cmp_iterator(&list, left);
            cmp_iterator(&tail, right);
        }

        test_split(-10..0, -11, 0..0, -10..0); // case F
        test_split(0..10, 10, 0..10, 0..0); // case B
        test_split(0..10, 0, 0..1, 1..10); // case H
        test_split(0..10, 9, 0..10, 10..10); // case T
        test_split(0..10, 3, 0..4, 4..10); // case G
        test_split(-10..0, -3, -10..-2, -2..0); // case G
        test_split(0..1, -1, 0..1, 0..0); // case F/S
        test_split(0..1, 1, 0..1, 0..0); // case B/S
        test_split(0..1, 0, 0..1, 0..0); // case S
    }
    #[test]
    fn split_before() {
        use std::ops::Range;
        type Rng = Range<isize>;
        fn test_split(elems: Rng, i: isize, left: Rng, right: Rng) {
            let mut list = LinkedList::from_iter(elems);

            print!("split_after {:?} at {}", list, i);
            let tail = {
                let mut c = if i >= 0 {
                    let mut c = list.head_mut();
                    for _ in 0..i {
                        c.move_next();
                    }
                    c
                } else {
                    let mut c = list.tail_mut();
                    for _ in i..-1 {
                        c.move_prev();
                    }
                    c
                };

                println!(" = {:?}", c.current());
                c.split_before()
            };

            println!("+++ {:?}, {:?}", list, tail);

            println!(
                "--- {:?}, {:?}",
                left.clone().collect::<Vec<isize>>(),
                right.clone().collect::<Vec<isize>>()
            );
            cmp_iterator(&list, left);
            cmp_iterator(&tail, right);
        }

        test_split(-10..0, -11, 0..0, -10..0); // case F
        test_split(0..10, 10, 0..10, 0..0); // case B
        test_split(0..10, 0, 0..0, 0..10); // case H
        test_split(0..10, 9, 0..9, 9..10); // case T
        test_split(0..10, 3, 0..3, 3..10); // case G
        test_split(-10..0, -3, -10..-3, -3..0); // case G
        test_split(0..1, -1, 0..0, 0..1); // case F/S
        test_split(0..1, 1, 0..1, 0..0); // case B/S
        test_split(0..1, 0, 0..0, 0..1); // case S
    }

    #[test]
    fn usecase_split() {
        type Rng = std::ops::Range<usize>;
        fn test_surprise(n: usize, v: usize, left: Rng, right: Rng) {
            let mut list = LinkedList::from_iter(0..n);
            print!("split_before {:?} when e == {:?}: ", list, v);
            let tail = {
                let mut c = list.head_mut();
                loop {
                    let split_after = match c.current() {
                        Some(i) => i == &v,
                        None => {
                            break LinkedList::new();
                        }
                    };
                    if split_after {
                        break c.split_after();
                    }
                    c.move_next();
                }
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, left);
            cmp_iterator(&tail, right);
        }

        use std::cmp::min;
        for i in 0..6 {
            test_surprise(5, i, 0..min(i + 1, 5), min(i + 1, 5)..5);
        }
    }

    #[test]
    fn usecase_split_before() {
        type Rng = std::ops::Range<usize>;
        fn test_surprise_before(n: usize, v: usize, left: Rng, right: Rng) {
            let mut list = LinkedList::from_iter(0..n);
            print!("split_before {:?} when e == {:?}: ", list, v);
            let tail = {
                let mut c = list.head_mut();
                loop {
                    let split_after = match c.current() {
                        Some(i) => i == &v,
                        None => {
                            break LinkedList::new();
                        }
                    };
                    if split_after {
                        break c.split_before();
                    }
                    c.move_next();
                }
            };
            println!("{:?}, {:?}", list, tail);
            cmp_iterator(&list, left);
            cmp_iterator(&tail, right);
        }

        for i in 0..6 {
            test_surprise_before(5, i, 0..i, i..5);
        }
    }

    #[test]
    fn new_cursor_1() {
        let list = LinkedList::from_iter(0..4);
        let c = list.head();
        assert_eq!(c.current(), Some(&0));
    }
    #[test]
    fn new_cursor_2() {
        let list = LinkedList::from_iter(0..4);
        let c = list.tail();
        assert_eq!(c.current(), Some(&3));
    }
    #[test]
    fn new_cursor_3() {
        let n = 3;
        let list = LinkedList::from_iter(0..n);
        let mut c = list.head();

        for i in 0..n {
            assert_eq!(c.current(), Some(&i));
            assert_eq!(c.end, None);
            c.move_next();
        }

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Tail));

        c.move_next();

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Tail));

        c.move_prev();

        for i in (0..n).rev() {
            assert_eq!(c.current(), Some(&i));
            assert_eq!(c.end, None);
            c.move_prev();
        }

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Head));
        c.move_prev();
        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Head));
    }

    #[test]
    fn new_cursor_mut_1() {
        let mut list = LinkedList::from_iter(0..4);
        let mut c = list.head_mut();
        assert_eq!(c.current(), Some(&mut 0));
    }
    #[test]
    fn new_cursor_mut_2() {
        let mut list = LinkedList::from_iter(0..4);
        let mut c = list.tail_mut();
        assert_eq!(c.current(), Some(&mut 3));
    }
    #[test]
    fn new_cursor_mut_3() {
        let n = 3;
        let mut list = LinkedList::from_iter(0..n);
        let mut c = list.head_mut();

        for i in 0..n {
            let mut i = i;
            assert_eq!(c.current(), Some(&mut i));
            assert_eq!(c.end, None);
            c.move_next();
        }

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Tail));

        c.move_next();

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Tail));

        c.move_prev();

        for i in (0..n).rev() {
            let mut i = i;
            assert_eq!(c.current(), Some(&mut i));
            assert_eq!(c.end, None);
            c.move_prev();
        }

        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Head));
        c.move_prev();
        assert_eq!(c.current(), None);
        assert_eq!(c.end, Some(End::Head));
    }

    #[test]
    fn insert_tail_before() {
        let mut list = LinkedList::new();
        {
            let mut c = list.cursor_mut(End::Tail); // []<>
            assert_eq!(c.current_len, 0);
            c.insert_before(0); // [0]<>
            assert_eq!(c.current_len, 1);
            assert_eq!(c.peek_before(), Some(&mut 0));
            c.insert_before(1); // [0, 1]<>
            assert_eq!(c.current_len, 2);
            assert_eq!(c.peek_before(), Some(&mut 1));
            c.insert_before(2); // [0, 1, 2]<>
            assert_eq!(c.current_len, 3);
            assert_eq!(c.peek_before(), Some(&mut 2));
        }
        cmp_iterator(&list, 0..3);
    }
    #[test]
    fn insert_tail_after() {
        let mut list: LinkedList<usize> = LinkedList::new();
        {
            let mut c = list.cursor_mut(End::Tail); // []<>
            c.insert_after(0); // <>[0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 0));
            c.insert_after(1); // <>[1, 0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 1));
            c.insert_after(2); // <>[2, 1, 0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 2));
        }
        println!("{:?}", list);
        cmp_iterator(&list, (0..3).rev());
    }
    #[test]
    fn insert_head_before() {
        let mut list: LinkedList<usize> = LinkedList::new();
        {
            let mut c = list.cursor_mut(End::Head); // <>[]
            c.insert_before(0); // [0]<>
            assert_eq!(c.current_len, 1);
            assert_eq!(c.peek_before(), Some(&mut 0));
            c.insert_before(1); // [0, 1]<>
            assert_eq!(c.current_len, 2);
            assert_eq!(c.peek_before(), Some(&mut 1));
            c.insert_before(2); // [0, 1, 2]<>
            assert_eq!(c.current_len, 3);
            assert_eq!(c.peek_before(), Some(&mut 2));
        }
        println!("{:?}", list);
        cmp_iterator(&list, 0..3);
    }
    #[test]
    fn insert_head_after() {
        let mut list: LinkedList<usize> = LinkedList::new();
        {
            let mut c = list.cursor_mut(End::Head); // <>[]
            c.insert_after(0); // <>[0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 0));
            c.insert_after(1); // <>[1, 0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 1));
            c.insert_after(2); // <>[2, 1, 0]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 2));
        }
        println!("{:?}", list);
        cmp_iterator(&list, (0..3).rev());
    }
    #[test]
    fn insert_mixed() {
        let mut list = LinkedList::new();
        {
            let mut c = list.cursor_mut(End::Head); // <>[]
            assert_eq!(c.current_len, 0);
            c.insert_before(0); // [0]<>
            assert_eq!(c.current_len, 1);
            assert_eq!(c.peek_before(), Some(&mut 0));
            c.move_next(); // [0]<>
            assert_eq!(c.current_len, 1);
            assert_eq!(c.peek_before(), Some(&mut 0));
            c.insert_after(2); // [<0>, 2]
            assert_eq!(c.current_len, 0);
            assert_eq!(c.peek_after(), Some(&mut 2));
            c.move_next(); // [0, <2>]
            assert_eq!(c.current_len, 1);
            assert_eq!(c.peek_before(), Some(&mut 0));
            c.insert_before(1); // [0, 1, <2>]
            assert_eq!(c.current_len, 2);
            assert_eq!(c.peek_before(), Some(&mut 1));
        }
        cmp_iterator(&list, 0..3);
    }

    #[test]
    fn insert_list_empty() {
        let mut list: LinkedList<usize> = LinkedList::from_iter(0..3);
        {
            let mut c = list.tail_mut();
            let ins = LinkedList::from_iter(0..0);
            assert_eq!(ins.len, 0);
            c.insert_list_after(ins);
            assert_eq!(c.current_len, 2);
        }
        assert_eq!(list.len, 3);
        println!("{:?}", list);
        cmp_iterator(&list, 0..3);
    }
    #[test]
    fn insert_list_after() {
        let mut list: LinkedList<usize> = LinkedList::from_iter(0..3);
        {
            let mut c = list.tail_mut();
            let ins = LinkedList::from_iter(3..6);
            assert_eq!(ins.len, 3);
            c.insert_list_after(ins);
            assert_eq!(c.current_len, 2);
            assert_eq!(c.peek_after(), Some(&mut 3));
        }
        assert_eq!(list.len, 6);
        println!("{:?}", list);
        cmp_iterator(&list, 0..6);
        {
            let mut c = list.tail_mut();
            for _ in 0..3 {
                c.move_prev()
            }
            let ins = LinkedList::from_iter(6..9);
            assert_eq!(ins.len, 3);
            c.insert_list_after(ins);
            assert_eq!(c.current_len, 2);
            assert_eq!(c.peek_after(), Some(&mut 6));
        }
        assert_eq!(list.len, 9);
        println!("{:?}", list);
        cmp_iterator(&list, (0..3).chain(6..9).chain(3..6));
    }
    fn insert_list_before() {
        let mut list: LinkedList<usize> = LinkedList::from_iter(3..6);
        {
            let mut c = list.head_mut();
            let ins = LinkedList::from_iter(0..3);
            assert_eq!(ins.len, 3);
            c.insert_list_before(ins);
            assert_eq!(c.current_len, 3);
            assert_eq!(c.peek_before(), Some(&mut 2));
        }
        assert_eq!(list.len, 6);
        println!("{:?}", list);
        cmp_iterator(&list, 0..6);
        {
            let mut c = list.head_mut();
            for _ in 0..3 {
                c.move_next()
            }
            let ins = LinkedList::from_iter(6..9);
            assert_eq!(ins.len, 3);
            c.insert_list_before(ins);
            assert_eq!(c.current_len, 6);
            assert_eq!(c.peek_after(), Some(&mut 6));
        }
        assert_eq!(list.len, 9);
        println!("{:?}", list);
        cmp_iterator(&list, (0..3).chain(6..9).chain(3..6));
    }
    #[test]
    fn current_len() {
        let mut list: LinkedList<usize> = LinkedList::from_iter(0..3);
        println!("{:?}", list);
        cmp_iterator(&list, 0..3);

        {
            let mut c = list.head_mut(); // [<0>, 1, 2]
            assert_eq!(c.current_len, 0);
            c.move_next(); // [0, <1>, 2]
            assert_eq!(c.current_len, 1);
            c.move_next(); // [0, 1, <2>]
            assert_eq!(c.current_len, 2);
            c.move_next(); // [0, 1, 2]<>
            assert_eq!(c.current_len, 3);
            c.move_prev(); // [0, 1, <2>]
            assert_eq!(c.current_len, 2);
            c.move_prev(); // [0, <1>, 2]
            assert_eq!(c.current_len, 1);
            c.move_prev(); // [<0>, 1, 2]
            assert_eq!(c.current_len, 0);
            c.move_prev(); // <>[0, 1, 2]
            assert_eq!(c.current_len, 0);
            c.move_next(); // [<0>, 1, 2]
            assert_eq!(c.current_len, 0);
        }

        {
            let mut c = list.cursor_mut(End::Head);
            assert_eq!(c.current_len, 0);
            c.move_next();
            assert_eq!(c.current_len, 0);
            c.move_next();
            assert_eq!(c.current_len, 1);
            c.move_next();
            assert_eq!(c.current_len, 2);
            c.move_next();
            assert_eq!(c.current_len, 3);
            c.move_next();
            assert_eq!(c.current_len, 3);
        }

        {
            let mut c = list.cursor_mut(End::Tail);
            assert_eq!(c.current_len, 3);
            c.move_prev();
            assert_eq!(c.current_len, 2);
            c.move_prev();
            assert_eq!(c.current_len, 1);
            c.move_prev();
            assert_eq!(c.current_len, 0);
            c.move_prev();
            assert_eq!(c.current_len, 0);
        }
    }

    //#[test]
    fn broken() {
        {
            let mut list: LinkedList<usize> = LinkedList::from_iter(0..3);
            {
                let mut c = list.tail_mut();
                c.insert_list_after(LinkedList::from_iter(3..6));
            }
            println!("{:?}", list);
            cmp_iterator(&list, 0..6);
        }

        assert!(false, "unchecked");
    }
}
