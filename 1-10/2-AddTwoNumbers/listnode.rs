use vstd::prelude::*;


verus!{


#[derive(PartialEq, Eq)]
pub struct ListNode<T> {
  pub val: T,
  pub next: Option<Box<ListNode<T>>>
}

impl<T> ListNode<T> {
  #[inline]
  pub fn new(val: T) -> (res:Self)
    ensures
      res.next.is_None(),
      res.val == val,
  {
    ListNode {
      next: None,
      val
    }
  }

  #[inline]
  pub fn new_with_next(val:T, next:ListNode<T>) -> (res:Self)
    ensures
      res.next.is_Some(),
      res.next.unwrap() == next,
      res.val == val,
      // false
      res@ =~= seq![val] + next@
  {
    ListNode{
      next : Some(Box::new(next)),
      val,
    }
  }
}


impl<T> ListNode<T>{
  pub open spec fn view(&self) -> Seq<T>
    decreases self
  {
    let s = seq![self.val];
    match self.next {
      None => s,
      Some(next) => s + next.view()
    }
  }

  pub open spec fn wf_len_aux(&self, acc:int) -> bool
    decreases self
  {
    match self.next {
      None => acc < usize::MAX,
      Some(next) => acc + next.len_spec() < usize::MAX
    }
  }


  pub open spec fn wf_len(&self) -> bool{
    self.wf_len_aux(0)
  }

  pub fn len(&self) -> (res:usize)
    requires self.wf_len()
    ensures res == self.len_spec()
    decreases self
  {
    match &self.next {
      None => 1,
      Some(next) => 1 + next.len()
    }
  }

  pub open spec fn len_spec(&self) -> int
    decreases self
  {
    match self.next {
      None => 1,
      Some(next) => 1 + next.len_spec()
    }
  }

  pub proof fn lemma_len_positive(&self)
    ensures self.len_spec() >= 1
    decreases self
  {
    match self.next {
      None => {},
      Some(l) => { l.lemma_len_positive() }
    }
  }
}



pub fn test(){
  let h1 = ListNode::new(5i32);
  let h2 = ListNode { val : 6i32, next : Some(Box::new(h1))};

  assert(h1@ =~= seq![5i32]);

  assert(h2.view() =~= seq![6i32, 5i32]) by {
    reveal_with_fuel(ListNode::view, 3);
  }

  assert(h2.len_spec() == 2) by {
    reveal_with_fuel(ListNode::len_spec, 2)
  }
}




}//verus!


