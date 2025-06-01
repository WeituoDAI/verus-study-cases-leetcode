use vstd::prelude::*;
use vstd::math::{ max};

mod listnode;

pub use listnode::*;

verus!{

spec fn wf(x:ListNode<u32>) -> bool
  decreases x
{
  &&& 0 <= x.val <= 9
  &&& match x.next {
    None => true,
    Some(next) => wf(*next)
  }
}

spec fn as_num(x:ListNode<u32>) -> int
  decreases x
{
  let sum = x.val;
  match x.next {
    None => sum as int,
    Some(next) => (as_num(*next) * 10 + sum),
  }
}

spec fn as_num_option(x:Option<Box<ListNode<u32>>>) -> int
{
  match x {
    None => 0,
    Some(x) => as_num(*x)
  }
}

// fn test_my(){
//   let x = ListNode::<u32>::new(8);
//   assert(as_num(x) == 8) by { reveal_with_fuel(as_num, 2)}
//   let y = ListNode::new_with_next(1, x);
//   assert(as_num(y) == 81) by { reveal_with_fuel(as_num, 2)}
//   let z = ListNode::new_with_next(0, y);
//   assert(as_num(z) == 810) by { reveal_with_fuel(as_num, 2)}
//   let w = ListNode::new_with_next(2, z);
//   assert(as_num(w) == 8102) by { reveal_with_fuel(as_num, 2)}
// }

spec fn len_option(l:Option<Box<ListNode<u32>>>) -> int{
  match l {
    None => 0,
    Some(l) => l.len_spec()
  }
}

fn helper(l1: Option<Box<ListNode<u32>>>, l2: Option<Box<ListNode<u32>>>,carry : &mut u32)
  -> (res:Option<Box<ListNode<u32>>>)
  requires
    match l1 {None => true, Some(l) => wf(*l) },
    match l2 {None => true, Some(l) => wf(*l) },
    *old(carry) == 0 || *old(carry) == 1,
  ensures
    *(carry) == 0 || *(carry) == 1,
    as_num_option(l1) + as_num_option(l2) + *old(carry) == as_num_option(res)

  decreases
    max(len_option(l1), len_option(l2)), *old(carry)
{
  if *carry == 0 && l1.is_none() && l2.is_none(){
      return None;
  }
  let a = match l1 {
      Some(T) => *T,
      None => ListNode::new(0),
  };
  let b = match l2 {
      Some(T) => *T,
      None => ListNode::new(0),
  };
  let  val_raw : u32 = a.val + b.val + *carry;
  // assert(val_raw < 20);
  let mut node : ListNode<u32> = ListNode::new(val_raw%10);
  *carry = val_raw/10;
  // assert(*carry == 0 || *carry == 1);

  assert(decreases_to!(max(len_option(l1), len_option(l2)), *old(carry) =>
    max(len_option(a.next), len_option(b.next)), *carry)) by
  {
    if l1.is_Some() {
      assert(len_option(l1) >= 1) by { l1.unwrap().lemma_len_positive()};
      // assert(
      //   max(len_option(a.next), len_option(b.next)) ==
      //   max(len_option(l1), len_option(l2)) - 1
      // );
    }
    else if l2.is_Some() {
      assert(len_option(l2) >= 1) by { l2.unwrap().lemma_len_positive() }
      // assert(
      //   max(len_option(a.next), len_option(b.next)) ==
      //   max(len_option(l1), len_option(l2)) - 1
      // );
    }
    else{
      // assert(
      //   max(len_option(a.next), len_option(b.next)) ==
      //   max(len_option(l1), len_option(l2))
      // );
      assert(*old(carry) == 1);
      assert(*carry == 0);
    }
  }

  // if l1 == None, l2 == None, old(carry) == 1
  // carry == 0, node = ListNode::new(1)

  // if l1 ~ Seq[5], l2 == None, old(carry) == 1
  // carry = 0, node = ListNode { val:6, next: None }

  // if l1 ~ Seq[5], l2 ~ Seq[4], old(carry) ==1
  // carry = 1, node = ListNode { val:0, next: helper(None, None, 1)}

  node.next = helper(a.next,b.next,carry);
  return Some(Box::new(node));
}

fn add_two_numbers(l1: Option<Box<ListNode<u32>>>, l2: Option<Box<ListNode<u32>>>)
  -> (res:Option<Box<ListNode<u32>>>)
  requires
    match l1 {None => true, Some(l) => wf(*l) },
    match l2 {None => true, Some(l) => wf(*l) },
  ensures
    as_num_option(res) == as_num_option(l1) + as_num_option(l2)
{
  let mut carry = 0;
  return helper(l1, l2, &mut carry)
}



}//verus!


fn main(){}