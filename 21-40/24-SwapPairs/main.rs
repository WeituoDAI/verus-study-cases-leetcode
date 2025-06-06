mod listnode;

use vstd::prelude::*;
use listnode::*;

verus!{

pub open spec fn as_seq<T>(node:Option<Box<ListNode<T>>>)
  -> Seq<T>
{
  match node {
    None => Seq::<T>::empty(),
    Some(node) => node@
  }
}

pub open spec fn swap_pairs_spec(s:Seq<i32>) -> Seq<i32>
  decreases s
{
  if s.len() == 0 || s.len() == 1 { s }
  else {
    seq![s[1], s[0]] + swap_pairs_spec(s.subrange(2, s.len() as int))
  }
}

pub fn swap_pairs(head: Option<Box<ListNode<i32>>>) -> (res:Option<Box<ListNode<i32>>>)
  ensures as_seq(res) =~= swap_pairs_spec(as_seq(head))
  decreases head,
{
  let ghost old_head = head;
  let ghost old_seq = as_seq(old_head);

  match head {
    Some(mut h) => {
      match h.next {
        Some(mut n) => {
          //// TODO : can we make this more automatic ???
          //// It is good to use this ?
          proof{ reveal_with_fuel(ListNode::view, 2); }
          // assert(n@ =~= old_seq.subrange(1, old_seq.len() as int));
          // assert(old_seq.len() >= 2);
          assert(as_seq(n.next) =~=
           old_seq.subrange(2, old_seq.len() as int)
          );
          h.next = swap_pairs(n.next);
          // assert(as_seq(h.next) =~= swap_pairs_spec(as_seq(n.next)));
          n.next = Some(h);
          // assert(n@ =~= seq![n.val] + h@);
          Some(n)
        },
        _ =>{
          Some(h)
        },
      }
    },
    _ => head,
  }
}

}//verus!


fn main(){}