mod listnode;
use vstd::prelude::*;
use listnode::*;
use vstd::multiset::*;


// The use of &mut is limited in verus
// so I cannot give a solution without allocation/copy

verus!{

broadcast use vstd::seq_lib::group_to_multiset_ensures;

pub open spec fn is_sorted_option(l:Option<Box<ListNode<usize>>>) -> bool{
  match l {
    None => true,
    Some(l) =>
      forall |i:int, j:int| 0 <= i < j < l@.len() ==> l@[i] <= l@[j]
  }
}

pub proof fn lemma_is_sorted_next(l:Option<Box<ListNode<usize>>>)
  requires is_sorted_option(l), l.is_Some()
  ensures is_sorted_option(l.unwrap().next)
{
  let l2 = l.unwrap().next;
  match l2 {
    None => {},
    Some(l2) => {
      assert forall |i:int, j:int| 0 <= i < j < l2@.len() implies l2@[i] <= l2@[j] by
      {
        let l = l.unwrap();
        assert(l2@[i] == l@[i + 1]);
        assert(l2@[j] == l@[j + 1]);
      }
    }
  }
}

pub proof fn lemma_is_sorted_insert_front(l:Option<Box<ListNode<usize>>>)
  requires
    match l {
      None => true,
      Some(l) =>
        {
          &&& is_sorted_option(l.next)
          &&& match l.next {
            None => true,
            Some(l_next) =>
              {forall |i:int| 0 <= i < l_next@.len() ==>
                l_next@[i] >= l.val}
          }
        }
    }
  ensures
    is_sorted_option(l)
{
  if l.is_None(){}
  else {
    let l = l.unwrap();
    match l.next {
      None => {},
      Some(l_next) => {
        assert forall |i:int, j:int| 0 <= i < j < l@.len() implies l@[i] <= l@[j] by
        {
          if i > 0 {
            assert(l@[i] == l_next@[i-1]);
            assert(l@[j] == l_next@[j-1]);
          }
          else {
            assert(l@[i] == l.val);
            assert(l.val <= l_next@[0]);
          }
        }
      }
    }
  }
}


pub open spec fn to_multiset(l:Option<Box<ListNode<usize>>>) -> Multiset<usize>{
  match l {
    None => Multiset::empty(),
    Some(l) => l@.to_multiset()
  }
}


// copied from verus project. "examples/mergesort.rs"
pub broadcast proof fn lemma_to_multiset_distributes_over_add(s1: Seq<usize>, s2: Seq<usize>)
    ensures
        (#[trigger] (s1 + s2).to_multiset() =~= s1.to_multiset().add(s2.to_multiset())),
    decreases s2.len(),
{
    s2.to_multiset_ensures();
    if (s2.len() == 0) {
        assert((s1 + s2).to_multiset() =~= s1.to_multiset());
        assert(s2.to_multiset() =~= Multiset::<usize>::empty());
    } else {
        lemma_to_multiset_distributes_over_add(s1, s2.drop_last());
        vstd::seq::Seq::drop_last_distributes_over_add(s1, s2);
        assert(s2.drop_last() =~= s2.remove(s2.len() - 1));
        assert(s1 + s2 =~= (s1 + s2).drop_last().push(s2[(s2.len() - 1) as int]));
        assert((s1 + s2).to_multiset() =~= ((s1 + s2).drop_last().push(
            s2[(s2.len() - 1) as int],
        )).to_multiset());
        (s1 + s2).drop_last().to_multiset_ensures();
    }
}


pub proof fn lemma_to_multiset_insert_front(l:Option<Box<ListNode<usize>>>)
  requires l.is_Some(),
  ensures
    to_multiset(l) =~= seq![l.unwrap().val].to_multiset().add(to_multiset(l.unwrap().next)),
{
  broadcast use lemma_to_multiset_distributes_over_add;
}



pub fn merge_two_lists(l1: Option<Box<ListNode<usize>>>, l2: Option<Box<ListNode<usize>>>) -> (res:Option<Box<ListNode<usize>>>)
  requires
    is_sorted_option(l1),
    is_sorted_option(l2),
  ensures
    is_sorted_option(res),
    to_multiset(res) =~= to_multiset(l1).add(to_multiset(l2))
  decreases l1, l2
{
  broadcast use lemma_to_multiset_distributes_over_add;
  match (l1, l2) {
    (None, None) => None,
    (Some(n), None) | (None, Some(n)) => Some(n),
    (Some(l1), Some(l2)) => {
      let ghost l1_val = l1.val;
      let ghost l2_val = l2.val;
      proof{
        lemma_is_sorted_next(Some(l1));
        lemma_is_sorted_next(Some(l2));
        assert(l1.val == l1@[0]);
        assert(l2.val == l2@[0]);
      }
      let res =
        if l1.val >= l2.val {
          Some(Box::new(ListNode {
              val: l2.val,
              next: merge_two_lists(Some(l1), l2.next)
          }))
        } else {
          Some(Box::new(ListNode {
              val: l1.val,
              next: merge_two_lists(l1.next, Some(l2))
          }))
        };

      // Prove is_sorted_option(res)
      proof{
        let next = res.unwrap().next;
        let ghost minimum = if l1_val >= l2_val {l2_val} else {l1_val};
        assert(forall |i:int| 0 <= i < l1@.len() ==> minimum <= l1@[i]);
        assert(forall |i:int| 0 <= i < l2@.len() ==> minimum <= l2@[i]);
        assert(is_sorted_option(res)) by {
          if next.is_None(){}
          else {
            let s = next.unwrap()@;
            assert forall |i:int| 0 <= i < s.len()
              implies s[i] >= minimum
            by {
              let e = s[i];
              assert(s.contains(e));
              assert(s.to_multiset().contains(e));
              assert(to_multiset(next) =~= s.to_multiset());
              assert(to_multiset(next).contains(e));
              assert(to_multiset(Some(l1)).contains(e) || to_multiset(Some(l2)).contains(e));
              assert(l1@.contains(e) || l2@.contains(e));
            }
            lemma_is_sorted_insert_front(res);
          }
        }
      }

      // Prove to_multiset(res) =~= ...
      proof{
        lemma_to_multiset_insert_front(res);
      }
      res
    }
  }
}


}//verus!


fn main(){}