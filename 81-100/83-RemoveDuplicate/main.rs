mod listnode;

use vstd::prelude::*;
use listnode::*;


verus!{


pub open spec fn seq_delete_dup(s:Seq<i32>) -> Seq<i32>
  decreases s.len()
{
  if s.len() == 0 { s }
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s1.len() == 0 {
      s
    }
    else {
      if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        seq_delete_dup(seq![s[0]] + s2)
      }
      else {
        let s2 = seq_delete_dup(s1);
        seq![s[0]] + s2
      }
    }
  }
}



pub fn delete_duplicates(head: Option<Box<ListNode<i32>>>) -> (res:Option<Box<ListNode<i32>>>)
  ensures
    match head {
      None =>  res.is_none(),
      Some(h) => res.is_some() && res.unwrap()@ =~= seq_delete_dup(h@)
    }
  decreases head
{
  match head {
    None => return head,
    Some(mut x) => {
      if let Some(y) = x.next {
        if y.val == x.val {
          let ghost x0 = x;
          x.next = y.next;
          proof{
            assert(x@ =~= seq![x0@[0]] + x@.subrange(1, x@.len() as int));
            // assert(x0@[0] == x0@[1]);
            assert(y@ =~= x0@.subrange(1, x0@.len() as int));
            // assert(x0@[0] == y@[0]);
            // assert(x0@ =~= seq![x0@[0]] + y@);
            assert(seq_delete_dup(x0@) == seq_delete_dup(seq![x0@[0]] + y@.subrange(1, y@.len() as int)));
          }
          return delete_duplicates(Some(x));
        }
        else {
          let ghost x0 = x;
          x.next = delete_duplicates(Some(y));
          proof{
            assert(x0@ =~= seq![x0@[0]] + x0@.subrange(1, x0@.len() as int));
            assert(y@ =~= x0@.subrange(1, x0@.len() as int));
            // assert(x0@[0] != y@[0]);
            // assert(x0@[0] != x0@[1]);
            assert(seq_delete_dup(x0@) =~= seq![x0@[0]] + seq_delete_dup(y@));
          }
          return Some(x);
        }
      }
      return Some(x);
    }
  }
}

//// prove lemma about seq_delete_dup

// In leetcode, it is assumed that the list is sorted
proof fn lemma_0(s:Seq<i32>, res:Seq<i32>)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    res =~= seq_delete_dup(s),
  ensures
    forall |i:int, j:int| 0 <= i <= j < res.len() ==> res[i] <= res[j],
    forall |val:i32| res.contains(val) ==> s.contains(val),
  decreases
    s.len()
{
  if s.len() == 0 {}
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s1.len() == 0 {}
    else {
      if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        assert(res =~= seq_delete_dup(seq![s[0]] + s2));
        lemma_0(seq![s[0]] + s2, res);
      }
      else {
        let s2 = seq_delete_dup(s1);
        assert(res =~= seq![s[0]] + s2);
        lemma_0(s1, s2);
        assert forall |val:i32| res.contains(val) implies s.contains(val) by
        {
          let j = choose |j:int| 0 <= j < res.len() && res[j] == val;
          if j == 0 {}
          else {
            assert(s2[j-1] == val);
            assert(s2.contains(val));
          }
        }
        assert forall |i:int, j:int| 0 <= i <= j < res.len() implies res[i] <= res[j] by
        {
          if i == 0 {
            assert(res[0] == s[0]);
            assert(res.contains(res[j]));
            assert(s.contains(res[j]));
            let k = choose |k:int| 0 <= k < s.len() && s[k] == res[j];
            assert(s[0] <= s[k]);
          }
          else {}
        }
      }
    }
  }
}


proof fn lemma_1(s:Seq<i32>, res:Seq<i32>, val:i32)
  requires
    res =~= seq_delete_dup(s),
    s.contains(val),
  ensures
    res.contains(val),
  decreases
    s.len()
{
  if s.len() == 0 {}
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s1.len() == 0 {}
    else {
      if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        let s3 = seq![s[0]] + s2;
        assert(res =~= seq_delete_dup(s3));

        if val == s[0] {
          assert(s3[0] == s[0]);
          lemma_1(s3, res, val);
        }
        else {
          let k = choose |k:int| 0 <= k < s.len() && s[k] == val;
          assert(k != 0);
          assert(k != 1);
          assert(s2 =~= s.subrange(2, s.len() as int));
          assert(s2[k - 2] == s[k]);
          assert(s3[k - 1] == s[k]);
          lemma_1(s3, res, val);
        }
      }
      else {
        let s2 = seq_delete_dup(s1);
        assert(res =~= seq![s[0]] + s2);
        if val == s[0]{
          assert(res[0] == s[0]);
        }
        else{
          let k = choose |k:int| 0 <= k < s.len() && s[k] == val;
          assert(k != 0);
          assert(s1[k - 1] == s[k]);
          lemma_1(s1, s2, val);
          let j = choose |j:int| 0 <= j < s2.len() && s2[j] == val;
          assert(res[j + 1] == s2[j])
        }
      }
    }
  }
}


proof fn lemma_2(s:Seq<i32>, res:Seq<i32>)
  requires
    res =~= seq_delete_dup(s),
    s.len() > 0,
  ensures
    res.len() > 0,
    res[0] == s[0]
  decreases
    s.len()
{
  if s.len() == 0 {}
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s1.len() == 0 {}
    else {
      if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        assert(res =~= seq_delete_dup(seq![s[0]] + s2));
        lemma_2(seq![s[0]] + s2, res);
      }
      else {
        let s2 = seq_delete_dup(s1);
        assert(res =~= seq![s[0]] + s2);
      }
    }
  }
}



proof fn lemma_3(s:Seq<i32>, res:Seq<i32>, i:int)
  requires
    res =~= seq_delete_dup(s),
    0 <= i < res.len() - 1,
  ensures
    res[i] != res[i + 1],
  decreases
    s.len(),
{
  if s.len() == 0 {}
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s1.len() == 0 {}
    else {
      if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        let s3 = seq![s[0]] + s2;
        assert(res =~= seq_delete_dup(s3));
        lemma_3(s3, res, i)
      }
      else {
        let s2 = seq_delete_dup(s1);
        assert(res =~= seq![s[0]] + s2);
        if i == 0 {
          assert(s2.len() > 0 && s2[0] == s1[0]) by {lemma_2(s1, s2)}
          assert(res[1] == s2[0]);
        }
        else{
          lemma_3(s1, s2, i-1);
          assert(s2[i-1] != s2[i]);
          assert(res[i] == s2[i-1]);
          assert(res[i+1] == s2[i]);
        }
      }
    }
  }
}


proof fn lemma_4(s:Seq<i32>, res:Seq<i32>)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    res =~= seq_delete_dup(s),
  ensures
    // i.e. no duplicate
    forall |i:int, j:int| 0 <= i < j < res.len() ==> res[i] < res[j],
{
  assert forall |i:int, j:int| 0 <= i < j < res.len() implies res[i] < res[j] by{
    assert(res[i] <= res[j]) by { lemma_0(s, res) };
    if res[i] != res[j] {}
    else {
      assert(res[i] <= res[i + 1] <= res[j]) by { lemma_0(s, res) };
      assert(res[i] == res[i + 1]);
      assert(false) by { lemma_3(s, res, i) }
    }
  }
}

proof fn main_lemma(s:Seq<i32>, res:Seq<i32>)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    res =~= seq_delete_dup(s),
  ensures
    forall |i:int, j:int| 0 <= i < j < res.len() ==> res[i] < res[j],
    forall |val:i32| s.contains(val) <==> res.contains(val),
{
  lemma_4(s, res);
  lemma_0(s, res);
  assert forall |val:i32| s.contains(val) implies res.contains(val) by
  {
    lemma_1(s, res, val)
  }
}


}//verus!

fn main(){}