mod listnode;

use vstd::prelude::*;
use listnode::*;


verus!{


pub open spec fn seq_delete_dup(s:Seq<i32>) -> Seq<i32>
  // requires !s.contains(1000)
{
  seq_delete_dup_aux(s, -1000 as i32)
}

pub open spec fn seq_delete_dup_aux(s:Seq<i32>, prev:i32) -> Seq<i32>
  decreases s.len()
{
  if s.len() == 0 { s }
  else {
    if s[0] == prev { seq_delete_dup_aux(s.subrange(1, s.len() as int), prev) }
    else {
      let s1 = s.subrange(1, s.len() as int);
      if s1.len() == 0 { s }
      else if s1[0] == s[0] {
        seq_delete_dup_aux(s1.subrange(1, s1.len() as int), s[0])
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        seq![s[0]] + s2
      }
    }
  }
}


pub open spec fn myview(x:Option<Box<ListNode<i32>>>) -> Seq<i32>{
  match x {
    None => seq![],
    Some(x) => x@,
  }
}

fn aux(head: Option<Box<ListNode<i32>>>, prev:i32) -> (res:Option<Box<ListNode<i32>>>)
  ensures
    myview(res) =~= seq_delete_dup_aux(myview(head), prev)
  decreases head,
{
  match head {
      None => return head,
      Some(mut x) => {
          if x.val == prev{
              proof{
                assert(myview(x.next) =~= myview(head).subrange(1, myview(head).len() as int));
              }
              return aux(x.next, prev)
          }
          else {
              if let Some(y) = x.next{
                if y.val == x.val{
                  proof{
                    assert(y@ =~= x@.subrange(1, x@.len() as int));
                    assert(myview(y.next) =~= y@.subrange(1, y@.len() as int));
                  }
                  return aux(y.next, y.val)
                }
                let ghost x0 = x;
                x.next = aux(Some(y), x.val);
                proof{
                  assert(y@ =~= x0@.subrange(1, x0@.len() as int));
                }
              }
              return Some(x);
          }
      }
  }
}

pub fn delete_duplicates(head: Option<Box<ListNode<i32>>>) -> (res:Option<Box<ListNode<i32>>>)
  // requires
  // head@ sorted, all values in head@ > -1000
  ensures
    myview(res) =~= seq_delete_dup(myview(head))
{
  aux(head, -1000) // we know there is no 1000 in the list
}


///// prove lemma about seq_delete_dup


// res is sorted, and its values are contained in s
proof fn lemma_0(s:Seq<i32>, res:Seq<i32>, prev:i32)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    res =~= seq_delete_dup_aux(s, prev),
  ensures
    forall |i:int, j:int| 0 <= i <= j < res.len() ==> res[i] <= res[j],
    forall |val:i32| res.contains(val) ==> s.contains(val),
  decreases
    s.len()
{
  if s.len() == 0 { }
  else {
    if s[0] == prev {
      assert(res =~= seq_delete_dup_aux(s.subrange(1, s.len() as int), prev));
      lemma_0(s.subrange(1, s.len() as int), res, prev);
    }
    else {
      let s1 = s.subrange(1, s.len() as int);
      if s1.len() == 0 { }
      else if s1[0] == s[0] {
        assert(res =~= seq_delete_dup_aux(s1.subrange(1, s1.len() as int), s[0]));
        lemma_0(s1.subrange(1, s1.len() as int), res, s[0]);
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        assert(res =~= seq![s[0]] + s2);
        lemma_0(s1, s2, s[0]);
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

// res does not contains prev
proof fn lemma_1(s:Seq<i32>, res:Seq<i32>, prev:i32)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    forall |i:int| 0 <= i < s.len() ==> s[i] >= prev,
    res =~= seq_delete_dup_aux(s, prev),
  ensures
    forall |i:int| 0 <= i < res.len() ==> res[i] > prev,
  decreases
    s.len()
{
  if s.len() == 0 { }
  else {
    if s[0] == prev {
      assert(res =~= seq_delete_dup_aux(s.subrange(1, s.len() as int), prev));
      lemma_1(s.subrange(1, s.len() as int), res, prev);
    }
    else {
      let s1 = s.subrange(1, s.len() as int);
      if s1.len() == 0 {}
      else if s1[0] == s[0] {
        assert(res =~= seq_delete_dup_aux(s1.subrange(1, s1.len() as int), s[0]));
        lemma_1(s1.subrange(1, s1.len() as int), res, s[0]);
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        assert(res =~= seq![s[0]] + s2);
        lemma_1(s1, s2, s[0]);
      }
    }
  }
}

//res does not contains any value that occurs more than twice in s
proof fn lemma_2(s:Seq<i32>, res:Seq<i32>, prev:i32, k:int)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    forall |i:int| 0 <= i < s.len() ==> s[i] >= prev,
    res =~= seq_delete_dup_aux(s, prev),
    0 <= k < s.len() - 1,
    s[k] == s[k + 1]
  ensures
    !res.contains(s[k])
  decreases
    s.len()
{
  if s.len() == 0 { }
  else {
    if s[0] == prev {
      assert(res =~= seq_delete_dup_aux(s.subrange(1, s.len() as int), prev));
      if k == 0{
        assert(prev == s[k]);
        lemma_1(s, res, prev);
      }
      else{
        assert(s[k] == s.subrange(1, s.len() as int)[k-1]);
        lemma_2(s.subrange(1, s.len() as int), res, prev, k-1);
      }
    }
    else {
      let s1 = s.subrange(1, s.len() as int);
      if s1.len() == 0 {}
      else if s1[0] == s[0] {
        assert(res =~= seq_delete_dup_aux(s1.subrange(1, s1.len() as int), s[0]));
        if k == 0 || k == 1{
          assert(s[0] == s[k]);
          lemma_1(s1.subrange(1, s1.len() as int), res, s[0])
        }
        else{
          assert(s[k] == s1.subrange(1, s1.len() as int)[k-2]);
          lemma_2(s1.subrange(1, s1.len() as int), res, s[0], k - 2);
        }
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        assert(res =~= seq![s[0]] + s2);
        if k == 0 {}
        else {
          assert(s[k] == s1[k-1]);
          lemma_2(s1, s2, s[0], k-1);
        }
      }
    }
  }
}


// res contains any value that occurs exactly once in s
proof fn lemma_3(s:Seq<i32>, res:Seq<i32>, prev:i32, k:int)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    forall |i:int| 0 <= i < s.len() ==> s[i] >= prev,
    res =~= seq_delete_dup_aux(s, prev),

    0 <= k < s.len(),
    s[k] != prev,
    k != s.len() - 1 ==> s[k + 1] != s[k],
    k != 0 ==> s[k-1] != s[k],

  ensures
    res.contains(s[k])

  decreases
    s.len()
{
  if s.len() == 0 { }
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s[0] == prev {
      assert(res =~= seq_delete_dup_aux(s1, prev));
      assert(k != 0);
      assert(s1[k-1] == s[k]);
      // if k != s.len() - 1 { assert(s1[k] == s[k+1]); }
      // if k > 1 { assert(s1[k-2] == s[k-1]); }
      lemma_3(s1, res, prev, k-1)
    }
    else {
      if s1.len() == 0 {}
      else if s1[0] == s[0] {
        let s2 = s1.subrange(1, s1.len() as int);
        assert(res =~= seq_delete_dup_aux(s2, s[0]));
        assert(k != 0);
        assert(k != 1);
        // if k != s.len() - 1 { assert(s2[k-1] == s[k+1]); }
        // if k > 2 { assert(s2[k-3] == s[k-1]); }
        lemma_3(s2, res, s[0], k-2)
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        assert(res =~= seq![s[0]] + s2);
        // if s1.len() == 0 {}
        // else{
        if k == 0 { assert(res[0] == s[0]) }
        else {
          // if k != s.len() - 1 { assert(s1[k] == s[k+1]) }
          // if k == 1 { assert(s[0] != s[1]); }
          // if k > 1 { assert(s1[k-2] == s[k-1])}
          lemma_3(s1, s2, s[0], k-1);
          let j = choose |j:int| 0 <= j < s2.len() && s2[j] == s1[k-1];
          assert(res[j+1] == s2[j]);
        }
      }
    }
  }
}


proof fn lemma_4(s:Seq<i32>, res:Seq<i32>, prev:i32, k:int)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    // forall |i:int| 0 <= i < s.len() ==> s[i] >= prev,
    res =~= seq_delete_dup_aux(s, prev),
    0 <= k < res.len() - 1,
  ensures
    res[k] != res[k+1],
    // forall |i:int| 0 <= i < res.len() ==> res[i] > prev,
  decreases
    s.len()
{
  if s.len() == 0 { }
  else {
    let s1 = s.subrange(1, s.len() as int);
    if s[0] == prev {
      assert(res =~= seq_delete_dup_aux(s1, prev));
      lemma_4(s1, res, prev, k);
    }
    else {
      if s1.len() == 0 {}
      else if s1[0] == s[0] {
        assert(res =~= seq_delete_dup_aux(s1.subrange(1, s1.len() as int), s[0]));
        lemma_4(s1.subrange(1, s1.len() as int), res, s[0], k);
      }
      else {
        let s2 = seq_delete_dup_aux(s1, s[0]);
        assert(res =~= seq![s[0]] + s2);
        if k == 0 {
          if s2.len() == 0 {}
          else {
            assert(res[0] == s[0]);
            lemma_1(s1, s2, s[0]);
          }
        }
        else {
          lemma_4(s1, s2, s[0], k-1);
        }
      }
    }
  }
}


proof fn lemma_5(s:Seq<i32>, res:Seq<i32>, prev:i32)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    res =~= seq_delete_dup_aux(s, prev),
  ensures
    forall |i:int, j:int| 0 <= i < j < res.len() ==> res[i] < res[j],
{
  assert forall |i:int, j:int| 0 <= i < j < res.len() implies res[i] < res[j] by{
    lemma_0(s, res, prev);
    assert(res[i] <= res[j]);
    if res[i] != res[j] {}
    else {
      assert(res[i] <= res[i + 1] <= res[j]);
      assert(res[i] == res[i + 1]);
      assert(false) by { lemma_4(s, res, prev, i) }
    }
  }
}

proof fn main_lamma(s:Seq<i32>, res:Seq<i32>)
  requires
    forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
    forall |i:int| 0 <= i < s.len() ==> s[i] > -1000,
    res =~= seq_delete_dup(s),
  ensures
    forall |i:int, j:int| 0 <= i < j < res.len() ==> res[i] < res[j],
    forall |val:i32| res.contains(val) ==> s.contains(val),
    forall |val:i32| #[trigger]s.to_multiset().count(val) >= 2 ==> !res.contains(val),
    forall |val:i32| #[trigger]s.to_multiset().count(val) == 1 ==> res.contains(val),
{
  lemma_0(s, res, -1000 as i32);
  lemma_5(s, res, -1000 as i32);

  assert forall |val:i32| #[trigger]s.to_multiset().count(val) >= 2
    implies !res.contains(val) by
  {
    lemma_to_multiset_1(s, val);
    let (a, b) = choose |a:int, b:int| 0 <= a < b < s.len() && #[trigger]s[a] == val && #[trigger]s[b] == val;
    assert(s[a] <= s[a+1] <= s[b]);
    assert(s[a] == s[a+1]);
    lemma_2(s, res, -1000 as i32, a)
  }

  assert forall |val:i32| #[trigger]s.to_multiset().count(val) == 1
    implies res.contains(val) by
  {
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    assert(s.contains(val));
    let k = choose |k:int| 0 <= k < s.len() && s[k] == val;
    assert(s.remove(k).to_multiset().count(val) == 0);
    assert(!s.remove(k).contains(val));
    assert(forall |i:int| 0 <= i < s.remove(k).len() ==> s.remove(k)[i] != val);
    assert(s.remove(k) =~= s.subrange(0, k) + s.subrange(k + 1, s.len() as int));
    assert forall |j:int| 0 <= j < s.len() && j != k implies s[j] != val by
    {
      if j < k {
        assert(s[j] == s.remove(k)[j])
      }
      else {
        assert(s[j] == s.remove(k)[j-1])
      }
    }
    lemma_3(s, res, -1000 as i32, k)
  }

}


//// lemma for Seq::to_multiset
proof fn lemma_to_multiset_1(s:Seq<i32>, val:i32)
  requires
    s.to_multiset().count(val) >= 2,
  ensures
    exists |i:int, j:int| 0 <= i < j < s.len() && #[trigger]s[i] == val && #[trigger]s[j] == val,
{
  broadcast use vstd::seq_lib::group_to_multiset_ensures;
  if (forall |i:int, j:int| 0 <= i < j < s.len() && #[trigger]s[i] == val ==> #[trigger]s[j] != val){
    assert(s.contains(val));
    let k = choose |k:int| 0 <= k < s.len() && s[k] == val;
    assert(s[k] == val);
    assert(s.remove(k).to_multiset().count(val) >= 1);
    assert(s.remove(k).contains(val));
    let h = choose |h:int| 0 <= h < s.remove(k).len() && s.remove(k)[h] == val;
    assert(false);
  }
  else {}
}












}//verus!

fn main(){}
