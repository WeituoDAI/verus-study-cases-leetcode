use vstd::prelude::*;

verus!{


pub open spec fn precondition(v:Vec<u32>) -> bool{
  &&& 1 <= v.len()
  &&& forall |i:int| 0 <= i < v.len() ==> 2 <= #[trigger]v@[i] <= 40
  &&& forall |i:int, j:int| 0 <= i < j < v.len() ==> v@[i] != v@[j]
  // &&& 1 <= target <= 40
}

pub open spec fn sum(s:Seq<u32>) -> int
  decreases s
{
  if s.len() == 0 { 0 }
  else {
    sum(s.drop_last()) + s.last()
  }
}


// pub fn vec_from_elems(x:u32, n:usize) -> (res:Vec<u32>)
//   ensures res@ =~= seq![x;n as nat],
// {
//   let mut v = Vec::new();
//   for i in 0..n
//     invariant
//       v@ =~= seq![x;i as nat]
//   {
//     v.push(x.clone())
//   }
//   return v;
// }

pub fn push_n_times(v:&mut Vec<u32>, x:u32, n:usize)
  ensures
    v@ =~= old(v)@ + seq![x;n as nat]
{
  for i in 0 .. n
    invariant
      v@ =~= old(v)@ + seq![x;i as nat]
  {
    v.push(x)
  }
}

proof fn lemma_sum_push_n_times(s:Seq<u32>, x:u32, n:nat)
  requires

  ensures
    sum(s + seq![x;n]) == sum(s) + x * n
  decreases n
{
  if n == 0 {}
  else if n == 1 {
    assert((s + seq![x;1]).drop_last() =~= s);
  }
  else {
    let s0 = s + seq![x;n];
    let s1 = s0.drop_last();
    assert(s1 =~= s + seq![x;(n-1) as nat]);
    assert(sum(s1) == sum(s) + x * (n-1)) by {
      lemma_sum_push_n_times(s, x, (n-1) as nat);
    }
    assert(sum(s0) == sum(s1) + x) by {
      lemma_sum_push_n_times(s1, x, 1);
    }
    assert(x * (n-1) + x == x * n) by (nonlinear_arith);
  }
}

// proof fn lemma_to_set_subset<T>(s1:Seq<T>, s2:Seq<T>, s3:Seq<T>)
//   requirs
//     s1.to_set().subset_of(s2.to_set())
// {}

#[verifier::loop_isolation(false)]
pub fn helper(tmp:Vec<u32>,can:&Vec<u32>, index:usize, target:u32, acc:&mut Vec<Vec<u32>>, Ghost(total):Ghost<u32>)
  requires
    precondition(*can),
    0 <= target <= 40,
    0 <= index <= can.len(),

    // forall |i:int| 0 <= i < tmp.len() ==> #[trigger]can@.contains(tmp@[i]),
    tmp@.to_set().subset_of(can@.to_set()),
    tmp@.to_set().subset_of(can@.subrange(0, index as int).to_set()),
    sum(tmp@) + target == total,

    forall |i:int| 0 <= i < old(acc).len() ==> #[trigger]sum(old(acc)@[i]@) == total,
    forall |i:int| 0 <= i < old(acc).len() ==> #[trigger] old(acc)@[i]@.to_set().subset_of(can@.to_set()),


  ensures
    old(acc).len() <= acc.len(),
    old(acc)@ =~= acc@.subrange(0, old(acc).len() as int),
    forall |i:int| 0 <= i < acc.len() ==> #[trigger]sum(acc@[i]@) == total,
    forall |i:int| 0 <= i < acc.len() ==> #[trigger] acc@[i]@.to_set().subset_of(can@.to_set()),

    forall |p:Vec<u32>| #![all_triggers]
      p.len() >= tmp.len() &&
      tmp@ =~= p@.subrange(0, tmp.len() as int) &&
      p@.subrange(tmp.len() as int, p.len() as int)
        .to_set().subset_of(can@.subrange(index as int, can.len() as int).to_set()) &&
      sum(p@) == total ==>

      exists |j:int| 0 <= j < acc.len() &&
      #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()
      // #[trigger] acc.deep_view().contains(p@),


  decreases can.len() - index,
{
  if target == 0 {
    acc.push(tmp);
    assert forall |p:Vec<u32>|#![all_triggers]
      p.len() >= tmp.len() &&
      tmp@ =~= p@.subrange(0, tmp.len() as int) &&
      p@.subrange(tmp.len() as int, p.len() as int)
        .to_set().subset_of(can@.subrange(index as int, can.len() as int).to_set()) &&
      sum(p@) == total implies

            exists |j:int| 0 <= j < acc.len() &&
            #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()

    by {
      assert(sum(tmp@) == total);
      assert(sum(p@) == total);
      assert(tmp@ =~= p@.subrange(0, tmp.len() as int));
      assert(tmp@ =~= p@) by{
        admit()
      }
      assert(acc@[acc.len() - 1]@ =~= tmp@);
      assert(acc@[acc.len() - 1]@.to_multiset() =~= p@.to_multiset());
    }
    return;
  }


  if index == can.len() {
    proof{
      assert forall |p:Vec<u32>|#![all_triggers]
        p.len() >= tmp.len() &&
        tmp@ =~= p@.subrange(0, tmp.len() as int) &&
        p@.subrange(tmp.len() as int, p.len() as int)
          .to_set().subset_of(can@.subrange(index as int, can.len() as int).to_set()) &&
        sum(p@) == total implies
          exists |j:int| 0 <= j < acc.len() &&
          #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()

        // #[trigger] acc.deep_view().contains(p@)
      by {
        assert(sum(tmp@) != total);
        assert(sum(p@) == total);

        if p.len() == tmp.len(){
          assert(p@ =~= tmp@);
          assert(false)
        }
        else{
          assert(can@.subrange(index as int, can.len() as int) =~= seq![]);
          let p1 = p@.subrange(tmp.len() as int, p.len() as int);
          assert(p1.to_set().is_empty());
          assert(p1 =~= seq![]) by{
            assert(p1.len() =~= p1.to_set().len()) by{
              p1.lemma_cardinality_of_empty_set_is_0()
            }
          }
          assert(p@ =~= tmp@);
          assert(false);
        }
      }
    }
    return;
  }


  let val = can[index];
  let num = target / val;
  assert(num * val <= target) by (nonlinear_arith)
    requires num == target / val;
  assert(num <= 40) by (nonlinear_arith)
    requires num == target / val, target <= 40, val >= 2;

  assert(tmp@.to_set().subset_of(can@.subrange(0, index + 1).to_set())) by{
    assert(tmp@.to_set().subset_of(can@.subrange(0, index as int).to_set()));
    assert(forall |k:int| 0 <= k < index ==>
      can@.subrange(0, index + 1)[k] == can@.subrange(0, index as int)[k]);
  }

  helper(tmp.clone(), can, index + 1, target, acc, Ghost(total));


  let mut i = 1;
  let ghost acc_prev = *acc;


  while i <= num
    invariant
      0 < target <= 40,
      0 <= index < can.len(),

      0 <= num <= 40,
      1 <= i <= num + 1,
      2 <= val <= 40,
      num * val <= target,

      old(acc).len() <= acc.len(),
      old(acc)@ =~= acc@.subrange(0, old(acc).len() as int),
      forall |i:int| 0 <= i < acc.len() ==> #[trigger]sum(acc@[i]@) == total,
      forall |i:int| 0 <= i < acc.len() ==> #[trigger] acc@[i]@.to_set().subset_of(can@.to_set()),

      acc_prev@ =~= acc@.subrange(0, acc_prev.len() as int),

      forall |p:Vec<u32>, k:int| #![all_triggers]
        0 <= k < i &&
        p.len() >= tmp.len() + k &&
        tmp@ =~= p@.subrange(0, tmp.len() as int) &&
        p@.subrange(tmp.len() as int, tmp.len() + k) =~= seq![val;k as nat] &&
        p@.subrange(tmp.len() + k, p.len() as int)
          .to_set().subset_of(can@.subrange(index + 1, can.len() as int).to_set()) &&
        sum(p@) == total ==>
        // acc.deep_view().contains(p@),
          exists |j:int| 0 <= j < acc.len() &&
          #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()


    decreases num + 1 - i
  {
    proof{
      acc_prev = *acc;
    }

    let mut v = tmp.clone();
    push_n_times(&mut v, val, i as usize);

    assert(i * val <= target) by (nonlinear_arith)
      requires 1 <= i <= num, val <= 40, num * val <= target;

    let new_target = target - i * val;
    assert(sum(v@) + new_target == total) by {
      lemma_sum_push_n_times(tmp@, val, i as nat);
      assert(sum(v@) == sum(tmp@) + val * i);
      assert(new_target == target - val * i) by (nonlinear_arith)
        requires new_target == target - i * val;
    }
    assert(v@.to_set().subset_of(can@.subrange(0, index + 1).to_set())) by{
      assert(v@.to_set() =~= tmp@.to_set().insert(val)) by {
        assert(v@ =~= tmp@ + seq![val; i as nat]);
        admit()
      }
      assert(tmp@.to_set().subset_of(can@.subrange(0, index as int).to_set()));
      assert(tmp@.to_set().subset_of(can@.subrange(0, index + 1).to_set()));
      assert(can@.subrange(0, index + 1)[index as int] == val);
    }
    helper(v, can, index + 1, new_target, acc, Ghost(total));
    i = i + 1;

    proof{
      assert forall |p:Vec<u32>, k:int| #![all_triggers]
        0 <= k < i &&
        p.len() >= tmp.len() + k &&
        tmp@ =~= p@.subrange(0, tmp.len() as int) &&
        p@.subrange(tmp.len() as int, tmp.len() + k) =~= seq![val;k as nat] &&
        p@.subrange(tmp.len() + k, p.len() as int)
          .to_set().subset_of(can@.subrange(index + 1, can.len() as int).to_set()) &&
        sum(p@) == total implies
        // acc.deep_view().contains(p@)
          exists |j:int| 0 <= j < acc.len() &&
          #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()
      by {
        if k == i - 1 {}
        else {
          let j0 = choose |j0:int| 0 <= j0 < acc_prev.len() &&
            #[trigger]acc_prev@[j0]@.to_multiset() =~= p@.to_multiset();
          assert(acc[j0]@.to_multiset() =~= p@.to_multiset());
        }
      }
    }
  }

  proof{

    assert(
      forall |p:Vec<u32>, k:int|
        0 <= k <= num &&
        p.len() >= tmp.len() + k &&
        tmp@ =~= p@.subrange(0, tmp.len() as int) &&
        p@.subrange(tmp.len() as int, tmp.len() + k) =~= seq![val;k as nat] &&
        #[trigger]p@.subrange(tmp.len() + k, p.len() as int)
          .to_set().subset_of(can@.subrange(index + 1, can.len() as int).to_set()) &&
        sum(p@) == total ==>

          exists |j:int| 0 <= j < acc.len() &&
          #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()
    );

    assert forall |p:Vec<u32>| #![all_triggers]
      p.len() >= tmp.len() &&
      tmp@ =~= p@.subrange(0, tmp.len() as int) &&
      p@.subrange(tmp.len() as int, p.len() as int).to_set()
          .subset_of(can@.subrange(index as int, can.len() as int).to_set()) &&
      sum(p@) == total implies
          exists |j:int| 0 <= j < acc.len() &&
          #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()
    by{

      if p@.contains(val){
        // p has n <= num  elements = val
        // rearrange p to get p0,
        //      s.t. p0.to_multiset() =~= p.to_multiset()
        //         && p0.subrange(0, tmp.len()) =~= tmp@
        //         && p0.subrange(tmp.len(), tmp.len() + n) =~= seq![val;n]

        // exists q0 . q0.to_multiset() =~= q.to_multiset(), q0 in acc
        // thus q0.to_multiset() =~= p
        admit()
      }
      else {
        assert(p@.subrange(tmp.len() as int, p.len() as int)
          .to_set().subset_of(can@.subrange(index as int, can.len() as int).to_set())
        );
        assert(p@.subrange(tmp.len() + 0, p.len() as int).to_set()
          .subset_of(can@.subrange(index + 1, can.len() as int).to_set())
        ) by{
          admit()
        }
        let k0 = choose |k0:int| 0 <= k0 < acc.len() &&
          #[trigger]acc@[k0]@.to_multiset() =~= p@.to_multiset();
      }


    }


  }
}


pub fn combination_sum(candidates: Vec<u32>, target: u32) -> (res:Vec<Vec<u32>>)
  requires
    precondition(candidates),
    1 <= target <= 40,
  ensures
    forall |i:int| 0 <= i < res.len() ==> #[trigger] sum(res@[i]@) == target,
    forall |i:int| 0 <= i < res.len() ==> #[trigger] res@[i]@.to_set().subset_of(candidates@.to_set()),

    forall |p:Vec<u32>| #![all_triggers]
      p@.to_set().subset_of(candidates@.to_set()) &&
      sum(p@) == target ==>
        exists |j:int| 0 <= j < res.len() &&
        #[trigger]res@[j]@.to_multiset() =~= p@.to_multiset()

{
  let mut acc = vec![];
  let tmp = vec![];
  helper(tmp, &candidates, 0, target, &mut acc, Ghost(target));

  proof{
    assert forall |p:Vec<u32>| #![all_triggers]
      p@.to_set().subset_of(candidates@.to_set()) &&
      sum(p@) == target implies
        exists |j:int| 0 <= j < acc.len() &&
        #[trigger]acc@[j]@.to_multiset() =~= p@.to_multiset()
    by
    {
      assert(p@.subrange(0, p@.len() as int) =~= p@);
      assert(candidates@.subrange(0, candidates.len() as int) =~= candidates@);
    }
  }

  return acc
}


}//verus!

fn main(){}