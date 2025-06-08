use vstd::prelude::*;
use vstd::math::abs;

verus!{

pub fn abs_i32(x:i32) -> (res:i32)
  requires x > -100000 // just for example, this work for this problem
  ensures res == abs(x as int)
{
  if x < 0 { -x } else {x}
}

pub open spec fn is_sorted(v:&Vec<i32>) -> bool{
  forall |i:int, j:int| 0 <= i <= j < v.len() ==>
    v@[i] <= v@[j]
}


//An example mergesort in vstd/examples/mergesort.rs
#[verifier::external_body]
pub fn sort(v:&mut Vec<i32>)
  ensures
    is_sorted(v),
    v@.to_multiset() =~= old(v)@.to_multiset(),
    // all post conditions below can be deduced by v@.to_multiset() =~= old(v)@.to_multiset()

    v@.len() == old(v)@.len(),
    forall |val:i32| old(v)@.contains(val) <==> v@.contains(val),
    // forall |i:int, j:int, k:int|
    //   #![trigger old(v)@[i], old(v)@[j], old(v)@[k]]
    //   0 <= i < j < k < v.len() ==>
    //   (exists |p:int, q:int, r:int| 0 <= p < q < r < v.len() &&
    //     v@[p] == old(v)@[i] && v@[q] == old(v)@[j] && v@[r] == old(v)@[k]),

    // To avoid cyclic trigger, we cannot do this
    // forall |i:int, j:int, k:int|
    //   #![trigger v@[i], v@[j], v@[k]]
    //   0 <= i < j < k < v.len() ==>
    //   (exists |p:int, q:int, r:int| 0 <= p < q < r < v.len() &&
    //     v@[i] == old(v)@[p] && v@[j] == old(v)@[q] && v@[k] == old(v)@[r]),
{
  unimplemented!()
}

proof fn lemma_to_multiset(s1:Seq<i32>, s2:Seq<i32>, i:int, j:int, k:int)
  requires
    s1.to_multiset() =~= s2.to_multiset(),
    s1.len() == s2.len(),
    0 <= i < j < k < s1.len()
  ensures
    exists |p:int, q:int, r:int|
      0 <= p < q < r < s1.len() &&
        s2[p] + s2[q] + s2[r] == s1[i] + s1[j] + s1[k],
{
  admit()
  // we can prove, but it is not the important point of this problem
}





// proof fn lemma_to_multiset_1<T>(s:Seq<T>)
//   ensures
//     forall |v:T| #[trigger]s.contains(v) <==> s.to_multiset().contains(v)
// {
//   broadcast use vstd::multiset::group_multiset_axioms;
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;
// }
// proof fn lemma_to_multiset_2<T>(s1:Seq<T>, s2:Seq<T>)
//   requires
//     s1.to_multiset() =~= s2.to_multiset()
//   ensures
//     forall |v:T| s1.contains(v) <==> s2.contains(v),
//     s1.len() == s2.len(),
// {
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;
//   assert(s1.len() == s1.to_multiset().len());
//   assert(s2.len() == s2.to_multiset().len());
//   lemma_to_multiset_1(s1);
//   lemma_to_multiset_1(s2);
//}





pub fn three_sum_closest(nums_0:Vec<i32>, target: i32) -> (res:i32)
  requires
    3 <= nums_0.len() <= 500,
    forall |i:int| 0 <= i < nums_0.len() ==> -1000 <= #[trigger]nums_0@[i] <= 1000,
    -10000 <= target <= 10000,
    // assume nums is sorted
    // is_sorted(&nums),

  ensures
    forall |i:int, p:int, q:int|
      0 <= i < p < q < nums_0.len()
      ==>
      abs(nums_0@[i] + nums_0@[p]
          + nums_0@[q] - target)
      >= abs(res - target),

    exists |i:int, p:int, q:int|
      0 <= i < p < q < nums_0.len() &&
      res == nums_0@[i] + nums_0@[p] + nums_0@[q],
{
  let mut nums = nums_0;
  sort(&mut nums);
  assert(is_sorted(&nums));
  assert forall |i:int| 0 <= i < nums.len() implies -1000 <= #[trigger]nums@[i] <= 1000 by
  {
    assert(nums@.contains(nums@[i]));
  }

  let len = nums.len();
  // let mut res = 30000;
  // let mut min_dif = 1000000;

  // for simplifying the invariant in loop
  // we compute the res, min_dif once more before the loop
  let mut res = nums[0] + nums[1] + nums[len - 1 ];
  let mut min_dif = abs_i32(res - target);
  if min_dif == 0 {
    proof {lemma_to_multiset(nums@, nums_0@, 0, 1, len - 1);}
    return target;
  }

  let ghost ghost_min_dif = min_dif;
  let ghost prev_min_dif = min_dif;

  for i in 0..len - 2
    invariant
      0 <= i <= len - 2,
      len == nums.len(),
      3 <= len <= 500,
      -10000 <= target <= 10000,
      forall |i:int| 0 <= i < nums.len() ==> -1000 <= #[trigger]nums@[i] <= 1000,
      is_sorted(&nums),
      nums@.to_multiset() =~= nums_0@.to_multiset(),
      nums.len() == nums_0@.len(),


      0 < min_dif <= ghost_min_dif,
      ghost_min_dif == abs(nums[0] + nums[1] + nums[len - 1] - target),

      //I1
      forall |i0:int, p:int, q:int| 0 <= i0 < i && i0 < p < q < len
        ==>
        #[trigger] abs(nums@[i0 as int] + nums@[p]
                        + nums@[q] - target)
                    >= min_dif,

      //I2
      // i > 0 ==>
      exists |i0:int, p:int, q:int| 0 <= i0 < p < q < len &&
        nums@[i0 as int] + nums@[p] + nums@[q] == res,

      // To prove I1
      // need to show that min_dif decreases
      // is there a general way to show that a variable decreases ???
      min_dif <= prev_min_dif,

      min_dif == abs(res - target),

  {
    let mut j = i + 1;
    let mut k = len - 1;

    proof{
      prev_min_dif = min_dif;
    }

    while j < k
      invariant
        0 <= i <= len - 2,
        len == nums.len(),
        3 <= len <= 500,
        -10000 <= target <= 10000,
        forall |i:int| 0 <= i < nums.len() ==> -1000 <= #[trigger]nums@[i] <= 1000,
        is_sorted(&nums),
        nums@.to_multiset() =~= nums_0@.to_multiset(),
        nums.len() == nums_0@.len(),

        0 < min_dif <= ghost_min_dif,
        ghost_min_dif == abs(nums[0] + nums[1] + nums[len - 1] - target),

        i + 1 <= j <= k <= len - 1,

        //I1
        forall |p:int, q:int| i < p < q < len &&
          (p < j || q > k) ==>
          abs(nums@[i as int] + nums@[p]
              + nums@[q] - target)
          >= min_dif,

        //I2
        // (i > 0 || j != i + 1 || k != len - 1)
          exists |i0:int, p:int, q:int| 0 <= i0 < p < q < len &&
            nums@[i0] + nums@[p] + nums@[q] == res,

        // To prove I1
        // need to show that min_dif decreases
        // is there a general way to show that a variable decreases ???
        min_dif <= prev_min_dif,

        min_dif == abs(res - target),

      decreases k - j
    {
      let cur = nums[i] + nums[j] + nums[k];
      let cur_dif = abs_i32(cur - target);
      if cur_dif < min_dif{
        min_dif = cur_dif;
        res = cur;
      }
      // assert(min_dif <= abs(nums@[i as int] + nums@[j as int]
      //         + nums@[k as int] - target));
      if cur > target { k -= 1 }
      else if cur < target { j += 1 }
      else {
        proof {
          // assert(target == nums@[i as int] + nums@[j as int] + nums@[k as int]);
          lemma_to_multiset(nums@, nums_0@, i as int, j as int, k as int);
          assert(exists |p:int, q:int, r:int|
            0 <= p < q < r < nums_0@.len() &&
            nums_0@[p] + nums_0@[q] + nums_0@[r] == target
          );
        }
        return target
      }
    }
    assert(j == k);
    assert(forall |p:int, q:int| i < p < q < len
           ==>
          abs(nums@[i as int] + nums@[p]
              + nums@[q] - target)
          >= min_dif);
  }

  proof{
    assert forall |i:int, p:int, q:int|
      0 <= i < p < q < len
      implies
      abs(nums_0@[i] + nums_0@[p]
          + nums_0@[q] - target)
      >= min_dif
    by
    {
      lemma_to_multiset(nums_0@, nums@, i, p, q);
      // lemma_to_multiset(nums@, nums_0@);

    }
    assert(exists |i:int, p:int, q:int|
       0 <= i < p < q < nums_0@.len() &&
       res == nums_0@[i] + nums_0@[p] + nums_0@[q])
    by
    {
      let (x, y, z) = choose |x:int, y:int, z:int| 0 <= x < y < z < len &&
        nums@[x] + nums@[y] + nums@[z] == res;
      lemma_to_multiset(nums@, nums_0@, x, y, z)
    }
  }
  return res
}




// Remark
//  the sort is at start of the algorithm,
//  we can prove several post-conditions for the vector after sort
//  and port the "proof for the sorted vector" to the "proof for the original vector"
//  the port should be trivial (mathematically), but in Hoare Logic, not trivial
//  Because of this inconvenience, from this problem on,
//    for any prob/algorithm for vector that we should sort the vector at first,
//    we will just assume the vector is originally sorted


}//verus!


fn main(){}