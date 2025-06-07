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
{
  unimplemented!()
}



pub fn three_sum_closest(nums:Vec<i32>, target: i32) -> (res:i32)
  requires
    3 <= nums.len() <= 500,
    forall |i:int| 0 <= i < nums.len() ==> -1000 <= #[trigger]nums@[i] <= 1000,
    -10000 <= target <= 10000,
    // assume nums is sorted
    is_sorted(&nums),

  ensures
    forall |i:int, p:int, q:int|
      0 <= i < p < q < nums.len()
      ==>
      abs(nums@[i] + nums@[p]
          + nums@[q] - target)
      >= abs(res - target),

    exists |i:int, p:int, q:int|
      0 <= i < p < q < nums.len() &&
      res == nums@[i] + nums@[p] + nums@[q],
{
  let len = nums.len();
  // let mut res = 30000;
  // let mut min_dif = 1000000;

  // for simplifying the invariant in loop
  // we compute the res, min_dif once more before the loop
  let mut res = nums[0] + nums[1] + nums[len - 1 ];
  let mut min_dif = abs_i32(res - target);
  if min_dif == 0 { return target }


  let ghost ghost_min_dif = min_dif;
  let ghost prev_min_dif = min_dif;
  // let ghost min_dif_seq = seq![min_dif;(len - 2) as nat];

  for i in 0..len - 2
    invariant
      0 <= i <= len - 2,
      len == nums.len(),
      3 <= len <= 500,
      -10000 <= target <= 10000,
      forall |i:int| 0 <= i < nums.len() ==> -1000 <= #[trigger]nums@[i] <= 1000,
      is_sorted(&nums),

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
      else { return target }
    }
    assert(j == k);
    assert(forall |p:int, q:int| i < p < q < len
           ==>
          abs(nums@[i as int] + nums@[p]
              + nums@[q] - target)
          >= min_dif);
  }

  proof{
    assert(forall |i:int, p:int, q:int|
      0 <= i < p < q < len
      ==>
      #[trigger] abs(nums@[i] + nums@[p]
          + nums@[q] - target)
      >= min_dif
    );
  }
  return res
}





}//verus!


fn main(){}