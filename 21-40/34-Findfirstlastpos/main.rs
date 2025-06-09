use vstd::prelude::*;

verus!{


pub open spec fn requirement(nums: &Vec<i32>, target: i32) -> bool{
  &&& 0 <= nums.len() <= 100000
  &&& forall |i:int| 0 <= i < nums.len() ==> -1000_000_000 <= #[trigger]nums@[i] <=  1000_000_000
  &&& -1000_000_000 <= target <= 1000_000_000
  &&& forall |i:int, j:int| 0 <= i <= j < nums.len() ==> nums@[i] <= nums@[j]
}


fn lower_bound(nums: &Vec<i32>, target: i32) -> (res:i32)
  requires
    requirement(nums, target),
  ensures
    forall |j:int| 0 <= j < res ==> nums@[j] < target,
    forall |j:int| res <= j < nums@.len() ==> nums@[j] >= target,
    0 <= res <= nums.len(),
{
  let len: usize = nums.len();
  let mut lo: usize = 0;
  let mut hi: usize = len;
  while lo < hi
    invariant
      requirement(nums, target),
      len == nums.len(),
      0 <= lo <= hi <= len,
      forall |j:int| 0 <= j < lo ==> nums@[j] < target,
      forall |j:int| hi <= j < len ==> nums@[j] >= target,
    decreases hi - lo,
  {
    let mid: usize = lo + (hi - lo) / 2;
    if target > nums[mid] {
      lo = 1 + mid;
    } else {
      hi = mid;
    }
  }
  lo as i32
}



fn upper_bound(nums: &Vec<i32>, target: i32) -> (res:i32)
  requires
    requirement(nums, target),
  ensures
    forall |j:int| res + 1 <= j < nums.len() ==> nums@[j] > target,
    forall |j:int| 0 <= j < res + 1 ==> nums@[j] <= target,
    -1 <= res <= nums.len() - 1,
{
  let len: usize = nums.len();
  let mut lo: usize = 0;
  let mut hi: usize = len;
  while lo < hi
    invariant
      requirement(nums, target),
      len == nums.len(),
      0 <= lo <= hi <= len,
      forall |j:int| hi <= j < len ==> nums@[j] > target,
      forall |j:int| 0 <= j < lo ==> nums@[j] <= target,
    decreases hi - lo,
  {
    let mid: usize = lo + (hi - lo) / 2;
    if target < nums[mid] {
      hi = mid;
    } else {
      lo = 1 + mid;
    }
  }
  hi as i32 - 1
}


pub fn search_range(nums: Vec<i32>, target: i32) -> (res:Vec<i32>)
  requires requirement(&nums, target),
  ensures
    (!nums@.contains(target)) <==> res@ =~= seq![-1i32, -1i32],

    nums@.contains(target) ==>
      (forall |i:int| 0 <= i < res@[0] ==> nums@[i] < target)
      && (forall |i:int| res@[0] <= i <= res@[1] ==> nums@[i] == target)
      && (forall |i:int| res@[1] < i < nums.len() ==> nums@[i] > target)

{
  let first_pos = lower_bound(&nums, target);
  let last_pos = upper_bound(&nums, target);

  assert(forall |j:int| last_pos + 1 <= j < nums.len() ==> nums@[j] > target);
  assert(forall |j:int| 0 <= j < last_pos + 1 ==> nums@[j] <= target);
  assert(forall |j:int| 0 <= j < first_pos ==> nums@[j] < target);
  assert(forall |j:int| first_pos <= j < nums.len() ==> nums@[j] >= target);

  assert(forall |j:int| first_pos <= j < last_pos + 1 ==> nums@[j] == target);

  proof{
    assert(
      (!nums@.contains(target))
      <==> first_pos > last_pos
    ) by
    {
      if first_pos <= last_pos{
        assert(nums@[first_pos as int] == target);
      }
    }
  }


  if first_pos > last_pos {
    return vec![-1, -1];
  }

  // assert(first_pos <= last_pos);
  // assert(nums@.contains(target));
  // assert(nums@[first_pos as int] == target);


  vec![first_pos, last_pos]
}



}//verus!

fn main(){}