use vstd::prelude::*;



verus!{


// #[verifier::loop_isolation(false)]
pub fn search_insert(nums: Vec<i32>, target: i32) -> (res:i32)
  requires
    1 <= nums@.len() <= 10000,
    // sorted, distinct
    forall |i:int, j:int| 0 <= i < j < nums@.len() ==> nums@[i] < nums@[j],

  ensures

    target > nums@[nums@.len() - 1] ==> res == nums@.len(),

    target < nums@[0] ==> res == 0,

    nums@[0] <= target <= nums@[nums@.len() - 1] ==>
      (forall |i:int| 0 <= i < res ==> nums@[i] < target)
      &&
      (forall |i:int| res <= i < nums@.len() ==> nums@[i] >= target)
    ,

    //direct result of the previous post-condition
    (exists |i:int| 0 <= i < nums@.len() && nums@[i] == target)
      ==> nums@[res as int] == target,



{
  let mut low = 0i32;
  let mut high = nums.len() as i32 - 1;
  let mut mid = 0i32;

  while(low<=high)
    invariant
      1 <= nums@.len() <= 10000,

      low <= high + 1,

      0 <= low <= nums@.len(),
      -1 <= high <= nums@.len() - 1,

      low <= high ==> high >= 0,
      low <= high ==> low <= nums@.len() - 1,

      forall |i:int, j:int| 0 <= i < j < nums@.len() ==> nums@[i] < nums@[j],

      forall |i:int| 0 <= i < low ==> nums@[i] < target,
      forall |i:int| high < i < nums@.len() ==> nums@[i] > target,


    decreases high - low + 1
  {
    mid = ((low + high) as usize /2) as i32;

    assert(0 <= low <= mid <= high < nums@.len());

    if(nums[mid as usize]==target){
      // assert(forall |i:int| 0 <= i < mid ==> nums@[i] < target);
      return mid;
    }
    if(target<nums[mid as usize]){
      high = mid - 1;
    } else {
      low = mid + 1;
    }
  }
  // assert(low == high + 1);
  // assert(forall |i:int| 0 <= i < low ==> nums@[i] < target);
  // assert(forall |i:int| low <= i < nums@.len() ==> nums@[i] > target);
  return  low;
}

}//verus!

fn main(){}