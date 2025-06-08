use vstd::prelude::*;

use vstd::math::{max, min};

verus!{

pub fn max_usize(x:usize, y:usize) -> (res:usize)
  ensures
    res == max(x as int, y as int),
{
  if x > y {x} else {y}
}

pub fn min_usize(x:usize, y:usize) -> (res:usize)
  ensures
    res == min(x as int, y as int),
    res <= x || res <= y,
{
  if x > y {y} else {x}
}


pub open spec fn area_spec(s:Seq<usize>, left:int, right:int) -> int{
  min(s[left] as int, s[right] as int) * (right - left)
}

pub proof fn area_lemma(s:Seq<usize>, left:int, right:int)
  requires
    2 <= s.len() <= 100000,
    forall |i:int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] <= 10000,
    0 <= left <= right < s.len(),
  ensures
    area_spec(s, left, right) <= s[left] * (right - left),
    area_spec(s, left, right) <= s[right] * (right - left),
    s[left] * (right - left) <= 10000_00000,
    s[right] * (right - left) <= 10000_00000,
{
  let m = min(s[left] as int, s[right] as int);
  assert(m <= s[left]);
  assert(m <= s[right]);
  let cur_len = right - left;
  assert(m * cur_len <= s[left] * cur_len) by (nonlinear_arith)
    requires 0 <= m <= s[left], 0 <= cur_len;
  assert(m * cur_len <= s[right] * cur_len) by (nonlinear_arith)
    requires 0 <= m <= s[right], 0 <= cur_len;
  assert(s[left] * cur_len <= 10000_00000) by (nonlinear_arith)
    requires 0 <= s[left] <= 10000, 0 <= cur_len <= 100000;
  assert(s[right] * cur_len <= 10000_00000) by (nonlinear_arith)
    requires 0 <= s[right] <= 10000, 0 <= cur_len <= 100000;
}

#[inline]
pub fn area(v:&Vec<usize>, left:usize, right:usize) -> (res:usize)
  requires
    2 <= v.len() <= 100000,
    forall |i:int| 0 <= i < v.len() ==> 0 <= #[trigger] v@[i] <= 10000,
    0 <= left <= right < v.len(),
  ensures
    res == area_spec(v@, left as int, right as int),
{
  proof { area_lemma(v@, left as int, right as int); }
  min_usize(v[left], v[right]) * (right - left)
}


pub fn max_area(height: Vec<usize>) -> (res:usize)
  requires
    2 <= height.len() <= 100000,
    forall |i:int| 0 <= i < height.len() ==> 0 <= #[trigger] height@[i] <= 10000,
  ensures
    forall |i:int, j:int| 0 <= i < j < height.len()
      ==> area_spec(height@, i, j) <= res,
    exists |i:int, j:int| 0 <= i < j < height.len() &&
      res == area_spec(height@, i, j),
{
  let mut left = 0;
  let mut right = height.len() - 1;
  let mut val = area(&height, left, right);

  while left < right
    invariant
      2 <= height.len() <= 100000,
      forall |i:int| 0 <= i < height.len() ==> 0 <= #[trigger] height@[i] <= 10000,
      0 <= left <= right <= height.len() - 1,

      forall |i:int, j:int| 0 <= i < j < height.len() &&
        (i < left || j > right) ==>
        area_spec(height@, i, j) <= val,

      exists |i:int, j:int| 0 <= i < j < height.len() &&
        val == area_spec(height@, i, j),

    decreases
      right - left
  {

    let new_val = area(&height, left, right);
    val = max_usize(val, new_val);
    if height[left] > height[right]{
      proof{
        assert forall |i:int, j:int| 0 <= i < j < height.len() &&
          (i < left || j > right - 1) implies
          area_spec(height@, i, j) <= val by
        {
          if j > right {}
          else {
            if i < left {}
            else {
              assert(i >= left);
              assert(j == right);
              assert(
                   area_spec(height@, i, right as int)
                <= height@[right as int] * (right - i)
              ) by {
                area_lemma(height@, i, right as int)
              }
              assert(
                   height@[right as int] * (right - i)
                <= height@[right as int] * (right - left)
              ) by (nonlinear_arith)
              requires
                0 <= height@[right as int] <= 10000,
                0 <= left <= i <= right <= 100000;
              assert(area_spec(height@, i, right as int) <= new_val);
            }
          }
        }
      }

      right -= 1;
    }
    else {
      proof{
        assert forall |i:int, j:int| 0 <= i < j < height.len() &&
          (i < left + 1 || j > right) implies
          area_spec(height@, i, j) <= val by
        {
          if i < left {}
          else {
            if j > right {}
            else {
              assert(j <= right);
              assert(i == left);
              assert(
                   area_spec(height@, left as int, j)
                <= height@[left as int] * (j - left)
              ) by {
                area_lemma(height@, left as int, j)
              }
              assert(
                   height@[left as int] * (j - left)
                <= height@[left as int] * (right - left)
              ) by (nonlinear_arith)
              requires
                0 <= height@[left as int] <= 10000,
                0 <= left <= j <= right <= 100000;
              assert(area_spec(height@, left as int, j) <= new_val);
            }
          }
        }
      }

      left += 1;
    }
  }

  // assert(
  //   forall |i:int, j:int| 0 <= i < j < height.len()
  //     ==> area_spec(height@, i, j) <= val
  // );


  return val
}




}//verus!


fn main(){}