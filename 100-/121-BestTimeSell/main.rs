use vstd::prelude::*;
use vstd::math::{min, max};

verus!{

pub fn min_i32(x:i32, y:i32) -> (res:i32)
  ensures res == min(x as int, y as int)
{
  if x < y {x} else {y}
}

pub fn max_i32(x:i32, y:i32) -> (res:i32)
  ensures res == max(x as int, y as int)
{
  if x < y {y} else {x}
}


pub fn max_profit(prices: Vec<i32>) -> (res:i32)
  requires
    1 <= prices.len() <= 100000,
    forall |i:int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10000,
  ensures
    forall |j:int, k:int| 0 <= j < k < prices.len() ==> prices[k] - prices[j] <= res,

    res > 0 ==> exists |j:int, k:int| 0 <= j < k < prices.len() && prices[k] - prices[j] == res,

{
  let mut maxPro = 0;
  let mut minPrice = i32::MAX;
  for i in 0..prices.len()
    invariant
      i == 0 ==> minPrice == i32::MAX,
      i == 0 ==> maxPro == 0,
      minPrice >= 0,
      1 <= prices.len() <= 100000,
      forall |j:int| 0 <= j < prices.len() ==> 0 <=#[trigger] prices[j] <= 10000,
      forall |j:int| 0 <= j < i ==> #[trigger] prices[j] >= minPrice,
      i > 0 ==> exists |j:int| 0 <= j < i && #[trigger] prices[j] == minPrice,

      forall |j:int, k:int| 0 <= j < k < i ==> prices[k] - prices[j] <= maxPro,

      maxPro > 0 ==> exists |j:int, k:int| 0 <= j < k < i && prices[k] - prices[j] == maxPro,
  {
      minPrice = min_i32(minPrice, prices[i]);
      maxPro = max_i32(maxPro, prices[i] - minPrice);
  }

  return maxPro;
}



}//verus!

fn main(){}