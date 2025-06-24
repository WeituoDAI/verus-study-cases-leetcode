use vstd::prelude::*;

verus!{




pub fn my_sqrt(x: u32) -> (res:u32)
  ensures
    res * res <= x < (res + 1) * (res + 1)
{
  if x == 0 {return 0}
  if (x == 1 || x == 2 ) {return 1}
  let mut bg = 1;
  let mut ed = x -1;
  let mut mid;

  assert(ed * ed > x) by {
    assert((x-1) * (x-1) > x) by (nonlinear_arith)
      requires x >= 3;
  }

  while ed > bg + 1
    invariant
      1 <= bg < ed,
      bg * bg <= x,
      ed * ed > x,
      x >= 3,

    decreases ed - bg
  {
    mid = bg + (ed - bg)/2;
    let tmp = x/mid;
    if tmp == mid {
      proof{
        assert(mid * mid <= x) by (nonlinear_arith)
          requires x/mid == mid, mid > 0;
        assert(x <= mid * (mid + 1)) by (nonlinear_arith)
          requires x/mid == mid, mid > 0;
        assert(x < (mid + 1) * (mid + 1)) by (nonlinear_arith)
          requires x <= mid * (mid + 1), mid > 0;
      }
      return mid;
    }
    if tmp > mid {
      bg = mid;
      proof{
        assert(mid * mid < x) by (nonlinear_arith)
          requires tmp == x/mid, tmp > mid, mid > 0;
      }
    }
    else {
      ed = mid;
      proof{
        assert(mid * mid > x) by (nonlinear_arith)
          requires tmp == x/mid, tmp < mid, mid > 0;
      }
    }
  }

  assert(bg * bg <= x < ed * ed);
  assert(ed == bg + 1);

  return bg;
}



}//verus!

fn main(){}