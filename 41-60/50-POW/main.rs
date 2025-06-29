use vstd::prelude::*;
use vstd::arithmetic::power;
use power::pow;

verus!{


// in leetcode, this problem is for computing power of float
// but verus only supports integer arith, so here we just compute power of integer



// pub open spec fn fast_pow(x:nat, n:nat) -> nat
//   decreases n
// {
//   if n == 0 { 1 }
//   else if n % 2 == 0 {
//     fast_pow(x, n/2) * fast_pow(x, n/2)
//   }
//   else {
//     fast_pow(x, n/2) * fast_pow(x, n/2) * x
//   }
// }


fn myPow(x:u32, n:u32) -> (res:u32)
  requires
    x > 0,
    pow(x as int, n as nat) < u32::MAX,
  ensures
    res == pow(x as int, n as nat)
{

  let mut res = 1;
  let ghost x0 = x as int;
  let ghost n0 = n as nat;
  let mut x = x;
  let mut n = n;

  while n != 0
    invariant
      x0 > 0,
      x > 0,
      pow(x0, n0) < u32::MAX,
      res * pow(x as int, n as nat) == pow(x0, n0),
      res >= 1,
      n >= 0,
    decreases n
  {
    let ghost res_prev = res as nat;
    let ghost n_prev = n as nat;
    let ghost x_prev = x as int;

    if n % 2 == 1
    {
      //proof for no overflow
      proof{
        assert(pow(x as int, 1) == x) by { power::lemma_pow1(x as int)}
        assert(pow(x as int, n as nat) >= x) by { power::lemma_pow_increases(x as nat, 1, n as nat) }
        assert(res as nat * x < u32::MAX) by (nonlinear_arith)
          requires
            res as nat * pow(x as int, n as nat)  < u32::MAX,
            pow(x as int, n as nat) >= x;
      }
      res *= x;
      proof{
        assert(res >= 1) by (nonlinear_arith)
          requires res_prev >= 1, x >= 1, res == res_prev * x;
      }
    }

    if n > 1{ //avoid overflow
      //proof for no overflow
      proof{
        assert(pow(x as int, n as nat) < u32::MAX) by (nonlinear_arith)
          requires res_prev * pow(x as int, n as nat) < u32::MAX, res_prev >=1;
        assert(n >= 2);
        assert(pow(x as int, 2) < u32::MAX) by {
          power::lemma_pow_increases(x as nat, 2, n as nat)
        }
        assert(x * x < u32::MAX) by {
          power::lemma_square_is_pow2(x as int)
        }
      }
      x *= x;
      assert(x > 0) by (nonlinear_arith) requires x_prev > 0, x == x_prev * x_prev;
    }

    n /= 2;

    proof{
      assert(res_prev * pow(x_prev, n_prev) == pow(x0, n0));
      if n_prev == 1 {
        assert(x_prev == x);
        assert(res == res_prev * x_prev);
        assert(res >= 1) by (nonlinear_arith)
          requires res_prev >= 1, x_prev >= 1, res == res_prev * x_prev;
      }
      else {
        assert(x == x_prev * x_prev);
        assert(n == n_prev / 2);
        assert(pow(x as int, n as nat) == pow(x_prev * x_prev, n as nat));
        assert(pow(x_prev * x_prev, n as nat) == pow(x_prev, n as nat) * pow(x_prev, n as nat)) by{
          broadcast use power::lemma_pow_distributes;
        }
        assert(pow(x_prev, n as nat) * pow(x_prev, n as nat) == pow(x_prev, (n + n) as nat)) by {
          broadcast use power::lemma_pow_adds;
        }
        assert(pow(x as int, n as nat) == pow(x_prev, n as nat + n as nat));
        if n_prev % 2 == 0 {
          assert(n_prev == n * 2);
          assert(pow(x_prev, n_prev) == pow(x as int, n as nat));
          assert(res * pow(x as int, n as nat) == pow(x0, n0));
        }
        else {
          assert(n_prev == n * 2 + 1);
          assert(res * pow(x as int, n as nat) == res_prev * (x_prev * pow(x_prev, (n_prev - 1) as nat)))
            by (nonlinear_arith)
            requires
              res == res_prev * x_prev,
              pow(x as int, n as nat) == pow(x_prev, (n_prev - 1) as nat),
              pow(x_prev, n_prev) == x_prev * pow(x_prev, (n_prev - 1) as nat)
          ;
          assert(res * pow(x as int, n as nat) == pow(x0, n0));
        }
      }
    }
  }//end of loop

  assert(res * pow(x as int, 0) == pow(x0, n0));
  assert(res == pow(x0, n0)) by {power::lemma_pow0(x as int)};


  return res;

}





}//verus!


fn main(){}