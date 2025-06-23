use vstd::prelude::*;
use vstd::math::max;


verus!{

pub fn max_i32(x:i32, y:i32) -> (res:i32)
  ensures res == max(x as int, y as int)
{
  if x < y {y} else {x}
}

pub open spec fn precondition(a:Seq<u32>) -> bool{
  &&& 1 <= a.len() <= 10000
  &&& forall |i:int| 0 <= i < a.len() ==> (a[i] == 0 || a[i] == 1)
}

pub open spec fn pow2(e: nat) -> nat
    decreases
            e,
{
  if e == 0 {1}
  else { 2 * pow2((e-1) as nat)}
}



pub open spec fn to_binary(s:Seq<u32>) -> nat
  decreases s
{
  if s.len() == 0 {0}
  else {
    (s[0] * pow2((s.len() - 1) as nat) + to_binary(s.subrange(1, s.len() as int))) as nat
  }
}






pub fn addBinary(a:Vec<u32>, b:Vec<u32>)  -> (res:Vec<u32>)
  requires
    precondition(a@),
    precondition(b@),
    a@.len() >= b@.len(), //assumption, this makes the problem easier
  ensures
    to_binary(a@) + to_binary(b@) == to_binary(res@)
{
  let mut i = (a.len() - 1) as i32;
  let mut j = (b.len() - 1) as i32;
  let mut res = Vec::<u32>::with_capacity((max_i32(i, j) + 2) as usize);
  let mut carry = 0;

  assert(to_binary(a@.subrange(i + 1, a.len() as int)) + to_binary(b@.subrange(j + 1, b.len() as int))
      == to_binary(res@) + carry * pow2(res@.len())
  );

  let ghost x = 0u32;
  let ghost y = 0u32;

  while i>=0
    invariant
      precondition(a@),
      precondition(b@),
      a@.len() >= b@.len(), //assumption

      -1 <= i <= a.len() - 1,
      -1 <= j <= b.len() - 1,
      j <= i,

      j >= 0 ==> b.len() - j == a.len() - i,

      carry == 0 || carry == 1,

      to_binary(a@.subrange(i + 1, a.len() as int)) + to_binary(b@.subrange(j + 1, b.len() as int))
      == to_binary(res@) + carry * pow2(res@.len()),

      res@.len() == a.len() - i - 1,

    decreases
      i + 1
  {
    let ghost i0 = i as int;
    let ghost j0 = j as int;
    let ghost res0 = res;
    let ghost carry0 = carry;
    let ghost x0 = x;
      // x * pow2((a.len() - i - 1) as nat) == x * pow2(res@.len()),

    let ch1 = a[i as usize];
    // let ch1 = if i < 0 {0} else {a[i as usize]};
    let ch2 = if j < 0 {0} else {b[j as usize]};
    proof{
      x = ch1;
      y = ch2;
    }

    let val = ch1 + ch2 + carry;
    res.insert(0, val%2);
    carry = val/2;
    // if i >= 0 { i -= 1;}
    i -= 1;
    if j >= 0 { j -= 1;}

    proof{
      assert(to_binary(a@.subrange(i0 + 1, a.len() as int)) + to_binary(b@.subrange(j0 + 1, b.len() as int))
        == to_binary(res0@) + carry0 * pow2(res0@.len()));

      assert(x == 0 || x == 1);
      assert(y == 0 || y == 1);
      assert(carry0 == 0 || carry0 == 1);
      assert(0 <= val <= 3);

      let a0 = a@.subrange(i0 + 1, a.len() as int);
      let a1 = a@.subrange(i + 1, a.len() as int);
      let b0 = b@.subrange(j0 + 1, b.len() as int);
      let b1 = b@.subrange(j + 1, b.len() as int);

      assert(res@[0] == val%2);
      assert(res0@ =~= res@.subrange(1, res@.len() as int));
      assert(to_binary(res@) == (val%2)*pow2(res0@.len()) + to_binary(res0@) );
      assert(x == a1[0]);
      assert(a0 =~= a1.subrange(1, a1.len() as int));
      assert(to_binary(a1) == x * pow2(a0.len()) + to_binary(a0));
      assert(to_binary(b1) == y * pow2(b0.len()) + to_binary(b0)) by {
        if j0 == -1 { assert(j == -1); assert(y == 0); assert(b0 =~= b1)}
        else {
          assert(y == b1[0]);
          assert(b0 =~= b1.subrange(1, b1.len() as int));
        }
      }

      assert(to_binary(a1) + to_binary(b1) ==
        x * pow2(a0.len()) + y * pow2(b0.len())
        + to_binary(res0@) + carry0 * pow2(res0@.len())
      );

      assert(to_binary(res@) + carry * pow2(res@.len())
        ==  (val%2)*pow2(res0@.len()) + to_binary(res0@) + (val/2) * pow2(res@.len())
      );

      assert(pow2(res@.len()) == 2 * pow2(res0@.len())) by{
        assert(res@.len() - 1 == res0@.len());
      }
      assert((val/2) * pow2(res@.len()) == (val/2) * 2 * pow2(res0@.len())) by (nonlinear_arith)
        requires pow2(res@.len()) == 2 * pow2(res0@.len());

      assert(x + y + carry0 == (val/2) * 2 + val%2);

      assert((val%2)*pow2(res0@.len()) + (val/2) * 2 * pow2(res0@.len())
        == (x + y + carry0) * pow2(res0@.len())) by(nonlinear_arith)
        requires x + y + carry0 == (val/2) * 2 + val%2;
    }//proof

  }

  assert(to_binary(a@) + to_binary(b@) == to_binary(res@) + carry * pow2(res@.len())) by
  {
    assert(a@.subrange(0, a.len() as int) =~= a@);
    assert(b@.subrange(0, b.len() as int) =~= b@);
  }

  let ghost res0 = res;
  if(carry == 1)
      {res.insert(0,1);}

  assert(to_binary(a@) + to_binary(b@) == to_binary(res@)) by
  {
    if carry == 0 {}
    else {
      assert(res0@ =~= res@.subrange(1, res@.len() as int));
      assert(to_binary(res@) == carry * pow2(res0@.len() as nat) + to_binary(res0@));
    }
  }

  return res;
}


pub fn addBinary_0(a:Vec<u32>, b:Vec<u32>)  -> (res:Vec<u32>)
  requires
    precondition(a@),
    precondition(b@),
  ensures
    to_binary(a@) + to_binary(b@) == to_binary(res@)
{
  if a.len() < b.len() { addBinary(b, a) }
  else { addBinary(a, b)}
}


}//verus!


fn main(){}