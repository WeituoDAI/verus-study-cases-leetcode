use vstd::prelude::*;
// use vstd::math::abs;

//todo

verus!{


pub open spec fn to_seq(i:nat) -> Seq<nat>
  decreases i
{
  if 0 <= i < 10 { seq![i] }
  else {
    to_seq(i/10).push(i%10)
  }
}

pub open spec fn to_nat_2(s:Seq<nat>) -> nat
  recommends forall |i:int| 0 <= i < s.len() ==> s[i] < 10,
  decreases s
{
  if s.len() == 0 {0}
  else {
    to_nat_2(s.drop_last()) * 10 + s.last()
  }
}


pub open spec fn to_nat(s:Seq<nat>) -> nat
  decreases s
{
  if s.len() == 0 {0}
  else {
    s[0] * pow10((s.len() - 1) as nat) + to_nat(s.subrange(1, s.len() as int))
  }
}


#[verifier::spinoff_prover]
pub proof fn to_nat_eq(s:Seq<nat>)
  requires
    forall |i:int| 0 <= i < s.len() ==> s[i] < 10,
  ensures
    to_nat(s) == to_nat_2(s)
  decreases
    s,
{
    if s.len() == 0 {}
    else if s.len() == 1{
        assert(to_nat(s) == s[0] * pow10(0) + to_nat(s.subrange(1, 1)));
        assert(to_nat_2(s) == to_nat_2(s.drop_last()) * 10 + s.last());
        assert(to_nat_2(s) == to_nat_2(seq![]) * 10 + s[0]);
        assert(to_nat(s) == s[0] * 1 + to_nat(seq![]));
    }
    else {
        assert(to_nat(s) == s[0] * pow10((s.len() - 1) as nat) 
            + to_nat(s.subrange(1, s.len() as int))
        );

        assert(to_nat(s) == s[0] * pow10((s.len() - 1) as nat) 
            + to_nat_2(s.subrange(1, s.len() as int).drop_last()) * 10 +
                 s.subrange(1, s.len() as int).last()
        ) by  {to_nat_eq(s.subrange(1, s.len() as int))}

        assert(to_nat(s) == 
            s[0] * pow10((s.len() - 1) as nat) 
            + to_nat_2(s.subrange(1, s.len() - 1)) * 10
            + s.last()) 
        by {
            assert(s.subrange(1, s.len() as int).last() == s.last());
            assert(s.subrange(1, s.len() as int).drop_last() =~= s.subrange(1, s.len() - 1));
        }



        assert(to_nat_2(s) == to_nat_2(s.drop_last()) * 10 + s.last());

        // assert(to_nat_2(s.drop_last()) == )
        assert(s.drop_last().len() >= 1);
        assert(to_nat(s.drop_last()) == s.drop_last()[0] * pow10((s.drop_last().len() - 1) as nat) 
            + to_nat(s.drop_last().subrange(1, s.drop_last().len() as int))
        );

        assert(to_nat_2(s.drop_last()) == to_nat(s.drop_last())) by {to_nat_eq(s.drop_last())}

        assert(to_nat_2(s) == 
            (s.drop_last()[0] * pow10((s.drop_last().len() - 1) as nat) 
            + to_nat(s.drop_last().subrange(1, s.drop_last().len() as int))) * 10 + s.last()
        );

        assert(
            (s.drop_last()[0] * pow10((s.drop_last().len() - 1) as nat) 
            + to_nat(s.drop_last().subrange(1, s.drop_last().len() as int))) * 10
            == 
            s.drop_last()[0] * pow10((s.drop_last().len() - 1) as nat) * 10
            + to_nat(s.drop_last().subrange(1, s.drop_last().len() as int)) * 10
        ) by (nonlinear_arith);


        assert(
          to_nat_2(s) ==  

          s[0] * pow10((s.len() - 2) as nat) * 10
            + to_nat(s.drop_last().subrange(1, s.drop_last().len() as int)) * 10 + s.last()
        );

        assert(s.drop_last().subrange(1, s.drop_last().len() as int) =~= s.subrange(1, s.len() - 1));

        assert(
          to_nat_2(s) ==  

          s[0] * pow10((s.len() - 2) as nat) * 10
            + to_nat(s.subrange(1, s.len() - 1)) * 10 + s.last()
        );
        assert(to_nat(s) == 
            s[0] * pow10((s.len() - 1) as nat) 
            + to_nat_2(s.subrange(1, s.len() - 1)) * 10
            + s.last()
        ) ;

        assert(s[0] * pow10((s.len() - 2) as nat) * 10 == s[0]*pow10((s.len() - 1) as nat)) by(nonlinear_arith)
            requires s.len() >= 2;
        to_nat_eq(s.subrange(1, s.len() - 1));

        assert(to_nat(s) == to_nat_2(s));
    }
}


proof fn lemma_to_seq_eq_count_digits(x:nat)
    requires x > 0
    ensures to_seq(x).len() == count_digits(x)
    decreases x
{
    if x < 10 {
        assert(count_digits(x) == 1) by {reveal_with_fuel(count_digits, 2)}
    }
    else {
        lemma_to_seq_eq_count_digits(x/10);
    }
}


pub open spec fn reverse_nat(n:nat) -> nat{
  to_nat(to_seq(n).reverse())
}

pub open spec fn reverse_int(i:int) -> int
{
  if i >= 0 {
    reverse_nat(i as nat) as int
  }
  else{
    - (reverse_nat((-i) as nat) as int)
  }
}

pub open spec fn reverse_truncate(i:i32) -> i32{
  let x = reverse_int(i as int);
  if x > i32::MAX || x < i32::MIN { 0 }
  else { x as i32 }
}




pub proof fn reverse_eq(x:nat)
  ensures
    reverse_spec(x) == reverse_nat(x)
  decreases
    x
{
  if x < 10 {
    assert(reverse_spec(x) == x);
    assert(to_seq(x).reverse() == seq![x]);
    assert(to_nat(seq![x]) == x) by{
      assert(seq![x].subrange(1, 1).len() == 0);
      assert(pow10(0) == 1);
      assert(x * 1 == x);
      reveal_with_fuel(to_nat, 2);
    }
  }
  else {
    assert(
      reverse_spec(x) == (x % 10) * pow10(count_digits(x/10))
        + reverse_spec(x/10)
    );

    assert(
      reverse_nat(x) ==
        to_nat(to_seq(x).reverse())
    );

    assert(to_seq(x) =~= to_seq(x/10).push(x%10));
    assert(to_seq(x) =~= to_seq(x/10) + seq![x%10]);
    assert(to_seq(x).reverse() =~= seq![x%10] + to_seq(x/10).reverse());
    assert(to_seq(x).reverse()[0] == x%10);
    assert(to_seq(x).reverse().len() == 1 + to_seq(x/10).reverse().len());
    assert(to_seq(x).reverse().subrange(1, to_seq(x).reverse().len() as int) =~= to_seq(x/10).reverse());
    assert(to_nat(to_seq(x).reverse()) =~=
      x%10 * pow10(to_seq(x/10).len()) + to_nat(to_seq(x).reverse().subrange(1, to_seq(x).reverse().len() as int))
    );
    assert(to_nat(to_seq(x).reverse())
      == x%10 * pow10(to_seq(x/10).len()) + to_nat(to_seq(x/10).reverse())
    );

    assert(reverse_nat(x) == x%10 * pow10(to_seq(x/10).len()) + reverse_nat(x/10));

    assert(to_seq(x/10).len() == count_digits(x/10)) by {
      lemma_to_seq_eq_count_digits(x/10)
    }
    reverse_eq(x/10);

  }
}




pub open spec fn reverse_spec (x: nat) -> nat
  decreases x
{
  if x < 10 {x}
  else {
    (x % 10) * pow10(count_digits(x/10))
        + reverse_spec(x/10)
  }
}


pub open spec fn no_overflow(x:nat) -> bool{
  reverse_spec(x) <= i32::MAX
}


pub open spec fn count_digits(x:nat) -> nat
  decreases x
{
  if x == 0 {0}
  else { 1 + count_digits(x/10)}
}

pub open spec fn pow10(n:nat) -> nat
  decreases n
{
  if n == 0 {1}
  else {10 * pow10((n - 1) as nat)}
}

pub proof fn lemma_pow10_0(n:nat)
  ensures pow10(n) >= 1
  decreases n
{
  if n == 0{}
  else {lemma_pow10_0((n-1) as nat)}
}


pub proof fn lemma_pow10(n:nat)
  requires n >= 1
  ensures pow10(n) >= 10
{
  assert(pow10(n) == 10 * pow10((n-1) as nat));
  lemma_pow10_0((n-1) as nat)
}

pub proof fn lemma_pow10_mono(n:nat, m:nat)
  requires n >= m
  ensures pow10(n) >= pow10(m)
  decreases n
{
  if n == m {}
  else {
    assert(pow10(n) == 10 * pow10((n-1) as nat));
    lemma_pow10_mono((n-1) as nat, m)
  }
}







#[verifier::spinoff_prover]
pub fn reverse (x: u32) -> (res:u32)
  requires x >= 0

  ensures
    no_overflow(x as nat) ==>
      res == reverse_spec(x as nat),

    !no_overflow(x as nat) ==> res == 0,
{
  let mut num = x;
  let mut reversed = 0;

  assert(reversed as nat * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
        == reverse_spec(x as nat)) by
  {
    assert(reverse_spec(reversed as nat) == 0);
  }

  while num != 0
    invariant

      reversed >= 0,

      0 <= num <= x,

      //I1
      reversed as nat * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
        == reverse_spec(x as nat),

      //I2
      no_overflow(x as nat) && num != 0 ==>
        !(reversed > i32::MAX as u32 / 10 ||
       (reversed == i32::MAX as u32/10 && num%10 > 7)),

      no_overflow(x as nat) && num == 0 ==>
        reversed <= i32::MAX,

      //I4
      !no_overflow(x as nat) && 0 < num < 10 ==>
        (reversed > i32::MAX/10 || (reversed == i32::MAX/10 && num > 7)),

      //I5
      !no_overflow(x as nat) ==> num > 0,

    decreases num
  {
    let ghost num_old = num as nat;
    let ghost reversed_old = reversed as nat;

    let digit = num % 10;
    num = num /10;

    if reversed > i32::MAX as u32 / 10 ||
       (reversed == i32::MAX as u32/10 && digit > 7)
    {
      return 0;
    }
    assert(!(reversed_old > i32::MAX as u32 / 10 ||
       (reversed_old == i32::MAX as u32/10 && digit > 7)));

    reversed = reversed * 10 + digit;
    let ghost num_val = num;

    //I1
    proof{
      assert(reversed as nat * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
        == reverse_spec(x as nat)) by
      {
        assert(reversed == reversed_old * 10 + digit);
        assert(num_old == num * 10 + digit);

        assert(reversed_old * pow10(count_digits(num_old)) + reverse_spec(num_old)
          == reverse_spec(x as nat)
        );

        assert(count_digits(num_old) == count_digits(10 * num as nat + digit as nat));

        assert(
          (reversed_old * 10 + digit as nat) * pow10(count_digits(num as nat))
          + reverse_spec(num as nat)

          ==

          reversed_old * pow10(count_digits(10 * num as nat + digit as nat))
          + reverse_spec(num as nat * 10 +  digit as nat)

        ) by {

          assert(reverse_spec(num as nat * 10 + digit as nat)
            == digit * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
          ) by{
            if num == 0 {
              assert(pow10(count_digits(num as nat)) == 1);
              assert(digit * pow10(count_digits(num as nat)) == digit * 1);
            }
            else {
              assert(num_old/10 == num);
              assert(num_old%10 == digit);
            }
          }

          assert(count_digits(10 * num as nat + digit as nat) == 1 + count_digits(num as nat));

          assert((reversed_old * 10 + digit as nat) * pow10(count_digits(num as nat))
            == reversed_old * 10 * pow10(count_digits(num as nat)) + digit as nat * pow10(count_digits(num as nat))
          ) by (nonlinear_arith);

          assert(
            reversed_old * pow10(count_digits(10 * num as nat + digit as nat))
            == reversed_old * pow10(1 + count_digits(num as nat))
          );

          assert(
            reversed_old * pow10(count_digits(10 * num as nat + digit as nat))
            == reversed_old * (10 * pow10(count_digits(num as nat)))
          ) by{
            reveal_with_fuel(pow10, 2)
          }

          assert(reversed_old * (10 * pow10(count_digits(num as nat)))
            == reversed_old * 10 * pow10(count_digits(num as nat))
          ) by (nonlinear_arith);
        }
      }
    }

    //I2
    proof{
      if no_overflow(x as nat) && num!=0 {
        assert(reversed as nat * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
          <= i32::MAX);

        assert(pow10(count_digits(num as nat)) >= 10) by{
          assert(count_digits(num as nat) >= 1);
          lemma_pow10(count_digits(num as nat));
        }
        assert(reversed as nat * 10 <= i32::MAX as nat) by (nonlinear_arith)
          requires
            reversed as nat * pow10(count_digits(num as nat)) <= i32::MAX as nat,
            pow10(count_digits(num as nat)) >= 10
        ;

        assert(!(reversed > i32::MAX as u32 / 10 ||
                (reversed == i32::MAX as u32/10 && num%10 > 7))) by{
          assert(reversed <= i32::MAX/10);
          assert(reversed != i32::MAX/10 || num%10 <= 7 ) by{
            if reversed == i32::MAX/10 {
              assert(reversed * pow10(count_digits(num as nat)) + reverse_spec(num as nat) <= i32::MAX);
              assert(count_digits(num as nat) <= 1) by{
                if count_digits(num as nat) >= 2 {
                  assert(pow10(count_digits(num as nat)) >= 100) by {
                    lemma_pow10_mono(count_digits(num as nat), 2);
                    assert(pow10(2) == 100) by {reveal_with_fuel(pow10, 3)}
                  }
                  assert(reversed as nat* 100 <= i32::MAX) by (nonlinear_arith)
                    requires
                      pow10(count_digits(num as nat)) >= 100,
                      reversed * pow10(count_digits(num as nat)) <= i32::MAX;
                }
              }
            }
          }
        }
      }
    }

    //I4
    proof{
      if !no_overflow(x as nat) && 0 < num < 10 {
        assert(reversed as nat * pow10(count_digits(num as nat)) + reverse_spec(num as nat)
            > i32::MAX);
        assert(count_digits(num as nat) == 1) by {reveal_with_fuel(count_digits, 2)}
        assert(pow10(count_digits(num as nat)) == 10) by {reveal_with_fuel(pow10, 2)}
        assert(reversed as nat * 10 + num as nat  > i32::MAX);

        assert(reversed > i32::MAX/10 || (reversed == i32::MAX/10 && num > 7));
      }
    }

    //I5
    proof{
      if !no_overflow(x as nat) && num == 0 {
        assert(0 < num_old < 10);
        assert(reversed_old > i32::MAX/10 || (reversed_old == i32::MAX/10 && num_old > 7));
        assert(!(reversed_old > i32::MAX / 10 ||(reversed_old == i32::MAX/10 && num_old > 7)));
        assert(false);
      }
    }
  }

  assert(no_overflow(x as nat));
  assert(reversed == reverse_spec(x as nat)) by{
    assert(pow10(count_digits(0)) == 1);
  }

  reversed
}









}//verus!


fn main(){}