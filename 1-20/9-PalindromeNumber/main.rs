use vstd::prelude::*;


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

proof fn to_seq_no_empty(i:nat)
  ensures to_seq(i).len() > 0,
  decreases i
{
  if 0 <= i < 10 {}
  else {
    to_seq_no_empty(i/10)
  }
}


proof fn to_seq_eq(a:nat, b:nat)
  requires to_seq(a) =~= to_seq(b)
  ensures a == b
  decreases a,
{
  if 0<= a < 10{
    if 0 <= b < 10{
      assert(to_seq(b)[0] == b);
      assert(to_seq(a)[0] == a);
    }
    else {
      assert(to_seq(b) =~= to_seq(b/10).push(b%10));
      assert(to_seq(b/10).len() > 0) by {to_seq_no_empty(b/10)}
      // assert(to_seq(a) =~= to_seq(b/10).push(b%10));
    }
  }
  else{
    if 0 <= b < 10 { to_seq_eq(b, a)}
    else {
      assert(to_seq(a) =~= to_seq(a/10).push(a%10));
      assert(to_seq(b) =~= to_seq(b/10).push(b%10));

      assert(to_seq(a/10) =~= to_seq(a).drop_last());
      assert(to_seq(b/10) =~= to_seq(b).drop_last());
      assert(a%10 == to_seq(a).last());
      assert(b%10 == to_seq(b).last());
      assert(a/10 == b/10) by {to_seq_eq(a/10, b/10)}
    }
  }
}

proof fn to_seq_not_0(a:nat)
  requires a > 0,
  ensures to_seq(a)[0] != 0
  decreases a,
{
  if 0 <= a <  10 {}
  else {
    assert(to_seq(a) =~= to_seq(a/10).push(a%10));
    assert(to_seq(a)[0] =~= to_seq(a/10)[0]);
    to_seq_not_0(a/10);
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

pub open spec fn count_digits(x:nat) -> nat
  decreases x
{
  if x == 0 {0}
  else { 1 + count_digits(x/10)}
}

pub proof fn count_digits_mono(x:nat, y:nat)
	requires x >= y
	ensures count_digits(x) >= count_digits(y)
	decreases x
{
	if x == y {}
	else{
		count_digits_mono(x/10, y/10);
	}
}

proof fn lemma_u32MAX()
  ensures pow10(count_digits(u32::MAX as nat)) < u32::MAX * 10
{
  reveal_with_fuel(count_digits, 11);
  reveal_with_fuel(pow10, 11);
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
  requires n  >= m,
  ensures pow10(n) >= pow10(m)
  decreases n
{
  if n == m {}
  else {
    assert(pow10(n) == 10 * pow10((n-1) as nat));
    lemma_pow10_mono((n-1) as nat, m)
  }
}


pub proof fn lemma_reverse_spec(n:nat)
	ensures reverse_spec(n) <= pow10(count_digits(n))
  decreases n,
{
  if n == 0 {}
  else if n < 10 {
    assert(count_digits(n) == 1) by {reveal_with_fuel(count_digits, 2)}
    assert(pow10(1) == 10) by {reveal_with_fuel(pow10, 2)}
  }
  else {
    assert(
      reverse_spec(n) ==
        (n % 10) * pow10(count_digits(n/10))
        + reverse_spec(n/10)
    );

    assert(count_digits(n) == 1 + count_digits(n/10));
    assert(pow10(count_digits(n)) == pow10(1 + count_digits(n/10)));
    assert(pow10(count_digits(n)) == 10 * pow10(count_digits(n/10)));

    assert(reverse_spec(n/10) <= pow10(count_digits(n/10))) by {lemma_reverse_spec(n/10)}

    assert((n%10) * pow10(count_digits(n/10)) + reverse_spec(n/10)
          <= (n%10) * pow10(count_digits(n/10)) + pow10(count_digits(n/10))
    );

    assert((n%10) * pow10(count_digits(n/10)) + pow10(count_digits(n/10)) <= 10 * pow10(count_digits(n/10)))
      by(nonlinear_arith);
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




#[verifier::spinoff_prover]
pub fn isPalindrome(mut x: u32) -> (res:bool)

  ensures
    to_seq(x as nat).reverse() =~= to_seq(x as nat) <==> res,

    // res == true ==> to_seq(x as nat).reverse() =~= to_seq(x as nat),

{

	let ghost x_old = x as nat;


	if (x % 10 == 0 && x != 0) {
    proof{
      assert(! (to_seq(x as nat).reverse() =~= to_seq(x as nat))) by{
        if 0 <= x < 10 {}
        else {
          assert(to_seq(x as nat) =~= to_seq(x as nat/10).push(x as nat%10));
          assert(to_seq(x as nat).reverse()[0] == 0);
          assert(to_seq(x as nat)[0] != 0) by {to_seq_not_0(x as nat)}
        }
      }
    }
    return false;
  }
	if x == 0 {return true}

	assert(x > 0 && x%10 != 0);

	let mut rev = 0;


	let digit = x % 10;
	rev = rev * 10 + digit;
	x = x/10;


	assert(rev * pow10(count_digits(x as nat)) + reverse_spec(x as nat)
        == reverse_spec(x_old)) by
  {
    if x_old < 10 {
      assert(x == 0);
      assert(count_digits(0) == 0);
      assert(pow10(0) == 1);
      assert(reverse_spec(0) == 0);
      assert(reverse_spec(x as nat) == 0);
      assert(reverse_spec(x_old) == x_old);
      assert(rev == x_old);
      assert(pow10(count_digits(x as nat)) == 1);
      assert(rev * 1 + 0 == x_old);
    }
    else {
      assert(x_old >= 10);
      assert(x_old%10 == rev);
      assert(x_old/10 == x);
      assert(reverse_spec(x_old) ==
            (x_old % 10) * pow10(count_digits(x_old/10))
          + reverse_spec(x_old/10)
      );
      assert(reverse_spec(x_old) == rev *pow10(count_digits(x_old/10)) + reverse_spec(x_old/10));
      assert(reverse_spec(x_old) == rev *pow10(count_digits(x as nat)) + reverse_spec(x as nat));
    }
  }


	assert(x > rev ==> count_digits(x as nat) >= count_digits(rev as nat)) by{
		if x > rev
			{count_digits_mono(x as nat, rev as nat) }
	}


	while x > rev
		invariant
			0 < rev,

			0 <= x,

			x > rev ==> count_digits(x as nat) >= count_digits(rev as nat),
			x <= rev ==> count_digits(x as nat) >= count_digits(rev as nat) - 2,

			x_old <= u32::MAX,

			rev * pow10(count_digits(x as nat)) + reverse_spec(x as nat)
        == reverse_spec(x_old),

      x>0 ==> to_seq(x as nat) + to_seq(rev as nat).reverse() =~= to_seq(x_old),
			x==0 ==> to_seq(rev as nat).reverse() =~= to_seq(x_old),

			x <= rev ==> (x * 10 + rev % 10) > rev/10,
			// x == 0 ==>


		decreases x
	{
		//prove no overflow
		assert(rev * 10 + x % 10 <= u32::MAX) by{
			//
			assert(x > rev);
			assert(count_digits(x as nat) >= count_digits(rev as nat)) by {
				count_digits_mono(x as nat, rev as nat)
			}
			assert(pow10(count_digits(x as nat)) >= pow10(count_digits(rev as nat))) by{
				lemma_pow10_mono(count_digits(x as nat), count_digits(rev as nat));
			}
			assert(rev * pow10(count_digits(rev as nat)) <= reverse_spec(x_old)) by(nonlinear_arith)
				requires
				pow10(count_digits(x as nat)) >= pow10(count_digits(rev as nat)),
				rev * pow10(count_digits(x as nat)) + reverse_spec(x as nat) == reverse_spec(x_old);
			if(rev <= 100){}
			else{
				assert(count_digits(rev as nat) >= count_digits(100)) by{count_digits_mono(rev as nat, 100)}
				assert(count_digits(100) == 3) by {reveal_with_fuel(count_digits, 4)}
				assert(pow10(count_digits(rev as nat)) >= pow10(3)) by {lemma_pow10_mono(count_digits(rev as nat), 3)}
				assert(pow10(3) == 1000) by {reveal_with_fuel(pow10, 4)}
				assert(rev * 1000 <= reverse_spec(x_old)) by (nonlinear_arith)
					requires 1000 <= pow10(count_digits(rev as nat)),
								rev * pow10(count_digits(rev as nat)) <= reverse_spec(x_old);

				assert(rev * 10 + x%10 <= rev * 1000 / 10) ;

				assert(rev * 10 + x%10 <= reverse_spec(x_old) / 10);

				assert(reverse_spec(x_old) <= pow10(count_digits(x_old))) by {lemma_reverse_spec(x_old)}

				assert(pow10(count_digits(x_old)) <= pow10(count_digits(u32::MAX as nat))) by{
					assert(count_digits(x_old) <= count_digits(u32::MAX as nat)) by{count_digits_mono(u32::MAX as nat, x_old)}
					lemma_pow10_mono(count_digits(u32::MAX as nat),count_digits(x_old))
				}
				assert(pow10(count_digits(u32::MAX as nat)) < u32::MAX * 10) by{
          lemma_u32MAX()
				}
			}
		}
		let ghost rev_prev = rev as nat;
		let ghost x_prev = x as nat;

		let digit = x % 10;
		rev = rev * 10 + digit;
		x = x/10;

    //I1
    proof{
      assert(rev as nat * pow10(count_digits(x as nat)) + reverse_spec(x as nat)
        == reverse_spec(x_old as nat)) by
      {
				//
        assert(rev == rev_prev * 10 + digit);
        assert(x_prev == x * 10 + digit);

        assert(rev_prev * pow10(count_digits(x_prev)) + reverse_spec(x_prev)
          == reverse_spec(x_old as nat)
        );

        assert(count_digits(x_prev) == count_digits(10 * x as nat + digit as nat));

        assert(
          (rev_prev * 10 + digit as nat) * pow10(count_digits(x as nat))
          + reverse_spec(x as nat)

          ==

          rev_prev * pow10(count_digits(10 * x as nat + digit as nat))
          + reverse_spec(x as nat * 10 +  digit as nat)

        ) by {

          assert(reverse_spec(x as nat * 10 + digit as nat)
            == digit * pow10(count_digits(x as nat)) + reverse_spec(x as nat)
          ) by{
            if x == 0 {
              assert(pow10(count_digits(x as nat)) == 1);
              assert(digit * pow10(count_digits(x as nat)) == digit * 1);
            }
            else {
              assert(x_prev/10 == x);
              assert(x_prev%10 == digit);
            }
          }

          assert(count_digits(10 * x as nat + digit as nat) == 1 + count_digits(x as nat));

          assert((rev_prev * 10 + digit as nat) * pow10(count_digits(x as nat))
            == rev_prev * 10 * pow10(count_digits(x as nat)) + digit as nat * pow10(count_digits(x as nat))
          ) by (nonlinear_arith);

          assert(
            rev_prev * pow10(count_digits(10 * x as nat + digit as nat))
            == rev_prev * pow10(1 + count_digits(x as nat))
          );

          assert(
            rev_prev * pow10(count_digits(10 * x as nat + digit as nat))
            == rev_prev * (10 * pow10(count_digits(x as nat)))
          ) by{
            reveal_with_fuel(pow10, 2)
          }

          assert(rev_prev * (10 * pow10(count_digits(x as nat)))
            == rev_prev * 10 * pow10(count_digits(x as nat))
          ) by (nonlinear_arith);
        }
      }
    }


		assert(x > rev ==> count_digits(x as nat) >= count_digits(rev as nat)) by{
			if x > rev {
				count_digits_mono(x as nat, rev as nat)
			}
		}

		assert(x <= rev ==> count_digits(x as nat) >= count_digits(rev as nat) - 2) by{
			assert(count_digits(x_prev) >= count_digits(rev_prev));
			assert(count_digits(x as nat) == count_digits(x_prev) - 1);
			assert(count_digits(rev as nat) == count_digits(rev_prev) + 1);
		}



    // let ghost x_v = x;

		//I2
	}


	proof{
		// assert(x > 0);

		assert(x * 10 + rev % 10 > rev/10);


		assert(count_digits(x as nat) >= count_digits(rev as nat) - 2);
		assert(rev >= x);
		assert(rev * pow10(count_digits(x as nat)) + reverse_spec(x as nat)
        		== reverse_spec(x_old));


    // assert(to_seq(x_old).reverse() =~= to_seq(x_old))

		if x == 0 {

			assert(count_digits(rev as nat) <= 2);
			assert(to_seq(rev as nat).reverse() =~= to_seq(x_old));

			assert(to_seq(x_old).reverse() =~= to_seq(x_old) <==>
				to_seq(rev as nat).reverse() =~= to_seq(rev as nat)
			);
			assert(rev % 10 > rev / 10);
      assert(rev != 0);
      lemma_1(rev as nat);


		}
		else {
      assert((x * 10 + rev % 10) > rev/10);
  		assert(count_digits(x as nat) >= count_digits(rev as nat) - 2);

			assert(to_seq(x as nat) + to_seq(rev as nat).reverse() =~= to_seq(x_old));
			assert(to_seq(x_old).reverse() =~= to_seq(x_old) <==>
				to_seq(x as nat) + to_seq(rev as nat).reverse()
				=~= to_seq(rev as nat) + to_seq(x as nat).reverse()
			);

      lemma_2(x as nat, rev as nat);
			// x != 0,
			// to_seq(10 * rev + digit) = to_seq(rev) + [digit] + to_seq(rev).reverse()
			// to_seq(rev) + (to_seq(rev) + [digit]).reverse()


		}
	}

  // proof{
  //   assert(to_seq(x_old).reverse() =~= to_seq(x_old) ==> x == rev || (x == rev/10)) by{
  //     if x == 0{
  //         lemma_1(rev as nat);
  //     }
  //     else {
  //       lemma_2(x as nat, rev as nat);
  //     }
  //   }
  // }


	return x == rev || x == (rev / 10)

}

proof fn lemma_1(rev:nat)
  requires
    rev%10 > rev/10,
    count_digits(rev) <= 2,
  ensures
    to_seq(rev).reverse() =~= to_seq(rev) <==> 0 == (rev/10)
{
  assert(to_seq(rev).len() == count_digits(rev)) by{
    lemma_to_seq_eq_count_digits(rev)
  }

  assert(0 == rev/10 ==> to_seq(rev).reverse() =~= to_seq(rev)) by{
    if 0 == rev/10 { assert(0 < rev < 10); }
  }

  assert(to_seq(rev).reverse() =~= to_seq(rev) ==> 0 == (rev/10)) by{
    if to_seq(rev).reverse() =~= to_seq(rev) {
      assert(to_seq(rev).len() <= 2);
      if to_seq(rev).len() == 0 {
        assert(rev == 0); assert(false)
      }
      else if to_seq(rev).len()==2{
        assert(count_digits(rev) == 2);
        assert(to_seq(rev).reverse() =~= seq![to_seq(rev)[1], to_seq(rev)[1]]);
        assert(to_seq(rev)[0] == to_seq(rev)[1]);
        assert(to_seq(rev)[0] == rev%10);

        assert(9 < rev < 100) by{
          assert(count_digits(9) == 1) by {reveal_with_fuel(count_digits, 2)}
          assert(count_digits(100) == 3) by {reveal_with_fuel(count_digits, 4)}
          if rev <= 9 {
            assert(count_digits(rev) <= 1) by {count_digits_mono(9, rev)}
            assert(false)
          }
          if rev >= 100{
            assert(count_digits(rev) >= 3) by {count_digits_mono(rev, 100)}
          }
        }
        assert(to_seq(rev) =~= seq![rev/10, rev%10]) by {reveal_with_fuel(to_seq, 2)}
        assert(rev/10 == rev%10);
        assert(false);
      }
      else {
        assert(count_digits(rev) == 1);
        if rev >= 10 {
          assert(count_digits(rev) >= 2) by {
            count_digits_mono(rev, 10);
            assert(count_digits(10) == 2) by {reveal_with_fuel(count_digits, 2)}
          }
          assert(false)
        }
        assert(0 < rev <10);
      }
    }
  }
}

proof fn lemma_2(x:nat, rev:nat)
  requires
    x <= rev,
    x != 0,
    x * 10 + rev % 10 > rev/10,
    count_digits(x) >= count_digits(rev) - 2,
  ensures
    to_seq(x) + to_seq(rev).reverse()
      =~= to_seq(rev) + to_seq(x).reverse()
    <==>
      x == rev || x == (rev / 10),
{
  //
  assert(x == rev || x == (rev/10) ==>     to_seq(x) + to_seq(rev).reverse()
      =~= to_seq(rev) + to_seq(x).reverse()
  ) by

  {
    if x == rev {}
    else if x == (rev/10) {
      let digit = (rev - 10 * x) as nat;
      assert(0 <= digit <= 9) by (nonlinear_arith)
        requires x == rev/10, digit == rev - 10 * x;
      assert(to_seq(10 * x + digit) =~= to_seq(x).push(digit));
    }
  }

  assert(to_seq(x) + to_seq(rev).reverse()
      =~= to_seq(rev) + to_seq(x).reverse()
      ==> x == rev || x == (rev/10)
  ) by
  {
    if count_digits(rev) == count_digits(x) + 2{

      assert(count_digits(rev) >= 2);

      assert(rev >= 10) by {
        if (rev <= 9) {
          assert(count_digits(9) == 1) by {reveal_with_fuel(count_digits, 2)}
          count_digits_mono(9, rev);
          assert(count_digits(rev) <= 1);
          assert(false);
          //
        }
        else{}
      }

      assert(x * 10 + rev % 10 > rev/10);
      assert(to_seq(x).len() == count_digits(x)) by {lemma_to_seq_eq_count_digits(x)};
      assert(to_seq(rev).len() == count_digits(rev)) by {lemma_to_seq_eq_count_digits(rev)};

      let len1 = to_seq(x).len() as int;
      assert(to_seq(rev).len() == len1 + 2);

      assert((to_seq(x) + to_seq(rev).reverse())[len1] == to_seq(rev).reverse()[0]);
      assert(to_seq(rev).reverse()[0] == to_seq(rev)[len1 + 1]);

      assert((to_seq(rev) + to_seq(x).reverse())[len1] == to_seq(rev)[len1]);
      assert(to_seq(x) =~= (to_seq(x) + to_seq(rev).reverse()).subrange(0, len1));
      assert(to_seq(rev).subrange(0, len1) =~= (to_seq(rev) + to_seq(x).reverse()).subrange(0, len1));


      if to_seq(x) + to_seq(rev).reverse()
        =~= to_seq(rev) + to_seq(x).reverse()
      {
        assert(to_seq(x) =~= to_seq(rev).subrange(0, len1));
        assert(to_seq(rev)[len1] == to_seq(rev)[len1 + 1]);

        assert(to_seq(rev) =~= to_seq(rev/10).push(rev%10));
        assert(to_seq(rev) =~= to_seq(rev/10/10).push(rev/10 %10).push(rev%10));

        assert(to_seq(x) =~= to_seq(rev/10/10));
        assert(rev/10 %10 == rev %10);
        assert(x == rev/10/10) by {to_seq_eq(x, rev/10/10)}

        assert(false)
        // assert()
      }

      // assert(to_seq(rev)[len1 + 1] == rev%10);

      // to_seq(x)    a1 a2 ... ak
      // to_seq(rev)  b1 b2 ... bk bk1 bk2

      // a1 a2 ... ak bk2 bk1 bk ... b1
      // b1 b2 ... bk bk1 bk2 a1 ... ak
      // bk1 == bk2

      // 10 * x   :     a1 a2 ... ak 0
      // rev % 10 :           bk2
      // rev / 10 :     a1 a2 ... ak bk1

      //
    }
    else if count_digits(rev) == count_digits(x) + 1 {
      // to_seq(x)    a1 a2 ... ak
      // to_seq(rev)  b1 b2 ... bk c

      // a1 a2 ... ak c bk ... b1
      // b1 b2 ... bk c bk2 a1 ... ak
      // ==> x == rev / 10
      let len1 = to_seq(x).len() as int;

      assert(to_seq(x).len() == count_digits(x)) by {lemma_to_seq_eq_count_digits(x)};
      assert(to_seq(rev).len() == count_digits(rev)) by {lemma_to_seq_eq_count_digits(rev)};
      assert(to_seq(rev).len() == len1 + 1);

      assert((to_seq(x) + to_seq(rev).reverse())[len1] == to_seq(rev).reverse()[0]);
      assert(to_seq(rev).reverse()[0] == to_seq(rev)[len1]);

      assert((to_seq(rev) + to_seq(x).reverse())[len1] == to_seq(rev)[len1]);
      assert(to_seq(x) =~= (to_seq(x) + to_seq(rev).reverse()).subrange(0, len1));
      assert(to_seq(rev).subrange(0, len1) =~= (to_seq(rev) + to_seq(x).reverse()).subrange(0, len1));


      if to_seq(x) + to_seq(rev).reverse()
        =~= to_seq(rev) + to_seq(x).reverse()
      {
        assert(to_seq(x) =~= to_seq(rev).subrange(0, len1));
        assert(to_seq(rev) =~= to_seq(rev/10).push(rev%10));
        assert(to_seq(x) =~= to_seq(rev/10));
        assert(x == rev/10) by {to_seq_eq(x, rev/10)}
      }
    }
    else {
      count_digits_mono(rev, x);
      assert(count_digits(rev) == count_digits(x));

      // to_seq(x)    a1 a2 ... ak
      // to_seq(rev)  b1 b2 ... bk

      // a1 a2 ... ak bk ... b1
      // b1 b2 ... bk a1 ... ak
      // ==> x == rev
      // to_seq(x)    a1 a2 ... ak
      // to_seq(rev)  b1 b2 ... bk c

      // a1 a2 ... ak c bk ... b1
      // b1 b2 ... bk c bk2 a1 ... ak
      // ==> x == rev / 10
      let len1 = to_seq(x).len() as int;

      assert(to_seq(x).len() == count_digits(x)) by {lemma_to_seq_eq_count_digits(x)};
      assert(to_seq(rev).len() == count_digits(rev)) by {lemma_to_seq_eq_count_digits(rev)};
      assert(to_seq(rev).len() == len1);


      assert(to_seq(x) =~= (to_seq(x) + to_seq(rev).reverse()).subrange(0, len1));
      assert(to_seq(rev).subrange(0, len1) =~= (to_seq(rev) + to_seq(x).reverse()).subrange(0, len1));


      if to_seq(x) + to_seq(rev).reverse()
        =~= to_seq(rev) + to_seq(x).reverse()
      {
        assert(to_seq(x) =~= to_seq(rev));
        // assert(to_seq(x) == to_seq(rev));
        assert(x == rev) by {to_seq_eq(x, rev)}
      }
    }
  }
}




// proof fn lemma_1(x:nat, rev:nat)
//   requires  x == rev || x == (rev/10)
//   ensures to_seq(rev).reverse() =~= to_seq(rev)

}//verus!


fn main(){}