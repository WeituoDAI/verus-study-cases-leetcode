use vstd::prelude::*;


verus!{


pub open spec fn to_nat(s:Seq<u32>) -> nat
  recommends forall |i:int| 0 <= i < s.len() ==> s[i] < 10,
  decreases s
{
  if s.len() == 0 {0}
  else {
    (to_nat(s.drop_last()) * 10 + s.last()) as nat
  }
}

proof fn lemma_to_nat_last_add_one(s:Seq<u32>)
  requires s.len() > 0, 0 <= s.last() < 9
  ensures to_nat(s.drop_last().push(add(s.last(), 1))) == to_nat(s) + 1
{
  let s1 = s;
  let s2 = s.drop_last().push(add(s.last(), 1));
  let s10 = s.drop_last();
  assert(s10 =~= s2.drop_last());
  assert(to_nat(s1) == to_nat(s10) * 10 + s.last());
  assert(to_nat(s2) == to_nat(s10) * 10 + add(s.last(), 1));
}


proof fn lemma_to_nat_9(n:nat)
  requires n >= 1,
  ensures
    to_nat(seq![9u32;n]) + 1 == to_nat(seq![1u32] + seq![0u32;n])
  decreases n
{
  let s1 = seq![9;n];
  let s2 = seq![1] + seq![0;n];
  if n == 1{
    assert(to_nat(s1) == 9) by {reveal_with_fuel(to_nat, 2)}
    assert(to_nat(s2) == 10) by {reveal_with_fuel(to_nat, 3)}
  }
  else {
    let s10 = seq![9;(n-1) as nat];
    let s20 = seq![1] + seq![0;(n-1) as nat];
    assert(s10 =~= s1.drop_last());
    assert(s20 =~= s2.drop_last());
    assert(to_nat(s1) == to_nat(s10) * 10 + 9);
    assert(to_nat(s2) == to_nat(s20) * 10 + 0);
    lemma_to_nat_9((n-1) as nat);
  }
}

proof fn lemma_to_nat(s:Seq<u32>, n:nat)
  requires s.len() > 0, 0 <= s.last() < 9,
  ensures
    to_nat(s + seq![9u32;n]) + 1
    == to_nat(s.drop_last().push(add(s.last(), 1)) + seq![0u32;n])
  decreases n
{
  if n == 0 {
    lemma_to_nat_last_add_one(s)
  }
  else {
    let s1 = s + seq![9u32;n];
    let s2 = s.drop_last().push(add(s.last(), 1)) + seq![0u32;n];

    let s10 = s + seq![9u32;(n-1) as nat];
    let s20 = s.drop_last().push(add(s.last(), 1)) + seq![0u32;(n-1) as nat];

    assert(s10 =~= s1.drop_last());
    assert(s20 =~= s2.drop_last());

    assert(to_nat(s2) == to_nat(s20) * 10 + 0);
    assert(to_nat(s1) == to_nat(s10) * 10 + 9);
    lemma_to_nat(s, (n-1) as nat);
  }
}


// pub open spec fn to_nat(s:Seq<nat>) -> nat
//   decreases s
// {
//   if s.len() == 0 {0}
//   else {
//     s[0] * pow10((s.len() - 1) as nat) + to_nat(s.subrange(1, s.len() as int))
//   }
// }


pub open spec fn precondition(s:Seq<u32>) -> bool{
  &&& 1 <= s.len() <= 100
  &&& forall |i:int| 0 <= i < s.len() ==> 0 <= #[trigger]s[i] <= 9
  &&& s.len() != 0 ==> s[0] != 0
}




pub fn plus_one(digits_0: Vec<u32>) -> (res:Vec<u32>)
  requires precondition(digits_0@)
  ensures
    to_nat(res@) == to_nat(digits_0@) + 1
{
  let ghost digits_old = digits_0;

  let mut digits = digits_0;
  let len = digits.len();

  for i in 0..len
    invariant
      digits_0@ =~= digits_old@,

      len == digits.len(),
      precondition(digits_old@),
      digits_old.len() == len,

      forall |j:int| 0 <= j < len ==> 0 <= #[trigger]digits@[j] <= 9,
      forall |j:int| 0 <= j < len - i ==> #[trigger]digits@[j] == digits_old@[j],

      forall |j:int| 0 <= j < i ==> #[trigger]digits_old[len - j - 1] == 9,
      forall |j:int| len - i <= j < len ==> #[trigger]digits_old[j] == 9,


      forall |j:int| 0 <= j < i ==> #[trigger]digits[len - j - 1] == 0,
      forall |j:int| len - i <= j < len ==> #[trigger]digits[j] == 0,


      // We can also use invariant like this :
      // to_nat(digits_old@.subrange(len - i,len as int)) + 1
      // ==
      // to_nat(seq![1u32] + digits@.subrange(len - i, len as int))

      // Compare with Q2 : add two numbers

  {
    let tmp = digits[(len - i - 1) as usize];
    if tmp == 9 {
        digits.set((len - i - 1) as usize, 0);
    }
    else {

      let ghost head = digits@.subrange(0, len - i);
      assert(head =~= digits_old@.subrange(0, len - i));

      proof{
        assert(0 <= digits[len - i -1] < 9);
      }

      digits.set((len - i - 1) as usize, tmp + 1);

      proof{
        assert(digits_old@ =~= head + seq![9u32;i as nat]);
        assert(digits@ =~= head.drop_last().push(add(head.last(),1)) + seq![0u32; i as nat]);
        assert(to_nat(digits@) == to_nat(digits_old@) + 1 ) by {lemma_to_nat(head, i as nat)}
      }


      return digits;
    }
  }

  proof{
    assert forall |j:int| 0 <= j < len implies #[trigger] digits_old[j] == 9
    by {
      assert(digits_old[j] == digits_old[len - (len - 1 - j) - 1]);
    }
    assert(digits_old@ =~= seq![9;len as nat]);

    assert forall |j:int| 0 <= j < len implies #[trigger] digits[j] == 0
    by {
      assert(digits[j] == digits[len - (len - 1 - j) - 1]);
    }
    assert(digits@ =~= seq![0;len as nat]);
  }

  digits.push(0);
  digits.set(0, 1);

  proof{
    assert(digits@ =~= seq![1u32] + seq![0u32;len as nat]);
    assert(to_nat(digits@) == to_nat(digits_old@) + 1) by{
      lemma_to_nat_9(len as nat)
    }
  }

  return digits;
}



}//verus!

fn main(){}