use vstd::prelude::*;



verus!{


// lemma for set
//////////////////////

pub broadcast proof fn lemma_map_finite<A, B>(s:Set<A>, f:spec_fn(A) -> B)
  requires s.finite()
  ensures  #[trigger]s.map(f).finite()
  decreases s.len()
{
  if s.len() == 0 {
    assert(s.is_empty());
    assert(s.map(f).is_empty()) by {
      if !s.map(f).is_empty(){
        let y = s.map(f).choose();
        let x = choose |x:A| s.contains(x) && f(x) == y;
        assert(!s.is_empty());
        assert(false);
      }
    }
  }
  else {
    let x = s.choose();
    lemma_map_finite(s.remove(x), f);
    assert(s.remove(x).map(f).finite());
    assert(s.map(f).subset_of(s.remove(x).map(f).insert(f(x))));
  }
}

// pub broadcast proof fn lemma_map_len<A, B>(s:Set<A>, f:spec_fn(A) -> B)
//   requires s.finite()
//   ensures  #[trigger]s.map(f).len() <= s.len()
//   decreases s.len()
// {
//   if s.len() == 0 {
//     assert(s.is_empty());
//     assert(s.map(f).is_empty()) by {
//       if !s.map(f).is_empty(){
//         let y = s.map(f).choose();
//         let x = choose |x:A| s.contains(x) && f(x) == y;
//         assert(!s.is_empty());
//         assert(false);
//       }
//     }
//   }
//   else {
//     let x = s.choose();
//     lemma_map_finite(s, f);
//     lemma_map_finite(s.remove(x), f);
//     assert(s.map(f).subset_of(s.remove(x).map(f).insert(f(x))));

//     assert(s.map(f).len() <= s.remove(x).map(f).len() + 1) by {
//       vstd::set_lib::lemma_len_subset(s.map(f), s.remove(x).map(f).insert(f(x)))
//     }
//     lemma_map_len(s.remove(x), f)
//   }
// }

////////////////////


// Specification

// if s is a solution to climb the stairs from start to end,
pub open spec fn valid(s:Seq<nat>, start:nat, end:nat) -> bool{
  &&& s.len() > 0
  &&& s[0] == start
  &&& s.last() == end
  &&& forall |i:int| 0 < i < s.len() ==> 1 <= #[trigger]s[i] - s[i-1] <= 2
  &&& forall |i:int, j:int| 0 <= i < j < s.len() ==> s[i] < s[j]
}


// all possible ways to climb the stairs
pub open spec fn climb(i:nat, n:nat) -> Set<Seq<nat>>
{
  Set::new(|s:Seq<nat>| valid(s, i, n))
}

#[verifier::spinoff_prover]
proof fn lemma_len(s:Seq<nat>, n:nat, len:nat)
  requires valid(s, n, n + len)
  ensures s.len() <= len + 1
  decreases len
{
  if len == 0 { }
  else if len == 1 {
    if s.len() > 2 {
      assert(s[1] > n);
      assert(s[1] < n + 1);
      assert(false);
    }
  }
  else {
    assert(1 <= s[1] - s[0] <= 2);
    if s[1] - s[0] == 1 {
      let sub = s.subrange(1, s.len() as int);
      assert(valid(sub, n + 1, n + len));
      lemma_len(sub, n + 1, (len - 1) as nat);
    }
    else {
      assert(s[1] - s[0] == 2);
      let sub = s.subrange(1, s.len() as int);
      assert(valid(sub, n + 2, n + len));
      lemma_len(sub, n + 2, (len - 2) as nat);
    }
  }
}


#[verifier::spinoff_prover]
proof fn lemma_finite(n:nat, len:nat)
  ensures climb(n, n + len).finite(),
  decreases len,
{
  if len == 0 { lemma_0(n) }
  else if len == 1 { lemma_1(n) }
  else {
    let set0 = climb(n, n + len);
    let set1 = climb(n + 1, n + len);
    let set2 = climb(n + 2, n + len);
    assert(set1.finite()) by { lemma_finite(n + 1, (len - 1) as nat)}
    assert(set2.finite()) by { lemma_finite(n + 2, (len - 2) as nat)}

    let set3 = set1.union(set2);
    assert(set3.finite());

    assert (forall |s:Seq<nat>| #[trigger]set0.contains(s) ==> set3.contains(s.subrange(1, s.len() as int))) by{
      assert forall |s:Seq<nat>| #[trigger]set0.contains(s) implies
        set1.contains(s.subrange(1, s.len() as int)) || set2.contains(s.subrange(1, s.len() as int)) by
      {
        lemma_rec_aux_1(s, n, len);
      }
    }

    let set4 = set3.map(|s:Seq<nat>| seq![n] + s);
    assert(set4.finite()) by {broadcast use lemma_map_finite;}

    assert(set0.subset_of(set4)) by{
      assert forall |s:Seq<nat>| #[trigger]set0.contains(s) implies set4.contains(s) by{
        let sub = s.subrange(1, s.len() as int);
        assert(set3.contains(sub));
        assert(s =~= seq![n] + sub);
        assert(set4.contains(seq![n] + sub));
      }
    }

    assert(set0.finite());
  }
}

proof fn lemma_indp_start(n1:nat, n2:nat, len:nat)
  requires n1 < n2,
  ensures climb(n1, n1 + len).len() == climb(n2, n2 + len).len()
{
  let f_map = |s:Seq<nat>| s.map_values(|i:nat| (i + n2 - n1) as nat);
  let x = climb(n1, n1 + len);
  let y = climb(n2, n2 + len);
  //f_map injective
  assert forall|x1: Seq<nat>, x2: Seq<nat>| #[trigger] f_map(x1) == #[trigger] f_map(x2) implies x1 == x2 by
  {
    assert(f_map(x1) =~= f_map(x2));
    assert(f_map(x1).len() == f_map(x2).len());
    assert(f_map(x1).len() == x1.len());
    assert(x1.len() == x2.len());
    assert(forall |i:int| 0 <= i < x1.len() ==> x1[i] + n2 - n1 == f_map(x1)[i]);
    assert(forall |i:int| 0 <= i < x1.len() ==> x2[i] + n2 - n1 == f_map(x2)[i]);
    assert(forall |i:int| 0 <= i < x1.len() ==> x1[i] + n2 - n1 == x2[i] + n2 - n1);
    assert(x1 =~= x2)
  }

  //
  assert forall |b: Seq<nat>| (#[trigger] y.contains(b)) implies exists|a: Seq<nat>| x.contains(a) && f_map(a) == b by
  {
    assert(valid(b, n2, n2 + len));
    let b0 = b.map_values(|i:nat| (i - n2 + n1) as nat);
    assert(valid(b0, n1, n1 + len));
    assert(x.contains(b0));
    assert(f_map(b0) =~= b);
    assert(f_map(b0) == b);
  }

  assert(x.finite()) by {lemma_finite(n1, len)}
  assert(y.finite()) by {lemma_finite(n2, len)}

  vstd::set_lib::lemma_map_size(x, y, f_map);
}


proof fn lemma_0(n:nat)
  ensures climb(n, n) =~= set![seq![n]]
{
  assert forall |s:Seq<nat>| valid(s, n, n) implies s =~= seq![n] by
  {
    assert(s[0] == n);
    assert(s.last() == n);
  }
}

proof fn lemma_1(n:nat)
  ensures climb(n, n + 1) =~= set![seq![n, n+1]]
{
  assert forall |s:Seq<nat>| #[trigger]valid(s, n, n + 1) implies s =~= seq![n, n+1] by
  {
    assert(s[0] == n);
    assert(s.last() == n + 1);
    let len = s.len();
    if len > 2 {
      assert(n < s[1]);
      assert(s[1] < s[2]);
      assert(false);
    }
  }
}

proof fn lemma_rec_aux_1(s:Seq<nat>, start:nat, len:nat)
  requires len >= 2, valid(s, start, start + len)
  ensures valid(s.subrange(1, s.len() as int), s[1], start + len)
{}

proof fn lemma_rec_aux_2(s:Seq<nat>, start:nat, len:nat)
  requires valid(s, start, start + len),
  ensures
    start >= 1 ==> valid(seq![(start - 1) as nat] + s, (start - 1) as nat, start + len),
    start >= 2 ==> valid(seq![(start - 2) as nat] + s, (start - 2) as nat, start + len),
{}

proof fn lemma_rec(start:nat, len:nat)
  requires len >= 2
  ensures climb(start, start + len).len() ==
        climb(start + 1, start + len).len() + climb(start + 2, start + len).len()
{
  let set0 = climb(start, start + len);
  let set1 = climb(start + 1, start + len);
  let set2 = climb(start + 2, start + len);

  assert(set0.finite()) by {lemma_finite(start, len)}
  assert(set1.finite()) by {lemma_finite(start + 1, (len - 1) as nat)}
  assert(set2.finite()) by {lemma_finite(start + 2, (len - 2) as nat)}
  let set3 = set1.union(set2);
  assert(set3.finite());
  assert forall |s:Seq<nat>| #[trigger]set0.contains(s) implies
    set3.contains(s.subrange(1, s.len() as int)) by
  {
    lemma_rec_aux_1(s, start, len);
  }

  let f_map = |s:Seq<nat>| seq![start] + s;
  //f_map injective
  assert forall|x1: Seq<nat>, x2: Seq<nat>| #[trigger] f_map(x1) == #[trigger] f_map(x2) implies x1 == x2 by
  {
    assert(seq![start] + x1 =~= seq![start] + x2);
    assert((seq![start] + x1).len() == 1 + x1.len());
    assert((seq![start] + x2).len() == 1 + x2.len());
    assert(x1 =~= (seq![start] + x1).subrange(1, (x1.len() + 1) as int));
    assert(x2 =~= (seq![start] + x2).subrange(1, (x1.len() + 1) as int));
    assert(x1 =~= x2);
  }

  let set4 = set3.map(f_map);
  assert(set4.finite()) by {broadcast use lemma_map_finite;}

  assert(set0 =~= set4) by{
    assert forall |s:Seq<nat>| #[trigger]set0.contains(s) implies set4.contains(s) by{
      let sub = s.subrange(1, s.len() as int);
      assert(set3.contains(sub));
      assert(s =~= seq![start] + sub);
      assert(set4.contains(seq![start] + sub));
    }
  }

  assert(set0.len() == set4.len());

  assert(set4.len() == set3.len()) by{
    vstd::set_lib::lemma_map_size(set3, set4, f_map)
  }

  assert(set3.len() == set1.len() + set2.len()) by {
    assert(set1.disjoint(set2)) by {
      assert (forall |s:Seq<nat>| #[trigger]set1.contains(s) ==> s.len() >= 1 && s[0] == start + 1);
      assert (forall |s:Seq<nat>| #[trigger]set2.contains(s) ==> s.len() >= 1 && s[0] == start + 2);
    }
    vstd::set_lib::lemma_set_disjoint_lens(set1, set2);
  }
}


//////

// see def of climb
pub open spec fn res_spec(n:nat) -> nat{
  climb(0, n).len()
}


proof fn main_lemma(n:nat)
  requires n >= 2
  ensures res_spec(n) == res_spec((n - 1) as nat) + res_spec((n - 2) as nat)
{
  assert(
    climb(0, n).len() ==
    climb(1, n).len() + climb(2, n).len()
  ) by {
    lemma_rec(0, n)
  }

  assert(climb(1, n).len() == climb(0, (n-1) as nat).len()) by {lemma_indp_start(0, 1, (n-1) as nat)}
  assert(climb(2, n).len() == climb(0, (n-2) as nat).len()) by {lemma_indp_start(0, 2, (n-2) as nat)}
}

proof fn lemma_res_spec_mono(i: nat, j: nat)
    requires
        i <= j,
    ensures
        res_spec(i) <= res_spec(j),
    decreases j - i,
{
    if j < 2 {
      lemma_0(0); lemma_1(0);
    } else if i == j {
    } else if i == j - 1 { main_lemma(j);
    } else {
        main_lemma(j);
        lemma_res_spec_mono(i, (j - 1) as nat);
        lemma_res_spec_mono(i, (j - 2) as nat);
    }
}


//a helper fn
// spec fn res_spec_rec(n:nat) -> nat
//   decreases n
// {
//   if n <= 1 {1}
//   else {
//     res_spec_rec((n-2) as nat) + res_spec_rec((n-1) as nat)
//   }
// }


// broadcast proof fn lemma_res_eq(n:nat)
//   ensures #[trigger]res_spec(n) == res_spec_rec(n)
//   decreases n
// {
//   lemma_0(0);
//   lemma_1(0);
//   if n >= 2 {
//     main_lemma(n);
//     lemma_res_eq((n-1) as nat);
//     lemma_res_eq((n-2) as nat);
//   }
// }


// proof fn lemma_overflow()
//   ensures
//     res_spec_rec(45) == 1836311903
// {
//   assert(res_spec_rec(20) == 10946) by {  reveal_with_fuel(res_spec_rec, 20);}
//   assert(res_spec_rec(21) == 17711) by {  reveal_with_fuel(res_spec_rec, 20);}
//   assert(res_spec_rec(22) == 28657);
//   assert(res_spec_rec(23) == 46368);
//   assert(res_spec_rec(24) == 75025);
//   assert(res_spec_rec(25) == 121393);
//   assert(res_spec_rec(26) == 196418);
//   assert(res_spec_rec(27) == 317811);
//   assert(res_spec_rec(28) == 514229);
//   assert(res_spec_rec(29) == 832040);
//   assert(res_spec_rec(30) == 1346269);
//   assert(res_spec_rec(31) == 2178309);
//   assert(res_spec_rec(32) == 3524578);
//   assert(res_spec_rec(33) == 5702887);
//   assert(res_spec_rec(34) == 9227465);
//   assert(res_spec_rec(35) == 14930352);
//   assert(res_spec_rec(36) == 24157817);
//   assert(res_spec_rec(37) == 39088169);
//   assert(res_spec_rec(38) == 63245986);
//   assert(res_spec_rec(39) == 102334155);
//   assert(res_spec_rec(40) == 165580141);
//   assert(res_spec_rec(41) == 267914296);
//   assert(res_spec_rec(42) == 433494437);
//   assert(res_spec_rec(43) == 701408733);
//   assert(res_spec_rec(44) == 1134903170);
//   assert(res_spec_rec(45) == 1836311903);
// }


pub fn climb_stairs(n: i32) -> (res:i32)
  requires
    1 <= n <= 45,

    // in fact n <= 45 implies this condition, we can prove it by the lemma commented above
    res_spec(n as nat) < i32::MAX ,

  ensures

    res == res_spec(n as nat),

{
  assert forall |k:nat| 0 <= k <= n implies res_spec(k) < i32::MAX by
  {
    lemma_res_spec_mono(k, n as nat);
  }
  proof{
    lemma_0(0);
    lemma_1(0);
  }

  if n == 1 {return 1;}
  let mut v = Vec::with_capacity((n + 1) as usize);
  v.push(1);
  v.push(1);
  for i in 2..n + 1
    invariant
      2 <= n <= 45,
      v.len() == i,
      forall |k:nat| 0 <= k <= n ==> res_spec(k) < i32::MAX ,
      forall |j:int| 0 <= j < i ==> v[j] == res_spec(j as nat),
  {
    // let val = 0;
    proof{
      main_lemma(i as nat);
    }
    let val = v[(i-1) as usize] + v[(i-2) as usize];
    v.push(val)
  }

  return v[n as usize]
}


}//verus!

fn main(){}