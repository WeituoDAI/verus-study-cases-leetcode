use vstd::prelude::*;

use vstd::multiset::Multiset;

verus!{


broadcast use {
  vstd::multiset::group_multiset_properties,
  vstd::seq_lib::group_seq_properties
};


pub open spec fn precondition(s:Multiset<u32>) -> bool{
  exists |single:u32| pre_aux(s, single)
}

pub open spec fn pre_aux(s:Multiset<u32>, single:u32) -> bool{
  &&& s.count(single) == 1
  &&& forall |val:u32| s.count(val) > 0 && val != single ==> s.count(val) == 2
}

pub open spec fn xor_all(s:Seq<u32>) -> u32
  decreases s
{
  if s.len() == 0 {0}
  else {
    s[0] ^ xor_all(s.subrange(1, s.len() as int))
  }
}


pub open spec fn double(s:Multiset<u32>) -> bool{
  forall |val:u32| s.count(val) > 0 ==> s.count(val) == 2
}

// proof fn lemma_sort(s:Seq<u32>)
//   ensures xor_all(s.sort_by(|x:u32, y:u32| x <= y)) == xor_all(s)
// {

// }


proof fn lemma_fold(s:Seq<u32>, s2:Seq<u32>, init:u32, f:spec_fn(u32, u32) -> u32)
  requires
    s.to_multiset() =~= s2.to_multiset(),
    vstd::seq_lib::commutative_foldr(f),
  ensures
    s.fold_right(f, init) == s2.fold_right(f, init)
{
  vstd::seq_lib::lemma_fold_right_permutation(s, s2, f, init);
}


proof fn lemma_xor()
  ensures
    vstd::seq_lib::commutative_foldr(|x:u32, y:u32| x ^ y),
{
  assert (forall|x: u32, y: u32, v: u32| x ^ (y ^ v) == y ^ (x ^ v)) by (bit_vector);
}

proof fn lemma_xor_double(s:Seq<u32>, init:u32)
  requires double(s.to_multiset()), vstd::relations::sorted_by(s, |x:u32, y:u32| x <= y)
  ensures s.fold_right(|x:u32, y:u32| x ^ y, init) == init
  decreases s
{
  let set = s.to_multiset();
  assert(set.len() == s.len());


  if s.len() == 0 {}
  else if s.len() == 1 {
    assert(double(set));
    assert(set.len() == 1);
    let e = set.choose();
    assert(set.count(e) == 2);
    assert(set.len() >= 2);
    // assert(set.to_multiset())
    assert(false);
  }
  else {
    let e2 = s[s.len() - 1];
    let e1 = s[s.len() - 2];

    let f_xor = |x:u32, y:u32| x ^ y;

    assert((|x:u32, y:u32| x <= y) (e1, e2));
    assert(e1 <= e2);

    assert(set =~= s.drop_last().to_multiset().insert(s.last())) by{
      assert(s =~= s.drop_last().push(s.last()));
    }
    let set1 = s.drop_last().to_multiset();

    assert(set.count(e2) == 2);
    assert(set1.count(e2) == 1);

    assert(s.drop_last().contains(e2));
    assert(s.drop_last().len() == s.len() - 1);
    let j = choose |j:int| 0 <= j < s.len() - 1 && s.drop_last()[j] == e2;

    assert(s.drop_last()[j] == e2);

    assert(s.drop_last()[s.drop_last().len() - 1] == e1);

    assert(vstd::relations::sorted_by(s.drop_last(), |x:u32, y:u32| x <= y));

    assert((|x:u32, y:u32| x <= y) (e2, e1));

    assert(e1 == e2);

    let s1 = s.drop_last();
    let s2 = s1.drop_last();

    assert(
      s.fold_right(f_xor, init)
      == s1.fold_right(f_xor, f_xor(e2, init))
    );

    assert(
      s1.fold_right(f_xor, f_xor(e2, init))
      == s2.fold_right(f_xor, f_xor(e1, f_xor(e2, init)))
    );

    assert(f_xor(e1, f_xor(e2, init)) == init) by {
      assert(e1 ^ (e2 ^ init) == init) by (bit_vector)
        requires e1 == e2;
    }

    assert(vstd::relations::sorted_by(s2, |x:u32, y:u32| x <= y));

    assert(s =~= s2.push(e1).push(e1));

    assert(s2.to_multiset().count(e1) == 0);



    assert(double(s2.to_multiset())) by {
      assert forall |val:u32| s2.to_multiset().count(val) > 0 implies s2.to_multiset().count(val) == 2 by
      {
        assert(s.to_multiset() =~= s2.to_multiset().insert(e1).insert(e1));
        if val != e1 {
          assert(s.to_multiset().count(val) > 0);
        }
      }
    }
    lemma_xor_double(s2, init);

  }
}






proof fn lemma_xor_double_0(s:Seq<u32>, init:u32)
  requires double(s.to_multiset()),
  ensures s.fold_right(|x:u32, y:u32| x ^ y, init) == init
{
  let s2 = s.sort_by(|x:u32, y:u32| x <= y);
  s.lemma_sort_by_ensures(|x:u32, y:u32| x <= y);
  lemma_xor_double(s2, init);
  lemma_xor();
  lemma_fold(s, s2, init, |x:u32, y:u32| x ^ y);
}

proof fn main_lemma(s:Seq<u32>, single:u32)
  requires pre_aux(s.to_multiset(), single)
  ensures s.fold_right(|x:u32, y:u32| x ^ y, 0) == single,
{
  assert(s.contains(single));
  let i = choose |i:int| 0 <= i < s.len() && s[i] == single;
  assert(s[i] == single);

  let s2 = s.remove(i).push(single);
  assert(s2.to_multiset() =~= s.to_multiset());

  assert(s2.last() == single);
  let s20 = s2.drop_last();

  assert(double(s20.to_multiset())) by{
    assert(s2 =~= s20.push(single));
    assert(s.to_multiset() =~= s20.to_multiset().insert(single));
    assert forall |val:u32| s20.to_multiset().count(val) > 0 implies s20.to_multiset().count(val) == 2 by
    {
      if val != single {
        assert(s.to_multiset().count(val) > 0);
      }
    }
  }

  let f_xor = |x:u32, y:u32| x ^ y;
  assert(s2.fold_right(f_xor, 0) == single) by{
    assert(s2.fold_right(f_xor, 0) == s20.fold_right(f_xor, f_xor(single, 0)));
    lemma_xor_double_0(s20, f_xor(single, 0));
    assert( single ^ 0 == single) by (bit_vector);
  }

  lemma_xor();
  lemma_fold(s, s2, 0, f_xor);

  // admit()
}



pub fn helper(v:&Vec<u32>, i:usize, acc:u32) -> (res:u32)
  requires 0 <= i <= v.len(),
  ensures
    res == v@.subrange(i as int, v.len() as int).reverse().fold_right(|x:u32, y:u32| x ^ y, acc)
  decreases v.len() - i
{
  if i >= v.len() { acc }
  else {
    proof{
      let f_xor = |x:u32, y:u32| x ^ y;
      // let ghost r = helper(v, (i+1) as usize, v[i as int] ^ acc);

      let s1 = v@.subrange(i + 1, v.len() as int).reverse();
      let s2 = v@.subrange(i as int, v.len() as int).reverse();

      assert(s2.fold_right(f_xor, acc) ==
             s2.drop_last().fold_right(f_xor, f_xor(s2.last(), acc)));
      assert(s2.drop_last() =~= s1);
      assert(s2.last() == v[i as int]);
      assert(s2.fold_right(f_xor, acc) ==
             s1.fold_right(f_xor, v[i as int] ^ acc));
    }
    helper(v, i+1, v[i] ^ acc) // tail recursive
  }
}


pub fn single_number(v:Vec<u32>) -> (res:u32)
  requires
    precondition(v@.to_multiset())
  ensures
    v@.to_multiset().count(res) == 1,
    forall |val:u32| v@.to_multiset().count(val) > 0 && val != res ==> v@.to_multiset().count(val) == 2,

{
  let ghost f_xor = |x:u32, y:u32| x^y;
  let res = helper(&v, 0, 0);

  proof{
    assert(v@.subrange(0, v.len() as int) =~= v@);
    assert(res == v@.reverse().fold_right(f_xor, 0));

    assert(v@.reverse().to_multiset() =~= v@.to_multiset()) by {
      lemma_reverse_to_multiset(v@)
    }

    assert(res == v@.fold_right(f_xor, 0)) by{
      lemma_xor();
      lemma_fold(v@, v@.reverse(), 0, f_xor);
    }

    let single = choose |single:u32| pre_aux(v@.to_multiset(), single);
    assert(res == single) by {main_lemma(v@, single);}
  }

  return res;
}


proof fn lemma_reverse_to_multiset(s:Seq<u32>)
  ensures s.reverse().to_multiset() =~= s.to_multiset()
  decreases s
{
  if s.len() == 0 {}
  else {
    let s2 = s.drop_first();
    let e = s.first();
    assert(s =~= seq![e] + s2);
    assert(s.to_multiset() =~= seq![e].to_multiset().add(s2.to_multiset())) by{
      vstd::seq_lib::lemma_multiset_commutative(seq![e], s2)
    }
    assert(s.reverse() =~=  s2.reverse().push(e));
    assert(s.reverse().to_multiset() =~= s2.reverse().to_multiset().insert(e));
    assert(s2.reverse().to_multiset() =~= s2.to_multiset()) by { lemma_reverse_to_multiset(s2); }
  }
}




}//verus!

fn main(){}