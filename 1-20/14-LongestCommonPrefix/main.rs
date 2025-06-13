use vstd::prelude::*;
use vstd::math::min;


verus!{

#[inline]
pub fn min_usize(x:usize, y:usize) -> (res:usize)
  ensures res == min(x as int, y as int)
{
  if x < y {x} else {y}
}

// pub open spec fn leq_i(s1:Seq<i32>, s2:Seq<i32>, index:int) -> bool
//   decreases s2.len() - index,
// {
//   if index >= s1.len() {true}
//   else if index >= s2.len() {false}
//   else if s1[index] < s2[index] {true}
//   else if s1[index] > s2[index] {false}
//   else {leq_i(s1, s2, index + 1)}
// }


pub open spec fn leq(s1:Seq<i32>, s2:Seq<i32>) -> bool
  decreases s1,
{
  if s1.len() == 0 {true}
  else if s2.len() == 0 {false}
  else {
    if s1[0] < s2[0] {true}
    else if s1[0] > s2[0] {false}
    else {leq(s1.subrange(1, s1.len() as int), s2.subrange(1, s2.len() as int))}
  }
}



pub proof fn lemma_leq_aux(s1:Seq<i32>, s2:Seq<i32>, s3:Seq<i32>, len:int, k:int)
  requires
    leq(s1, s2), leq(s2, s3),
    len <= s1.len(), len <= s3.len(),
    s1.subrange(0, len) =~= s3.subrange(0, len),
    0 <= k <= len,
  ensures
    s2.len() >= k,
    s1.subrange(0, k) =~= s2.subrange(0, k),
    s3.subrange(0, k) =~= s2.subrange(0, k)

  decreases k
{
  if k == 0 {}
  else if k == 1 {
    if s2.len() == 0 {
      assert(!leq(s1, s2));
      assert(false);
    }
    else {
      assert(s1[0] <= s2[0]) by {assert(leq(s1, s2))}
      assert(s2[0] <= s3[0]) by {assert(leq(s2, s3))}
      assert(s1[0] == s3[0]) by {
        assert(s1[0] == s1.subrange(0, len)[0]);
        assert(s3[0] == s3.subrange(0, len)[0]);
      }
      assert(s2[0] == s1[0]);
    }
  }
  else {
    assert(s2.len() >= 1 && s1.subrange(0, 1) =~= s2.subrange(0, 1)) by {lemma_leq_aux(s1, s2, s3, len, 1)}
    assert(len >= 2);

    assert(s1[0] == s1.subrange(0, len)[0]);
    assert(s3[0] == s3.subrange(0, len)[0]);
    assert(s2[0] == s2.subrange(0, 1)[0]);

    assert(s1[0] == s3[0]);
    assert(s1[0] == s2[0]);


    assert(leq(s1.subrange(1, s1.len() as int), s2.subrange(1, s2.len() as int)));
    assert(leq(s2.subrange(1, s2.len() as int), s3.subrange(1, s3.len() as int)));
    assert(k - 1 <= len - 1);


    let s10 = s1.subrange(1, s1.len() as int);
    let s20 = s2.subrange(1, s2.len() as int);
    let s30 = s3.subrange(1, s3.len() as int);

    assert(s10.len() == s1.len() - 1);
    assert(s30.len() == s3.len() - 1);

    assert(len - 1 <= s10.len());
    assert(len - 1 <= s30.len());
    assert(s10.subrange(0, len-1) =~= s1.subrange(1, len));
    assert(s30.subrange(0, len-1) =~= s3.subrange(1, len));

    assert(s1.subrange(1, len) =~= s1.subrange(0, len).subrange(1, len));
    assert(s3.subrange(1, len) =~= s3.subrange(0, len).subrange(1, len));

    assert(s10.subrange(0, len-1) =~= s30.subrange(0, len-1));

    lemma_leq_aux(s10, s20, s30, len-1, k-1);
    assert(s20.len() >= k- 1);
    assert(s10.subrange(0, k-1) =~= s20.subrange(0, k-1));

    assert(s20.subrange(0, k-1) =~= s2.subrange(1, k));
    assert(s10.subrange(0, k-1) =~= s1.subrange(1, k));

    assert(s1.subrange(0, k) =~= seq![s1[0]] + s1.subrange(1, k));
    assert(s2.subrange(0, k) =~= seq![s2[0]] + s2.subrange(1, k));
  }
}


pub proof fn lemma_leq(s1:Seq<i32>, s2:Seq<i32>, s3:Seq<i32>, len:int)
  requires
    len >= 0,
    leq(s1, s2), leq(s2, s3),
    len <= s1.len(), len <= s3.len(),
    s1.subrange(0, len) =~= s3.subrange(0, len),
  ensures
    s2.len() >= len,
    s1.subrange(0, len) =~= s2.subrange(0, len),
    s3.subrange(0, len) =~= s2.subrange(0, len)
{
  lemma_leq_aux(s1, s2, s3, len, len)
}


// proof fn test(){
//   assert(leq(seq![], seq![1,2])) by {reveal_with_fuel(leq, 2)}
//   assert(leq(seq![1,1], seq![1,2])) by {reveal_with_fuel(leq, 2)}
//   assert(leq(seq![1], seq![1,2])) by {reveal_with_fuel(leq, 3)}
//   assert(!leq(seq![1,3], seq![1,2])) by {reveal_with_fuel(leq, 3)}
//   assert(leq(seq![1,1,99], seq![1,2])) by {reveal_with_fuel(leq, 3)}
// }


pub open spec fn min_len(v:Seq<Vec<i32>>, len:int) -> bool
{
  &&& forall |i:int| 0 <= i < v.len() ==> #[trigger]v[i].len() >= len
  &&& exists |i:int| 0 <= i < v.len() && #[trigger]v[i].len() == len
}


// if we assume v is sorted
pub fn longest_common_prefix(v:&Vec<Vec<i32>>) -> (res:Vec<i32>)
  requires
    v.len() >= 1,
    forall |i:int, j:int| 0 <= i <= j < v.len() ==> leq(v@[i]@, v@[j]@),

  ensures
    forall |j:int|#![all_triggers] 0 <= j < v.len() ==>
      res@ =~= v@[j]@.subrange(0, res@.len() as int)
      && v@[j]@.len() >= res@.len(),

    min_len(v@, res.len() as int)
    // || v@[0]@[res.len() as int] != v@[v.len() - 1]@[res.len() as int]
   || exists |k1:int, k2:int| #![all_triggers]
    0 <= k1 < k2 < v.len() &&
    v@[k1]@[res.len() as int] != v@[k2]@[res.len() as int],


{

  if v.len() == 1 {return v[0].clone()}

  let v1 = &v[0];
  let v2 = &v[v.len() - 1];

  let len = min_usize(v1.len(), v2.len());
  let mut res = Vec::<i32>::new();

  let i = 0;


  for i in 0..len
    invariant
      v.len() > 1,
      0 <= i <= len,
      len <= v1.len(),
      len <= v2.len(),
      forall |j:int| 0 <= j < i ==> v1@[j] == v2@[j],
      forall |j:int| 0 <= j < v.len() ==> #[trigger]leq(v1@, v@[j]@) && leq(v@[j]@, v2@),
      res@ =~= v1@.subrange(0, i as int),
      res@ =~= v2@.subrange(0, i as int),

      v1@ =~= v@[0]@,
      v2@ =~= v@[v.len()-1]@,

      res@.len() == i,

  {
    if v1[i] == v2[i]{
      res.push(v1[i])
    }
    else {
      assert(v1@.subrange(0, i + 1) =~= v2@.subrange(0, i+1) ==> false) by{
        assert(v1@.subrange(0, i+1)[i as int] == v1@[i as int]);
        assert(v2@.subrange(0, i+1)[i as int] == v2@[i as int]);
      }


      assert forall |j:int|#![all_triggers] 0 <= j < v.len() implies
        v@[j]@.len() >= res@.len() &&
        res@ =~= v@[j]@.subrange(0, res@.len() as int)
      by
      {
        assert(leq(v1@, v@[j]@));
        assert(leq(v@[j]@, v2@));
        lemma_leq(v1@, v@[j]@, v2@, res@.len() as int);
      }
      assert(0 < v.len() - 1);
      assert(v@[0]@[res.len() as int] != v@[v.len() - 1]@[res.len() as int]);

      return res;
    }
  }

  assert(res@ =~= v1@.subrange(0, len as int));
  assert(res@ =~= v2@.subrange(0, len as int));

  assert forall |j:int| #![all_triggers]0 <= j < v.len() implies
    res@ =~= v@[j]@.subrange(0, res@.len() as int)
    && v@[j]@.len() >= res@.len()

  by
  {
    assert(leq(v1@, v@[j]@));
    assert(leq(v@[j]@, v2@));
    lemma_leq(v1@, v@[j]@, v2@, res@.len() as int);
  }
  return res;
}




///////////////////////////////////////////////////

#[verifier::external_body]
pub fn sort(v: &mut Vec<Vec<i32>>)
  ensures
    old(v)@.to_multiset() =~= v@.to_multiset(),
    forall |i:int, j:int| 0 <= i <= j < v.len() ==> leq(v@[i]@, v@[j]@),

    //corr
    old(v).len() == v.len(),
    forall |val:Vec<i32>| old(v)@.contains(val) <==> v@.contains(val),

{
  unimplemented!()
}

// this is quite awkward
// I will not do similar proof any more in this project...
proof fn lemma_to_multiset(s1:Seq<Vec<i32>>, s2:Seq<Vec<i32>>, len:int)
  requires
    s1.to_multiset() =~= s2.to_multiset(),
    s1.len() == s2.len(),
    forall |val:Vec<i32>| s1.contains(val) <==> s2.contains(val),
    min_len(s1, len) ||
    exists |k1:int, k2:int| #![trigger s1[k1]@[len], s1[k2]@[len]]0 <= k1 < k2 < s1.len() && s1[k1]@[len] != s1[k2]@[len],
  ensures
    min_len(s2, len) ||
    exists |k1:int, k2:int| #![trigger s2[k1]@[len], s2[k2]@[len]]0 <= k1 < k2 < s2.len() && s2[k1]@[len] != s2[k2]@[len],

{
  assert(min_len(s1, len) ==> min_len(s2, len)) by{
    if min_len(s1, len){
      assert forall |i:int| 0 <= i < s2.len() implies #[trigger]s2[i].len() >= len by
      {
        assert(s2.contains(s2[i]));
        assert(s1.contains(s2[i]));
        let i0 = choose |i0:int| 0<=i0<s1.len() && s1[i0] == s2[i];
        assert(s1.contains(s1[i0]));
        assert(s1[i0].len() >= len);
      }

      assert(exists |i:int| 0 <= i < s2.len() && #[trigger]s2[i].len() == len) by{
        let i0 = choose |i0:int| 0 <= i0 < s1.len() && #[trigger]s1[i0].len() == len;
        assert(s1[i0].len() == len);
        assert(s2.contains(s1[i0]));
      }
    }
  }

  if (exists |k1:int, k2:int| #![trigger s1[k1]@[len], s1[k2]@[len]]0 <= k1 < k2 < s1.len() && s1[k1]@[len] != s1[k2]@[len])
  {
    let (k1, k2) = choose |k1:int, k2:int| #![trigger s1[k1]@[len], s1[k2]@[len]]0 <= k1 < k2 < s1.len() && s1[k1]@[len] != s1[k2]@[len];
    assert(s2.contains(s1[k2]));
    assert(s2.contains(s1[k1]));
  }
}


pub fn longest_common_prefix_2(v:&mut Vec<Vec<i32>>) -> (res:Vec<i32>)
  requires
    old(v).len() >= 1,

  ensures
    forall |j:int|#![all_triggers] 0 <= j < v.len() ==>
      res@ =~= v@[j]@.subrange(0, res@.len() as int)
      && v@[j]@.len() >= res@.len(),

    min_len(v@, res.len() as int)
   || exists |k1:int, k2:int| #![all_triggers]
    0 <= k1 < k2 < v.len() &&
    v@[k1]@[res.len() as int] != v@[k2]@[res.len() as int],

{
  sort(v);

  let res = longest_common_prefix(v);
  proof{
    lemma_to_multiset(v@, old(v)@, res.len() as int);
  }
  return res;
}


}//verus!

fn main(){}