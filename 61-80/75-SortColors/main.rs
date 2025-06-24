use vstd::prelude::*;

verus!{


spec fn precondition(s:Seq<u32>) -> bool {
  &&& 0 <= s.len() <= 300
  &&& forall |i:int| 0 <= i < s.len() ==> 0 <= #[trigger]s[i] <= 2
}


spec fn count(s:Seq<u32>, val:u32) -> nat
  decreases s.len()
{
  if s.len() == 0 {0}
  else if s.last() == val { 1 + count(s.drop_last(), val)}
  else { count(s.drop_last(), val) }
}

broadcast proof fn lemma_count(s:Seq<u32>, val:u32)
  ensures #[trigger] count(s, val) <= s.len()
  decreases s.len()
{
  if s.len() == 0 {}
  else {
    lemma_count(s.drop_last(), val);
  }
}

proof fn lemma_count_012(s:Seq<u32>)
  requires precondition(s)
  ensures count(s, 0) + count(s, 1) + count(s, 2) == s.len()
  decreases s.len()
{
  if s.len() == 0 {}
  else {
    lemma_count_012(s.drop_last());
  }
}

broadcast proof fn lemma_count_to_multiset(s:Seq<u32>, val:u32)
  ensures #[trigger]count(s, val) == s.to_multiset().count(val)
  decreases s
{
  broadcast use {
    vstd::seq_lib::group_to_multiset_ensures,
    vstd::multiset::group_multiset_properties
  };

  if s.len() == 0 {}
  else {
    let v = if s.last() == val {1nat} else {0};
    // let v2 = if s.first() == val {1nat} else {0};


    assert(count(s, val) == v + count(s.drop_last(), val));

    assert(s.to_multiset() =~=
      s.drop_last().to_multiset().insert(s.last())
    ) by {
      assert(s =~= s.drop_last().push(s.last()))
    }
    assert(s.to_multiset().count(val) == v + s.drop_last().to_multiset().count(val));
    lemma_count_to_multiset(s.drop_last(), val);
  }
}

proof fn lemma_count_const(a:nat, b:nat, c:nat)
  ensures
    count(seq![0u32; a] + seq![1u32; b] + seq![2u32; c], 0) == a,
    count(seq![0u32; a] + seq![1u32; b] + seq![2u32; c], 1) == b,
    count(seq![0u32; a] + seq![1u32; b] + seq![2u32; c], 2) == c,
  decreases a + b + c,
{
  // broadcast use {lemma_count_to_multiset, vstd::seq_lib::group_to_multiset_ensures};
  let s1 = seq![0u32; a] + seq![1u32; b] + seq![2u32; c];
  if a + b + c == 0 {}
  else {
    if c != 0{
      let s2 = seq![0u32; a] + seq![1u32; b] + seq![2u32; (c-1) as nat];
      assert(s2 =~= s1.drop_last());
      lemma_count_const(a, b, (c-1) as nat);
    }
    else if b != 0 {
      let s2 = seq![0u32; a] + seq![1u32; (b-1) as nat];
      assert(s2 =~= s1.drop_last());
      lemma_count_const(a, (b-1) as nat, c);
    }
    else {
      let s2 = seq![0u32; (a-1) as nat];
      assert(s2 =~= s1.drop_last());
      lemma_count_const((a-1) as nat, b, c);
    }
  }
}


#[verifier::spinoff_prover]
fn sortColors(nums: &mut Vec<u32>)
  requires precondition(old(nums)@)
  ensures
    vstd::relations::sorted_by(nums@, |x:u32,y:u32| x <= y),
    nums@.to_multiset() =~= old(nums)@.to_multiset(),
{
  let mut a = 0;
  let mut b = 0;
  let mut c = 0;
  for i in 0..nums.len()
    invariant
      precondition(nums@),
      a == count(nums@.subrange(0, i as int), 0),
      b == count(nums@.subrange(0, i as int), 1),
      c == count(nums@.subrange(0, i as int), 2),
      0 <= a <= nums.len(),
      0 <= b <= nums.len(),
      0 <= c <= nums.len(),
  {
    broadcast use lemma_count;
    if(nums[i] == 0) { a +=1; }
    else if(nums[i] == 1) { b +=1; }
    else { c+= 1; }
    proof{
      assert(nums@.subrange(0, i + 1).drop_last() =~= nums@.subrange(0, i as int));
      assert(nums@.subrange(0, i + 1).last() == nums[i as int]);
    }
  }


  assert(nums@.subrange(0, nums.len() as int) =~= nums@);
  assert(a == count(nums@, 0));
  assert(b == count(nums@, 1));
  assert(c == count(nums@, 2));
  assert(a as nat + b as nat + c == nums@.len()) by {lemma_count_012(nums@)}

  for i in 0..a
    invariant
      0 <= i <= a <= nums.len(),
      nums@.len() == old(nums).len(),
      nums@.subrange(0, i as int) =~= seq![0u32;i as nat],
  {
    nums.set(i, 0);
    proof{
      assert(seq![0u32;i as nat].push(0) =~= seq![0u32; (i+1) as nat]);
    }
  }

  assert(a as nat + b as nat + c == nums@.len());

  for i in 0..b
    invariant
      0 <= i <= b,
      b as nat + a as nat <= nums.len(),
      nums@.len() == old(nums).len(),
      nums@.subrange(0, a as int) =~= seq![0u32;a as nat],
      nums@.subrange(a as int, a + i as int) =~= seq![1u32;i as nat],
  {
    nums.set(i + a, 1);
    proof{
      assert(seq![1u32;i as nat].push(1) =~= seq![1u32; (i+1) as nat]);
    }
  }

  // assert(a as nat + b as nat + c == nums@.len());
  for i in 0..c
    invariant
      0 <= i <= c,
      a as nat + b as nat + c as nat <= nums.len(),
      nums@.len() == old(nums).len(),
      nums@.subrange(0, a as int) =~= seq![0u32;a as nat],
      nums@.subrange(a as int, a + b as int) =~= seq![1u32;b as nat],
      nums@.subrange(a as int + b, a + b as int + i as int) =~= seq![2u32;i as nat],
  {
    nums.set(i + a + b, 2);
    proof{
      assert(seq![2u32;i as nat].push(2) =~= seq![2u32; (i+1) as nat]);
    }
  }

  assert(
    nums@ =~= seq![0u32;a as nat] + seq![1u32;b as nat] + seq![2;c as nat]
  );
  proof{
    lemma_count_const(a as nat, b as nat, c as nat);
  }
  assert(vstd::relations::sorted_by(nums@, |x:u32,y:u32| x <= y));
  assert(nums@.to_multiset() =~= old(nums)@.to_multiset()) by{
    broadcast use {
      vstd::seq_lib::group_to_multiset_ensures,
      lemma_count_to_multiset,
    };
    // assert forall |val:u32| nums@.to_multiset().contains(val) implies
    //   nums@.to_multiset().count(val) == old(nums)@.to_multiset().count(val) by
    // {
    //   // assert(nums@.contains(val));
    //   // assert(0 <= val <= 2);
    //   // assert(old(nums)@.to_multiset().count(0) == a);
    //   // assert(old(nums)@.to_multiset().count(1) == b);
    //   // assert(old(nums)@.to_multiset().count(2) == c);
    // }
    // assert forall |val:u32| old(nums)@.to_multiset().contains(val) implies
    //   nums@.to_multiset().count(val) == old(nums)@.to_multiset().count(val) by
    // {
    //   // assert(count(nums@, val) > 0);
    //   // assert(nums@.contains(val));
    //   // assert(0 <= val <= 2);
    // }
  }
}


}//verus!

fn main(){}