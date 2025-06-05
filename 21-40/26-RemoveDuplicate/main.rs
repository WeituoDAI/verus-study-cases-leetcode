use vstd::prelude::*;

verus!{

proof fn lemma_subrange_contains<T>(s:Seq<T>, la:int, ra:int, lb:int, rb:int)
  requires
    0 <= la <= lb <= rb <= ra <= s.len(),
  ensures
    forall |e:T| s.subrange(lb, rb).contains(e)
      ==> s.subrange(la, ra).contains(e),
  decreases
    ra - la,
{
  let s1 = s.subrange(lb, rb);
  let s2 = s.subrange(la, ra);
  assert forall |e:T| s1.contains(e) implies s2.contains(e) by
  {
    let k = choose |i: int| 0 <= i <s1.len() && s1[i] == e;
    assert(s1[k] == s[k + lb]);
    assert(s[k+lb] == s2[k+lb-la]);
  }
}

// #[verifier::loop_isolation(false)]
pub fn remove_duplicates(nums: &mut Vec<i32>) -> (res:usize)
  requires
    1 <= old(nums)@.len() <= 30000,
    forall |i:int, j:int|
      0 <= i <= j < old(nums)@.len() ==> old(nums)@[i] <= old(nums)@[j],
  ensures
    nums@.subrange(0, res as int).to_set() =~= old(nums)@.to_set(),

    forall |p:int, q:int|
      0 <= p < q < res ==> nums@[p] < nums@[q],
{
  let mut k = 1;
  let len = nums.len();

  let ghost s_old = nums@;

  assert(nums@.subrange(0, k as int).contains(s_old[0]))by{
    assert(nums@[0] == s_old[0]);
    assert(nums@.subrange(0, k as int)[0] == nums@[0]);
  }

  for i in 1..len
    invariant
      len == nums@.len(),
      1 <= len <= 30000,
      1 <= i <= len,
      1 <= k <= i,

      nums@[0] == s_old[0],
      s_old.len() == len,

      forall |p:int, q:int|
        0 <= p <= q < len ==> s_old[p] <= s_old[q],

      forall |p:int|
        k <= p < len ==> #[trigger]nums@[p] == s_old[p],

      forall |p:int, q:int|
        k <= p <= q < len ==> nums@[p] <= nums@[q],

      // I1
      forall |p:int| 0 <= p < i ==>
        nums@.subrange(0, k as int).contains(#[trigger]s_old[p]),
        // (exists |q:int| 0 <= q < k && nums@[q] == #[trigger]s_old[p])

      // I2
      forall |p:int, q:int|
        0 <= p < k && i <= q < len ==>
          nums@[p] <= nums@[q],

      // I3
      forall |p:int, q:int|
        0 <= p < q < k ==> nums@[p] < nums@[q],

      // I4
      forall |p:int| 0 <= p < k ==>
        #[trigger] s_old.contains(nums@[p]),

  {
    let e = nums[i];

    let ghost flag = false;
    let ghost nums_old = nums@;

    if e != nums[k-1] {
      nums.set(k, e); // &mut is limited in Verus
      k += 1;

      proof { flag = true }
    }

    // I1
    proof{
      if flag {
        assert forall |p:int| 0 <= p < i implies
          nums@.subrange(0, k-1).contains(#[trigger]s_old[p]) by
        {
          assert(nums@.subrange(0, k-1) =~= nums_old.subrange(0, k-1));
        }
        assert forall |p:int| 0 <= p < i + 1 implies
          nums@.subrange(0, k as int).contains(#[trigger]s_old[p]) by
        {
          if p < i {
            assert(forall |ele:i32| nums@.subrange(0, k-1).contains(ele)
              ==> nums@.subrange(0, k as int).contains(ele)) by
            {
              lemma_subrange_contains(nums@, 0, k as int, 0, k - 1);
            }
          }
          else {
            assert(p == i);
            assert(nums@.subrange(0, k as int)[k-1] == nums@[i as int]);
          }
        }
      }
      else {
        assert forall |p:int| 0 <= p < i + 1 implies
          nums@.subrange(0, k as int).contains(#[trigger]s_old[p]) by
        {
          if p < i {}
          else {
            assert(nums@[i as int] == nums@[k-1]);
            assert(nums@.subrange(0, k as int)[k-1] == nums@[k-1]);
          }
        }
      }
    }

    // I3
    proof{
      assert forall |p:int, q:int|
          0 <= p <= q < k implies nums@[p] <= nums@[q] by
      {
        if !flag {}
        else {
          assert(forall |a:int| 0 <= a < k-1 ==>
            #[trigger]nums@[a] == nums_old[a]);
          if q < k - 1 {}
          else {
            assert(q == k - 1);
            assert(nums@[k-1] == nums_old[i as int]);
          }
        }
      }
    }

  }//end of loop

  k
}


fn test(){
  let mut v= vec![1usize,2];
  v.set(1, 4);

  assert(v@ =~= seq![1,4]);
}


}//verus!

fn main(){}