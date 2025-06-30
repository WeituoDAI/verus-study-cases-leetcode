use vstd::prelude::*;

verus!{


pub open spec fn precondition(nums1:Seq<i32>, nums2:Seq<i32>, m:i32, n:i32) -> bool{
  &&& nums2.len() == n as nat
  &&& nums1.len() == m as nat + n as nat
  &&& 0 <= m
  &&& 0 <= n
  &&& 0 < m + n < 10000
  &&& forall |i:int| m <= i < nums1.len() ==> #[trigger] nums1[i] == 0
  &&& sorted_index(nums1, 0, m as int)
  &&& sorted(nums2)
}

pub open spec fn sorted(s:Seq<i32>) -> bool {
  forall |i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn sorted_index(s:Seq<i32>, start:int, end:int) -> bool{
  &&& 0 <= start <= end <= s.len()
  &&& forall |i:int, j:int| start <= i <= j < end ==> s[i] <= s[j]
}


#[verifier::loop_isolation(false)]
pub fn merge(nums1: &mut Vec<i32>, m: i32, nums2: &Vec<i32>, n: i32)
  requires
    precondition(old(nums1)@, nums2@, m, n)
  ensures
    sorted(nums1@),
    nums1@.to_multiset() =~= old(nums1)@.subrange(0, m as int).to_multiset().add(nums2@.to_multiset())
{
  broadcast use vstd::seq_lib::group_to_multiset_ensures;
  broadcast use vstd::multiset::group_multiset_properties;

  let ghost m0 = m;
  let ghost n0 = n;
  let ghost nums1_prev = *nums1;

  let mut k = m + n - 1;
  let mut m :i32 = m - 1;
  let mut n = n - 1;
  while m >= 0 && n >= 0
    invariant
      -1 <= n < nums2.len(),
      -1 <= m < nums1.len(),
      m + n >= -1,
      k == m + n + 1,
      0 <= k < nums1.len(),
      nums1.len() == m0 as nat + n0 as nat,
      nums2.len() == n0 as nat,
      m < m0,
      n < n0,
      m0 + n0 < 10000,
      sorted(nums2@),
      sorted_index(nums1@, 0, m as int + 1),


      forall |i:int| 0 <= i <= m ==> nums1[i] == nums1_prev[i],
      forall |i:int, j:int| 0 <= i <= m && k < j < nums1.len() ==> nums1[i] <= nums1[j],
      forall |i:int, j:int| 0 <= i <= n && k < j < nums1.len() ==> nums2[i] <= nums1[j],

      sorted_index(nums1@, k as int + 1, nums1.len() as int),

      nums1@.subrange(k as int + 1, nums1.len() as int).to_multiset()
      =~=
      nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset().add(
        nums2@.subrange(n as int + 1, n0 as int).to_multiset()),

    decreases
      k
  {
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_properties;

    let ghost k0 = k as int;
    let ghost nums_prev = *nums1;

    let v1 = nums1[m as usize];
    let v2 = nums2[n as usize];
    if v1 <= v2{
      let ghost nums10 = nums1@.subrange(k as int + 1, nums1.len() as int);
      nums1.set(k as usize, v2);
      assert(k >= m + 1);
      k -= 1;
      n -= 1;
      assert(k >= m);
      proof{
        let nums11 = nums1@.subrange(k as int + 1, nums1.len() as int);
        assert(nums11 =~= seq![v2] + nums10);
        assert(nums11.to_multiset() =~= (nums10 + seq![v2]).to_multiset()) by{
          vstd::seq_lib::lemma_seq_union_to_multiset_commutative(seq![v2], nums10)
        }
        assert(nums10 + seq![v2] =~= nums10.push(v2));
        assert(nums11.to_multiset() =~= nums10.to_multiset().insert(v2));

        let nums20 = nums2@.subrange(n as int + 2, n0 as int);
        let nums21 = nums2@.subrange(n as int + 1, n0 as int);
        assert(nums21 =~= seq![v2] + nums20);

        assert(
          nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset().add(
          nums20.to_multiset())  =~= nums10.to_multiset()
        );

        assert(nums21.to_multiset() =~= nums20.to_multiset().insert(v2)) by
        {
          vstd::seq_lib::lemma_seq_union_to_multiset_commutative(seq![v2],  nums20);
          assert(nums20 + seq![v2] =~= nums20.push(v2));
        }
      }
    }
    else {
      let ghost nums10 = nums1@.subrange(k as int + 1, nums1.len() as int);
      nums1.set(k as usize, v1);
      k -= 1;
      m -= 1;
      proof{
        let nums11 = nums1@.subrange(k as int + 1, nums1.len() as int);
        assert(nums11 =~= seq![v1] + nums10);
        assert(nums11.to_multiset() =~= (nums10 + seq![v1]).to_multiset()) by{
          vstd::seq_lib::lemma_seq_union_to_multiset_commutative(seq![v1], nums10)
        }
        assert(nums10 + seq![v1] =~= nums10.push(v1));
        assert(nums11.to_multiset() =~= nums10.to_multiset().insert(v1));

        let nums1_prev0 = nums1_prev@.subrange(m as int + 2, m0 as int);
        let nums1_prev1 = nums1_prev@.subrange(m as int + 1, m0 as int);
        assert(nums1_prev1 =~= seq![v1] + nums1_prev0);
        let nums20 = nums2@.subrange(n as int + 1, n0 as int);

        assert(
          nums1_prev0.to_multiset().add(
          nums20.to_multiset())  =~= nums10.to_multiset()
        );

        assert(nums1_prev1.to_multiset() =~= nums1_prev0.to_multiset().insert(v1)) by
        {
          vstd::seq_lib::lemma_seq_union_to_multiset_commutative(seq![v1],  nums1_prev0);
          assert(nums1_prev0 + seq![v1] =~= nums1_prev0.push(v1));
        }
      }
    }
  }


  let ghost nums_x = *nums1;
  assert(n == -1 || m == -1);

  assert(sorted_index(nums1@, k as int + 1, nums1.len() as int));

  if m < 0 {
    assert(n >= 0);
    assert(n == k);
    assert(sorted_index(nums1@, n as int + 1, nums1.len() as int));

    for j in 0..(n+1)
      invariant
        0 <= j <= n + 1,
        n < nums2.len(),
        nums2.len() <= nums1.len(),
        nums1.len() == m0 + n0,

        forall |i:int| 0 <= i < j ==> nums1[i] == nums2[i],
        forall |i:int| n < i < nums1.len() ==> nums1[i] == nums_x[i],

        sorted_index(nums1@, 0, j as int),
        sorted_index(nums1@, n as int + 1, nums1.len() as int),
    {
      nums1[j as usize] = nums2[j as usize]
    }

    assert(sorted(nums1@)) by {
      assert(forall |i:int| 0 <= i <= n ==> nums1[i] == nums2[i]);
      assert(sorted_index(nums1@, n as int + 1, nums1.len() as int));
      assert(sorted_index(nums1@, 0, n as int + 1));
      assert(sorted_index(nums1@, 0, nums1.len() as int));
    }

    assert(nums1@.subrange(n as int + 1, nums1.len() as int) =~= nums_x@.subrange(n as int + 1, nums1.len() as int));
    // assert(
    //   nums1@.subrange(n as int + 1, nums1.len() as int).to_multiset()
    //   =~=
    //   nums1_prev@.subrange(0, m0 as int).to_multiset().add(
    //   nums2@.subrange(n as int + 1, n0 as int).to_multiset())
    // );

    assert(nums1@.subrange(0, n as int + 1) =~= nums2@.subrange(0, n as int + 1));

    assert(nums1@ =~= nums1@.subrange(0, n as int + 1) + nums1@.subrange(n as int + 1, nums1.len() as int));
    assert(nums1@.to_multiset() =~=  nums1@.subrange(0, n as int + 1).to_multiset().add(nums1@.subrange(n as int + 1, nums1.len() as int).to_multiset())) by
    {
      vstd::seq_lib::lemma_multiset_commutative(nums1@.subrange(0, n as int + 1), nums1@.subrange(n as int + 1, nums1.len() as int));
    }

    assert(nums1@.subrange(0, n as int + 1).to_multiset() =~= nums2@.subrange(0, n as int + 1).to_multiset());
    assert(nums1@.subrange(n as int + 1, nums1.len() as int).to_multiset() =~=
      nums2@.subrange(n as int + 1, n0 as int).to_multiset().add(nums1_prev@.subrange(0, m0 as int).to_multiset())
    );

    // assert(nums2@.subrange(0, n as int + 1).to_multiset().add(
    //   nums2@.subrange(n as int + 1, n0 as int).to_multiset().add(nums1_prev@.subrange(0, m0 as int).to_multiset()))
    //   =~= nums2@.subrange(0, n as int + 1).to_multiset().add(
    //   nums2@.subrange(n as int + 1, n0 as int).to_multiset()).add(nums1_prev@.subrange(0, m0 as int).to_multiset())
    // );

    assert(nums2@.subrange(0, n as int + 1).to_multiset().add(
      nums2@.subrange(n as int + 1, n0 as int).to_multiset()) =~=
      nums2@.to_multiset()
    ) by{
      vstd::seq_lib::lemma_multiset_commutative(nums2@.subrange(0, n as int + 1), nums2@.subrange(n as int + 1, n0 as int));
      assert(nums2@ =~= nums2@.subrange(0, n as int + 1) + nums2@.subrange(n as int + 1, n0 as int));
    }

    assert(nums1@.to_multiset() =~=
      nums1_prev@.subrange(0, m0 as int).to_multiset().add(nums2@.to_multiset()));

    return;
  }


  proof{
    assert(sorted_index(nums1@, k as int + 1, nums1.len() as int));
    assert(
      nums1@.subrange(k as int + 1, nums1.len() as int).to_multiset()
      =~=
      nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset().add(
      nums2@.subrange(n as int + 1, n0 as int).to_multiset())
    );

    assert(n < 0);
    assert(m >= 0);

    assert(sorted_index(nums1@, 0, m as int + 1));
    assert(k == m);
    assert(sorted_index(nums1@, 0, nums1.len() as int));
    assert(sorted(nums1@));


    // assert(
    //   nums1@.subrange(m as int + 1, nums1.len() as int).to_multiset()
    //   =~=
    //   nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset().add(
    //   nums2@.subrange(0, n0 as int).to_multiset())
    // );
    assert(forall |i:int| 0 <= i <= m ==> nums1[i] == nums1_prev[i]);
    assert(nums1@.subrange(0, m as int + 1) =~= nums1_prev@.subrange(0, m as int + 1));

    assert(nums1@ =~= nums1@.subrange(0, m as int + 1) + nums1@.subrange(m as int + 1, nums1.len() as int));
    assert(nums1@.to_multiset() =~=
        nums1@.subrange(0, m as int + 1).to_multiset().add(
        nums1@.subrange(m as int + 1, nums1.len() as int).to_multiset())
        ) by
    {
      vstd::seq_lib::lemma_multiset_commutative(nums1@.subrange(0, m as int + 1), nums1@.subrange(m as int + 1, nums1.len() as int))
    }
    // assert(nums1@.to_multiset() =~=
    //   nums1_prev@.subrange(0, m as int + 1).to_multiset().add(
    //       nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset().add(
    //       nums2@.subrange(0, n0 as int).to_multiset()))
    // );

    // assert(nums1@.to_multiset() =~=
    //   nums1_prev@.subrange(0, m as int + 1).to_multiset().add(
    //       nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset()).add(
    //       nums2@.subrange(0, n0 as int).to_multiset())
    // );

    assert(nums1_prev@.subrange(0, m as int + 1).to_multiset().add(
          nums1_prev@.subrange(m as int + 1, m0 as int).to_multiset())
      =~=
        nums1_prev@.subrange(0, m0 as int).to_multiset()
    ) by{
      vstd::seq_lib::lemma_multiset_commutative(nums1_prev@.subrange(0, m as int + 1), nums1_prev@.subrange(m as int + 1, m0 as int));
      assert(nums1_prev@.subrange(0, m0 as int) =~= nums1_prev@.subrange(0, m as int + 1) + nums1_prev@.subrange(m as int + 1, m0 as int));
    }
    assert(nums2@.subrange(0, n0 as int) =~= nums2@);
    assert(nums1@.to_multiset() =~=
      nums1_prev@.subrange(0, m0 as int).to_multiset().add(nums2@.to_multiset()));
  }
}






}//verus!

fn main(){}
