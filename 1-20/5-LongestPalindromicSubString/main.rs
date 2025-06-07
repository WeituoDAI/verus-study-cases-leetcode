use vstd::prelude::*;

verus!{


/// Check vstd/seq_lib.rs

// pub open spec fn reverse(self) -> Seq<A>
//     decreases self.len(),
// {
//     if self.len() == 0 {
//         Seq::empty()
//     } else {
//         Seq::new(self.len(), |i: int| self[self.len() - 1 - i])
//     }
// }
pub open spec fn is_palindromic<T>(s:Seq<T>) -> bool {
  s.reverse() =~= s
}

// end not included
// [start, end)
pub open spec fn is_sub_palindromic<T>(s:Seq<T>, start:int, end:int) ->bool{
  is_palindromic(s.subrange(start, end)) || s.len() == 0
}


pub open spec fn sub_pal_center_at_smaller<T>(s:Seq<T>, i:int, j:int, upper:int) -> bool{
  &&& 0 <= i <= j <= s.len()
  &&& i == j || i + 1 == j
  &&&
    if i == j {
      let expand_len = (upper - 1) / 2;
      (i - expand_len < 0) || (j + expand_len >= s.len())
      || (s[i-expand_len] != s[j+expand_len])
    }
    else {
      let expand_len = upper/2 - 1;
      (i - expand_len < 0) || (j + expand_len >= s.len())
      || (s[i-expand_len] != s[j+expand_len])
    }
}


// pub proof fn lemma_reverse<T>(s1:Seq<T>, s2:Seq<T>)
//   ensures (s1 + s2).reverse() =~= s2.reverse() + s1.reverse()
// {}

// right included
// [left, right]
pub proof fn lemma_0<T>(s:Seq<T>, left:int, right:int)
  requires
    0 <= left <= right < s.len(),
    forall |k:int| 0 <= k <= right - left ==>
      s[left + k] == #[trigger] s[right - k],
  ensures
    is_sub_palindromic(s, left, right+1)
  decreases
    right - left
{
  if right - left == 0 { }
  else if right - left == 1 {
    let s_sub = s.subrange(left, right + 1);
    assert(s_sub.len() == 2);
    assert(s_sub.reverse() =~= s_sub) by {
      assert(s[left + 0] == s[right - 0]);
    }
  }
  else {
    assert forall |k:int| 0 <= k <= (right - 1) - (left + 1) implies
      s[left + 1 + k] == #[trigger] s[right - 1 - k] by
    {
      assert(0 <= (k+1) <= right - left - 1 <= right - left);
      assert(s[left + (k+1)] == s[right - (k+1)]);
    }
    assert(is_sub_palindromic(s, left + 1, right)) by {lemma_0(s, left+1, right-1)}
    let s_sub_sub = s.subrange(left + 1, right);
    let s_sub = s.subrange(left, right + 1);
    let s_rev = s_sub.reverse();
    assert(s_rev =~= s_sub) by {
      assert(s[left + 0] == s[right - 0]);
      assert(s_rev =~= (seq![s[left]] + s_sub_sub + seq![s[right]]).reverse());
    }
  }
}


pub proof fn lemma_1<T>(s:Seq<T>, i:int, j:int, expand_len:int) //right included
  requires
    0 <= i <= j < s.len(),
    i == j || i + 1 == j,
    expand_len >= 0,
    i - expand_len >= 0,
    j + expand_len < s.len(),
    forall |k:int| 0 <= k <= expand_len ==>
      s[i - k] == #[trigger] s[j + k],
  ensures
    is_sub_palindromic(s, i - expand_len, j + expand_len + 1)
  decreases
    expand_len
{
  if expand_len == 0{}
  else {
    let left = i - expand_len;
    let right = j + expand_len;
    assert forall |p:int| 0 <= p <= right - left implies
      s[left + p] == #[trigger] s[right - p] by
    {
      if p <= expand_len {
        assert(left + p == i - (expand_len - p));
        assert(right - p == j + (expand_len - p));
        assert(s[i - (expand_len - p)] == s[j + (expand_len - p)])
      }
      else {
        assert(left + p == j + (i - j + p - expand_len));
        assert(right - p == i - (i - j + p - expand_len));
        assert(s[i - (i - j + p - expand_len)] == s[j + (i - j + p - expand_len)])
      }
    }
    lemma_0(s, left, right);
  }
}


#[verifier::loop_isolation(false)]
fn expand(s: &Vec<u8>, mut i: isize, mut j: isize, left: &mut usize, right: &mut usize)
  requires
    0 < s@.len() <= 1000000,
    0 <= i <= s@.len(),
    i <= j <= s@.len(),
    s@.len() >= *old(right) >= *old(left) >= 0,
    i == j || j == i + 1,
    is_sub_palindromic(s@, *old(left) as int, *old(right) + 1),
  ensures
    s@.len() >= *right >= *left >= 0,
    is_sub_palindromic(s@, *left as int, *right + 1),

    forall |k:int|
      (
      && i == j
      && i - k >= 0 && j + k < s@.len()
      && #[trigger] is_sub_palindromic(s@, i - k, j + k + 1) )
      ==> 2*k + 1 <= *right - *left + 1
    ,

    forall |k:int|
      (
      && i + 1 == j
      && i - k >= 0 && j + k < s@.len()
      && #[trigger] is_sub_palindromic(s@, i - k, j + k + 1) )
      ==> 2*k + 2 <= *right - *left + 1
    ,

    *right - *left >= *old(right) - *old(left),

{
  let ghost i_old = i;
  let ghost j_old = j;

  let ghost current_len = *right - *left;

  while i >= 0 && j < s.len() as isize
        && s[i as usize] == s[j as usize]
    invariant
      0 <= s.len() <= 1000000,
      0 <= i_old <= s.len(),
      i_old <= j_old <= s.len(),
      -1 <= i <= i_old <= j_old <=j <= s@.len(),
      s@.len() >= *right >= *left >= 0,

      i_old - i == j - j_old,

      forall |k:int| 0 <= k < j - j_old ==>
        s@[i_old - k] == #[trigger] s@[j_old + k],

      is_sub_palindromic(s@, *left as int, *right + 1),

      (*right - *left) >= (j - i - 2),
      (*right - *left) >= current_len,

    // NOTE : decreases clause, the integer seems to have type nat.
    //        here "decreases i" does not work
    decreases i + 1,
  {
    if (j - i) as usize > *right - *left {
        *left = i as usize;
        *right = j as usize;

        proof{
          assert(is_sub_palindromic(s@, i as int, j + 1)) by {
            assert(
              forall |k:int| 0 <= k < j - j_old ==>
                s@[i_old - k] == #[trigger] s@[j_old + k]
            );
            lemma_1(s@, i_old as int, j_old as int, j - j_old);
          }
        }
    }
    i -= 1;
    j += 1;
  }

  proof{
    let ghost i_ = i as int;
    let ghost j_ = j as int;
    let ghost max_len = *right as int - *left as int + 1;
    assert(i < 0 || j >= s.len() || s@[i as int] != s@[j as int]);

    if i_old == j_old {
      // i = center - x
      // j = center + x
      let center = i_old as int;
      let x = (center - i) as int;

      assert forall |k:int| 2*k + 1 > max_len
        && center - k >= 0 && center + k < s@.len()
        implies
        ! #[trigger] is_sub_palindromic(s@, center - k, center + k + 1) by
      {
        assert(x <= k);
        let s_sub = s@.subrange(center - k, center + k + 1);
        let s_rev = s_sub.reverse();
        assert(s_rev[k-x] != s_sub[k-x]) by {
          assert(s@[i as int] != s@[j as int])
        }
      }
    }
    else {
      // i = center_1 - x
      // j = center_2 + x
      let center_1 = i_old as int;
      let center_2 = j_old as int;
      let x = (center_1 - i) as int;

      assert forall |k:int| 2*k + 2 > max_len
        && center_1 - k >= 0 && center_2 + k < s@.len()
        implies
        ! #[trigger] is_sub_palindromic(s@, center_1 - k, center_2 + k + 1) by
      {
        assert(x <= k);
        let s_sub = s@.subrange(center_1 - k, center_2 + k + 1);
        let s_rev = s_sub.reverse();
        assert(s_rev[k-x] != s_sub[k-x]) by {
          assert(s@[i as int] != s@[j as int])
        }
      }
    }
  }

}



pub fn longest_palindrome_aux(s: Vec<u8>) -> (res : (usize, usize))
  requires
    0 < s@.len() <= 1000_000 // for ease
  ensures
    // return res : (left, right)
    // refers to the index of substring, [left, right], right included

    // Existence
    // the length is : res.1 - res.0 + 1
    is_sub_palindromic(s@, res.0 as int, res.1 + 1),

    // Maximal
    // notice that :
    //       is_sub_palindromatic(s@, p, q)
    //  <==> s@.subrange(p, q).is_palindromatic()
    //  thus, s@.subrange(p, q).len() == q - p <= res.1 - res.0 + 1
    forall |p:int, q:int|
      0 <= p < q <= s@.len() && is_sub_palindromic(s@, p, q)
      ==> q - p <= res.1 - res.0 + 1
{
    // Convert string to char vector
    let mut left = 0;
    let mut right = 0;
    let len = s.len();

    assert(is_sub_palindromic(s@, left as int, right + 1)) by{}

    for i in 0..len
      invariant
        len == s@.len(),
        0 <= len <= 1000000,
        0 <= i <= len,
        0 <= left <= right <= len,
        is_sub_palindromic(s@, left as int, right + 1),


        forall |k:int, p:int, q:int|
          (0 <= p < i && p == q
          && p - k >= 0 && q + k < s@.len()
          && #[trigger] is_sub_palindromic(s@, p - k, q + k + 1) )
          ==> 2*k + 1 <= right as int - left as int + 1
        ,

        forall |k:int, p:int, q:int|
          (0 <= p < i && p + 1 == q
          && p - k >= 0 && q + k < s@.len()
          && #[trigger] is_sub_palindromic(s@, p - k, q + k + 1) )
          ==> 2*k + 2 <= right as int - left as int + 1
        ,

    {
      // Odd length palindrome
      expand(&s, i as isize , i as isize, &mut left, &mut right);
      // Even length palindrome
      expand(&s, i as isize, i as isize + 1, &mut left, &mut right);
    }

    proof{
      assert(
        forall |k:int, p:int, q:int|
          (
            0 <= p < len && p == q
          && p - k >= 0 && q + k < s@.len()
          && #[trigger] is_sub_palindromic(s@, p - k, q + k + 1) )
          ==> 2*k + 1 <= right as int - left as int + 1
      );

      assert(
        forall |k:int, p:int, q:int|
          (
            0 <= p < len && p + 1 == q
          && p - k >= 0 && q + k < s@.len()
          && #[trigger] is_sub_palindromic(s@, p - k, q + k + 1) )
          ==> 2*k + 2 <= right as int - left as int + 1
      );

      assert forall |p:int, q:int|
        0 <= p < q <= len && is_sub_palindromic(s@, p, q)
        implies
        q - p <= right - left + 1 by
      {
        if (q - p) % 2 == 0{
          let center_1 = (q + p)/2 - 1;
          let center_2 = center_1 + 1;
          let radius = (q - p)/2 - 1;
          assert(center_1 - radius == p);
          assert(center_2 + radius == q - 1);
          assert(is_sub_palindromic(s@, center_1 - radius, center_2 + radius + 1));
          assert(2 * radius + 2 <= right - left + 1);
          assert(q - p - 2 + 2 <= right - left + 1);
        }
        else {
          let center = (q + p)/2; // 2 * center = q + p - 1
          let radius = (q - p)/2; // 2 * radius = q - p - 1
          assert(center - radius == p );
          assert(center + radius == q - 1);
          assert(is_sub_palindromic(s@, center - radius, center + radius + 1));
          assert(2 * radius + 1 <= right - left + 1);
          assert(q - p - 1 + 1 <= right - left + 1);
        }
      }
    }
    // Return the longest palindrome substring
    (left, right)
}


//// We need to transport the proof over Vec<u8> to proof over String
//// We just need to use the same method used in P3; But we do not want to repeat this procedure...
//// To make our life easier, from this problem on, we will regard each String problem as a Vec<u8> Problem
pub fn longest_palindrome(s: String) -> (res : (usize, usize))
  requires
    s.is_ascii(),
    0 < s@.len() <= 1000_000 // for ease
  ensures
    true
{
    let s_chars: Vec<u8> = s.as_str().as_bytes_vec();
    longest_palindrome_aux(s_chars)
}


}//verus!

fn main(){}
