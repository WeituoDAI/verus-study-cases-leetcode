use vstd::prelude::*;

verus!{

use std::collections::HashMap;
use vstd::math::max;
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub fn max_i32(a:i32, b:i32) -> (res:i32)
  ensures res == max(a as int, b as int)
{
  if a >= b {a}
  else {b}
}


pub open spec fn no_repeat(l:Seq<u8>, start:int, end:int) -> bool {
  forall |i:int, j:int| start <= i < j < end ==>
    l[i] != l[j]
}

pub open spec fn max_no_repeat(l:Seq<u8>, end:int, n:int) -> bool{
  forall |i:int, j:int| 0 <= i < j <= end &&
    no_repeat(l, i, j) ==> j - i <= n
}

pub open spec fn is_le_3(x: int, y: int, z:int) -> bool {
    x <= y <= z
}

#[verifier::loop_isolation(false)]
pub fn help(s: Vec<u8>) -> (res:i32)
  requires
    0 <= s.len() < 5000000,
  ensures
    max_no_repeat(s@, s.len() as int, res as int)
{
  let mut hash: HashMap<u8, i32> = HashMap::new();
  let mut ans = 0;
  let mut start = 0;
  let str_len = s.len();

  for end in 0..str_len
    invariant
      0 <= str_len < 5000000,
      str_len == s.len(),
      start <= end <= str_len,
      0 <= start <= str_len,
      0 <= ans <= str_len,

      forall |k:u8| hash@.contains_key(k) ==>
        0 <= hash@[k] < end,

      forall |j:int| 0 <= j < end ==>
        hash@.contains_key(#[trigger] s@[j]),

      forall |j:int| 0 <= j < end ==>
        #[trigger] s@[hash@[s@[j]] as int] == s@[j],

      forall |j:int, k:int| 0 <= j < end &&
        #[trigger] hash@[s@[j]] < k < end ==> #[trigger] s@[k] != s@[j],

      forall |ch:u8| hash@.contains_key(ch) ==>
        exists |k:int| 0 <= k < end && s@[k] == ch,

      forall |j:int, k:int| start <= j < k < end ==>
        s@[j] != s@[k],

      no_repeat(s@, start as int, end as int),

      !hash@.contains_key(s@[end as int]) ==>
        no_repeat(s@, start as int, end + 1),

      hash@.contains_key(s@[end as int]) ==>
        s@[hash@[s@[end as int]] as int] == s@[end as int],

      start > 0 ==>
        exists |k:int| start <= k <= end &&
          s@[start - 1] == #[trigger]s@[k],

      forall |j:int|
        ((#[trigger] is_le_3(0, j, start - 1) && (start < end)) ==>
          ! no_repeat(s@, j, end as int)),

      ans >= end - start,

      end != 0 ==> end > start,

      max_no_repeat(s@, end as int, ans as int),

      // no_repeat(s@.subrange(start as int, (end + 1)))
  {

    let ch = s[end as usize];
    let ghost start_old = start;

    // assert(forall |j:int|
    //     ((#[trigger] is_le_3(0, j, start - 1) && (start < end)) ==>
    //       ! no_repeat(s@, j, end as int))
    // );

    match hash.insert(ch, end as i32) {
      None => {},
      Some(i) => {
        start = max_i32(start, i + 1);
        //////
        proof{
          assert(no_repeat(s@, start as int, end + 1));
          assert(s@[i as int] == s@[end as int]);
          if start > i + 1 {
            assert(start > 0);
          } else {
            assert(s@[start - 1] == s@[end as int]);
            assert(i < end);
            assert(exists |k:int| start <= k <= end &&
               s@[start - 1 ] == #[trigger] s@[k]);
          }
        }
        //////
      }
    }
    let ghost ans_old = ans;
    ans = max_i32(ans, end as i32 - start + 1);

    proof{
      assert forall |p:int, q:int| #![all_triggers] 0 <= p < q < end + 1 &&
        no_repeat(s@, p, q) implies q - p <= ans by
      {
        if q < end {
          assert(q - p  <= ans_old) by{
            assert(max_no_repeat(s@, end as int, ans_old as int));
            assert(0 <= p < q < end);
            assert(no_repeat(s@, p, q));
          }
          assert(q - p <= ans_old <= ans);
        }
        else {
          assert(q == end);
          if start == 0{}
          else {
            assert(start > 0);
            if p < start {
              if start_old == start {
                assert(! no_repeat(s@, p, end as int)) by {
                  assert(forall |j:int|
                    ((#[trigger] is_le_3(0, j, start_old - 1) && (start_old < end)) ==>
                      ! no_repeat(s@, j, end as int))
                  );
                  assert(start <= end);
                  assert(start_old < end);
                  assert(is_le_3(0, p, start - 1));
                  assert(is_le_3(0, p, start_old - 1));
                }
              }
              else {
                assert(start_old < start);
                if p < start_old {}
                else {
                  assert(p >= start_old);
                  assert(q - p == end - p);
                  assert(q - p <= end - start_old);
                  assert(ans >= ans_old);
                  assert(ans_old >= end - start_old);
                  assert(ans >= q - p);
                }
              }
            }
            else {}
          }
        }
      }
    }
  }
  ans
}


pub fn length_of_longest_substring(s: String) -> i32
  requires
    s@.len() < 5000000,
    s.is_ascii(),
{
  let s = s.as_str().as_bytes_vec();
  help(s)
}


// fn test(){
//   let s = String::from_str("123");
//   proof{
//       reveal_strlit("123");
//       reveal_strlit("12");
//   }
//   assert(s@[0] =~= "12"@[0])
// }





}//verus!

fn main(){}