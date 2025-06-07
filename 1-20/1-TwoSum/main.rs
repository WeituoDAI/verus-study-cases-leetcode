use vstd::prelude::*;


verus!{


spec fn aux(p:int, q:int, k:int, len:int) -> bool{
  0 <= p < k <= q < len
}

// brute force

fn find_sum_2(l:Vec<i32>, sum:i32) -> (res:Option<(usize, usize)>)
  requires
    - 10_0000_0000 <= sum <= 10_0000_0000,
    forall |i:int| 0 <= i < l.len() ==> - 10_0000_0000 <=#[trigger]l[i] <= 10_0000_0000,
  ensures
    (forall |i:int, j:int| 0 <= i < j < l.len() ==> l[i] + l[j] != sum)
      <==> res == None::<(usize, usize)>,

    !(forall |i:int, j:int| 0 <= i < j < l.len() ==> l[i] + l[j] != sum)
      <==> res.is_Some() && l[res.unwrap().0 as int] + l[res.unwrap().1 as int] == sum,
{
  let len = l.len();
  let mut i = 0;

  while i < len
    invariant
      len == l.len(),
      0 <= i <= len,
      - 10_0000_0000 <= sum <= 10_0000_0000,
      forall |i:int| 0 <= i < l.len() ==> - 10_0000_0000 <= #[trigger]l[i] <= 10_0000_0000,
      forall |p:int, q:int| 0 <= p < i <= q < len ==>
        l[p] + l[q] != sum,
      forall |p:int, k:int, q:int| 0 <= k <= i && #[trigger] aux(p,q,k,len as int) ==>
        l[p] + l[q] != sum,
    decreases
      len - i
  {
    let mut j = i + 1;

    while j < len
      invariant
        len == l.len(),
        0 <= i < j <= len,
        - 10_0000_0000 <= sum <= 10_0000_0000,
        forall |i:int| 0 <= i < l.len() ==> - 10_0000_0000 <= #[trigger]l[i] <= 10_0000_0000,

        forall |q:int| i < q < j ==> l[i as int] + l[q] != sum,

      decreases len - j
    {
      if(l[i] + l[j] == sum){
        // assert(! (forall |i:int, j:int| 0 <= i < j < l.len() ==> l[i] + l[j] != sum));
        return Some((i, j))
      }
      j = j + 1;
    }

    i = i + 1;
  }

  assert forall |p:int, q:int| 0 <= p < q < len implies
    l[p] + l[q] != sum by
  {
    assert(aux(p,q,q,len as int)); //problem of trigger
  }
  None
}


// method 2
use std::collections::HashMap;

fn find_sum_3(l:Vec<i32>, sum:i32) -> (res:Option<(usize, usize)>)
  requires
    - 10_0000_0000 <= sum <= 10_0000_0000,
    forall |i:int| 0 <= i < l.len() ==> - 10_0000_0000 <=#[trigger]l[i] <= 10_0000_0000,
  ensures
    (forall |i:int, j:int| 0 <= i < j < l.len() ==> l[i] + l[j] != sum)
      <==> res == None::<(usize, usize)>,

    !(forall |i:int, j:int| 0 <= i < j < l.len() ==> l[i] + l[j] != sum)
      <==> res.is_Some() && l[res.unwrap().0 as int] + l[res.unwrap().1 as int] == sum,
{
  broadcast use vstd::std_specs::hash::group_hash_axioms;
  let mut map : HashMap<i32, usize> = HashMap::new();
  let mut i = 0;
  let len = l.len();
  while i < len
    invariant
      len == l.len(),
      0 <= i <= len,

      - 10_0000_0000 <= sum <= 10_0000_0000,
      forall |i:int| 0 <= i < l.len() ==> - 10_0000_0000 <=#[trigger]l[i] <= 10_0000_0000,

      forall |k:i32| #[trigger] map@.contains_key(k) ==>
          0 <= map@[k] < i &&
          l[map@[k] as int] + k == sum,

      forall |j:int| 0 <= j < i ==>
          map@.contains_key((sum - l[j]) as i32),

      forall |j:int| 0 <= j < i ==>
          0 <= map@[(sum-#[trigger] l[j]) as i32] < i,
          // map@[(sum-l[j]) as usize] == j   // error ! may repeat number

      forall |j:int| 0 <= j < i-1 ==>
          #[trigger] l[j] + l[i-1] != sum,

      forall |j:int, p:int| 0 <= j < p < i ==>
          l[j] + l[p] != sum,

    decreases
      len - i
  {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    let v = l[i];
    let value = map.get(&v);
    match value {
      Some(k) => {
        return Some((i, *k))
      },
      None => {
        map.insert(sum - v, i);
        // assert(map@[(sum - v) as usize] == i);
        i = i + 1;
      }
    }
  }
  // assert(
  //         forall |j:int, p:int| 0 <= j < p < len ==>
  //             l[j] + l[p] != sum
  // );
  None
}

fn main(){}

}//veurs!