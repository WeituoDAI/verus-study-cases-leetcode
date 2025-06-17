use vstd::prelude::*;
use vstd::arithmetic::power2;
use power2::pow2;

verus!{



// pub open spec fn triangle(num_rows:nat) -> Seq<nat>
//   recommends num_rows > 0,
//   decreases num_rows
// {
//   if num_rows == 1 { seq![1] }
//   else {
//     let prev = triangle((num_rows - 1) as nat);
//     let

//   }
// }


proof fn lemma_pow2()
  ensures pow2(29) + pow2(29) <= i32::MAX
{
  power2::lemma2_to64()
}



#[verifier::loop_isolation(false)]
pub fn generate(num_rows: i32) -> (res:Vec<Vec<i32>>)
  requires 1 <= num_rows <= 30,
  ensures
    res.len() == num_rows,
    forall |k:int| 0 <= k < num_rows ==> #[trigger]res[k].len() == k + 1,
    forall |k:int| 0 <= k < num_rows ==> #[trigger] res[k][0] == 1,
    forall |k:int| 0 <= k < num_rows ==> #[trigger] res[k][k] == 1,
    forall |k:int, m:int| (1 <= k < num_rows && 1 <= m < k) ==>
      #[trigger] res[k][m] == res[k-1][m-1] + res[k-1][m],

{
  let mut res : Vec<Vec<i32>> = Vec::with_capacity(num_rows as usize);
  let mut vec_0 = Vec::new();
  vec_0.push(1);
  res.push(vec_0);

  proof{ power2::lemma2_to64(); }

  for i in 1..num_rows
    invariant
      // num_rows >= 1,
      res.len() == i,
      forall |k:int| 0 <= k < i ==> #[trigger]res[k].len() == k + 1,

      forall |k:int, m:int| (0 <= k < i && 0 <= m <= k) ==> 0 <= #[trigger] res[k][m] <= pow2(k as nat) ,

      forall |k:int, m:int| (1 <= k < i && 1 <= m < k) ==> #[trigger] res[k][m] == res[k-1][m-1] + res[k-1][m],

      forall |k:int| 0 <= k < i ==> #[trigger] res[k][0] == 1,
      forall |k:int| 0 <= k < i ==> #[trigger] res[k][k] == 1,
  {

    let mut new_v = Vec::with_capacity((i + 1) as usize);
    new_v.push(1i32);

    // assert(new_v[0] == pow2(0)) by { }
    // assert(new_v[0] <= pow2(i as nat));

    for j in 1..i
      invariant
        // num_rows >= 1,
        // 1 <= i < num_rows,
        // res.len() == i,
        // forall |k:int| 0 <= k < i ==> #[trigger]res[k].len() == k + 1,
        new_v.len() == j,

        forall |k:int, m:int| (0 <= k < i && 0 <= m <= k) ==> 0 <= #[trigger] res[k][m] <= pow2(k as nat) ,
        forall |m:int| 0 <= m < j ==> 0 <= #[trigger] new_v[m] <= pow2(i as nat) ,

        forall |m:int| 1 <= m < j ==> 0 <= #[trigger] new_v[m] == res[i-1][m-1] + res[i-1][m] ,

        new_v[0] == 1,
    {
      assert(res[(i-1)].len() == i);
      assert(res[(i-1)][j as int] <= pow2((i-1) as nat));
      assert(res[(i-1)][(j-1)] <= pow2((i-1) as nat));
      assert(res[(i-1)][j as int] + res[(i-1)][(j-1)] <= pow2(i as nat));
      assert(res[(i-1)][j as int] + res[(i-1)][(j-1)] <= pow2(num_rows as nat));
      assert(pow2(num_rows as nat) <= i32::MAX);

      new_v.push(
        res[(i-1) as usize][j as usize] + res[(i-1) as usize][(j-1) as usize]
      );
    }
    new_v.push(1i32);
    // assert(new_v[i as int] == 1);
    // assert(
    //   forall |m:int| 0 <= m < i + 1 ==> 0 <= #[trigger] new_v[m] <= pow2(i as nat)
    // );
    // assert(
    //   forall |m:int| 1 <= m < i ==> 0 <= #[trigger] new_v[m] == res[i-1][m-1] + res[i-1][m]
    // );
    res.push(new_v)
  }

  return res;
}



}//verus!

fn main(){}