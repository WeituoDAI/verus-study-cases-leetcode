use vstd::prelude::*;

verus!{

#[verifier::external_body]
pub fn matrix_update(matrix:&mut Vec<Vec<i32>>, i:usize, j:usize, val:i32)
  requires
    0 <= i < old(matrix)@.len(),
    0 <= j < old(matrix)@[j as int]@.len(),
  ensures
    matrix@.len() == old(matrix)@.len(),
    forall |k:int| 0 <= k < matrix@.len() && k != i ==> #[trigger]matrix@[k]@ =~= old(matrix)@[k]@,
    matrix@[i as int]@ =~= old(matrix)@[i as int]@.update(j as int, val),
{
  matrix[i][j] = val;
}


pub open spec fn precondition(matrix:Vec<Vec<i32>>) -> bool{
  &&& 1 <= matrix@.len() <= 20
  &&& forall |i:int| 0 <= i < matrix@.len() ==> #[trigger]matrix@[i]@.len() == matrix@.len()
  &&& forall |i:int, j:int| 0 <= i < matrix@.len() && 0 <= j < matrix@.len() ==> -1000 <= #[trigger]matrix@[i]@[j] <= 1000
}


pub open spec fn is_rotate(m1:Vec<Vec<i32>>, m2:Vec<Vec<i32>>) -> bool{
  &&& precondition(m1)//for ease
  &&& precondition(m2)//for ease
  &&& m1@.len() == m2@.len()
  &&& forall |i:int, j:int| 0 <= i < m1@.len() && 0 <= j < m1@.len() ==> m2@[i]@[j] == m1@[m1@.len() - j - 1]@[i]
}


#[verifier::spinoff_prover]
pub fn rotate(matrix: &mut Vec<Vec<i32>>)
  requires
    precondition(*old(matrix)),
  ensures
    is_rotate(*old(matrix), *matrix)

{
  let ghost matrix_old = *matrix;
  let size = matrix.len();

  for a in 0..size/2
    invariant
      precondition(*matrix),
      precondition(matrix_old),

      size == matrix_old.len(),
      size == matrix.len(),

      forall |p:int, q:int|
        (0 <= p < a || size - a <= p < size || 0 <= q < a || size - a <= q < size)
        && (0 <= p < size) && (0 <= q < size)
        ==>
        #[trigger] matrix@[p]@[q] == matrix_old@[size - q - 1]@[p],

      forall |p:int, q:int| a <= p < size - a && a <= q < size - a ==>
        #[trigger]matrix@[p]@[q] == matrix_old@[p]@[q],
  {
    for i in a..size - a - 1
      invariant
        precondition(*matrix),
        precondition(matrix_old),
        size == matrix_old.len(),
        size == matrix.len(),
        0 <= a < size/2,

        forall |p:int, q:int|
          (0 <= p < a || size - a <= p < size || 0 <= q < a || size - a <= q < size)
          && (0 <= p < size) && (0 <= q < size)
          ==>
          #[trigger] matrix@[p]@[q] == matrix_old@[size - q - 1]@[p],

        forall |q:int| a <= q < i ==> #[trigger]matrix@[a as int]@[q] == matrix_old@[size - q - 1]@[a as int],
        forall |q:int| a <= q < i ==> #[trigger]matrix@[size - 1 - q]@[a as int] == matrix_old@[size - a - 1]@[size - q - 1],
        forall |q:int| a <= q < i ==> #[trigger]matrix@[size - a - 1]@[size - q - 1] == matrix_old@[q]@[size - a - 1],
        forall |q:int| a <= q < i ==> #[trigger]matrix@[q]@[size - a - 1] == matrix_old@[a as int]@[q],

        forall |q:int| i <= q < size - a - 1 ==> #[trigger]matrix@[a as int]@[q] == matrix_old@[a as int]@[q],
        forall |q:int| i <= q < size - a - 1==> #[trigger]matrix@[size - 1 - q]@[a as int] == matrix_old@[size - 1 - q]@[a as int],
        forall |q:int| i <= q < size - a - 1==> #[trigger]matrix@[size - a - 1]@[size - q - 1] == matrix_old@[size - a - 1]@[size - q - 1],
        forall |q:int| i <= q < size - a - 1 ==> #[trigger]matrix@[q]@[size - a - 1] == matrix_old@[q]@[size - a - 1],

        forall |p:int, q:int| a < p < size - a - 1 && a < q < size - a - 1 ==>
          #[trigger]matrix@[p]@[q] == matrix_old@[p]@[q],

    {
      let tmp = matrix[a][i];

      let v1 = matrix[size - 1 - i][a];
      matrix_update(matrix, a, i, v1);
      // matrix[a][i] = matrix[size - 1 - i][a];
      let v2 = matrix[size - 1 - a][size-1-i];
      matrix_update(matrix, size - 1 - i, a, v2);
      // matrix[size-1-i][a] = matrix[size - 1 - a][size-1-i];
      let v3 = matrix[i][size-1-a];
      matrix_update(matrix, size - 1 - a, size - 1 - i, v3);
      // matrix[size-1-a][size-1-i] = matrix[i][size-1-a];
      matrix_update(matrix, i, size - 1 - a, tmp);
      // matrix[i][size-1-a] = tmp;

      // proof{admit()}
    }
    proof{
      assert(forall |q:int| a <= q < size - a - 1 ==> #[trigger]matrix@[a as int]@[q] == matrix_old@[size - q - 1]@[a as int]);
      assert(forall |q:int| a <= q < size - a - 1 ==> #[trigger]matrix@[size - 1 - q]@[a as int] == matrix_old@[size - a - 1]@[size - q - 1]);
      assert(forall |q:int| a <= q < size - a - 1 ==> matrix@[size - a - 1]@[size - q - 1] == #[trigger]matrix_old@[q]@[size - a - 1]);
      assert(forall |q:int| a <= q < size - a - 1 ==> #[trigger]matrix@[q]@[size - a - 1] == matrix_old@[a as int]@[q]);

      assert forall |p:int, q:int| (0 <= p <= a || size - a - 1 <= p < size || 0 <= q <= a || size - a - 1 <= q < size)
          && (0 <= p < size) && (0 <= q < size) implies
        #[trigger] matrix@[p]@[q] == matrix_old@[size - q - 1]@[p] by
      {
        if 0 <= p < a {}
        else if size - a <= p < size { }
        else if 0 <= q < a {}
        else if size - a <= q < size {}
        else if p == a{}
        else if p == size - a - 1 {
          assert(a <= q <= size - a - 1);
          assert(a <= size - q - 1 <= size - a - 1);
          if size - q - 1 < size - a - 1{
            //to use the trigger
            assert(matrix@[size - a - 1]@[size - (size - q - 1) - 1] == matrix_old@[size - q - 1][size - a - 1]);
          }
          else {
            assert(q == a);
            //to use the trigger
            assert(matrix@[size - 1 - q]@[a as int] == matrix_old@[size - a - 1][size - q - 1]);
          }
        }
        else if q == a {
          assert(a <= size - 1 - p < size - a -1);
          //to use the trigger
          assert(matrix@[size - 1 - (size - 1 - p)]@[a as int] == matrix_old@[size - a - 1]@[p]);
        }
        else if q == size - a - 1 {
          assert(a <= size - 1 - p < size - a -1);
          //to use the trigger
          assert(matrix@[size - 1 - (size - 1 - p)]@[size - a - 1] == matrix_old@[a as int]@[p]);
        }
      }

    }
  }

  assert(forall |p:int, q:int| (0 <= p < size) && (0 <= q < size) ==>
    #[trigger] matrix@[p]@[q] == matrix_old@[size - q - 1]@[p]);


}


}//verus!

fn main(){}