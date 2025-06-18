use vstd::prelude::*;


verus!{

#[verifier::ext_equal]
pub struct TreeNode{
  pub val : i32,
  pub left : Option<Box<TreeNode>>,
  pub right : Option<Box<TreeNode>>,
}



impl TreeNode{


  pub open spec fn new_spec(val:i32) -> Self{
    TreeNode{
      val,
      left:None,
      right:None,
    }
  }

  pub fn new(val:i32) -> (res:Self)
    ensures res =~= Self::new_spec(val),
  {
    TreeNode{
      val,
      left:None,
      right:None,
    }
  }
}


fn test(){
  let n1 = TreeNode::new(5);
  let n2 = TreeNode::new(5);

  let n3 = TreeNode{val:9, left:Some(Box::new(n1)), right:None};
  let n4 = TreeNode{val:9, left:Some(Box::new(n2)), right:None};

  assert(n3 =~= n4);

}


pub fn is_same_tree(p: Option<Box<TreeNode>>, q: Option<Box<TreeNode>>) -> (res:bool)
  ensures
    p =~= q <==> res,
  decreases p, q,
{
  if p.is_none() && q.is_none() {true}
  else if p.is_none() {false}
  else if q.is_none() {false}
  else {
    let tp = p.unwrap();
    let tq = q.unwrap();
    if tp.val != tq.val {false}
    else {
      is_same_tree(tp.left, tq.left) && is_same_tree(tp.right, tq.right)
    }
  }
}



}//verus!

fn main(){}