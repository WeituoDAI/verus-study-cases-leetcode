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

  pub open spec fn sym(&self) -> Self
    decreases self,
  {
    let val = self.val;
    let left =
      match self.right {
        None => None,
        Some(t) => Some(Box::new(t.sym()))
      };
    let right = match self.left {
        None => None,
        Some(t) => Some(Box::new(t.sym()))
      };
    Self{
      val,
      left,
      right,
    }
  }
}


pub fn is_sym_aux(p:Option<Box<TreeNode>>, q:Option<Box<TreeNode>>) -> (res:bool)
  ensures
    match (p, q) {
      | (None, None) => res,
      | (None, _) | (_, None) => !res,
      | (Some(p), Some(q)) =>
        (p.sym() =~= *q <==> res)
        && (q.sym() =~= *p <==> res)
    },
  decreases p, q
{
  if p.is_none() && q.is_none() {true}
  else if p.is_none() {false}
  else if q.is_none() {false}
  else {
    let tp = p.unwrap();
    let tq = q.unwrap();
    if tp.val != tq.val {false}
    else {
      is_sym_aux(tp.left, tq.right) && is_sym_aux(tp.right, tq.left)
    }
  }
}


pub fn is_sym(p:Option<Box<TreeNode>>) -> (res:bool)
  ensures
    match p {
      None => res,
      Some(p) => p.sym() =~= *p <==> res
    }
{
  match p {
    None => true,
    Some(p) => is_sym_aux(p.left, p.right),
  }
}




}//verus!

fn main(){}