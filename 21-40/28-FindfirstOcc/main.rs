use vstd::prelude::*;

verus!{

// pub open spec fn appear<T>(s:Seq<T>, needle:Seq<T>) -> bool{
//   &&& needle.len() <= s.len()
//   &&& exists |k:int| k <= s.len() - needle.len() &&
//     s.subrange(k, #[trigger]add(k, needle.len() as int)) =~= needle
// }

pub open spec fn appear<T>(s:Seq<T>, needle:Seq<T>) -> bool{
  &&& needle.len() <= s.len()
  &&& exists |k:int|  is_sub(s, needle, k as int)
}

#[verifier::inline]
pub open spec fn is_sub<T>(s:Seq<T>, needle:Seq<T>, pos:int) -> bool{
  &&& pos >= 0
  &&& s.len() >= needle.len() + pos
  &&& s.subrange(pos, #[trigger]add(pos as int, needle.len() as int)) =~= needle
}

pub open spec fn first_occ<T>(s:Seq<T>, needle:Seq<T>, pos:int) -> bool{
  &&& is_sub(s, needle, pos)
  &&& forall |i:int| 0 <= i < pos ==> !is_sub(s, needle, i)
}


pub fn aux(s:&Vec<u8>, s2:&Vec<u8>,  start:usize) -> (res:bool)
  requires
    s.len() >= s2.len() + start,
  ensures
    res <==> is_sub(s@, s2@, start as int),
{
  let len = s2.len();
  let end = len + start;

  for i in 0..len
    invariant
      0 <= i <= len,
      s2.len() == len,
      s.len() >= s2.len() + start,

      forall |j:int| 0 <= j < i ==> s2[j] == s[j + start],
  {
    if s2[i] != s[i + start]{
      return false
    }
  }
  // assert(forall |j:int| 0 <= j < len ==> s2[j] == s[j + start]);
  // assert(s@.subrange(start as int, start + len) =~= s2@);
  return true;
}





pub fn find_first_occ(s:Vec<u8>, needle:Vec<u8>) -> (res:i32)
  requires
    s.len() < 10000, needle.len() < 10000,

  ensures
    !appear(s@, needle@) <==> res == -1,

    appear(s@, needle@) ==> first_occ(s@, needle@, res as int),

{

  if s.len() < needle.len()
  {
    assert(!appear(s@, needle@));
    return -1;
  }

  for i in 0..s.len() - needle.len() + 1
    invariant
      s.len() < 10000, needle.len() < 10000,
      needle.len() <= s.len(),
      0 <= i <= s.len() - needle.len() + 1,
      forall |j:int| 0 <= j < i ==>
        !is_sub(s@, needle@, j),
  {
    if aux(&s, &needle, i){
      // assert(i <= s.len() - needle.len());
      // assert(appear(s@, needle@));
      // assert(s@.subrange(i as int, i + needle.len() as int) =~= needle@);
      return i as i32
    }
  }

  // assert(forall |j:int| 0 <= j <= s.len() - needle.len() ==>
  //       !( s@.subrange(j, #[trigger]add(j, needle.len() as int)) =~= needle@)
  // );
  // assert(!appear(s@, needle@));
  return -1;
}



}//verus!

fn main(){}