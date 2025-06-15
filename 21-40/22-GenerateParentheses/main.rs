use vstd::prelude::*;
// use vstd::math::min;


verus!{


//correct ?
pub open spec fn valid_index(s:Seq<char>, len:int, acc:int) -> bool
  recommends len <= s.len(), len >= 0,
  decreases len
{
  if len < 0 || acc < 0 {
    false
  }
  else if len == 0 {
    acc == 0
  }
  else {
    let c = s[len - 1];
    if c == '('{
      &&& valid_index(s, len - 1, acc - 1)
    }
    else if c == ')'{
      &&& valid_index(s, len - 1, acc + 1)
    }
    else {
      false
    }
  }
}

proof fn lemma_valid(s1:Seq<char>, s2:Seq<char>, x:char, len:int, acc:int)
  requires
    s1.len() >= len,
    valid_index(s1, len, acc),
    s2 =~= s1.push(x),
  ensures
    valid_index(s2, len, acc),
  decreases
    len,
{
  if len < 0 || acc < 0{}
  else if len == 0 {}
  else {
    let c= s1[len - 1];
    if c == '('{
      lemma_valid(s1, s2, x, len - 1, acc - 1)
    }
    else if c == ')'{
      lemma_valid(s1, s2, x, len - 1, acc + 1)
    }
    else {}
  }
}

proof fn lemma_valid_sub(s1:Seq<char>, s2:Seq<char>, index:int, len:int, acc:int)
  requires
    len >= 0,
    s1.len() >= len,
    s2.len() >= s1.len(),
    s1 =~= s2.subrange(0, len),
    len >= index,
    valid_index(s1, index, acc),
  ensures
    valid_index(s2, index, acc),
  decreases
    index,
{
  if index < 0 || acc < 0 {}
  else if index == 0 {}
  else {
    let c= s1[index - 1];
    if c == '('{
      lemma_valid_sub(s1, s2, index - 1, len, acc -1)
    }
    else if c == ')'{
      lemma_valid_sub(s1, s2, index - 1, len, acc +1)
    }
    else {}
  }
}

proof fn lemma_valid_uniq(s:Seq<char>, index:int, acc:int, acc2:int)
  requires
    s.len() >= index,
    valid_index(s, index, acc),
    valid_index(s, index, acc2),
  ensures
    acc == acc2
  decreases index,
{
  if index < 0 {}
  else if index == 0 {}
  else {
    let c= s[index - 1];
    if c == '('{
      lemma_valid_uniq(s, index - 1, acc - 1, acc2 - 1);
    }
    else if c == ')'{
      lemma_valid_uniq(s, index - 1, acc + 1, acc2 + 1);
    }
    else {}
  }
}

proof fn lemma_valid_pair(s:Seq<char>, index:int, acc:int)
  requires
    s.len() >= index,
    valid_index(s, index, acc),
  ensures
    (acc - index) % 2 == 0
  decreases index,
{
  if index < 0 {}
  else if index == 0 {}
  else {
    let c= s[index - 1];
    if c == '('{
      lemma_valid_pair(s, index - 1, acc - 1);
      assert((index - acc) % 2 == 0);
    }
    else if c == ')'{
      lemma_valid_pair(s, index - 1, acc + 1);
      assert((index - acc - 2) % 2 == 0);
    }
    else {}
  }
}


proof fn lemma_valid_ext(s:Seq<char>, index:int, sub_index:int, acc:int)
  requires
    s.len() >= index,
    index >= sub_index,
    sub_index >= 0,
    valid_index(s, index, acc),
  ensures
    exists |k:int| valid_index(s, sub_index, k)
  decreases index - sub_index,
{
  if sub_index == index{}
  else {
    if index < 0 || acc < 0 {}
    else if index == 0 {}
    else{
      let c= s[index - 1];
      if c == '('{
        lemma_valid_ext(s, index - 1, sub_index, acc - 1)
      }
      else if c == ')'{
        lemma_valid_ext(s, index - 1, sub_index, acc + 1)
      }
      else {}
    }
  }
}


pub open spec fn count_lpar(s:Seq<char>) -> nat
  decreases s
{
  if s.len() == 0 {0}
  else {
    if s.last() == '(' {
      1 + count_lpar(s.drop_last())
    }
    else {
      count_lpar(s.drop_last())
    }
  }
}

proof fn lemma_count_lpar_push(s:Seq<char>)
  ensures
    count_lpar(s.push('(')) == count_lpar(s) + 1,
    forall |x:char| x != '(' ==> #[trigger]count_lpar(s.push(x)) == count_lpar(s),
{
  let s1 = s.push('(');
  assert(s1.last() == '(');
  assert(s1.drop_last() =~= s);

  assert forall |x:char| x != '(' implies #[trigger]count_lpar(s.push(x)) == count_lpar(s) by
  {
    let s2 = s.push(x);
    assert(s2.last() == x);
    assert(s2.drop_last() =~= s);
  }

}

proof fn lemma_count_lpar_mono(s1:Seq<char>, s2:Seq<char>, len:int)
  requires s1 =~= s2.subrange(0, len), len == s1.len(), s1.len() <= s2.len()
  ensures count_lpar(s2) >= count_lpar(s1)
  // decreases len
{
  lemma_count_lpar_mono_aux(s1, s2.subrange(len, s2.len() as int), s2)
}

proof fn lemma_count_lpar_mono_aux(s1:Seq<char>, s2:Seq<char>, s3:Seq<char>)
  requires s3 =~= s1 + s2,
  ensures count_lpar(s3) == count_lpar(s1) + count_lpar(s2)
  decreases s2.len()
{
  if s2.len() == 0{}
  else if s2.len() == 1 {
    assert(s3.drop_last() =~= s1);
    assert(s3 =~= s1.push(s2[0]));
    lemma_count_lpar_push(s2);
    if s2[0] == '(' {
      assert(count_lpar(s2) == 1) by {reveal_with_fuel(count_lpar, 2)}
    }
    else {
      assert(count_lpar(s2) == 0) by {reveal_with_fuel(count_lpar, 2)}
    }
  }
  else{
    assert(s3 =~= s1 + s2.drop_last() + seq![s2.last()]);
    assert(seq![s2.last()].len() == 1);
    lemma_count_lpar_mono_aux(s1 + s2.drop_last(), seq![s2.last()], s3);
    lemma_count_lpar_mono_aux(s1, s2.drop_last(), s1 + s2.drop_last());
    lemma_count_lpar_mono_aux(s2.drop_last(), seq![s2.last()], s2);
  }
}


proof fn lemma_valid_count_lpar(s:Seq<char>, index:int, acc:int)
  requires
    s.len() >= index,
    valid_index(s, index, acc),
  ensures
    count_lpar(s.subrange(0, index)) == (index + acc) / 2
  decreases index,
{
  if index < 0 {}
  else if index == 0 {}
  else {
    let c= s[index - 1];
    if c == '('{
      lemma_valid_count_lpar(s, index - 1, acc - 1);
      assert(count_lpar(s.subrange(0, index - 1)) == (index + acc - 2) / 2);
      assert(s.subrange(0, index).last() == '(');
      assert(s.subrange(0, index).drop_last() =~= s.subrange(0, index - 1));
      assert(count_lpar(s.subrange(0, index)) == 1 + count_lpar(s.subrange(0, index - 1)));
    }
    else if c == ')'{
      lemma_valid_count_lpar(s, index - 1, acc + 1);
      assert(count_lpar(s.subrange(0, index - 1)) == (index + acc) / 2);
      assert(s.subrange(0, index).last() == ')');
      assert(s.subrange(0, index).drop_last() =~= s.subrange(0, index - 1));
      assert(count_lpar(s.subrange(0, index)) == count_lpar(s.subrange(0, index - 1)));
    }
    else {}
  }
}




// the main specification of valide parentheses
pub open spec fn valid_par(s:Seq<char>) -> bool{
  valid_index(s, s.len() as int, 0)
}





proof fn test(){
  let s = seq!['(', ')'];
  assert(valid_index(s, 0, 0));
  assert(valid_index(s, 1, 1)) by {reveal_with_fuel(valid_index, 2)}
  // assert(!valid_index(s, 2, 1)) by {reveal_with_fuel(valid_index, 3)}
  assert(valid_index(s, 2, 0)) by {reveal_with_fuel(valid_index, 3)}

  let ss = seq!['(', '(', ')'];
  assert(valid_index(ss, 3, 1)) by {reveal_with_fuel(valid_index, 5)}

  assert(!valid_par(ss)) by {reveal_with_fuel(valid_index, 5)}

  let ss2 = seq!['(', ')', '(', '(', ')', ')'];
  assert(valid_par(ss2)) by {reveal_with_fuel(valid_index, 7)}

  // assert(valid_index(seq![')'], 1, -1)) by {reveal_with_fuel(valid_index, 7)}


}



pub fn helper(tmp:Vec<char>, ans:&mut Vec<Vec<char>>, lp:usize, rp:usize, len:usize)
  requires
    len >= 1,
    0 <= rp <= lp <= len,
    tmp.len() == lp + rp,
    count_lpar(tmp@) == lp,
    valid_index(tmp@, lp + rp, lp - rp),

    forall |i:int| 0 <= i < old(ans).len() ==>
      #[trigger] valid_par(old(ans)@[i]@),
    forall |i:int| 0 <= i < old(ans).len() ==>
      #[trigger] old(ans)@[i].len() == 2 * len,

  ensures
    forall |i:int| 0 <= i < ans.len() ==>
      #[trigger] valid_par(ans@[i]@),

    forall |i:int| 0 <= i < ans.len() ==>
      #[trigger] ans@[i].len() == 2 * len,

    ans.len() >= old(ans).len(),
    old(ans)@ =~= ans@.subrange(0, old(ans).len() as int),

    forall |p:Vec<char>| tmp@ =~= p@.subrange(0, lp + rp) &&
      valid_par(p@) && p.len() == 2*len  ==> #[trigger]ans.deep_view().contains(p@),



  decreases len - lp, len - rp,
{
  // broadcast use lemma_count_lpar_push;

  if rp == len{
    ans.push(tmp);
    proof{
      assert forall |p:Vec<char>| tmp@ =~= p@.subrange(0, lp + rp) &&
        valid_par(p@) && p.len() == 2*len  implies #[trigger]ans.deep_view().contains(p@) by
      {
        assert(tmp@ =~= p@);
        assert(ans.deep_view()[ans@.len() - 1] =~= tmp@);
      }
    }
    return;
  }
  else if lp == rp {
    let mut str = tmp.clone();
    str.push('(');
    // assert(valid_index(str@, lp + rp + 1, lp + 1 - rp)) by {
      assert(valid_index(str@, lp + rp, lp - rp)) by {lemma_valid(tmp@, str@, '(', lp + rp, lp - rp)}
    // }
    assert(count_lpar(str@) == lp + 1) by {lemma_count_lpar_push(tmp@)}

    helper(str, ans, lp + 1, rp, len);

    proof{
      assert forall |p:Vec<char>| tmp@ =~= p@.subrange(0, lp + rp) &&
        valid_par(p@) && p.len() == 2*len  implies #[trigger]ans.deep_view().contains(p@) by
      {
        assert(valid_index(p@, lp + rp, 0)) by {
          lemma_valid_sub(tmp@, p@, lp + rp, lp + rp, 0)
        }

        assert(2 * len > lp + rp);

        assert(exists |k:int| #[trigger]valid_index(p@, lp + rp + 1, k)) by{
          lemma_valid_ext(p@, 2 * len, lp + rp + 1, 0)
        }
        let k = choose |k:int| #[trigger]valid_index(p@, lp + rp + 1, k);
        if p@[lp + rp] == '(' {
          assert(p@.subrange(0, lp + rp + 1) =~= str@);
        }
        else if p@[lp + rp] == ')'{
          assert(valid_index(p@, lp + rp, k + 1));
          assert(valid_index(tmp@, lp + rp, 0));
          assert(0 == k + 1) by{
            lemma_valid_uniq(p@, lp + rp, 0, k + 1)
          }
          assert(false)
        }
        else{
        }
      }
    }

    return;
  }
  else {
    assert(lp > rp);
    let mut str2 = tmp.clone();
    str2.push(')');

    assert(valid_index(str2@, lp + rp, lp - rp)) by {lemma_valid(tmp@, str2@, ')', lp + rp, lp - rp)}
    assert(count_lpar(str2@) == lp) by {lemma_count_lpar_push(tmp@)}

    helper(str2, ans, lp, rp+1, len);

    if lp == len {
      proof{
        assert forall |p:Vec<char>| tmp@ =~= p@.subrange(0, lp + rp) &&
          valid_par(p@) && p.len() == 2*len  implies #[trigger]ans.deep_view().contains(p@) by
        {
          assert(valid_index(p@, lp + rp, lp - rp)) by {
            lemma_valid_sub(tmp@, p@, lp + rp, lp + rp ,lp - rp)
          }
          assert(exists |k:int| #[trigger]valid_index(p@, lp + rp + 1, k)) by{
            lemma_valid_ext(p@, 2 * len, lp + rp + 1, 0)
          }
          let k = choose |k:int| #[trigger]valid_index(p@, lp + rp + 1, k);

          if p@[lp + rp] == '(' {
            let p1 = p@.subrange(0, 2*len);
            assert(count_lpar(p1) == len) by {
              lemma_valid_count_lpar(p@, 2 * len, 0);
            }
            assert(count_lpar(tmp@) == lp);
            assert(p1.subrange(0, lp + rp) =~= tmp@);
            assert(p1.subrange(0, lp + rp + 1) =~= tmp@.push('('));

            assert(count_lpar(p1.subrange(0, lp + rp + 1)) == len + 1) by{
              lemma_count_lpar_push(tmp@)
            }

            assert(count_lpar(p1) >= len + 1) by {
              lemma_count_lpar_mono(p1.subrange(0, lp + rp + 1), p1, lp + rp + 1)
            }
            assert(false)
          }
          else if p@[lp + rp] == ')'{
            assert(k + 1 == lp - rp) by{
              lemma_valid_uniq(p@, lp + rp, k + 1, lp - rp)
            }
            assert(p@.subrange(0, lp + rp + 1) =~= str2@);
          }
          else{}
        }
      }
      return;
    }

    else {
      let mut str = tmp.clone();
      str.push('(');

      assert(valid_index(str@, lp + rp, lp - rp)) by {lemma_valid(tmp@, str@, '(', lp + rp, lp - rp)}

      let ghost ans_prev = *ans;
      assert(count_lpar(str@) == lp + 1) by {lemma_count_lpar_push(tmp@)}

      helper(str, ans, lp + 1, rp, len);

      proof{
        assert forall |p:Vec<char>| tmp@ =~= p@.subrange(0, lp + rp) &&
          valid_par(p@) && p.len() == 2*len  implies #[trigger]ans.deep_view().contains(p@) by
        {
          assert(valid_index(p@, lp + rp, lp - rp)) by {
            lemma_valid_sub(tmp@, p@, lp + rp, lp + rp ,lp - rp)
          }
          assert(exists |k:int| #[trigger]valid_index(p@, lp + rp + 1, k)) by{
            lemma_valid_ext(p@, 2 * len, lp + rp + 1, 0)
          }
          let k = choose |k:int| #[trigger]valid_index(p@, lp + rp + 1, k);

          if p@[lp + rp] == '(' {
            assert(k - 1 == lp - rp) by{
              lemma_valid_uniq(p@, lp + rp, k - 1, lp - rp)
            }
            assert(p@.subrange(0, lp + rp + 1) =~= str@);
          }
          else if p@[lp + rp] == ')'{
            assert(k + 1 == lp - rp) by{
              lemma_valid_uniq(p@, lp + rp, k + 1, lp - rp)
            }
            assert(p@.subrange(0, lp + rp + 1) =~= str2@);
            assert(ans_prev.deep_view().contains(p@));
            let j = choose |j:int| ans_prev.deep_view()[j] == p@ && 0 <= j < ans_prev.len();
            assert(ans@[j] == ans_prev@[j]);
            assert(ans.deep_view()[j] == ans_prev.deep_view()[j]);
          }
          else{}
        }
      }


      return;
    }

    // let ghost str = tmp@.push(')');
  }
}



pub fn generate(n:usize) -> (ans:Vec<Vec<char>>)
  requires n >= 1,
  ensures
    forall |i:int| 0 <= i < ans.len() ==>
      #[trigger] valid_par(ans@[i]@),
    forall |i:int| 0 <= i < ans.len() ==>
      #[trigger] ans@[i].len() == 2 * n,

    forall |p:Vec<char>| valid_par(p@) && p.len() == 2*n ==>
      #[trigger]ans.deep_view().contains(p@),

{
  let mut ans = vec![];
  let tmp = vec![];
  helper(tmp, &mut ans, 0, 0, n);
  return ans;
}



}//verus!

fn main(){}