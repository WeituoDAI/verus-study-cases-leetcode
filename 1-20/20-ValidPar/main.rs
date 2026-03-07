
use vstd::prelude::*;


verus!{




#[derive(Structural, PartialEq, Eq, Copy, Clone)]
pub enum Par{
    La, Ra,
    Lb, Rb,
    Lc, Rc,
}
pub use Par::{La, Ra, Lb, Rb, Lc, Rc};


/// main function
fn valid_par(v:Vec<Par>) -> (res:bool)
    // requires v.len() < 10000,
    ensures
        res == valid_par_spec(v@),
{
    let mut stack = Vec::new();
    let len = v.len();
    let mut i = 0;

    let ghost s : Seq<Seq<Par>> = seq![seq![]];
    proof{
        stack_spec_eqv_rec_spec(v@)
    }

    while i < len
        invariant
            0 <= i <= len,
            len == v.len(),

            s[0] == Seq::<Par>::empty(),
            s.len() == i + 1,

            forall |j:int| 0 <= j < i ==> aux(v[j], s[j], s[j+1]),

            s.last() == stack@,

            // stack.len()

        decreases len - i
    {
        let slen = stack.len();
        proof{
            if stack_spec_0(v@) {
                let s2 = choose |s2:Seq<Seq<Par>>| stack_spec(v@, s2);
                assert(stack_spec(v@, s2));
                stack_spec_unique(v@, s, s2, i as int);
            }
            stack_spec_eqv_rec_spec(v@)
        }

        match v[i] {
            La | Lb | Lc => {
                stack.push(v[i]);
            },
            Ra => {
                if slen == 0 {
                    // proof{
                    //     assert(!stack_spec_0(v@)) by {
                    //         if stack_spec_0(v@) {
                    //             let s2 = choose |s2:Seq<Seq<Par>>| stack_spec(v@, s2);
                    //             assert(stack_spec(v@, s2));
                    //             stack_spec_unique(v@, s, s2, i as int);
                    //         }
                    //     }
                    // }
                    return false;
                }
                else if stack.pop().unwrap() != La { return false; }
            },
            Rb => {
                if slen == 0 { return false; }
                else if stack.pop().unwrap() != Lb { return false; }
            },
            Rc => {
                if slen == 0 { return false; }
                else if stack.pop().unwrap() != Lc { return false; }
            },
        }

        proof{
            s = s.push(stack@);
        }

        i = i + 1;
    }

    proof{
        assert(s.first() == Seq::<Par>::empty());
        assert(forall |j:int| 0 <= j < v.len() ==> aux(v[j], s[j], s[j+1]));
        assert(s.len() == v.len() + 1);
        assert(s.last() == stack@);
        assert(stack@.len() == 0 ==> s.last() == Seq::<Par>::empty());
        assert(stack@.len() == 0 ==> stack_spec(v@, s));

        assert(stack@.len()!=0 ==> !stack_spec_0(v@)) by {
            if stack_spec_0(v@) {
                let s2 = choose |s2:Seq<Seq<Par>>| stack_spec(v@, s2);
                assert(stack_spec(v@, s2));
                stack_spec_unique(v@, s, s2, len as int);
                // assert(s.last() == s2.last());
                // assert(stack@ == s.last());
            }
        }
    }

    return stack.len() == 0;
}


////////////////
spec fn aux(e:Par, s1:Seq<Par>, s2:Seq<Par>) -> bool{
    match e {
        La => { s2 == s1.push(La) },
        Lb => { s2 == s1.push(Lb) },
        Lc => { s2 == s1.push(Lc) },
        Ra => { s2 == s1.drop_last() && s1.last() == La && s1.len() > 0 },
        Rb => { s2 == s1.drop_last() && s1.last() == Lb && s1.len() > 0 },
        Rc => { s2 == s1.drop_last() && s1.last() == Lc && s1.len() > 0 },
    }
}

spec fn stack_spec(v:Seq<Par>, s:Seq<Seq<Par>>) -> bool{
    &&& s.len() == v.len() + 1 //1
    &&& s[0] == Seq::<Par>::empty() //2
    &&& s.last() == Seq::<Par>::empty() //3
    &&& forall |i:int| 0 <= i < v.len() ==> aux(v[i], s[i], s[i+1]) //4
}

spec fn rec_spec(v:Seq<Par>) -> bool
    decreases v.len(),
{
    if v.len() == 0 { true }
    else if v.len() == 1 { false }
    else {
        ||| v[0] == La && v.last() == Ra && rec_spec(v.subrange(1, v.len() - 1))
        ||| v[0] == Lb && v.last() == Rb && rec_spec(v.subrange(1, v.len() - 1))
        ||| v[0] == Lc && v.last() == Rc && rec_spec(v.subrange(1, v.len() - 1))
        ||| exists |i:int| #![all_triggers] 0 < i < v.len() &&
                rec_spec(v.subrange(0, i)) && rec_spec(v.subrange(i, v.len() as int))
    }
}


spec fn stack_spec_0(v:Seq<Par>) -> bool{
    exists |s:Seq<Seq<Par>>| stack_spec(v, s)
}

// main proof
proof fn stack_spec_eqv_rec_spec(v:Seq<Par>)
    ensures
        rec_spec(v) <==> stack_spec_0(v)
{
    if rec_spec(v) {
        rec_to_stack(v)
    }
    if stack_spec_0(v) {
        let s = choose |s:Seq<Seq<Par>>| stack_spec(v, s);
        stack_to_rec(v, s)
    }
}


proof fn stack_spec_unique(v:Seq<Par>, s1:Seq<Seq<Par>>, s2:Seq<Seq<Par>>, j:int)
    requires
        0 <= j <= v.len(),
        s1.first() == Seq::<Par>::empty(),
        s2.first() == Seq::<Par>::empty(),
        forall |i:int| 0 <= i < j ==> aux(v[i], s1[i], s1[i+1]),
        forall |i:int| 0 <= i < j ==> aux(v[i], s2[i], s2[i+1]),
    ensures
        forall |i:int| 0 <= i <= j ==> s1[i] == s2[i],
    decreases j
{
    if j == 0 {}
    else {
        stack_spec_unique(v, s1, s2, j-1);
        assert(s1[j] == s2[j]) by {
            assert(aux(v[j-1], s1[j-1], s1[j]));
            assert(aux(v[j-1], s2[j-1], s2[j]));
            assert(s1[j-1] == s2[j-1])
        }
    }
}


proof fn rec_to_stack(v:Seq<Par>)
    requires
        rec_spec(v),
    ensures
        stack_spec_0(v)
    decreases v.len(),
{
    if v.len() == 0 {
        let s = seq![Seq::<Par>::empty()];
        assert(stack_spec(v, s))
    }
    else if v.len() == 1 {}
    else if(
        (v[0] == La && v.last() == Ra && rec_spec(v.subrange(1, v.len() - 1)))
        || (v[0] == Lb && v.last() == Rb && rec_spec(v.subrange(1, v.len() - 1)))
        || (v[0] == Lc && v.last() == Rc && rec_spec(v.subrange(1, v.len() - 1)))
    ){
        let v0 = v.subrange(1, v.len() - 1);
        assert(stack_spec_0(v0)) by { rec_to_stack(v0) }
        let s0 = choose |s0:Seq<Seq<Par>>| stack_spec(v0, s0);
        assert(stack_spec(v0, s0));

        let s1 = s0.map(|i:int, a:Seq<Par>| a.insert(0, v[0]));
        let s = s1.insert(0, Seq::<Par>::empty()).push(Seq::<Par>::empty());

        assert(s.len() == v.len() + 1);
        assert(s.first() == Seq::<Par>::empty());
        assert(s.last() == Seq::<Par>::empty());
        assert forall |i:int| 0 <= i < v.len() implies aux(v[i], s[i], s[i+1]) by {
            if i == 0 {
                assert(s[0] == Seq::<Par>::empty());
                assert(s[1] == seq![v[0]]);
            }
            else if i == v.len() - 1 {
                assert(s[i+1] == Seq::<Par>::empty());
                assert(s0[i-1] == Seq::<Par>::empty());
                assert(s[i] == seq![v[0]]);
                assert(seq![v[0]].drop_last() == Seq::<Par>::empty())
            }
            else {
                assert(aux(v0[i-1], s0[i-1], s0[i]));
                assert(v0[i-1] == v[i]);

                assert(s[i] == s0[i-1].insert(0, v[0]));
                assert(s[i+1] == s0[i].insert(0, v[0]));

                assert(s0[i-1].insert(0, v[0]).push(v[i]) == s0[i-1].push(v[i]).insert(0, v[0]));
                assert(s0[i-1].len() > 0 ==> s0[i-1].insert(0, v[0]).drop_last() == s0[i-1].drop_last().insert(0, v[0]));
            }
        }

        assert(stack_spec(v, s));
    }
    else {
        let i = choose |i:int| #![all_triggers] 0 < i < v.len() &&
            rec_spec(v.subrange(0, i)) && rec_spec(v.subrange(i, v.len() as int));

        let v1 = v.subrange(0, i);
        let v2 = v.subrange(i, v.len() as int);
        assert(rec_spec(v1));
        assert(rec_spec(v2));

        assert(stack_spec_0(v1)) by { rec_to_stack(v1) }
        assert(stack_spec_0(v2)) by { rec_to_stack(v2) }

        let s1 = choose |s1:Seq<Seq<Par>>| stack_spec(v1, s1);
        let s2 = choose |s2:Seq<Seq<Par>>| stack_spec(v2, s2);
        assert(stack_spec(v1, s1));
        assert(stack_spec(v2, s2));

        let s = s1.drop_last() + s2;
        assert(s.len() == v.len() + 1);
        assert(s[0] == Seq::<Par>::empty());
        assert(s.last() == Seq::<Par>::empty());

        assert forall |i:int| 0 <= i < v.len() implies aux(v[i], s[i], s[i+1]) by {
            if 0 <= i < v1.len() - 1 {
                assert(aux(v1[i], s1[i], s1[i+1]));
            }
            else if v1.len() <= i < v.len() {
                assert(v[i] == v2[i - v1.len()]);
                assert(s[i] == s2[i - v1.len()]);
                assert(s[i+1] == s2[i - v1.len() + 1]);
                assert(aux(v2[i - v1.len()], s2[i - v1.len()], s2[i - v1.len() + 1]))
            }
            else {
                assert(i == v1.len() - 1);
                assert(s2.first() == s1.last());
                assert(s[i+1] == s2[0]);
            }
        }
        assert(stack_spec(v, s))
    }
}


proof fn stack_to_rec(v:Seq<Par>, s:Seq<Seq<Par>>)
    requires
        stack_spec(v, s)
    ensures
        rec_spec(v)
    decreases
        v.len()
{
    if v.len() == 0 {}
    else if v.len() == 1 {
        assert(aux(v[0], s[0], s[1]));
    }
    else if exists |k:int| 0 < k < s.len() - 1 && s[k] == Seq::<Par>::empty() {
        let k = choose |k:int| 0 < k < s.len() - 1 && s[k] == Seq::<Par>::empty();

        assert(s[k] == Seq::<Par>::empty());

        let v_1 = v.subrange(0, k);
        let v_2 = v.subrange(k, v.len() as int);
        let s_1 = s.subrange(0, k + 1);
        let s_2 = s.subrange(k, s.len() as int); // start at empty

        assert(stack_spec(v_1, s_1)) by {
            assert(forall|i:int| 0 <= i < v_1.len() ==> v_1[i] == v[i]);
            assert(forall|i:int| 0 <= i < s_1.len() ==> s_1[i] == s[i]);
            assert(forall|i:int| 0 <= i < v_1.len() ==> aux(v[i], s[i], s[i+1]));
        }
        assert(stack_spec(v_2, s_2)) by {
            assert(forall|i:int| 0 <= i < v_2.len() ==> v_2[i] == v[i + k]);
            assert(forall|i:int| 0 <= i < s_2.len() ==> s_2[i] == s[i + k]);
            assert(forall|i:int| v_1.len() <= i < v.len() ==> aux(v[i], s[i], s[i+1]));
            assert(forall|i:int| 0 <= i < v_2.len() ==> #[trigger]aux(v[i+k], s[i+k], s[i+k+1]));
        }
        assert(rec_spec(v)) by {
            assert(rec_spec(v_1)) by { stack_to_rec(v_1, s_1) }
            assert(rec_spec(v_2)) by { stack_to_rec(v_2, s_2) }
        }
    }
    else {
        assert(forall |k:int| 0 < k < s.len() - 1 ==> s[k] != Seq::<Par>::empty());

        let v0 = v.subrange(1, v.len() - 1);
        let s0 = s.subrange(1, s.len() - 1).map(
            |i:int, a:Seq<Par>| a.drop_first()
        );

        assert(s0.len() == s.len() - 2);
        assert(forall |i:int| 0 <= i < s0.len() ==> s0[i] == s[i+1].drop_first());
        lem1(v, s, v0, s0);
        assert(rec_spec(v0)) by {
            stack_to_rec(v0, s0)
        }

    }
}


proof fn lem0(v:Seq<Par>, s:Seq<Seq<Par>>, bound:int)
    requires
        // stack_spec(v, s),
        s.len() == v.len() + 1,
        s[0] == Seq::<Par>::empty(),
        0 <= bound <= v.len(),
        // s.last() == Seq::<Par>::empty()
        forall |i:int| 0 <= i < bound ==> aux(v[i], s[i], s[i+1]),

        v.len() > 1,
        forall |i:int| 0 < i < bound ==> s[i] != Seq::<Par>::empty(),
    ensures
        forall |i:int| 0 < i < bound ==> #[trigger]s[i].len() > 0 && s[i][0] == v[0]
    decreases
        bound,
{
    assert forall |i:int| 0 < i < bound implies #[trigger]s[i].len() > 0 && s[i][0] == v[0] by {
        if s[i].len() == 0 {
            assert(s[i] == Seq::<Par>::empty());
        }
        assert(s[i][0] == v[0]) by {
            if bound <= 2 {}
            else {
                assert(bound >= 3);
                if i < bound - 1 {
                    lem0(v, s, bound - 1);
                }
                else {
                    lem0(v, s, bound - 1);
                    assert(i == bound - 1);
                    assert(0 < i - 1 < bound - 1);
                    assert(s[i-1].len() > 0);
                    assert(s[i-1][0] == v[0]);
                    assert(aux(v[i-1], s[i-1], s[i]));
                    assert(aux(v[i], s[i], s[i+1]));
                    assert(s[i] != Seq::<Par>::empty());
                }
            }
        }
    }
}

proof fn lem1(v:Seq<Par>, s:Seq<Seq<Par>>, v0:Seq<Par>, s0:Seq<Seq<Par>>)
    requires
        stack_spec(v, s),
        v.len() > 1,
        forall |i:int| 0 < i < s.len() - 1 ==> s[i] != Seq::<Par>::empty(),

        v0 == v.subrange(1, v.len() - 1),
        s0.len() == s.len() - 2,
        forall |i:int| 0 <= i < s0.len() ==> s0[i] == s[i+1].drop_first(),

    ensures
        stack_spec(v0, s0),
        v[0] == La <==> v.last() == Ra,
        v[0] == Lb <==> v.last() == Rb,
        v[0] == Lc <==> v.last() == Rc,
{
    if v.len() == 2 {
        assert(s.len() == 3);
        assert(s0.len() == 1);

        // v[0], v[1]
        assert(s[0].len() == 0);
        assert(s[1] == seq![v[0]]);
        assert(s[2].len() == 0);

        assert(s0[0] == s[1].drop_first());
        assert(s0[0] == Seq::<Par>::empty());
    }
    else {
        assert(s0.len() == v0.len() + 1); //1

        assert(s0[0] == s[1].drop_first());
        assert(aux(v[0], s[0], s[1]));
        assert(s[1].len() == 1);
        assert(s0[0] == Seq::<Par>::empty()); //2

        assert(s0[s0.len() - 1] == s[s0.len() as int].drop_first());
        assert(s0.last() == s[s.len() - 2].drop_first());
        assert(aux(v[v.len() - 1], s[v.len() - 1], s[v.len() as int]));
        assert(s[v.len() as int].len() == 0);
        assert(s[v.len() - 1].len() == 1);
        assert(s0.last() == Seq::<Par>::empty()); //3

        assert forall |i:int| 0 <= i < v0.len() implies aux(v0[i], s0[i], s0[i+1]) //4
        by {
            assert(aux(v[i+1], s[i+1], s[i+2]));
            assert(v[i+1] == v0[i]);

            assert(forall |k:int| 0 < k < v.len() ==> #[trigger]s[k].len() > 0 && s[k][0] == v[0]) by{
                lem0(v, s, v.len() as int)
            }
            assert(s[i+2].len() > 0);

            assert(s0[i].drop_last() == s[i+1].drop_first().drop_last());
            assert(s0[i].last() == s[i+1].drop_first().last());

            match v[i+1] {
                La | Lb | Lc => {
                    assert(s[i+1].push(v[i+1]).drop_first() == s[i+1].drop_first().push(v[i+1]));
                }
                Ra | Rb | Rc => {
                    assert(s[i+1].len() > 1);
                    assert(s[i+1].last() == s[i+1].drop_first().last());
                    assert(s[i+1].drop_last().drop_first() == s[i+1].drop_first().drop_last());
                },
            }
        }
        assert(stack_spec(v0, s0));
        assert(
            (v[0] == La <==> v.last() == Ra)
            && (v[0] == Lb <==> v.last() == Rb)
            && (v[0] == Lc <==> v.last() == Rc)
        )
        by {
            assert(aux(v0[v0.len() - 1], s0[v0.len() - 1], s0[v0.len() as int]));
            assert(s[s.len() - 2][0] == v[0]) by {
                lem0(v, s, v.len() as int)
            }
        }
    }
}


spec fn valid_par_spec(v:Seq<Par>) -> bool{
    rec_spec(v)
}


}//verus

fn main(){}
