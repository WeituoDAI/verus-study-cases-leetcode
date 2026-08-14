use vstd::prelude::*;

verus! {

pub open spec fn is_three_sum(t: Seq<i32>) -> bool {
    t.len() == 3
        && t[0] as int + t[1] as int + t[2] as int == 0
}

pub open spec fn values_from_input(input: Seq<i32>, t: Seq<i32>) -> bool {
    t.len() == 3
        && exists |i: int, j: int, k: int|
            0 <= i < j < k < input.len()
                && input[i] == t[0]
                && input[j] == t[1]
                && input[k] == t[2]
}

pub open spec fn all_valid(input: Seq<i32>, answer: Seq<Vec<i32>>) -> bool {
    forall |k: int| 0 <= k < answer.len() ==>
        #[trigger] is_three_sum(answer[k]@) && values_from_input(input, answer[k]@)
}

pub open spec fn triple_lt(a: Seq<i32>, b: Seq<i32>) -> bool {
    a[0] < b[0]
        || (a[0] == b[0] && a[1] < b[1])
        || (a[0] == b[0] && a[1] == b[1] && a[2] < b[2])
}

pub open spec fn result_ordered(answer: Seq<Vec<i32>>) -> bool {
    forall |p: int, q: int| #![auto] 0 <= p < q < answer.len() ==>
        triple_lt(answer[p]@, answer[q]@)
}

pub open spec fn all_distinct(answer: Seq<Vec<i32>>) -> bool {
    forall |p: int, q: int| #![auto] 0 <= p < q < answer.len() ==> answer[p]@ != answer[q]@
}

pub open spec fn firsts_before(input: Seq<i32>, answer: Seq<Vec<i32>>, i: int) -> bool {
    forall |p: int| #![auto] 0 <= p < answer.len() ==>
        i == 0 || answer[p]@[0] <= input[i - 1]
}

pub open spec fn before_left(
    input: Seq<i32>, answer: Seq<Vec<i32>>, i: int, left: int,
) -> bool {
    forall |p: int| #![auto] 0 <= p < answer.len() ==>
        answer[p]@[0] < input[i]
        || (answer[p]@[0] == input[i] && answer[p]@[1] <= input[left - 1])
}

pub open spec fn triple_sum(input: Seq<i32>, i: int, j: int, k: int) -> int {
    input[i] as int + input[j] as int + input[k] as int
}

pub open spec fn triple_in_answer(
    input: Seq<i32>, answer: Seq<Vec<i32>>, i: int, j: int, k: int,
) -> bool {
    exists |p: int| #![trigger answer[p]@]
        0 <= p < answer.len()
        && answer[p]@ =~= seq![input[i], input[j], input[k]]
}

// All zero-sum pairs (j,k) with i fixed that lie outside the open window
// [left, right] are already represented in answer.
pub open spec fn covered_range(
    input: Seq<i32>, answer: Seq<Vec<i32>>, i: int, left: int, right: int,
) -> bool {
    forall |j: int, k: int|
        0 <= i && i < j && j < k && k < input.len()
            && (j < left || k > right)
            && #[trigger] triple_sum(input, i, j, k) == 0
        ==> triple_in_answer(input, answer, i, j, k)
}

// All zero-sum triples whose first index is strictly less than bound
// are already represented in answer.
pub open spec fn covered_before(
    input: Seq<i32>, answer: Seq<Vec<i32>>, bound: int,
) -> bool {
    forall |i: int, j: int, k: int|
        0 <= i && i < bound && i < j && j < k && k < input.len()
            && #[trigger] triple_sum(input, i, j, k) == 0
        ==> triple_in_answer(input, answer, i, j, k)
}

pub open spec fn all_complete(input: Seq<i32>, answer: Seq<Vec<i32>>) -> bool {
    covered_before(input, answer, input.len() as int)
}

proof fn lemma_ordered_distinct(answer: Seq<Vec<i32>>)
    requires result_ordered(answer)
    ensures all_distinct(answer)
{
    assert forall |p: int, q: int| #![auto] 0 <= p < q < answer.len()
        implies answer[p]@ != answer[q]@ by {
        assert(triple_lt(answer[p]@, answer[q]@));
    }
}

pub open spec fn is_sorted_spec(v: Seq<i32>) -> bool {
    forall |p: int, q: int| #![auto] 0 <= p <= q < v.len() ==> v[p] <= v[q]
}

proof fn lemma_seq3_congr(a0: i32, b0: i32, a1: i32, b1: i32, a2: i32, b2: i32)
    requires a0 == b0 && a1 == b1 && a2 == b2
    ensures seq![a0, a1, a2] =~= seq![b0, b1, b2]
{
}

proof fn lemma_push_index(s: Seq<Vec<i32>>, x: Vec<i32>)
    ensures
        s.push(x).len() == s.len() + 1,
        forall |q: int| #![trigger s.push(x)[q]] 0 <= q < s.len() ==> s.push(x)[q] == s[q],
{
}

proof fn lemma_ordered_push(s: Seq<Vec<i32>>, x: Vec<i32>)
    requires
        result_ordered(s),
        forall |p: int| #![auto] 0 <= p < s.len() ==> triple_lt(s[p]@, x@),
    ensures
        result_ordered(s.push(x)),
{
    assert forall |p: int, q: int| #![auto] 0 <= p < q < s.push(x).len()
        implies triple_lt(s.push(x)[p]@, s.push(x)[q]@) by {
        if q < s.len() {
            assert(s.push(x)[p]@ =~= s[p]@);
            assert(s.push(x)[q]@ =~= s[q]@);
            assert(result_ordered(s));
        } else {
            assert(q == s.len());
            assert(s.push(x)[q]@ =~= x@);
            assert(triple_lt(s[p]@, x@));
            assert(s.push(x)[p]@ =~= s[p]@);
        }
    }
}

proof fn lemma_before_left_mono(
    input: Seq<i32>, answer: Seq<Vec<i32>>, i: int, old_left: int, new_left: int,
)
    requires
        before_left(input, answer, i, old_left),
        0 < old_left <= new_left < input.len(),
        is_sorted_spec(input),
    ensures
        before_left(input, answer, i, new_left),
{
    assert forall |p: int| #![auto] 0 <= p < answer.len() implies
        answer[p]@[0] < input[i]
        || (answer[p]@[0] == input[i] && answer[p]@[1] <= input[new_left - 1]) by {
        if answer[p]@[0] < input[i] {
        } else {
            assert(answer[p]@[0] == input[i]);
            assert(answer[p]@[1] <= input[old_left - 1]);
            assert(input[old_left - 1] <= input[new_left - 1]);
        }
    }
}

// After answer grows by a push, any triple already in the old answer is still in.
proof fn lemma_answer_grows(
    input: Seq<i32>, old_ans: Seq<Vec<i32>>, new_ans: Seq<Vec<i32>>,
    i: int, j: int, k: int, x: Vec<i32>,
)
    requires
        new_ans =~= old_ans.push(x),
        triple_in_answer(input, old_ans, i, j, k),
    ensures
        triple_in_answer(input, new_ans, i, j, k),
{
    let p0 = choose |p0: int| #![trigger old_ans[p0]@]
        0 <= p0 < old_ans.len()
        && old_ans[p0]@ =~= seq![input[i], input[j], input[k]];
    lemma_push_index(old_ans, x);
    assert(new_ans[p0]@ =~= seq![input[i], input[j], input[k]]);
}

// LeetCode 15: return every distinct triple [a, b, c] such that a+b+c == 0.
// The input is assumed to be sorted, then each fixed element is paired with
// two inward-moving pointers. Equal values are skipped to avoid duplicates.
pub fn three_sum(nums: Vec<i32>) -> (res: Vec<Vec<i32>>)
    requires
        nums.len() <= 3000,
        forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums@[i] <= 100000,
        is_sorted_spec(nums@),
    ensures
        all_valid(nums@, res@),
        all_complete(nums@, res@),
        result_ordered(res@),
        all_distinct(res@),
{
    let n = nums.len();
    let mut answer: Vec<Vec<i32>> = Vec::new();
    if n < 3 {
        return answer;
    }
    let mut i: usize = 0;

    while i <= n - 3
        invariant
            3 <= n <= 3000,
            n == nums.len(),
            0 <= i <= n,
            is_sorted_spec(nums@),
            all_valid(nums@, answer@),
            result_ordered(answer@),
            firsts_before(nums@, answer@, i as int),
            i != 0 || answer.len() == 0,
            covered_before(nums@, answer@, i as int),
        decreases n - i
    {
        if i > 0 && nums[i] == nums[i - 1] {
            proof {
                // Triples starting at i have the same values as those starting at i-1.
                assert forall |i2: int, j: int, k: int| #![auto]
                    0 <= i2 && i2 < ((i + 1) as int) && i2 < j && j < k && k < n
                        && triple_sum(nums@, i2, j, k) == 0
                    implies triple_in_answer(nums@, answer@, i2, j, k)
                by {
                    if i2 < i as int {
                        assert(triple_sum(nums@, i2, j, k) == 0);
                    } else {
                        assert(i2 == i as int);
                        assert(nums@[i as int] == nums@[i as int - 1]);
                        assert(triple_sum(nums@, i as int - 1, j, k) == 0);
                        assert(triple_in_answer(nums@, answer@, i as int - 1, j, k));
                        let p0 = choose |p0: int| #![trigger answer@[p0]@] 0 <= p0 < answer.len()
                            && answer@[p0]@ =~= seq![
                                nums@[i as int - 1], nums@[j], nums@[k]
                            ];
                        lemma_seq3_congr(
                            nums@[i as int - 1], nums@[i2],
                            nums@[j], nums@[j],
                            nums@[k], nums@[k],
                        );
                        assert(answer@[p0]@ =~= seq![nums@[i2], nums@[j], nums@[k]]);
                    }
                }
            }
            i += 1;
            continue;
        }

        let mut left: usize = i + 1;
        let mut right: usize = n - 1;

        proof {
            assert forall |p: int| #![auto] 0 <= p < answer.len() implies
                answer@[p]@[0] < nums@[i as int]
                || (answer@[p]@[0] == nums@[i as int]
                    && answer@[p]@[1] <= nums@[left as int - 1])
            by {
                if i == 0 {
                    assert(answer.len() == 0);
                } else {
                    assert(nums@[i as int - 1] < nums@[i as int]);
                    assert(firsts_before(nums@, answer@, i as int));
                }
            }
        }

        while left < right
            invariant
                3 <= n <= 3000,
                n == nums.len(),
                0 <= i < n,
                i + 1 <= left <= right < n,
                is_sorted_spec(nums@),
                all_valid(nums@, answer@),
                result_ordered(answer@),
                left > i + 1 || firsts_before(nums@, answer@, i as int),
                left > i + 1 || i != 0 || answer.len() == 0,
                i == 0 || nums@[i as int - 1] != nums@[i as int],
                before_left(nums@, answer@, i as int, left as int),
                covered_before(nums@, answer@, i as int),
                covered_range(nums@, answer@, i as int, left as int, right as int),
            decreases right - left
        {
            let ghost old_left = left as int;
            let ghost old_right = right as int;
            let ghost old_measure = right - left;

            // Skip duplicate left values.
            if left > i + 1 && nums[left] == nums[left - 1] {
                proof {
                    assert(nums@[old_left] == nums@[old_left - 1]);
                    assert forall |j: int, k: int| #![auto]
                        0 <= (i as int) && (i as int) < j && j < k && k < n
                            && (j < old_left + 1 || k > old_right)
                            && triple_sum(nums@, i as int, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i as int, j, k)
                    by {
                        if k > old_right {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else if j < old_left {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else {
                            assert(j == old_left);
                            assert(old_left - 1 > i as int);
                            assert(triple_sum(nums@, i as int, old_left - 1, k) == 0);
                            assert(triple_in_answer(
                                nums@, answer@, i as int, old_left - 1, k,
                            ));
                            let p0 = choose |p0: int| #![trigger answer@[p0]@] 0 <= p0 < answer.len()
                                && answer@[p0]@ =~= seq![
                                    nums@[i as int], nums@[old_left - 1], nums@[k]
                                ];
                            lemma_seq3_congr(
                                nums@[i as int], nums@[i as int],
                                nums@[old_left - 1], nums@[j],
                                nums@[k], nums@[k],
                            );
                            assert(answer@[p0]@ =~= seq![
                                nums@[i as int], nums@[j], nums@[k]
                            ]);
                        }
                    }
                }
                left += 1;
                proof {
                    lemma_before_left_mono(
                        nums@, answer@, i as int, old_left, left as int,
                    );
                }
                assert(right - left < old_measure);
                continue;
            }

            // Skip duplicate right values.
            if right + 1 < n && nums[right] == nums[right + 1] {
                proof {
                    assert(nums@[old_right] == nums@[old_right + 1]);
                    assert forall |j: int, k: int| #![auto]
                        0 <= (i as int) && (i as int) < j && j < k && k < n
                            && (j < old_left || k > old_right - 1)
                            && triple_sum(nums@, i as int, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i as int, j, k)
                    by {
                        if k > old_right {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else if j < old_left {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else {
                            assert(k == old_right);
                            assert(old_right + 1 < n);
                            assert(triple_sum(nums@, i as int, j, old_right + 1) == 0);
                            assert(triple_in_answer(
                                nums@, answer@, i as int, j, old_right + 1,
                            ));
                            let p0 = choose |p0: int| #![trigger answer@[p0]@] 0 <= p0 < answer.len()
                                && answer@[p0]@ =~= seq![
                                    nums@[i as int], nums@[j], nums@[old_right + 1]
                                ];
                            lemma_seq3_congr(
                                nums@[i as int], nums@[i as int],
                                nums@[j], nums@[j],
                                nums@[old_right + 1], nums@[k],
                            );
                            assert(answer@[p0]@ =~= seq![
                                nums@[i as int], nums@[j], nums@[k]
                            ]);
                        }
                    }
                }
                right -= 1;
                assert(right - left < old_measure);
                continue;
            }

            let sum: i64 = nums[i] as i64 + nums[left] as i64 + nums[right] as i64;

            if sum < 0 {
                proof {
                    assert(triple_sum(nums@, i as int, old_left, old_right) < 0);
                    // Moving left past old_left cannot miss a zero-sum pair:
                    // any pair with j == old_left and k <= old_right has sum < 0.
                    assert forall |j: int, k: int| #![auto]
                        0 <= (i as int) && (i as int) < j && j < k && k < n
                            && (j < old_left + 1 || k > old_right)
                            && triple_sum(nums@, i as int, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i as int, j, k)
                    by {
                        if k > old_right {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else if j < old_left {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else {
                            assert(j == old_left);
                            assert(k <= old_right);
                            assert(nums@[k] <= nums@[old_right]);
                            assert(triple_sum(nums@, i as int, j, k)
                                <= triple_sum(nums@, i as int, old_left, old_right));
                            assert(triple_sum(nums@, i as int, j, k) < 0);
                            assert(false);
                        }
                    }
                }
                if left + 1 >= right {
                    left = right;
                } else {
                    left += 1;
                }
                proof {
                    lemma_before_left_mono(
                        nums@, answer@, i as int, old_left, left as int,
                    );
                }
                assert(right - left < old_measure);
            } else if sum > 0 {
                proof {
                    assert(triple_sum(nums@, i as int, old_left, old_right) > 0);
                    // Moving right past old_right cannot miss a zero-sum pair:
                    // any pair with k == old_right and j >= old_left has sum > 0.
                    assert forall |j: int, k: int| #![auto]
                        0 <= (i as int) && (i as int) < j && j < k && k < n
                            && (j < old_left || k > old_right - 1)
                            && triple_sum(nums@, i as int, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i as int, j, k)
                    by {
                        if k > old_right {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else if j < old_left {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                        } else {
                            assert(k == old_right);
                            assert(j >= old_left);
                            assert(nums@[j] >= nums@[old_left]);
                            assert(triple_sum(nums@, i as int, j, k)
                                >= triple_sum(nums@, i as int, old_left, old_right));
                            assert(triple_sum(nums@, i as int, j, k) > 0);
                            assert(false);
                        }
                    }
                }
                if left + 1 >= right {
                    right = left;
                } else {
                    right -= 1;
                }
                assert(right - left < old_measure);
            } else {
                // sum == 0: record the triple, then shrink the window.
                let ghost old_answer = answer@;
                let ghost old_len = answer.len() as int;
                let triple = vec![nums[i], nums[left], nums[right]];
                proof {
                    assert(triple@ =~= seq![
                        nums@[i as int], nums@[old_left], nums@[old_right]
                    ]);
                    assert(left == i + 1
                        || nums@[left as int] != nums@[left as int - 1]);
                    assert forall |p: int| #![auto] 0 <= p < old_answer.len()
                        implies triple_lt(old_answer[p]@, triple@) by {
                        if old_answer[p]@[0] < nums@[i as int] {
                            assert(triple_lt(old_answer[p]@, triple@));
                        } else {
                            assert(old_answer[p]@[0] == nums@[i as int]);
                            if left == i + 1 {
                                if i == 0 {
                                    assert(old_answer.len() == 0);
                                } else {
                                    assert(firsts_before(nums@, old_answer, i as int));
                                    assert(nums@[i as int - 1] < nums@[i as int]);
                                    assert(old_answer[p]@[0] <= nums@[i as int - 1]);
                                    assert(false);
                                }
                            } else {
                                assert(nums@[old_left - 1] < nums@[old_left]);
                                assert(before_left(nums@, old_answer, i as int, old_left));
                                assert(old_answer[p]@[1] <= nums@[old_left - 1]);
                                assert(old_answer[p]@[1] < nums@[old_left]);
                                assert(triple_lt(old_answer[p]@, triple@));
                            }
                        }
                    }
                }
                answer.push(triple);
                if left + 1 >= right {
                    left = right;
                } else {
                    left += 1;
                    right -= 1;
                }
                proof {
                    assert(triple_sum(nums@, i as int, old_left, old_right) == 0);
                    assert(answer@ =~= old_answer.push(triple));
                    lemma_push_index(old_answer, triple);
                    assert(answer@[old_len]@ =~= seq![
                        nums@[i as int], nums@[old_left], nums@[old_right]
                    ]);
                    assert forall |p: int| #![auto] 0 <= p < answer.len() implies
                        is_three_sum(answer@[p]@)
                        && values_from_input(nums@, answer@[p]@) by {
                        if p < old_len {
                            assert(all_valid(nums@, old_answer));
                        } else {
                            assert(p == old_len);
                            assert(triple_sum(nums@, i as int, old_left, old_right) == 0);
                            assert(answer@[p]@ =~= seq![
                                nums@[i as int], nums@[old_left], nums@[old_right]
                            ]);
                        }
                    }
                    lemma_ordered_push(old_answer, triple);
                    assert(result_ordered(answer@));

                    assert forall |p: int| #![auto] 0 <= p < answer.len() implies
                        answer@[p]@[0] < nums@[i as int]
                        || (answer@[p]@[0] == nums@[i as int]
                            && answer@[p]@[1] <= nums@[left as int - 1]) by {
                        if p < old_len {
                            assert(before_left(nums@, old_answer, i as int, old_left));
                            assert(old_answer[p]@[0] < nums@[i as int]
                                || (old_answer[p]@[0] == nums@[i as int]
                                    && old_answer[p]@[1] <= nums@[old_left - 1]));
                            assert(old_left <= left as int - 1);
                            assert(nums@[old_left - 1] <= nums@[left as int - 1]);
                            assert(answer@[p]@ =~= old_answer[p]@);
                        } else {
                            assert(p == old_len);
                            assert(answer@[p]@[0] == nums@[i as int]);
                            assert(answer@[p]@[1] == nums@[old_left]);
                            assert(old_left <= left as int - 1);
                            assert(nums@[old_left] <= nums@[left as int - 1]);
                        }
                    }

                    // covered_before is preserved under push.
                    assert forall |i2: int, j: int, k: int| #![auto]
                        0 <= i2 && i2 < (i as int) && i2 < j && j < k && k < n
                            && triple_sum(nums@, i2, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i2, j, k)
                    by {
                        assert(triple_sum(nums@, i2, j, k) == 0);
                        assert(triple_in_answer(nums@, old_answer, i2, j, k));
                        lemma_answer_grows(
                            nums@, old_answer, answer@, i2, j, k, triple,
                        );
                    }

                    // covered_range for the new window.
                    assert forall |j: int, k: int| #![auto]
                        0 <= (i as int) && (i as int) < j && j < k && k < n
                            && (j < left as int || k > right as int)
                            && triple_sum(nums@, i as int, j, k) == 0
                        implies triple_in_answer(nums@, answer@, i as int, j, k)
                    by {
                        if k > old_right {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                            assert(triple_in_answer(
                                nums@, old_answer, i as int, j, k,
                            ));
                            lemma_answer_grows(
                                nums@, old_answer, answer@,
                                i as int, j, k, triple,
                            );
                        } else if j < old_left {
                            assert(triple_sum(nums@, i as int, j, k) == 0);
                            assert(triple_in_answer(
                                nums@, old_answer, i as int, j, k,
                            ));
                            lemma_answer_grows(
                                nums@, old_answer, answer@,
                                i as int, j, k, triple,
                            );
                        } else {
                            // j >= old_left and k <= old_right.
                            // The new window condition forces j == old_left or k == old_right,
                            // and sortedness forces the values to match the pushed triple.
                            if j == old_left {
                                assert(nums@[k] <= nums@[old_right]);
                                assert(triple_sum(nums@, i as int, j, k)
                                    <= triple_sum(nums@, i as int, old_left, old_right));
                                assert(nums@[k] == nums@[old_right]);
                                lemma_seq3_congr(
                                    nums@[i as int], nums@[i as int],
                                    nums@[old_left], nums@[j],
                                    nums@[old_right], nums@[k],
                                );
                                assert(answer@[old_len]@ =~= seq![
                                    nums@[i as int], nums@[j], nums@[k]
                                ]);
                            } else {
                                assert(j > old_left);
                                if old_right == old_left + 1 {
                                    // Adjacent case: no room for j > old_left inside the window.
                                    assert(j >= old_left + 1);
                                    assert(k >= j + 1 >= old_left + 2);
                                    assert(k > old_right);
                                    assert(false);
                                } else {
                                    // Non-adjacent: right moved to old_right - 1.
                                    assert(left as int == old_left + 1);
                                    assert(right as int == old_right - 1);
                                    assert(j >= left as int);
                                    assert(k > right as int);
                                    assert(k == old_right);
                                    assert(nums@[j] >= nums@[old_left]);
                                    assert(triple_sum(nums@, i as int, j, k)
                                        >= triple_sum(
                                            nums@, i as int, old_left, old_right,
                                        ));
                                    assert(nums@[j] == nums@[old_left]);
                                    lemma_seq3_congr(
                                        nums@[i as int], nums@[i as int],
                                        nums@[old_left], nums@[j],
                                        nums@[old_right], nums@[k],
                                    );
                                    assert(answer@[old_len]@ =~= seq![
                                        nums@[i as int], nums@[j], nums@[k]
                                    ]);
                                }
                            }
                        }
                    }
                }
                assert(right - left < old_measure);
            }
        }

        // Inner loop finished: left == right, so the window is empty.
        // Every zero-sum pair for this i is covered.
        proof {
            assert(left == right);
            assert forall |i2: int, j: int, k: int| #![auto]
                0 <= i2 && i2 < ((i + 1) as int) && i2 < j && j < k && k < n
                    && triple_sum(nums@, i2, j, k) == 0
                implies triple_in_answer(nums@, answer@, i2, j, k)
            by {
                if i2 < i as int {
                    assert(triple_sum(nums@, i2, j, k) == 0);
                } else {
                    assert(i2 == i as int);
                    assert(j < left as int || k > right as int) by {
                        if j < left as int {
                        } else {
                            assert(j >= left as int);
                            assert(k > j);
                            assert(k > right as int);
                        }
                    };
                    assert(triple_sum(nums@, i as int, j, k) == 0);
                }
            }
        }
        i += 1;
    }

    // Outer loop finished: i >= n - 2, so every first index i2 <= n - 3 is covered.
    proof {
        assert(i as int >= n as int - 2);
        assert forall |i2: int, j: int, k: int| #![auto]
            0 <= i2 && i2 < (n as int) && i2 < j && j < k && k < n
                && triple_sum(nums@, i2, j, k) == 0
            implies triple_in_answer(nums@, answer@, i2, j, k)
        by {
            assert(i2 <= n as int - 3);
            assert(i2 < i as int);
            assert(triple_sum(nums@, i2, j, k) == 0);
        }
    }

    proof {
        assert(result_ordered(answer@));
        lemma_ordered_distinct(answer@);
    }
    answer
}

} // verus!

fn main() {
    // Temporary executable tests. They can be enabled after the formal proof
    // is completed; runtime tests are not a substitute for Verus proofs.
    // assert_eq!(
    //     three_sum(vec![-1, 0, 1, 2, -1, -4]),
    //     vec![vec![-1, -1, 2], vec![-1, 0, 1]],
    // );
    // assert_eq!(three_sum(vec![0, 1, 1]), Vec::<Vec<i32>>::new());
    // assert_eq!(three_sum(vec![0, 0, 0, 0]), vec![vec![0, 0, 0]]);
    // assert_eq!(
    //     three_sum(vec![-2, 0, 1, 1, 2]),
    //     vec![vec![-2, 0, 2], vec![-2, 1, 1]],
    // );
    // assert_eq!(three_sum(vec![]), Vec::<Vec<i32>>::new());
    // assert_eq!(three_sum(vec![1, 2]), Vec::<Vec<i32>>::new());
}
