// use vstd::prelude::*;

// use vstd::arithmetic::power::*;
// // use vstd::arithmetic::logarithm::*;


// verus!{

// // broadcast use group_pow_properties;

// pub open spec fn count_digit(n:nat) -> nat
//   decreases n
// {
//   if n < 10 { 1 } else {
//     1 + count_digit(n/10)
//   }
// }

// pub open spec fn pow10(n:nat) -> nat {
//   pow(10int, n) as nat
// }

// // spec fn reverse(n: nat) -> nat
// //   decreases n
// // {
// //   if n < 10 {n} else {
// //     ((n % 10) * pow10(count_digit(n / 10)) + reverse(n / 10)) as nat
// //   }
// // }


// proof fn lemma_0(a:nat, b:nat, digit:nat)
//   ensures
//     (a/10) * pow10(digit + 1) + b * 10 + a % 10
//     == a * pow10(digit) + b
//   decreases
//     digit
// {


//   (10 * a/10 + a%10) * pow10(digit) + b ==
//   (a/10) * pow10(digit + 1) + a%10 * pow10(digit) + b

//   if digit == 0 {
//     // assert(pow10(digit) == 1);
//     // assert(pow10(digit + 1) == 10);
//     // assert( (a/10) * 10 + b * 10 + a % 10
//   }
//   else {
//     admit()
//   }
// }

// pub fn is_palindrome(x: usize) -> bool {
//   if x % 10 == 0 && x != 0 {
//     return false;
//   }
//   if x == 0 {
//     return true;
//   }

//   let mut num = x;
//   let mut reversed = 0;

//   assert(x == num * pow10(0) + reversed) by {
//     assert(pow10(0) == 1);
//   }

//   let ghost digit_reversed : nat = 0;
//   // let ghost digit_num : nat = count_digit(num as nat);
//   // let ghost digit = digit_num;

//   reversed = reversed * 10 + num % 10;
//   num /= 10;

//   assert(reversed == x % 10);
//   assert(reversed != 0);
//   proof {
//     digit_reversed = digit_reversed + 1;
//   }

//   // assert(x == num * pow10(digit_reversed) + reversed) by {
//   // }

//   // assert forall |a:nat, b:nat, digit:nat|
//   //   (a/10) * pow10(digit + 1) + b * 10 + a % 10
//   //   == #[trigger] add(mul(a, pow10(digit)), b) by
//   // {

//   // }

//   // while num > reversed
//   //   invariant
//   //     // reversed == 0,
//   //     // digit == digit_reversed + digit_num,

//   //     x == num * pow10(digit_reversed) + reversed,

//   //     // x == (num / 10) * pow(digit_reversed + 1) + reversed

//   //   decreases num
//   // {
//   //   reversed = reversed * 10 + num % 10;
//   //   num /= 10;

//   //   proof {
//   //     digit_reversed = digit_reversed + 1;
//   //     digit_num = (digit_num - 1) as nat; // may overflow ==> digit_num = 0
//   //   }
//   // }

//   num == reversed || num == reversed / 10
// }






// }//verus!

fn main(){}
