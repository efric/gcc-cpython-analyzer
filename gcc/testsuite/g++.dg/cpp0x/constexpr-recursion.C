// Test that we catch excessive recursion.
// { dg-do compile { target c++11 } }
// { dg-options "-fconstexpr-depth=5" }
// { dg-prune-output "in .constexpr. expansion" }
constexpr int f (int i) { return f (i-1); } // { dg-error ".constexpr. evaluation depth" }
constexpr int i = f(42);	
