import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat
open Finset
open BigOperators

theorem idt16(x y: ℝ):
   ∑ k in range (n+1), x ^ (2*k) * y ^ (n - 2*k) * choose n 2*k  = (1/2)*((x + y) ^ n +(y - x) ^ n) := by
   have h₁:y - x =(-x:ℝ)  + y := by
      rw [sub_eq_neg_add]
   rw [h₁]
   rw [add_pow,add_pow]
   have h₂: ∑ m in range (n + 1), x ^ m * y ^ (n - m) * ↑(Nat.choose n m) +
      ∑ m in range (n + 1), (-x) ^ m * y ^ (n - m) * ↑(Nat.choose n m) =
       2*(∑ m in range (n+1), x ^ (2*m) * y ^ (n - 2*m) * choose n 2*m):= by sorry
   rw [h₂]
   rw [← mul_assoc]
   norm_num
