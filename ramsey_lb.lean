import data.nat.basic
import data.int.basic
import data.rat.basic

import algebra.field_power

import tactic

import data.finset
import algebra.big_operators
import data.real.basic
import data.set.lattice

open finset
open nat

local notation `edges_of `X := powerset_len 2 X

universe u
variables {α : Type u} (K : finset α) {n : ℕ} --[decidable_eq α]

/-

lemma number_of_colorings_of_K_with_monochromatic_K_subgraph (k : ℕ) (hn : card(K_1) = n)
    := card (colorings_of_K_with_monochromatic_K_subgraph k) = 2^(n.choose(2) - n.choose(k)) * 2 * n.choose(k)

----------
-/

/-
  The set of all two colorings of the complete graph
-/
--Note: Present implementation only works with 2 colorings
def colorings : finset (finset (finset α)) := powerset (edges_of K)

/-
  The cardinality of colorings
-/
lemma num_complete_colorings (hn : card K = n) : 
    card (colorings K) = 2^(nat.choose n 2) :=
begin
    rw colorings,
    rw card_powerset,
    rw card_powerset_len,
    rw hn,
end

/-
  The set of all 2 colorings of the compelte graph such that the coloring is monochromatic
  on a complete subgraph of order k
-/
def mono_sub_colorings (n : ℕ) (k : ℕ) : finset (finset (finset α)) :=
begin
  sorry,
end

/-
  The cardinality of mono_sub_colorings
-/
lemma num_mono_sub_colorings (n k : ℕ) (h : n ≥ k) : 
  (card (@mono_sub_colorings α n k) : ℚ) = ((2 : ℚ)^((n.choose(2)) - (k.choose(2))) : ℚ) * 2 * n.choose(k) := 
begin
  sorry,
end

/-
  Central inequality of the next theorem, except without binomial coefficients
  (for readability and convenience).
-/
lemma core_ineq
  {a b c : ℕ}
  (h : ((2 : ℚ)^(1 - b : ℤ) * c : ℚ) < 1) :
  ((2 : ℚ)^(a - b : ℤ) * 2 * c : ℚ) < (2:ℚ)^(a : ℤ) :=
begin 
  --rw fpow_add two_ne_zero a (-b),
  --fpow_add alt approach above

  rw @fpow_sub ℚ _ _ two_ne_zero 1 b at h, 
  rw fpow_one (2: ℚ) at h,
    
  rw @fpow_sub ℚ _ _ two_ne_zero a b,

  rw div_mul_eq_mul_div_comm (2) ((2 : ℚ)^(a : ℤ)) ((2 : ℚ)^(b : ℤ)),
  rw mul_assoc ((2 : ℚ)^(a : ℤ)) (2 / 2 ^ ↑b) (↑c),
  rw mul_comm ((2 : ℚ) ^ ↑a) (2 / 2 ^ ↑b * ↑c),

  apply mul_lt_of_lt_div,

  exact nat.fpow_pos_of_pos (nat.pos_of_ne_zero(two_ne_zero)) (a : ℤ),
  rw div_self,

  exact h,

  apply fpow_ne_zero_of_ne_zero,
  exact dec_trivial,
end

/-
  Proof that the cardinality of colorings is strictly less than the 
  cardinality of mono_sub_colorings given a certain hypothesis.
-/
theorem card_strict_inequality (n k : ℕ) (hnk : n ≥ k) (hn : card (K) = n) 
  (h : (2^(1 - k.choose(2) : ℤ) * n.choose(k) : ℚ) < 1) :
  (card (@mono_sub_colorings α n k) : ℚ) < (card (colorings K) : ℚ) := 
begin 
  rw num_complete_colorings K hn,
  rw num_mono_sub_colorings n k hnk,

  exact @core_ineq (n.choose 2) (k.choose 2) (n.choose k) (h),
end
