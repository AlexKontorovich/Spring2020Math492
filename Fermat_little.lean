import data.nat.gcd
import algebra.big_operators


import data.zmod.basic

def divides (d n: ℤ):=  ∃l:ℤ, n = d*l
def is_congruent_mod_n (a b n: ℤ) := divides n (b-a)
def relatively_prime(a b:ℤ) := ∀l:ℤ, ¬(divides l a) ∨ ¬(divides l b)

theorem relatively_prime_sum_to_one (a b : ℤ) (h : relatively_prime a b) : 
∃ m n: ℤ, m* a + n * b = 1 := sorry

--helper theorem that is not true :(--
-- the iff is not true, but I can't use it without it--
theorem divides_in_product (a b c: ℤ): a*b = c ↔ divides a c:= sorry

--Generalized Euclid Lemma --
theorem divides_product_coprime_and_not_coprime (a b n:ℤ) (c: divides n (a*b))
(d: relatively_prime a n):
divides n b:=
begin
  -- cases breaks down existential qualifiers
  cases c with l k,
  cases relatively_prime_sum_to_one a n d with m h,
  cases h with q manb_eq_one,
  
  -- multiplies both sides by b
  have := congr_arg (has_mul.mul b) manb_eq_one, -- does not work if I covert to naturals
  rw [mul_one] at this,
  -- this : b * (m * a + q * n) = b

  -- order-changing  
  rw [mul_add] at this,
  rw [mul_comm] at this,
  rw [mul_assoc] at this,
  rw k at this,
  rw [mul_comm] at this,
  rw [mul_assoc] at this,
  rw [add_comm] at this,
  rw [mul_comm] at this,
  rw [mul_assoc] at this,
  rw [mul_left_comm] at this,
  rw <- mul_add at this,

  rw divides_in_product n (q*b+l*m) b at this, -- can use "apply" instead and get rid of iff
  apply this,

end


theorem cancel_out_mod_n (a b c n: ℤ) (p: is_congruent_mod_n (a*b) (a*c) n)
(q: relatively_prime a n) : is_congruent_mod_n b c n :=

begin
  cases p with j k,
  rw <-mul_sub at k,  --does not work if I convert to naturals
  rw eq_comm at k,
  rw divides_in_product n j (a*(c-b)) at k,  -- cannot use "apply" and get rid of iff
  apply divides_product_coprime_and_not_coprime a (c-b) n,
  {
    apply k,
  },
  {
    apply q,
  },

end


-- residue class --
def reduced_residue_class (n : nat) : finset nat := 
(finset.range n).filter $ assume k, k.coprime n

def prod_rsc (n) : nat := (reduced_residue_class n).prod id

-- not scaled :( --
def scaled_residue_class (a n: nat): finset nat :=
(finset.range n).filter $ assume k, k.coprime n

def prod_scaled_rsc (a n: nat): nat := (scaled_residue_class a n).prod id

--congruence of residue classes --
theorem congruent_residue_classes(a n: nat)(c:a.coprime n): 
is_congruent_mod_n (prod_rsc n)(prod_scaled_rsc a n) n:= sorry



--Zulip proof of Bézout 
lemma bezout (a : ℕ) (b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (h : nat.gcd a b = 1) :
    ∃ x : ℕ, ∃ y : ℕ, a*x + 1 = b*y :=
begin
  let k := max (int.nat_abs (nat.gcd_a a b)) (int.nat_abs (nat.gcd_b a b)) + 1,
  let x : ℤ := b*k - nat.gcd_a a b,
  let y : ℤ := a*k + nat.gcd_b a b,
  refine ⟨int.to_nat x, int.to_nat y, int.coe_nat_inj _⟩,
  suffices : (a * int.to_nat x + 1 : ℤ) = b * int.to_nat y, {simpa},
  have k1 : 1 ≤ k := nat.le_add_left _ _,
  have ha' : (1:ℤ) ≤ a := int.coe_nat_le.2 ha,
  have hb' : (1:ℤ) ≤ b := int.coe_nat_le.2 hb,
  have x0 : 0 ≤ x,
  { refine sub_nonneg.2 _,
    have := mul_le_mul_of_nonneg_right hb' (int.coe_nat_nonneg k),
    rw one_mul at this,
    refine le_trans (le_trans int.le_nat_abs _) this,
    refine int.coe_nat_le.2 _,
    exact nat.le_succ_of_le (le_max_left _ _) },
  have y0 : 0 ≤ y,
  { refine sub_le_iff_le_add.1 _,
    rw zero_sub,
    have := mul_le_mul_of_nonneg_right ha' (int.coe_nat_nonneg k),
    rw one_mul at this,
    refine le_trans (le_trans int.le_nat_abs _) this,
    rw [int.nat_abs_neg, int.coe_nat_le],
    exact nat.le_succ_of_le (le_max_right _ _) },
  rw [int.to_nat_of_nonneg x0, int.to_nat_of_nonneg y0],
  have := nat.gcd_eq_gcd_ab a b,
  rw [h, int.coe_nat_one] at this,
  rw [this, mul_sub, ← add_assoc, sub_add_cancel, mul_left_comm, ← mul_add],
end



-- alternative definitions of residue classes --

-- lean definition for residue class --
example (n : ℕ+) : units (zmod n) ≃ {x : zmod n // nat.coprime x.val n} :=
zmod.units_equiv_coprime

-- lean doesn't know if this is finite 
def rsc (n: nat) := {k: nat| k<n ∧ k.coprime n}


