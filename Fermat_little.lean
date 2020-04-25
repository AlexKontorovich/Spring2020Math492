import data.nat.gcd
import algebra.big_operators


import data.zmod.basic

def divides (d n: ℤ):=  ∃l:ℤ, n = d*l
def is_congruent_mod_n (a b n: ℤ) := divides n (b-a)
def relatively_prime(a b:ℤ) := ∀l:ℤ, ¬(divides l a) ∨ ¬(divides l b)

theorem relatively_prime_sum_to_one (a b : ℤ) (h : relatively_prime a b) : 
∃ m n: ℤ, m* a + n * b = 1 := 
by library_search,

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

--bad definition
def rsc (n: nat) := {k: nat| k<n ∧ k.coprime n}

-- Zulip definition for residue class --
example (n : ℕ+) : units (zmod n) ≃ {x : zmod n // nat.coprime x.val n} :=
zmod.units_equiv_coprime
