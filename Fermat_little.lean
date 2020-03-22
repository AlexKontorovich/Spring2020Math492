
def divides (d n: ℤ):=  ∃l:ℤ, n = d*l
def is_congruent_mod_n (a b n: ℤ) := divides n (b-a)
def relatively_prime(a b:ℤ) := ∀l:ℤ, ¬(divides l a) ∨ ¬(divides l b)

-- Bézout 
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
  -- k: a*b = n*l;
  cases relatively_prime_sum_to_one a n d with m h,
  cases h with q manb_eq_one,
  -- m q : ℤ,
  -- manb_eq_one : m * a + q * n = 1

  -- multiplies both sides by b
  have := congr_arg (has_mul.mul b) manb_eq_one,
  -- this : b * (m * a + n' * n) = b * 1
  rw [mul_one] at this,
  -- this : b * (m * a + q * n) = b

  --annoying order-changing  
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
  rw <-mul_sub at k,
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



--residue class :( -- 
def reduced_residue_class (p: ℤ):= sorry
/-
Suggestions from zulip:

units (zmod n)
{ k : nat | k < n \and k.coprime n }
(finset.range n).filter $ assume k, k.coprime n

-/

