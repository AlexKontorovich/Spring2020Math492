import data.nat.gcd
import algebra.big_operators


import data.zmod.basic

def divides (d n: ℤ):=  ∃l:ℤ, n = d*l
def is_congruent_mod_n (a b n: ℤ) := divides n (b-a)
def relatively_prime(a b:ℤ) := ∀l:ℤ, 
l≥ 2 → (divides l a) → ¬(divides l b)

theorem relatively_prime_sum_to_one (a b : ℤ) (h : relatively_prime a b) : 
∃ m n: ℤ, m* a + n * b = 1 := 
begin
  sorry,
end

--helper theorem that is not true :(--
-- the iff is not true, but I can't use it without it--
theorem divides_in_product (a c: ℤ): (∃ b:ℤ , a*b = c) ↔ divides a c:= 
begin
  split,
  {
    intros,
    rw divides,
    cases a_1 with ell,
    --by library_search,
    exact Exists.intro ell (eq.symm a_1_h),
  },
  {
    intros,
    cases a_1 with ell,
    --by library_search,
    exact Exists.intro ell (eq.symm a_1_h),
  },
end

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

  rw divides,
  --by library_search,
  exact Exists.intro (q * b + l * m) (eq.symm this),
--  rw divides_in_product n (q*b+l*m) b at this, -- can use "apply" instead and get rid of iff

end

lemma xyz : ∀ x y z:ℤ, x*y*z = y*x*z:=
begin
  intros,
  have xy: x*y = y*x, 
  {
    rw mul_comm,
  },
  rw xy,
end

theorem cancel_out_mod_n (a b c n: ℤ) (p: is_congruent_mod_n (a*b) (a*c) n)
(q: relatively_prime a n) : is_congruent_mod_n b c n :=
-- need a!=0; n≥ 2...!!!
begin
  cases p with j k,
  rw <-mul_sub at k,  --does not work if I convert to naturals
  rw eq_comm at k,

  rw is_congruent_mod_n,
  rw divides,

  have mExists : ∃ m:ℤ , a*m=j,
  {
    have bezout : ∃ u v :ℤ, u*a + v*n =1,
    {
      --by library_search,
      exact relatively_prime_sum_to_one a n q,
    },
    cases bezout with u vv,
    cases vv with v bezout,

    use u  * j + v * (c - b)   ,

    have rw1: a * (u * j + v * (c - b)) = a * (u * j) + a * (v * (c - b)),
    {
      --by library_search,
      exact mul_add a (u * j) (v * (c - b)),
    },
    rw rw1,
    clear rw1,

    have rw2: a * (u * j) + a * (v * (c - b)) = 
    a * (u * j) + a *  v * (c - b),
    {
      --by library_search, 
      sorry,
    },
    rw rw2,


    sorry,
/-
    have timesJ : (u * a  + v * n)*j = 1*j,
    {
      --by library_search,
      exact congr_fun (congr_arg has_mul.mul bezout) j,
    },


    have rw11: (u * a + v * n) * j = u * a *j + v * n * j ,
    {
      --by library_search,
      exact add_mul (u * a) (v * n) j,
    },
    
    have rw2: u * a * j + v * n * j = 1*j,
    {
      --by library_search,
      exact (eq.congr rfl timesJ).mp (eq.symm rw1),
    },

    have rw3: u * a * j + v * n * j = j,
    {
--      by library_search, 
      sorry,
    },
    
    sorry,
--    m=
-/
  },
  cases mExists,

  rw eq_comm at mExists_h,

  rw mExists_h at k,

  rw ← mul_assoc at k,

  use mExists_w,

  have rw1: n * a * mExists_w 
  =
  a* n * mExists_w ,
  {
    exact xyz n a mExists_w,
  },
  rw rw1 at k,
  symmetry,
  


  sorry,
/-
  rw divides_in_product n j (a*(c-b)) at k,  -- cannot use "apply" and get rid of iff
  apply divides_product_coprime_and_not_coprime a (c-b) n,
  {
    apply k,
  },
  {
    apply q,
  },
-/
end

--bad definition
def rsc (n: nat) := {k: nat| k<n ∧ k.coprime n}

-- Zulip definition for residue class --
example (n : ℕ+) : units (zmod n) ≃ {x : zmod n // nat.coprime x.val n} :=
zmod.units_equiv_coprime