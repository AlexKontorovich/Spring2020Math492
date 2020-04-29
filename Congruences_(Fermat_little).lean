import data.nat.gcd
import algebra.big_operators
import data.int.gcd
import algebra.euclidean_domain
import data.zmod.basic

def divides (d n: ℤ):=  ∃l:ℤ, n = d*l
def is_congruent_mod_n (a b n: ℤ) := divides n (b-a)
def relatively_prime(a b:ℤ) :=  nat.coprime (int.nat_abs a) (int.nat_abs b)

theorem relatively_prime_sum_to_one (a b : ℤ) (h : relatively_prime a b) : 
∃ m n: ℤ, m* a + n * b = 1 :=  
begin
  existsi [int.sign a * nat.gcd_a (int.nat_abs a) (int.nat_abs b),
           int.sign b * nat.gcd_b (int.nat_abs a) (int.nat_abs b)],
  rw [mul_right_comm, mul_comm _ a, int.mul_sign,
      mul_right_comm, mul_comm _ b, int.mul_sign,
      ← nat.gcd_eq_gcd_ab,
      show nat.gcd (int.nat_abs a) (int.nat_abs b) = 1, from h,
      int.coe_nat_one],
end


theorem divides_in_product (a b c: ℤ): a*b = c ↔ divides a c:= 
  begin
    split,
    {
      intros,
      rw divides,
      cases a_1 with ell,
      exact Exists.intro b rfl,
    },
    {
      intros,
      cases a_1 with ell,
      by library_search,
      --exact Exists.intro ell (eq.symm a_1_h),
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
  have := congr_arg (has_mul.mul b) manb_eq_one, 
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

  rw divides_in_product n (q*b+l*m) b at this, 
  apply this,

end


theorem cancel_out_mod_n (a b c n: ℤ) (p: is_congruent_mod_n (a*b) (a*c) n)
(q: relatively_prime a n): is_congruent_mod_n b c n :=

begin
  cases p with j k,
  rw <-mul_sub at k,  
  rw eq_comm at k,
  rw divides_in_product n j (a*(c-b)) at k,  
  apply divides_product_coprime_and_not_coprime a (c-b) n,
  {
    apply k,
  },
  {
    apply q,
  },

end



