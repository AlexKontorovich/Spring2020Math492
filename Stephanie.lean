import analysis.normed_space.basic
import topology.instances.ennreal
import analysis.normed_space.basic
import topology.instances.ennreal
import algebra.archimedean algebra.geom_sum
import data.nat.choose data.complex.basic
import tactic.linarith
import analysis.calculus.deriv
import data.complex.exponential

open finset
open cau_seq
namespace complex
noncomputable theory


lemma is_cau_abs_cos (z : ℂ) : is_cau_seq _root_.abs
  (λ n, (range n).sum (λ m, abs (
      ((-1) ^ m) * z ^ (2 * m ) / nat.fact (2 * m )))) :=
begin
sorry,
end

lemma is_cau_abs_sin (z : ℂ) : is_cau_seq _root_.abs
  (λ n, (range n).sum (λ m, abs (
      ((-1) ^ m) * z ^ (2 * m + 1) / nat.fact (2 * m + 1)))) :=
begin
sorry,
/-
let ⟨n, hn⟩ := exists_nat_gt (abs z) in
have hn0 : (0 : ℝ) < n, from lt_of_le_of_lt (abs_nonneg _) hn,
series_ratio_test n (complex.abs z / n) 
(div_nonneg_of_nonneg_of_pos (complex.abs_nonneg _) hn0)
  (by rwa [div_lt_iff hn0, one_mul])
  (λ m hm,
    by rw [abs_abs, abs_abs, nat.fact_succ, pow_succ,
      mul_comm m.succ, nat.cast_mul, ← div_div_eq_div_mul, mul_div_assoc,
      mul_div_right_comm, abs_mul, abs_div, abs_cast_nat];
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_le_left (abs_nonneg _) hn0
        (nat.cast_le.2 (le_trans hm (nat.le_succ _)))) (abs_nonneg _))
-/
end

lemma is_cau_sin (z : ℂ) :
 is_cau_seq abs (λ n, (range n).sum (λ m, 
 ((-1) ^ m) * z ^ (2 * m + 1) / nat.fact (2 * m + 1))) 
:=
begin
    exact is_cau_series_of_abv_cau (is_cau_abs_sin z),
end

lemma is_cau_cos (z : ℂ) :
 is_cau_seq abs (λ n, (range n).sum (λ m, 
 ((-1) ^ m) * z ^ (2 * m ) / nat.fact (2 * m))) 
:=
begin
    exact is_cau_series_of_abv_cau (is_cau_abs_cos z),
end

def sin' (z : ℂ) : cau_seq ℂ complex.abs :=
 ⟨λ n, (range n).sum 
 (λ m, ((-1) ^ m) * z ^ (2 * m + 1) / nat.fact (2 * m + 1)), 
 is_cau_sin z⟩
def sin1 (z : ℂ) : ℂ := lim (sin' z)

def cos' (z : ℂ) : cau_seq ℂ complex.abs :=
 ⟨λ n, (range n).sum 
 (λ m, (-1) ^ m * z ^ (2 * m) / nat.fact (2 * m)), 
 is_cau_cos z⟩
def cos1 (z : ℂ) : ℂ := lim (cos' z)

/-
lemma series_arith : --maybe take the first few terms and conjecture that the rest of the series follows?
(λ n)(λ m) 
-/



theorem euler : ∀ x, exp (x * I) = cos1 x + sin1 x * I 
:= 
begin
    intros,

    -- figure out the right way to do indices here...
    have partials: ∀ n:ℕ , (exp' (x*I)).1 (2*n+1) =
     (cos' x).1 n + ((sin' x).1 n) * I,
    {
        intros,
        rw exp',
        simp,
        rw cos',
        simp,
        rw sin',
        simp,

        induction n with n0 hn,
        { -- case n0=0
            sorry,
--            simp,
        },
        { -- induction on n0

            rw sum_range_succ _ _,
            rw sum_range_succ _ _,
            rw sum_range_succ _ _,
            rw hn,
            simp,
            ring,

/-        
            have l1: 
            sum (range (nat.succ n0)) (λ (m : ℕ), 
            (x * I) ^ m / ↑(nat.fact m)) =
            (x * I) ^ n0 / ↑(nat.fact n0) + 
            sum (range ( n0)) (λ (m : ℕ), 
            (x * I) ^ m / ↑(nat.fact m)),
            {
                exact sum_range_succ _ _,
            },



            have l2: 
            sum (range (nat.succ n0)) (λ (m : ℕ), 
            (-1) ^ m * x ^ (2 * m) / ↑(nat.fact (2 * m))) =
            (-1) ^ n0 * x ^ (2 * n0) / ↑(nat.fact (2 * n0))
            + sum (range ( n0)) (λ (m : ℕ), 
            (-1) ^ m * x ^ (2 * m) / ↑(nat.fact (2 * m))), 
            {
                exact sum_range_succ _ _,
            },

            rw l1,
            rw l2,
-/
        },
/-
        have sum2 : ∀ f g,  (range n).sum f + (range n).sum g = 
        (range n).sum (f+g),
        {
            intros,
            sorry,
        },

        rw sum2 ((cos' x).1)  (λ k, ((sin' x).1 k) * I),
-/
    }
 --rw → linarith
end

end complex
