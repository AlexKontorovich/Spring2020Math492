import data.nat.basic
import data.int.basic
import data.rat.basic

import algebra.field_power

import tactic


--@fpow_sub specifies all parameters, not just the explicit ones. Makes reading #checks easier

#check fpow_sub
#check @fpow_sub


--Suggest is inexact, unlike library_search
--But it is useful in its inexactness: since you know approximately what the name of the theorem youre looking
--for is, you can miss certain parameters like (a > 0) you may have forgotten and still find what you need

example (a b : ℕ) : 2^(a + b) = 2^a * 2^b := by exact nat.pow_add 2 a b
example (a b : ℤ) : (2 : ℚ)^(a - b) = (2 : ℚ)^a / (2 : ℚ)^b := by exact fpow_sub two_ne_zero a b
example (a b c: ℚ) (h : b ≠ 0) : a / b * c = a * c / b := 
begin
    by exact mul_right_comm a b⁻¹ c
end

/--/

lemma num_2_cols_Kn_with_mono_Kk_lt_num_2_cols_Kn
    (n k : ℕ) (h : 2^(1 - k.choose(2)) * n.choose(k) < 1) :
    2^(n.choose(2) - k.choose(2)) * 2 * n.choose(k) < 2^(n.choose(2)) :=
begin
    have a : ℤ := (n.choose(2) : ℤ),
    
end

-/

--calc
--    2^(a - b) * 2 * c = (2^a / 2^b) * 2 * c : by suggest --by rw fpow_sub two_ne_zero a b


/-
    ... = 2^a * 2 / 2^b * c 
    ... = 2^a * 2^(1 - b) * c 
    ... < 2^a * 1
    ... = 2^a : by mul_one

    
    --Todo: Nest calc within, change a, b, c from inputs to have's
-/

--(n k : ℕ) {a : (n.choose(2) : ℤ)} {b : (k.choose(2) : ℤ)} (c : n.choose(k)) 

lemma strict_ineq
    (a b c : ℤ)
    (h : (2^(1 - b) * c : ℚ) < 1) :
    (2^(a - b) * 2 * c : ℚ) < 2^a :=
begin 
    rw fpow_sub two_ne_zero a b
    
end
