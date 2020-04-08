import tactic
import data.real.basic

universe u
--local attribute [instance] classical.prop_decidable
noncomputable def absVal (a : ℝ) : ℝ := if a < 0 then -a else a

theorem triIneqInt (a : ℝ) (b : ℝ) 
: (absVal(b - a) ≤ absVal(a) + absVal(b)) :=
begin
repeat {rw absVal},
split_ifs,
repeat {linarith},
end

def absValAlt : ℤ → ℕ
| (int.of_nat n) := n
| (int.neg_succ_of_nat n) := n + 1