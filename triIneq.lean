import tactic
import data.int.basic

universe u
--local attribute [instance] classical.prop_decidable
def absVal (a : ℤ) : ℤ := if a < 0 then -a else a

theorem triIneqInt (a : ℤ) (b : ℤ) 
: (absVal(b - a) ≤ absVal(a) + absVal(b)) :=
begin
rw absVal,
rw absVal,
rw absVal,
split_ifs,
linarith,
linarith,
linarith,
linarith,
linarith,
linarith,
linarith,
linarith,
end

--def absValAlt : ℤ → ℕ
--| (int.of_nat n) := n
--| (int.neg_succ_of_nat n) := n + 1