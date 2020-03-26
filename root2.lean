/- Very unfinished, Will finish by end of term -/

import data.rat.basic
import data.nat.prime
import data.real.basic


open nat algebra

variables a b : ℕ
variable x : ℝ

def root2 (x : ℝ) := (x^2 = 2)
def is_rat (x : ℝ) Prop := ∃ a : ℕ ∃ b : ℤ, x = a / b


/-
theorem root2_irrat (rt : root2 x) (a b : ℕ):  ¬ is_rat x :=
assume is_rat x,
exists.elim h (fun (a b: ℕ) (hw1 : x = a / b), 
  begin
    sorry
  end
) 
-/


def even (n : ℕ) : Prop := ∃ m, n = 2 * m
def odd (n : ℕ) : Prop := ∃ m, n = 2 * m + 1


lemma not_even_and_odd (n : ℕ) : ¬((even n) ∧ (odd n)) := 
sorry



lemma not_even_and_odd (n : ℕ) : ¬((even n) ∧ (odd n)) :=
assume (h : even n ∧ odd n),
have he: even n, from h.left,
have ho: odd n, from h.right,
have ev: ∃ m, n = 2 * m, from he,
have od: ∃ m, n = 2 * m + 1, from ho,

exists.elim ev (fun (m1 : ℕ) (h1 : n = 2 * m1), 
exists.elim od (fun (m2 : ℕ) (h2 : n = 2 * m2 + 1),
begin
eq.trans (eq.symm h1) h2

end
)) 


lemma even_square_even_root {n m: ℕ} (n = m^2) (e: even n) : even m :=
exists.elim e (assume m1, assume hw1 : n = 2 * m1,
begin
/- Requires prime number theory or claim that not even = odd-/
sorry
end)


theorem root2_irrat {a b asq bsq : ℕ} (gcd_1 : gcd a b = 1) (p: asq = a^2) (q: bsq = b^2): asq ≠ 2 * bsq :=
assume (h : asq = 2 * bsq),
have evasq : even asq := 
begin
  rw even,
  /- exists.elim bsq  -/
  sorry
end,
have eva : even a := 
begin
/- apply even_square_even_root asq p -/
sorry
end,

