import tactic
import data.nat.prime
open nat

theorem simproot2 {x y : ℕ} (coprime : gcd x y = 1) : x^2 ≠ 2 * y^2 :=
  -- For Contradiction, will show false
  assume contr : x^2 = 2 * y^2,
  have twodivxsquare : 2 ∣ x^2,
  by exact dvd.intro (y ^ 2) (eq.symm contr),
  have twodivx: 2 ∣ x,
  from prime.dvd_of_dvd_pow prime_two twodivxsquare,
  exists.elim twodivx $
  assume (z : nat) (introz : x = 2 * z),
  have subst : 2 * (2 * z^2) = 2 * y^2,
  by 
  begin
  rw introz at contr,
  simp[eq.symm contr, nat.pow],
  simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
  end,
  have subst2 : 2 * z^2 = y^2,
  from eq_of_mul_eq_mul_left dec_trivial subst,
  have revsubst : y^2 = 2 * z^2,
  by rw ←subst2,
  have twodivysquare : 2 ∣ y^2,
  by exact dvd.intro (z ^ 2) (eq.symm revsubst),
  have twodivy: 2 ∣ y,
  from prime.dvd_of_dvd_pow prime_two twodivysquare,
  have fin : 2 ∣ gcd x y, 
  from dvd_gcd twodivx twodivy, 
  have last : 2 ∣ 1,
  from 
  begin
  rw coprime at fin,
  use fin,
  end,
  show false, 
  from absurd last dec_trivial
