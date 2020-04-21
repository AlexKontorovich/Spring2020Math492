import tactic


def injective {X Y} (f : X → Y)
    := ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂


def range {X Y} (f : X → Y)
    := { y | ∃ x, f x = y }


/--
Type of pairs (k,p) where k
is a natural number and p is a witness to the proof that k < n.
-/
def finite_subset (n : ℕ) := Σ' k, k < n


def lift_finite (m n : ℕ) (p : m < n) : finite_subset m → finite_subset n
    := λ k, ⟨k.1, lt.trans k.2 p⟩


lemma pred_exists (n : ℕ) (p: n > 0) : exists k, nat.succ k = n
:=
begin
induction n with d hd,
{linarith,},
{ 
    existsi d, 
  refl
}
end


lemma succ_greater_than_nat (n : ℕ) : nat.succ n > n
:= 
begin
rw nat.succ_eq_add_one,
linarith
end


/--
The lifting function is injective
-/
theorem lift_finite_injective (m n : ℕ) (p : m < n) : injective (lift_finite m n p) 
:= begin


/- pf sketch 

--  suppose f x1 = f x2 = < k, pf: k < n >

--  we know x1 = < l , pf: k < m > and x2 = < j , pf: j < m >

--  note that (f x1).1 = (f x2).1 = k

--  furthermore, k < m < n 

--  then x1 = < k, pf: k < m > = x2

--  done
-/

introv x p2,
cases x,
cases x₂,
cases p2,
refl
end


theorem comp_inj_is_inj 
{X Y Z} (f : X → Y) (g : Y → Z)
(p1 : injective f) 
(p2 : injective g) 
:  injective (g ∘ f)
:= begin

introv x p3,
change g (f x) = g (f x₂) at p3,
apply p1,
apply p2, 
apply p3,
end


-- forgot library function, lifted from square root prime code
-- credit to github user dm1237
lemma succ_eq_add_one (n : ℕ) : nat.succ n = n + 1 := 
begin
    exact rfl,
end


theorem either_zero_or_not
(x y : ℕ)
: x = y ∨ x ≠ y
:= begin 
induction x with d hd,
cases y, 
{simp}, -- base case y = 0

{simp, 
 rw succ_eq_add_one,
  sorry},
{sorry}


end



lemma my_le_trans
(j k m : ℕ)
(p1: k < m)
(p2: j < k)
: j < m - 1
:=
begin

sorry
end

#print le_trans



lemma inequality_fact
(j m : ℕ)
(p: j < m)
: j - 1 < m - 1
:= begin
sorry
end

-- warning, sort of janky
-- ie, don't use if we don't miss k in the codomain
-- it's not injective by itself
-- but relabel k ∘ f ∘ lift IS injective
-- because f ∘ lift misses k
def relabel_finite_set 
(m k : ℕ) 
(p: k < m)
: finite_subset m → finite_subset (m - 1)
:= λ j, if H : j.1 < k then ⟨j.1, my_le_trans j.1 k m p H ⟩ else ⟨j.1 - 1, inequality_fact j.1 m j.2⟩



lemma relabel_miss_injectivity
(m k : ℕ) 
(p: k < m)
()
: relabel 



/--
Pigeonhole principle, induction on n
-/
theorem pigeonhole_principle
    (n m : ℕ)
    (f : finite_subset n → finite_subset m)
: (n > m) → ¬(injective f)
:= begin

  intros n_gt_m f_injective,
  induction n with d hd,
  { linarith, /- case d = 0 -/ },

  let succ_for_lift := (succ_greater_than_nat d),
  let lift := (lift_finite d (d+1) succ_for_lift),
  let g := f ∘ lift,
  let hd' := hd g,

  rcases lt_or_eq_of_le (nat.lt_succ_iff.1 n_gt_m) with h | rfl,

  {   /- case where d > m -/
      /- prove injective g -/ 
    apply hd' h,
    let lift_injective := (lift_finite_injective d (d+1) succ_for_lift),  
    let g_injective := comp_inj_is_inj lift f lift_injective f_injective,
    exact g_injective,
  },

  {   /- case where d = m -/
      /- prove f : finite_subset (nat.succ m) → finite_subset m is not injective -/ 
    let k := f ⟨m, succ_greater_than_nat m⟩, -- let k = f(m)
    

    sorry 
  }
 
end


#print pigeonhole_principle