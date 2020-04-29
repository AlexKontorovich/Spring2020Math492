import tactic


def injective {X Y} (f : X → Y) := ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂


def range {X Y} (f : X → Y) := { y | ∃ x, f x = y }


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


lemma succ_greater_than_nat (n : ℕ) : nat.succ n > n
:= 
begin
  rw nat.succ_eq_add_one,
  linarith
end


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


-- forgot library function, lifted from square root prime code
-- credit to github user dm1237
lemma succ_eq_add_one (n : ℕ) : nat.succ n = n + 1 := 
begin
    exact rfl,
end

-- forgot library function
lemma my_le_trans
(j k m : ℕ)
(p1: k < m)
(p2: j < k)
: j < m - 1
:=
begin
  intros,
  -- try induction?
  sorry,
end

-- I'm not gonna waste time proving this
lemma inequality_fact
(j m : ℕ)
(p: j < m)
(p2: 0 < j)
: j - 1 < m - 1
:= begin
  intros,
--  by library_search,
  exact nat.sub_mono_left_strict p2 p,
--sorry
end

/--
Type of pairs (k,p) where k
is a natural number and p is a witness to the proof that k < n.
-/
def finite_subset (n : ℕ) := Σ' k, k < n

/--
Every pair that lives in finite_subest m lives in finite_subset n
where m < n
-/
def lift_finite (m n : ℕ) (p : m < n) : finite_subset m → finite_subset n
    := λ k, ⟨k.1, lt.trans k.2 p⟩


/--
Application of lift_finite from m to m + 1
-/
def lift_one
(m : ℕ)
: finite_subset m → finite_subset (m + 1)
:= (lift_finite m (m+1) (succ_greater_than_nat m))



/--
The lifting function is injective
-/
theorem lift_finite_injective (m n : ℕ) (p : m < n) :
 injective (lift_finite m n p) 
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
refl,
end


/--
The lifting from m to m + 1 injective
-/
lemma lift_one_injective (m : ℕ) 
: injective (lift_one m) 
:= begin
apply lift_finite_injective m (m + 1) (succ_greater_than_nat m),
end



-- warning, sort of janky
-- ie, don't use if we don't miss k in the codomain
-- it's not injective by itself
-- but relabel k ∘ f ∘ lift IS injective
-- because f ∘ lift misses k
lemma relabel
(m k : ℕ) 
(p: k < m)
: finite_subset m → finite_subset (m - 1)
:= 
begin
  intros j,

  let a:= j.1,

  have H : ((a < k) ∨ (k ≤ a )),
  {
--    by library_search,
    exact lt_or_ge (a) k,
  },

  sorry,

  cases H,
  {

  }
  {

  }

/-
λ j, 
if H : j.1 < k 
then ⟨j.1, my_le_trans j.1 k m p H ⟩ 
else ⟨j.1 - 1, inequality_fact j.1 m j.2 ⟩
-/
end

/-
This formalizes the notion that when f is injective and misses k 
in the codomain then when we relabel to bring m to m - 1, 
composition is injective
-/
lemma relabel_with_inj_f_misses_k_is_inj
(m k : ℕ) 
(p: k < m)
(f: finite_subset m → finite_subset m)
(inj: injective f)
: injective ((relabel m k p) ∘ f)
:=
begin
  intros x,
  intros,

  sorry,
end


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


  let g := f ∘ (lift_one d),
  let hd' := hd g,

  rcases lt_or_eq_of_le (nat.lt_succ_iff.1 n_gt_m) with h | rfl,

  {   /- case where d > m -/
      /- prove injective g -/ 
    apply hd' h, 
    let g_injective := comp_inj_is_inj (lift_one d) f (lift_one_injective d) f_injective,
    exact g_injective,
  },

  {   /- case where d = m -/
      /- prove f : finite_subset (nat.succ m) → finite_subset m is not injective -/ 

    induction m with l hl,
    
    {
      let e:= f ⟨0,_ ⟩  ,
      let e1 := e.1,
      let e2 := e.2,
      linarith,
      exact n_gt_m,
--      sorry,
    }, -- need to recall the proof we gave before


    let k := f ⟨l + 1, succ_greater_than_nat (l + 1)⟩, -- let k = f(l + 1)
    let violator := f ∘ (lift_one (l + 1)),
    let restriction := (relabel (l + 1) k.1 k.2) ∘ violator,
    let violator_is_inj := comp_inj_is_inj (lift_one (l + 1)) f (lift_one_injective (l + 1)) f_injective,
    let res_is_inj := relabel_with_inj_f_misses_k_is_inj (l + 1) k.1 k.2 violator violator_is_inj,
    /- contradiction, since restriction: [m] →  [m - 1] is injective,
     but this can't be true IH
     -/
    refine hl _ _ _ _ ,
    {
      intros,
      linarith,
    },
    {
      exact restriction,
    },
    {
      exact succ_greater_than_nat _,
    },
    {
      exact res_is_inj,
    },

  }
 
end


#print pigeonhole_principle