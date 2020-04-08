
import tactic
import data.real.basic

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

#print nat.sub_le

#print nat.lt_succ_of_le

#print nat.sub_lt_succ

#print nat.


lemma pred_exists (n : ℕ) (p: n > 0) : exists k, nat.succ k = n
:=
begin
/-
    start with k:ℤ set k=n-1 but k>= 0 so k :ℕ 

let k:ℤ := n-1,
let k_ge_zero : k ≥ 0 :=
begin
    sorry,
end,
-/
induction n with d hd,
{linarith,},
{ 
    existsi d, 
  refl}
end


lemma succ_greater_than_nat (n : ℕ) : nat.succ n > n
:= 
begin
rw nat.succ_eq_add_one,
linarith,
/-
--exact nat.less_than_or_equal,
induction n with d hd,
{exact nat.zero_lt_one,
},
{
    rw nat.succ_eq_add_one,
    simp,
    sorry,
--    nat.less_than_or_equal
--    exact nat.lt_of_succ_lt,
}
-/
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

    linarith, -- case d=0

    let g := f∘ (lift_finite d (d+1) (succ_greater_than_nat d)),

    let hd' := hd g,

    /-
    induction m with d hd,
    { 
         cases pred_exists n n_gt_m with k hk,
         let n_gt_k := succ_greater_than_nat k,
         rw hk at n_gt_k,
         let fk := f ⟨k, n_gt_k⟩,
         let fk2 := fk.2,
         linarith,
    },

    {
        let n_gt_d : n>d :=
        begin
            exact lt.trans (succ_greater_than_nat d)  n_gt_m,
        end,



        sorry    
    },
    
    -/
end


#print pigeonhole_principle
