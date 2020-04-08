
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
{sorry},
{ existsi d, 
  refl}
end


lemma succ_greater_than_nat (n : ℕ) : nat.succ n > n

:= 
begin
induction n with d hd,
{sorry},
{sorry}
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
    induction m with d hd,
    { 
         cases pred_exists n n_gt_m with k hk,
         let n_gt_k := succ_greater_than_nat k,
         rw hk at n_gt_k,
         let fk := f ⟨k, n_gt_k⟩,
         let fk2 := fk.2,
         sorry
    },

    {
        sorry    
    },
    
    
end


#print pigeonhole_principle
