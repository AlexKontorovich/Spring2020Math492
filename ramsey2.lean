  
import data.finset
import algebra.big_operators
import data.real.basic
import data.set.lattice

open finset
open nat

local notation `edges_of `X := powerset_len 2 X

universe u
variables {α : Type u} (G : finset α) {n : ℕ} [decidable_eq α]

lemma sum_const_nat {m : ℕ} {f : α → ℕ} {s : finset α} (h₁ : ∀x ∈ s, f x = m) :
  s.sum f = card s * m :=
begin
  rw [← nat.smul_eq_mul, ← sum_const],
  apply sum_congr rfl h₁
end

lemma exists_intermediate_set {A B : finset α} (i : ℕ)
  (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) :
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
  induction k with k ih,
    intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
  intros A BsubA cards,
  have: (A \ B).nonempty,
    rw [← card_pos, card_sdiff BsubA, ← cards, nat.add_right_comm, nat.add_sub_cancel, nat.add_succ],
    apply nat.succ_pos,
  rcases this with ⟨a, ha⟩,
  set A' := erase A a,
  have z: i + card B + k = card A',
    rw [card_erase_of_mem, ← cards, nat.add_succ, nat.pred_succ],
    rw mem_sdiff at ha, exact ha.1,
  rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
  refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩,
  rintros t th, apply mem_erase_of_ne_of_mem _ (BsubA th), rintro rfl,
  rw mem_sdiff at ha, tauto
end

/-- We can shrink A to any smaller size. -/
lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : card A ≥ i) :
  ∃ (B : finset α), B ⊆ A ∧ card B = i :=
begin
  rcases exists_intermediate_set i _ (empty_subset A) with ⟨B, _, x₁, x₂⟩,
  simp at x₂, exact ⟨B, x₁, x₂⟩, simpa,
end

def colourings : finset (finset (finset α)) := powerset (edges_of G)

lemma number_of_colourings (hn : card G = n) : card (colourings G) = 2^(choose n 2) :=
begin
    rw colourings,
    rw card_powerset,
    rw card_powerset_len,
    rw hn,
--  rw [colourings, card_powerset, card_powerset_len, hn]
end
