import tactic

/--
`injective` Basic definition of injectivity.
-/
def injective {X Y} (f : X → Y) := ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂

/--
`comp_inj_is_inj` Demonstrates the composition of injective functions is injective.
-/
theorem comp_inj_is_inj 
{X Y Z} (f : X → Y) (g : Y → Z)
(p1 : injective f) 
(p2 : injective g) 
:  injective (g ∘ f)
:= 
begin
  introv x p3,
  change g (f x) = g (f x₂) at p3,
  apply p1,
  apply p2, 
  apply p3,
end

/--
`succ_greater_than_nat` Simple statement that n + 1 > n.
-/
lemma succ_greater_than_nat 
(n : ℕ) 
: nat.succ n > n
:= 
begin
  rw nat.succ_eq_add_one,
  linarith
end


/-
lemma my_le_trans
(j k m : ℕ)
(p1: k < m)
(p2: j ≤ k)
: j < m - 1
:=
begin
  intros,
  induction j with d hd, 
  {
    induction m with dm hdm,
    {exact lt_of_le_of_lt p2 p1},
    {
      sorry,
    }
  },
  {
    induction m with dm hdm,
    {linarith,},
    {
      sorry,
    }
  },
  
end
-/


lemma downward_ineq
(j m : ℕ)
(p: j < m)
(p2: 0 < j)
: j - 1 < m - 1
:= 
begin
  intros,
  exact nat.sub_mono_left_strict p2 p,
end


/--
Type of pairs (k,p) where k
is a natural number and p is a witness to the proof that k < n.
-/
def finite_subset (n : ℕ) := { k // k < n }

/--
Every pair that lives in finite_subest m lives in finite_subset n
where m < n
-/
def lift_finite 
(m n : ℕ) 
(p : m < n) 
: finite_subset m → finite_subset n
:= 
  λ k, ⟨k.1, lt.trans k.2 p⟩


/--
`lift_one` Application of lift_finite from m to m + 1
-/
def lift_one
(m : ℕ)
: finite_subset m → finite_subset (m + 1)
:= 
  (lift_finite m (m+1) (succ_greater_than_nat m))


/--
`lift_one_fst` Establishes that lifting preserves the first half of the pair.
-/
lemma lift_one_fst {m} (j : finite_subset m) : (lift_one m j).1 = j.1 
:=
begin
  refl,
end

/--
`ext_iff` Extensionality theorem for finite subsets as pairs.
-/
lemma ext_iff 
(n : ℕ) 
(a b : finite_subset n) 
: a = b ↔ a.1 = b.1 
:=
begin
  cases a,
  cases b,
  split,
  { intro h, rw h},
  { intro h, cases h, refl,}
end


/--
`lift_finite_injective` Demonstrates the lifting function is injective.
-/
theorem lift_finite_injective 
(m n : ℕ) 
(p : m < n) 
: injective (lift_finite m n p) 
:=
begin
  intros x₁ x₂ h,
  rw ext_iff at ⊢ h,
  exact h
end


/--
`lift_one_injective` Direct lemma of `lift_finite_injective`
-/
lemma lift_one_injective (m : ℕ) 
: injective (lift_one m) 
:= 
begin
  apply lift_finite_injective m (m + 1) (succ_greater_than_nat m),
end



lemma ge_zero_witness_k
(n k : ℕ )
(p : k ≥ 0)
(p3 : n > k)
: n > 0
:=
begin
exact lt_of_le_of_lt p p3,
end


lemma ge_zero
(k : ℕ)
: k ≥ 0
:= begin
exact bot_le,
end

lemma minus_one_both_sides_eq
{n m k : ℕ }
(p : k ≥ 0)
(p2 : m > k)
(p3 : n > k)
(p4: m - 1 = n - 1)
: m = n 
:=
begin
have m_ge_zero  := (ge_zero_witness_k m k p p2),
have n_ge_zero := (ge_zero_witness_k n k p p3), 
exact nat.pred_inj m_ge_zero n_ge_zero p4,
end

/--
`relabel` Given an element `⟨ k , k < m ⟩` that is missing from the a collection of
`finite_subset m`, this function can 'squash' the collection into
`finite_subset (m - 1)`.
-/
def relabel 
(m k : ℕ) 
(h : k < m) 
(j : finite_subset m) 
: finite_subset (m - 1) 
:=
  if H : j.1 ≤ k 
  then ⟨j.1, sorry⟩ 
  else ⟨j.1 - 1, downward_ineq j.1 m j.2 sorry⟩



/--
`miss_proof` Proof that `f : [m + 2] -> [m + 1]` restricted 
to `[m + 1] = {0, 1, ..., m}` does not hit `f (m + 1)`
-/
lemma miss_proof
(m : ℕ) 
(f : finite_subset (m + 2) → finite_subset (m + 1))
(inj : injective f)
(pf: m + 1 < m + 2)
: ∀ j : finite_subset (m + 1), (f ∘ lift_one (m + 1)) j ≠ f ⟨m + 1,  pf⟩
:= 
begin
  introv p,
  change f (lift_one (m+1) j) = f ⟨m + 1,  pf⟩ at p,
  let p2 := inj (lift_one (m+1) j) ⟨m + 1,  pf⟩,
  let p3 := p2 p,
  rw ext_iff at p3,
  rw lift_one_fst at p3,
  let p4 := j.2,
  linarith,
end

/--
`relabel_behavior` Given `m k : ℕ`, `h : k < m`, `x y : finite_subset m`,
and `(relabel m k h) x = (relabel m k h) y`, the `if-then-else` structure
of `relabel` yields that either the values of `x, y` must either be less than 
or equal to `k` or vice versa 
-/
lemma relabel_behavior 
(m k : ℕ) 
(h : k < m) 
(x y : finite_subset m) 
(hxy : relabel m k h x = relabel m k h y) 
: (x.1 ≤ k ∧ y.1 ≤ k) ∨ (x.1 ≥ k ∧ y.1 ≥ k) 
:=
begin
  unfold relabel at hxy,
  split_ifs at hxy with hxk hyk hyk,
  { 
    left; split; assumption 
  },
  { right; split,
    { rw subtype.mk_eq_mk at hxy,    
      cases lt_or_eq_of_le hxk with hxlk hxek,
      { 
        rw hxy at hxlk, 
        exact absurd (nat.le_of_pred_lt hxlk) hyk,
      },

      { 
        exact ge_of_eq hxek 
      }, 
    },

    { 
      exact le_of_not_ge hyk 
    },
  },
  { right; split,
    { 
      exact le_of_not_ge hxk 
    },

    { rw subtype.mk_eq_mk at hxy,
      cases lt_or_eq_of_le hyk with hylk hyek,
      { 
        rw ← hxy at hylk, exact absurd (nat.le_of_pred_lt hylk) hxk 
      },
      { exact ge_of_eq hyek 
      }, 
    },
  },

  { 
    right; split; apply le_of_not_ge; assumption 
  },


end


/--
`apply_relabel_lt` Lemma that describes the behavior of 
`relabel m k h` when the argument is less than `k`. 
-/
lemma apply_relabel_lt 
(m k : ℕ) 
(hkm : k < m) 
(z : finite_subset m)  
(h2 : z.1 ≤ k)
: (relabel m k hkm z).1 = z.1 :=
begin
  unfold relabel, 
  rw dif_pos h2,
end


/--
`apply_relabel_lt` Lemma that describes the behavior of 
`relabel m k h` when the argument is greater than `k`. 
-/
lemma apply_relabel_gt 
(m k : ℕ) 
(hkm : k < m) 
(z : finite_subset m) 
(h2 : k < z.1)
: (relabel m k hkm z).1 = z.1 - 1
:= 
begin
  unfold relabel,
  rw dif_neg (not_le_of_lt h2),
end

/--
`relabel_inj` This formalizes the notion that when `f` is injective and misses `k` 
in the codomain, then when we relabel to bring `m` to `m - 1`, 
composition is in fact injective.
-/
lemma relabel_inj (m k : ℕ) (hkm : k < m + 1) 
(f: finite_subset (m + 2) → finite_subset (m + 1)) 
(inj : injective f)
(pf : (f ⟨ m + 1, succ_greater_than_nat (m + 1)⟩ ).1 < m + 1) 
(miss : ∀ j : finite_subset (m + 1), (f ∘ lift_one (m + 1)) j ≠ f ⟨m + 1,  succ_greater_than_nat (m + 1)⟩ ) 
: injective ((relabel (m + 1) (f ⟨m + 1, succ_greater_than_nat (m + 1)⟩).1 pf) ∘ f ∘ lift_one (m + 1)) 
:=
begin
  intros x y h,
  change (relabel (m + 1) (f ⟨ m + 1, succ_greater_than_nat (m + 1)⟩ ).1 pf (f (lift_one (m + 1) x))) = (relabel (m + 1) (f ⟨ m + 1, succ_greater_than_nat (m + 1)⟩ ).1 pf (f (lift_one (m + 1) y))) at h,
  rcases relabel_behavior _ _ _ _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩; unfold relabel at h,
  { 
    rw [dif_pos h1, dif_pos h2, subtype.mk_eq_mk] at h, 
    rw ← subtype.ext at h,

    let comp_inj := comp_inj_is_inj (lift_one (m + 1)) f (lift_one_injective (m + 1)) inj,
    change (f ∘ lift_one (m + 1)) x = (f ∘ lift_one (m + 1)) y at h,
    apply comp_inj, 
    apply h,  
  },

  {
    have m_x := (miss x),
    replace m_x := mt subtype.eq m_x,
    have m_y := (miss y),
    replace m_y := mt subtype.eq m_y,

    have h1_strict := lt_of_le_of_ne h1 (ne.symm m_x),
    have h2_strict := lt_of_le_of_ne h2 (ne.symm m_y),

    rw dif_neg (not_le.mpr h1_strict) at h,
    rw dif_neg (not_le.mpr h2_strict) at h,

    let comp_inj := comp_inj_is_inj (lift_one (m + 1)) f (lift_one_injective (m + 1)) inj,

    rw ext_iff at h, 

    let k_ge_zero := ge_zero (f ⟨ m + 1, succ_greater_than_nat (m + 1)⟩).val,
    let h_final := minus_one_both_sides_eq k_ge_zero h1_strict h2_strict h,
    rw ← ext_iff at h_final, 
    apply comp_inj,
    apply h_final,
  },

end






/--
`pigeonhole_principle` The pigeonhole principle, which states
that among `n` pigeons, there must be at least `n` cages 
for the pigeons to reside in order for every pigeon to have its 
own unique page.  Stated more formally, the pigeonhole principle
asserts that there exists no injective function from any finite set
of `n` elements to any set with fewer than `n` elements.
-/
theorem pigeonhole_principle
(n m : ℕ)
(f : finite_subset n → finite_subset m)
: (n > m) → ¬(injective f)
:= 
begin

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
      let e:= f ⟨0,_ ⟩,
      let e2 := e.2,
      linarith,
      exact n_gt_m,
    },

    let k := f ⟨l + 1, succ_greater_than_nat (l + 1)⟩, 
    let violator := f ∘ (lift_one (l + 1)),
    let restriction := (relabel (l + 1) k.1 k.2) ∘ violator,
    let violator_is_inj := comp_inj_is_inj (lift_one (l + 1)) f (lift_one_injective (l + 1)) f_injective,
    let miss := miss_proof l f f_injective (succ_greater_than_nat (l + 1)),
    let res_is_inj := relabel_inj l k.1 k.2 f f_injective k.2 miss,

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