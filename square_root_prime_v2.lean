import tactic
import data.nat.prime
import data.int.basic
open classical 
-- HUMAN PROOF 1:
--Claim: Let n > 1. If n has no positive PRIME factor less ≤ sqrt(n), then n is prime
-- Proof by Contradiction: 
-- Suppose n is not prime. Then n has atleast two positive prime factors p1 and p2 such that 
-- n = p1p2*k for some positive integer k. By hypothesis p1 and p2 are > sqrt(n). Then 
-- n = p1p2*k ≥ p1p2 > n, and so n > n. Contradiction 

-- HUMAN PROOF 2:
-- Claim: Let n > 1. If n has no positive PROPER factor less ≤ sqrt(n), then n is prime
-- Proof my Contrapositive:
-- Suppose that n is composite. Then n = a*b where a ≤ b and b < n. Hence a^2 ≤ ab = n. 
-- Hence a ≤ sqrt(n). 


--Important theorems adapted from the Natural Number Game------------------------------
theorem ge_iff_exists_add (a b: ℕ): a ≥ b ↔ ∃ (c: ℕ), a = b + c := 
begin
    apply le_iff_exists_add,  -- Ok, maybe this theorem was a little bit silly :)
end

def greater (a b: ℕ): Prop := a ≥ b ∧ a ≠ b

--axiom zero (a : ℕ): a < 1 ↔ a =0 

lemma zero (a : ℕ): a < 1 ↔ a =0 := 
begin
    split,

--    by library_search,
    exact nat.sub_eq_zero_of_le,

    intros h,
    linarith,
end

--axiom zero2 (a u : ℕ): u + a = u ↔ a = 0

lemma zero2 (a u : ℕ): u + a = u ↔ a = 0 :=
begin
    split,

    intros h,

--    by library_search,
    exact (add_left_inj u).mp h,

    intros h1,
--    by library_search,
    exact eq.trans (congr_arg (has_add.add u) h1) rfl,
end


theorem g_iff_exists_add (a b: ℕ): greater a b ↔ ∃ (c: ℕ), a = b + c ∧ c ≥ 1:= 
begin                             --Perhaps a little bit overkill
    rw greater,
    rw ge_iff_exists_add,
    rw ne_from_not_eq,

    split,

    { intro h,
        have h_left: ∃ (c : ℕ), a = b + c, from and.left h,
        have h_right: ¬a = b, from and.right h,

        cases h_left with u hu,
        use u,

        split,
        apply hu,

        

        by_contradiction,
        push_neg at a_1,
        rw zero at a_1,
        subst a_1,
        rw add_zero at hu,


--        have h_right: a ≠ b, from and.right h,
        exact h_right hu,
    },
    {  intro h2,

        cases h2 with u hu,
        have hu_left: a = b+u, from and.left hu,
        split,
        use u,
        apply hu_left,

        by_contradiction,
        subst hu_left,
        rw zero2 at a_1,
        rw ← zero at a_1,
        have hu_right: u ≥ 1, from and.right hu,
        linarith,  -- Thanks Olu :)
    }   

end

theorem my_simp (u v a : ℕ): u*v + (a*a + u*a) = a*u + (u*v + a*a):= 
begin
    rw ← add_assoc,
    rw ← add_assoc,
    rw add_comm,
    simp,
    rw mul_comm,
end
-----------------------------------------------------------------------------------------
def dvd (m n: ℕ): Prop := ∃ k, n = m * k
def prime (p : ℕ) : Prop := p ≥ 2 ∧ ∀ n, dvd n p → n = 1 ∨ n = p
def composite (d : ℕ): Prop:= ∃ (a b: ℕ), d = a*b ∧ a ≤ b ∧ b < d

lemma greater_than_not_zero (n : ℕ)(n ≥ 2): n ≠ 0:=
begin
    exact lattice.ne_bot_of_gt H,
end

lemma dvd_n_less_than_n (u n : ℕ) (ha: dvd u n) (hb: u ≠ 1) (hc: u ≠ n) (hn : n ≠ 0) : u < n :=
begin
  refine lt_of_le_of_ne _ hc,
  rcases ha with ⟨k, rfl⟩,
  simpa using nat.mul_le_mul_left _ (_:1≤_),
  refine nat.pos_iff_ne_zero.2 (mt _ hn),
  rintro rfl, refl,
end

--- The grand unification lemma ----
lemma either_prime_or_composite (n:ℕ ) (ge: n≥ 2): (¬ (prime n) ↔ composite n) :=
begin
    split,
    {
        intros h,
        rw prime at h,
        rw composite,

        push_neg at h,

        cases h,
        {
            linarith,
        } ,
        {
            cases h with u hu,
           let hu_left:= hu.1,
           rw dvd at hu_left,
           cases hu_left with k hk,

           have u_g_k : (u≤ k)∨ (u>k),
           {
--               by library_search,
                exact le_or_lt u k,
           },
           cases u_g_k,
            {
                use u,
                use k,
                split,
                exact hk,
                split,
                exact u_g_k,

                let hu_mid:= hu.2.1,

                have u_ge_1 : (u≥ 1),
                {
                    by_contradiction,
                    have u_zero: u=0,
                    {
                        linarith,
                    },
                    have n_zero: n=0,
                    {
                        subst u_zero,
                        simp at hk,
                        exact hk,
                    },
                    linarith,
                },
                have u_ge_2 : (u≥ 2),
                {
                    by_contradiction,
                    have u_less_2 : u<2,
                    {
                        linarith,
                    },
                    have u_eq_1: u=1,
                    {
                        linarith,
                    },
--                    by library_search,
                    exact hu_mid u_eq_1,
                },
                by_contradiction,

                have k_ge_n: k≥ n,
                {
                    linarith,
                },
                have uk_ge_2n: u*k≥ 2* n,
                {
--                    by library_search,
                    exact canonically_ordered_semiring.mul_le_mul u_ge_2 k_ge_n,
                },
                have n_ge_2n: n≥ 2*n,
                {
                    linarith,
                },
                have twon_gt_n: 2*n > n,
                {
                    linarith,
                },
                linarith,
                
            },
            {
                use k,
                use u,
                split,
                rw mul_comm at hk,
                exact hk,
                split,
                --exact u_g_k,

                let hu_mid:= hu.2.1,

                have u_ge_1 : (u≥ 1),
                {
                    by_contradiction,
                    have u_zero: u=0,
                    {
                        linarith,
                    },
                    have n_zero: n=0,
                    {
                        subst u_zero,
                        simp at hk,
                        exact hk,
                    },
                    linarith,
                },
                have u_ge_2 : (u≥ 2),
                {
                    by_contradiction,
                    have u_less_2 : u<2,
                    {
                        linarith,
                    },
                    have u_eq_1: u=1,
                    {
                        linarith,
                    },
--                    by library_search,
                    exact hu_mid u_eq_1,
                },
                by_contradiction,

                have k_ge_n: k≥ n,
                {
                    linarith,
                },
                have uk_ge_2n: u*k≥ 2* n,
                {
--                    by library_search,
                    exact canonically_ordered_semiring.mul_le_mul u_ge_2 k_ge_n,
                },
                have n_ge_2n: n≥ 2*n,
                {
                    linarith,
                },
                have twon_gt_n: 2*n > n,
                {
                    linarith,
                },
                linarith,
                
                have ha: dvd u n, from and.left hu,
                have h2: u ≠ 1 ∧ u ≠ n, from and.right hu,
                have hc: u ≠ n, from and.right h2,
                have hb: u ≠ 1, from and.left h2,
                have hn: n ≠ 0,
                {
                    exact lattice.ne_bot_of_gt ge,
                },
                
                apply dvd_n_less_than_n,
                have h4: dvd u n, from and.left hu,
                apply h4,
                apply hb,
                apply hc,
                apply hn,  
            },

        }
        
    },
    {
      intros h,
      rw composite at h,
      by_contradiction,
      rw prime at a,

      cases h with a1 ha1,
      cases ha1 with b hb,
      
      have h1: n = a1*b, from and.left hb,
      have temp: a1 ≤ b ∧ b < n, from and.right hb,
      have h2: a1 ≤ b, from and.left temp,
      have h3: b < n, from and.right temp,

      have hc := a.right b,

      have b_isnt_one: b ≠ 1,
      {
        by_contradiction,
        push_neg at a_1,
        subst a_1,
        rw mul_one at h1,
        linarith,
      },
     
      have b_divides_n: dvd b n,
      {
          rw dvd,
          rw mul_comm at h1,
          use a1,
          rw h1,
      },

      have b_is_trivial: b = 1 ∨ b = n,
      {
        exact hc b_divides_n,
      },

      cases b_is_trivial,
      {
          exact b_isnt_one b_is_trivial,
      },
      {
          linarith,
      },

    },
end


theorem ge_refl(x : ℕ) : x ≥ x :=
begin
    linarith,

--    
end

theorem ge_cancel (a b : ℕ) (ha : a*b ≥ a) (hb: a ≥ 1) : b ≥ 1 :=
begin
    by library_search,
--exact (le_mul_iff_one_le_right hb).mp ha,


end

theorem example1 (a b c :ℕ) (hba: b ≥ a) (hca: c ≥ a) : b*c ≥ a*a :=
begin 
    exact canonically_ordered_semiring.mul_le_mul hba hca,
--    by library_search,
/-
    
-/
end 

-- Adapted from the Natural Number Game---
lemma one_eq_succ_zero: 1 = nat.succ(0) := 
begin
    refl,   -- OK maybe a little bit silly :)
end

lemma succ_eq_add_one (n : ℕ) : nat.succ n = n + 1 := 
begin
    exact rfl,
--    by library_search,

--    
end
----------------------------------------------------------------------
lemma x_plus_stuff_plus_one_ge_x (x d : ℕ) : x + d + 1 ≥ x := 
-- Helps to prove my_lemma_helper
begin
    linarith,
/-
   
-/
end

lemma my_lemma_helper (x y: ℕ) : y+x ≥ x := 
begin 
    linarith,
/-    
-/
end

lemma my_lemma (c x : ℕ) (hab: c >= 1): c * x >= x := 
begin 
    exact nat.le_mul_of_pos_left hab,
--    by library_search,
/-
    
-/
end

theorem example2 (a b c : ℕ) (hba: c ≥ 1): a*b*c ≥ a*b := 
begin
    exact nat.le_mul_of_pos_right hba,
--    by library_search,
/-
    
-/
end

theorem example3 (a:ℕ) : ¬ a < a :=  
begin
    linarith,
/-
    
-/
end


lemma another_helper (u v : ℕ) : v ≤ u ↔ v*v ≤ v*u := 
begin
    cases v,
    
  { split,
    { intro h,
      simp,
    },
    intro,    

    linarith,
--    exact zero_le u,
  },
  {
    symmetry,
    apply mul_le_mul_left,
    simp,
  }
end

theorem square_root_prime2 (n : ℕ) (h1: composite n): ∃ (c d : ℕ), n = c*d ∧ c*c ≤ n :=
-- HUMAN PROOF 2 in Code :)
begin 
    rw composite at h1,
    cases h1 with v hv,
    cases hv with u hu,
    use v,
    use u,
    have hl: n = v*u, from and.left hu,
    rw hl,

    have hmr: v ≤ u ∧ u < n, from and.right hu,
    have hr: u < n, from and.right hmr,
    have hm: v ≤ u, from and.left hmr,

    rw another_helper at hm, 

    split,
    refl,
    apply hm,

end
