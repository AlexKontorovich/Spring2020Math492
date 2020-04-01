import
data.real.basic
data.set.basic
order.basic
topology.algebra.continuous_functions
analysis.normed_space.basic
topology.metric_space.lipschitz
tactic.tfae
order.liminf_limsup
order.complete_lattice
data.set.intervals
topology.algebra.group
order.conditionally_complete_lattice
order.complete_lattice
order.lattice
order.bounds
tactic.finish
data.nat.enat
topology.algebra.ordered
namespace lattice

lemma cSup_is_bigger {f : ℝ → ℝ} (Hf : continuous f)
 {a b : ℝ} (Hab : a < b) (K := {x : ℝ | x>=a ∧ x<b ∧ f x < 0})
 (c:= Sup K) (Hbdd: bdd_above K) (Hne: a ∈ K) :
 a <= Sup K := conditionally_complete_lattice.le_cSup K a Hbdd Hne 


lemma cSup_is_smaller {f : ℝ → ℝ} (Hf : continuous f)
 {a b : ℝ} (Hab : a < b) (K := {x : ℝ | x>=a ∧ x<b ∧ f x < 0})
 (c:= Sup K) (Hbdd: b ∈ upper_bounds K) (Hne: K.nonempty) :
 Sup K <= b := conditionally_complete_lattice.cSup_le K b Hne Hbdd


lemma continuous_implies {f : ℝ → ℝ} (Hf : continuous f)
 {a b : ℝ} (Hab : a < b) (K := {x : ℝ | x>a ∧ x<b ∧ f x < 0}) 
 (c:= Sup K):
 f c = 0
 := 
 --having trouble proving this
 sorry

theorem intermediate_value {f : ℝ → ℝ} (Hf : continuous f)
 {a b : ℝ} (Hab : a < b)
        (Hav : f a < 0) (Hbv : f b > 0)  : 
        ∃ c, a < c ∧ c < b ∧ f c = 0 :=
begin
let K := {x : ℝ | x>=a ∧ x<b ∧ f x < 0},
have Hbdd: bdd_above K, use b,
have Hne: K.nonempty, use a,
let c := Sup K,
have Hac: a < c, apply cSup_is_bigger,
--not sure how to use apply syntax, keep getting errors
have Hbc: c < b, apply cSup_is_smaller,
--same here
have c:ℝ, exact c,
have Hc: f c = 0, from continuous_implies,
end