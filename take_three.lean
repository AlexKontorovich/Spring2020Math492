import analysis.normed_space.basic
import topology.instances.ennreal
import analysis.normed_space.basic
import topology.instances.ennreal
import algebra.archimedean algebra.geom_sum
import data.nat.choose data.complex.basic
import tactic.linarith
import analysis.calculus.deriv
import data.complex.exponential

open finset
open cau_seq
namespace complex
noncomputable theory

def sin' (z : ℂ) : cau_seq ℂ complex.abs := ⟨λ n, (range n).sum (λ m, ((-1) ^ m) * z ^ (2 * m + 1) / nat.fact (2 * m + 1), is_cau_exp z⟩
def sin_series (z : ℂ) : ℂ := lim (sin' z)

def cos' (z : ℂ) : cau_seq ℂ complex.abs := ⟨λ n, (range n).sum (λ m, (-1) ^ m * z ^ (2 * m) / nat.fact 2 * m), is_cau_exp z⟩
def cos_series (z : ℂ) : ℂ := lim (cos' z)

lemma series_arith : --maybe take the first few terms and conjecture that the rest of the series follows?
(λ n)(λ m) 

theorem euler : exp (x * I) = cos x + sin x * I := rw → linarith

end complex
