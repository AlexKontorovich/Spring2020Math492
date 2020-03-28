import data.set.intervals topology.algebra.continuous_functions analysis.normed_space.basic topology.metric_space.lipschitz
def range (f: ℝ → ℝ) (A : set ℝ) := {b | ∃ a: A, f a = b}

def continuousAT (f: ℝ → ℝ) (x a: ℝ) (ε : ℝ) (ε > 0) (δ : ℝ) (δ > 0 )
:= (abs(x-a)<δ) → (abs(f x - f a)< ε)

def continuousON (f: ℝ → ℝ) (A : set ℝ) (x : A) :=  continuousAT f x

theorem IVT (f: ℝ → ℝ) (A : set ℝ) (a : A) (b: A) (c: A)
(H: continuous f) (L : range f A) (L > f a) (L < f  b):
∃ c (c > a) (c < b) (f c = L) :=
sorry


