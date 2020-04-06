open set 

variable U : Type
variable T : set U
variables {X Y Z : Type}


def injective (f: X → Y) : Prop := ∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

def surjective (f : X → Y) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : X → Y) := injective f ∧ surjective f



axiom pairing {x y : (set U)} : ∃ z : (set (set U)), ∀ w : set U, w ∈ z ↔ w = x ∨ w = y
axiom unique_pair (x : set U) : ∃ z : set (set U), ∀ w, w ∈ z ↔ w = x

def set_containing_set (A : set U) : set (set U) := {A}




def mysucc (A : set U) : set (set U) := A ∪ {A}






def induct T := 
assume x, 
assume h: x ∈ T, 
show ∅ ∈ T, mysucc x ∈ T from sorry

































