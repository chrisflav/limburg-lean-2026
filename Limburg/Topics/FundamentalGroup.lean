import Mathlib

variable {X : Type} [TopologicalSpace X]

namespace Playground

structure Loop (x : X) where
  path : Set.Icc (0 : ℝ) (1 : ℝ) → X
  continuous : Continuous path
  startpoint : path 0 = x
  endpoint : path 1 = x

variable {x : X}

structure Homotopy (f g : Loop x) where
  map : Set.Icc (0 : ℝ) (1 : ℝ) → Set.Icc (0 : ℝ) (1 : ℝ) → X
  map_left : ∀ y, map 0 y = f.path y
  map_right : ∀ y, map 1 y = g.path y

variable (x) in
def Homotopic (f g : Loop x) : Prop :=
  Nonempty (Homotopy f g)

lemma Homotopic.equivalence : Equivalence (Homotopic x) := sorry

variable (x) in
def Homotopic.setoid : Setoid (Loop x) where
  r := Homotopic x
  iseqv := Homotopic.equivalence

variable (x) in
def FundamentalGroup : Type :=
  Quotient (Homotopic.setoid x)

instance : Group (FundamentalGroup x) := sorry

end Playground
