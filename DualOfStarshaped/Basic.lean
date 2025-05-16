import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

-- want to define a class for functions that are admissible, i.e. smooth functions from ℝ to ℝ which are positive and 2pi periodic
def admissableFunction (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧
  Periodic f (2 * π) ∧
  ∀ x : ℝ, f x > 0
