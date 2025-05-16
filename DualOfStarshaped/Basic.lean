import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Real

def admissibleFunction (f : ℝ → ℝ) : Prop :=
  (ContDiff ℝ (⊤ : ℕ∞) f) ∧
  (∀ x : ℝ, f x > 0 ∧ f (x + 2*π) = f x) ∧
  (∀ q p : ℤ, Int.gcd p q = 1 → (∀ x : ℝ, deriv f x = (p : ℝ)/(q : ℝ) → f x ≥ (p + 1)/q))

def symmetricAdmissibleFunction (f : ℝ → ℝ) : Prop :=
    admissibleFunction f ∧
    (∀ x : ℝ, f (x + π) = f x)

lemma nonOptimality (f : ℝ → ℝ) (hf : symmetricAdmissibleFunction f) :
    ∃ g : ℝ → ℝ, symmetricAdmissibleFunction g ∧
    ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, g x < ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, f x :=
  sorry

theorem systolicInequality (f : ℝ → ℝ) (hf : symmetricAdmissibleFunction f) :
    ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, f x > 4/3 :=
  sorry

theorem systolicInequalityIsSharp :
    ∀ ε > 0, ∃ f : ℝ → ℝ, symmetricAdmissibleFunction f ∧
    ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, f x < 4/3 + ε :=
  sorry
