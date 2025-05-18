import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

open Real

noncomputable def angle (u v : ℝ × ℝ) : ℝ :=
  arccos ((u.1 * v.1 + u.2 * v.2) / (norm u * norm v)) * (if (u.1 * v.2 - u.2 * v.1) < 0 then -1 else 1)

lemma rightAngle (u v : ℝ × ℝ)(o : u.1 * v.1 + u.2 * v.2 = 0)(p: u.1 * v.2 - u.2 * v.1 > 0) : angle u v = π/2 :=
  by
  unfold angle
  rw [o]
  rw [zero_div]
  simp only [Real.arccos_zero]
  rw [if_neg (not_lt_of_gt p)]
  norm_num

def admissibleFunction (f : ℝ → ℝ) : Prop :=
  (ContDiff ℝ (⊤ : ℕ∞) f) ∧
  (∀ x : ℝ, f x > 0 ∧ f (x + 2*π) = f x) ∧
  (∀ p q : ℤ, Int.gcd p q = 1 → (∀ x : ℝ, angle (p, q) (cos x * deriv f x - sin x * f x, sin x * deriv f x + cos x * f x) = π/2 → (p * cos x + q * sin x) * f x ≥ 1))

def symmetricAdmissibleFunction (f : ℝ → ℝ) : Prop :=
    admissibleFunction f ∧
    (∀ x : ℝ, f (x + π) = f x)

noncomputable def integrate (f : ℝ → ℝ) : ℝ :=
  ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, f x

structure starshapedPolygon where
  n : ℕ
  nonEmpty : n ≥ 3
  vertices : Fin n → ℚ × ℚ
  isStarshaped : ∀ i j : Fin n, j = (i + 1) % n → angle ((vertices i).1, (vertices i).2) ((vertices j).1, (vertices j).2) > 0
  simple : ∑ i : Fin n, ∑ j : Fin n, (if j = (i + 1) % n then angle ((vertices i).1, (vertices i).2) ((vertices j).1, (vertices j).2) else 0) = 2 * π

def symmetricStarshapedPolygon (p : starshapedPolygon) : Prop :=
  p.n % 2 = 0 ∧
  ∀ i j: Fin p.n, j = (i + p.n/2) % p.n → p.vertices i = -p.vertices j

def admissiblePolygon (p : starshapedPolygon) : Prop :=
  sorry

def polygonArea (p : starshapedPolygon) : ℚ :=
  ∑ i : Fin p.n, ∑ j : Fin p.n, (if j = (i + 1) % p.n then ((p.vertices i).1 * (p.vertices j).2 - (p.vertices i).2 * (p.vertices j).1)/2 else 0)

lemma polygonalApproximation (f : ℝ → ℝ) (hf : symmetricAdmissibleFunction f) :
    ∀ ε > 0, ∃ p : starshapedPolygon, admissiblePolygon p ∧
    symmetricStarshapedPolygon p ∧
    polygonArea p < ε + integrate f :=
  sorry

theorem systolicInequalityForPolygons (p : starshapedPolygon) (hp : admissiblePolygon p)(hs : symmetricStarshapedPolygon p) :
    polygonArea p ≥ (4 : ℚ)/(3 : ℚ) :=
  sorry

lemma nonOptimality (f : ℝ → ℝ) (hf : symmetricAdmissibleFunction f) :
    ∃ g : ℝ → ℝ, symmetricAdmissibleFunction g ∧
    integrate g < integrate f :=
  sorry

theorem systolicInequality (f : ℝ → ℝ) (hf : symmetricAdmissibleFunction f) :
    integrate f > (4 : ℝ)/(3 : ℝ) :=
  by
  by_contra h
  rw [not_lt] at h
  have strict : ∃ g : ℝ → ℝ, symmetricAdmissibleFunction g ∧
    integrate g < integrate f := nonOptimality f hf
  obtain ⟨g, hg⟩ := strict
  have approximation : ∀ ε > 0, ∃ p : starshapedPolygon, admissiblePolygon p ∧
    symmetricStarshapedPolygon p ∧
    polygonArea p < ε + integrate g := polygonalApproximation g hg.1
  let δ := (4 : ℝ)/(3 : ℝ) - integrate g
  have hδ : δ > 0 := sub_pos_of_lt (lt_of_lt_of_le hg.2 h)
  obtain ⟨p, hp⟩ := approximation (δ) (hδ)
  have hc : polygonArea p < (4 : ℝ)/(3 : ℝ) := sorry
  have hc2 : polygonArea p < (4 : ℚ)/(3 : ℚ) := sorry
  have contradiction : polygonArea p ≥ (4 : ℚ)/(3 : ℚ) := systolicInequalityForPolygons p hp.1 hp.2.1
  have ncontradiction : ¬ polygonArea p < (4 : ℚ)/(3 : ℚ) := sorry
  exact (hc2 ∧ ncontradiction)

theorem systolicInequalityIsSharp :
    ∀ ε > 0, ∃ f : ℝ → ℝ, symmetricAdmissibleFunction f ∧
    integrate f < (4 : ℝ)/(3 : ℝ) + ε :=
  sorry
