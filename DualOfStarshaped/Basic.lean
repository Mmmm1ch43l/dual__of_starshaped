import Mathlib
--set_option maxHeartbeats 1000000

namespace polygons
  open Rat

  def dot (u v : ℚ × ℚ) : ℚ :=
    u.1 * v.1 + u.2 * v.2

  def cross (u v : ℚ × ℚ) : ℚ :=
    u.1 * v.2 - u.2 * v.1

  def rotateRight (u : ℚ × ℚ) : ℚ × ℚ :=
    (u.2, -u.1)

  structure starshaped where
    n : ℕ
    nonEmpty : n ≥ 3
    neZero : NeZero n := ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) nonEmpty)⟩
    succ (i : Fin n) : Fin n := Fin.ofNat' n (i + 1)
    succ2 (i : Fin n) : Fin n := Fin.ofNat' n (i + 2)
    succ3 (i : Fin n) : Fin n := Fin.ofNat' n (i + 3)
    vertices : Fin n → ℚ × ℚ
    isStarshaped : ∀ i : Fin n, cross (vertices i) (vertices (succ i)) > 0
    simple : ∃! i : Fin n, (vertices i).1 ≤ 0 ∧ (vertices (succ i)).1 > 0

  def convex (P : starshaped) : Prop :=
    ∀ i : Fin P.n, let j := P.succ i; let k := P.succ2 i
    cross (P.vertices j - P.vertices i) (P.vertices k - P.vertices j) > 0

  def area (P : starshaped) : ℚ :=
    ∑ i : Fin P.n, (cross (P.vertices i) (P.vertices (P.succ i)))/2

  def admissible (P : starshaped) : Prop :=
    ∀ i : Fin P.n, let j := P.succ i; let k := P.succ2 i; let l := P.succ3 i
    -- check no degenerate vertices
    (cross (P.vertices j - P.vertices i) (P.vertices k - P.vertices j) ≠ 0) ∧
    ∀ p q : ℤ, Int.gcd p q = 1 →
    -- check tangencies at vertices
    (cross (p, q) (rotateRight (P.vertices j - P.vertices i)) < 0 ∧
    cross (p, q) (rotateRight (P.vertices k - P.vertices j)) > 0 ∨
    cross (p, q) (rotateRight (P.vertices j - P.vertices i)) > 0 ∧
    cross (p, q) (rotateRight (P.vertices k - P.vertices j)) < 0
    → dot (p, q) (P.vertices j) ≥ 1) ∧
    -- check tangencies at edges
    (cross (p, q) (rotateRight (P.vertices k - P.vertices j)) = 0 ∧
    -- check whether tangency is real
    (cross (p, q) (rotateRight (P.vertices j - P.vertices i)) < 0 ∧
    cross (p, q) (rotateRight (P.vertices l - P.vertices k)) > 0 ∨
    cross (p, q) (rotateRight (P.vertices j - P.vertices i)) > 0 ∧
    cross (p, q) (rotateRight (P.vertices l - P.vertices k)) < 0)
    → dot (p, q) (P.vertices j) ≥ 1)

  def symmetric (P : starshaped) : Prop :=
    P.n % 2 = 0 ∧
    ∀ i j : Fin P.n, j = (i + P.n/2) % P.n → P.vertices i = -P.vertices j

  theorem systolicInequality (P : starshaped) (hp : admissible P ∧ symmetric P) :
      area P ≥ (4 : ℚ) / (3 : ℚ) :=
    sorry

  theorem systolicInequalityIsSharp :
      ∃ P : starshaped, admissible P ∧ symmetric P ∧
      area P = (4 : ℚ) / (3 : ℚ) := by
    -- construct the polygon
    let P : starshaped := {
      n := 8,
      nonEmpty := by norm_num,
      vertices := λ i : Fin 8 ↦ match i with
        | ⟨0, _⟩ => ((1 : ℚ), (1 : ℚ) / (3 : ℚ))
        | ⟨1, _⟩ => ((1 : ℚ) / (3 : ℚ), (1 : ℚ) / (3 : ℚ))
        | ⟨2, _⟩ => ((-1 : ℚ) / (3 : ℚ), (1 : ℚ))
        | ⟨3, _⟩ => ((-1 : ℚ) / (3 : ℚ), (1 : ℚ) / (3 : ℚ))
        | ⟨4, _⟩ => ((-1 : ℚ), (-1 : ℚ) / (3 : ℚ))
        | ⟨5, _⟩ => ((-1 : ℚ) / (3 : ℚ), (-1 : ℚ) / (3 : ℚ))
        | ⟨6, _⟩ => ((1 : ℚ) / (3 : ℚ), (-1 : ℚ))
        | ⟨7, _⟩ => ((1 : ℚ) / (3 : ℚ), (-1 : ℚ) / (3 : ℚ)),
      isStarshaped := by
        intro i
        fin_cases i
        all_goals {
          rw [Fin.ofNat']
          norm_num
          unfold cross
          norm_num
        },
      simple := by
        use ⟨5, by norm_num⟩
        constructor
        norm_num
        intro i
        fin_cases i
        all_goals norm_num
      }
    -- check that it's admissible
    have ha : admissible P := by
      sorry
    -- check that it's symmetric
    have hs : symmetric P := by
      unfold symmetric
      constructor
      norm_num
      intro i j h
      fin_cases i
      all_goals {
        fin_cases j
        all_goals {
          norm_num at h
          try {
            unfold P
            norm_num
          }
        }
      }
    -- check that the area is really 4/3
    have harea : area P = (4 : ℚ) / (3 : ℚ) := by
      unfold area
      unfold cross
      unfold P
      have hp : P.n = 8 := by norm_num
      simp only [hp]
      unfold Finset.sum
      norm_num
      unfold Fin.succ
      norm_num
      dsimp
      norm_num
    exact ⟨P, ha, hs, harea⟩

end polygons

namespace smoothDomains
  open Real

  noncomputable def angle (u v : ℝ × ℝ) : ℝ :=
    arccos ((u.1 * v.1 + u.2 * v.2) / (norm u * norm v)) * (if (u.1 * v.2 - u.2 * v.1) < 0 then -1 else 1)

  lemma rightAngle (u v : ℝ × ℝ)(o : u.1 * v.1 + u.2 * v.2 = 0)(p: u.1 * v.2 - u.2 * v.1 > 0) : angle u v = π/2 :=
    by
    unfold angle
    rw [o, zero_div, if_neg (not_lt_of_gt p)]
    norm_num

  def admissible (f : ℝ → ℝ) : Prop :=
    (ContDiff ℝ (⊤ : ℕ∞) f) ∧
    (∀ x : ℝ, f x > 0 ∧ f (x + 2*π) = f x) ∧
    (∀ p q : ℤ, Int.gcd p q = 1 →
    (∀ x : ℝ, angle (p, q) (cos x * deriv f x - sin x * f x, sin x * deriv f x + cos x * f x) = π/2
    → (p * cos x + q * sin x) * f x ≥ 1))

  def symmetric (f : ℝ → ℝ) : Prop :=
    ∀ x : ℝ, f (x + π) = f x

  noncomputable def integrate (f : ℝ → ℝ) : ℝ :=
    ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, ((f x)^2)/2

  lemma polygonalApproximation (f : ℝ → ℝ) (hf : admissible f ∧ symmetric f) :
      ∀ ε > 0, ∃ P : polygons.starshaped, polygons.admissible P ∧ polygons.symmetric P ∧
      polygons.area P < ε + integrate f :=
    sorry

  lemma nonOptimality (f : ℝ → ℝ) (hf : admissible f ∧ symmetric f) :
      ∃ g : ℝ → ℝ, admissible g ∧ symmetric g ∧
      integrate g < integrate f :=
    sorry

  theorem systolicInequality (f : ℝ → ℝ) (hf : admissible f ∧ symmetric f) :
      integrate f > (4 : ℝ) / (3 : ℝ) :=
    by
    -- assume integrate f ≤ 4/3
    by_contra h
    rw [not_lt] at h
    -- use non optimality to get integrate g < 4/3
    obtain ⟨g, hg⟩ := nonOptimality f hf
    -- use polygonal approximation to get a polygon p with area < 4/3
    obtain ⟨P, hp⟩ := polygonalApproximation g (And.intro hg.1 hg.2.1) ((4 : ℝ) / (3 : ℝ) - integrate g) (sub_pos_of_lt (lt_of_lt_of_le hg.2.2 h))
    have hcoe : (4 : ℝ) / (3 : ℝ) = ↑((4 : ℚ) / (3 : ℚ)) := (Rat.cast_div (4 : ℚ) (3 : ℚ)).symm
    rw [sub_add_cancel, hcoe, Rat.cast_lt] at hp
    -- conclude with the systolic inequality for polygons
    exact not_le_of_gt hp.2.2 (polygons.systolicInequality P (And.intro hp.1 hp.2.1))

  theorem systolicInequalityIsSharp :
      ∀ ε > 0, ∃ f : ℝ → ℝ, admissible f ∧ symmetric f ∧
      integrate f < (4 : ℝ) / (3 : ℝ) + ε :=
    sorry

end smoothDomains
