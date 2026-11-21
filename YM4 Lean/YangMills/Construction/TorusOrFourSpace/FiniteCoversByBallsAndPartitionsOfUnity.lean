import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Kind
variable (D : Params)
def torusBall (x : Pt D torus) (r : ℝ) : Set (Pt D torus) :=
  {y | quotDist D torus y x < r}
def BallsCoverTorus {I : Type} (x : I → Pt D torus) (r : ℝ) : Prop :=
  ∀ y, ∃ j, y ∈ torusBall D (x j) r
structure IsSubordinatePartitionOfUnity {I A : Type} [Fintype A] (x : I → Pt D torus) (r : ℝ)
    (χ : A → Pt D torus → ℝ) : Prop where
  mem_unitInterval : ∀ a, χ a ∈ smoothUnitIntervalSet D torus
  sum_eq_one : ∀ y, ∑ a, χ a y = 1
  support_subset : ∀ a, ∃ j, supportQ D torus (χ a) ⊆ torusBall D (x j) r
end Kind
open Kind
def TorusBallCoversAndPartitionsOfUnity : Prop :=
  ∀ (D : Params) (r : ℝ), 0 < r →
    (∃ J : ℕ, 1 ≤ J ∧ ∃ x : Fin J → Pt D torus, BallsCoverTorus D x r) ∧
    (∀ (J : ℕ), 1 ≤ J → ∀ x : Fin J → Pt D torus, BallsCoverTorus D x r →
      ∃ (A : Type) (_ : Fintype A) (_ : Nonempty A) (χ : A → Pt D torus → ℝ),
        IsSubordinatePartitionOfUnity D x r χ) ∧
    (∀ χ ∈ smoothSet D torus,
      IsC1Fn D torus χ ∧ IsCompactQ D torus (supportQ D torus χ) ∧
        IsLipschitzQ D torus χ ∧
        vecSupNormQ D torus (gradVec D torus χ) ≠ ∞ ∧
        ENNReal.ofReal (lipConstQ D torus χ) =
          vecSupNormQ D torus (gradVec D torus χ))
end YangMills.Construction.PeriodicSpace
