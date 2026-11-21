import YangMills.Construction.RotationInvariance.HarmonicOfEachIndexOnTheUnionOfTubes
import YangMills.Construction.RotationInvariance.IntervalOfAPointInItsTubeAndTuplesWithoutPerpendicularDifferences
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace EuclideanFunctionals.HarmonicRotationCovariance
variable {q : ℕ}
def RotationFactor (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) (x : Fin (q + 1) → RealPlane) (s : ℝ) : Prop :=
  ∀ k : ℤ,
    indexHarmonic S θ₀ ψ k (embedPlaneTuple (mapPoints (rotate s) x)) =
      Complex.exp (4 * I * (k : ℂ) * (s : ℂ)) * indexHarmonic S θ₀ ψ k (embedPlaneTuple x)
def CovariantOnTubeInterval (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) : Prop :=
  ∀ x ∈ orderedRealTuples q, ∀ (ν : rightAngleMultiples) (σ : Equiv.Perm (Fin (q + 1))),
    embedPlaneTuple x ∈ orderedTube ν σ →
      (∃ a b : ℝ, tubeAngleInterval ν σ x = Set.Ioo a b ∧ (0 : ℝ) ∈ Set.Ioo a b) ∧
        ∀ s ∈ tubeAngleInterval ν σ x,
          RotationFactor S θ₀ ψ x s
def GenericTuplesProps (q : ℕ) : Prop :=
  IsOpen (genericTuples (q + 1)) ∧
    Dense (genericTuples (q + 1)) ∧
    (∀ s : ℝ, mapPoints (rotate s) '' genericTuples (q + 1) =
      genericTuples (q + 1)) ∧
    genericTuples (q + 1) ⊆ orderedRealTuples q
def CovariantBetweenOrdered (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) : Prop :=
  ∀ x ∈ orderedRealTuples q, ∀ s : ℝ, mapPoints (rotate s) x ∈ orderedRealTuples q →
    RotationFactor S θ₀ ψ x s
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (D : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ ψ : Fin (q + 1) → realLabels,
      CovariantOnTubeInterval S D.angle ψ ∧
      GenericTuplesProps q ∧
      CovariantBetweenOrdered S D.angle ψ
end EuclideanFunctionals.HarmonicRotationCovariance
end YangMills.Construction
end
