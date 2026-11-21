import YangMills.Construction.RotationInvariance.HarmonicOfEachIndexOnTheUnionOfTubes
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace EuclideanFunctionals
def IsContinuousHarmonicExtension (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (ψ : Fin (q + 1) → realLabels) (k : ℤ) (g : (Fin (q + 1) → RealPlane) → ℂ) : Prop :=
  ContinuousOn g (injectivePointTuples (q + 1)) ∧
    ∀ x ∈ orderedRealTuples q, g x = indexHarmonic S θ₀ ψ k (embedPlaneTuple x)
def distinctHarmonic (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (ψ : Fin (q + 1) → realLabels) (k : ℤ) : (Fin (q + 1) → RealPlane) → ℂ :=
  Classical.epsilon (IsContinuousHarmonicExtension S θ₀ ψ k)
namespace DistinctHarmonics
variable {q : ℕ}
def IsUniqueContinuousExtension (S : ConnFamily) (θ₀ : openingAngles) (ψ : Fin (q + 1) → realLabels)
    (k : ℤ) : Prop :=
  IsContinuousHarmonicExtension S θ₀ ψ k (distinctHarmonic S θ₀ ψ k) ∧
    ∀ g : (Fin (q + 1) → RealPlane) → ℂ, IsContinuousHarmonicExtension S θ₀ ψ k g →
      ∀ x ∈ injectivePointTuples (q + 1), g x = distinctHarmonic S θ₀ ψ k x
def IsAnalyticOnConnectedOpen (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) (k : ℤ) : Prop :=
  IsRealAnalyticTupleFun (injectivePointTuples (q + 1)) (distinctHarmonic S θ₀ ψ k) ∧
    IsConnected (injectivePointTuples (q + 1)) ∧ IsOpen (injectivePointTuples (q + 1))
def IsLabelInvariant (S : ConnFamily) (θ₀ : openingAngles) (ψ : Fin (q + 1) → realLabels)
    (k : ℤ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (q + 1))), ∀ x ∈ injectivePointTuples (q + 1),
    distinctHarmonic S θ₀ (permuteTuple σ ψ) k (permuteTuple σ x) =
      distinctHarmonic S θ₀ ψ k x
def IsTranslationInvariant (S : ConnFamily) (θ₀ : openingAngles) (ψ : Fin (q + 1) → realLabels)
    (k : ℤ) : Prop :=
  ∀ v : RealPlane, ∀ x ∈ injectivePointTuples (q + 1),
    distinctHarmonic S θ₀ ψ k (translateTuple x v) =
      distinctHarmonic S θ₀ ψ k x
def IsRotationCovariant (S : ConnFamily) (θ₀ : openingAngles) (ψ : Fin (q + 1) → realLabels)
    (k : ℤ) : Prop :=
  ∀ x ∈ injectivePointTuples (q + 1), ∀ s : ℝ,
    distinctHarmonic S θ₀ ψ k (mapPoints (rotate s) x) =
      Complex.exp (4 * I * (k : ℂ) * (s : ℂ)) * distinctHarmonic S θ₀ ψ k x
def SumEqualsKernelOnOrdered (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) : Prop :=
  ∀ x ∈ orderedRealTuples q,
    ∑ j ∈ Finset.Icc (-(maxFrequency S θ₀ (q + 1) : ℤ)) (maxFrequency S θ₀ (q + 1) : ℤ),
      distinctHarmonic S θ₀ ψ j x = tubeUnionFunction S ψ (embedPlaneTuple x)
def VanishesAboveMaxFrequency (S : ConnFamily) (θ₀ : openingAngles) (ψ : Fin (q + 1) → realLabels)
    (k : ℤ) : Prop :=
  (maxFrequency S θ₀ (q + 1) : ℤ) < |k| →
    ∀ x ∈ injectivePointTuples (q + 1), distinctHarmonic S θ₀ ψ k x = 0
def MaxHarmonicNonvanishing (S : ConnFamily) (θ₀ : openingAngles) (q : ℕ) : Prop :=
  1 ≤ maxFrequency S θ₀ (q + 1) →
    ∃ ψ : Fin (q + 1) → realLabels, ∃ x ∈ injectivePointTuples (q + 1),
      distinctHarmonic S θ₀ ψ (-(maxFrequency S θ₀ (q + 1) : ℤ)) x ≠ 0
def EqAngleHarmonicOnPencils (S : ConnFamily) (θ₀ : openingAngles)
    (ψ : Fin (q + 1) → realLabels) (k : ℤ) : Prop :=
  IsOpen (pencilSet θ₀ (q + 1)) ∧
    (∀ x ∈ pencilSet θ₀ (q + 1),
      distinctHarmonic S θ₀ ψ k x = angleHarmonic S θ₀ x ψ k) ∧
    ∀ g : (Fin (q + 1) → RealPlane) → ℂ,
      IsRealAnalyticTupleFun (injectivePointTuples (q + 1)) g →
      (∀ x ∈ pencilSet θ₀ (q + 1), g x = angleHarmonic S θ₀ x ψ k) →
      ∀ x ∈ injectivePointTuples (q + 1), g x = distinctHarmonic S θ₀ ψ k x
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (D : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ (k : ℤ) (ψ : Fin (q + 1) → realLabels),
      IsUniqueContinuousExtension S D.angle ψ k ∧
      IsAnalyticOnConnectedOpen S D.angle ψ k ∧
      IsLabelInvariant S D.angle ψ k ∧
      IsTranslationInvariant S D.angle ψ k ∧
      IsRotationCovariant S D.angle ψ k ∧
      SumEqualsKernelOnOrdered S D.angle ψ ∧
      VanishesAboveMaxFrequency S D.angle ψ k ∧
      MaxHarmonicNonvanishing S D.angle q ∧
      EqAngleHarmonicOnPencils S D.angle ψ k
end DistinctHarmonics
end EuclideanFunctionals
end YangMills.Construction
end
