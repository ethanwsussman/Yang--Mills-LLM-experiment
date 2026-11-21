import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.DensityAtDistinctPoints
import Mathlib
set_option autoImplicit false
open Complex (I)
open MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.HarmonicDensity
open RealPlane ForwardTube
variable {q : ℕ}
def AnalyticOffDiagonal (S : ConnFamily) (φ₀ : openingAngles)
    (φ : Fin (q + 1) → realLabels) : Prop :=
  IsRealAnalyticTupleFun (injectivePointTuples (q + 1)) (harmonicSum S φ₀ (q + 1) φ)
def EqOnOrderedTuples (S : ConnFamily) (φ₀ : openingAngles)
    (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ y ∈ orderedRealTuples q,
    harmonicSum S φ₀ (q + 1) φ y = tubeUnionFunction S φ (embedPlaneTuple y)
def ProductValuesAsIntegrals (S : ConnFamily) (φ₀ : openingAngles)
    (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ α : Fin (q + 1) → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
    (Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) →
    Integrable (profileIntegrand α (harmonicSum S φ₀ (q + 1) φ)) ∧
      centeredFnAtProducts S α φ =
        profileIntegral α (harmonicSum S φ₀ (q + 1) φ)
def RotationExpansion (S : ConnFamily) (φ₀ : openingAngles)
    (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ y ∈ injectivePointTuples (q + 1), ∀ t : ℝ,
    harmonicSum S φ₀ (q + 1) φ (mapPoints (rotate t) y) =
      ∑ k ∈ Finset.Icc (-(maxFrequency S φ₀ (q + 1) : ℤ)) (maxFrequency S φ₀ (q + 1) : ℤ),
        pointHarmonic S φ₀ k (q + 1) φ y * Complex.exp (4 * I * (k : ℂ) * (t : ℂ))
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (_ : ProductPlaneData m S) (φ₀ : openingAngles) (q : ℕ), 1 ≤ q →
    ∀ φ : Fin (q + 1) → realLabels,
      AnalyticOffDiagonal S φ₀ φ ∧
      EqOnOrderedTuples S φ₀ φ ∧
      ProductValuesAsIntegrals S φ₀ φ ∧
      RotationExpansion S φ₀ φ
end YangMills.Construction.EuclideanFunctionals.HarmonicDensity
end
