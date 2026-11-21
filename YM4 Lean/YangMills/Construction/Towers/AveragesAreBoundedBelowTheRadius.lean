import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfABoundedOperatorFunction
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import YangMills.Construction.Towers.PropertiesOfTheBackgrounds
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.CauchyTaylorBounds (IsFieldNorm BoundedOnBall)
open YangMills.Construction.Tower.FullSpace.BackgroundProperties (edgeSmoothingFn vertexSmoothingFn)
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
def fineFieldNorm (L k : ℕ) (ζ : (Tower.remainderIndex L k).Carrier → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Tower.finestMesh L k)⁻¹ * Tower.maxOperatorNorm ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs ζ)
def scaledForm (L k : ℕ) (ζ : (Tower.remainderIndex L k).Carrier → ℂ) :
    FullSpace.Edge L k 0 → Matrices.ComplexMatrix2 :=
  (Tower.finestMesh L k)⁻¹ • (FullSpace.edgePauliCoordinates L k 0).ofCoeffs ζ
def MeanBoundsBelowRadius : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ ρ C : ℝ, Tower.IteratedSmallFieldMeans.AdmissibleConstants L ρ C →
      IsFieldNorm (Tower.remainderIndex L k) (fineFieldNorm L k) ∧
      (∀ ζ, IsSupBelow (Tower.remainderIndex L k) ζ (Tower.finestMesh L k * ρ / 3) →
        fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ) ∧
      (∀ ζ, fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ →
        scaledForm L k ζ ∈ FullSpace.IteratedSmallFieldMeans.smallFormBall L k ρ ∧
          FullSpace.remainderGaugeField (scaledForm L k ζ) = gaugeFieldOfForm L k ζ) ∧
      BoundedOnBall (Tower.remainderIndex L k) (colourEdges L k 0) (colourEdges L k k)
        (edgeSmoothingFn L k) (fineFieldNorm L k) ρ C ∧
      BoundedOnBall (Tower.remainderIndex L k) (colourVertices L k 0) (colourVertices L k k)
        (vertexSmoothingFn L k) (fineFieldNorm L k) ρ C
end YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds
end
