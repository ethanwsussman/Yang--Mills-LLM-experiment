import YangMills.Construction.ResponseInTheExpansion.ByPartsOfACutLaw
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentMethod
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def unitVariation (j : Fin 3 × ι) : ColdStepAtMirrorFrames.BondField ι :=
  ColdStepAtMirrorFrames.bondVariation j.2 (EuclideanSpace.single j.1 1)
def fieldOfCoordinates (ζ : EuclideanSpace ℝ (Fin 3 × ι)) : ColdStepAtMirrorFrames.BondField ι :=
  fun b => WithLp.toLp 2 fun e => ζ (e, b)
def gradientCoord (p : ℝ → ℝ) (Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ) (η : ColdStepAtMirrorFrames.BondField ι)
    (j : Fin 3 × ι) : ℝ :=
  fderiv ℝ Ψ η (unitVariation j) + WeightedResponses.cutoffRadialDeriv p (η j.2) (EuclideanSpace.single j.1 1)
def driftCoord (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (p : ℝ → ℝ) (Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ)
    (η : ColdStepAtMirrorFrames.BondField ι) (j : Fin 3 × ι) : ℝ :=
  ∑ i, G j i * gradientCoord p Ψ η i - η j.2 j.1
def gaussianComparisonStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ Φ : ColdStepAtMirrorFrames.BondField ι → ℝ)
    (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (Cg A : ℝ) (k : ℕ) (c : Fin 3 × ι → ℝ),
    0 < ρ → ColdStepAtMirrorFrames.IsCutoff ρ p → ContDiff ℝ 1 Ψ → G.PosSemidef → ContDiff ℝ 2 Φ → 0 ≤ A →
    (∀ η, ∀ l : ℕ, l ≤ 2 → ‖iteratedFDeriv ℝ l Φ η‖ ≤ Cg * (1 + ‖η‖) ^ k) →
    (∀ j, eLpNorm (fun η => driftCoord G p Ψ η j) 2
      (ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) ≤ ENNReal.ofReal (c j)) →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 → ∑ j, ENNReal.ofReal (c j) *
        eLpNorm (fun z : ColdStepAtMirrorFrames.BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
          fderiv ℝ Φ (Real.cos θ • z.1 + Real.sin θ • fieldOfCoordinates z.2) (unitVariation j)) 2
          ((ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ).prod
            (multivariateGaussian 0 G)) ≤ ENNReal.ofReal A) →
    |(∫ η, Φ η ∂ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) -
      ∫ ζ, Φ (fieldOfCoordinates ζ) ∂multivariateGaussian 0 G| ≤ A
end YangMills.Construction.MomentMethod
end
