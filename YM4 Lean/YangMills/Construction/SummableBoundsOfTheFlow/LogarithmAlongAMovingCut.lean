import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
variable {ι : Type} [Fintype ι]
def cutoffSlope (p : ℝ → ℝ) (e η : BondField ι) : ℝ :=
  ∑ b, deriv p ‖η b‖ * ‖η b‖⁻¹ * ⟪η b, e b⟫
def shiftedCutoffIntegral (ρ : ℝ) (p : ℝ → ℝ) (G : BondField ι → ℝ) (a d : BondField ι) (s : ℝ) : ℝ :=
  ∫ w, G w * radialWeightProd (cutoffFactor ρ p) (w - (a + s • d))
def shiftedCutoffSlopeIntegral (ρ : ℝ) (p : ℝ → ℝ) (G : BondField ι → ℝ) (a d e : BondField ι) (s : ℝ) : ℝ :=
  ∫ w, G w * (cutoffSlope p e (w - (a + s • d)) * radialWeightProd (cutoffFactor ρ p) (w - (a + s • d)))
def logShiftedCutoffIntegralStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (G : BondField ι → ℝ)
    (a d : BondField ι) (M : ℝ), 0 < ρ → IsCutoff ρ p →
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable (fun w => G w * radialWeightProd (cutoffFactor ρ p) (w - (a + s • d))) volume) →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ w : BondField ι, (∀ b, ‖(w - (a + s • d)) b‖ < ρ) → |G w| ≤ M) →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < shiftedCutoffIntegral ρ p G a d s) →
    (∀ e : BondField ι, ∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable (fun w =>
      G w * (cutoffSlope p e (w - (a + s • d)) * radialWeightProd (cutoffFactor ρ p) (w - (a + s • d))))) ∧
    (∀ e : BondField ι, ContinuousOn
      (fun s => shiftedCutoffSlopeIntegral ρ p G a d e s / shiftedCutoffIntegral ρ p G a d s)
      (Set.Icc (0 : ℝ) 1)) ∧
    Real.log (shiftedCutoffIntegral ρ p G a d 1) - Real.log (shiftedCutoffIntegral ρ p G a d 0) =
      ∫ s in (0 : ℝ)..1, shiftedCutoffSlopeIntegral ρ p G a d d s / shiftedCutoffIntegral ρ p G a d s
end Estimates
end YangMills.Construction
end
