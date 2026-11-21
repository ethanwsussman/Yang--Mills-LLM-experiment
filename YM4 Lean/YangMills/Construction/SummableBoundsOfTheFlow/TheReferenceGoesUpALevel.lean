import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.StepDensities
def maxLowerOrderBounds (E₃ : ℝ) (Eh : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≤ 4 then E₃ else if k = 5 then max E₃ (Eh 4) else max (max E₃ (Eh 4)) (Eh 5)
def referenceNextLevelStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ Ck : ℕ → ℝ, (∀ k, 0 ≤ Ck k) ∧
    ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ (t : ℕ) (Eh : ℕ → ℝ),
      (∀ k, 0 ≤ Eh k) → ReferenceBoundsAtLevel T ℓ Eh t →
      TorusLumps.HasCurvatureForm
        (ReferenceDensity.familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) 0 ∧
      ReferenceBoundsAtLevel T ℓ
        (fun k => Eh k / 4 + Ck k * (1 + maxLowerOrderBounds T.energyRatio Eh k)) (t + 1)
end YangMills.Construction.StepDensities
end
