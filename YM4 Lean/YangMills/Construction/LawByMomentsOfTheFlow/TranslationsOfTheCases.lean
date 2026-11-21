import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheWeightOfADraw
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
variable {ℓ : TorusLumps.StepParameters}
def translateSample : (s n : ℕ) → [NeZero n] → (Fin 4 → ℤ) →
    WeightedResponses.MarkedSample ℓ s n → WeightedResponses.MarkedSample ℓ s n
  | 0, _, _, v, W => TorusFields.translate (TorusFields.siteOfInt v) W
  | s + 1, n, _, v, u =>
    (translateSample s (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) u.1, CellWindows.translateOutcome v u.2)
def translateStageState (T : WeightedResponses.StageTower ℓ) (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ)
    (q : WeightedResponses.StageState T s n) : WeightedResponses.StageState T s n :=
  (TorusFields.translate (TorusFields.siteOfInt v) q.1,
    ⟨TorusLumps.translateSet (TorusFields.siteOfInt v) q.2.1,
      TorusLumps.translateLabel (TorusFields.siteOfInt v) q.2.1 q.2.2⟩)
def translateCaseFunction {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] (v : Fin 4 → ℤ)
    (F : WeightedResponses.CaseFunction R n) : WeightedResponses.CaseFunction R n :=
  fun W Yt ωt bad b =>
    F (TorusFields.translate (TorusFields.siteOfInt fun i => (R.params.side : ℤ) * v i) W)
      (TorusLumps.translateSet (TorusFields.siteOfInt fun i => (R.params.side : ℤ) * v i) Yt)
      (TorusLumps.translateLabel (TorusFields.siteOfInt fun i => (R.params.side : ℤ) * v i) Yt ωt)
      (CellWindows.translateBonds (TorusFields.siteOfInt fun i => (R.params.side : ℤ) * v i) bad)
      (BaseTranslations.translateBases v b)
end YangMills.Construction.MomentLaw
end
