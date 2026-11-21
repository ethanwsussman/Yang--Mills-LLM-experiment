import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages (centredCube unitStep)
open LumpContours (contourMean)
open TorusFields (TorusField)
def BondKernelLocality : Prop :=
  ∀ (P : StepParameters), P.Admissible → 11 * 2 ^ 12 * P.baseDepth < P.side →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], 16 ≤ n → 16 ≤ n' →
    ∀ (W : TorusField (n * P.side)) (W' : TorusField (n' * P.side))
      (y : (stepBlockFrame P.side n).Cell) (y' : (stepBlockFrame P.side n').Cell),
      (baseChoices P (fineLevelField P n W) =
        Fintype.piFinset (baseSitesAt P.baseDepth (fineHotLumps P (fineLevelField P n W)))) ∧
      (FieldsAgreeNear W W' (cellCentreOnTorus P.side y) (cellCentreOnTorus P.side y') (3 * P.side) →
        SameNearbyLumps (fineHotLumps P (fineLevelField P n W)) (fineHotLumps P (fineLevelField P n' W')) y y') ∧
      (SameNearbyLumps (fineHotLumps P (fineLevelField P n W)) (fineHotLumps P (fineLevelField P n' W')) y y' →
        (baseSitesAt P.baseDepth (fineHotLumps P (fineLevelField P n W)) y).card =
          (baseSitesAt P.baseDepth (fineHotLumps P (fineLevelField P n' W')) y').card ∧
        ∀ z ∈ centredCube P.side, siteAtOffset y z ∈ baseSitesAt P.baseDepth (fineHotLumps P (fineLevelField P n W)) y ↔
          siteAtOffset y' z ∈ baseSitesAt P.baseDepth (fineHotLumps P (fineLevelField P n' W')) y') ∧
      ∀ (i : Fin 4) (x : ℝ) (V : (stepBlockFrame P.side n).GaugeField 1) (V' : (stepBlockFrame P.side n').GaugeField 1)
        (b : (stepBlockFrame P.side n).Cell → (stepBlockFrame P.side n).Site 0)
        (b' : (stepBlockFrame P.side n').Cell → (stepBlockFrame P.side n').Site 0) (z₀ z₁ : Fin 4 → ℤ),
        z₀ ∈ centredCube P.side → z₁ ∈ centredCube P.side →
        b y = siteAtOffset y z₀ → b' y' = siteAtOffset y' z₀ →
        b (y + unitStep 1 i) = siteAtOffset (y + unitStep 1 i) z₁ →
        b' (y' + unitStep 1 i) = siteAtOffset (y' + unitStep 1 i) z₁ →
        FieldsAgreeNear W W' (cellCentreOnTorus P.side y) (cellCentreOnTorus P.side y') (2 * P.side) →
        SameNearbyLumps (fineHotLumps P (fineLevelField P n W)) (fineHotLumps P (fineLevelField P n' W')) y y' →
        SameNearbyLumps (fineHotLumps P (fineLevelField P n W)) (fineHotLumps P (fineLevelField P n' W'))
          (y + unitStep 1 i) (y' + unitStep 1 i) →
        contourMean P.baseDepth (fineHotLumps P (fineLevelField P n W)) b (fineLevelField P n W) (y, i) =
          contourMean P.baseDepth (fineHotLumps P (fineLevelField P n' W')) b' (fineLevelField P n' W') (y', i) ∧
        (V y i = V' y' i → bondKernel P x (fineLevelField P n W) V b (y, i) =
          bondKernel P x (fineLevelField P n' W') V' b' (y', i))
end YangMills.Construction.TorusLumps
end
