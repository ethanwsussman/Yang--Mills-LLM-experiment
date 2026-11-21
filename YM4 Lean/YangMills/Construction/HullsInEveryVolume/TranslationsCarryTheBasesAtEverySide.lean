import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
def translationCarriesBasesStatement : Prop :=
  ∀ (p : TorusLumps.StepParameters) (n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusFields.TorusField (n * p.side)),
    (∀ (y : (TorusLumps.stepBlockFrame p.side n).Cell) (z : (TorusLumps.stepBlockFrame p.side n).Site 0),
      z ∈ TorusLumps.baseSitesAt p.baseDepth (TorusLumps.fineHotLumps p (TorusLumps.fineLevelField p n
          (TorusFields.translate (TorusFields.siteOfInt fun i => (p.side : ℤ) * v i) W))) y ↔
        z + BlockAverages.siteOfCoords 0 (fun i => (p.side : ℤ) * v i) ∈
          TorusLumps.baseSitesAt p.baseDepth (TorusLumps.fineHotLumps p (TorusLumps.fineLevelField p n W))
            (y + BlockAverages.siteOfCoords 1 v)) ∧
    ∀ (b b' : (TorusLumps.stepBlockFrame p.side n).Cell → (TorusLumps.stepBlockFrame p.side n).Site 0)
      (c : (TorusLumps.stepBlockFrame p.side n).Cell × Fin 4),
      (∀ y, b' y + BlockAverages.siteOfCoords 0 (fun i => (p.side : ℤ) * v i) = b (y + BlockAverages.siteOfCoords 1 v)) →
      LumpContours.contourMean p.baseDepth (TorusLumps.fineHotLumps p (TorusLumps.fineLevelField p n
          (TorusFields.translate (TorusFields.siteOfInt fun i => (p.side : ℤ) * v i) W))) b'
          (TorusLumps.fineLevelField p n (TorusFields.translate (TorusFields.siteOfInt fun i => (p.side : ℤ) * v i) W)) c =
        LumpContours.contourMean p.baseDepth (TorusLumps.fineHotLumps p (TorusLumps.fineLevelField p n W)) b
          (TorusLumps.fineLevelField p n W) (c.1 + BlockAverages.siteOfCoords 1 v, c.2)
end YangMills.Construction.HullTrees
end
