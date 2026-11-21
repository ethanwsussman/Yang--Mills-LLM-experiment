import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.LengthOfAnImageUnion
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts StepMarks
variable {R : StepSetup} {n : ℕ}
section Pieces
variable [NeZero n] (s : ChartSetting R n) (c : SettingCore R n)
open Classical in
def ChartSetting.freeComponents : Finset (Finset (TorusSite (n * R.params.side))) :=
  (s.storedComponents c).filter fun X => ¬ (X ∩ sitesInBlocks R.params.side c.core).Nonempty
def ChartSetting.attachedPart : Finset (TorusSite (n * R.params.side)) :=
  attachedSites R.params.side R.range c.badBonds s.support c.core
def ChartSetting.coarseHullOf : Finset (TorusSite n) :=
  coarseHull R.params.side R.range (clusterRange R.nextCoupling) c.badBonds s.support c.core
open Classical in
def ChartSetting.IsPiece (K : Finset (TorusSite (n * R.params.side))) : Prop :=
  (∃ P ⊆ s.freeComponents c, K = P.biUnion id) ∨
    ∃ Q ⊆ chainComponents (clusterRange R.nextCoupling) (s.coarseHullOf c),
      K = s.attachedPart c ∩ sitesInBlocks R.params.side (Q.biUnion id)
structure ChartSetting.IsMarked : Prop where
  bases : IsBaseChoice R.params.baseDepth (stepHotLumps R.params s.fine) s.bases
  fine_on_trees : ∀ b : TorusBond (n * R.params.side), parentBlock R.params.side b.1 ∉ s.storedBlockSet c →
    IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2) → s.fine b.1 b.2 = 1
open Classical in
def ChartSetting.lumpsInPiece (K : Finset (TorusSite (n * R.params.side))) :
    Finset (Finset (TorusSite (n * R.params.side))) :=
  (torusHotLumps R.params s.fine).filter (· ⊆ K)
open Classical in
def ChartSetting.coarseLumpsInPiece (K : Finset (TorusSite (n * R.params.side))) :
    Finset (Finset (TorusSite n)) :=
  (torusHotLumps R.params s.coarse).filter fun l => l ⊆ c.core ∧ sitesInBlocks R.params.side l ⊆ K
def ChartSetting.restSet : Finset (TorusSite n) :=
  Finset.univ \ thickening lumpRange (c.core ∩ torusHotSites R.params s.coarse)
def ChartSetting.energyNear (N : Finset (TorusSite n)) (η : FreeCoords s.free) : ℝ :=
  ∑ Y ∈ N, s.blockCostAt Y (s.extendByZero N fun b => η b.1) +
    ∑ Y ∈ Finset.univ \ N, (s.blockCostAt Y (s.extendByZero N fun b => η b.1) - s.blockCostAt Y 0)
end Pieces
end YangMills.Construction.StepSettings
namespace YangMills.Construction.StepEnergy
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts StepMarks
  StepSettings
def EnergyNearPieceAt (R : StepSetup) (cE C c : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n) (st : SettingCore R n) (K : Finset (TorusSite (n * R.params.side)))
    (η : FreeCoords s.free), R.params.n₀ ≤ n → s.IsAdmissible → s.IsCoreOf st → s.IsMarked st → s.IsPiece st K →
    s.InBalls η →
    (∀ b ∈ st.badBonds, b.1 ∈ K → b ∈ chartBonds R.params.side n ∧
      5 * R.ballRadius / 8 ≤
        ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse s.fine b : ℍ[ℝ])‖) →
    R.coupling * (∑ Y ∈ blocksNear R.params.side R.range K,
          levelShare R.params.coupling R.params.side (R.depth + 1) (s.restSet st) Y s.coarse +
        6 * R.params.κ * R.params.threshold ^ 2 * ((s.coarseLumpsInPiece st K).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ) +
        cE * ((badBlocksOff R.params.side st.badBonds st.core K).card : ℝ)) -
      R.coupling ^ C * Real.exp (-(c * R.range)) * ((blocksNear R.params.side R.range K).card : ℝ) ≤
    R.coupling * (s.energyNear (blocksNear R.params.side R.range K) η +
      R.params.κ * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ))
def EnergyNearPieceBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ R : StepSetup, R.OnParameters T y → EnergyNearPieceAt R T.cE C c
end YangMills.Construction.StepEnergy
end
