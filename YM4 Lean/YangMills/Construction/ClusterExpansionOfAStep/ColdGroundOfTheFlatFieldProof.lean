import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundOfTheFlatField
import YangMills.Construction.ClusterExpansionOfAStep.GroundBesideItsLabels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames RenormalizationStepParameters StepSettings StepGas StepCosts TorusFields TorusLumps
namespace TrivialFieldGround
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem markAt_empty (y : TorusSite n) : (emptyCoarseState R : CoarseState R n).markAt y = none := by
  unfold CoarseState.markAt
  rw [dif_neg]
  simp [emptyCoarseState]
theorem labelAt_empty (z : TorusSite (n * R.params.side)) :
    (emptyCoarseState R : CoarseState R n).labelAt z = Sum.inl () := by
  unfold CoarseState.labelAt
  rw [markAt_empty]
theorem recordedSites_empty : (coldCaseGround R (trivialField n)).recordedSites = ∅ := by
  classical
  ext z
  simp only [GasGround.recordedSites, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  show ¬ ((emptyCoarseState R : CoarseState R n).labelAt z).isRight = true
  rw [labelAt_empty]
  simp
theorem not_isRecorded (b : TorusBond (n * R.params.side)) : ¬ (coldCaseGround R (trivialField n)).IsRecorded b := by
  rintro ⟨s, hs, -⟩
  have : (emptyCoarseState R : CoarseState R n).markAt (parentBlock R.params.side b.1) = some s := hs
  rw [markAt_empty] at this
  simp at this
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
theorem free_eq : (coldCaseGround R (trivialField n)).groundSetting.free = (chartBonds R.params.side n) := by
  classical
  show ((coldCaseGround R (trivialField n)).freeBonds.filter
    fun b => (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl ()) = _
  ext b
  simp only [Finset.mem_filter, fieldAt_empty, and_true, GasGround.freeBonds, markedBonds]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩
    exact h
  · intro h
    exact ⟨⟨h, by
      show parentBlock R.params.side b.1 ∉ (∅ : Finset (TorusSite n))
      simp⟩, not_isRecorded b⟩
theorem storedBlockSet_empty (hYt : (coldCaseGround R (trivialField n)).groundSetting.support = ∅) :
    (coldCaseGround R (trivialField n)).groundSetting.storedBlockSet ⟨∅, ∅⟩ = ∅ := by
  classical
  have h1 : (coldCaseGround R (trivialField n)).groundSetting.storedComponents ⟨∅, ∅⟩ = ∅ := by
    unfold ChartSetting.storedComponents clusterComponents chainComponents
    simp only [hYt]
    simp [sitesInBlocks]
  unfold ChartSetting.storedBlockSet
  rw [h1]
  ext y
  simp [coreBlocks, thickening]
end TrivialFieldGround
open TrivialFieldGround in
theorem trivialFieldColdGround_holds : TrivialFieldColdGround := by
  classical
  intro T hT
  refine ⟨T.floorMin, fun y hy R hR n _ hn => ?_⟩
  have hfit : R.params.Admissible := hR.params_eq ▸ hT.fits y hy
  have hn' : R.params.n₀ ≤ n := by
    have h : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    rw [h]
    exact hn
  have hcold : IsCold (9 / 8 * R.params.threshold) (trivialField n) := by
    intro x μ ν _
    have h0 : curvature (trivialField n) x μ ν = 0 := by simp [curvature, holonomy, trivialField]
    rw [h0]
    have := hfit.σ_pos
    positivity
  have hYt : (coldCaseGround R (trivialField n)).groundSetting.support = ∅ := by
    rw [groundSetting_support, recordedSites_empty]
  have hst := storedBlockSet_empty hYt
  refine ⟨⟨hn', hcold, rfl, rfl, rfl⟩, ⟨?_, Or.inr ⟨rfl, hcold⟩⟩, fun hs => ⟨hs.isBaseChoice, ?_⟩, rfl, hYt⟩
  · rw [free_eq]
    unfold ChartSetting.freeBondsLeft
    rw [hst]
    ext b
    simp
  · intro b _ htree
    have hnf : (b.1, b.2) ∉ ((coldCaseGround R (trivialField n)).settingWithFamily GasFamily.empty).free := by
      intro hb
      have h1 : b ∈ (coldCaseGround R (trivialField n)).groundSetting.free := hb
      rw [free_eq] at h1
      exact (Finset.mem_filter.mp h1).2 htree
    show ((coldCaseGround R (trivialField n)).settingWithFamily GasFamily.empty).field 0 b.1 b.2 = 1
    unfold ChartSetting.field
    rw [dif_neg hnf]
    simp only [GasGround.settingWithFamily, fieldAt_empty]
    show (emptyCoarseState R : CoarseState R n).fieldWithStoredLinks (trivialField _) b.1 b.2 = 1
    unfold CoarseState.fieldWithStoredLinks
    rw [markAt_empty]
    rfl
end YangMills.Construction.ClusterExpansionOfAStep
