import YangMills.Construction.ClusterExpansionOfAStep.GroundBesideItsLabels
import YangMills.Construction.ClusterExpansionOfAStep.LabelsBySlices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SliceStates
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusLumps TorusFields StepSettings StepCosts SlicedLabels
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Glue
variable {Y YP : Finset (TorusSite n)} (ω : Y → CoarseLabel R.labels.Ω R.params.side)
  (ν : YP → CoarseLabel R.labels.Ω R.params.side)
def glueState : CoarseState R n :=
  ⟨Y, glueLabel Y YP ω ν⟩
theorem markAt_glueState_of_mem (hsub : YP ⊆ Y) {y : TorusSite n} (hy : y ∈ YP) :
    (glueState ω ν).markAt y = match ν ⟨y, hy⟩ with
      | Sum.inr s => some s
      | Sum.inl _ => none := by
  classical
  have hyY : y ∈ Y := hsub hy
  simp only [CoarseState.markAt, glueState, hyY, dif_pos, glueLabel, hy]
  rfl
theorem markAt_glueState_of_not_mem {y : TorusSite n} (hy : y ∉ YP) :
    (glueState ω ν).markAt y = CoarseState.markAt (⟨Y, ω⟩ : CoarseState R n) y := by
  classical
  by_cases hyY : y ∈ Y
  · simp only [CoarseState.markAt, glueState, hyY, dif_pos, glueLabel, hy, dif_neg, not_false_eq_true]
  · have h1 : ∀ q : CoarseState R n, q.1 = Y → q.markAt y = none := fun q hq => by
      unfold CoarseState.markAt
      rw [dif_neg (by rw [hq]; exact hyY)]
    rw [h1 _ rfl, h1 _ rfl]
end Glue
section Slice
variable {Y YP : Finset (TorusSite n)} (ω : Y → CoarseLabel R.labels.Ω R.params.side)
  (Z : Finset YP) (a : Z → Bool) (bad : Z → BlockBond R.params.side → Bool) (o : Z → BlockOffset R.params.side)
  (A : Finset (Z × BlockOffset R.params.side)) (B : Finset (Z × BlockBond R.params.side)) (g : B → UnitQuaternion)
def sliceState (u : A → R.labels.Ω) : CoarseState R n := glueState ω (sliceLabel Z a bad o A B g u)
def sliceBlockData (u : A → R.labels.Ω) (y : Z) : BlockLabels R.labels.Ω R.params.side :=
  { isCore := a y
    badBond := bad y
    siteLabel := fun k => fillOn A u (y, k)
    basePoint := o y
    linkValue := fun q => fillOn B g (y, q) }
variable {ω Z a bad o A B g}
theorem markAt_sliceState_of_mem (hsub : YP ⊆ Y) (u : A → R.labels.Ω) {y : TorusSite n} (hy : y ∈ YP)
    (hZ : (⟨y, hy⟩ : YP) ∈ Z) :
    (sliceState ω Z a bad o A B g u).markAt y = some (sliceBlockData Z a bad o A B g u ⟨⟨y, hy⟩, hZ⟩) := by
  classical
  unfold sliceState
  rw [markAt_glueState_of_mem ω _ hsub hy]
  simp only [sliceLabel, fillOn, hZ, dif_pos]
  rfl
theorem markAt_sliceState_of_not_mem_blocks (hsub : YP ⊆ Y) (u : A → R.labels.Ω) {y : TorusSite n}
    (hy : y ∈ YP) (hZ : (⟨y, hy⟩ : YP) ∉ Z) :
    (sliceState ω Z a bad o A B g u).markAt y = none := by
  classical
  unfold sliceState
  rw [markAt_glueState_of_mem ω _ hsub hy]
  simp only [sliceLabel, fillOn, hZ, dif_neg, not_false_eq_true]
theorem markAt_sliceState_of_not_mem (u : A → R.labels.Ω) {y : TorusSite n} (hy : y ∉ YP) :
    (sliceState ω Z a bad o A B g u).markAt y = CoarseState.markAt (⟨Y, ω⟩ : CoarseState R n) y :=
  markAt_glueState_of_not_mem ω _ hy
omit [NeZero n] in
theorem forgetLabels_sliceState (u u' : A → R.labels.Ω) (y : Z) :
    BlockLabels.forgetLabels (sliceBlockData Z a bad o A B g u y) =
      BlockLabels.forgetLabels (sliceBlockData Z a bad o A B g u' y) := by
  classical
  unfold BlockLabels.forgetLabels sliceBlockData
  congr 1
  funext k
  unfold fillOn
  by_cases h : (y, k) ∈ A <;> simp [h]
theorem sliceState_agreeUpToLabels (hsub : YP ⊆ Y) (u u' : A → R.labels.Ω) :
    (sliceState ω Z a bad o A B g u).AgreeUpToLabels (sliceState ω Z a bad o A B g u') := by
  classical
  intro y
  by_cases hy : y ∈ YP
  · by_cases hZ : (⟨y, hy⟩ : YP) ∈ Z
    · rw [markAt_sliceState_of_mem hsub u hy hZ, markAt_sliceState_of_mem hsub u' hy hZ]
      simp only [Option.map_some, forgetLabels_sliceState u u']
    · rw [markAt_sliceState_of_not_mem_blocks hsub u hy hZ, markAt_sliceState_of_not_mem_blocks hsub u' hy hZ]
  · rw [markAt_sliceState_of_not_mem u hy, markAt_sliceState_of_not_mem u' hy]
theorem labelAt_sliceState_of_mem (hsub : YP ⊆ Y) (u : A → R.labels.Ω) {z : TorusSite (n * R.params.side)}
    {y : TorusSite n} (hb : parentBlock R.params.side z = y) (hy : y ∈ YP) (hZ : (⟨y, hy⟩ : YP) ∈ Z) :
    (sliceState ω Z a bad o A B g u).labelAt z = fillOn A u (⟨⟨y, hy⟩, hZ⟩, siteOffset z) := by
  unfold CoarseState.labelAt
  rw [hb, markAt_sliceState_of_mem hsub u hy hZ]
  rfl
theorem labelAt_sliceState_of_not_mem_blocks (hsub : YP ⊆ Y) (u : A → R.labels.Ω)
    {z : TorusSite (n * R.params.side)} {y : TorusSite n}
    (hb : parentBlock R.params.side z = y) (hy : y ∈ YP) (hZ : (⟨y, hy⟩ : YP) ∉ Z) :
    (sliceState ω Z a bad o A B g u).labelAt z = Sum.inl () := by
  unfold CoarseState.labelAt
  rw [hb, markAt_sliceState_of_not_mem_blocks hsub u hy hZ]
theorem labelAt_sliceState_of_not_mem (u u' : A → R.labels.Ω) {z : TorusSite (n * R.params.side)}
    (hy : parentBlock R.params.side z ∉ YP) :
    (sliceState ω Z a bad o A B g u).labelAt z = (sliceState ω Z a bad o A B g u').labelAt z := by
  unfold CoarseState.labelAt
  rw [markAt_sliceState_of_not_mem u hy, markAt_sliceState_of_not_mem u' hy]
end Slice
end YangMills.Construction.SliceStates
end
