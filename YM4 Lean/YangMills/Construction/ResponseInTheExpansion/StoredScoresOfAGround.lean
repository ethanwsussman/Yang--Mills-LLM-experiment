import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas TorusFields TorusLumps StepCosts BlockPlaces BlockOffsets BlockAverages WeightedResponses
theorem isCold_trivialField (m : ℕ) {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
theorem coldCaseGround_trivialField_isAdmissible (R : StepSetup) (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n)
    (hadm : R.params.Admissible) : (coldCaseGround R (trivialField n)).IsAdmissibleGround :=
  Or.inl ⟨hn, isCold_trivialField n (by have := hadm.σ_pos; positivity), rfl, rfl, rfl⟩
theorem coldCaseGround_labelAt_eq_none {R : StepSetup} {n : ℕ} [NeZero n] (V : TorusField n) (y : TorusSite n) :
    (coldCaseGround R V).state.markAt y = none := by
  unfold CoarseState.markAt
  rw [dif_neg]
  exact Finset.notMem_empty _
theorem recordedSiteScore_nonneg {R : StepSetup} {n : ℕ} [NeZero n] (A : ResponseSetup R) (hs : ∀ w, 0 ≤ A.score w)
    (G : GasGround R n) (z : TorusSite (n * R.params.side)) : 0 ≤ recordedSiteScore A G z := by
  classical
  unfold recordedSiteScore siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
theorem sumElim_getRight {Ω : Type} (s : Ω → ℝ) :
    ∀ (u : Unit ⊕ Ω) (h : u.isRight = true), s (u.getRight h) = Sum.elim (fun _ => 0) s u
  | Sum.inl _, h => by simp at h
  | Sum.inr _, _ => rfl
theorem sumElim_of_not_isRight {Ω : Type} (s : Ω → ℝ) :
    ∀ (u : Unit ⊕ Ω), ¬ u.isRight = true → (0 : ℝ) = Sum.elim (fun _ => 0) s u
  | Sum.inl _, _ => rfl
  | Sum.inr _, h => by simp at h
section
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem sum_recordedSiteScore_coldCaseGround (A : ResponseSetup R) (hodd : Odd R.params.side) (V : TorusField n)
    (Y : TorusSite n) :
    ∑ o ∈ centredCube R.params.side, recordedSiteScore A (coldCaseGround R V) (fineSite R.params.side Y 0 o) = 0 := by
  classical
  refine Finset.sum_eq_zero fun o _ => ?_
  unfold recordedSiteScore siteScore
  rw [dif_neg]
  intro h
  have hright := (Finset.mem_filter.mp h).2
  have hleft : (coldCaseGround R V).state.labelAt (fineSite R.params.side Y 0 o) = Sum.inl () := by
    show (emptyCoarseState R : CoarseState R n).labelAt _ = _
    unfold CoarseState.labelAt
    have hnone : (emptyCoarseState R : CoarseState R n).markAt
        (parentBlock R.params.side (fineSite R.params.side Y 0 o)) = none := by
      unfold CoarseState.markAt
      rw [dif_neg]
      exact Finset.notMem_empty _
    rw [hnone]
  rw [hleft] at hright
  simp at hright
theorem sum_recordedSiteScore_le (A : ResponseSetup R) (hs₁ : 0 ≤ A.responseParams.s₁) (hs : ∀ w, 0 ≤ A.score w)
    (hodd : Odd R.params.side) (V : TorusField n) (q : CoarseState R n) (Y : TorusSite n) :
    ∑ o ∈ centredCube R.params.side, recordedSiteScore A (hotCaseGround R V q) (fineSite R.params.side Y 0 o) ≤
      siteScore (coarseLabelScore A.responseParams.s₁ A.score) q.1 q.2 Y ∧
    (Y ∈ q.1 → A.responseParams.s₁ + ∑ o ∈ centredCube R.params.side,
        recordedSiteScore A (hotCaseGround R V q) (fineSite R.params.side Y 0 o) ≤
      siteScore (coarseLabelScore A.responseParams.s₁ A.score) q.1 q.2 Y) := by
  classical
  haveI : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
  rw [← sum_sitesInBlocks hodd Y (fun z => recordedSiteScore A (hotCaseGround R V q) z)]
  have hlab : ∀ z ∈ sitesInBlocks R.params.side {Y}, q.labelAt z =
      match q.markAt Y with
      | some s => s.siteLabel (siteOffset z)
      | none => Sum.inl () := by
    intro z hz
    have hb : parentBlock R.params.side z = Y := by simpa [sitesInBlocks] using hz
    unfold CoarseState.labelAt
    rw [hb]
    rfl
  have hval : ∀ z, recordedSiteScore A (hotCaseGround R V q) z =
      Sum.elim (fun _ => 0) A.score (q.labelAt z) := by
    intro z
    unfold recordedSiteScore siteScore
    by_cases hz : z ∈ (hotCaseGround R V q).recordedSites
    · rw [dif_pos hz]
      have hr := (Finset.mem_filter.mp hz).2
      exact sumElim_getRight A.score _ hr
    · rw [dif_neg hz]
      have hr : ¬ (q.labelAt z).isRight = true :=
        fun h => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact sumElim_of_not_isRight A.score _ hr
  rcases hrec : q.markAt Y with _ | st
  · have hzero : ∑ z ∈ sitesInBlocks R.params.side {Y}, recordedSiteScore A (hotCaseGround R V q) z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      rw [hval, hlab z hz, hrec]
      rfl
    rw [hzero]
    have hnn : ∀ w : CoarseLabel R.labels.Ω R.params.side, 0 ≤ coarseLabelScore A.responseParams.s₁ A.score w := by
      intro w
      cases w with
      | inl _ => exact hs₁
      | inr st' =>
        refine add_nonneg hs₁ (Finset.sum_nonneg fun o _ => ?_)
        cases st'.siteLabel o with
        | inl _ => exact le_rfl
        | inr a => exact hs a
    refine ⟨?_, fun hy => ?_⟩
    · unfold siteScore
      split_ifs with hy
      · exact hnn _
      · exact le_rfl
    · unfold siteScore
      rw [dif_pos hy, add_zero]
      unfold CoarseState.markAt at hrec
      rw [dif_pos hy] at hrec
      generalize q.2 ⟨Y, hy⟩ = u at hrec
      cases u with
      | inl _ => exact le_rfl
      | inr a => simp at hrec
  · have hy : Y ∈ q.1 := by
      by_contra hy
      unfold CoarseState.markAt at hrec
      rw [dif_neg hy] at hrec
      simp at hrec
    have hq : q.2 ⟨Y, hy⟩ = Sum.inr st := by
      unfold CoarseState.markAt at hrec
      rw [dif_pos hy] at hrec
      generalize q.2 ⟨Y, hy⟩ = u at hrec
      cases u with
      | inl _ => simp at hrec
      | inr a =>
        simp at hrec
        rw [hrec]
    unfold siteScore
    rw [dif_pos hy, hq]
    have hsum : ∑ z ∈ sitesInBlocks R.params.side {Y}, recordedSiteScore A (hotCaseGround R V q) z =
        ∑ o : BlockOffset R.params.side, Sum.elim (fun _ => 0) A.score (st.siteLabel o) := by
      refine Finset.sum_nbij' siteOffset (blockSite Y) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
      · intro o _
        simp [sitesInBlocks, parentBlock_blockSite]
      · intro z hz
        have hb : parentBlock R.params.side z = Y := by simpa [sitesInBlocks] using hz
        rw [← hb]
        exact blockSite_parentBlock_siteOffset z
      · intro o _
        exact siteOffset_blockSite Y o
      · intro z hz
        rw [hval, hlab z hz, hrec]
    rw [hsum]
    have e : coarseLabelScore A.responseParams.s₁ A.score (Sum.inr st) =
        A.responseParams.s₁ + ∑ o : BlockOffset R.params.side, Sum.elim (fun _ => 0) A.score (st.siteLabel o) := rfl
    rw [e]
    exact ⟨by linarith, fun _ => le_rfl⟩
end
end YangMills.Construction.ResponseInTheExpansion
end
