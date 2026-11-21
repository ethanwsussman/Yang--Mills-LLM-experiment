import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAStateAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ParametersAgreeWithTheSum
import YangMills.Construction.ClusterExpansionOfAStep.PlacesOfABlock
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceBeforeItsLength
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceReturns
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages TorusLumps TorusFields StepSettings RenormalizationStepParameters StepGas StepFloors
  WeightedResponses BlockPlaces LumpContours
namespace CoarseScore
theorem s₁_nonneg_of_admissible {K : ResponseParameters} {P : StepParameters} (hK : K.Admissible P)
    (hc : 1 ≤ P.coupling) : 0 ≤ K.s₁ := by
  have hKc := hK.Kc_ge
  have hN := hK.N₀_nonneg
  have hC : 0 ≤ K.C₀ + 2 := by
    rw [hK.C₀_eq]
    linarith
  rw [hK.s₁_eq]
  have hprod : 0 ≤ 2 * (P.side : ℝ) ^ 4 * (K.C₀ + 2) := by positivity
  linarith
theorem coarseLabelScore_nonneg {Ω : Type} {L : ℕ} {s₁ : ℝ} {s : Ω → ℝ} (h₁ : 0 ≤ s₁) (hs : ∀ w, 0 ≤ s w)
    (w : CoarseLabel Ω L) : 0 ≤ coarseLabelScore s₁ s w := by
  rcases w with u | r
  · exact h₁
  · refine add_nonneg h₁ (Finset.sum_nonneg fun o _ => ?_)
    rcases r.siteLabel o with u | a
    · exact le_rfl
    · exact hs a
theorem measurable_siteLabel {Ω : Type} [MeasurableSpace Ω] {L : ℕ} (o : BlockOffset L) :
    Measurable fun r : BlockLabels Ω L => r.siteLabel o := by apply _root_.YangMills.Construction.StateMeasurability.measurable_siteLabel <;> assumption
theorem measurable_coarseLabelScore {Ω : Type} [MeasurableSpace Ω] {L : ℕ} (s₁ : ℝ) {s : Ω → ℝ}
    (hs : Measurable s) : Measurable (coarseLabelScore (L := L) s₁ s) := by
  have h : coarseLabelScore (L := L) s₁ s = Sum.elim (fun _ => s₁)
      (fun r => s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) s (r.siteLabel o)) := by
    funext w
    rcases w with u | r <;> rfl
  rw [h]
  refine Measurable.sumElim measurable_const (measurable_const.add ?_)
  refine Finset.measurable_sum _ fun o _ => ?_
  exact (Measurable.sumElim measurable_const hs).comp (measurable_siteLabel o)
theorem coarseLabelScore_gauge {R : StepSetup} {n : ℕ} [NeZero n] [NeZero R.params.side] {s₁ : ℝ}
    {s : R.labels.Ω → ℝ}
    (hs : ∀ (m : ℕ) [NeZero m] (Y : Finset (TorusSite m)) (g : TorusSite m → UnitQuaternion)
      (ω : Y → R.labels.Ω) (y : Y), s (R.labels.act Y g ω y) = s (ω y))
    (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (y : Y) :
    coarseLabelScore s₁ s (coarseGaugeAct (R := R) Y g ω y) = coarseLabelScore s₁ s (ω y) := by
  classical
  unfold coarseGaugeAct
  rcases hw : ω y with u | r
  · rfl
  · show s₁ + _ = s₁ + _
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    set q : CoarseState R n := ⟨Y, ω⟩ with hq
    have hrec : q.markAt y.1 = some r := by
      unfold CoarseState.markAt
      rw [dif_pos y.2]
      show (match ω ⟨y.1, y.2⟩ with
        | Sum.inr s => some s
        | Sum.inl _ => none) = _
      have : (⟨y.1, y.2⟩ : Y) = y := rfl
      rw [this, hw]
    have hat : q.labelAt (blockSite y.1 o) = r.siteLabel o := by
      unfold CoarseState.labelAt
      rw [parentBlock_blockSite, hrec, siteOffset_blockSite]
    unfold gaugeOnCoarseState
    by_cases h : blockSite (L := R.params.side) y.1 o ∈ q.labelSet
    · simp only [dif_pos h, Sum.elim_inr]
      rw [hs]
      have hne : q.labelAt (blockSite y.1 o) ≠ Sum.inl () := (Finset.mem_filter.mp h).2
      rcases hl : r.siteLabel o with u | a
      · exact absurd (hat.trans hl) hne
      · have h2 : q.labelAt (blockSite y.1 o) = Sum.inr a := hat.trans hl
        have h3 : q.labeling ⟨_, h⟩ = a := by
          unfold CoarseState.labeling
          split
          · rename_i b hb
            exact Sum.inr.inj (hb.symm.trans h2)
          · rename_i b hb
            exact absurd (hb.symm.trans h2) (by simp)
        rw [h3]
        rfl
    · simp only [dif_neg h]
end CoarseScore
open CoarseScore in
theorem scoredPriceCoversCoarseScore_proof (hb : scoredComponentPriceBound)
    (hsum : ClassExponentLePrice) (htab : ParameterChoiceMeetsClassSum)
    (hfl : EventuallyFloorConditions) : ScoredPriceCoversCoarseScore := by
  obtain ⟨rt₀, hrt₀, hb'⟩ := hb
  refine ⟨rt₀, hrt₀, fun T hT hrt K => ?_⟩
  by_cases hs₁ : 0 ≤ K.s₁
  swap
  · refine ⟨T.floorMin, fun y hy R A hK hA => ?_⟩
    have hadm : R.params.Admissible := hA.onFamily.params_eq ▸ hT.fits y hy
    exact absurd (hK ▸ s₁_nonneg_of_admissible hA.admissible.params_admissible hadm.a_ge) hs₁
  obtain ⟨CE, y₀, hCE, hbound⟩ := hb' T hT hrt K.s₁ hs₁
  obtain ⟨y₂, hy₂⟩ := hfl T hT (2 ^ 18 * CE + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨max y₀ (max y₂ T.floorMin), fun y hy R A hK hA hforms hx' hL => ?_⟩
  subst hK
  have hy0 : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyT : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hP := hA.onFamily.params_eq
  have hyps : ClassSumHypotheses R.params T.cE CE := by
    rw [hP]
    exact htab T hT CE 1 y hCE hyT fun x hx => hy₂ x (hy2.trans hx)
  have hadm : R.params.Admissible := by
    rw [hP]
    exact hT.fits y hyT
  have hy1 : R.params.y₁ ≤ R.coupling := by
    rw [hP]
    exact hA.onFamily.le_coupling
  have hshift : |R.nextCoupling - R.coupling| ≤ 2 * R.params.B := by
    have hB : R.params.B = T.B := by rw [hP]; rfl
    rw [hB]
    exact hA.abs_sub_le
  have hsc := hA.admissible.price
  haveI : NeZero R.params.side := ⟨by have := hadm.L_ge; omega⟩
  refine
    { nonneg := coarseLabelScore_nonneg hs₁ hsc.nonneg
      borel := measurable_coarseLabelScore _ hsc.borel
      gauge := fun n _ Y g ω y => coarseLabelScore_gauge hsc.gauge Y g ω y
      price := fun n _ hn V Y ω P hull hPc hoff => ?_ }
  refine hbound y hy0 R hA.onFamily hforms hx' hshift A.score hsc n hn V Y ω P hull hPc hoff _ ?_
  intro ν W Yt ωt bad b _ hst
  have hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) :=
    (congrArg Sigma.fst hst).symm
  have hPc' : P ⊆ chainComponents R.nextRange
      (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)) := hY ▸ hPc
  exact hsum R.params T.cE CE hadm hyps R.coupling R.nextCoupling hy1 hshift n hn.1 V W bad Yt P hPc'
end YangMills.Construction.ResponseInTheExpansion
end
