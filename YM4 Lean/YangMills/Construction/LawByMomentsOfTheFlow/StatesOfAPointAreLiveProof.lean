import YangMills.Construction.LawByMomentsOfTheFlow.GradientsOfAStepAreFarApartProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreSizedProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllParameters Q₁)
    (hm : ∀ Λ, Q₁ Λ → Q₂ Λ) : ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.stepParams.Admissible := by apply _root_.YangMills.SharedProofs.p7443 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : WeightedResponses.HoldsAtAdmissibleParameters P) : ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p43324 <;> assumption
section Live
variable {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ)
private theorem ae_live_of_density (β : ℝ) (k n : ℕ) [NeZero n] (hb : TorusLumps.IsBlockTorusSide ℓ n)
    (hrow : TorusLumps.HullExpansion ℓ (T.stage k).depth (T.stage k).coupling (T.stage k).functional
      (T.stage k).density (T.stage k).labels (T.stage k).labelWeight (T.stage k).clusterFactor
      (T.stage k).siteDensity) (hst : Measurable (WeightedResponses.stageState T k n))
    (hZ : (0 : ℝ) < ∫ W, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side k n) W
      ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side k n)))
    (hd : ∀ G : WeightedResponses.StageState T k n → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side k n) W
          ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side k n))) *
        ∫⁻ u, G (WeightedResponses.stageState T k n u) ∂(WeightedResponses.markedSampleLaw T β k n) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (TorusLumps.IsHullState ℓ (TorusLumps.clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(TorusFields.fieldHaar n)) :
    ∀ᵐ d ∂(WeightedResponses.markedSampleLaw T β k n),
      WeightedResponses.IsLiveState ℓ (T.stage k).coupling (T.stage k).labelWeight
        (WeightedResponses.stageState T k n d).1 (WeightedResponses.stageState T k n d).2.1
        (WeightedResponses.stageState T k n d).2.2 := by apply _root_.YangMills.SharedProofs.p25706 <;> assumption
end Live
theorem liveStatesStatement_holds (hDen : StageDensity.stageStateDensityStatement)
    (hLaw : WeightedResponses.ChainIsProbabilityLaw)
    (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) : liveStatesStatement := by
  unfold liveStatesStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and forAllParameters_admissible
    (forAllParameters_of_holdsOnAllParameters hDen)) fun Λ H => ?_
  obtain ⟨hFit, HD⟩ := H
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S u hu n _ hb => ?_⟩
  have lev : ∀ j ≤ S.data.windowLevel,
      ResponseInTheExpansion.StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ :=
    fun j hj => by
      have h := S.onFlow j hj
      rwa [← S.stage_eq j hj] at h
  have hOnParameters : ResponseInTheExpansion.IsTowerAtParameters Λ.table Λ.floor S.tower S.β u := by
    refine ⟨S.startsAtWilson, fun j hj => ?_, fun j hj => (lev j (hj.trans hu)).onFamily.onFamily⟩
    cases j with
    | zero => exact (lev 0 (Nat.zero_le _)).coupling_eq
    | succ j' => exact (lev j' (by omega)).nextCoupling_eq
  have hZ := (hLaw Λ.stepParams hFit hFit.depth_lt S.β (fun _ => 0) u n).2.1
  exact ae_live_of_density S.tower S.β u n hb (hOnParameters.onFamily u le_rfl).isStep.1.2
    (hSt Λ.stepParams hFit S.tower u n) hZ
    (fun G hG => HD S.tower S.β u n hOnParameters S.marksMeasurable hb G hG)
end YangMills.Construction.MomentLaw
end
