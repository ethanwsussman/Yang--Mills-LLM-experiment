import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.LawByMomentsOfTheFlow.FormOfAnInvariantFunction
import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheResponsesAtOne
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses StepCosts ShareFamilies BlockAverages ResponseInTheExpansion
  LevelTestFunctions RenormalizationStepParameters
private theorem trivialField_isCold {n : ℕ} {s : ℝ} (hs : 0 < s) : IsCold s (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem perturb_zero_trivialField {n k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    perturb c X 0 (trivialField n) = trivialField n := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.perturb_zero_trivialField <;> assumption
private theorem eventually_isCold_perturb (hc : ColdNearStatement) {n : ℕ} [NeZero n] {s : ℝ} (hs : 0 < s) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsCold s (perturb c X τ (trivialField n)) :=
  hc n (trivialField n) k c X 0 s (by rw [perturb_zero_trivialField]; exact trivialField_isCold hs)
private theorem contDiffAt_two_perturb {n : ℕ} {ψ : TorusField n → ℝ} (h : ContDiffThreeAt ψ (trivialField n)) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ψ (perturb c X σ (trivialField n))) 0 :=
  (h k c X).of_le (by norm_num)
private theorem levelShareFamily_eq {a : ℝ} {L u n : ℕ} [NeZero n] (y : TorusSite n) :
    levelShareFamily a L u n y = levelShare a L u Finset.univ y := by
  funext W
  exact dif_neg (NeZero.ne n)
private theorem quadraticForms_at_point (hF : invariantFunctionFormStatement) (hc : ColdNearStatement)
    {Λ : MomentParameters} {C : ℝ} (hσ : 0 < Λ.stepParams.threshold)
    (hsh : ∀ u, IsCurvatureFamily Λ.stepParams C (levelShareFamily Λ.stepParams.coupling Λ.stepParams.side u))
    (S : MomentPoint Λ) (t : ℕ) (ht : t ≤ S.data.windowLevel) (n : ℕ) [NeZero n] (hn : Λ.stepParams.n₀ ≤ n)
    (y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) :
    HasQuadraticFormAtIdentity (levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y) ∧
      HasQuadraticFormAtIdentity (responseRemainder (S.resp t).cold n y h) ∧
      HasQuadraticFormAtIdentity fun W => (S.resp t).cold n y W h := by
  have hst := S.onFlow t ht
  rw [← S.stage_eq t ht] at hst
  have row := hst.onFamily.admissible.bounds
  have hflat : IsCold Λ.stepParams.threshold (trivialField n) := trivialField_isCold hσ
  have hfam := hsh (S.tower.stage t).depth
  have shareSmooth : ContDiffThreeAt
      (levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y) (trivialField n) := by
    rw [← levelShareFamily_eq]
    exact hfam.smooth n hn y (trivialField n) hflat
  have restSmooth : ContDiffThreeAt (responseRemainder (S.resp t).cold n y h) (trivialField n) :=
    row.remainder_smooth n hn y (trivialField n) hflat h
  have densitySmooth : ContDiffThreeAt ((S.resp t).siteRemainder n y) (trivialField n) :=
    row.site_family.smooth n hn y (trivialField n) hflat
  have hgauge : ∀ (h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) (W : TorusField n),
      IsCold Λ.stepParams.threshold W →
      ∀ g : TorusSite n → UnitQuaternion, (S.resp t).cold n y (gaugeTransform g W) h' = (S.resp t).cold n y W h' :=
    fun h' W hW g => row.cold_gauge n hn y g W hW h'
  refine ⟨hF n _ Λ.stepParams.threshold hσ (fun W hW g => ?_) fun k c X => contDiffAt_two_perturb shareSmooth c X,
    hF n _ Λ.stepParams.threshold hσ (fun W hW g => ?_) fun k c X => contDiffAt_two_perturb restSmooth c X,
    hF n _ Λ.stepParams.threshold hσ (fun W hW g => hgauge h W hW g) fun k c X => ?_⟩
  · rw [← levelShareFamily_eq]
    exact hfam.gauge n hn y g W hW
  · simp only [responseRemainder, hgauge _ W hW g]
  · have hsplit : ∀ W : TorusField n, IsCold Λ.stepParams.threshold W → (S.resp t).cold n y W h =
        responseRemainder (S.resp t).cold n y h W + blockMean Λ.stepParams.side (S.tower.stage t).depth n y h *
          ((S.resp t).coeff * levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y W +
            (S.resp t).siteRemainder n y W - (S.resp t).siteRemainder n y (trivialField n) +
            (S.resp t).cold n y (trivialField n) (constOneWeight _)) := by
      intro W hW
      have hs := row.share_site n hn y W hW
      simp only [centeredResponse, centered] at hs
      simp only [responseRemainder]
      rw [show (S.resp t).cold n y W (constOneWeight _) = (S.resp t).coeff *
          levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y W +
          ((S.resp t).siteRemainder n y W - (S.resp t).siteRemainder n y (trivialField n)) +
          (S.resp t).cold n y (trivialField n) (constOneWeight _) by linarith]
      ring
    have hsum : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
        responseRemainder (S.resp t).cold n y h (perturb c X σ (trivialField n)) +
          blockMean Λ.stepParams.side (S.tower.stage t).depth n y h *
          ((S.resp t).coeff * levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y
              (perturb c X σ (trivialField n)) +
            (S.resp t).siteRemainder n y (perturb c X σ (trivialField n)) -
            (S.resp t).siteRemainder n y (trivialField n) +
            (S.resp t).cold n y (trivialField n) (constOneWeight _))) 0 :=
      (contDiffAt_two_perturb restSmooth c X).add (contDiffAt_const.mul
        ((((contDiffAt_const.mul (contDiffAt_two_perturb shareSmooth c X)).add
          (contDiffAt_two_perturb densitySmooth c X)).sub contDiffAt_const).add contDiffAt_const))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [eventually_isCold_perturb hc hσ c X] with τ hτ
    exact hsplit _ hτ
theorem responsesHaveForms (hF : invariantFunctionFormStatement)
    (hS : levelSharesUniformStatement) (hc : ColdNearStatement) : responsesHaveFormsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hT⟩ := hS a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ Tb hTa hTL hD hCS hCH hr hCd Kr _ => ?_⟩
  obtain ⟨y₀, hy⟩ := hT L hL hL₀ Tb hTa hTL hD hCS hCH hr hCd
  refine ⟨y₀, fun y hy₀ hret hrow g _ _ k _ _ _ R d _ => ?_⟩
  obtain ⟨C, _, hC⟩ := hy y hy₀ hret hrow
  refine ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S t ht n _ hn z h => ?_⟩
  exact quadraticForms_at_point hF hc (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) hD.σ_pos (fun u => (hC u).1) S t ht n hn z h
end YangMills.Construction.MomentLaw
end
