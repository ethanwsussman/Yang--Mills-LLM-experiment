import YangMills.Construction.ClusterExpansionOfAStep.FieldsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASettingProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariableInASetting
import YangMills.Construction.ResponseInTheExpansion.ScoresOfTwoSettings
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
private theorem stepHotLumps_eq_of_torusHotLumps_eq {p : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
    {U U' : TorusFields.TorusField (n * p.side)}
    (h : TorusLumps.torusHotLumps p U = TorusLumps.torusHotLumps p U') :
    StepCosts.stepHotLumps p U = StepCosts.stepHotLumps p U' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.stepHotLumps_eq_of_torusHotLumps_eq <;> assumption
theorem supportResponseLocality (hPot : StepSettings.PotentialFactorization)
    (hF : StepSettings.FieldsAgreeOfCoordsAgree)
    (hSc : WeightedResponses.BondScoresAgreeNearBlocks) : supportResponseLocalityStatement := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ⟨T.floorMin, fun y hy R A hAK htab n _ s hn hs => ?_⟩⟩
  have hon := htab.onFamily
  have hrow : R.HasExpansions := hon.isStep.1
  have hσ : R.params.threshold = T.threshold := by rw [hon.params_eq]; rfl
  have hadm : R.params.Admissible := by rw [hon.params_eq]; exact hT.fits y hy
  have hρA : 0 < R.anchorRadius := by rw [hon.anchorRadius_eq]; exact hT.chain.2.2.2.1
  have hρ1 : R.anchorRadius ≤ 1 := by rw [hon.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
  have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
    have h1 : R.ballRadius = R.params.threshold / 64 := rfl
    have h2 : R.params.threshold ≤ 1 := by rw [hσ]; exact hT.σ_one
    have h3 := Real.pi_gt_three
    have h4 : 0 < R.params.threshold := by rw [hσ]; exact hT.σ_pos
    linarith
  have hblock : TorusLumps.IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hlive : ∀ η, s.InBalls η →
      WeightedResponses.IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling ∧
      s.bases ∈ TorusLumps.baseChoices R.params
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 (s.field η)) := by
    intro η hη
    refine ⟨⟨hs.isHull η hη, ?_⟩, ?_⟩
    · obtain ⟨hD, hk, hj, heq, -⟩ := hPot R hadm hrow hρA hρπ n hn s hs η hη
      have hΦ : 0 < ∏ X ∈ TorusLumps.chainComponents R.range s.support,
          R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X :=
        Finset.prod_pos fun X hX =>
          lt_of_le_of_ne (hrow.2.factor_nonneg _ hblock _ _ _ X) (hs.factor_ne_zero η hη X hX).symm
      have hpos := mul_pos (mul_pos hD hΦ) (Real.exp_pos (-s.potential η))
      rw [← heq] at hpos
      exact (mul_pos_iff_of_pos_right hk).mp ((mul_pos_iff_of_pos_right hj).mp hpos)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := hs.isBaseChoice
      rw [← stepHotLumps_eq_of_torusHotLumps_eq (hs.hotLumps_eq η hη)] at this
      exact this
  refine ⟨hlive, ?_⟩
  intro f k bad hsz hrk hk4 hside η η' hη hη' hagree
  have hodd : Odd R.params.side := by rw [hon.params_eq]; exact hT.L_odd
  have hLge : 2 ^ 40 ≤ R.params.side := by rw [hon.params_eq]; exact hT.L_ge
  have hrtpos : 0 < R.params.rt := by rw [hon.params_eq]; exact hT.rt_pos
  have ha : 1 ≤ R.params.coupling := by rw [hon.params_eq]; exact hT.a_ge
  have hC₁ : 1 ≤ A.responseParams.C₀ := by
    have h := htab.admissible.params_admissible
    have h2 := h.N₀_nonneg
    have h3 := h.Kc_ge
    rw [h.C₀_eq]
    linarith
  have hn16 : 16 ≤ n := by
    have h₁ : 4096 ≤ R.params.n₀ := by rw [hon.params_eq]; exact hT.n₀_ge
    omega
  have hgrid : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side := by rw [hon.params_eq]; exact hT.L_gt
  have hnear : ∀ Y ∈ upperSites f, BlockOffsets.CoordsAgreeNear s s Y Y k η η' := by
    intro Y hY q hq
    unfold StepSettings.ChartSetting.coordsByIndex
    by_cases h : StepSettings.nearBond R.params.side Y q ∈ s.free
    · rw [dif_pos h, dif_pos h]
      refine hagree ⟨_, h⟩ ⟨Y, hY, ?_⟩
      show TorusFields.supDist (TorusLumps.parentBlock R.params.side
        (StepSettings.fineSite R.params.side Y q.1 q.2.1)) Y ≤ k
      rw [BlockOffsets.parentBlock_fineSite hodd Y q.1 q.2.1 hq.2, TorusFields.supDist_comm]
      exact TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => by
        have := hq.1 i
        rw [Int.abs_eq_natAbs] at this
        omega
    · rw [dif_neg h, dif_neg h]
  have hscore : ∀ Y ∈ upperSites f, WeightedResponses.blockBondScores (s.field η) s.coarse s.bases Y =
      WeightedResponses.blockBondScores (s.field η') s.coarse s.bases Y := by
    intro Y hY
    have hSA := SettingShifts.settingsAgreeNear_refl s hs Y k hside
    unfold WeightedResponses.blockBondScores
    refine Finset.sum_congr rfl fun i _ => ?_
    have h₁ := hSc R n n s s Y Y k k η η' 0 i hadm hgrid hn16 hn16 hs.subset_chart hSA hk4 le_rfl (hnear Y hY)
      (fun l => by simp) (fun l => by
        simp only [zero_add]
        by_cases hl : l = i
        · subst hl
          simp
        · simp [Pi.single_eq_of_ne hl])
    have h₂ := hSc R n n s s Y Y k k η η' (-Pi.single i 1) i hadm hgrid hn16 hn16 hs.subset_chart hSA hk4 le_rfl
      (hnear Y hY)
      (fun l => by
        by_cases hl : l = i
        · subst hl
          simp
        · simp [Pi.single_eq_of_ne hl]) (fun l => by simp)
    have e₀ : Y + TorusFields.siteOfInt (0 : Fin 4 → ℤ) = Y := by
      rw [TorusLumps.siteOfInt_zero_offset, add_zero]
    have e₁ : Y + TorusFields.siteOfInt (-Pi.single i 1 : Fin 4 → ℤ) = Y - TorusFields.unitStep n i := by
      funext l
      simp only [Pi.add_apply, Pi.sub_apply, TorusFields.siteOfInt, TorusFields.unitStep]
      by_cases hl : l = i
      · subst hl
        simp [sub_eq_add_neg]
      · simp [Pi.single_eq_of_ne hl]
    rw [e₀] at h₁
    rw [e₁] at h₂
    rw [h₁, h₂]
  have hlocal : ∀ y ∈ lowerSites f,
      |WeightedResponses.centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f -
        WeightedResponses.centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η') s.support s.labelling f| ≤
      (1 + WeightedResponses.siteScore A.score s.support s.labelling y) *
        Real.exp (-(8 * R.params.rt * k)) := by
    intro y hy
    have hY : TorusLumps.parentBlock R.params.side y ∈ upperSites f := by
      rw [← parentBlocks_lowerSites]
      exact Finset.mem_image_of_mem _ hy
    obtain ⟨o, ho, hyo⟩ :=
      BlockOffsets.exists_fineSite_of_parentBlock hodd (TorusLumps.parentBlock R.params.side y) y rfl
    have hSA := SettingShifts.settingsAgreeNear_refl s hs (TorusLumps.parentBlock R.params.side y) k hside
    have hFA := hF R n n s s _ _ k k η η' o hadm (by omega) (by omega) hs.subset_chart hs.subset_chart hSA
      (by omega) le_rfl (hnear _ hY) ho
    rw [← hyo] at hFA
    obtain ⟨m, hm⟩ : ∃ m, m = R.params.side * k - R.params.side := ⟨_, rfl⟩
    rw [← hm] at hFA
    have hLk : R.params.side ≤ R.params.side * k := Nat.le_mul_of_pos_right _ (by omega)
    have hm2 : 2 * m + 2 < n * R.params.side := by
      have h₁ : R.params.side * (2 * k + 2) < R.params.side * n := Nat.mul_lt_mul_of_pos_left hside (by omega)
      have h₂ : R.params.side * (2 * k + 2) = 2 * (R.params.side * k) + 2 * R.params.side := by ring
      have h₃ : R.params.side * n = n * R.params.side := mul_comm _ _
      omega
    have hagree' : TorusLumps.StatesAgreeNear R.params (s.field η) (s.field η') s.support s.support
        s.labelling s.labelling y y m :=
      ⟨hm2, hm2, hFA, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
    have hkm : k ≤ m := by
      have h₁ : 2 * k ≤ R.params.side * k := Nat.mul_le_mul_right _ (by omega)
      have h₂ : 4 * R.params.side ≤ R.params.side * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk4
      omega
    have hr : (TorusLumps.clusterRange R.coupling : ℝ) / 64 ≤ m := by
      have h₁ : (TorusLumps.clusterRange R.coupling : ℝ) ≤ m := by exact_mod_cast hrk.trans hkm
      have h₂ : (0 : ℝ) ≤ TorusLumps.clusterRange R.coupling := Nat.cast_nonneg _
      linarith
    have hfg := htab.admissible.bounds.forget (n * R.params.side) (n * R.params.side) hblock hblock (s.field η)
      (s.field η') s.support s.support s.labelling s.labelling y y m f f (hlive η hη).1 (hlive η' hη').1 hr
      hagree' (fun _ _ _ _ _ => rfl)
    refine hfg.trans ?_
    have hs₀ : 0 ≤ WeightedResponses.siteScore A.score s.support s.labelling y := by
      unfold WeightedResponses.siteScore
      split_ifs
      · exact htab.admissible.price.nonneg _
      · exact le_rfl
    have hexp : -R.params.decayRate * m ≤ -(8 * R.params.rt * k) := by
      have hmr : (m : ℝ) = R.params.side * k - R.params.side := by
        rw [hm, Nat.cast_sub hLk]
        push_cast
        ring
      have hLr : (2 : ℝ) ^ 40 ≤ R.params.side := by exact_mod_cast hLge
      have hkr : (4 : ℝ) ≤ k := by exact_mod_cast hk4
      have h₁ : (2 : ℝ) ^ 40 * (k - 1) ≤ R.params.side * (k - 1) := mul_le_mul_of_nonneg_right hLr (by linarith)
      have h₂ : 8 * (k : ℝ) * 2 ^ 12 ≤ R.params.side * k - R.params.side := by nlinarith
      rw [hmr]
      unfold TorusLumps.StepParameters.decayRate
      have h₃ : 8 * R.params.rt * k ≤ R.params.rt / 2 ^ 12 * (R.params.side * k - R.params.side) := by
        have := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ R.params.rt / 2 ^ 12)
        calc 8 * R.params.rt * k = R.params.rt / 2 ^ 12 * (8 * (k : ℝ) * 2 ^ 12) := by ring
          _ ≤ _ := this
      linarith
    calc (1 + WeightedResponses.siteScore A.score s.support s.labelling y) *
          Real.exp (-R.params.decayRate * m) * WeightedResponses.weightNorm R.params.side R.depth f
        ≤ (1 + WeightedResponses.siteScore A.score s.support s.labelling y) *
          Real.exp (-R.params.decayRate * m) * 1 :=
          mul_le_mul_of_nonneg_left hsz (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by linarith)
  have hsum : ResponseInTheExpansion.centeredSupportResponse A s.coarse f (s.field η) s.support s.labelling bad s.bases -
      ResponseInTheExpansion.centeredSupportResponse A s.coarse f (s.field η') s.support s.labelling bad s.bases =
      ∑ y ∈ lowerSites f,
        (WeightedResponses.centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f -
          WeightedResponses.centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η') s.support
            s.labelling f) := by
    unfold ResponseInTheExpansion.centeredSupportResponse ResponseInTheExpansion.supportResponseSum
    have hS : ∑ Y ∈ ResponseInTheExpansion.weightSupportSites R.params.side (R.depth + 1) n f,
          WeightedResponses.blockMean R.params.side (R.depth + 1) n Y f *
            WeightedResponses.blockBondScores (s.field η) s.coarse s.bases Y =
        ∑ Y ∈ ResponseInTheExpansion.weightSupportSites R.params.side (R.depth + 1) n f,
          WeightedResponses.blockMean R.params.side (R.depth + 1) n Y f *
            WeightedResponses.blockBondScores (s.field η') s.coarse s.bases Y :=
      Finset.sum_congr rfl fun Y hY => by rw [hscore Y hY]
    rw [hS, Finset.sum_sub_distrib]
    unfold lowerSites
    ring
  rw [hsum]
  have hE : 0 ≤ Real.exp (-(8 * R.params.rt * k)) := (Real.exp_pos _).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hlocal).trans ?_)
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hE
  have hSn : 0 ≤ ∑ y ∈ lowerSites f, WeightedResponses.siteScore A.score s.support s.labelling y :=
    Finset.sum_nonneg fun y _ => by
      unfold WeightedResponses.siteScore
      split_ifs
      · exact htab.admissible.price.nonneg _
      · exact le_rfl
  unfold lowerSizeConst ResponseInTheExpansion.meanSiteScore
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hc : lowerSites f = ∅
  · simp [hc]
  · have hcard : ((lowerSites f).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hc)
    have e : A.responseParams.C₀ * ((lowerSites f).card : ℝ) *
          (1 + ((lowerSites f).card : ℝ)⁻¹ *
            ∑ y ∈ lowerSites f, WeightedResponses.siteScore A.score s.support s.labelling y) =
        A.responseParams.C₀ * ((lowerSites f).card +
          ∑ y ∈ lowerSites f, WeightedResponses.siteScore A.score s.support s.labelling y) := by
      field_simp
    rw [e]
    nlinarith
end YangMills.Construction.FreeEnergies
end
