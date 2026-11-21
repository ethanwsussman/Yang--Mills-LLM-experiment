import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ResponseInTheExpansion.GroundOfAMirror
import YangMills.Construction.ResponseInTheExpansion.HatsOfAgreeingGrounds
import YangMills.Construction.ResponseInTheExpansion.SizeOfAGasBlock
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.StoredScoresOfAGround
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendToATorus
import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
private theorem abs_sub_le_of_hull_bounds {L4 C₀ e a s₁ σ s' S S₁ A B : ℝ} (hL : 0 ≤ L4) (ha : 0 ≤ a)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 2)
    (hC : 0 ≤ C₀) (hs₁ : s₁ = 2 * L4 * (C₀ + 2) + 40 * a) (hS : 0 ≤ S) (hSS : S ≤ S₁) (hσ : 0 ≤ σ)
    (hs : s₁ + σ ≤ s') (hA : |A| ≤ (L4 * (C₀ + e) + σ + 8 * a * (2 + e)) * S)
    (hB : |B| ≤ (L4 * (C₀ + e) + 0 + 8 * a * (2 + e)) * S) : |A - B| ≤ (C₀ + s') * S₁ := by
  have h1 := abs_sub A B
  have h2 : 2 * (L4 * (C₀ + e)) + 16 * a * (2 + e) + σ ≤ s' := by
    have e1 : L4 * e ≤ L4 * 2 := mul_le_mul_of_nonneg_left (by linarith) hL
    have e2 : a * e ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left he ha
    rw [hs₁] at hs
    nlinarith
  have h3 : (L4 * (C₀ + e) + σ + 8 * a * (2 + e)) * S + (L4 * (C₀ + e) + 0 + 8 * a * (2 + e)) * S ≤ s' * S := by
    have := mul_le_mul_of_nonneg_right h2 hS
    nlinarith
  have hs0 : 0 ≤ s' := by
    have : 0 ≤ s₁ := by
      rw [hs₁]
      positivity
    linarith
  have h4 : s' * S ≤ (C₀ + s') * S₁ :=
    mul_le_mul (by linarith) hSS hS (by linarith)
  linarith
theorem stepSizeBoundsOfCold_proof (hH : ResponseInTheExpansion.centredGasBlockAgreementStatement)
    (hS : ResponseInTheExpansion.gasBlockMeanBoundStatement)
    (hI : WeightedResponses.coldStepIntegralEqGasMean) (hM : ResponseInTheExpansion.MirrorGroundAgrees)
    (hE : WeightedResponses.weightExtensionStatement) (hW : WeightedResponses.WeightsCompatibleAcrossTori)
    (hHu : StepGas.HullStateIsHotCase) (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero)
    (hfl : StepFloors.EventuallyFloorConditions) : WeightedResponses.StepSizeBoundsOfCold := by
  obtain ⟨r₁, p₁, g₁⟩ := hH
  obtain ⟨r₂, p₂, g₂⟩ := hS
  obtain ⟨r₃, p₃, g₃⟩ := hI
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (r₃ c),
    fun c => lt_min (lt_min (p₁ c) (p₂ c)) (p₃ c), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, H₁⟩ := g₁ T hD (hrt.trans ((min_le_left _ _).trans (min_le_left _ _))) K
  obtain ⟨y₂, S₁⟩ := g₂ T hD (hrt.trans ((min_le_left _ _).trans (min_le_right _ _))) K
  obtain ⟨y₃, I₁⟩ := g₃ T hD (hrt.trans (min_le_right _ _)) K
  obtain ⟨y₄, U₁⟩ := hHu T hD
  obtain ⟨yF, hF⟩ := hfl T hD 1 1 one_pos one_pos
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (200 * T.B) (max yF 1)),
    fun y hy R A hK hAt hFo hL hcs => ?_⟩
  have hy0 := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy0)
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy0)
  have hy3 : y₃ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy0)
  have hy4 : y₄ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy0)
  have hy5 : 200 * T.B ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyF : yF ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hy6 : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hR := hAt.onFamily
  have hxy := hR.le_coupling
  have hfit : R.params.Admissible := hFo.admissible
  have hodd := hfit.L_odd
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have core := H₁ y hy1 R A hK hAt hFo
  have bound := S₁ y hy2 R A hK hAt
  have hIm := I₁ y hy3 R A hK hAt
  have hKf := hAt.admissible.params_admissible
  have hKf0 := hAt.admissible.params_admissible
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have e := hKf0.C₀_eq
    have h1 := hKf0.N₀_nonneg
    have h2 := hKf0.Kc_ge
    have h3 := hfit.a_ge
    have h4 : 0 ≤ A.responseParams.C₀ + 2 := by
      rw [e]
      linarith only [h1, h2, h3]
    rw [hKf0.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) h4) (by linarith only [h3])
  have hsnn := hAt.admissible.price.nonneg
  have ha1 := hfit.a_ge
  have hC1 : 1 ≤ A.responseParams.C₀ := by
    have e := hKf.C₀_eq
    have h1 := hKf.N₀_nonneg
    have h2 := hKf.Kc_ge
    rw [e]
    linarith
  set e := Real.exp (-(6 * T.gasRate * R.coupling)) with he
  have he0 : 0 < e := Real.exp_pos _
  have he2 : e ≤ 1 / 2 := by
    have h1 : 1 ≤ 6 * T.gasRate * R.coupling := by
      have h2 : (1 : ℝ) ≤ R.coupling := hy6.trans hxy
      have h3 := (hF R.coupling (hyF.trans hxy)).gas_powers.2.1
      have h4 : (1 : ℝ) ≤ R.coupling ^ (1 / 90 : ℝ) := Real.one_le_rpow h2 (by norm_num)
      linarith
    have h3 : Real.exp 1 ≤ Real.exp (6 * T.gasRate * R.coupling) := Real.exp_le_exp.mpr h1
    have h4 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h5 : e * Real.exp (6 * T.gasRate * R.coupling) = 1 := by
      rw [he, ← Real.exp_add]
      simp
    nlinarith
  have hot : ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
      ∀ (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
      (ω : Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side),
      WeightedResponses.IsLiveState R.params R.nextCoupling (StepSettings.coarseWeightExpansion R) W Y ω →
      (StepGas.hotCaseGround R W ⟨Y, ω⟩).IsHotCase := by
    intro n _ bs W Y ω hl
    have hpos : 0 < StepSettings.coarseStateWeight R (StepSettings.hotCoreSites R W) W ⟨Y, ω⟩ := by
      have := hl.2
      unfold StepSettings.coarseWeightExpansion at this
      rwa [dif_neg (NeZero.ne n)] at this
    have hΦ : ∀ X ∈ TorusLumps.chainComponents R.nextRange Y,
        StepSettings.coarseFactor W (⟨Y, ω⟩ : StepSettings.CoarseState R n) X ≠ 0 := by
      intro X hX h0
      have := hZ R hFo n bs W ⟨Y, ω⟩ hl.1 ⟨X, hX, h0⟩
      linarith
    exact U₁ y hy4 R hR hFo n bs W ⟨Y, ω⟩ hl.1 hΦ
  have hatHot : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (W : TorusFields.TorusField n)
      (Y : Finset (TorusFields.TorusSite n))
      (ω : Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) (y' : TorusFields.TorusSite n)
      (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n)),
      (StepGas.hotCaseGround R W ⟨Y, ω⟩).IsAdmissibleGround →
      WeightedResponses.centeredHullResponse A.coldStep A.hullStep n y' W Y ω h =
        WeightedResponses.gasBlockMean A (StepGas.hotCaseGround R W ⟨Y, ω⟩) y' h -
          WeightedResponses.gasBlockMean A (StepGas.coldCaseGround R (TorusFields.trivialField n)) y' h := by
    intro n _ hn W Y ω y' h hG
    have e1 : WeightedResponses.caseMean R (StepSettings.hotCoreSites R W) W ⟨Y, ω⟩
        (WeightedResponses.caseResponse A W y' h) = _ := (hIm n _ hG y' h).2
    have e2 : WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A (TorusFields.trivialField n) y' h) = _ :=
      (hIm n _ (ResponseInTheExpansion.coldCaseGround_trivialField_isAdmissible R n hn hfit) y' h).2
    show WeightedResponses.caseMean R (StepSettings.hotCoreSites R W) W ⟨Y, ω⟩
        (WeightedResponses.caseResponse A W y' h) -
      WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A (TorusFields.trivialField n) y' h) = _
    rw [e1, e2]
    ring
  have hatCold : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (W : TorusFields.TorusField n)
      (y' : TorusFields.TorusSite n)
      (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n)),
      (StepGas.coldCaseGround R W).IsAdmissibleGround →
      WeightedResponses.centeredResponse A.coldStep n y' W h =
        WeightedResponses.gasBlockMean A (StepGas.coldCaseGround R W) y' h -
          WeightedResponses.gasBlockMean A (StepGas.coldCaseGround R (TorusFields.trivialField n)) y' h := by
    intro n _ hn W y' h hG
    have e1 : WeightedResponses.caseMean R ∅ W (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A W y' h) = _ := (hIm n _ hG y' h).2
    have e2 : WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A (TorusFields.trivialField n) y' h) = _ :=
      (hIm n _ (ResponseInTheExpansion.coldCaseGround_trivialField_isAdmissible R n hn hfit) y' h).2
    show WeightedResponses.caseMean R ∅ W (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A W y' h) -
      WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
        (WeightedResponses.caseResponse A (TorusFields.trivialField n) y' h) = _
    rw [e1, e2]
    ring
  have hcold : ∀ (n : ℕ) [NeZero n] (W : TorusFields.TorusField n), R.params.n₀ ≤ n →
      TorusFields.IsCold R.params.threshold W → (StepGas.coldCaseGround R W).IsAdmissibleGround := by
    intro n _ W hn hc
    refine Or.inl ⟨hn, fun x μ ν hlt => ?_, rfl, rfl, rfl⟩
    have h1 := hc x μ ν hlt
    have h2 := hfit.σ_pos
    exact show TorusFields.curvature W x μ ν < 9 / 8 * R.params.threshold from by linarith only [h1, h2]
  have hblock : ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n → R.params.n₀ ≤ n := by
    intro n _ bs
    have h1 := bs.2
    have h2 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  refine ⟨?_, ?_⟩
  · intro n _ hn y₀ W hc h
    have := hcs n hn y₀ W hc h
    have hS0 : 0 ≤ WeightedResponses.weightNorm R.params.side (R.depth + 1) h :=
      le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
    nlinarith
  · intro n _ bs y₀ W Y ω hl h
    show |WeightedResponses.centeredHullResponse (Ω := TorusLumps.CoarseLabel R.labels.Ω R.params.side)
        A.coldStep A.hullStep n y₀ W Y ω h| ≤
      (A.responseParams.C₀ + WeightedResponses.siteScore
        (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score) Y ω y₀) *
        WeightedResponses.weightNorm R.params.side (R.depth + 1) h
    have hn := hblock n bs
    have hsc0 : 0 ≤ WeightedResponses.siteScore
        (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score) Y ω y₀ := by
      classical
      unfold WeightedResponses.siteScore
      split_ifs with hy
      · have hnn : ∀ w : TorusLumps.CoarseLabel R.labels.Ω R.params.side,
            0 ≤ WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score w := by
          intro w
          cases w with
          | inl _ => exact hs₁
          | inr st' =>
            refine add_nonneg hs₁ (Finset.sum_nonneg fun o _ => ?_)
            cases st'.siteLabel o with
            | inl _ => exact le_rfl
            | inr a => exact hsnn a
        exact hnn _
      · exact le_rfl
    haveI hNL : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
    have hS2 : WeightedResponses.weightNorm R.params.side R.depth h ≤
        WeightedResponses.weightNorm R.params.side (R.depth + 1) h :=
      (hW R.params.side hodd R.depth (n * R.params.side) (n * R.params.side)).2.2 h
    have hS0 : 0 ≤ WeightedResponses.weightNorm R.params.side R.depth h :=
      le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
    have hS10 : 0 ≤ WeightedResponses.weightNorm R.params.side (R.depth + 1) h := hS0.trans hS2
    by_cases hyY : y₀ ∈ Y
    · have hG : (StepGas.hotCaseGround R W ⟨Y, ω⟩).IsAdmissibleGround := Or.inr (hot n bs W Y ω hl)
      rw [hatHot n hn W Y ω y₀ h hG]
      have hA := bound n (StepGas.hotCaseGround R W ⟨Y, ω⟩) y₀ h hG
      have hB := bound n (StepGas.coldCaseGround R (TorusFields.trivialField n)) y₀ h
        (ResponseInTheExpansion.coldCaseGround_trivialField_isAdmissible R n hn hfit)
      rw [ResponseInTheExpansion.sum_recordedSiteScore_coldCaseGround A hodd] at hB
      have hst := (ResponseInTheExpansion.sum_recordedSiteScore_le A hs₁ hsnn hodd W ⟨Y, ω⟩ y₀).2 hyY
      have hσ0 : 0 ≤ ∑ o ∈ BlockAverages.centredCube R.params.side,
          WeightedResponses.recordedSiteScore A (StepGas.hotCaseGround R W ⟨Y, ω⟩)
            (StepSettings.fineSite R.params.side y₀ 0 o) :=
        Finset.sum_nonneg fun o _ => ResponseInTheExpansion.recordedSiteScore_nonneg A hsnn _ _
      exact abs_sub_le_of_hull_bounds (by positivity) (by linarith) he0.le he2 (by linarith) hKf.s₁_eq
        hS0 hS2 hσ0 hst hA hB
    · by_cases hemp : Y = ∅
      · subst hemp
        have hWc : TorusFields.IsCold R.params.threshold W := by
          intro x μ ν hlt
          by_contra hcon
          have h1 := TorusLumps.mem_torusHotSites_of_mem_plaquetteVertices hfit bs.1 hlt (not_lt.mp hcon)
            (TorusLumps.base_mem_plaquetteVertices x μ ν)
          have h2 := hl.1.1 ((TorusFields.mem_thickening _ _ _).mpr
            ⟨x, h1, by rw [TorusFields.supDist_self]; omega⟩)
          simp at h2
        have hC : StepSettings.hotCoreSites R W = ∅ := Finset.subset_empty.mp hl.1.1
        have hq : (⟨∅, ω⟩ : StepSettings.CoarseState R n) = StepGas.emptyCoarseState R := by
          unfold StepGas.emptyCoarseState
          congr 1
          funext z
          exact absurd z.2 (Finset.notMem_empty _)
        have heq : WeightedResponses.centeredHullResponse A.coldStep A.hullStep n y₀ W ∅ ω h =
            WeightedResponses.centeredResponse A.coldStep n y₀ W h := by
          show WeightedResponses.caseMean R (StepSettings.hotCoreSites R W) W ⟨∅, ω⟩
              (WeightedResponses.caseResponse A W y₀ h) - _ =
            WeightedResponses.caseMean R ∅ W (StepGas.emptyCoarseState R)
              (WeightedResponses.caseResponse A W y₀ h) - _
          rw [hC, hq]
        rw [heq]
        have := hcs n hn y₀ W hWc h
        nlinarith
      · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hr1 := hFo.range_le
        have hr2 := hFo.nextRange_ge
        have hr3 := hFo.range_ge_base
        set m := R.nextRange / 4 - 2 with hm
        have hm3 : 2 ≤ m := by omega
        have hn₀m : R.params.n₀ ≤ 4 * m := by omega
        haveI hN4 : NeZero (4 * m) := ⟨by omega⟩
        have hIsHot := hot n bs W Y ω hl
        obtain ⟨hmc, hag⟩ := hM R n W ⟨Y, ω⟩ y₀ hFo hIsHot hyY ⟨z, hz⟩
        have hG : (StepGas.hotCaseGround R W ⟨Y, ω⟩).IsAdmissibleGround := Or.inr hIsHot
        have hG' := hcold (4 * m) (TorusMirror.mirrorField m y₀ W) hn₀m hmc
        have hn4 : 8 ≤ n := by
          have := hfit.n₀_ge
          omega
        obtain ⟨h', hw, hsz⟩ := hE R.params.side hodd (R.depth + 1) n (4 * m) hn4 (by omega) y₀ 0 h
        have hmfl : (TorusLumps.clusterRange R.nextCoupling : ℝ) / 64 ≤ m := by
          have h1 : R.nextRange ≤ 4 * m + 11 := by omega
          have h2 : (R.nextRange : ℝ) ≤ 4 * m + 11 := by exact_mod_cast h1
          have h3 : (2 : ℝ) ≤ m := by exact_mod_cast hm3
          show (R.nextRange : ℝ) / 64 ≤ m
          linarith
        have hzero : ∑ o ∈ BlockAverages.centredCube R.params.side,
            WeightedResponses.recordedSiteScore A (StepGas.hotCaseGround R W ⟨Y, ω⟩)
              (StepSettings.fineSite R.params.side y₀ 0 o) ≤ 0 := by
          have := (ResponseInTheExpansion.sum_recordedSiteScore_le A hs₁ hsnn hodd W ⟨Y, ω⟩ y₀).1
          have e0 : WeightedResponses.siteScore
              (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score) Y ω y₀ = 0 := by
            classical
            unfold WeightedResponses.siteScore
            rw [dif_neg hyY]
          rw [e0] at this
          exact this
        have hd := core n (4 * m) _ _ y₀ 0 m h h' 0 hG hG' hn hn₀m hag hmfl hw hzero
        rw [← hatCold (4 * m) hn₀m _ 0 h' hG', ← hatHot n hn W Y ω y₀ h hG] at hd
        have hcm := hcs (4 * m) hn₀m 0 (TorusMirror.mirrorField m y₀ W) hmc h'
        have hexp : Real.exp (-R.params.decayRate * m) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have h1 : 0 ≤ R.params.decayRate := by
            unfold TorusLumps.StepParameters.decayRate
            exact div_nonneg hfit.rt_pos.le (by norm_num)
          have h2 : (0 : ℝ) ≤ m := by positivity
          nlinarith
        have hCs : (A.responseParams.C₀ - 1) * WeightedResponses.weightNorm R.params.side (R.depth + 1) h' ≤
            (A.responseParams.C₀ - 1) * WeightedResponses.weightNorm R.params.side (R.depth + 1) h :=
          mul_le_mul_of_nonneg_left hsz (by linarith)
        have t := abs_sub_abs_le_abs_sub
          (WeightedResponses.centeredHullResponse A.coldStep A.hullStep n y₀ W Y ω h)
          (WeightedResponses.centeredResponse A.coldStep (4 * m) 0 (TorusMirror.mirrorField m y₀ W) h')
        have hdd : (1 + 0) * Real.exp (-R.params.decayRate * m) *
            WeightedResponses.weightNorm R.params.side (R.depth + 1) h ≤
            WeightedResponses.weightNorm R.params.side (R.depth + 1) h := by
          have := mul_le_mul_of_nonneg_right hexp hS10
          linarith
        have hlast : A.responseParams.C₀ * WeightedResponses.weightNorm R.params.side (R.depth + 1) h ≤
            (A.responseParams.C₀ + WeightedResponses.siteScore
              (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score) Y ω y₀) *
              WeightedResponses.weightNorm R.params.side (R.depth + 1) h :=
          mul_le_mul_of_nonneg_right (by linarith) hS10
        nlinarith
end YangMills.Construction.ResponseInTheExpansion
end
