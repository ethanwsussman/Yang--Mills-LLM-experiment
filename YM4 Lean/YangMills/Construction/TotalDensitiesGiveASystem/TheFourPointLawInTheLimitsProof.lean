import YangMills.Construction.FourPointCondition.ConditionOnTheStates
import YangMills.Construction.FourPointCondition.ConditionsOfTheRatioAtAnObservableProof
import YangMills.Construction.FourPointCondition.LawsAtTheDataOfTheFlow
import YangMills.Construction.InfiniteLattice.WeakConvergenceAndTheKernelsAndDensitiesOfAWindow
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawInTheLimits
import YangMills.Construction.TotalDensitiesGiveASystem.TheParametersAreDrawnParameters
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TrajectoryData YangMills.Construction.FourPointCondition
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.SystemsWithFiveBounds YangMills.Construction.TestFunctions
private theorem holdsOnParameters_both {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) :
    HoldsOnParameterFamilies fun T y => YangMills.Construction.Conventions.IsAdmissibleBlockingFactor T.side ∧ P T y ∧ Q T y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max (max L₁ L₂) 13, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hL₀ T hTa hTL hD hC hO hrt hCd
  have hL₁ : max L₁ L₂ ≤ L := le_trans (le_max_left _ _) hL₀
  have hS : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor T.side :=
    hTL ▸ ⟨hL, le_trans (le_max_right _ _) hL₀⟩
  obtain ⟨y₁, Y₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hL₁) T hTa hTL hD hC hO
    (le_trans hrt (min_le_left _ _)) (le_trans (le_max_left _ _) hCd)
  obtain ⟨y₂, Y₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hL₁) T hTa hTL hD hC hO
    (le_trans hrt (min_le_right _ _)) (le_trans (le_max_right _ _) hCd)
  exact ⟨max y₁ y₂, fun y hy hW hH => ⟨hS, Y₁ y (le_trans (le_max_left _ _) hy) hW hH,
    Y₂ y (le_trans (le_max_right _ _) hy) hW hH⟩⟩
private theorem exists_subexpGrowth : ∃ room : ℕ → ℝ, YangMills.Construction.RoomFunctions.IsSubexpGrowth room := by
  refine ⟨fun s => (s : ℝ) + 1, ⟨fun a b h => ?_, fun s => ?_, ?_, ?_⟩⟩
  · have : (a : ℝ) ≤ b := by exact_mod_cast h
    simpa using this
  · have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · have h₁ : Tendsto (fun s : ℕ => (s : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h₂ : Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp h₁
    have h₃ : Tendsto (fun s : ℕ => 1 + 1 / (s : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have h₄ := h₂.mul h₃
    rw [zero_mul] at h₄
    refine h₄.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have hs₁ : (s : ℝ) + 1 ≠ 0 := by positivity
    field_simp
private theorem oneLoopCoeff_pos : 0 < oneLoopCoeff := by apply _root_.YangMills.SharedProofs.p28620 <;> assumption
private theorem gaugeGroupDim_nonneg : 0 ≤ gaugeGroupDim := by
  unfold gaugeGroupDim
  norm_num [YangMills.Construction.ParameterChoice.colorNumber]
private theorem fourPointLowerConst_nonneg (ϑ : ℝ) : 0 ≤ fourPointLowerConst ϑ := by
  unfold fourPointLowerConst
  have := Real.pi_pos
  positivity
abbrev _root_.YangMills.SharedProofs.p79149 := @fourPointLowerConst_nonneg
private theorem fourPointUpperConst_nonneg : 0 ≤ fourPointUpperConst := by
  unfold fourPointUpperConst
  positivity
private theorem isInLimitInterval_of_bounds {vt d g r : ℝ}
    (f : Fin 4 → YangMills.Construction.InfiniteLattice.AmbientSpace → ℝ) (hlog : 0 < Real.log (1 / d))
    (hg : g ^ 2 * Real.log (1 / d) ∈ Icc (2 / 3 * oneLoopCoeff) (4 / 3 * oneLoopCoeff))
    (h : FourPointBounds (fourPointLowerConst vt) fourPointUpperConst g f r) :
    IsInLimitInterval vt d f r := by
  set l := Real.log (1 / d) with hl
  set a := oneLoopCoeff with ha
  have ha0 : 0 < a := oneLoopCoeff_pos
  have hP : 0 ≤ ∏ i, uniformNorm (f i) := Finset.prod_nonneg fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hD := gaugeGroupDim_nonneg
  have hF := fourPointLowerConst_nonneg vt
  have hC := fourPointUpperConst_nonneg
  have hl4 : 0 < l ^ 4 := by positivity
  have hinv : l ^ (-4 : ℤ) = (l ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have e₈ : g ^ 8 * l ^ 4 = (g ^ 2 * l) ^ 4 := by ring
  have h₃ : (2 / 3 * a) ^ 4 * l ^ (-4 : ℤ) ≤ g ^ 8 := by
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hl4, e₈]
    exact pow_le_pow_left₀ (by positivity) hg.1 4
  have h₄ : g ^ 8 ≤ (4 / 3 * a) ^ 4 * l ^ (-4 : ℤ) := by
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hl4, e₈]
    exact pow_le_pow_left₀ (by nlinarith [hg.1]) hg.2 4
  obtain ⟨hlo, hhi⟩ := h
  constructor
  · calc fourPointLowerConst vt * gaugeGroupDim * (2 / 3 * a) ^ 4 * l ^ (-4 : ℤ) * ∏ i, uniformNorm (f i)
        = fourPointLowerConst vt * gaugeGroupDim * ((2 / 3 * a) ^ 4 * l ^ (-4 : ℤ)) * ∏ i, uniformNorm (f i) := by ring
      _ ≤ fourPointLowerConst vt * gaugeGroupDim * g ^ 8 * ∏ i, uniformNorm (f i) := by gcongr
      _ ≤ r := hlo
  · calc r ≤ fourPointUpperConst * gaugeGroupDim * g ^ 8 * ∏ i, uniformNorm (f i) := hhi
      _ ≤ fourPointUpperConst * gaugeGroupDim * ((4 / 3 * a) ^ 4 * l ^ (-4 : ℤ)) * ∏ i, uniformNorm (f i) := by gcongr
      _ = fourPointUpperConst * gaugeGroupDim * (4 / 3 * a) ^ 4 * l ^ (-4 : ℤ) * ∏ i, uniformNorm (f i) := by ring
private theorem isInLimitInterval_of_tendsto {vt d s : ℝ}
    {f : Fin 4 → YangMills.Construction.InfiniteLattice.AmbientSpace → ℝ} {u : ℕ+ → ℂ}
    (hu : Tendsto u atTop (𝓝 ((s : ℝ) : ℂ)))
    (hev : ∀ᶠ j in atTop, ∃ r : ℝ, u j = r ∧ IsInLimitInterval vt d f r) :
    IsInLimitInterval vt d f s := by
  have hre : Tendsto (fun j => (u j).re) atTop (𝓝 s) := by
    have h := (Complex.continuous_re.tendsto _).comp hu
    rwa [Complex.ofReal_re] at h
  constructor
  · refine ge_of_tendsto hre (hev.mono fun j ⟨r, hj, hI⟩ => ?_)
    rw [hj, Complex.ofReal_re]
    exact hI.1
  · refine le_of_tendsto hre (hev.mono fun j ⟨r, hj, hI⟩ => ?_)
    rw [hj, Complex.ofReal_re]
    exact hI.2
private theorem coupling_pos_of_cutoff_le {lam Ca β : ℝ} {K : ℕ} (hlam : 0 < lam) (h : (K : ℝ) ≤ (β + Ca) / lam)
    (hK : ⌈Ca / lam⌉₊ + 1 ≤ K) : 0 < β := by
  have h₁ : Ca / lam < K := by
    have h₂ : ((⌈Ca / lam⌉₊ + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    have h₃ := Nat.le_ceil (Ca / lam)
    push_cast at h₂
    linarith
  rw [div_lt_iff₀ hlam] at h₁
  rw [le_div_iff₀ hlam] at h
  linarith
abbrev _root_.YangMills.SharedProofs.p71275 := @coupling_pos_of_cutoff_le
private theorem trajectoryData_at_admissibleSchedules (hD : trajectoryDataStatement) :
    HoldsAtAdmissibleParameters fun T y => ∃ D : TrajectoryParameters T y, HasTrajectoryDataForAllShifts D := by
  obtain ⟨Q, hQ, floorL, ceilRt, ceilσ, floorN, floorCs, C₀, h1, h2, hT'⟩ := hD
  exact ⟨⟨Q, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs, fun _ => 0⟩, ⟨hQ, h1, h2⟩, fun T hDr hM =>
    hT' T hDr hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.derivBound_ge hM.holds⟩
abbrev _root_.YangMills.SharedProofs.p67844 := @trajectoryData_at_admissibleSchedules
theorem fourPointLawInLimits_holds
    (hT : YangMills.Construction.TotalDensitiesGiveASystem.ResponseParametersToAdmissibleParameters)
    (hD : trajectoryDataStatement)
    (hLaws : lawsAtFlowDataStatement) (hStates : fourPointBoundsInTorusLimitStates)
    (hWeak : YangMills.Construction.InfiniteLattice.WeakConvergence.WeakConvergenceWindowStatement) :
    fourPointLawInLimits := by
  refine HoldsAtAdmissibleParameters.mono
    (HoldsAtAdmissibleParameters.and (hT _ (holdsOnParameters_both hLaws hStates)) (trajectoryData_at_admissibleSchedules hD))
    fun T y hDr hA Bs hBs => ?_
  obtain ⟨⟨hL, ⟨Kr, -, hlaws⟩, hst⟩, D, hDw⟩ := hA
  obtain ⟨al, -, hlaw⟩ := hlaws D hDw
  have hlam : 0 < D.rateBound := by
    have hL₁ : (1 : ℝ) < T.side := by
      have h : 1 < T.side := lt_of_lt_of_le (by norm_num) hDr.L_ge
      exact_mod_cast h
    have hlog := Real.log_pos hL₁
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  refine ⟨D.floorStar, fun g hg hy vt hvt hvt1 => ?_⟩
  obtain ⟨room, hroom⟩ := exists_subexpGrowth
  obtain ⟨d₀, -, -, hR, -, -⟩ := hlaw Bs D.rateBound hBs hlam le_rfl vt hvt hvt1 g hg hy room hroom
  obtain ⟨d₄, hd₄, hC⟩ := hst vt hvt hvt1 _ _ _ _ _ hR
  refine ⟨d₄, hd₄.1, fun d hd Q S hQ X hX => ?_⟩
  have hd₀ : d ∈ Ioc (0 : ℝ) d₀ := ⟨hd.1, hd.2.trans hd₄.2⟩
  have hlog : 0 < Real.log (1 / d) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hd.1, one_mul]
    exact lt_of_le_of_lt hd₀.2 hR.d₀_mem.2
  refine isInLimitInterval_of_tendsto (hQ 4 (by norm_num) X) ?_
  filter_upwards [Q.tendsto_cutoff.eventually_ge_atTop
      (1 + (flowProfile (T.stepParameters y) g Bs room al).depthAt (T.stepParameters y).side d),
    Q.tendsto_cutoff.eventually_ge_atTop (⌈(D.rateBound + D.c₅) / D.rateBound⌉₊ + 1)] with j hj hj₁
  have hdatum : (flowProfile (T.stepParameters y) g Bs room al).IsFirstPassage (Q.cutoff j) (Q.coupling j) := Q.pair j
  have hdeep : (flowProfile (T.stepParameters y) g Bs room al).IsDeepEnough (T.stepParameters y).side (Q.cutoff j) 1 d := by
    unfold CouplingEvaluation.IsDeepEnough
    omega
  have hβ : 0 < Q.coupling j := coupling_pos_of_cutoff_le hlam (hR.cutoff_le (Q.cutoff j) (Q.coupling j) hdatum) hj₁
  obtain ⟨ν, hmem, hνe⟩ :=
    ((hWeak (T.stepParameters y).side (Q.cutoff j) hL (Q.cutoff j).pos (Q.coupling j) hβ).2.1.2.2 (Q.state j)).1
      (Q.isLimit j)
  obtain ⟨r, hr, hdisp⟩ := hC (Q.cutoff j) (Q.coupling j) hβ hdatum ν hmem d hd hdeep X.1 hX
  refine ⟨r, ?_, isInLimitInterval_of_bounds X.1 hlog (hR.log_mem (Q.cutoff j) (Q.coupling j) hdatum d hd₀ hdeep) hdisp⟩
  rw [← hνe]
  exact hr
end YangMills.Construction.TotalDensities
end
