import YangMills.Construction.FourPointCondition.FourPointConditionForAnyChoice
import YangMills.Construction.InfiniteLattice.ConnectedFourPointOfAStateMomentsExtensionsAndLimitPoints
import YangMills.Construction.Torus.OneBallLiftAndTransportOfQuadruples
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawInTheLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set YangMills.Construction.TestFunctions YangMills.Construction.PeriodicLattice YangMills.Construction.ResponseInTheExpansion YangMills.Construction.RenormalizationStepParameters YangMills.Construction.QuadrupleClasses
namespace YangMills.Construction.FourPointCondition
private theorem holdsOnParameters_and {P Q W : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q)
    (h : ∀ T y, Conventions.IsAdmissibleBlockingFactor T.side → P T y → Q T y → W T y) : HoldsOnParameterFamilies W := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max (max L₁ L₂) 13, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hL₀ T hTa hTL hD hC hO hrt hCd
  have hL₁ : max L₁ L₂ ≤ L := le_trans (le_max_left _ _) hL₀
  have hS : Conventions.IsAdmissibleBlockingFactor T.side := hTL ▸ ⟨hL, le_trans (le_max_right _ _) hL₀⟩
  obtain ⟨y₁, Y₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hL₁) T hTa hTL hD hC hO
    (le_trans hrt (min_le_left _ _)) (le_trans (le_max_left _ _) hCd)
  obtain ⟨y₂, Y₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hL₁) T hTa hTL hD hC hO
    (le_trans hrt (min_le_right _ _)) (le_trans (le_max_right _ _) hCd)
  exact ⟨max y₁ y₂, fun y hy hW hH => h T y hS (Y₁ y (le_trans (le_max_left _ _) hy) hW hH)
    (Y₂ y (le_trans (le_max_right _ _) hy) hW hH)⟩
private theorem gaugeGroupDim_nonneg : 0 ≤ gaugeGroupDim := by
  unfold gaugeGroupDim
  norm_num [ParameterChoice.colorNumber]
private theorem oneLoopCoeff_pos : 0 < oneLoopCoeff := by apply _root_.YangMills.SharedProofs.p28620 <;> assumption
private theorem fourPointLowerConst_nonneg (ϑ : ℝ) : 0 ≤ fourPointLowerConst ϑ := by apply _root_.YangMills.SharedProofs.p79149 <;> assumption
private theorem fourPointUpperConst_nonneg : 0 ≤ fourPointUpperConst := by
  unfold fourPointUpperConst
  positivity
private theorem prod_uniformNorm_nonneg {Y : Type*} (f : Fin 4 → Y → ℝ) : 0 ≤ ∏ i, uniformNorm (f i) :=
  Finset.prod_nonneg fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _
private theorem isInLimitInterval_of_bounds {Y : Type*} {vt d g r : ℝ} (f : Fin 4 → Y → ℝ)
    (hlog : 0 < Real.log (1 / d))
    (hg : g ^ 2 * Real.log (1 / d) ∈ Icc (2 / 3 * oneLoopCoeff) (4 / 3 * oneLoopCoeff))
    (h : FourPointBounds (fourPointLowerConst vt) fourPointUpperConst g f r) :
    IsInLimitInterval vt d f r := by
  set l := Real.log (1 / d) with hl
  set a := oneLoopCoeff with ha
  have ha0 : 0 < a := oneLoopCoeff_pos
  have hP := prod_uniformNorm_nonneg f
  have hD := gaugeGroupDim_nonneg
  have hF := fourPointLowerConst_nonneg vt
  have hC := fourPointUpperConst_nonneg
  have hl4 : 0 < l ^ 4 := by positivity
  have hinv : l ^ (-4 : ℤ) = (l ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have h₁ : (2 / 3 * a) ^ 4 ≤ g ^ 8 * l ^ 4 := by
    calc (2 / 3 * a) ^ 4 ≤ (g ^ 2 * l) ^ 4 := pow_le_pow_left₀ (by positivity) hg.1 4
      _ = g ^ 8 * l ^ 4 := by ring
  have h₂ : g ^ 8 * l ^ 4 ≤ (4 / 3 * a) ^ 4 := by
    calc g ^ 8 * l ^ 4 = (g ^ 2 * l) ^ 4 := by ring
      _ ≤ (4 / 3 * a) ^ 4 := pow_le_pow_left₀ (by positivity) hg.2 4
  have h₃ : (2 / 3 * a) ^ 4 * l ^ (-4 : ℤ) ≤ g ^ 8 := by
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hl4]
    exact h₁
  have h₄ : g ^ 8 ≤ (4 / 3 * a) ^ 4 * l ^ (-4 : ℤ) := by
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hl4]
    exact h₂
  obtain ⟨hlo, hhi⟩ := h
  constructor
  · calc fourPointLowerConst vt * gaugeGroupDim * (2 / 3 * a) ^ 4 * l ^ (-4 : ℤ) * ∏ i, uniformNorm (f i)
        = fourPointLowerConst vt * gaugeGroupDim * ((2 / 3 * a) ^ 4 * l ^ (-4 : ℤ)) * ∏ i, uniformNorm (f i) := by
          ring
      _ ≤ fourPointLowerConst vt * gaugeGroupDim * g ^ 8 * ∏ i, uniformNorm (f i) := by gcongr
      _ ≤ r := hlo
  · calc r ≤ fourPointUpperConst * gaugeGroupDim * g ^ 8 * ∏ i, uniformNorm (f i) := hhi
      _ ≤ fourPointUpperConst * gaugeGroupDim * ((4 / 3 * a) ^ 4 * l ^ (-4 : ℤ)) * ∏ i, uniformNorm (f i) := by
          gcongr
      _ = fourPointUpperConst * gaugeGroupDim * (4 / 3 * a) ^ 4 * l ^ (-4 : ℤ) * ∏ i, uniformNorm (f i) := by ring
private theorem isInLimitInterval_of_tendsto {Y ι : Type*} {l : Filter ι} [NeBot l] {vt d : ℝ}
    {f : Fin 4 → Y → ℝ} {u : ι → ℂ} {S : ℂ}
    (hu : Tendsto u l (nhds S)) (hev : ∀ᶠ j in l, ∃ r : ℝ, u j = r ∧ IsInLimitInterval vt d f r) :
    ∃ r : ℝ, S = r ∧ IsInLimitInterval vt d f r := by
  have hc : IsClosed ((fun r : ℝ => (r : ℂ)) '' {r | IsInLimitInterval vt d f r}) := by
    have : {r | IsInLimitInterval vt d f r} =
        Icc (fourPointLowerConst vt * gaugeGroupDim * (2 / 3 * oneLoopCoeff) ^ 4 * Real.log (1 / d) ^ (-4 : ℤ) *
          ∏ i, uniformNorm (f i)) (fourPointUpperConst * gaugeGroupDim * (4 / 3 * oneLoopCoeff) ^ 4 *
            Real.log (1 / d) ^ (-4 : ℤ) * ∏ i, uniformNorm (f i)) := rfl
    rw [this]
    exact (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  obtain ⟨r, hr, hS⟩ := hc.mem_of_tendsto hu (hev.mono fun j ⟨r, hj, hI⟩ => ⟨r, hI, hj.symm⟩)
  exact ⟨r, hS.symm, hr⟩
private theorem isDeepEnough_of_le (R : CouplingEvaluation) (L : ℕ) {K : ℕ+} {n : ℕ} {d : ℝ}
    (h : n + R.depthAt L d ≤ (K : ℕ)) : R.IsDeepEnough L K n d := by
  unfold CouplingEvaluation.IsDeepEnough
  omega
private theorem le_torusSide {L m : ℕ} {d : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hd : d < 1)
    (hm : 2 ≤ m) : 40 * d ≤ torusSide L m := by
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hp : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m := pow_le_pow_right₀ (by linarith) hm
  have : torusSide L m = 2 * (L : ℝ) ^ m := by simp [torusSide]
  rw [this]
  nlinarith
private theorem pos_of_cutoff_le {lam Ca β : ℝ} {K : ℕ} (hlam : 0 < lam) (h : (K : ℝ) ≤ (β + Ca) / lam)
    (hK : ⌈Ca / lam⌉₊ + 1 ≤ K) : 0 < β := by apply _root_.YangMills.SharedProofs.p71275 <;> assumption
private theorem limitBounds_at_coupling {L : ℕ} {vt lam Ca d₀ d₁ d₂ : ℝ} {n₀ : ℕ} {R : CouplingEvaluation}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hvt : 0 < vt) (hvt1 : vt ≤ 1)
    (hB : QuadrupleBalls.BallLiftPeriodizationStatement)
    (hR : EvaluationLaws R L vt lam Ca d₀ n₀) (hd₁ : d₁ ∈ Ioc (0 : ℝ) d₀) (hd₂ : d₂ ∈ Ioc (0 : ℝ) d₀)
    (hT : FourPointConditionHolds R L vt d₁ n₀)
    (hN : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → 0 < β → ∀ ν, InfiniteLattice.IsInfiniteVolumeLimit L K β ν →
      ∀ d ∈ Ioc (0 : ℝ) d₂, R.IsDeepEnough L K n₀ d → ∀ f ∈ collinearQuadsR4 d vt, ∃ r : ℝ,
        InfiniteLattice.smearedEnergyCumulant ν f = r ∧
        FourPointBounds (fourPointLowerConst vt) fourPointUpperConst (R.coupling K β d) f r) :
    ∃ d₄ ∈ Ioc (0 : ℝ) d₀, ∀ d ∈ Ioc (0 : ℝ) d₄,
        (∀ (Ks : ℕ → ℕ+) (βs : ℕ → ℝ), (∀ j, R.IsFirstPassage (Ks j) (βs j)) →
          Tendsto (fun j => (Ks j : ℕ)) atTop atTop →
          ∀ s : Conventions.StandingParameters, s.L = L → torusSide s.L s.m ∈ R.sides →
            ∀ f ∈ collinearQuadsTorus s d vt, ∀ S : ℂ,
              Tendsto (fun j => torusUrsellFunction s.L s.m (Ks j) (βs j) f) atTop (nhds S) →
              ∃ r : ℝ, S = r ∧ IsInLimitInterval vt d f r) ∧
        (∀ (Ks : ℕ → ℕ+) (βs : ℕ → ℝ) (ms : ℕ → ℕ+), (∀ j, R.IsFirstPassage (Ks j) (βs j)) →
          (∀ j, torusSide L (ms j) ∈ R.sides) →
          Tendsto (fun j => (Ks j : ℕ)) atTop atTop → Tendsto (fun j => (ms j : ℕ)) atTop atTop →
          ∀ f ∈ collinearQuadsR4 d vt, InfiniteLattice.IsSeparatedC1cTuple f → ∀ S : ℂ,
            Tendsto (fun j => torusUrsellFunction L (ms j) (Ks j) (βs j)
              fun i => periodize (torusSide L (ms j)) (f i)) atTop (nhds S) →
            ∃ r : ℝ, S = r ∧ IsInLimitInterval vt d f r) ∧
        ∀ S : (n : ℕ) → (Fin n → InfiniteLattice.AmbientSpace → ℝ) → ℂ,
          InfiniteLattice.IsWindowedVolumeLimit L (fun K => {β | R.IsFirstPassage K β}) S →
          ∀ f ∈ collinearQuadsR4 d vt, InfiniteLattice.IsSeparatedC1cTuple f →
            ∃ r : ℝ, S 4 f = r ∧ IsInLimitInterval vt d f r := by
  refine ⟨min d₁ d₂, ⟨lt_min hd₁.1 hd₂.1, (min_le_left _ _).trans hd₁.2⟩, fun d hd => ?_⟩
  have hd₀ : d ∈ Ioc (0 : ℝ) d₀ := ⟨hd.1, hd.2.trans ((min_le_left _ _).trans hd₁.2)⟩
  have hdT : d ∈ Ioc (0 : ℝ) d₁ := ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  have hdN : d ∈ Ioc (0 : ℝ) d₂ := ⟨hd.1, hd.2.trans (min_le_right _ _)⟩
  have hlog : 0 < Real.log (1 / d) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hd.1, one_mul]
    exact lt_of_le_of_lt hd₀.2 hR.d₀_mem.2
  refine ⟨?_, ?_, ?_⟩
  · intro Ks βs hdat hK s hsL hside f hf S hS
    refine isInLimitInterval_of_tendsto hS ?_
    filter_upwards [hK.eventually_ge_atTop (n₀ + R.depthAt L d)] with j hj
    have hdeep := isDeepEnough_of_le R L hj
    obtain ⟨r, hr, -, hdisp⟩ := hT { s with K := Ks j } (βs j) hsL (hdat j) d hdT hdeep f hf
    exact ⟨r, hr, isInLimitInterval_of_bounds f hlog (hR.log_mem (Ks j) (βs j) (hdat j) d hd₀ hdeep) hdisp⟩
  · intro Ks βs ms hdat _ hK hm f hf _ S hS
    refine isInLimitInterval_of_tendsto hS ?_
    filter_upwards [hK.eventually_ge_atTop (n₀ + R.depthAt L d), hm.eventually_ge_atTop 2] with j hj hj₂
    have hdeep := isDeepEnough_of_le R L hj
    have h40 : 40 * d ≤ torusSide L (ms j) := le_torusSide hL (hd₀.2.trans_lt hR.d₀_mem.2) hj₂
    obtain ⟨-, hmem, hsup⟩ := ((hB d vt hd.1 ⟨hvt, hvt1⟩).2 ⟨L, hL, Ks j, ms j⟩ h40).2.1 f hf
    obtain ⟨r, hr, -, hdisp⟩ := hT ⟨L, hL, Ks j, ms j⟩ (βs j) rfl (hdat j) d hdT hdeep _ hmem
    have hI := isInLimitInterval_of_bounds _ hlog (hR.log_mem (Ks j) (βs j) (hdat j) d hd₀ hdeep) hdisp
    have hprod : ∏ i, uniformNorm (periodize (torusSide L (ms j)) (f i)) = ∏ i, uniformNorm (f i) :=
      Finset.prod_congr rfl fun i _ => hsup i
    refine ⟨r, hr, ?_⟩
    unfold IsInLimitInterval at hI ⊢
    rw [hprod] at hI
    exact hI
  · rintro S ⟨-, Q, hQ⟩ f hf hC
    have ht := hQ 4 (by norm_num) f hC
    obtain ⟨r, hSr, hI⟩ := isInLimitInterval_of_tendsto (vt := vt) (d := d) (f := f) ht (by
      filter_upwards [Q.tendsto_K.eventually_ge_atTop (n₀ + R.depthAt L d),
        Q.tendsto_K.eventually_ge_atTop (⌈Ca / lam⌉₊ + 1)] with j hj hj₁
      have hdeep := isDeepEnough_of_le R L hj
      have hβ : 0 < Q.β j := pos_of_cutoff_le hR.lam_pos (hR.cutoff_le (Q.K j) (Q.β j) (Q.β_mem_window j)) hj₁
      obtain ⟨r, hr, hdisp⟩ :=
        hN (Q.K j) (Q.β j) (Q.β_mem_window j) hβ (Q.ν j) (Q.isInfiniteVolumeLimit j) d hdN hdeep f hf
      exact ⟨r, hr, isInLimitInterval_of_bounds f hlog
        (hR.log_mem (Q.K j) (Q.β j) (Q.β_mem_window j) d hd₀ hdeep) hdisp⟩)
    exact ⟨r, hSr, hI⟩
theorem limitBoundStatement_holds (hAny : fourPointBoundAtEveryProfile)
    (hStates : fourPointBoundsInTorusLimitStates)
    (hWeak : InfiniteLattice.FourPointMoments.MomentsExtensionsAndLimits)
    (hB : QuadrupleBalls.BallLiftPeriodizationStatement) : LimitBoundStatement := by
  refine holdsOnParameters_and hAny hStates ?_
  intro Tb y hL h₁ h₂ vt hvt hvt1 R lam Ca d₀ n₀ hR
  obtain ⟨d₁, hd₁, C₁⟩ := h₁ vt hvt hvt1 R lam Ca d₀ n₀ hR
  obtain ⟨d₂, hd₂, C₂⟩ := h₂ vt hvt hvt1 R lam Ca d₀ n₀ hR
  refine limitBounds_at_coupling hL hvt hvt1 hB hR hd₁ hd₂ C₁ fun K β hK hβ ν hν d hd hdeep f hf => ?_
  have hmem := ((hWeak (Tb.stepParameters y).side K hL K.pos β hβ).2.1.2 ⟨ν, hν.1⟩).2.2 hν
  exact C₂ K β hβ hK ⟨ν, hν.1⟩ hmem d hd hdeep f hf
end YangMills.Construction.FourPointCondition
end
