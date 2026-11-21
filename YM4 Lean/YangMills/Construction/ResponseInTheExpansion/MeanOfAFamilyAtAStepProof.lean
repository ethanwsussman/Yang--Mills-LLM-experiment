import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.MeanOfAFamilyAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames FamilyNorms BlockMeans Estimates TorusLumps TorusFields RenormalizationStepParameters StepSettings
  BlockAverages WeightedResponses
namespace ResponseInTheExpansion
open TermCalculus
namespace FamilyMeanAtStep
def expTotal (f : LocalDensity) : TorusFunctional := fun n W =>
  if h : n = 0 then 1 else
    haveI : NeZero n := ⟨h⟩
    Real.exp (∑ y, centered f n y W)
variable {ℓ : TorusLumps.StepParameters} {ε η₃ b : ℝ} {h : LocalDensity}
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
theorem secondDerivLimit_scaledDensity (hF : ℓ.Admissible)
    (hsm : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
      ContDiffThreeAt (h n y) W)
    (hlim : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
        Filter.atTop (𝓝 (secondDerivLimit h c c' X X')))
    (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions) :
    secondDerivLimit (scaledDensity b h) c c' X X' = b * secondDerivLimit h c c' X X' := by
  have h1 : Filter.Tendsto (fun n : ℕ =>
      mixedDeriv (scaledDensity b h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (b * secondDerivLimit h c c' X X')) := by
    refine ((hlim c c' X X').const_mul b).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn
    have : NeZero n := ⟨by have := hF.n₀_ge; omega⟩
    exact (mixedDeriv_const_mul b (h n 0) (trivialField n) _ _ (by omega)
      (hsm n hn 0 _ (trivialField_isCold hF.σ_pos n) 2 _ _)).symm
  exact h1.limUnder_eq
theorem coldExpansion_scaledDensity (hF : ℓ.Admissible) (t : ℕ) (hb : 0 < b)
    (hh : ColdDensityBounds ℓ ε (ε / η₃) h) (hE : b * ε = ℓ.E)
    (hE₃ : b * (ε / η₃) = ℓ.E₃)
    (hlim : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
        Filter.atTop (𝓝 (secondDerivLimit h c c' X X')))
    (hsum : ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ μ ν, A μ ν = - A ν μ) →
      (∀ μ ν, A' μ ν = - A' ν μ) →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) 0) :
    ColdExpansion ℓ t 0 (expTotal (scaledDensity b h)) (scaledDensity b h) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _ _ W _
    simp only [expTotal, dif_neg (NeZero.ne n)]
    exact Real.exp_pos _
  · intro n _ hn y W hW k c X
    exact contDiffAt_const.mul (hh.smooth n hn y W hW k c X)
  · intro n _ hn y g W hW
    simp only [scaledDensity]
    rw [hh.gauge n hn y g W hW]
  · intro n _ hn y u W hW
    simp only [scaledDensity]
    rw [hh.translation n hn y u W hW]
  · intro n _ _ W _
    simp only [expTotal, dif_neg (NeZero.ne n), Real.log_exp]
    have : ∑ y, centered (scaledDensity b h) n y (trivialField n) = 0 :=
      Finset.sum_eq_zero fun y _ => by simp [centered]
    rw [this]
    ring
  · intro n _ hn y W hW k c X h1 h3 hX
    have e : mixedDeriv (scaledDensity b h n y) W c X = b * mixedDeriv (h n y) W c X :=
      mixedDeriv_const_mul b (h n y) W c X h3 (hh.smooth n hn y W hW k c X)
    rw [e, abs_mul, abs_of_pos hb]
    have d := hh.decay n hn y W hW k c X h1 h3 hX
    have := mul_le_mul_of_nonneg_left d hb.le
    refine this.trans (le_of_eq ?_)
    by_cases hk : k = 3
    · rw [if_pos hk, if_pos hk, ← hE₃, mul_div_assoc]
    · rw [if_neg hk, if_neg hk, ← hE, mul_div_assoc]
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    have hk3 : k ≤ 3 := by omega
    have e₁ : mixedDeriv (centered (scaledDensity b h) n y) W (fun l => bondFrom y (bb l)) X =
        b * mixedDeriv (centered h n y) W (fun l => bondFrom y (bb l)) X := by
      rw [centered_scaledDensity]
      exact mixedDeriv_const_mul b _ W _ X hk3 ((hh.smooth n hn y W hW k _ X).sub contDiffAt_const)
    have e₂ : mixedDeriv (centered (scaledDensity b h) n' y') W' (fun l => bondFrom y' (bb l)) X =
        b * mixedDeriv (centered h n' y') W' (fun l => bondFrom y' (bb l)) X := by
      rw [centered_scaledDensity]
      exact mixedDeriv_const_mul b _ W' _ X hk3 ((hh.smooth n' hn' y' W' hW' k _ X).sub contDiffAt_const)
    rw [e₁, e₂, ← mul_sub, abs_mul, abs_of_pos hb, ← hE, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (hh.local_density n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu) hb.le
  · intro A A' hA hA'
    have := (hsum A A' hA hA').mul_left b
    rw [mul_zero] at this
    have e : (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit (scaledDensity b h) cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) =
        fun cc => b * secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2) :=
      funext fun cc => secondDerivLimit_scaledDensity hF hh.smooth hlim _ _ _ _
    rw [e]
    exact this
theorem isCurvatureFamily_of_coldDensityBounds (hη : 0 < η₃) (hη1 : η₃ ≤ 1) (hε : 0 < ε)
    (hh : ColdDensityBounds ℓ ε (ε / η₃) h) :
    IsCurvatureFamily ℓ (ε / η₃) h := by
  have hle : ε ≤ ε / η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  refine ⟨hh.smooth, hh.gauge, hh.translation, ?_, ?_⟩
  · intro n _ hn y W hW k c X h1 h3 hX
    refine (hh.decay n hn y W hW k c X h1 h3 hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (weight_pos ℓ _).le
    split_ifs
    · exact le_rfl
    · exact hle
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    exact (hh.local_density n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu).trans
      (div_le_div_of_nonneg_right hle (weight_pos ℓ _).le)
theorem secondDerivLimit_tendsto_and_hasSum_zero (hN : InvariantFamilyCurvatureForm) (hF : ℓ.Admissible)
    (hη : 0 < η₃) (hη1 : η₃ ≤ 1) (hε : 0 < ε)
    (hh : ColdDensityBounds ℓ ε (ε / η₃) h) (hc : SumInvariantUnderIsometries ℓ h) :
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
        Filter.atTop (𝓝 (secondDerivLimit h c c' X X'))) ∧
    ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) 0 := by
  obtain ⟨hl, v, hv⟩ := hN ℓ hF _ h (isCurvatureFamily_of_coldDensityBounds hη hη1 hε hh) hc
  refine ⟨hl, fun A A' hA hA' => ?_⟩
  have h1 := hv A A' hA hA'
  have h2 := hh.no_curvature_term A A' hA hA'
  rw [h1.tsum_eq] at h2
  rwa [h2] at h1
theorem isLinearPotential_planeCurvature (X : imaginaryQuaternions) (μ ν : Fin 4) (hμν : μ < ν) :
    IsLinearPotential (constantPlaneCurvature X μ ν) (linearPotential (planeCurvature X μ ν)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdStepDensities.constantPlaneCurvature_isLinearPotential <;> assumption
theorem quaternionI_norm_eq_one : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem blockConditionalMean_scaledDensity (R : StepSetup) (b : ℝ) (h : LocalDensity) (F : BlockFrame)
    (Y : F.Cell) (V : F.GaugeField F.top) :
    blockConditionalMean R (scaledDensity b h) F Y V = b * blockConditionalMean R h F Y V := by
  unfold blockConditionalMean conditionalExpansionMean cutoffMean
  have e : ∀ η, cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach
      (localFamilyOfDensity (scaledDensity b h)) Y η V =
      b * cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity h) Y η V :=
    fun η => by
    unfold cellCentredExpansion
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centredExpansion, ColdStepAtMirrorFrames.subtractTrivial, localFamilyOfDensity, scaledDensity]
    ring
  simp only [e, mul_assoc]
  rw [MeasureTheory.integral_const_mul, mul_div_assoc]
theorem termBounds_of_densityBounds (hA : TopFamilyOnTori) (hF : ℓ.Admissible)
    (hn : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ)) {t : ℕ}
    {E E₃ B : ℝ} {g : TopLevelFamily} (hEE : E ≤ E₃) (hB0 : 0 ≤ B)
    (hB : B * weightGrowthSup ℓ.rt ℓ.n₁ ≤ 2⁻¹ ^ 6 * E)
    (hd : IsLocalDensity ℓ.side t ℓ.n₀ (5 / 4 * ℓ.threshold) g)
    (hdec : DerivDecay ℓ.side t ℓ.n₀ (5 / 4 * ℓ.threshold) g fun k m => 2⁻¹ ^ 6 * (if k = 3 then E₃ else E) /
      torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) m + B * Real.exp (-(ℓ.rt / 2 ^ 6 * m)))
    (hloc : IsLocalOnTori ℓ.side t ℓ.n₀ (9 / 8 * ℓ.threshold) (centredFamily g) fun r =>
      2⁻¹ ^ 4 * E / torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) r) :
    TermBounds ℓ (2⁻¹ ^ 5 * E) (2⁻¹ ^ 5 * E₃) (2⁻¹ ^ 4 * E) (densityOfTopFamily ℓ.side t g) := by
  have hσ := hF.σ_pos
  refine termBounds_of_topLevelFamily hA hF (by linarith) (by linarith) hd
    (derivDecay_mono hdec fun k m _ _ => ?_) (isLocalOnTori_mono hloc fun m => ?_)
  · rw [torusDecayFactor_eq_weight hn]
    have hw := weight_pos ℓ m
    have he := exp_le_weightGrowthSup_div ℓ hF.rt_pos hF.n₁_pos m (ℓ.rt / 2 ^ 6) (by
      have := hF.rt_pos
      linarith)
    have h1 : B * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ 2⁻¹ ^ 6 * E / ℓ.weight m := by
      calc B * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ B * (weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m) :=
            mul_le_mul_of_nonneg_left he hB0
        _ = B * weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m := by rw [mul_div_assoc]
        _ ≤ _ := div_le_div_of_nonneg_right hB hw.le
    have h2 : (2⁻¹ : ℝ) ^ 6 * E / ℓ.weight m ≤ 2⁻¹ ^ 6 * (if k = 3 then E₃ else E) / ℓ.weight m := by
      refine div_le_div_of_nonneg_right ?_ hw.le
      split_ifs
      · nlinarith
      · exact le_rfl
    refine (add_le_add le_rfl (h1.trans h2)).trans (le_of_eq ?_)
    split_ifs <;> · rw [← add_div]; congr 1; ring
  · rw [torusDecayFactor_eq_weight hn]
end FamilyMeanAtStep
open FamilyMeanAtStep in
theorem meanOfFamilyAtStepStatement_holds (hL : ColdExpansionRegular) (hN : InvariantFamilyCurvatureForm)
    (hA : TopFamilyOnTori) (hNum : curvatureValueLinearityStatement) : meanOfFamilyAtStepStatement := by
  intro T hD hOn
  obtain ⟨c, nss, hTies, hAll⟩ := hOn
  refine ⟨T.CE, max (max T.floorMin T.yC) ((2 ^ 6 * T.CE * weightGrowthSup T.rt T.n₁ + 1) ^ 2), hD.CE_pos.le,
    fun y hy R hR ε h hε hh hc => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hy
  have hyC : T.yC ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hy
  have hyS : (2 ^ 6 * T.CE * weightGrowthSup T.rt T.n₁ + 1) ^ 2 ≤ y := (le_max_right _ _).trans hy
  have hF : (T.stepParameters y).Admissible := hD.fits y hy₀
  have hn₁ : (T.stepParameters y).n₁ = ((T.stepParameters y).side : ℝ) ^ (1 / 640 : ℝ) := rfl
  have hRow : R.HasExpansions := hR.isStep.1
  have expansionF := hL R.params R.depth R.coupling R.functional R.density (hR.params_eq ▸ hF)
    (by rw [hR.params_eq]; rfl) hRow.1
  have hfam : IsNormBoundedLocalFamily T.side R.depth T.n₀ T.threshold (T.rt / 2 ^ 10) T.E (T.E / T.η₃)
      (localFamilyOfDensity R.density) := by
    rw [hR.params_eq] at expansionF
    exact ⟨expansionF.smooth, expansionF.gauge_invariant, expansionF.translation_invariant, expansionF.decay, expansionF.locality⟩
  have hx : y ≤ R.coupling := hR.le_coupling
  have hxpos : 0 < R.coupling := lt_of_lt_of_le (lt_of_lt_of_le one_pos hD.yC_ge) (hyC.trans hx)
  rw [hR.params_eq] at hh hc ⊢
  have hE0 : 0 < T.E := hF.E_pos
  set b : ℝ := T.E / ε with hbdef
  have hb : 0 < b := div_pos hE0 hε
  have hEb : b * ε = (T.stepParameters y).E := by
    show b * ε = T.E
    rw [hbdef]
    field_simp
  have hE₃ : b * (ε / T.η₃) = (T.stepParameters y).E₃ := by
    show b * (ε / T.η₃) = T.E / T.η₃
    rw [hbdef]
    field_simp
  obtain ⟨hl, hs⟩ := secondDerivLimit_tendsto_and_hasSum_zero hN hF hD.η₃_pos hD.η₃_le hε hh hc
  have hrow := coldExpansion_scaledDensity hF R.depth hb hh hEb hE₃ hl hs
  have expansionS := hL (T.stepParameters y) R.depth 0 _ (scaledDensity b h) hF hn₁ hrow
  have M := (hAll y hyC).conditionalMean R.depth R.coupling (localFamilyOfDensity R.density)
    (localFamilyOfDensity (scaledDensity b h)) T.E false hx hE0 hfam expansionS
  have hmean : blockConditionalMean R (scaledDensity b h) = conditionalExpansionMean false T.coupling T.ρA (T.threshold / 64)
      R.coupling (frameRadius R.coupling) T.cutoff
      (localFamilyOfDensity R.density) (localFamilyOfDensity (scaledDensity b h)) := by
    have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
    have hs' : R.ballRadius = T.threshold / 64 := by
      show R.params.threshold / 64 = _
      rw [hR.params_eq]
      rfl
    unfold blockConditionalMean
    rw [ha, hR.anchorRadius_eq, hs', hR.barrierFn_eq]
    rfl
  have hρ : T.ρA = c.ρA := hTies.2.2.1.symm
  rw [hρ] at hmean
  have hCE0 : 0 < T.CE := hD.CE_pos
  have hroot : 2 ^ 6 * T.CE * weightGrowthSup T.rt T.n₁ + 1 ≤ Real.sqrt R.coupling :=
    Real.le_sqrt_of_sq_le (hyS.trans hx)
  have hrpow : R.coupling ^ (-(1 / 2) : ℝ) = (Real.sqrt R.coupling)⁻¹ := by
    rw [Real.rpow_neg hxpos.le, Real.sqrt_eq_rpow]
  have hsq : 0 < Real.sqrt R.coupling := Real.sqrt_pos.mpr hxpos
  have hB : T.CE * T.E * R.coupling ^ (-(1 / 2 : ℝ)) * weightGrowthSup T.rt T.n₁ ≤ 2⁻¹ ^ 6 * T.E := by
    rw [hrpow]
    have h1 : T.CE * weightGrowthSup T.rt T.n₁ * (Real.sqrt R.coupling)⁻¹ ≤ 2⁻¹ ^ 6 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hsq]
      nlinarith
    calc T.CE * T.E * (Real.sqrt R.coupling)⁻¹ * weightGrowthSup T.rt T.n₁ =
          T.E * (T.CE * weightGrowthSup T.rt T.n₁ * (Real.sqrt R.coupling)⁻¹) := by ring
      _ ≤ T.E * 2⁻¹ ^ 6 := mul_le_mul_of_nonneg_left h1 hE0.le
      _ = 2⁻¹ ^ 6 * T.E := mul_comm _ _
  have hEη : T.E ≤ T.E / T.η₃ := by
    rw [le_div_iff₀ hD.η₃_pos]
    nlinarith [hD.η₃_le]
  have P : TermBounds (T.stepParameters y) (2⁻¹ ^ 5 * T.E) (2⁻¹ ^ 5 * (T.E / T.η₃)) (2⁻¹ ^ 4 * T.E)
      (densityOfTopFamily (T.stepParameters y).side R.depth (blockConditionalMean R (scaledDensity b h))) := by
    rw [hmean]
    exact termBounds_of_densityBounds hA hF hn₁ hEη (by positivity) hB M.density M.decay M.locality
  have hscale : densityOfTopFamily (T.stepParameters y).side R.depth (blockConditionalMean R h) =
      scaledDensity b⁻¹ (densityOfTopFamily (T.stepParameters y).side R.depth
        (blockConditionalMean R (scaledDensity b h))) := by
    funext n Y V
    simp only [densityOfTopFamily, scaledDensity, blockConditionalMean_scaledDensity]
    field_simp
  have P' := termBounds_scaled (inv_pos.mpr hb).le P
  have hbinv : b⁻¹ * T.E = ε := by
    rw [hbdef]
    field_simp
  have e₁ : b⁻¹ * (2⁻¹ ^ 5 * T.E) = 2⁻¹ ^ 5 * ε := by rw [← hbinv]; ring
  have e₂ : b⁻¹ * (2⁻¹ ^ 5 * (T.E / T.η₃)) = 2⁻¹ ^ 5 * (ε / T.η₃) := by rw [← hbinv]; ring
  have e₃ : b⁻¹ * (2⁻¹ ^ 4 * T.E) = 2⁻¹ ^ 4 * ε := by rw [← hbinv]; ring
  rw [e₁, e₂, e₃] at P'
  rw [hscale]
  refine ⟨P', ?_⟩
  obtain ⟨q, hq, hbq⟩ := M.flat_form
  obtain ⟨v, hv, hvb⟩ := hbq quaternionI 0 1 (linearPotential (planeCurvature quaternionI 0 1))
    quaternionI_norm_eq_one (by decide) (isLinearPotential_planeCurvature quaternionI 0 1 (by decide))
  obtain ⟨-, -, -, -, ls⟩ := hA (T.stepParameters y) hF R.depth (5 / 4 * T.threshold)
    (blockConditionalMean R (scaledDensity b h))
    (by have := hD.σ_pos; show T.threshold ≤ _; linarith)
  have tend : ∀ (c₁ c₂ : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions), Filter.Tendsto (fun n : ℕ =>
      mixedDeriv (densityOfTopFamily (T.stepParameters y).side R.depth
        (blockConditionalMean R (scaledDensity b h)) n 0) (trivialField n)
        ![bondFrom 0 c₁, bondFrom 0 c₂] ![X, X']) Filter.atTop (𝓝 (q c₁ c₂ X X')) := fun c₁ c₂ X X' => by
    refine (hq c₁ c₂ X X').congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (T.stepParameters y).n₀] with n hn'
    rw [ls c₁ c₂ X X' n hn', hmean]
    rfl
  have hnum : HasUnitPlaneValue (densityOfTopFamily (T.stepParameters y).side R.depth
      (blockConditionalMean R (scaledDensity b h))) v := by
    refine ⟨fun c₁ c₂ X X' => ⟨_, tend c₁ c₂ X X'⟩, ?_⟩
    have hterm : limitFormTerm (densityOfTopFamily (T.stepParameters y).side R.depth
        (blockConditionalMean R (scaledDensity b h))) unitPlaneCurvature unitPlaneCurvature =
        fun e => q e.1 e.2 (linearPotential (planeCurvature quaternionI 0 1) e.1)
          (linearPotential (planeCurvature quaternionI 0 1) e.2) := by
      funext ⟨c₁, c₂⟩
      exact (tend c₁ c₂ _ _).limUnder_eq
    rw [hterm]
    exact hv
  refine ⟨b⁻¹ * v, (hNum _ hF).2.1 b⁻¹ _ v P.admissible hnum, ?_⟩
  rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
  calc b⁻¹ * |v| ≤ b⁻¹ * (T.CE * T.E * R.coupling ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hvb (inv_pos.mpr hb).le
    _ = T.CE * (b⁻¹ * T.E) * R.coupling ^ (-(1 / 2 : ℝ)) := by ring
    _ = T.CE * ε * R.coupling ^ (-(1 / 2) : ℝ) := by rw [hbinv]
end ResponseInTheExpansion
end YangMills.Construction
end
