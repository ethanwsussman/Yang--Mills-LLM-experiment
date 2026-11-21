import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.ClusterExpansionOfAStep.LabelDataOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstant
import YangMills.Construction.ResponseInTheExpansion.ColdHalfOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.NumberOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.ResponseIsCarried
import YangMills.Construction.ResponseInTheExpansion.ResponseLessTheActionReturns
import YangMills.Construction.ResponseInTheExpansion.ResponseLessTheShareReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
namespace ColdResponseCoefficient
theorem rpow_neg_half_eq_inv_sqrt {u : ℝ} (hu : 0 < u) : u ^ (-(1 / 2) : ℝ) = (Real.sqrt u)⁻¹ := by
  rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow]
theorem rpow_neg_three_halves_eq_inv_sqrt_pow {u : ℝ} (hu : 0 < u) :
    u ^ (-(3 / 2) : ℝ) = ((Real.sqrt u) ^ 3)⁻¹ := by
  rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num
theorem mul_rpow_neg_three_halves_le_site {x x' c Ka : ℝ} (hx : 0 < x) (hx'0 : 0 < x') (hx' : x' ≤ 4 * x)
    (hKa : 0 < Ka) (hc : 0 ≤ c) (hfl : 4 * c / Ka ≤ x) :
    c * x ^ (-(3 / 2) : ℝ) ≤ Ka * x' ^ (-(1 / 2) : ℝ) / 2 := by
  rw [rpow_neg_half_eq_inv_sqrt hx'0, rpow_neg_three_halves_eq_inv_sqrt_pow hx]
  set s := Real.sqrt x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have h1 : Real.sqrt x' ≤ 2 * s := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h0 : 0 < Real.sqrt x' := Real.sqrt_pos.mpr hx'0
  have h2 : (2 * s)⁻¹ ≤ (Real.sqrt x')⁻¹ := inv_anti₀ h0 h1
  have h3 : c ≤ Ka * x / 4 := by
    rw [div_le_iff₀ hKa] at hfl
    linarith
  have h4 : c * (s ^ 3)⁻¹ ≤ Ka * (2 * s)⁻¹ / 2 := by
    rw [← hs2] at h3
    rw [mul_inv, mul_inv_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have h5 : Ka * (2 * s)⁻¹ / 2 ≤ Ka * (Real.sqrt x')⁻¹ / 2 := by
    have := mul_le_mul_of_nonneg_left h2 hKa.le
    linarith
  exact h4.trans h5
theorem mul_rpow_neg_three_halves_le_total {x x' c Kb : ℝ} (hx : 0 < x) (hx'0 : 0 < x') (hx' : x' ≤ 4 * x)
    (hKb : 0 < Kb) (hc : 0 ≤ c) (hfl : (8 * c / Kb) ^ 2 ≤ x) :
    c * x ^ (-(3 / 2) : ℝ) ≤ Kb * x'⁻¹ / 2 := by
  rw [rpow_neg_three_halves_eq_inv_sqrt_pow hx]
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have h2 : (4 * x)⁻¹ ≤ x'⁻¹ := inv_anti₀ hx'0 hx'
  have h3 : 8 * c / Kb ≤ s := by
    apply Real.le_sqrt_of_sq_le
    exact hfl
  have h3' : 8 * c ≤ s * Kb := by
    rwa [div_le_iff₀ hKb] at h3
  have h4 : c * (s ^ 3)⁻¹ ≤ Kb * (4 * x)⁻¹ / 2 := by
    rw [← hs2]
    field_simp
    nlinarith
  have h5 : Kb * (4 * x)⁻¹ / 2 ≤ Kb * x'⁻¹ / 2 := by
    have := mul_le_mul_of_nonneg_left h2 hKb.le
    linarith
  exact h4.trans h5
theorem coeff_unique_at (hOne : ResponseInTheExpansion.ColdResponseCoeffUniqueStatement)
    {T : RenormalizationStepParameters.ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy : T.floorMin ≤ y)
    {ℓ : TorusLumps.StepParameters} (hℓ : ℓ = T.stepParameters y) (K : WeightedResponses.ResponseParameters)
    (t : ℕ) (x α α' Ca : ℝ) (P : WeightedResponses.ColdResponse ℓ.side (t + 1))
    (Ra Rb Ra' Rb' : TorusLumps.LocalDensity) (h₁ : 0 < K.η₃) (h₂ : K.η₃ ≤ 1) (h₃ : 0 ≤ K.Kb) (h₄ : 0 < x)
    (h₅ : WeightedResponses.LevelShareBounds ℓ t Ca)
    (h₆ : TorusLumps.SumInvariantUnderIsometries ℓ (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side (t + 1)))
    (h₇ : ResponseInTheExpansion.UnitResponseInvariant ℓ P)
    (h₈ : WeightedResponses.ColdResponseBounds ℓ K (t + 1) x α P Ra Rb)
    (h₉ : WeightedResponses.ColdResponseBounds ℓ K (t + 1) x α' P Ra' Rb') : α = α' := by
  subst hℓ
  exact hOne T hT y hy K t x α α' Ca P Ra Rb Ra' Rb' h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
theorem levelShareBounds_of_admissible {T : RenormalizationStepParameters.ParameterAssignment} (hT : T.Admissible) {y : ℝ}
    (hy : T.floorMin ≤ y) (t : ℕ) (hSh : ShareFamilies.LevelSharesFormCurvatureFamily)
    (hForm : TorusLumps.HasCurvatureForm (ShareFamilies.levelShareFamily T.coupling T.side (t + 1)) 1)
    (hFlat : BlockAverages.flatTopVanishingStatement) :
    WeightedResponses.LevelShareBounds (T.stepParameters y) t
      (TorusLumps.weightGrowthSup T.rt T.n₁ * TorusLumps.maxOfFirstFour T.N) := by
  obtain ⟨h₁, -, h₃⟩ := hSh T hT y hy t
  have hfit := hT.fits y hy
  refine ⟨h₁, hForm, h₃, fun n _ _ z => ?_⟩
  exact (hFlat (TorusFields.torusFrame T.side t n) T.coupling
    (TorusFields.cellsOfSites (TorusFields.torusFrame T.side t n) Finset.univ)
    (by have : (1 : ℝ) ≤ T.coupling := hfit.a_ge; linarith) hfit.L_odd).2.2 _
theorem coldResponseUniqueCoefficient_holds
    (hShare : ResponseInTheExpansion.responseSubShareBoundsStatement)
    (hAction : ResponseInTheExpansion.totalResponseSubActionStatement)
    (hRem : ResponseInTheExpansion.responseRemainderBoundsStatement)
    (hCoeff : ResponseInTheExpansion.responseCurvatureCoeffStatement)
    (hCl : WeightedResponses.ColdBoundsFromHalfBounds)
    (hOne : ResponseInTheExpansion.ColdResponseCoeffUniqueStatement)
    (hSh : ShareFamilies.LevelSharesFormCurvatureFamily)
    (hFm : ShareFamilies.LevelSharesHaveUnitCurvatureForm) (hFlat : BlockAverages.flatTopVanishingStatement)
    (hCar : WeightedResponses.StepResponseIsometryInvariant)
    (hLab : ClusterExpansionOfAStep.CoarseLabelsStandard) : ResponseInTheExpansion.coldResponseUniqueCoefficient := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, g₁⟩ := hShare a ha
  obtain ⟨L₂, r₂, hr₂, g₂⟩ := hAction a ha
  obtain ⟨L₃, r₃, hr₃, g₃⟩ := hRem a ha
  obtain ⟨L₄, r₄, hr₄, g₄⟩ := hCoeff a ha
  obtain ⟨r₆, hr₆, g₆⟩ := hCar
  refine ⟨max (max L₁ L₂) (max L₃ L₄), fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₆ c)))),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (lt_min (hr₄ c) (hr₆ c)))),
    fun T hTa hLT hT hCS hOn hrt => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have u₂ := u₁.trans (min_le_right _ _)
  have t₃ := u₂.trans (min_le_left _ _)
  have u₃ := u₂.trans (min_le_right _ _)
  have t₄ := u₃.trans (min_le_left _ _)
  have t₆ := u₃.trans (min_le_right _ _)
  have l₀ : max (max L₁ L₂) (max L₃ L₄) ≤ T.side := hLT
  have l₁ : L₁ ≤ T.side := (le_trans (le_max_left _ _) (le_max_left _ _)).trans l₀
  have l₂ : L₂ ≤ T.side := (le_trans (le_max_right _ _) (le_max_left _ _)).trans l₀
  have l₃ : L₃ ≤ T.side := (le_trans (le_max_left _ _) (le_max_right _ _)).trans l₀
  have l₄ : L₄ ≤ T.side := (le_trans (le_max_right _ _) (le_max_right _ _)).trans l₀
  obtain ⟨C₂, g₁⟩ := g₁ T hTa l₁ hT hCS hOn t₁
  obtain ⟨C₃, g₂⟩ := g₂ T hTa l₂ hT hCS hOn t₂
  obtain ⟨C₁, g₃⟩ := g₃ T hTa l₃ hT hCS hOn t₃
  obtain ⟨C₄, g₄⟩ := g₄ T hTa l₄ hT hCS hOn t₄
  refine ⟨C₁, max (max C₂ C₄) 1, max C₃ 1, fun K hKc hKa hKb => ?_⟩
  have hKa0 : 0 < K.Ka := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hKa)
  have hKb0 : 0 < K.Kb := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hKb)
  obtain ⟨C, y₄, hC0, g₄⟩ := g₄ K ((le_trans (le_max_right _ _) (le_max_left _ _)).trans hKa) hKb0
  obtain ⟨y₁, g₁⟩ := g₁ K ((le_trans (le_max_left _ _) (le_max_left _ _)).trans hKa) hKb0
  obtain ⟨y₂, g₂⟩ := g₂ K ((le_max_left _ _).trans hKb)
  obtain ⟨y₃, g₃⟩ := g₃ K hKc
  obtain ⟨y₆, g₆⟩ := g₆ T hT t₆ K
  set Ca : ℝ := TorusLumps.weightGrowthSup T.rt T.n₁ * TorusLumps.maxOfFirstFour T.N with hCa
  set c : ℝ := C * |Ca| with hc
  have hc0 : 0 ≤ c := mul_nonneg hC0 (abs_nonneg _)
  refine ⟨C, max (max (max y₁ y₂) (max y₃ y₄)) (max y₆ (max T.floorMin (max (2 * T.B + 1)
    (max (4 * c / K.Ka) ((8 * c / K.Kb) ^ 2))))), hC0, fun y hy R A hK hA hArr => ?_⟩
  have e₀ : max (max y₁ y₂) (max y₃ y₄) ≤ y := (le_max_left _ _).trans hy
  have e₀' := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀
  have e₂ : y₂ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀
  have e₃ : y₃ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans e₀
  have e₄ : y₄ ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans e₀
  have e₆ : y₆ ≤ y := (le_max_left _ _).trans e₀'
  have e₇ := (le_max_right _ _).trans e₀'
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans e₇
  have e₈ := (le_max_right _ _).trans e₇
  have hyB : 2 * T.B + 1 ≤ y := (le_max_left _ _).trans e₈
  have e₉ := (le_max_right _ _).trans e₈
  have hy₁ : 4 * c / K.Ka ≤ y := (le_max_left _ _).trans e₉
  have hy₂ : (8 * c / K.Kb) ^ 2 ≤ y := (le_max_right _ _).trans e₉
  have hℓ : R.params = T.stepParameters y := hA.onFamily.params_eq
  have hxy : y ≤ R.coupling := hA.onFamily.le_coupling
  have hmv := hA.abs_sub_le
  have hB1 : 1 ≤ T.B := hT.B_ge
  rw [abs_le] at hmv
  have hx0 : 0 < R.coupling := by linarith
  have hx'0 : 0 < R.nextCoupling := by linarith [hmv.1]
  have hx'4 : R.nextCoupling ≤ 4 * R.coupling := by linarith [hmv.2]
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hT.fits y hy0
  have hresp := hA.admissible
  have hKf : K.Admissible R.params := hK ▸ hresp.params_admissible
  have hS : WeightedResponses.LevelShareBounds R.params R.depth Ca := by
    rw [hℓ]
    exact levelShareBounds_of_admissible hT hy0 R.depth hSh (hFm T hT R.depth) hFlat
  obtain ⟨b, hb, hfF, hfG⟩ := g₄ y e₄ R A hK hA hArr
  obtain ⟨G, hG, hTG⟩ := g₂ y e₂ R A hK hA hArr
  have hF := g₁ y e₁ R A hK hA hArr
  have hRm := g₃ y e₃ R A hK hA hArr
  have hbc : |b| * Ca ≤ c * R.coupling ^ (-(3 / 2) : ℝ) := by
    have h1 : |b| * Ca ≤ |b| * |Ca| := mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
    have h2 : |b| * |Ca| ≤ C * R.coupling ^ (-(3 / 2) : ℝ) * |Ca| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have h3 : C * R.coupling ^ (-(3 / 2) : ℝ) * |Ca| = c * R.coupling ^ (-(3 / 2) : ℝ) := by
      rw [hc]
      ring
    linarith
  have hb₁ : |b| * Ca ≤ K.Ka * R.nextCoupling ^ (-(1 / 2) : ℝ) / 2 :=
    hbc.trans (mul_rpow_neg_three_halves_le_site hx0 hx'0 hx'4 hKa0 hc0 (hy₁.trans hxy))
  have hb₂ : |b| * Ca ≤ K.Kb * R.nextCoupling⁻¹ / 2 :=
    hbc.trans (mul_rpow_neg_three_halves_le_total hx0 hx'0 hx'4 hKb0 hc0 (hy₂.trans hxy))
  obtain ⟨Ra, Rb, hcl⟩ := hCl R.params K R.depth R.nextCoupling A.coeff b Ca A.coldStep G hfit hKf.η₃_pos
    hKf.η₃_le hKa0.le hKb0.le hx'0 hS hF hG hTG hRm hfF (hfG G hG hTG) hb₁ hb₂
  refine ⟨A.coeff + b, by simpa using hb, ⟨Ra, Rb, hcl⟩, ?_⟩
  rintro α'' ⟨Ra'', Rb'', hcl''⟩
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have hcar := (g₆ y e₆ R A hK hA (hLab R hL2) hArr).2.2
  have hSc : TorusLumps.SumInvariantUnderIsometries R.params
      (ShareFamilies.levelShareFamily R.params.coupling R.params.side (R.depth + 1)) := by
    rw [hℓ]
    exact (hSh T hT y hy0 R.depth).2.1
  exact coeff_unique_at hOne hT hy0 hℓ K R.depth R.nextCoupling α'' (A.coeff + b) Ca A.coldStep Ra'' Rb'' Ra Rb
    hKf.η₃_pos hKf.η₃_le hKb0.le hx'0 hS hSc hcar hcl'' hcl
end ColdResponseCoefficient
end ResponseInTheExpansion
end YangMills.Construction
end
