import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.GasPartHasItsBounds
import YangMills.Construction.ResponseInTheExpansion.MeanOfAFamilyAtAStep
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheTotalOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.RemaindersOfAResponseAreCarried
import YangMills.Construction.ResponseInTheExpansion.SmoothPartsHaveTheirBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps RenormalizationStepParameters StepSettings WeightedResponses TermCalculus
theorem responseTermDecomposition (hSm : smoothTermsBoundsStatement) (hGas : gasTermBoundsStatement)
    (hMn : meanOfFamilyAtStepStatement) (hCr : remaindersInvariantUnderIsometries) (hTot : sumOfTermsStatement) :
    responseTermDecompositionStatement := by
  intro a _
  obtain ⟨r₁, hr₁, g₁⟩ := hGas
  obtain ⟨r₂, hr₂, g₂⟩ := hTot
  refine ⟨0, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), fun T _ _ hD hCd hOn hrt => ?_⟩
  obtain ⟨C₁, y₁, hC₁, g₃⟩ := hSm T hD hCd hOn
  obtain ⟨C₂, y₂, hC₂, g₄⟩ := hMn T hD hOn
  obtain ⟨C₃, hC₃, g₁⟩ := g₁ T hD hCd hOn (hrt.trans (min_le_left _ _))
  refine ⟨C₁ + C₂ + C₃, by positivity, fun K hKb => ?_⟩
  obtain ⟨y₃, g₁⟩ := g₁ K
  obtain ⟨y₄, g₂⟩ := g₂ T hD hCd hOn (hrt.trans (min_le_right _ _)) K
  refine ⟨max (max y₁ y₂) (max (max y₃ y₄) (max T.floorMin T.yC)), fun y hy R A hK hA hSym => ?_⟩
  have f₁ := (le_max_left _ _).trans hy
  have f₂ := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_max_left _ _).trans f₁
  have e₂ : y₂ ≤ y := (le_max_right _ _).trans f₁
  have f₃ := (le_max_left _ _).trans f₂
  have f₄ := (le_max_right _ _).trans f₂
  have e₃ : y₃ ≤ y := (le_max_left _ _).trans f₃
  have e₄ : y₄ ≤ y := (le_max_right _ _).trans f₃
  have hyMin : T.floorMin ≤ y := (le_max_left _ _).trans f₄
  have hyC : T.yC ≤ y := (le_max_right _ _).trans f₄
  have hon := hA.onFamily
  have hparams : R.params = T.stepParameters y := hon.params_eq
  have hadmR := hA.admissible
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hx1 : 1 ≤ R.coupling := hD.yC_ge.trans (hyC.trans hxy)
  have hx0 : 0 < R.coupling := lt_of_lt_of_le one_pos hx1
  have hfit : R.params.Admissible := by
    rw [hparams]
    exact hD.fits y hyMin
  obtain ⟨Pf, Ps, Pm, Pt⟩ := g₃ y e₁ R A hon hadmR.abs_coeff_le
  have Pg := g₁ y e₃ R A hK hA hSym
  obtain ⟨hslope, htotal⟩ := g₂ y e₄ R A hK hA
  have hKf : K.Admissible R.params := hK ▸ hadmR.params_admissible
  have hη : K.η₃ = T.η₃ := by
    have h1 := hKf.E₃_eq
    have h2 : R.params.E₃ = R.params.E / T.η₃ := by
      rw [hparams]
      rfl
    rw [h2] at h1
    have h3 := hKf.η₃_pos
    have h4 := hD.η₃_pos
    exact mul_left_cancel₀ hfit.E_pos.ne' ((div_eq_div_iff h4.ne' h3.ne').1 h1)
  have hfam : ColdDensityBounds R.params (K.Kb / R.coupling) (K.Kb / R.coupling / T.η₃) A.totalRemainder := by
    have h0 := hadmR.bounds.total_family
    rw [hK, hη, ← div_eq_mul_inv] at h0
    exact h0
  have hε : 0 < K.Kb / R.coupling := div_pos hKb hx0
  obtain ⟨Pr, v, hv, hvb⟩ := g₄ y e₂ R hon (K.Kb / R.coupling) A.totalRemainder hε hfam
    (hCr T hD y hyMin R A hon hadmR).1
  have hh : 0 ≤ R.coupling ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  have ht : 0 ≤ R.coupling ^ (-(3 / 2) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  have hi : 0 ≤ R.coupling⁻¹ := by positivity
  have c₁ : C₁ ≤ C₁ + C₂ + C₃ := by linarith
  have c₂ : C₂ ≤ C₁ + C₂ + C₃ := by linarith
  have c₃ : C₃ ≤ C₁ + C₂ + C₃ := by linarith
  have mt := mul_le_mul_of_nonneg_right c₁ ht
  have mh := mul_le_mul_of_nonneg_right c₁ hh
  have mi : C₁ / R.coupling ≤ (C₁ + C₂ + C₃) / R.coupling := div_le_div_of_nonneg_right c₁ hx0.le
  have mg := mul_le_mul_of_nonneg_right c₃ ht
  subst hK
  rw [← hη] at Pr
  refine ⟨termBounds_mono mt mt mt Pf, termBounds_mono mi mi mi Ps, termBounds_mono mh mh mh Pm, Pr,
    ⟨v, hv, hvb.trans ?_⟩, termBounds_mono mt mt mt Pt, termBounds_mono mg mg mg Pg, hslope, htotal⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c₂ hε.le) hh
end YangMills.Construction.ResponseInTheExpansion
end
