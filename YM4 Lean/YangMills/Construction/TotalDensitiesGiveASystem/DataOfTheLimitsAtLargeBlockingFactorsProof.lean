import YangMills.Construction.TotalDensitiesGiveASystem.DataOfTheLimitsAtLargeBlockingFactors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
private def limitSetupConstants : ParameterChoice.DerivedConstants where
  o := 0
  flowConstB := 0
  cubeSizeOrderConst := 0
  ϑ₀ := 0
  L₀ := fun _ => 0
  c₂ := fun _ => 0
  M₁Thr := fun _ => 0
  δ₀Ring := fun _ => 0
  a₀Ring := fun _ => 0
  B₀ := fun _ => 0
  δ₁Ring := fun _ => 0
  B₃ := fun _ => 0
  B₁ := fun _ _ _ => 0
  c₁ := fun _ _ _ => 0
  B₅ := fun _ _ _ => 0
  a₀ := fun _ _ _ => 0
  a₁ := fun _ _ _ => 0
  εBarG := fun _ _ _ => 0
  rB := fun _ _ _ => 0
  radiusCeilingC := fun _ _ _ => 0
  aPr := fun _ _ _ => 0
  aPos := fun _ _ _ => 0
  aR := fun _ _ _ => 0
  radiusCeilingComplex := fun _ _ _ => 0
  aUpperW := fun _ _ _ => 0
  aLowerW := fun _ _ _ => 0
  complexPairConst := fun _ _ _ => 0
  radiusCeilingCommon := fun _ _ _ => 0
  BW := fun _ _ => 0
  δW := fun _ _ => 0
  μ₀ := fun _ _ => 0
  C₁Fl := fun _ => 0
  Cβ := fun _ => 0
  CPrime := fun _ => 1
  γAPrime := fun _ _ => 0
  γStar := fun _ _ _ => 0
  CW0 := fun _ _ _ _ => 0
  kW := fun _ _ _ _ => 0

private def limitSetupChoice (L : ℕ) : ParameterChoice.FullChoice where
  r := 2
  r₀ := 0
  rStar := 0
  𝔭₀ := 0
  𝔭₁ := 0
  q := 0
  κ₀ := 0
  v := 0
  βs := 0
  β₀ := 0
  θ := 0
  qStar := 0
  βH := 0
  θs := 0
  νI := 0
  Cg := 0
  dial := 0
  L := L
  αHat := 0
  ϑ₂ := 0
  LFlat := 0
  blockNumber := 0
  gapNumber := L
  εv := 0
  εBar := 0
  κ := 0
  κ₁ := 0
  M₁ := 0
  M₁Sharp := 0
  Θ₁ := 0
  ϖT := 0
  rPrime := 0
  ℓa := 0
  cHat := 0
  cubeSizeConst := 0
  M := 1
  A₁ := 0
  A₀ := 0
  C₀ := 0
  C₁ := 0
  α₁ := 0
  α₀ := 0
  α₁Prime := 0
  α₀Prime := 0
  α₂ := 0
  α₃ := 0
  E₀ := 0
  α₄ := 0
  θc := 0
  M₀ := 0
  εI₀ := 0
  εI₁ := 0
  CN := 0
  CV := 0
  KA := 0
  CL := 0
  κ₂ := 0
  Cn := 0
  Kϑ := 0
  CStar := 0
  cJ := 0
  γ := 1
  γH := (2 : ℝ) ^ (-(1 / 2) : ℝ)
  ϱ := 0
  ca := 0
  γJ := (2 : ℝ) ^ (-(1 / 2) : ℝ)
  γU := 0
  γUPrime := 0
  ϑ := 0
  γW := fun _ => 0

theorem largeOddBlockingFactorsHaveLimitSetup_of_choosable :
    TotalDensitiesGiveASystem.LargeOddBlockingFactorsHaveLimitSetup := by
  refine ⟨max 13 (8 * 105 ^ 4), fun L hodd hL => ?_⟩
  have hfactor : Conventions.IsAdmissibleBlockingFactor L :=
    ⟨hodd, (le_max_left _ _).trans hL⟩
  have hγ : 0 < (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  let A : FamiliesOfLimits.LimitSetup :=
    { consts := limitSetupConstants
      choice := limitSetupChoice L
      standingConstraints :=
        { factor_admissible := hfactor
          M_eq_pow := ⟨0, by simp [limitSetupChoice]⟩
          exponent_lowerBound := by norm_num [ParameterChoice.ExponentLowerBound, limitSetupChoice]
          c₂_nonneg := le_rfl
          Cβ_nonneg := le_rfl
          CPrime_pos := one_pos
          γ_pos := one_pos
          γH_pos := hγ
          γH_le_ceiling := by
            change (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤
              ((1 : ℝ) ^ (-2 : ℤ) + 2 * 0 + 1) ^ (-(1 / 2) : ℝ)
            norm_num
          γJ_pos := hγ
          γJ_le_γH := le_rfl
          gap_lowerBound := le_rfl }
      activityKind := .singleScale }
  refine ⟨⟨A, ?_, (le_max_right _ _).trans hL, (2 : ℝ) ^ (-(1 / 2) : ℝ), ⟨hγ, le_rfl⟩⟩, rfl⟩
  exact ⟨hodd, Nat.zero_le L⟩
end YangMills.Construction.TotalDensities
end
