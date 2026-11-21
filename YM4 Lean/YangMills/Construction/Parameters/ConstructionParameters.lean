import YangMills.Construction.Averaging.SmoothingRadius
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ParameterChoice
abbrev spacetimeDim : ℕ := 4
abbrev colorNumber : ℕ := 2
def IsPositivePowerOf (L x : ℕ) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ x = L ^ b
structure InitialChoice where
  r : ℕ
  r₀ : ℝ
  rStar : ℝ
  𝔭₀ : ℕ
  𝔭₁ : ℝ
  q : ℕ
  κ₀ : ℝ
  v : ℝ
  βs : ℝ
  β₀ : ℝ
  θ : ℝ
  qStar : ℕ
  βH : ℝ
  θs : ℝ
  νI : ℕ
  Cg : ℕ
  dial : ℝ
structure ChoiceUpToCubes extends InitialChoice where
  L : ℕ
  αHat : ℝ
  ϑ₂ : ℝ
  LFlat : ℕ
  blockNumber : ℕ
  gapNumber : ℕ
  εv : ℝ
  εBar : ℝ
  κ : ℝ
  κ₁ : ℝ
  M₁ : ℕ
  M₁Sharp : ℝ
  Θ₁ : ℝ
  ϖT : ℕ
  rPrime : ℕ
  ℓa : ℕ
  cHat : ℝ
  cubeSizeConst : ℝ
  M : ℕ
structure ChoiceUpToDegreeConstants extends ChoiceUpToCubes where
  A₁ : ℝ
  A₀ : ℝ
structure ChoiceUpToRadii extends ChoiceUpToDegreeConstants where
  C₀ : ℝ
  C₁ : ℝ
  α₁ : ℝ
  α₀ : ℝ
  α₁Prime : ℝ
  α₀Prime : ℝ
  α₂ : ℝ
  α₃ : ℝ
  E₀ : ℝ
  α₄ : ℝ
  θc : ℝ
  M₀ : ℝ
  εI₀ : ℝ
  εI₁ : ℝ
structure ChoiceUpToCoupling extends ChoiceUpToRadii where
  CN : ℝ
  CV : ℝ
  KA : ℝ
  CL : ℝ
  κ₂ : ℝ
  Cn : ℝ
  Kϑ : ℝ
  CStar : ℝ
  cJ : ℝ
  γ : ℝ
  γH : ℝ
structure FullChoice extends ChoiceUpToCoupling where
  ϱ : ℝ
  ca : ℝ
  γJ : ℝ
  γU : ℝ
  γUPrime : ℝ
  ϑ : ℝ
  γW : ℝ → ℝ
structure FreeVariables where
  g : ℝ
  m : ℕ
  β : ℝ
  K : ℕ
def FreeVariables.bareCouplingConstant (V : FreeVariables) : ℝ := V.β ^ (-(1 / 2) : ℝ)
structure DerivedConstants where
  o : ℝ
  flowConstB : ℝ
  cubeSizeOrderConst : ℝ
  ϑ₀ : ℝ
  L₀ : InitialChoice → ℕ
  c₂ : ℕ → ℝ
  M₁Thr : ℕ → ℝ
  δ₀Ring : ℕ → ℝ
  a₀Ring : ℕ → ℝ
  B₀ : ℕ → ℝ
  δ₁Ring : ℕ → ℝ
  B₃ : ℕ → ℝ
  B₁ : ℕ → ℕ → ℕ → ℝ
  c₁ : ℕ → ℕ → ℕ → ℝ
  B₅ : ℕ → ℕ → ℕ → ℝ
  a₀ : ℕ → ℕ → ℕ → ℝ
  a₁ : ℕ → ℕ → ℕ → ℝ
  εBarG : ℕ → ℕ → ℕ → ℝ
  rB : ℕ → ℕ → ℕ → ℝ
  radiusCeilingC : ℕ → ℕ → ℕ → ℝ
  aPr : ℕ → ℕ → ℕ → ℝ
  aPos : ℕ → ℕ → ℕ → ℝ
  aR : ℕ → ℕ → ℕ → ℝ
  radiusCeilingComplex : ℕ → ℕ → ℕ → ℝ
  aUpperW : ℕ → ℕ → ℕ → ℝ
  aLowerW : ℕ → ℕ → ℕ → ℝ
  complexPairConst : ℕ → ℕ → ℕ → ℝ
  radiusCeilingCommon : ℕ → ℕ → ℕ → ℝ
  BW : ℕ → ℕ → ℝ
  δW : ℕ → ℕ → ℝ
  μ₀ : ℕ → ℕ → ℝ
  C₁Fl : ChoiceUpToDegreeConstants → ℝ
  Cβ : ChoiceUpToRadii → ℝ
  CPrime : ChoiceUpToRadii → ℝ
  γAPrime : ChoiceUpToCoupling → ℝ → ℝ
  γStar : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  CW0 : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  kW : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℕ
def windowWidth (rStar : ℝ) (L : ℕ) : ℝ := (1 - 2 * rStar / L) / 10
def oneLoopCoefficient (L : ℕ) : ℝ :=
  11 * (colorNumber : ℝ) ^ 2 / (12 * Real.pi ^ 2) * Real.log L
def doubledFiniteCoefficient (T : DerivedConstants) (L : ℕ) : ℝ := 2 * T.c₂ L
def variationalRadius (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : ℝ := min (T.a₀ L 𝔐 R₁) 1
def firstRadius (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : ℝ :=
  min (T.a₁ L 𝔐 R₁)
    (min (variationalRadius T L 𝔐 R₁ / T.B₃ L) (Averaging.smoothingRadius L / T.B₃ L))
def firstRadiusScaled (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : ℝ :=
  firstRadius T L 𝔐 R₁ / (1 + 15 * ((spacetimeDim : ℝ) - 1) * (L : ℝ) ^ 2)
def primedCeilingZero (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : ℝ := T.radiusCeilingCommon L 𝔐 R₁
def primedCeilingOne (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : ℝ := T.radiusCeilingCommon L 𝔐 R₁
def secondCubeSize (L M₁ : ℕ) : ℕ := L ^ 2 * M₁
def secondCouplingScale (cHat : ℝ) (L M : ℕ) : ℝ := cHat * ((L : ℝ) * M) ^ (-4 : ℤ)
structure IsAdmissible (T : DerivedConstants) (c : FullChoice) : Prop where
  r_floor : 2 ≤ c.r
  r₀_floor : (c.r : ℝ) ≤ c.r₀
  rStar_pos : 0 < c.rStar
  𝔭₀_pos : 1 ≤ c.𝔭₀
  q_pos : 1 ≤ c.q
  κ₀_pos : 0 < c.κ₀
  v_floor : 2 * (c.𝔭₀ : ℝ) + (spacetimeDim : ℝ) * c.r₀ ≤ c.v
  βs_mem : c.βs ∈ Ioc (0 : ℝ) (1 / 4)
  β₀_mem : c.β₀ ∈ Ioo (0 : ℝ) (1 / 3)
  θ_mem : c.θ ∈ Ioo (0 : ℝ) (1 / 2 * (1 - 3 * c.β₀))
  qStar_pos : 1 ≤ c.qStar
  βH_mem : c.βH ∈ Ioo (0 : ℝ) 1
  θs_mem : c.θs ∈ Ioo (0 : ℝ) 1
  νI_mem : c.νI ∈ Icc (c.r + 1) (8 * c.r)
  Cg_mem : c.Cg = 1 ∨ c.Cg = 2
  dial_mem : c.dial ∈ Ioo (0 : ℝ) 1
  L_odd : Odd c.L
  L_floor : T.L₀ c.toInitialChoice ≤ c.L
  c₂_nonneg : 0 ≤ T.c₂ c.L
  smoothingRadius_mem : Averaging.smoothingRadius c.L ∈ Ioc (0 : ℝ) 1
  αHat_mem : c.αHat ∈ Ioo (1 / 2 : ℝ) 1
  ϑ₂_mem : c.ϑ₂ ∈ Ioo ((c.L : ℝ) ^ (-(2 * c.αHat - 1))) 1
  LFlat_floor : 2 ≤ c.LFlat
  LFlat_half : 2 * c.LFlat < c.L
  LFlat_square : 3 * c.LFlat ^ 2 ≤ c.L
  blockNumber_floor : T.M₁Thr c.L ≤ c.blockNumber
  blockNumber_power : IsPositivePowerOf c.L c.blockNumber
  gapNumber_floor : c.L ≤ c.gapNumber
  gapNumber_power : IsPositivePowerOf c.L c.gapNumber
  B₁_pos : 0 < T.B₁ c.L c.blockNumber c.gapNumber
  c₁_pos : 0 < T.c₁ c.L c.blockNumber c.gapNumber
  B₃_floor : 1 ≤ T.B₃ c.L
  B₅_pos : 0 < T.B₅ c.L c.blockNumber c.gapNumber
  a₀_pos : 0 < T.a₀ c.L c.blockNumber c.gapNumber
  a₁_pos : 0 < T.a₁ c.L c.blockNumber c.gapNumber
  B₃_mul_a₁_le_a₀ : T.B₃ c.L * T.a₁ c.L c.blockNumber c.gapNumber ≤ T.a₀ c.L c.blockNumber c.gapNumber
  εBarG_pos : 0 < T.εBarG c.L c.blockNumber c.gapNumber
  rB_pos : 0 < T.rB c.L c.blockNumber c.gapNumber
  radiusCeilingC_pos : 0 < T.radiusCeilingC c.L c.blockNumber c.gapNumber
  aPr_pos : 0 < T.aPr c.L c.blockNumber c.gapNumber
  aPos_pos : 0 < T.aPos c.L c.blockNumber c.gapNumber
  aR_pos : 0 < T.aR c.L c.blockNumber c.gapNumber
  radiusCeilingComplex_pos : 0 < T.radiusCeilingComplex c.L c.blockNumber c.gapNumber
  aUpperW_pos : 0 < T.aUpperW c.L c.blockNumber c.gapNumber
  aLowerW_pos : 0 < T.aLowerW c.L c.blockNumber c.gapNumber
  complexPairConst_pos : 0 < T.complexPairConst c.L c.blockNumber c.gapNumber
  radiusCeilingCommon_pos : 0 < T.radiusCeilingCommon c.L c.blockNumber c.gapNumber
  εv_pos : 0 < c.εv
  εv_lower : T.B₃ c.L * firstRadiusScaled T c.L c.blockNumber c.gapNumber ≤ c.εv
  εv_upper : c.εv + 3 / 2 * c.εv ^ 2 ≤ variationalRadius T c.L c.blockNumber c.gapNumber
  εv_smoothing : 2 * c.εv ≤ Averaging.smoothingRadius c.L
  εBar_pos : 0 < c.εBar
  εBar_le_firstRadius : c.εBar ≤ firstRadius T c.L c.blockNumber c.gapNumber
  B₃_mul_εBar_le_εv : T.B₃ c.L * c.εBar ≤ c.εv
  εBar_le_εBarG : c.εBar ≤ T.εBarG c.L c.blockNumber c.gapNumber
  κ_pos : 0 < c.κ
  κ₁_pos : 0 < c.κ₁
  M₁_power : IsPositivePowerOf c.L c.M₁
  M₁_floor : c.gapNumber * c.blockNumber ≤ c.M₁
  M₁Sharp_floor : 5 * (c.L : ℝ) * c.M₁ ≤ c.M₁Sharp
  Θ₁_floor : 1 ≤ c.Θ₁
  ϖT_pos : 1 ≤ c.ϖT
  rPrime_power : IsPositivePowerOf c.L c.rPrime
  ℓa_power : IsPositivePowerOf c.L c.ℓa
  cHat_pos : 0 < c.cHat
  cubeSizeConst_pos : 0 < c.cubeSizeConst
  M_power : ∃ k : ℕ, c.M = c.L ^ k
  A₁_pos : 0 < c.A₁
  A₀_pos : 0 < c.A₀
  C₁Fl_floor : 1 ≤ T.C₁Fl c.toChoiceUpToDegreeConstants
  C₀_pos : 0 < c.C₀
  C₁_pos : 0 < c.C₁
  α₁_pos : 0 < c.α₁
  α₀_pos : 0 < c.α₀
  α₁Prime_pos : 0 < c.α₁Prime
  α₀Prime_pos : 0 < c.α₀Prime
  α₂_pos : 0 < c.α₂
  α₃_pos : 0 < c.α₃
  α₄_pos : 0 < c.α₄
  E₀_pos : 0 < c.E₀
  εI₀_pos : 0 < c.εI₀
  εI₁_pos : 0 < c.εI₁
  θc_mem : c.θc ∈ Ioo (0 : ℝ) 1
  M₀_pos : 0 < c.M₀
  Cβ_nonneg : 0 ≤ T.Cβ c.toChoiceUpToRadii
  CPrime_pos : 0 < T.CPrime c.toChoiceUpToRadii
  CN_floor : 1 ≤ c.CN
  CV_floor : 1 ≤ c.CV
  KA_floor : 1 ≤ c.KA
  CL_floor : 1 ≤ c.CL
  κ₂_floor : 1 ≤ c.κ₂
  Cn_floor : 1 ≤ c.Cn
  Kϑ_pos : 0 < c.Kϑ
  CStar_pos : 0 < c.CStar
  cJ_nonneg : 0 ≤ c.cJ
  γ_pos : 0 < c.γ
  γH_pos : 0 < c.γH
  ϱ_pos : 0 < c.ϱ
  ca_pos : 0 < c.ca
  γAPrime_mem : T.γAPrime c.toChoiceUpToCoupling c.ϱ ∈ Ioc (0 : ℝ) c.γH
  γU_le_γJ : c.γU ≤ c.γJ
  γUPrime_le_γU : c.γUPrime ≤ c.γU
  γUPrime_pos : 0 < c.γUPrime
  γW_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < c.γW t
  γStar_mem : T.γStar c.toChoiceUpToCoupling c.ca c.γJ ∈ Ioc (0 : ℝ) c.γJ
  ϑ₀_mem : T.ϑ₀ ∈ Ioc (0 : ℝ) 1
  ϑ_mem : c.ϑ ∈ Ioc (0 : ℝ) 1
  kW_pos : 1 ≤ T.kW c.ϑ c.toChoiceUpToCoupling c.ϱ c.ca
end ParameterChoice
end YangMills.Construction
end
