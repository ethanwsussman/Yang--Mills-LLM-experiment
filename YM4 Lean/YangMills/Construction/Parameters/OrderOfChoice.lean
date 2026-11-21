import YangMills.Construction.FlowConstants.ReferenceWindow
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.ParameterChoice
def SupFromLE (a : ℝ) (h : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ x, a ≤ x → h x ≤ b
def SupFromLT (a : ℝ) (h : ℝ → ℝ) (b : ℝ) : Prop :=
  ∃ b' < b, ∀ x, a ≤ x → h x ≤ b'
structure TailCeiling where
  fn : ℝ → ℝ
  bound : ℝ
def TailCeiling.HoldsAt (p : TailCeiling) (s : ℝ) : Prop :=
  SupFromLE (s ^ (-2 : ℤ)) p.fn p.bound
def TailCeiling.IsWellFormed (p : TailCeiling) : Prop :=
  0 < p.bound ∧ Tendsto p.fn atTop (nhds 0)
def responseRate (T : DerivedConstants) (L : ℕ) : ℝ := T.δ₀Ring L / 8
def collarRatio (T : DerivedConstants) (L M M₁ : ℕ) : ℝ :=
  1 / 16 * T.δ₀Ring L * (M : ℝ) / (M₁ : ℝ)
def expAbsSum (a : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-a * |(n : ℝ)|)
def summabilityThreshold : ℝ :=
  3 * 2 ^ (spacetimeDim + 1) * (2 * Real.log (2 * (spacetimeDim : ℝ)) + 1)
def rarityConstant : ℝ :=
  5 ^ spacetimeDim * ((1 + 3 ^ spacetimeDim) * Real.log 2 + 2 * (spacetimeDim : ℝ) * Real.log 3)
def smallFieldThreshold (c : ChoiceUpToDegreeConstants) (x : ℝ) : ℝ :=
  c.A₀ * x ^ (-(1 / 2) : ℝ) * Real.log x ^ c.𝔭₀
def logRatio (c : InitialChoice) (x : ℝ) : ℝ :=
  Real.log x ^ (-((c.𝔭₀ : ℝ) - c.𝔭₁))
def blockSizeReal (c : ChoiceUpToCubes) (x : ℝ) : ℝ := (Thresholds.blockSize c.L c.r x : ℝ)
def shiftedInverseSq (T : DerivedConstants) (c : ChoiceUpToCoupling) : ℝ :=
  c.γ ^ (-2 : ℤ) - doubledFiniteCoefficient T c.L
def inverseSqAtHigh (c : ChoiceUpToCoupling) : ℝ := c.γH ^ (-2 : ℤ)
def ChoiceUpToCubes.eraseM (c : ChoiceUpToCubes) : ChoiceUpToCubes := { c with M := 0 }
def ChoiceUpToRadii.eraseεI₀ (c : ChoiceUpToRadii) :
    ChoiceUpToRadii := { c with εI₀ := 0, εI₁ := 0 }
def ChoiceUpToRadii.eraseεI₁ (c : ChoiceUpToRadii) :
    ChoiceUpToRadii := { c with εI₁ := 0 }
def ChoiceUpToRadii.eraseα₀ (c : ChoiceUpToRadii) :
    ChoiceUpToRadii :=
  { c.eraseεI₀ with
    α₀ := 0, α₁Prime := 0, α₀Prime := 0, α₂ := 0, α₃ := 0, E₀ := 0, α₄ := 0, θc := 0, M₀ := 0 }
def ChoiceUpToRadii.eraseα₁ (c : ChoiceUpToRadii) :
    ChoiceUpToRadii := { c.eraseα₀ with α₁ := 0 }
def ChoiceUpToCoupling.eraseγ (c : ChoiceUpToCoupling) : ChoiceUpToCoupling :=
  { c with γ := 0, γH := 0 }
def FullChoice.atShape (c : FullChoice) (t : ℝ) : FullChoice :=
  { c with ϑ := t, γU := 0, γUPrime := 0, γW := fun _ => 0 }
structure ExternalConstants where
  blockFloor : ℝ
  propagatorFloor : ℕ → ℝ
  decayBlockFloor : ℕ → ℝ
  decayProductFloor : ℕ → ℝ
  productFloor : ℕ → ℝ
  Cδ : ℝ
  κThreshold : ℕ → ℝ
  remainderConst : ℕ → ℝ
  κAnalytic : ℝ
  rateFraction : ℝ
  islandFraction : ℝ
  cBar : ℝ
  determinantFloor : ℕ → ℝ
  decayConst : ℕ → ℝ
  chartFloor : ℕ → ℝ
  theoremBFloor : ℕ → ℝ → ℝ
  cubeFloorConst : ℝ
  MOfκ : ℕ → ℝ → ℝ
  logFloorConst : ℕ → ℝ
  lastTermConst : ℕ → ℝ
  MThreshold : ℕ → ℝ
  largeFieldCubeFloor : ChoiceUpToCubes → ℝ
  ratioConst : ℝ
  ratioConstM : ℕ → ℝ
  C₀Multiple : ℕ → ℝ
  α₁Ceiling : ChoiceUpToRadii → ℝ
  α₀Ceiling : ChoiceUpToRadii → ℝ
  α₂Const : ℕ → ℝ
  E₀Normaliser : ℕ → ℝ
  potentialConst : ℝ
  ε₀Ceiling : ChoiceUpToRadii → ℝ
  ε₁Ceiling : ChoiceUpToRadii → ℝ
  CRem : ChoiceUpToRadii → ℝ
  couplingCeiling : ChoiceUpToCoupling → ℝ
  cutoffCeilings : List (ChoiceUpToCoupling → TailCeiling)
  normaliserCeiling : ℝ → ℕ → ℝ
  preparatoryFunctionOne : ChoiceUpToCoupling → ℝ → ℝ
  preparatoryFunctionTwo : ChoiceUpToCoupling → ℝ → ℝ
  CFirst : ℕ → ℝ
  CSecond : ℕ → ℝ
  CThird : ℕ → ℝ
  CBar : ℕ → ℝ
  CCheck : ℕ → ℝ
  γLargeField : ChoiceUpToCoupling → ℝ
  αBar : ChoiceUpToCoupling → ℝ
  γVolOne : ChoiceUpToCoupling → ℝ → ℝ
  γVolTwo : ChoiceUpToCoupling → ℝ → ℝ
  Cϖ : ChoiceUpToCoupling → ℝ
  γF : ChoiceUpToCoupling → ℝ → ℝ
  γh : ChoiceUpToCoupling → ℝ → ℝ
  γM : ℝ → ChoiceUpToCoupling → ℝ → ℝ
  neverHealedCeilings : Fin 3 → ChoiceUpToCoupling → TailCeiling
  γMAge : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γw : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γwd : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γwm : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γhl : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γSharp : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  ϱPr : ℝ
  Xϱ : ℝ → ℕ → ℝ → ℝ → ℝ
  γ𝔪 : ChoiceUpToCoupling → ℝ → ℝ → ℝ
  εStar : ℝ
  γTAge : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γTChessboard : ℝ → ChoiceUpToCoupling → ℝ → ℝ
  CW0TwoPoint : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  fourPointRoomThreshold : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  CE0 : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γTwoPoint : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ
  γFourPoint : ℝ → ChoiceUpToCoupling → ℝ → ℝ → ℝ → ℝ
  uniformCeiling : FullChoice → TailCeiling
structure ExternalConstantsInRange (N : ExternalConstants) (c : ChoiceUpToCoupling) :
    Prop where
  decayConst_pos : 0 < N.decayConst c.L
  largeFieldCubeFloor_ge_one : 1 ≤ N.largeFieldCubeFloor c.toChoiceUpToCubes.eraseM
  α₁Ceiling_pos : 0 < N.α₁Ceiling c.toChoiceUpToRadii.eraseα₁
  α₀Ceiling_pos : 0 < N.α₀Ceiling c.toChoiceUpToRadii.eraseα₀
  α₂Const_pos : 0 < N.α₂Const c.L
  ε₀Ceiling_pos : 0 < N.ε₀Ceiling c.toChoiceUpToRadii.eraseεI₀
  ε₁Ceiling_pos : 0 < N.ε₁Ceiling c.toChoiceUpToRadii.eraseεI₁
  CRem_pos : 0 < N.CRem c.toChoiceUpToRadii.eraseεI₁
  couplingCeiling_pos : 0 < N.couplingCeiling c.eraseγ
  cutoffCeilings_wellFormed : ∀ p ∈ N.cutoffCeilings, (p c.eraseγ).IsWellFormed
  normaliserCeiling_pos : 0 < N.normaliserCeiling c.A₀ c.𝔭₀
  preparatoryFunctionOne_tendsto_zero :
    Tendsto (N.preparatoryFunctionOne c.eraseγ) atTop (nhds 0)
  preparatoryFunctionTwo_tendsto_zero :
    Tendsto (N.preparatoryFunctionTwo c.eraseγ) atTop (nhds 0)
  γLargeField_mem : N.γLargeField c.eraseγ ∈ Ioc (0 : ℝ) 1
structure InitialConstraints (c : InitialChoice) : Prop where
  r_floor : 2 ≤ c.r
  r₀_floor : (c.r : ℝ) ≤ c.r₀
  rStar_pos : 0 < c.rStar
  𝔭₀_floor_five : 5 * c.r ≤ c.𝔭₀
  𝔭₀_floor_six : 6 * c.r + 1 ≤ c.𝔭₀
  𝔭₀_floor_dimension : ((spacetimeDim : ℝ) + 5) * c.r₀ + 8 * (c.r : ℝ) + 3 ≤ (c.𝔭₀ : ℝ)
  𝔭₁_lower : (c.𝔭₀ : ℝ) + ((spacetimeDim : ℝ) + 5) * c.r₀ < 2 * c.𝔭₁
  𝔭₁_upper : c.𝔭₁ ≤ (c.𝔭₀ : ℝ) - 4 * (c.r : ℝ) - 1
  q_floor_sum : c.𝔭₀ + 7 * c.r + 1 ≤ c.q
  q_floor_three : 3 * c.𝔭₀ + 3 * c.r + 1 ≤ c.q
  q_floor_twentyOne : 21 * c.𝔭₀ + 1 ≤ c.q
  q_floor_fortyOne : 41 * c.𝔭₀ + 1 ≤ c.q
  κ₀_floor : 17 ≤ c.κ₀
  v_floor : 2 * (c.𝔭₀ : ℝ) + (spacetimeDim : ℝ) * c.r₀ ≤ c.v
  βs_mem : c.βs ∈ Ioc (0 : ℝ) (1 / 4)
  β₀_mem : c.β₀ ∈ Ioo (0 : ℝ) (1 / 3)
  θ_mem : c.θ ∈ Ioo (0 : ℝ) (1 / 2 * (1 - 3 * c.β₀))
  qStar_floor : c.𝔭₁ < (c.qStar : ℝ)
  qStar_gap : (1 + (spacetimeDim : ℝ) + (spacetimeDim : ℝ) * c.β₀) * (c.r : ℝ) < (c.qStar : ℝ) - c.𝔭₁
  βH_mem : c.βH ∈ Ioo (0 : ℝ) 1
  θs_mem : c.θs ∈ Ioo (0 : ℝ) 1
  νI_mem : c.νI ∈ Icc (c.r + 1) (8 * c.r)
  Cg_mem : c.Cg = 1 ∨ c.Cg = 2
  dial_mem : c.dial ∈ Ioo (0 : ℝ) 1
structure BlockingFactorFloors (N : ExternalConstants) (c : InitialChoice) (o : ℝ) (L : ℕ) : Prop where
  floor_eleven : 11 < L
  enlargement_floor : (1 + 7 * c.βs) * (L : ℝ) ^ (-2 : ℤ) ≤ 1
  square_floor : 2 * (1 + c.βs) * (1 + c.β₀) ^ 2 / (1 - c.βs / 8) ≤ (L : ℝ) ^ 2
  width_floor : 4 * c.rStar ≤ (L : ℝ)
  o_floor : 1 ≤ o * (L : ℝ)
  absolute_floor : N.blockFloor ≤ (L : ℝ)
structure ScaleConstraints (T : DerivedConstants) (N : ExternalConstants) (c : ChoiceUpToCubes) : Prop where
  L_odd : Odd c.L
  L_floors : BlockingFactorFloors N c.toInitialChoice T.o c.L
  L₀_floors : ∀ L : ℕ, T.L₀ c.toInitialChoice ≤ L →
    BlockingFactorFloors N c.toInitialChoice T.o L
  αHat_mem : c.αHat ∈ Ioo (1 / 2 : ℝ) 1
  ϑ₂_mem : c.ϑ₂ ∈ Ioo ((c.L : ℝ) ^ (-(2 * c.αHat - 1))) 1
  LFlat_floor : 2 ≤ c.LFlat
  LFlat_half : (c.LFlat : ℝ) < 1 / 2 * (c.L : ℝ)
  LFlat_square : (c.LFlat : ℝ) ^ 2 ≤ 1 / 3 * (c.L : ℝ)
  blockNumber_power : IsPositivePowerOf c.L c.blockNumber
  blockNumber_floor : T.M₁Thr c.L ≤ (c.blockNumber : ℝ)
  blockNumber_propagators : N.propagatorFloor c.L ≤ (c.blockNumber : ℝ)
  blockNumber_decay : N.decayBlockFloor c.L ≤ (c.blockNumber : ℝ)
  gapNumber_decay : N.decayProductFloor c.L ≤ (c.gapNumber : ℝ) * (c.blockNumber : ℝ)
  gapNumber_power : IsPositivePowerOf c.L c.gapNumber
  gapNumber_floor : c.L ≤ c.gapNumber
  gapNumber_product : N.productFloor c.L ≤ (c.gapNumber : ℝ) * (c.blockNumber : ℝ)
  εv_lower : T.B₃ c.L * firstRadiusScaled T c.L c.blockNumber c.gapNumber ≤ c.εv
  εv_upper : c.εv + 3 / 2 * c.εv ^ 2 ≤ variationalRadius T c.L c.blockNumber c.gapNumber
  εv_smoothing : 2 * c.εv ≤ Averaging.smoothingRadius c.L
  εBar_le_firstRadius : c.εBar ≤ firstRadius T c.L c.blockNumber c.gapNumber
  B₃_mul_εBar_le_εv : T.B₃ c.L * c.εBar ≤ c.εv
  εBar_le_εBarG : c.εBar ≤ T.εBarG c.L c.blockNumber c.gapNumber
structure DecayRateConstraints (N : ExternalConstants) (c : ChoiceUpToCubes) : Prop where
  κ_floor_log : 10 * Real.log (c.L : ℝ) + 1 ≤ c.κ
  κ_floor_width : N.Cδ / windowWidth c.rStar c.L ≤ c.κ
  κ_floor_theorem : N.κThreshold c.L ≤ c.κ
  κ_floor_summability : summabilityThreshold ≤ c.κ
  κ_floor_five : 5 ≤ c.κ
  κ_floor_half : 3 ^ (2 ^ (spacetimeDim + 1) * spacetimeDim) * Real.exp (-c.κ / 2) ≤ 1 / 2
  κ_floor_enlargement :
    3 ^ (2 ^ (spacetimeDim + 1) * spacetimeDim) * Real.exp (-(c.βs * c.κ / 16)) ≤ 1 / 2
  κ_floor_remainder : N.remainderConst c.L ≤ Real.exp (1 / 2 * c.βs * c.κ)
  κ_floor_domains : 32 * Real.log 80 + 1 ≤ c.κ
  rateFraction_lt : N.rateFraction < 1 / 2
  κ_floor_localised : N.κAnalytic / (1 - 2 * N.rateFraction) ≤ c.κ
  islandFraction_pos : 0 < N.islandFraction
  κ_floor_islands :
    2 * (rarityConstant + 5 ^ spacetimeDim + Real.log 2) / N.islandFraction ≤ c.κ
  κ₁_floor_half : 2 * (c.L : ℝ) * c.κ ≤ 1 / 2 * (c.κ₁ - 1)
  κ₁_floor_sixteen : 16 * c.κ + 1 ≤ c.κ₁
  κ₁_floor_four : 4 * (c.L : ℝ) * c.κ + 1 ≤ c.κ₁
def ResponseFloor (T : DerivedConstants) (c : ChoiceUpToCubes) (m : ℕ) : Prop :=
  22 * (spacetimeDim : ℝ) ^ 2 * T.B₃ c.L *
      Real.exp (-(2 * responseRate T c.L * (c.L : ℝ) ^ 2 * (m : ℝ))) < 1 / 10 * c.βs
structure CubeConstraints (T : DerivedConstants) (N : ExternalConstants) (c : ChoiceUpToCubes) : Prop where
  M₁_power : IsPositivePowerOf c.L c.M₁
  M₁_floor : T.M₁Thr c.L ≤ (c.M₁ : ℝ)
  M₁_product : c.gapNumber * c.blockNumber ≤ c.M₁
  M₁_kernel : N.cBar * c.κ₁ ≤ T.δ₁Ring c.L * (c.M₁ : ℝ)
  M₁_determinant : N.determinantFloor c.L ≤ (c.M₁ : ℝ)
  M₁_response : ResponseFloor T c c.M₁
  M₁_path_count : 3 * Real.log (c.L : ℝ) + Real.log 2 ≤ 1 / 32 * N.decayConst c.L * ((c.M₁ : ℝ) - 1)
  M₁_decoupling : 8 * Real.log (expAbsSum (T.δ₀Ring c.L / 32)) + Real.log 16 ≤
    1 / 32 * T.δ₀Ring c.L * ((c.M₁ : ℝ) - 2)
  M₁_chart : N.chartFloor c.L ≤ ((c.L : ℝ) - 2) * (c.M₁ : ℝ)
  M₁Sharp_floor : 5 * (c.L : ℝ) * (c.M₁ : ℝ) ≤ c.M₁Sharp
  Θ₁_floor : 1 ≤ c.Θ₁
  ϖT_pos : 1 ≤ c.ϖT
  rPrime_power : IsPositivePowerOf c.L c.rPrime
  ℓa_power : IsPositivePowerOf c.L c.ℓa
  cHat_pos : 0 < c.cHat
  cubeSizeConst_floor : N.theoremBFloor c.L T.flowConstB ≤ c.cubeSizeConst
structure PartitionCubeConstraints (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCubes) : Prop where
  M_power : ∃ m' : ℕ, c.M = c.L ^ m'
  M_floor_cube : (c.L : ℝ) ^ 3 * (c.M₁ : ℝ) ≤ (c.M : ℝ)
  M_floor_fourth : (c.L : ℝ) ^ 4 * (c.M₁ : ℝ) ≤ (c.M : ℝ)
  M_floor_multiples : max (max (21 * (c.L : ℝ)) (80 * (c.L : ℝ)))
      (max (120 * (c.L : ℝ)) (N.cubeFloorConst * (c.L : ℝ))) * (c.M₁ : ℝ) ≤ (c.M : ℝ)
  M_floor_gap : 4 * (c.L : ℝ) * (c.gapNumber : ℝ) * (c.M₁ : ℝ) ≤ (c.M : ℝ)
  M_floor_gap_sixteen : 16 * ((c.gapNumber : ℝ) + 1) * (c.M₁ : ℝ) ≤ (c.M : ℝ)
  M_floor_rate_L : 16 * (c.L : ℝ) * c.κ₁ ≤ T.δ₁Ring c.L * (c.M : ℝ)
  M_floor_rate : c.κ₁ ≤ T.δ₁Ring c.L * (c.M : ℝ)
  M_floor_theorem : N.MOfκ c.L c.κ ≤ (c.M : ℝ)
  M_floor_κ : c.κ ≤ T.δ₀Ring c.L * (c.M : ℝ)
  M_floor_exponential : Real.exp (-(T.δ₀Ring c.L * (c.M : ℝ) / 3)) * Real.exp (16 * c.κ₁) < 1
  M_floor_collar : max (c.ϖT : ℝ) 3 ≤ (c.M : ℝ)
  M_floor_μ₀ : 2 * c.κ₁ ≤ T.μ₀ c.L c.M₁ * (c.M : ℝ)
  M_floor_δW : 2 * c.κ₁ ≤ T.δW c.L c.M₁ * (c.M : ℝ)
  M_floor_δW_five : 5 ≤ T.δW c.L c.M₁ * (c.M : ℝ)
  M_floor_δW_log : 32 * c.κ₁ + 2 * Real.log ((c.L : ℝ) * (c.M : ℝ)) + N.logFloorConst c.L ≤
    T.δW c.L c.M₁ * (c.M : ℝ) / 4
  M_floor_ratio : 4 * Real.log (c.L : ℝ) + 1 ≤ T.δ₀Ring c.L * (c.M : ℝ) / (32 * (c.M₁ : ℝ))
  collarRatio_floor_κ : 4 / 3 * ((2 * c.κ + 2) * (101 * (spacetimeDim : ℝ)) + 1) ≤
    collarRatio T c.L c.M c.M₁
  collarRatio_floor_log : 11 * Real.log (2 * (c.L : ℝ) ^ spacetimeDim) ≤ collarRatio T c.L c.M c.M₁
  M_floor_response : 2 * (c.M₁ : ℝ) ≤ responseRate T c.L * (c.M : ℝ)
  M_floor_last_term : N.lastTermConst c.L * T.B₃ c.L * T.B₅ c.L c.blockNumber c.gapNumber * (c.M : ℝ) ^ 5 *
    Real.exp (-(4 * responseRate T c.L * (c.M : ℝ))) < 1 / 12
  M_floor_threshold : N.MThreshold c.L ≤ (c.M : ℝ)
  M_floor_large_field : N.largeFieldCubeFloor c.eraseM ≤ (c.M : ℝ)
structure ConstantConstraints (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToRadii) : Prop where
  A₁_pos : 0 < c.A₁
  ratio_floor_B₃ : N.ratioConst * (1 + c.β₀) * T.B₃ c.L * (c.L : ℝ) ^ (spacetimeDim + 2) ≤ c.A₀ / c.A₁
  ratio_floor_M : N.ratioConstM c.L * (c.M : ℝ) ^ 2 ≤ c.A₀ / c.A₁
  ratio_floor_L : 64 * (c.L : ℝ) ^ 4 ≤ c.A₀ / c.A₁
  C₁Fl_floor : 1 ≤ T.C₁Fl c.toChoiceUpToDegreeConstants
  C₀_floor : N.C₀Multiple c.L * max c.A₀ c.A₁ ≤ c.C₀
  C₁_floor : 2 * T.B₃ c.L ^ 2 * T.cubeSizeOrderConst * (c.M : ℝ) * c.C₀ < c.C₁
  α₁_LM : ((c.L : ℝ) * (c.M : ℝ)) ^ 4 * c.α₁ ≤ 1
  α₁_enlargement : T.cubeSizeOrderConst * (c.M : ℝ) * c.α₁ ≤ c.βs
  α₁_radiusCeilingC : c.α₁ ≤ T.radiusCeilingC c.L c.blockNumber c.gapNumber
  α₁_aPr : c.α₁ ≤ T.aPr c.L c.blockNumber c.gapNumber
  α₁_primedCeiling : c.α₁ ≤ primedCeilingOne T c.L c.blockNumber c.gapNumber
  α₁_half_min : c.α₁ ≤ 1 / 2 * min (T.c₁ c.L c.blockNumber c.gapNumber) (min (T.aR c.L c.blockNumber c.gapNumber)
    (min (((c.L : ℝ) * (c.M : ℝ)) ^ (-4 : ℤ) * T.radiusCeilingComplex c.L c.blockNumber c.gapNumber)
      (min (((c.L : ℝ) * (c.M : ℝ)) ^ (-4 : ℤ) * T.aUpperW c.L c.blockNumber c.gapNumber) (T.aLowerW c.L c.blockNumber c.gapNumber / (c.M₁ : ℝ)))))
  α₁_theorem : c.α₁ ≤ N.α₁Ceiling c.eraseα₁
  α₀_LM : ((c.L : ℝ) * (c.M : ℝ)) ^ 4 * c.α₀ ≤ 1
  α₀_half_α₁ : T.B₃ c.L ^ 2 * T.cubeSizeOrderConst * (c.M : ℝ) * c.α₀ < 1 / 2 * c.α₁
  α₀_enlargement : (4 * T.B₃ c.L ^ 2 * T.cubeSizeOrderConst * (c.M : ℝ)) ^ 2 * c.α₀ ≤ c.βs
  α₀_radiusCeilingC : c.α₀ ≤ T.radiusCeilingC c.L c.blockNumber c.gapNumber
  α₀_aPr : c.α₀ ≤ T.aPr c.L c.blockNumber c.gapNumber
  α₀_aPos : c.α₀ ≤ T.aPos c.L c.blockNumber c.gapNumber
  α₀_primedCeiling : c.α₀ ≤ primedCeilingZero T c.L c.blockNumber c.gapNumber
  α₀_c₁ : c.α₀ ≤ T.c₁ c.L c.blockNumber c.gapNumber - c.α₁
  α₀_aR : c.α₀ ≤ T.aR c.L c.blockNumber c.gapNumber - c.α₁
  α₀_radiusCeilingComplex : c.α₀ ≤ ((c.L : ℝ) * (c.M : ℝ)) ^ (-4 : ℤ) * T.radiusCeilingComplex c.L c.blockNumber c.gapNumber - c.α₁
  α₀_aUpperW : c.α₀ ≤ ((c.L : ℝ) * (c.M : ℝ)) ^ (-4 : ℤ) * T.aUpperW c.L c.blockNumber c.gapNumber - c.α₁
  α₀_aLowerW : c.α₀ ≤ 1 / 2 * (T.aLowerW c.L c.blockNumber c.gapNumber / (c.M₁ : ℝ) - c.α₁)
  α₀_theorem : c.α₀ ≤ N.α₀Ceiling c.eraseα₀
  α₁Prime_le_α₁ : c.α₁Prime ≤ c.α₁
  α₁Prime_radiusCeilingComplex : c.α₁Prime ≤ 1 / 2 * T.radiusCeilingComplex c.L c.blockNumber c.gapNumber
  α₁Prime_square : T.complexPairConst c.L c.blockNumber c.gapNumber * c.α₁Prime ^ 2 ≤ 1 / 4 * c.α₀
  α₁Prime_primedCeiling : c.α₁Prime ≤ primedCeilingOne T c.L c.blockNumber c.gapNumber
  α₀Prime_square : T.complexPairConst c.L c.blockNumber c.gapNumber * c.α₀Prime ≤ c.α₀ - T.complexPairConst c.L c.blockNumber c.gapNumber * c.α₁Prime ^ 2
  α₀Prime_le_α₀ : c.α₀Prime ≤ c.α₀
  α₀Prime_radiusCeilingComplex : c.α₀Prime ≤ T.radiusCeilingComplex c.L c.blockNumber c.gapNumber - c.α₁Prime
  α₀Prime_primedCeiling : c.α₀Prime ≤ primedCeilingZero T c.L c.blockNumber c.gapNumber
  α₂_eighth : c.α₂ ≤ c.α₁ / 8
  α₂_α₀ : c.α₂ ≤ c.α₀ / N.α₂Const c.L
  α₃_α₁ : T.B₃ c.L * c.α₃ < 1 / 2 * c.α₁
  α₃_α₀ : 2 * T.B₃ c.L * c.α₃ ≤ c.βs * (c.L : ℝ) ^ (-2 : ℤ) * c.α₀
  E₀_floor : 2 * N.E₀Normaliser c.L ≤ c.E₀
  α₄_LM : ((c.L : ℝ) * (c.M : ℝ)) ^ 4 * c.α₄ ≤ 1
  θc_mem : c.θc ∈ Ioo (0 : ℝ) 1
  M₀_floor : N.potentialConst * T.B₅ c.L c.blockNumber c.gapNumber * (c.M : ℝ) ^ 6 < c.M₀
  εI₀_ceiling : c.εI₀ ≤ N.ε₀Ceiling c.eraseεI₀
  εI₁_ceiling : c.εI₁ ≤ N.ε₁Ceiling c.eraseεI₁
  εI₁_remainder : c.εI₁ ≤ oneLoopCoefficient c.L / (2 * N.CRem c.eraseεI₁)
  Cβ_nonneg : 0 ≤ T.Cβ c
  CPrime_pos : 0 < T.CPrime c
structure PreparatoryConstraints (c : ChoiceUpToCoupling) : Prop where
  CN_floor : 1 ≤ c.CN
  CV_floor : 1 ≤ c.CV
  KA_floor : 1 ≤ c.KA
  CL_floor : 1 ≤ c.CL
  κ₂_floor : 1 ≤ c.κ₂
  Cn_floor : 1 ≤ c.Cn
  CN_floor_L : (c.L : ℝ) ≤ c.CN
  Kϑ_pos : 0 < c.Kϑ
  CStar_pos : 0 < c.CStar
  cJ_nonneg : 0 ≤ c.cJ
structure CouplingConstraints (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) : Prop where
  γ_c₂ : c.γ ≤ (8 * T.c₂ c.L + 4) ^ (-(1 / 2) : ℝ)
  γ_margin : T.CPrime c.toChoiceUpToRadii * c.γ ^ (c.κ₀ - 8) ≤ min (oneLoopCoefficient c.L / 4) 1
  γ_Cβ : (T.Cβ c.toChoiceUpToRadii + 1) * c.γ ^ 2 ≤ 1
  γ_c₅ : 2 * doubledFiniteCoefficient T c.L * c.γ ^ 2 ≤ 1
  γ_c₂_β₀ : 2 * T.c₂ c.L * c.γ ^ 2 ≤ 1 - (1 + c.β₀) ^ (-2 : ℤ)
  radius_zero : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => c.C₀ * x ^ (-(1 / 2) : ℝ) * Real.log x ^ c.q) c.α₀
  radius_one : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => c.C₁ * x ^ (-(1 / 2) : ℝ) * Real.log x ^ c.q) c.α₁
  threshold_firstRadius : SupFromLE (c.γ ^ (-2 : ℤ))
    (fun x => T.cubeSizeOrderConst * (c.L : ℝ) * (c.M : ℝ) * smallFieldThreshold c.toChoiceUpToDegreeConstants x)
    ((c.gapNumber : ℝ) * (c.M₁ : ℝ) * firstRadius T c.L c.blockNumber c.gapNumber)
  cube_size_A₁ : SupFromLT (c.γ ^ (-2 : ℤ)) (fun x => T.cubeSizeOrderConst * c.A₀ * Real.exp (-blockSizeReal c.toChoiceUpToCubes x))
    (1 / 3 * c.A₁)
  threshold_firstRadiusScaled : SupFromLE (c.γ ^ (-2 : ℤ)) (smallFieldThreshold c.toChoiceUpToDegreeConstants)
    (firstRadiusScaled T c.L c.blockNumber c.gapNumber)
  γ_theorem : c.γ ≤ N.couplingCeiling c.eraseγ
  cutoff_ceilings : ∀ p ∈ N.cutoffCeilings, (p c.eraseγ).HoldsAt c.γ
  γ_normaliser : c.γ ≤ N.normaliserCeiling c.A₀ c.𝔭₀
  preparatory_one : SupFromLE (shiftedInverseSq T c) (N.preparatoryFunctionOne c.eraseγ) (1 / 4)
  preparatory_two : SupFromLE (shiftedInverseSq T c) (N.preparatoryFunctionTwo c.eraseγ) 1
  preparatory_triple : Real.exp 1 ≤ (2 + T.Cβ c.toChoiceUpToRadii) * shiftedInverseSq T c
  shiftedInverseSq_floor : max (Real.exp 2) (2 * doubledFiniteCoefficient T c.L) ≤ shiftedInverseSq T c
  ratio_first : SupFromLT (c.γ ^ (-2 : ℤ)) (fun x => N.CFirst c.L * (c.A₁ / c.A₀) * logRatio c.toInitialChoice x) 1
  ratio_second : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => 4 * N.CSecond c.L * (c.L : ℝ) * T.B₃ c.L * logRatio c.toInitialChoice x) (1 / 4)
  decay_second : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => 44 * (spacetimeDim : ℝ) ^ 2 * N.CSecond c.L * (c.L : ℝ) * T.B₃ c.L *
    (1 + c.β₀) * (c.A₀ / c.A₁) *
      Real.exp (-(responseRate T c.L * (c.M : ℝ) * blockSizeReal c.toChoiceUpToCubes x))) (1 / 4)
  decay_third : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => 22 * (spacetimeDim : ℝ) ^ 2 * N.CSecond c.L * T.B₃ c.L * (1 + c.β₀) *
    (c.A₀ / c.A₁) * Real.exp (-(responseRate T c.L * (c.L : ℝ) * (secondCubeSize c.L c.M₁ : ℝ) *
      blockSizeReal c.toChoiceUpToCubes x))) (1 / 2)
  ratio_three_quarters : SupFromLT (c.γ ^ (-2 : ℤ)) (fun x => logRatio c.toInitialChoice x) (3 / 4)
  ratio_enlargement : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => 9 * T.B₃ c.L * (1 + c.β₀) * (c.A₁ / c.A₀) * logRatio c.toInitialChoice x)
    (1 / 8 * c.βs)
  threshold_enlargement : SupFromLE (c.γ ^ (-2 : ℤ))
    (fun x => 8 * T.B₃ c.L * c.A₁ * x ^ (-(1 / 2) : ℝ) * Real.log x ^ c.𝔭₁) (1 / 8 * c.βs)
  decay_twelfth : SupFromLT (c.γ ^ (-2 : ℤ)) (fun x => 23 * (spacetimeDim : ℝ) ^ 2 * T.B₃ c.L * (1 + c.β₀) ^ 2 *
    Real.exp (-blockSizeReal c.toChoiceUpToCubes x)) (1 / 12)
  waiting_depth_first : SupFromLT (c.γ ^ (-2 : ℤ)) (fun x => T.B₃ c.L * (1 + c.β₀) *
    (1 + (c.L : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ ((c.r : ℝ) / 2)) * (c.A₁ / c.A₀) * logRatio c.toInitialChoice x) (1 / 24)
  waiting_depth_second : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => N.CThird c.L * T.B₃ c.L ^ 3 *
    T.B₅ c.L c.blockNumber c.gapNumber * (c.M : ℝ) ^ 6 * ((c.L : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ ((c.r : ℝ) / 2)) *
      (c.L : ℝ) ^ (-(Real.log x ^ c.r))) (1 / 24)
  profile : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => N.CBar c.L * T.B₃ c.L * T.B₅ c.L c.blockNumber c.gapNumber * (c.M : ℝ) ^ 5 *
    (c.LFlat : ℝ) ^ 2 * (blockSizeReal c.toChoiceUpToCubes x) ^
      (-(2 * Real.log (c.LFlat : ℝ) / Real.log (c.L : ℝ)))) (1 / 4)
  waiting_depth_third : SupFromLE (c.γ ^ (-2 : ℤ)) (fun x => N.CCheck c.L * T.B₃ c.L * T.B₅ c.L c.blockNumber c.gapNumber * (c.M : ℝ) ^ 5 *
    (1 + c.β₀) * ((c.L : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ ((c.r : ℝ) / 2)) * (c.L : ℝ) ^ (-(2 * Real.log x ^ c.r))) 1
  γ_large_field : c.γ ≤ N.γLargeField c.eraseγ
  γH_ceiling : c.γH ≤ (c.γ ^ (-2 : ℤ) + doubledFiniteCoefficient T c.L + 1) ^ (-(1 / 2) : ℝ)
  inverseSqAtHigh_floor : max (2 * (T.Cβ c.toChoiceUpToRadii + 1))
    (Real.exp (Real.log 2 / ((c.L : ℝ) ^ (1 / (c.r : ℝ)) - 1))) ≤ inverseSqAtHigh c
  inverseSqAtHigh_sup : SupFromLE (inverseSqAtHigh c) (fun x => (T.Cβ c.toChoiceUpToRadii + 1) * ((c.L : ℝ) * Real.log x ^ c.r + 1) / x) 1
structure RangesUpToCoupling (T : DerivedConstants) (c : ChoiceUpToCoupling) : Prop where
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
  M_power : ∃ m' : ℕ, c.M = c.L ^ m'
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
structure ChosenUpToCoupling (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) : Prop where
  ranges : RangesUpToCoupling T c
  constants_mem : ExternalConstantsInRange N c
  initial : InitialConstraints c.toInitialChoice
  scales : ScaleConstraints T N c.toChoiceUpToCubes
  decayRates : DecayRateConstraints N c.toChoiceUpToCubes
  cubes : CubeConstraints T N c.toChoiceUpToCubes
  partitionCubes : PartitionCubeConstraints T N c.toChoiceUpToCubes
  constants : ConstantConstraints T N c.toChoiceUpToRadii
  preparatory : PreparatoryConstraints c
  couplings : CouplingConstraints T N c
def SourceRadiusPos (ϱ : ℝ) : Prop := 0 < ϱ
def SourceRadiusGeSixWidths (T : DerivedConstants) (c : ChoiceUpToCoupling) (ϱ : ℝ) :
    Prop :=
  6 * (FlowConstants.widthSharp T c + 1) ≤ ϱ
def SourceRadiusGeFiniteFlow (T : DerivedConstants) (L : ℕ) (ϱ : ℝ) : Prop :=
  48 * T.c₂ L ≤ ϱ
def SourceRadiusGeWidth (T : DerivedConstants) (c : ChoiceUpToCoupling) (ϱ : ℝ) :
    Prop :=
  FlowConstants.widthSharp T c + 1 ≤ ϱ
def SourceRadiusGeGrowth (N : ExternalConstants) (c : ChoiceUpToCoupling) (ϱ : ℝ) : Prop :=
  4 * N.αBar c ≤ 1 / 2 * ϱ
structure SourceRadiusFloors (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) (ϱ : ℝ) : Prop where
  sixFlowWidths : SourceRadiusGeSixWidths T c ϱ
  finiteFlowPart : SourceRadiusGeFiniteFlow T c.L ϱ
  flowWidth : SourceRadiusGeWidth T c ϱ
  growthNumber : SourceRadiusGeGrowth N c ϱ
structure AgeConstantFloors (c : ChoiceUpToCoupling) (ca : ℝ) : Prop where
  ca_pos : 0 < ca
  ca_floor_histories : 17 * Real.log (c.L : ℝ) + Real.log 2 ≤ ca
  ca_floor_rotations : 32 * Real.log (2 * (c.L : ℝ) / c.ϑ₂) ≤ ca
  ca_floor_rarity :
    2 ^ spacetimeDim * ((16 + (spacetimeDim : ℝ)) * Real.log (c.L : ℝ) + Real.log 2) ≤ ca
structure SourceThresholdBounds (T : DerivedConstants) (c : ChoiceUpToCoupling) (ϱ : ℝ) :
    Prop where
  γAPrime_mem : T.γAPrime c ϱ ∈ Ioc (0 : ℝ) c.γH
  γAPrime_c₂ : T.γAPrime c ϱ ≤ (8 * T.c₂ c.L + 4) ^ (-(1 / 2) : ℝ)
structure CorrelationThresholdCeilings (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) (ϱ γJ : ℝ) : Prop where
  γVolOne_mem : N.γVolOne c ϱ ∈ Ioc (0 : ℝ) (T.γAPrime c ϱ)
  γVolTwo_mem : N.γVolTwo c ϱ ∈ Ioc (0 : ℝ) (T.γAPrime c ϱ)
  γJ_pos : 0 < γJ
  γJ_le_γH : γJ ≤ c.γH
  γJ_le_γAPrime : γJ ≤ T.γAPrime c ϱ
  γJ_c₂ : γJ ≤ (8 * T.c₂ c.L + 4) ^ (-(1 / 2) : ℝ)
  γJ_volume_one : γJ ≤ N.γVolOne c ϱ
  γJ_volume_two : γJ ≤ N.γVolTwo c ϱ
structure SourceAndCorrelationThresholds (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) (ϱ γJ : ℝ) : Prop
    extends SourceThresholdBounds T c ϱ, CorrelationThresholdCeilings T N c ϱ γJ
structure AnchorCeilings (N : ExternalConstants) (B₃ : ℕ → ℝ) (c : ChoiceUpToCoupling)
    (ca γJ γ'' : ℝ) : Prop where
  healed : γ'' ≤ min (N.γF c ca) (min (N.γh c ca) (N.γM c.dial c ca))
  never_healed : ∀ i, (N.neverHealedCeilings i c).HoldsAt γ''
  flow : γ'' ≤ N.γF c ca
  moment_zero : γ'' ≤ N.γMAge c ca γJ
  w : γ'' ≤ N.γw c ca γJ
  wd : γ'' ≤ N.γwd c ca γJ
  wm : γ'' ≤ N.γwm c ca γJ
  hl : γ'' ≤ N.γhl c ca γJ
  sharp : γ'' ≤ N.γSharp c ca γJ
  radius : γ'' ≤ min γJ (N.Xϱ c.A₀ c.𝔭₀ (B₃ c.L) N.ϱPr ^ (-(1 / 2) : ℝ))
  𝔪 : γ'' ≤ N.γ𝔪 c ca γJ
  age : γ'' ≤ N.γTAge N.εStar c ca γJ
  chessboard : γ'' ≤ N.γTChessboard N.εStar c ca
def anchorCouplingSet (N : ExternalConstants) (B₃ : ℕ → ℝ) (c : ChoiceUpToCoupling) (ca γJ : ℝ) :
    Set ℝ :=
  {γ' | γ' ∈ Ioc (0 : ℝ) γJ ∧ ∀ γ'' ∈ Ioc (0 : ℝ) γ', AnchorCeilings N B₃ c ca γJ γ''}
structure AnchorCouplingEqHalfSup (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) (ca γJ : ℝ) : Prop where
  γF_pos : 0 < N.γF c ca
  γh_pos : 0 < N.γh c ca
  γM_pos : 0 < N.γM c.dial c ca
  neverHealedCeilings_wellFormed : ∀ i, (N.neverHealedCeilings i c).IsWellFormed
  γMAge_mem : N.γMAge c ca γJ ∈ Ioc (0 : ℝ) γJ
  γw_mem : N.γw c ca γJ ∈ Ioc (0 : ℝ) γJ
  γwd_mem : N.γwd c ca γJ ∈ Ioc (0 : ℝ) γJ
  γwm_mem : N.γwm c ca γJ ∈ Ioc (0 : ℝ) γJ
  γhl_mem : N.γhl c ca γJ ∈ Ioc (0 : ℝ) γJ
  γSharp_mem : N.γSharp c ca γJ ∈ Ioc (0 : ℝ) γJ
  ϱPr_pos : 0 < N.ϱPr
  γ𝔪_mem : N.γ𝔪 c ca γJ ∈ Ioc (0 : ℝ) γJ
  γTAge_mem : N.γTAge N.εStar c ca γJ ∈ Ioc (0 : ℝ) γJ
  γTChessboard_pos : 0 < N.γTChessboard N.εStar c ca
  γStar_eq : T.γStar c ca γJ = 1 / 2 * sSup (anchorCouplingSet N T.B₃ c ca γJ)
structure DisplayedThresholdCeilings (N : ExternalConstants) (c : ChoiceUpToCoupling)
    (γJ γU γUPrime : ℝ) : Prop where
  γUPrime_pos : 0 < γUPrime
  γU_le_γJ : γU ≤ γJ
  γUPrime_le_γU : γUPrime ≤ γU
  γUPrime_power : N.Cϖ c * γUPrime ^ (c.κ₀ - 6) ≤ 1
def ShapeConstantInRange (T : DerivedConstants) : Prop := T.ϑ₀ ∈ Ioc (0 : ℝ) 1
def ShapeParameterInRange (ϑ : ℝ) : Prop := ϑ ∈ Ioc (0 : ℝ) 1
structure RoomConstantAndLevel (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) (ϱ ca : ℝ) : Prop where
  one_le_fourPointRoomThreshold : ∀ t ∈ Ioc (0 : ℝ) 1, 1 ≤ N.fourPointRoomThreshold t c ϱ ca
  CE0_floor : ∀ t ∈ Ioc (0 : ℝ) 1, 1 ≤ N.CE0 t c ϱ ca
  CW0_eq : ∀ t ∈ Ioc (0 : ℝ) 1, T.CW0 t c ϱ ca =
    max (N.CW0TwoPoint t c ϱ ca) (max (N.fourPointRoomThreshold t c ϱ ca) (N.CE0 t c ϱ ca))
  CW0_floor : ∀ t ∈ Ioc (0 : ℝ) 1, 1 ≤ T.CW0 t c ϱ ca * c.A₀ ^ 2
  kW_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 1 ≤ T.kW t c ϱ ca
structure ShapeThresholdCeilings (T : DerivedConstants) (N : ExternalConstants)
    (c : FullChoice) : Prop where
  γTwoPoint_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < N.γTwoPoint t c.toChoiceUpToCoupling c.ϱ c.ca
  γFourPoint_mem : ∀ t ∈ Ioc (0 : ℝ) 1,
    N.γFourPoint t c.toChoiceUpToCoupling c.ϱ c.ca c.γJ ∈
      Ioc (0 : ℝ) (min (T.γAPrime c.toChoiceUpToCoupling c.ϱ)
        (T.γStar c.toChoiceUpToCoupling c.ca c.γJ))
  uniformCeiling_wellFormed : ∀ t ∈ Ioc (0 : ℝ) 1, (N.uniformCeiling (c.atShape t)).IsWellFormed
  γW_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < c.γW t
  γW_le_γJ : ∀ t ∈ Ioc (0 : ℝ) 1, c.γW t ≤ c.γJ
  γW_two_point : ∀ t ∈ Ioc (0 : ℝ) 1, c.γW t ≤ N.γTwoPoint t c.toChoiceUpToCoupling c.ϱ c.ca
  γW_four_point : ∀ t ∈ Ioc (0 : ℝ) 1,
    c.γW t ≤ N.γFourPoint t c.toChoiceUpToCoupling c.ϱ c.ca c.γJ
  γW_uniform : ∀ t ∈ Ioc (0 : ℝ) 1, (N.uniformCeiling (c.atShape t)).HoldsAt (c.γW t)
structure ChoiceOrderConditions (T : DerivedConstants) (N : ExternalConstants)
    (c : FullChoice) : Prop
    extends ChosenUpToCoupling T N c.toChoiceUpToCoupling where
  admissible : IsAdmissible T c
  sourceRadius : SourceRadiusPos c.ϱ
  ageConstant : AgeConstantFloors c.toChoiceUpToCoupling c.ca
  thresholds : SourceAndCorrelationThresholds T N c.toChoiceUpToCoupling c.ϱ c.γJ
  anchorCoupling : AnchorCouplingEqHalfSup T N c.toChoiceUpToCoupling c.ca c.γJ
  displayedThresholds :
    DisplayedThresholdCeilings N c.toChoiceUpToCoupling c.γJ c.γU c.γUPrime
  shapeConstant : ShapeConstantInRange T
  shapeParameter : ShapeParameterInRange c.ϑ
  roomConstant : RoomConstantAndLevel T N c.toChoiceUpToCoupling c.ϱ c.ca
  shapeThreshold : ShapeThresholdCeilings T N c
def BlockingFactorCondition (T : DerivedConstants) (c : ChoiceUpToCubes) : Prop :=
  Odd c.L ∧ T.L₀ c.toInitialChoice ≤ c.L
end YangMills.Construction.ParameterChoice
end
