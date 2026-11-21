import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.ParameterChoice
def BlockingFactorAdmissible (L : ℕ) : Prop := Odd L ∧ 13 ≤ L
structure AdmissibleBeforeCubeSize (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCubes) : Prop where
  initial : InitialConstraints c.toInitialChoice
  L_ge : 13 ≤ c.L
  scales : ScaleConstraints T N c
  εv_pos : 0 < c.εv
  εBar_pos : 0 < c.εBar
  decayRates : DecayRateConstraints N c
  cubes : CubeConstraints T N c
  cubeSizeConst_pos : 0 < c.cubeSizeConst
  cHat_le : c.cHat ≤ 2
structure AdmissibleUpToCubeSize (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCubes) : Prop extends AdmissibleBeforeCubeSize T N c where
  partitionCubes : PartitionCubeConstraints T N c
structure AdmissibleUpToRatio (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToDegreeConstants) : Prop where
  upToCubes : AdmissibleUpToCubeSize T N c.toChoiceUpToCubes
  A₁_pos : 0 < c.A₁
  A₀_pos : 0 < c.A₀
  ratio_ge_B₃ :
    N.ratioConst * (1 + c.β₀) * T.B₃ c.L * (c.L : ℝ) ^ (spacetimeDim + 2) ≤ c.A₀ / c.A₁
  ratio_ge_M : N.ratioConstM c.L * (c.M : ℝ) ^ 2 ≤ c.A₀ / c.A₁
  ratio_ge_L : 64 * (c.L : ℝ) ^ 4 ≤ c.A₀ / c.A₁
structure AdmissibleBeforeRadii (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToRadii) : Prop where
  upToRatio : AdmissibleUpToRatio T N c.toChoiceUpToDegreeConstants
  one_le_C₁Fl : 1 ≤ T.C₁Fl c.toChoiceUpToDegreeConstants
  C₀_pos : 0 < c.C₀
  C₀_ge : N.C₀Multiple c.L * max c.A₀ c.A₁ ≤ c.C₀
  C₁_pos : 0 < c.C₁
  C₁_gt : 2 * T.B₃ c.L ^ 2 * T.cubeSizeOrderConst * (c.M : ℝ) * c.C₀ < c.C₁
structure RadiiAdmissible (c : ChoiceUpToRadii) : Prop where
  α₁_pos : 0 < c.α₁
  α₀_pos : 0 < c.α₀
  α₁Prime_pos : 0 < c.α₁Prime
  α₀Prime_pos : 0 < c.α₀Prime
  α₂_pos : 0 < c.α₂
  α₃_pos : 0 < c.α₃
  E₀_pos : 0 < c.E₀
  α₄_pos : 0 < c.α₄
  θc_mem : c.θc ∈ Ioo (0 : ℝ) 1
  M₀_pos : 0 < c.M₀
structure AdmissibleBeforeCoupling (T : DerivedConstants) (N : ExternalConstants)
    (c : ChoiceUpToCoupling) : Prop where
  beforeRadii : AdmissibleBeforeRadii T N c.toChoiceUpToRadii
  radii : RadiiAdmissible c.toChoiceUpToRadii
  εI₀_pos : 0 < c.εI₀
  εI₁_pos : 0 < c.εI₁
  εI₀_le : c.εI₀ ≤ 1
  εI₁_le : c.εI₁ ≤ 1
  constants : ConstantConstraints T N c.toChoiceUpToRadii
  preparatory : PreparatoryConstraints c
structure ExternalBeforeCouplingAdmissible (N : ExternalConstants) (c : ChoiceUpToCoupling) :
    Prop where
  couplingCeiling_pos : 0 < N.couplingCeiling c.eraseγ
  cutoffCeilings_wellFormed : ∀ p ∈ N.cutoffCeilings, (p c.eraseγ).IsWellFormed
  normaliserCeiling_pos : 0 < N.normaliserCeiling c.A₀ c.𝔭₀
  preparatoryFunctionOne_tendsto :
    Tendsto (N.preparatoryFunctionOne c.eraseγ) atTop (nhds 0)
  preparatoryFunctionTwo_tendsto :
    Tendsto (N.preparatoryFunctionTwo c.eraseγ) atTop (nhds 0)
  γLargeField_mem : N.γLargeField c.eraseγ ∈ Ioc (0 : ℝ) 1
structure BlockGapConstantsAdmissible (T : DerivedConstants) (L 𝔐 R₁ : ℕ) : Prop where
  B₁_pos : 0 < T.B₁ L 𝔐 R₁
  c₁_pos : 0 < T.c₁ L 𝔐 R₁
  B₅_pos : 0 < T.B₅ L 𝔐 R₁
  a₀_pos : 0 < T.a₀ L 𝔐 R₁
  a₁_pos : 0 < T.a₁ L 𝔐 R₁
  B₃_mul_a₁_le_a₀ : T.B₃ L * T.a₁ L 𝔐 R₁ ≤ T.a₀ L 𝔐 R₁
  εBarG_pos : 0 < T.εBarG L 𝔐 R₁
  rB_pos : 0 < T.rB L 𝔐 R₁
  radiusCeilingC_pos : 0 < T.radiusCeilingC L 𝔐 R₁
  aPr_pos : 0 < T.aPr L 𝔐 R₁
  aPos_pos : 0 < T.aPos L 𝔐 R₁
  aR_pos : 0 < T.aR L 𝔐 R₁
  radiusCeilingComplex_pos : 0 < T.radiusCeilingComplex L 𝔐 R₁
  aUpperW_pos : 0 < T.aUpperW L 𝔐 R₁
  aLowerW_pos : 0 < T.aLowerW L 𝔐 R₁
  complexPairConst_pos : 0 < T.complexPairConst L 𝔐 R₁
  radiusCeilingCommon_pos : 0 < T.radiusCeilingCommon L 𝔐 R₁
structure AdmissibleBeforeShapeThreshold (T : DerivedConstants) (N : ExternalConstants)
    (c : FullChoice) : Prop where
  chosen : ChosenUpToCoupling T N c.toChoiceUpToCoupling
  sourceRadius : SourceRadiusPos c.ϱ
  ageConstant : AgeConstantFloors c.toChoiceUpToCoupling c.ca
  thresholds : SourceAndCorrelationThresholds T N c.toChoiceUpToCoupling c.ϱ c.γJ
  anchorCoupling : AnchorCouplingEqHalfSup T N c.toChoiceUpToCoupling c.ca c.γJ
  displayedThresholds :
    DisplayedThresholdCeilings N c.toChoiceUpToCoupling c.γJ c.γU c.γUPrime
structure AdmissibleConstantFamily (T : DerivedConstants) (N : ExternalConstants) : Prop where
  blockingFactorFloors : ∀ s : InitialChoice, InitialConstraints s → ∀ L : ℕ, T.L₀ s ≤ L →
    BlockingFactorFloors N s T.o L
  c₂_nonneg : ∀ L, BlockingFactorAdmissible L → 0 ≤ T.c₂ L
  one_le_B₃ : ∀ L, BlockingFactorAdmissible L → 1 ≤ T.B₃ L
  δ₀Ring_pos : ∀ L, BlockingFactorAdmissible L → 0 < T.δ₀Ring L
  δ₁Ring_pos : ∀ L, BlockingFactorAdmissible L → 0 < T.δ₁Ring L
  decayConst_pos : ∀ L, BlockingFactorAdmissible L → 0 < N.decayConst L
  α₂Const_pos : ∀ L, BlockingFactorAdmissible L → 0 < N.α₂Const L
  rateFraction_lt : N.rateFraction < 1 / 2
  islandFraction_pos : 0 < N.islandFraction
  blockGap : ∀ L 𝔐 R₁, BlockingFactorAdmissible L → IsPositivePowerOf L 𝔐 →
    IsPositivePowerOf L R₁ → BlockGapConstantsAdmissible T L 𝔐 R₁
  δW_pos : ∀ L M₁, BlockingFactorAdmissible L → IsPositivePowerOf L M₁ → 0 < T.δW L M₁
  μ₀_pos : ∀ L M₁, BlockingFactorAdmissible L → IsPositivePowerOf L M₁ → 0 < T.μ₀ L M₁
  one_le_largeFieldCubeFloor : ∀ c, AdmissibleBeforeCubeSize T N c →
    1 ≤ N.largeFieldCubeFloor c.eraseM
  one_le_C₁Fl : ∀ c, AdmissibleUpToRatio T N c → 1 ≤ T.C₁Fl c
  α₁Ceiling_pos : ∀ c, AdmissibleBeforeRadii T N c → 0 < N.α₁Ceiling c.eraseα₁
  α₀Ceiling_pos : ∀ c, AdmissibleBeforeRadii T N c → 0 < c.α₁ → 0 < N.α₀Ceiling c.eraseα₀
  ε₀Ceiling_pos : ∀ c, AdmissibleBeforeRadii T N c → RadiiAdmissible c →
    0 < N.ε₀Ceiling c.eraseεI₀
  ε₁Ceiling_pos : ∀ c, AdmissibleBeforeRadii T N c → RadiiAdmissible c → 0 < c.εI₀ →
    0 < N.ε₁Ceiling c.eraseεI₁
  CRem_pos : ∀ c, AdmissibleBeforeRadii T N c → RadiiAdmissible c → 0 < c.εI₀ →
    0 < N.CRem c.eraseεI₁
  Cβ_nonneg : ∀ c, AdmissibleBeforeRadii T N c → RadiiAdmissible c → 0 < c.εI₀ → 0 < c.εI₁ →
    0 ≤ T.Cβ c
  CPrime_pos : ∀ c, AdmissibleBeforeRadii T N c → RadiiAdmissible c → 0 < c.εI₀ → 0 < c.εI₁ →
    0 < T.CPrime c
  beforeCoupling : ∀ c, AdmissibleBeforeCoupling T N c → ExternalBeforeCouplingAdmissible N c
  sourceThreshold : ∀ c ϱ, ChosenUpToCoupling T N c → 0 < ϱ →
    SourceThresholdBounds T c ϱ
  γVolOne_mem : ∀ c ϱ, ChosenUpToCoupling T N c → 0 < ϱ →
    N.γVolOne c ϱ ∈ Ioc (0 : ℝ) (T.γAPrime c ϱ)
  γVolTwo_mem : ∀ c ϱ, ChosenUpToCoupling T N c → 0 < ϱ →
    N.γVolTwo c ϱ ∈ Ioc (0 : ℝ) (T.γAPrime c ϱ)
  anchorCoupling : ∀ c ϱ ca γJ, ChosenUpToCoupling T N c → 0 < ϱ →
    AgeConstantFloors c ca → CorrelationThresholdCeilings T N c ϱ γJ →
    AnchorCouplingEqHalfSup T N c ca γJ
  Xϱ_pos : ∀ c, ChosenUpToCoupling T N c →
    0 < N.Xϱ c.A₀ c.𝔭₀ (T.B₃ c.L) N.ϱPr
  roomConstant : ∀ c ϱ ca, ChosenUpToCoupling T N c → 0 < ϱ →
    AgeConstantFloors c ca → RoomConstantAndLevel T N c ϱ ca
  shapeConstant : ShapeConstantInRange T
  γTwoPoint_pos : ∀ c, AdmissibleBeforeShapeThreshold T N c → ∀ t ∈ Ioc (0 : ℝ) 1,
    0 < N.γTwoPoint t c.toChoiceUpToCoupling c.ϱ c.ca
  γFourPoint_mem : ∀ c, AdmissibleBeforeShapeThreshold T N c → ∀ t ∈ Ioc (0 : ℝ) 1,
    N.γFourPoint t c.toChoiceUpToCoupling c.ϱ c.ca c.γJ ∈
      Ioc (0 : ℝ) (min (T.γAPrime c.toChoiceUpToCoupling c.ϱ)
        (T.γStar c.toChoiceUpToCoupling c.ca c.γJ))
  uniformCeiling_wellFormed : ∀ c, AdmissibleBeforeShapeThreshold T N c → ∀ t ∈ Ioc (0 : ℝ) 1,
    (N.uniformCeiling (c.atShape t)).IsWellFormed
end YangMills.Construction.ParameterChoice
end
