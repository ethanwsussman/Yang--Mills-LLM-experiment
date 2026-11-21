import YangMills.Construction.EffectiveAction.WholeLatticeFamiliesOfAStep
import YangMills.Construction.Lattice.FluctuationFormOfAStep
import YangMills.Construction.PolymerActivities.ExpansionOfAStepInVertices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K k : ℕ}
def smallFieldNormalizer (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  stepNormalizer c (pureStepData c 1 W)
def SmallFieldNormalizerPos (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : Prop :=
  IsHessianStep c (pureStepData c 1 W) ∧
    RealConstraintDefined (Averaging.smoothingRadius c.L) (basePoint c (pureStepData c 1 W))
      {e : BondAtLevel c.L m K (k + 1) | e.IsPositivelyOriented} ∧
    HessianFormDefined c (pureStepData c 1 W)
      (basePoint c (pureStepData c 1 W)) ∧
    IsHessianPosDef c (pureStepData c 1 W)
      (basePoint c (pureStepData c 1 W)) ∧
    0 < smallFieldNormalizer c W
def normalizerLogRatio (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  Real.log (smallFieldNormalizer c W) -
    Real.log (smallFieldNormalizer c (1 : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
def normalizerLogRatioDomain : Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) :=
  {W | SmallFieldNormalizerPos c W ∧
    SmallFieldNormalizerPos c (1 : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2)}
structure StepParameterSizes (N : ChoiceConstants c) (C : Fin 2 → ℝ) : Prop where
  two_le_r : 2 ≤ c.r
  A₀_pos : 0 < c.A₀
  A₁_pos : 0 < c.A₁
  𝔭₀_pos : 0 < c.𝔭₀
  κ_pos : 0 < c.κ
  κ₀_pos : 0 < c.κ₀
  regRadius_pos : 0 < N.regRadius
  regThreshold_pos : 0 < N.regThreshold
  towerRadius_pos : 0 < N.towerRadius
  cubeConst_pos : 0 < N.cubeConst
  gaugeBound_pos : 0 < N.gaugeBound
  layerGaugeBound_pos : 0 < N.layerGaugeBound
  constants_pos : ∀ i, 0 < C i
  q_pos : 0 < c.q
  blockExp_pos : 0 < N.blockExp
  gapExp_pos : 0 < N.gapExp
  sizeExp_pos : 0 < N.sizeExp
  block_eq_pow : c.L ^ N.blockExp = c.blockNumber
  gap_eq_pow : c.L ^ N.gapExp = c.gapNumber
  size_eq_pow : c.L ^ N.sizeExp = c.M₁
  cube_eq_pow : c.L ^ N.cubeExp = c.M
  gap_mul_block_le : c.gapNumber * c.blockNumber ≤ c.M₁
  size_le_cube : c.M₁ ≤ c.M
variable (K k)
def normalizerFunctional : EffectiveAction.TorusFunctional c.L K (k + 1) :=
  fun _ W => normalizerLogRatio c W
def oneLoopShift : ℝ :=
  EffectiveAction.torusStiffness c.L K (k + 1) (normalizerFunctional c K k)
structure TorusExpansions (x : ℕ → ℝ) (m' : ℕ) (C : Fin 2 → ℝ) (s : ActivityDomainKind) where
  sizes : EffectiveAction.TorusSizeData m'
  params : ℕ → ChoiceConstants c
  params_eq : ∀ n, (params n).toAnalyticityConstants = sizes.constants n
  completed : ∀ n : ℕ, CompletedSteps c.L n K
  expansion : ∀ n : ℕ, VertexExpansion c x (m := n) (K := K) (k := k) (params n) C s
    (completed n) (sizes.innerRadius n) (sizes.outerRadius n)
    (fun W => (normalizerLogRatio c W : ℂ)) (normalizerLogRatioDomain c)
  step_le : k + 1 ≤ K
  cubes_fit : ∀ n ∈ sizes.sizes, m' + (k + 1) ≤ n + K
  params_sizes : ∀ n ∈ sizes.sizes, StepParameterSizes c (params n) C
  innerRadius_pos : ∀ n ∈ sizes.sizes, 0 < sizes.innerRadius n
  outerRadius_pos : ∀ n ∈ sizes.sizes, 0 < sizes.outerRadius n
  absConvergent : ∀ n ∈ sizes.sizes, (expansion n).toVertexTerms.AbsConvergent univ
namespace TorusExpansions
variable {c K k} {x : ℕ → ℝ} {m' : ℕ} {C : Fin 2 → ℝ} {s : ActivityDomainKind}
variable (E : TorusExpansions c K k x m' C s)
def fullFamilies : EffectiveAction.TorusActivityFamily c.L K (k + 1) :=
  fun n => (E.expansion n).toVertexTerms.fullFamily
def markedFamilies : EffectiveAction.TorusActivityFamily c.L K (k + 1) :=
  fun n => (E.expansion n).toVertexTerms.markedFamily
def unmarkedFamilies : EffectiveAction.TorusActivityFamily c.L K (k + 1) :=
  fun n => (E.expansion n).toVertexTerms.unmarkedFamily
end TorusExpansions
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
