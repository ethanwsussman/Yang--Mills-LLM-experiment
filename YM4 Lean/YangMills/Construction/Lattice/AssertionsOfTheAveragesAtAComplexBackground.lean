import YangMills.Construction.Lattice.ExplicitFormOfAProductOfBlockMeans
import YangMills.Construction.Lattice.ExponentialActionAndComplexData
import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.NumbersOfTheAveragesNearARealConfiguration
import YangMills.Construction.Lattice.StraightenedAveragesOfAComplexConfiguration
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.Averaging.ComplexStepSetting (radius curvatureBound)
open YangMills.Construction.SeparatedSequences.BondKinds
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
abbrev FineBondIndex (c : BondAtLevel L m K k) : Type :=
  PositiveBondsOf (blockPairSymmetricBondsAt 0 c)
def fineFormOfValues (c : BondAtLevel L m K k)
    (x : LieBondField (blockPairSymmetricBondsAt 0 c)) : BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  fun e => (x.eval e : Matrices.ComplexMatrix2)
def fineFormOfFamily (c : BondAtLevel L m K k) (t : FineBondIndex c → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  fineFormOfValues c fun e => toTraceless (t e)
def backgroundPolydisc (c : BondAtLevel L m K k) (s : ℝ) :
    Set (FineBondIndex c ⊕ FineBondIndex c → Matrices.ComplexMatrix2) :=
  {t ∈ Matrices.GroupLieProduct.tracelessPi _ |
    Matrices.GroupLieProduct.supNorm (t ∘ Sum.inl) < s ∧
      Matrices.GroupLieProduct.supNorm (t ∘ Sum.inr) < s}
structure RealAverageCurvatureBounds (c : BondAtLevel L m K k) (α₀ : ℝ)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  averages_defined : BlockPairComplexAveragesDefined c U
  curvature_le : ∀ n < k, ∀ p : PlaquetteAtLevel L m K n,
    p.LiesIn (sitesIn (bondBlockPairAt n c)) →
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (blockPairComplexAverage c U n) p - 1) ≤
        2 * α₀ * squaredLevelMesh L k n
  mesh_le : ∀ n < k, 2 * α₀ * squaredLevelMesh L k n ≤ curvatureBound L
structure BackgroundAverageFactorization (c : BondAtLevel L m K k)
    (U A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (x : ∀ n : ℕ, LieBondField (blockPairSymmetricBondsAt n c)) : Prop where
  averages_defined : BlockPairComplexAveragesDefined c (bareTwist k A' U)
  straightened_defined : ∀ n ≤ k, TwistedStraightenedAverageDefined c U A' n
  gauge_defined : ∀ n ≤ k, TwistedAccumulatedGaugeDefined c U A' n
  eq_gauge_exp : ∀ n ≤ k, ∀ e ∈ blockPairBondsAt n c,
    blockPairComplexAverage c (bareTwist k A' U) n e =
      gaugeTransform (twistedAccumulatedGauge c U A' n)
        ((twistedStraightenedAverage c U A' n).expTwistOn (blockPairComplexAverage c U n)) e
  eq_exp : ∀ n ≤ k, ∀ e ∈ blockPairBondsAt n c,
    blockPairComplexAverage c (bareTwist k A' U) n e =
      (x n).expTwistOn (blockPairComplexAverage c U n) e
  norm_le : ∀ n ≤ k, supOperatorNorm (x n) ≤
    nearRealAverageBound L * (L : ℝ) ^ n * finestMeshInLevelUnits L k * blockPairSupNormAt 0 c A'
  norm_lt : ∀ n ≤ k,
    nearRealAverageBound L * (L : ℝ) ^ n * finestMeshInLevelUnits L k *
      blockPairSupNormAt 0 c A' < complexReferenceRadius L
def BackgroundAveragesHolomorphic (c : BondAtLevel L m K k) [Fintype (FineBondIndex c)] (α₀ : ℝ)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  RealAverageCurvatureBounds c α₀ U ∧
  (∀ n ≤ k, ∀ e ∈ blockPairBondsAt n c,
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (Matrices.GroupLieProduct.supBall _ (nearRealAverageRadius L)) fun t =>
        blockPairComplexAverage c (bareTwist k (fineFormOfFamily c t) U) n e) ∧
  ∃ x : ∀ n : ℕ, (FineBondIndex c → Matrices.ComplexMatrix2) →
      LieBondField (blockPairSymmetricBondsAt n c),
    (∀ n ≤ k, ∀ e : PositiveBondsOf (blockPairSymmetricBondsAt n c),
      ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless β
          Coordinates.ComplexCoordinates.matrixEquiv
          (Matrices.GroupLieProduct.supBall _ (nearRealAverageRadius L)) fun t =>
            (x n t e : Matrices.ComplexMatrix2)) ∧
    ∀ A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsFinestBlockPairData k c α₀ U A' 0 →
      blockPairSupNormAt 0 c A' < nearRealAverageRadius L →
        BackgroundAverageFactorization c U A' fun n => x n fun e => A' e.1
section Operators
variable [∀ (n : ℕ) (c' : BondAtLevel L m K (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c'))]
structure BackgroundKernelBounds (C : ℝ) (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    [Fintype (FineBondIndex c)] (α₀ : ℝ) (U A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    Prop where
  derivatives_defined : BlockPairStepDerivativesDefined c (bareTwist k A' U)
  holonomies_defined : ∀ y ∈ bondEndpoints c,
    BlockHolonomiesDefined y (blockPairComplexAverage c (bareTwist k A' U))
  sum_norm_le : ∑ e : FineBondIndex c,
      ‖LinearMap.toContinuousLinearMap
        (twistedStraightenedKernel c hc (bareTwist k A' U) e)‖ ≤
    1 + C * (α₀ + blockPairSupNormAt 0 c A')
  norm_le : ∀ e : FineBondIndex c,
    ‖LinearMap.toContinuousLinearMap
        (twistedStraightenedKernel c hc (bareTwist k A' U) e)‖ ≤
      finestMeshInLevelUnits L k ^ 4 * (1 + C * (α₀ + blockPairSupNormAt 0 c A'))
structure BackgroundKernelDifferences (C : ℝ) (c : BondAtLevel L m K k)
    (hc : c.IsPositivelyOriented) [Fintype (FineBondIndex c)]
    (U A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  sum_norm_sub_le : ∑ e : FineBondIndex c,
      ‖LinearMap.toContinuousLinearMap
        (twistedStraightenedKernel c hc (bareTwist k A' U) e -
          twistedStraightenedKernel c hc U e)‖ ≤
    C * blockPairSupNormAt 0 c A'
  norm_sub_le : ∀ e : FineBondIndex c,
    ‖LinearMap.toContinuousLinearMap
        (twistedStraightenedKernel c hc (bareTwist k A' U) e -
          twistedStraightenedKernel c hc U e)‖ ≤
      C * finestMeshInLevelUnits L k ^ 4 * blockPairSupNormAt 0 c A'
def BackgroundTransportDifferences (C : ℝ) (c : BondAtLevel L m K k)
    (U A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ y ∈ bondEndpoints c, ∀ z ∈ blockSitesAtLevel 0 y, ∀ X ∈ Matrices.ComplexMatrix2.traceless,
    Matrices.ComplexMatrix2.operatorNorm
        (Matrices.ComplexMatrix2.conjugateBy (twistedBlockTransport c (bareTwist k A' U) k y z) X -
          Matrices.ComplexMatrix2.conjugateBy (twistedBlockTransport c U k y z) X) ≤
      C * blockPairSupNormAt 0 c A' * Matrices.ComplexMatrix2.operatorNorm X
structure BackgroundLinearParts (C : ℝ) (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    [Fintype (FineBondIndex c)] (α₀ : ℝ) (U A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    Prop extends
    BackgroundKernelBounds C c hc α₀ U A',
    BackgroundKernelDifferences C c hc U A' where
  transport_sub_le : BackgroundTransportDifferences C c U A'
def straightenedAverageAtTop (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    (W : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (x : LieBondField (blockPairSymmetricBondsAt 0 c)) :
    ↥Matrices.ComplexMatrix2.traceless :=
  twistedStraightenedAverage c W (fineFormOfValues c x) k (blockPairTopBond c hc)
open Classical in
def straightenedDerivKernel (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    [Fintype (FineBondIndex c)] (W : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (x : LieBondField (blockPairSymmetricBondsAt 0 c)) (e : FineBondIndex c) :
    ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless :=
  (fderiv ℂ (straightenedAverageAtTop c hc W) x).toLinearMap ∘ₗ
    LinearMap.single ℂ (fun _ : FineBondIndex c => ↥Matrices.ComplexMatrix2.traceless) e
structure BackgroundStraightenedSizes (c : BondAtLevel L m K k)
    (U A' A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  defined : ∀ n ≤ k, TwistedStraightenedAverageDefined c (bareTwist k A' U) A n
  norm_le : ∀ n ≤ k, supOperatorNorm (twistedStraightenedAverage c (bareTwist k A' U) A n) ≤
    2 * (L : ℝ) ^ n * finestMeshInLevelUnits L k * blockPairSupNormAt 0 c A
  le_half_radius : ∀ n ≤ k,
    2 * (L : ℝ) ^ n * finestMeshInLevelUnits L k * blockPairSupNormAt 0 c A ≤ radius L / 2
structure BackgroundStraightenedDerivatives (C C₃ : ℝ)
    (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented) [Fintype (FineBondIndex c)] (α₀ : ℝ)
    (U A' A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  differentiableAt_zero :
    DifferentiableAt ℂ (straightenedAverageAtTop c hc (bareTwist k A' U)) 0
  fderiv_zero : (fderiv ℂ (straightenedAverageAtTop c hc (bareTwist k A' U)) 0).toLinearMap =
    twistedStraightenedOperator c hc (bareTwist k A' U)
  differentiableAt : DifferentiableAt ℂ (straightenedAverageAtTop c hc (bareTwist k A' U))
    (blockPairFineForm c A)
  kernel_norm_le : ∀ e : FineBondIndex c,
    ‖LinearMap.toContinuousLinearMap (straightenedDerivKernel c hc (bareTwist k A' U)
        (blockPairFineForm c A) e)‖ ≤
      finestMeshInLevelUnits L k ^ 4 * (1 + C * (α₀ + blockPairSupNormAt 0 c A') +
        C₃ * blockPairSupNormAt 0 c A)
  kernel_sub_norm_le : ∀ e : FineBondIndex c,
    ‖LinearMap.toContinuousLinearMap (straightenedDerivKernel c hc (bareTwist k A' U)
          (blockPairFineForm c A) e -
        twistedStraightenedKernel c hc (bareTwist k A' U) e)‖ ≤
      C₃ * finestMeshInLevelUnits L k ^ 4 * blockPairSupNormAt 0 c A
structure BackgroundStraightenedAverages (C C₃ : ℝ) (c : BondAtLevel L m K k)
    (hc : c.IsPositivelyOriented) [Fintype (FineBondIndex c)] (α₀ : ℝ)
    (U A' A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop extends
    BackgroundStraightenedSizes c U A' A,
    BackgroundStraightenedDerivatives C C₃ c hc α₀ U A' A
end Operators
structure TwistedAverageFactorization (c : BondAtLevel L m K k)
    (W A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  averages_defined : BlockPairComplexAveragesDefined c (bareTwist k A W)
  gauge_defined : ∀ n ≤ k, TwistedAccumulatedGaugeDefined c W A n
  eq_gauge_exp : ∀ n ≤ k, ∀ e ∈ blockPairBondsAt n c,
    blockPairComplexAverage c (bareTwist k A W) n e =
      gaugeTransform (twistedAccumulatedGauge c W A n)
        ((twistedStraightenedAverage c W A n).expTwistOn (blockPairComplexAverage c W n)) e
end YangMills.Construction.PeriodicLattice
