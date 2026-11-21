import YangMills.Construction.LimitTheorem.AssertionsOnRotationsAtGivenData
import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.WhatALimitInheritsForm
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open LimitTheorem
open SeparatedTuples
open ReflectionPositivity.TupleForm
open TestSpaces (SepTupleOfCard)
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace)
open InfiniteLattice (GaugeField IsInfiniteVolumeLimit periodicGibbsSet smearedEnergyCumulant)
open TestFunctions (separatedPairsR4)
structure ApproximatingSequence (F : StatedSideFamily) where
  cutoff : ℕ+ → ℕ+
  tendsto_cutoff : Tendsto (fun j => (cutoff j : ℕ)) atTop atTop
  coupling : ℕ+ → ℝ
  isDatum : ∀ j, F.IsFirstPassage (cutoff j) (coupling j)
  state : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize F.L ((cutoff j : ℕ) : ℤ)))
  isLimit : ∀ j, IsInfiniteVolumeLimit F.L (cutoff j) (coupling j) (state j)
  mem_gibbs : ∀ j, state j ∈ periodicGibbsSet F.L (cutoff j) (coupling j)
def ApproximatingSequence.Defines {F : StatedSideFamily} (Q : ApproximatingSequence F)
    (S : CumulantFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
    Tendsto (fun j => smearedEnergyCumulant (Q.state j) X.1) atTop (𝓝 ((S n hn X : ℝ) : ℂ))
def lawConstantsOf (N : BoundConstants) : LawConstants := ⟨N.lawScale, N.lawError⟩
structure BaseLimitConditions (M : ℝ) (K : ExistentialConstants)
    (E : LawConstants) (S : CumulantFamily) : Prop where
  symmetries : LatticeSymmetries S
  axialPositive : IsReflectionPositiveAxial (centredOf S)
  distributions : HasDistributions S
  perBall : PerBallBoundsAt M (K.toConditionConstants E) (centredOf S)
  growth : GrowthBound (K.toConditionConstants E) (centredOf S)
  reconstruction : ReconstructionProperties (centredOf S)
  cumulants_eq : HasCumulants (centredOf S) S
  diagonalPositive : IsReflectionPositiveDiagonal (centredOf S)
  hamiltonian_ge : ∀ (h : IsPosSemidef (reflectionForm (centredOf S))) (i : Fin 3),
    HamiltonianGeMomentum (centredOf S) h i
  decomposition : DecompositionProperties (centredOf S)
  componentSymmetries : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ, ComponentSymmetries (A.comp ξ)
  componentOnePoint : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∃ c : A.space → ℝ, Continuous c ∧ ∫ ξ, c ξ ∂A.law = 0 ∧
        ∀ (ξ : A.space) (X : SepTupleOfCard 1),
          connectedFn (A.comp ξ) X = c ξ * ∫ x, X.1 0 x
  componentPerBall : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ, PerBallBoundsAt M (K.toConditionConstants E) (A.comp ξ)
  componentGrowth : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ, GrowthBound (K.toConditionConstants E) (A.comp ξ)
  componentReconstruction : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ, ComponentReconstruction (A.comp ξ)
  componentClustering : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ (X Y : SepTuple) (v : Fin 4 → ℝ),
        K.clusterRadius X Y ≤ TorusMetric.euclidNormVec v →
        SepTuple.Composable X (push (translate v) Y) ∧
          |A.comp ξ (SepTuple.juxt X (push (translate v) Y)) - A.comp ξ X * A.comp ξ Y| ≤
            K.clusterConst X Y * (TorusMetric.euclidNormVec v ^ 2)⁻¹
structure LimitLawConditions (ϑ : ℝ) (C : ConditionConstants) (S : CumulantFamily) : Prop where
  law : TwoPointLawHoldsAt ϑ C (centredOf S)
  twoPoint_pos : ∀ d ∈ Ioc (0 : ℝ) C.d₀, ∀ X : SepTupleOfCard 2,
    (X.1 0, X.1 1) ∈ separatedPairsR4 d ϑ → 0 < S 2 le_rfl X
  two_le_rank : ∀ h : IsPosSemidef (reflectionForm (centredOf S)),
    2 ≤ Module.rank ℂ (PhysicalSpace (centredOf S) h)
  componentLaw : ∀ A : DecompositionData,
    A.IsCanonical (centredOf S) →
      ∀ ξ, TwoPointLawHoldsAt ϑ C (A.comp ξ)
def BaseConditionsAt (M : ℝ) (N : BoundConstants) (K : ExistentialConstants) : Prop :=
  ∀ F : StatedSideFamily, F.M = M → BoundsHoldAt F N →
    ∀ (Q : ApproximatingSequence F) (S : CumulantFamily),
    Q.Defines S → BaseLimitConditions M K (lawConstantsOf N) S
def LawConditionsAt (M : ℝ) (N : BoundConstants) (K : ExistentialConstants) : Prop :=
  ∀ F : StatedSideFamily, F.M = M → BoundsHoldAt F N → ∀ ϑ : ℝ, ϑ ∈ Ioc (0 : ℝ) 1 →
    ϑ ≤ TwoPoints.Shapes.shapeConst → TwoPointLawAt F N ϑ →
    ∀ (Q : ApproximatingSequence F) (S : CumulantFamily), Q.Defines S →
      LimitLawConditions ϑ (K.toConditionConstants (lawConstantsOf N)) S
def RotationConditionsAt (M : ℝ) (N : BoundConstants) (K : ExistentialConstants) : Prop :=
  ∀ F : StatedSideFamily, F.M = M → BoundsHoldAt F N → ∀ ϑ : ℝ, ϑ ∈ Ioc (0 : ℝ) 1 →
    ϑ ≤ TwoPoints.Shapes.shapeConst → TwoPointLawAt F N ϑ →
    ∀ (Q : ApproximatingSequence F) (S : CumulantFamily), Q.Defines S →
      RotationAssertionsAt K S
def LimitConditionsExist : Prop :=
  ∀ (M : ℝ) (N : BoundConstants), 1 ≤ M → N.Admissible →
    ∃ K : ExistentialConstants, K.SideConditions ∧ BaseConditionsAt M N K ∧
      LawConditionsAt M N K ∧ RotationConditionsAt M N K
end YangMills.Construction.SystemsWithFiveBounds
end
