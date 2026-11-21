import YangMills.Construction.Lattice.DifferencesOfTheSystemAtASmallTriple
import YangMills.Construction.Lattice.FurtherSeminormsOfSolutionsAndSources
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions
open scoped ENNReal
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def augmentedSourceCorrection (W : FineBond L m S → Matrices.ComplexMatrix2) :
    AugmentedSourceTuple L m S → SourceTuple L m S
  | ((_, X₅), X₁) =>
    ((formCovariantDivergence S (Ω 0) W X₁ - trivialFormDivergence S (Ω 0) X₁, 0, 0, 0,
        fieldDiff S (covDivAt S Ω) W X₅, 0, 0, 0), 0)
def reducedAugmentedSourceCorrection (W : FineBond L m S → Matrices.ComplexMatrix2) :
    ReducedAugmentedSourceTuple L m S → ReducedSourceTuple L m S
  | ((_, X₅), X₁) =>
    ((formCovariantDivergence S (Ω 0) W X₁ - trivialFormDivergence S (Ω 0) X₁, 0, 0, 0,
        fieldDiff S (covDivAt S Ω) W X₅, 0, 0), 0)
def IsBoundedOverNeighbours {C D : Type} (𝒳 : Set C) (T : C → D) (N : FourTorus L m → C → ℝ≥0∞)
    (N' : FourTorus L m → D → ℝ≥0∞) (c : ℝ) : Prop :=
  ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ 𝒳,
    N' y (T Ψ) ≤ ENNReal.ofReal c * ⨆ (z : FourTorus L m) (_ : IsNearbyTop S Ω y z), N z Ψ
def ComparableOverNeighbours {C : Type} (𝒳 : Set C) (N N₀ : FourTorus L m → C → ℝ≥0∞) (c : ℝ) :
    Prop :=
  ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ 𝒳,
    N y Ψ ≤ ENNReal.ofReal c * (⨆ (z : FourTorus L m) (_ : IsNearbyTop S Ω y z), N₀ z Ψ) ∧
      N₀ y Ψ ≤ ENNReal.ofReal c * ⨆ (z : FourTorus L m) (_ : IsNearbyTop S Ω y z), N z Ψ
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def modifiedVariationMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) (Ψ : FullTuple L m S) : SourceTuple L m S :=
  match variationMap S Ω 𝔸 U J k Ψ with
  | ((f₁, f), X₅) =>
    ((f₁ + fieldDiff S (formDirichletLap S (Ω 0))
          (firstMemberRestriction S Ω U) Ψ.1 - formTransportDiagonal S (Ω 0) U Ψ.1, f), X₅)
def reducedModifiedVariationMap (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) (Ψ : ReducedTuple L m S) :
    ReducedSourceTuple L m S :=
  match reducedVariationMap S Ω 𝔸 U J k Ψ with
  | ((f₁, f), X₅) =>
    ((f₁ + fieldDiff S (formDirichletLap S (Ω 0))
          (firstMemberRestriction S Ω U) Ψ.1 - formTransportDiagonal S (Ω 0) U Ψ.1, f), X₅)
def weakVariationMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) (Ψ : FullTuple L m S) :
    AugmentedSourceTuple L m S :=
  (modifiedVariationMap S Ω 𝔸 U J k Ψ, -formTransportFlux S (Ω 0) U Ψ.1)
def reducedWeakVariationMap (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) (Ψ : ReducedTuple L m S) :
    ReducedAugmentedSourceTuple L m S :=
  (reducedModifiedVariationMap S Ω 𝔸 U J k Ψ, -formTransportFlux S (Ω 0) U Ψ.1)
structure FurtherSeminormConstantBounds (C ε : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) : Prop where
  l2_variation : IsBoundedOverNeighbours S Ω (fullTupleSpace S Ω) (variationMap S Ω 𝔸 U J k)
    (solutionL2SeminormAt S Ω trivialGaugeField) (sourceL2SeminormAt S Ω) (C * ε)
  reduced_l2_variation : IsBoundedOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedVariationMap S Ω 𝔸 U J k) (reducedSolutionL2SeminormAt S Ω trivialGaugeField)
    (reducedSourceL2SeminormAt S Ω) (C * ε)
  correction : IsBoundedOverNeighbours S Ω (augmentedSourceTupleSpace S Ω)
    (augmentedSourceCorrection S Ω (firstMemberRestriction S Ω U))
    (augmentedSourceSeminormAt S Ω) (sourceSeminormAt S Ω) (C * ε)
  reduced_correction : IsBoundedOverNeighbours S Ω (reducedAugmentedSourceTupleSpace S Ω)
    (reducedAugmentedSourceCorrection S Ω (firstMemberRestriction S Ω U))
    (reducedAugmentedSourceSeminormAt S Ω) (reducedSourceSeminormAt S Ω) (C * ε)
  l2_correction : IsBoundedOverNeighbours S Ω (augmentedSourceTupleSpace S Ω)
    (augmentedSourceCorrection S Ω (firstMemberRestriction S Ω U))
    (augmentedSourceL2SeminormAt S Ω) (sourceL2SeminormAt S Ω) (C * ε)
  reduced_l2_correction : IsBoundedOverNeighbours S Ω (reducedAugmentedSourceTupleSpace S Ω)
    (reducedAugmentedSourceCorrection S Ω (firstMemberRestriction S Ω U))
    (reducedAugmentedSourceL2SeminormAt S Ω) (reducedSourceL2SeminormAt S Ω) (C * ε)
  l2_comparable : ComparableOverNeighbours S Ω (fullTupleSpace S Ω)
    (solutionL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (solutionL2SeminormAt S Ω trivialGaugeField) C
  reduced_l2_comparable : ComparableOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedSolutionL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionL2SeminormAt S Ω trivialGaugeField) C
  strongL2_comparable : ComparableOverNeighbours S Ω (fullTupleSpace S Ω)
    (solutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (solutionStrongL2SeminormAt S Ω trivialGaugeField) C
  reduced_strongL2_comparable : ComparableOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedSolutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionStrongL2SeminormAt S Ω trivialGaugeField) C
structure FurtherSeminormExponentBounds (N β ε : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2) : Prop where
  weak_variation : IsBoundedOverNeighbours S Ω (fullTupleSpace S Ω)
    (weakVariationMap S Ω 𝔸 U J k)
    (solutionWeakHoelderSeminormAt S Ω β trivialGaugeField)
    (augmentedSourceHoelderSeminormAt S Ω β trivialGaugeField) (N * ε)
  reduced_weak_variation : IsBoundedOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedWeakVariationMap S Ω 𝔸 U J k)
    (reducedSolutionWeakHoelderSeminormAt S Ω β trivialGaugeField)
    (reducedAugmentedSourceHoelderSeminormAt S Ω β trivialGaugeField) (N * ε)
  weak_comparable : ComparableOverNeighbours S Ω (fullTupleSpace S Ω)
    (solutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (solutionWeakHoelderSeminormAt S Ω β trivialGaugeField) N
  reduced_weak_comparable : ComparableOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedSolutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (reducedSolutionWeakHoelderSeminormAt S Ω β trivialGaugeField) N
  strong_comparable : ComparableOverNeighbours S Ω (fullTupleSpace S Ω)
    (solutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (solutionStrongHoelderSeminormAt S Ω β trivialGaugeField) N
  reduced_strong_comparable : ComparableOverNeighbours S Ω (reducedTupleSpace S Ω)
    (reducedSolutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (reducedSolutionStrongHoelderSeminormAt S Ω β trivialGaugeField) N
end Operators
def ConstantBoundsFurtherSeminorms (L : ℕ) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (S : ScaleData)
    (_ : ∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
      Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (g ε : ℝ) (Ω : ℕ → Set (FourTorus L m)) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2),
    ε ≤ smallTripleRadius L → IsSmallInTrivialGauge S Ω g ε 𝔸 U J k →
      FurtherSeminormConstantBounds S Ω C ε 𝔸 U J k
def ExponentBoundsFurtherSeminorms (L : ℕ) (β N : ℝ) : Prop :=
  ∀ (m : ℕ) (S : ScaleData)
    (_ : ∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
      Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (g ε : ℝ) (Ω : ℕ → Set (FourTorus L m)) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (k : LeveledBond L m S → Matrices.ComplexMatrix2),
    ε ≤ smallTripleRadius L → IsSmallInTrivialGauge S Ω g ε 𝔸 U J k →
      FurtherSeminormExponentBounds S Ω N β ε 𝔸 U J k
end SequenceTriples
end YangMills.Construction
end
