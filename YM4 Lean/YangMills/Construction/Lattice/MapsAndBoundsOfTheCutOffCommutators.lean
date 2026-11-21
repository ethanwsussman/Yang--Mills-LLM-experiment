import YangMills.Construction.Lattice.CommutatorsOfTheSystemWithAFunction
import YangMills.Construction.Lattice.DifferencesOfTheSystemAtASmallTriple
import YangMills.Construction.Lattice.FurtherSeminormsOfSolutionsAndSources
import YangMills.Construction.SeparatedSequences.ProductsWithACutOffFunction
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
structure CutoffCommutatorData (g ϵ ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (V : Set (FourTorus L m)) (h : V → ℝ) (θ : FourTorus L m → ℝ) (K : Set (FourTorus L m)) : Prop where
  isAmbientTriple : IsAmbientTriple S Ω g 𝔸 U J j
  hypotheses : CommutatorLemmaHypotheses S Ω 𝔸 U J j θ ϑ
  small_or_empty : (IsSmallTriple S Ω g ϵ 𝔸 U J j ∧ ϵ ≤ smallTripleRadius L) ∨
    ∀ n : ℕ, 1 ≤ n → n ≤ S.top → Ω n = ∅
  isExtension : IsExtensionNearFirstMember Ω V h θ
  eq_zero_off : ∀ p : V, (p : FourTorus L m) ∉ K → h p = 0
def maxWithinDoubleRadius (n : FourTorus L m → ℝ≥0∞) (y : FourTorus L m) : ℝ≥0∞ :=
  ⨆ (y'' : FourTorus L m) (_ : y'' ∈ layerPoints S Ω ∧
    layerWeightedDist S Ω y y'' ≤ ENNReal.ofReal (2 * YangMills.Construction.Lattice.siteNearnessRadius L)), n y''
def IsBoundedByDoubleRadiusMax {C D : Type} (𝒳 : Set C) (T : C → D) (N : FourTorus L m → C → ℝ≥0∞)
    (N' : FourTorus L m → D → ℝ≥0∞) (c : ℝ) : Prop :=
  ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ 𝒳,
    N' y (T Ψ) ≤ ENNReal.ofReal c * maxWithinDoubleRadius S Ω (fun y'' => N y'' Ψ) y
def IsBoundedNearSet {D : Type} (𝒵 : Set D) (T : D → D) (N : FourTorus L m → D → ℝ≥0∞) (c : ℝ)
    (K : Set (FourTorus L m)) : Prop :=
  ∀ y ∈ layerPoints S Ω, ∀ g ∈ 𝒵,
    N y (T g) ≤ ENNReal.ofReal c *
      ⨆ y'' ∈ CutoffProducts.sitesMeetingSet S Ω K,
        ⨆ _ : y'' = y ∨ AreAdjacentPoints S Ω y y'', N y'' g
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def modifiedCommutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) (Ψ : FullTuple L m S) :
    SourceTuple L m S :=
  match commutatorMap S Ω 𝔸 U J j θ Ψ with
  | ((f₁, f), X₅) =>
    ((f₁ - commutatorOf (bondSmul S θ) (bondSmul S θ)
          (formDirichletLap S (Ω 0) (firstMemberRestriction S Ω U)) Ψ.1 +
        diagonalCommutatorForm S θ (Ω 0) Ψ.1, f), X₅)
def reducedModifiedCommutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) (Ψ : ReducedTuple L m S) :
    ReducedSourceTuple L m S :=
  match reducedCommutatorMap S Ω 𝔸 U J j θ Ψ with
  | ((f₁, f), X₅) =>
    ((f₁ - commutatorOf (bondSmul S θ) (bondSmul S θ)
          (formDirichletLap S (Ω 0) (firstMemberRestriction S Ω U)) Ψ.1 +
        diagonalCommutatorForm S θ (Ω 0) Ψ.1, f), X₅)
def weakCommutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) (Ψ : FullTuple L m S) :
    AugmentedSourceTuple L m S :=
  (modifiedCommutatorMap S Ω 𝔸 U J j θ Ψ, fluxCommutatorForm S θ (Ω 0) U Ψ.1)
def reducedWeakCommutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) (Ψ : ReducedTuple L m S) :
    ReducedAugmentedSourceTuple L m S :=
  (reducedModifiedCommutatorMap S Ω 𝔸 U J j θ Ψ, fluxCommutatorForm S θ (Ω 0) U Ψ.1)
structure CutoffCommutatorConstantBounds (C ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (θ : FourTorus L m → ℝ) (K : Set (FourTorus L m)) : Prop where
  l2_commutator : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω)
    (commutatorMap S Ω 𝔸 U J j θ)
    (solutionL2SeminormAt S Ω (firstMemberRestriction S Ω U)) (sourceL2SeminormAt S Ω)
    (C * ϑ⁻¹)
  reduced_l2_commutator : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedCommutatorMap S Ω 𝔸 U J j θ)
    (reducedSolutionL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSourceL2SeminormAt S Ω) (C * ϑ⁻¹)
  seminorm_smul : IsBoundedNearSet S Ω (augmentedSourceTupleSpace S Ω)
    (augmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (augmentedSourceSeminormAt S Ω) C K
  reduced_seminorm_smul : IsBoundedNearSet S Ω (reducedAugmentedSourceTupleSpace S Ω)
    (reducedAugmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (reducedAugmentedSourceSeminormAt S Ω) C K
  hoelder_smul : ∀ ε ∈ Ioc (0 : ℝ) 1, IsBoundedNearSet S Ω (augmentedSourceTupleSpace S Ω)
    (augmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (augmentedSourceHoelderSeminormAt S Ω ε (firstMemberRestriction S Ω U)) C K
  reduced_hoelder_smul : ∀ ε ∈ Ioc (0 : ℝ) 1,
    IsBoundedNearSet S Ω (reducedAugmentedSourceTupleSpace S Ω)
      (reducedAugmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
      (reducedAugmentedSourceHoelderSeminormAt S Ω ε (firstMemberRestriction S Ω U)) C K
  l2_smul : IsBoundedNearSet S Ω (augmentedSourceTupleSpace S Ω)
    (augmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (augmentedSourceL2SeminormAt S Ω) C K
  reduced_l2_smul : IsBoundedNearSet S Ω (reducedAugmentedSourceTupleSpace S Ω)
    (reducedAugmentedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (reducedAugmentedSourceL2SeminormAt S Ω) C K
  source_l2_smul : IsBoundedNearSet S Ω (sourceTupleSpace S Ω)
    (sourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ) (sourceL2SeminormAt S Ω) C K
  reduced_source_l2_smul : IsBoundedNearSet S Ω (reducedSourceTupleSpace S Ω)
    (reducedSourceTwistedSmul S Ω (firstMemberRestriction S Ω U) θ)
    (reducedSourceL2SeminormAt S Ω) C K
structure CutoffCommutatorExponentBounds (N β ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (θ : FourTorus L m → ℝ) : Prop where
  weak_commutator : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω)
    (weakCommutatorMap S Ω 𝔸 U J j θ)
    (solutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (augmentedSourceHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) (N * ϑ⁻¹)
  reduced_weak_commutator : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedWeakCommutatorMap S Ω 𝔸 U J j θ)
    (reducedSolutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (reducedAugmentedSourceHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) (N * ϑ⁻¹)
  weak_smul : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω) (fullTupleSmul S θ)
    (solutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (solutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) N
  reduced_weak_smul : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedTupleSmul S θ)
    (reducedSolutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (reducedSolutionWeakHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) N
  strong_smul : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω) (fullTupleSmul S θ)
    (solutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (solutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) N
  reduced_strong_smul : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedTupleSmul S θ)
    (reducedSolutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U))
    (reducedSolutionStrongHoelderSeminormAt S Ω β (firstMemberRestriction S Ω U)) N
  l2_smul : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω) (fullTupleSmul S θ)
    (solutionL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (solutionL2SeminormAt S Ω (firstMemberRestriction S Ω U)) N
  reduced_l2_smul : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedTupleSmul S θ)
    (reducedSolutionL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionL2SeminormAt S Ω (firstMemberRestriction S Ω U)) N
  strongL2_smul : IsBoundedByDoubleRadiusMax S Ω (fullTupleSpace S Ω) (fullTupleSmul S θ)
    (solutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (solutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U)) N
  reduced_strongL2_smul : IsBoundedByDoubleRadiusMax S Ω (reducedTupleSpace S Ω)
    (reducedTupleSmul S θ)
    (reducedSolutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionStrongL2SeminormAt S Ω (firstMemberRestriction S Ω U)) N
end Operators
def IsCutoffCommutatorConstant (L : ℕ) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (S : ScaleData)
    (_ : ∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
      Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (Ω : ℕ → Set (FourTorus L m)) (g ϵ ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (V : Set (FourTorus L m)) (h : V → ℝ) (θ : FourTorus L m → ℝ) (K : Set (FourTorus L m)),
    CutoffCommutatorData S Ω g ϵ ϑ 𝔸 U J j V h θ K →
      CutoffCommutatorConstantBounds S Ω C ϑ 𝔸 U J j θ K
def IsCutoffCommutatorExponentConstant (L : ℕ) (β N : ℝ) : Prop :=
  ∀ (m : ℕ) (S : ScaleData)
    (_ : ∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
      Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (Ω : ℕ → Set (FourTorus L m)) (g ϵ ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (V : Set (FourTorus L m)) (h : V → ℝ) (θ : FourTorus L m → ℝ) (K : Set (FourTorus L m)),
    CutoffCommutatorData S Ω g ϵ ϑ 𝔸 U J j V h θ K →
      CutoffCommutatorExponentBounds S Ω N β ϑ 𝔸 U J j θ
end YangMills.Construction.SequenceTriples
end
