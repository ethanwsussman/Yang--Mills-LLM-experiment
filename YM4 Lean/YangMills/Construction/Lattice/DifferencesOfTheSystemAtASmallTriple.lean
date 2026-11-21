import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.DifferencesBetweenAConfigurationAndTheIdentity
import YangMills.Construction.Lattice.SmallTriplesInATrivialisingGauge
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences SeparatedRegions Matrices
namespace SequenceTriples
def smallTripleRadius (L : ℕ) : ℝ := 1 / 8 * ((L : ℝ) ^ 2)⁻¹ * complexBackgroundRadius L
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
abbrev TripleParamSpace (L m : ℕ) (S : ScaleData) : Type :=
  (FineBond L m S → ComplexMatrix2) × (FineBond L m S → ComplexMatrix2) ×
    (LeveledBond L m S → ComplexMatrix2)
def tripleParamSet (𝔸 : Set (FourTorus L m)) : Set (TripleParamSpace L m S) :=
  {z | (∀ e, z.1 e ∈ complexLieAlgebra) ∧ (∀ e ∉ bondsNearBase S Ω, z.1 e = 0) ∧
    z.2.1 ∈ (Bare.bondFormSpace 𝔸 : Set (FineBond L m S → ComplexMatrix2)) ∧
    z.2.2 ∈ SeparatedRegions.leveledFunctionSpace S Ω}
def smallTripleParamSet : Set (TripleParamSpace L m S) :=
  {z | ∀ e ∈ bondIndexSet S (Ω 0),
    layerPointMesh S Ω (bondLocation S Ω e) * ComplexMatrix2.operatorNorm (z.1 e) < classCeiling L}
def fieldOfLog (U B : FineBond L m S → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  expTwist (fun c => ((S.finestMesh L : ℝ) : ℂ) • B c)
    (extendByOne
      {e | e ∉ bondsNearBase S Ω ∧ e.opposite ∉ bondsNearBase S Ω} U)
def IsHolomorphicInTriple {C D : Type} [AddCommGroup D] [Module ℂ D]
    (𝔸 : Set (FourTorus L m)) (X : Set C) (V : TripleParamSpace L m S → C → D) : Prop :=
  ∃ (E : Submodule ℂ (TripleParamSpace L m S)) (_ : FiniteDimensional ℂ E),
    (E : Set (TripleParamSpace L m S)) = tripleParamSet S Ω 𝔸 ∧
      ∀ Ψ ∈ X, ∀ φ : Module.Dual ℂ D,
        GroupLieNumberProduct.IsHolomorphicBetweenModules
          {z : E | (z : TripleParamSpace L m S) ∈ smallTripleParamSet S Ω}
          fun z : E => φ (V z Ψ)
structure IsBoundedSystemVariation {C D : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup D]
    [Module ℂ D] (X : Set C) (Y : Set D) (K₀ K : C → C) (ι₀ : D → C) (V : C → D)
    (N : FourTorus L m → C → ℝ≥0∞) (N' : FourTorus L m → D → ℝ≥0∞) (c : ℝ) : Prop where
  mapsTo : MapsTo V X Y
  map_add : ∀ Ψ ∈ X, ∀ Φ ∈ X, V (Ψ + Φ) = V Ψ + V Φ
  map_smul : ∀ (a : ℂ), ∀ Ψ ∈ X, V (a • Ψ) = a • V Ψ
  sub_eq : ∀ Ψ ∈ X, K₀ Ψ - K Ψ = ι₀ (V Ψ)
  bound : ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ X,
    N' y (V Ψ) ≤ ENNReal.ofReal c * ⨆ (y' : FourTorus L m) (_ : IsNearbyTop S Ω y y'), N y' Ψ
def SeminormsComparable {C : Type} (X : Set C) (N N₀ : FourTorus L m → C → ℝ≥0∞) (c : ℝ) : Prop :=
  ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ X,
    N y Ψ ≤ ENNReal.ofReal c * N₀ y Ψ ∧ N₀ y Ψ ≤ ENNReal.ofReal c * N y Ψ
structure IsEmbeddingCorrection {C D : Type} [Add D] (Y : Set D) (ι ι₀ : D → C) (n : D → D)
    (N' : FourTorus L m → D → ℝ≥0∞) (c : ℝ) : Prop where
  mapsTo : MapsTo n Y Y
  eq : ∀ g ∈ Y, ι g = ι₀ (g + n g)
  bound : ∀ y ∈ layerPoints S Ω, ∀ g ∈ Y,
    N' y (n g) ≤ ENNReal.ofReal c *
      ⨆ (y' : FourTorus L m) (_ : y' = y ∨ AreAdjacentPoints S Ω y y'), N' y' g
def laplacianVariation (P : Set (SiteAtLevel L m S.levels 0))
    (W : FineBond L m S → ComplexMatrix2) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  fieldDiff S (fun W' => covariantLaplacianOn S (Ω 0) P W' f) W
structure LaplacianVariationFormulas (U : FineBond L m S → ComplexMatrix2)
    (P : Set (SiteAtLevel L m S.levels 0)) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    Prop where
  forward : ∀ x ∈ P, (∀ ν : Fin 4, x + unitStep L m (levelDepth S.levels 0) ν ∈ P ∧
      x - unitStep L m (levelDepth S.levels 0) ν ∈ P) →
    laplacianVariation S Ω P (firstMemberRestriction S Ω U) f x =
      -(∑ ν : Fin 4, (forwardTransportCoeff S U ν x (trivialForwardDiff S (Ω 0) P ν f x) -
          backwardTransportCoeff S U ν (x - unitStep L m (levelDepth S.levels 0) ν)
            (trivialForwardDiff S (Ω 0) P ν f (x - unitStep L m (levelDepth S.levels 0) ν)))) -
        (((S.finestMesh L)⁻¹ : ℝ) : ℂ) • ∑ ν : Fin 4, (forwardTransportCoeff S U ν x (f x) +
          backwardTransportCoeff S U ν (x - unitStep L m (levelDepth S.levels 0) ν) (f x))
  divergence : ∀ x ∈ P,
    laplacianVariation S Ω P (firstMemberRestriction S Ω U) f x =
      ∑ ν : Fin 4, trivialBackwardDiff S (Ω 0) P ν (transportFlux S P U ν f) x +
        transportDiagonal S P U f x
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
structure SmallTripleVariationBounds (C ε : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2) : Prop where
  mem_class : firstMemberRestriction S Ω U ∈
    admissibleClass S Ω (classCeiling L) (classCeiling L)
  first : IsBoundedSystemVariation S Ω (firstBlockSpace S Ω) (firstBlockSourceSpace S Ω)
    (firstBlockOp S Ω trivialGaugeField) (firstBlockOp S Ω U)
    (firstBlockSourceEmbedding S) (firstVariationMap S Ω U)
    (firstBlockSolutionSeminormAt S Ω trivialGaugeField) (firstBlockSourceSeminormAt S Ω) (C * ε)
  second : IsBoundedSystemVariation S Ω (siteTripleSpace S Ω) (siteSourceTripleSpace S Ω)
    (siteBlockOp S Ω trivialGaugeField) (siteBlockOp S Ω U)
    (siteSourceEmbedding S) (siteVariationMap S Ω U)
    (siteSolutionSeminormAt S Ω trivialGaugeField) (siteSourceSeminormAt S Ω) (C * ε)
  fourth : IsBoundedSystemVariation S Ω (reducedTupleSpace S Ω) (reducedSourceTupleSpace S Ω)
    (reducedOp S Ω univ trivialGaugeField 0 0)
    (reducedOp S Ω 𝔸 U J j) (trivialReducedSourceEmbedding S Ω)
    (reducedVariationMap S Ω 𝔸 U J j)
    (reducedSolutionSeminormAt S Ω trivialGaugeField) (reducedSourceSeminormAt S Ω) (C * ε)
  fifth : IsBoundedSystemVariation S Ω (fullTupleSpace S Ω) (sourceTupleSpace S Ω)
    (fullOp S Ω univ trivialGaugeField 0 0) (fullOp S Ω 𝔸 U J j)
    (trivialSourceEmbedding S Ω) (variationMap S Ω 𝔸 U J j)
    (solutionSeminormAt S Ω trivialGaugeField) (sourceSeminormAt S Ω) (C * ε)
  first_holomorphic : IsHolomorphicInTriple S Ω 𝔸 (firstBlockSpace S Ω)
    fun z => firstVariationMap S Ω (fieldOfLog S Ω U z.1)
  second_holomorphic : IsHolomorphicInTriple S Ω 𝔸 (siteTripleSpace S Ω)
    fun z => siteVariationMap S Ω (fieldOfLog S Ω U z.1)
  fourth_holomorphic : IsHolomorphicInTriple S Ω 𝔸 (reducedTupleSpace S Ω)
    fun z => reducedVariationMap S Ω 𝔸 (fieldOfLog S Ω U z.1) z.2.1 z.2.2
  fifth_holomorphic : IsHolomorphicInTriple S Ω 𝔸 (fullTupleSpace S Ω)
    fun z => variationMap S Ω 𝔸 (fieldOfLog S Ω U z.1) z.2.1 z.2.2
  factor_le : 1 + 8 * ε ≤ 2
  first_seminorms : SeminormsComparable S Ω (firstBlockSpace S Ω)
    (firstBlockSolutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (firstBlockSolutionSeminormAt S Ω trivialGaugeField) (1 + 8 * ε)
  second_seminorms : SeminormsComparable S Ω (siteTripleSpace S Ω)
    (siteSolutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (siteSolutionSeminormAt S Ω trivialGaugeField) (1 + 8 * ε)
  fourth_seminorms : SeminormsComparable S Ω (reducedTupleSpace S Ω)
    (reducedSolutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionSeminormAt S Ω trivialGaugeField) (1 + 8 * ε)
  fifth_seminorms : SeminormsComparable S Ω (fullTupleSpace S Ω)
    (solutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (solutionSeminormAt S Ω trivialGaugeField) (1 + 8 * ε)
  correction : IsEmbeddingCorrection S Ω (sourceTupleSpace S Ω)
    (sourceEmbedding S Ω (firstMemberRestriction S Ω U)) (trivialSourceEmbedding S Ω)
    (sourceCorrection S Ω (firstMemberRestriction S Ω U)) (sourceSeminormAt S Ω)
    (16 * (L : ℝ) ^ 3 * ε)
  reduced_correction : IsEmbeddingCorrection S Ω (reducedSourceTupleSpace S Ω)
    (reducedSourceEmbedding S Ω (firstMemberRestriction S Ω U))
    (trivialReducedSourceEmbedding S Ω)
    (reducedSourceCorrection S Ω (firstMemberRestriction S Ω U)) (reducedSourceSeminormAt S Ω)
    (16 * (L : ℝ) ^ 3 * ε)
  site_formulas : ∀ f ∈ regionSiteSpace S (Ω 0),
    LaplacianVariationFormulas S Ω U (siteIndexSet S (Ω 0)) f
  component_formulas : ∀ A ∈ regionBondFormSpace S (Ω 0), ∀ μ : Fin 4,
    LaplacianVariationFormulas S Ω U (axisBaseSites S (Ω 0) μ) (bondFormComponent A μ)
end Operators
def IsVariationConstant (L : ℕ) (C : ℝ) : Prop :=
  1 ≤ C ∧ ∀ (m : ℕ) (S : ScaleData)
    (_ : ∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
      Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (g ε : ℝ) (Ω : ℕ → Set (FourTorus L m)) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2),
    ε ≤ smallTripleRadius L → IsSmallInTrivialGauge S Ω g ε 𝔸 U J j →
      SmallTripleVariationBounds S Ω C ε 𝔸 U J j
def variationConstant (L : ℕ) : ℝ := Classical.epsilon (IsVariationConstant L)
end SequenceTriples
end YangMills.Construction
end
