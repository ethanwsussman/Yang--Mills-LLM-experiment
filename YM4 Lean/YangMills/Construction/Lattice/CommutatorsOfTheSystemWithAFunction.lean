import YangMills.Construction.Lattice.CommutatorsWithAFunctionAndTheirMap
import YangMills.Construction.Lattice.HypothesesOnAFunctionInTheLemmaOnCommutators
import YangMills.Construction.Lattice.InteriorRegionsNearbyCurvature
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences SeparatedRegions Matrices
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
structure CommutatorLemmaHypotheses (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (h : FourTorus L m → ℝ) (ϑ : ℝ) : Prop where
  conjugate_norm_le : ∀ b ∈ (bondsInside 𝔸 : Set (FineBond L m S)), ∀ Z ∈ ComplexMatrix2.traceless,
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (U b) Z) ≤ 2 * ComplexMatrix2.operatorNorm Z ∧
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (U b)⁻¹ Z) ≤ 2 * ComplexMatrix2.operatorNorm Z
  curvature_le : ∀ y ∈ layerPoints S Ω, ∀ b ∈ bondIndexSet S (Ω 0), bondLocation S Ω b = y →
    layerPointMesh S Ω y ^ 2 * nearbyCurvature S.levels S.unitLevel 𝔸 U b ≤ 1
  current_seminorm_le : ∀ y ∈ layerPoints S Ω, (localSeminorms S Ω y).onBonds (-3) J ≤ 1
  leveled_seminorm_le : ∀ y ∈ layerPoints S Ω, (localSeminorms S Ω y).onExpansions (-3) j ≤ 1
  testFunction : IsCommutatorTestFunction S Ω h ϑ
def FirstRegionInteriorOrIsolated (𝔸 : Set (FourTorus L m)) : Prop :=
  IsInteriorRegion S.levels S.unitLevel (Ω 0) 𝔸 ∨ ∀ n : ℕ, 1 ≤ n → n ≤ S.top → Ω n = ∅
def IsLocallyConstantAt (θ : FourTorus L m → ℝ) (y : FourTorus L m) : Prop :=
  ∃ a : ℝ, ∀ p ∈ nearbyCellsUnion S Ω y, θ p = a
structure IsCommutatorRemainder {C D : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup D]
    [Module ℂ D] (𝒳 : Set C) (𝒴 : Set D) (K a : C → C) (ι : D → C) (T : C → D)
    (N : FourTorus L m → C → ℝ≥0∞) (N' : FourTorus L m → D → ℝ≥0∞) (θ : FourTorus L m → ℝ)
    (c ϑ : ℝ) : Prop where
  mapsTo : MapsTo T 𝒳 𝒴
  map_add_smul : ∀ Ψ ∈ 𝒳, ∀ Φ ∈ 𝒳, ∀ z : ℂ, T (Ψ + z • Φ) = T Ψ + z • T Φ
  comm_eq : ∀ Ψ ∈ 𝒳, K (a Ψ) - a (K Ψ) = ι (T Ψ)
  seminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ 𝒳,
    N' y (T Ψ) ≤ ENNReal.ofReal (c * ϑ⁻¹) *
      ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''), N y'' Ψ
  seminorm_eq_zero : ∀ y ∈ layerPoints S Ω, IsLocallyConstantAt S Ω θ y → ∀ Ψ ∈ 𝒳, N' y (T Ψ) = 0
open Classical in
def differenceQuotientBackShift (θ : FourTorus L m → ℝ) (base : SiteAtLevel L m S.levels 0 → FourTorus L m)
    (P : Set (SiteAtLevel L m S.levels 0)) (ν : Fin 4) (x : SiteAtLevel L m S.levels 0) : ℝ :=
  if x - unitStep L m (levelDepth S.levels 0) ν ∈ P then
    differenceQuotient S θ base P ν (x - unitStep L m (levelDepth S.levels 0) ν) else 0
structure LaplacianCommutatorFormulas (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (base : SiteAtLevel L m S.levels 0 → FourTorus L m) (U W : FineBond L m S → ComplexMatrix2)
    (θ : FourTorus L m → ℝ) (f B : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : Prop where
  interior_eq : ∀ x ∈ P, (∀ ν : Fin 4, x + unitStep L m (levelDepth S.levels 0) ν ∈ P ∧
      x - unitStep L m (levelDepth S.levels 0) ν ∈ P) →
    B x = -(∑ ν : Fin 4, (differenceQuotient S θ base P ν x • covariantForwardDiff S Y P W ν f x -
        differenceQuotientBackShift S θ base P ν x • covariantBackwardDiff S Y P W ν f x)) -
      diagonalCommutator S θ base P f x
  divergence_eq : ∀ x ∈ P, B x = ∑ ν : Fin 4, covariantBackwardDiff S Y P W ν
      (fluxCommutator S θ base P U ν f) x + diagonalCommutator S θ base P f x
structure LaplacianCommutatorFormulasHold (U : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    Prop where
  onSites : ∀ f ∈ regionSiteSpace S (Ω 0),
    LaplacianCommutatorFormulas S (Ω 0) (siteIndexSet S (Ω 0)) (fun x => (x : FourTorus L m)) U
      (firstMemberRestriction S Ω U) θ f
      (commutatorOf (siteSmul S θ) (siteSmul S θ)
        (dirichletLapAt S Ω (firstMemberRestriction S Ω U)) f)
  onComponents : ∀ A ∈ regionBondFormSpace S (Ω 0), ∀ μ : Fin 4,
    LaplacianCommutatorFormulas S (Ω 0) (axisBaseSites S (Ω 0) μ) (axisComponentBase S μ) U
      (firstMemberRestriction S Ω U) θ (bondFormComponent A μ)
      (bondFormComponent (commutatorOf (bondSmul S θ) (bondSmul S θ)
        (formDirichletLap S (Ω 0) (firstMemberRestriction S Ω U)) A) μ)
def sourceTupleSmul (θ : FourTorus L m → ℝ) : SourceTuple L m S → SourceTuple L m S
  | (f, X₅) => (fullTupleSmul S θ f, bondSmul S θ X₅)
def reducedSourceTupleSmul (θ : FourTorus L m → ℝ) :
    ReducedSourceTuple L m S → ReducedSourceTuple L m S
  | (f, X₅) => (reducedTupleSmul S θ f, bondSmul S θ X₅)
structure MultiplicationBounds {C D : Type} (𝒳 : Set C) (𝒴 : Set D) (a : C → C) (a' : D → D)
    (ι : D → C) (N : FourTorus L m → C → ℝ≥0∞) (N' : FourTorus L m → D → ℝ≥0∞)
    (θ : FourTorus L m → ℝ) : Prop where
  smul_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ 𝒳, N y (a Ψ) ≤ 2 * N y Ψ
  source_smul_le : ∀ y ∈ layerPoints S Ω, ∀ g ∈ 𝒴, N' y (a' g) ≤ N' y g
  embedding_smul : ∀ g ∈ 𝒴, (∀ y ∈ layerPoints S Ω, N' y g ≠ 0 → IsLocallyConstantAt S Ω θ y) →
    ι (a' g) = a (ι g)
structure MultiplicationBoundsHold (U : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    Prop where
  firstBlock : MultiplicationBounds S Ω (firstBlockSpace S Ω) (firstBlockSourceSpace S Ω) (siteSmul S θ)
    (firstSourceTwistedSmul S θ) (firstBlockSourceEmbedding S)
    (firstBlockSolutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (firstBlockSourceSeminormAt S Ω) θ
  siteBlock : MultiplicationBounds S Ω (siteTripleSpace S Ω) (siteSourceTripleSpace S Ω)
    (siteTripleSmul S θ) (siteSourceTwistedSmul S θ) (siteSourceEmbedding S)
    (siteSolutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (siteSourceSeminormAt S Ω) θ
  reduced : MultiplicationBounds S Ω (reducedTupleSpace S Ω) (reducedSourceTupleSpace S Ω)
    (reducedTupleSmul S θ) (reducedSourceTupleSmul S θ)
    (reducedSourceEmbedding S Ω (firstMemberRestriction S Ω U))
    (reducedSolutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (reducedSourceSeminormAt S Ω) θ
  full : MultiplicationBounds S Ω (fullTupleSpace S Ω) (sourceTupleSpace S Ω)
    (fullTupleSmul S θ) (sourceTupleSmul S θ)
    (sourceEmbedding S Ω (firstMemberRestriction S Ω U))
    (solutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (sourceSeminormAt S Ω) θ
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
structure CommutatorRemainderProperties (c ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
    (θ : FourTorus L m → ℝ) : Prop where
  firstBlock : IsCommutatorRemainder S Ω (firstBlockSpace S Ω) (firstBlockSourceSpace S Ω)
    (firstBlockOp S Ω U) (siteSmul S θ) (firstBlockSourceEmbedding S)
    (commMapFirst S Ω U θ)
    (firstBlockSolutionSeminormAt S Ω (firstMemberRestriction S Ω U))
    (firstBlockSourceSeminormAt S Ω) θ c ϑ
  siteBlock : IsCommutatorRemainder S Ω (siteTripleSpace S Ω) (siteSourceTripleSpace S Ω)
    (siteBlockOp S Ω U) (siteTripleSmul S θ) (siteSourceEmbedding S)
    (commMapSite S Ω U θ)
    (siteSolutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (siteSourceSeminormAt S Ω) θ c ϑ
  reduced : IsCommutatorRemainder S Ω (reducedTupleSpace S Ω) (reducedSourceTupleSpace S Ω)
    (reducedOp S Ω 𝔸 U J j) (reducedTupleSmul S θ)
    (reducedSourceEmbedding S Ω (firstMemberRestriction S Ω U))
    (reducedCommutatorMap S Ω 𝔸 U J j θ)
    (reducedSolutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (reducedSourceSeminormAt S Ω)
    θ c ϑ
  full : IsCommutatorRemainder S Ω (fullTupleSpace S Ω) (sourceTupleSpace S Ω)
    (fullOp S Ω 𝔸 U J j) (fullTupleSmul S θ)
    (sourceEmbedding S Ω (firstMemberRestriction S Ω U))
    (commutatorMap S Ω 𝔸 U J j θ)
    (solutionSeminormAt S Ω (firstMemberRestriction S Ω U)) (sourceSeminormAt S Ω) θ c ϑ
  laplacian : LaplacianCommutatorFormulasHold S Ω U θ
end Operators
def IsCommutatorBoundConstant (L : ℕ) (c : ℝ) : Prop :=
  1 ≤ c ∧
    ∀ (m : ℕ) (S : ScaleData)
      (_ : ∀ (n : ℕ) (e : BondAtLevel L m S.levels (n + 1)),
        Fintype (PositiveBondsOf (doubleBlockSymmetricSet e)))
      (Ω : ℕ → Set (FourTorus L m)) (g : ℝ) (𝔸 : Set (FourTorus L m))
      (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2)
      (h : FourTorus L m → ℝ) (ϑ : ℝ),
      IsAmbientTriple S Ω g 𝔸 U J j → CommutatorLemmaHypotheses S Ω 𝔸 U J j h ϑ →
        (FirstRegionInteriorOrIsolated S Ω 𝔸 → CommutatorRemainderProperties S Ω c ϑ 𝔸 U J j h) ∧
          MultiplicationBoundsHold S Ω U h
def commutatorBoundConstant (L : ℕ) : ℝ := Classical.epsilon (IsCommutatorBoundConstant L)
end SequenceTriples
end YangMills.Construction
end
