import YangMills.Construction.Lattice.FormOfACurrentAndPairsOnShell
import YangMills.Construction.Lattice.OperatorsAtAPairOfASeparatedSequence
import YangMills.Construction.Lattice.PairingOfTheExpansionsOfASequence
import YangMills.Construction.Lattice.PartitionsRegionsAndCellsAlongAReferenceSequence
import YangMills.Construction.Lattice.QuadraticExpansionOfTheActionOfARegion
import YangMills.Construction.Lattice.WeightedPropagatorAndProjectionOnTheTops
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions
namespace SequenceTriples
variable {L m : ℕ} (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (FourTorus L m))
def firstMemberRestriction (U : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  extendByOne (bondsInside (Ω 0)) U
structure IsAmbientTriple (g : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) : Prop where
  admissibleFactor : Conventions.IsAdmissibleBlockingFactor L
  m_pos : 0 < m
  levels_pos : 0 < S.levels
  unitLevel_eq_top : S.unitLevel = S.top
  isRegion : CellRegions.IsAdmissibleRegion S.levels 𝔸
  isGaugeField : Bare.IsComplexGaugeFieldInside 𝔸 U
  mem_forms : J ∈ (Bare.bondFormSpace 𝔸 : Set (FineBond L m S → Matrices.ComplexMatrix2))
  isSeparated : IsSeparatedWithGap S g Ω
  first_subset : Ω 0 ⊆ 𝔸
  mem_class : firstMemberRestriction S Ω U ∈
    admissibleClass S Ω (classCeiling L) (classCeiling L)
  mem_expansions : j ∈ SeparatedRegions.leveledFunctionSpace S Ω
def topSiteValues (W : FineBond L m S → Matrices.ComplexMatrix2)
    (l : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    FourTorus L m → Matrices.ComplexMatrix2 :=
  (layerPoints S Ω).indicator (layerSiteValue S Ω W l)
def topSiteAdjoint (W : FineBond L m S → Matrices.ComplexMatrix2)
    (σ : FourTorus L m → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  layerValueAdjoint S Ω W fun y => σ y
def restrictToRows (ν : PeriodicLattice.LeveledBond L m S.levels → Matrices.ComplexMatrix2) :
    SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2 :=
  (leveledIndexSet S Ω).indicator ν
def expansionExtension (ω : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) :
    PeriodicLattice.LeveledBond L m S.levels → Matrices.ComplexMatrix2 :=
  interiorOutwardExtend S Ω fun c => ω c.1
def quadraticOnExpansions (W A : FineBond L m S → Matrices.ComplexMatrix2) :
    SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2 :=
  restrictToRows S Ω (quadraticExpansions S Ω W A)
def secondOrderOp (W : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) :
    (FineBond L m S → Matrices.ComplexMatrix2) → FineBond L m S → Matrices.ComplexMatrix2 :=
  Bare.symmetricRepresentative (Ω 0) (S.finestMesh L) fun A =>
    2 * SeparatedRegions.leveledPairing S Ω (quadraticOnExpansions S Ω W A) j
abbrev weightedSiteOp (W : FineBond L m S → Matrices.ComplexMatrix2) :
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) →
      SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  weightedLaplacian S Ω W (topWeight S Ω)
def compressedHessian (𝔸 : Set (FourTorus L m)) (U A' : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun B =>
    B ∈ (Bare.bondFormSpace (Ω 0) : Set (FineBond L m S → Matrices.ComplexMatrix2)) ∧
    ∀ A ∈ (Bare.bondFormSpace (Ω 0) : Set (FineBond L m S → Matrices.ComplexMatrix2)),
      Bare.bondFormInnerOn (Ω 0) (S.finestMesh L) A B =
        Bare.bondFormInnerOn 𝔸 (S.finestMesh L) A
          (Bare.regionHessianOp 𝔸 (S.finestMesh L) U A')
def compressedOp (𝔸 : Set (FourTorus L m)) (U A : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  compressedHessian S Ω 𝔸 U A +
    covGradAt S Ω (firstMemberRestriction S Ω U)
      (covDivAt S Ω (firstMemberRestriction S Ω U) A)
def sourceSum (k : FineBond L m S → Matrices.ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : Matrices.ComplexMatrix2 :=
  ∑ᶠ (e : FineBond L m S) (_ : e ∈ bondIndexSet S (Ω 0) ∧ e.source = x), k e
def endpointSum (W k : FineBond L m S → Matrices.ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : Matrices.ComplexMatrix2 :=
  sourceSum S Ω k x +
    ∑ᶠ (e : FineBond L m S) (_ : e ∈ bondIndexSet S (Ω 0) ∧ e.target = x),
      Matrices.ComplexMatrix2.conjugateBy (W e)⁻¹ (k e)
def bondFormOfValues (k : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  PeriodicLattice.bondFormOfPositive ((bondIndexSet S (Ω 0)).indicator k)
def currentTerm (W J : FineBond L m S → Matrices.ComplexMatrix2)
    (v : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  bondFormOfValues S Ω fun e =>
    (1 / 2 : ℂ) • Complex.I •
      ⁅J e, v e.source + Matrices.ComplexMatrix2.conjugateBy (W e) (v e.target)⁆
def siteCurrentSource (W J A : FineBond L m S → Matrices.ComplexMatrix2)
    (v : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  (1 / 2 : ℂ) • endpointSum S Ω W (fun e => Complex.I • ⁅A e, J e⁆) -
    (1 / 2 : ℂ) • sourceSum S Ω fun e => Complex.I • ⁅covGradAt S Ω W v e, J e⁆
def bondCurrentSource (W J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2)
    (A : FineBond L m S → Matrices.ComplexMatrix2)
    (v : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  bondFormOfValues S Ω (fun e => -((1 / 2 : ℂ) • Complex.I • ⁅J e, v e.source⁆)) -
    secondOrderOp S Ω W j (A - covGradAt S Ω W v)
def siteSourceTerm (W J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2)
    (A : FineBond L m S → Matrices.ComplexMatrix2)
    (v : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  siteCurrentSource S Ω W J A v + covDivAt S Ω W (bondCurrentSource S Ω W J j A v)
abbrev SiteTriple (L m : ℕ) (S : SeparatedSequences.ScaleData) : Type :=
  (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) × (FourTorus L m → Matrices.ComplexMatrix2)
abbrev ReducedTuple (L m : ℕ) (S : SeparatedSequences.ScaleData) : Type :=
  (FineBond L m S → Matrices.ComplexMatrix2) × (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) × (FourTorus L m → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) × (FourTorus L m → Matrices.ComplexMatrix2)
abbrev FullTuple (L m : ℕ) (S : SeparatedSequences.ScaleData) : Type :=
  (FineBond L m S → Matrices.ComplexMatrix2) × (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) × (FourTorus L m → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) ×
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) × (FourTorus L m → Matrices.ComplexMatrix2) ×
    (SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2)
abbrev firstBlockSpace : Set (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :=
  regionSiteSpace S (Ω 0)
def siteTripleSpace : Set (SiteTriple L m S) :=
  regionSiteSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ pointFunctionSpace S Ω
def reducedTupleSpace : Set (ReducedTuple L m S) :=
  regionBondFormSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ
    pointFunctionSpace S Ω ×ˢ regionSiteSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ
    pointFunctionSpace S Ω
def fullTupleSpace : Set (FullTuple L m S) :=
  regionBondFormSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ
    pointFunctionSpace S Ω ×ˢ regionSiteSpace S (Ω 0) ×ˢ regionSiteSpace S (Ω 0) ×ˢ
    pointFunctionSpace S Ω ×ˢ SeparatedRegions.leveledFunctionSpace S Ω
def fullInjOne (A : FineBond L m S → Matrices.ComplexMatrix2) : FullTuple L m S :=
  (A, 0, 0, 0, 0, 0, 0, 0)
def reducedInjOne (A : FineBond L m S → Matrices.ComplexMatrix2) : ReducedTuple L m S :=
  (A, 0, 0, 0, 0, 0, 0)
def reducedInjTwo (v : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) : ReducedTuple L m S :=
  (0, v, 0, 0, 0, 0, 0)
def reducedInjFour (σ : FourTorus L m → Matrices.ComplexMatrix2) : ReducedTuple L m S :=
  (0, 0, 0, σ, 0, 0, 0)
def reducedInjFive (p : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    ReducedTuple L m S :=
  (0, 0, 0, 0, p, 0, 0)
abbrev firstBlockOp (U : FineBond L m S → Matrices.ComplexMatrix2) :
    (SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) →
      SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  weightedSiteOp S Ω (firstMemberRestriction S Ω U)
def siteBlockOp (U : FineBond L m S → Matrices.ComplexMatrix2) : SiteTriple L m S → SiteTriple L m S
  | (v, w, σ) =>
    let W := firstMemberRestriction S Ω U
    (weightedSiteOp S Ω W v + w,
      weightedSiteOp S Ω W w - topSiteAdjoint S Ω W σ,
      topSiteValues S Ω W v)
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def expansionValuesOfForm (W A : FineBond L m S → Matrices.ComplexMatrix2) :
    SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2 :=
  restrictToRows S Ω (rowAverage S Ω W A)
def expansionValuesAdjoint (W : FineBond L m S → Matrices.ComplexMatrix2)
    (ω : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  rowAverageTranspose S Ω W (expansionExtension S Ω ω)
def constrainedOp (𝔸 : Set (FourTorus L m)) (U A : FineBond L m S → Matrices.ComplexMatrix2) :
    FineBond L m S → Matrices.ComplexMatrix2 :=
  compressedOp S Ω 𝔸 U A +
    rowAverageTranspose S Ω (firstMemberRestriction S Ω U)
      (spacingWeightSMul S (rowAverage S Ω (firstMemberRestriction S Ω U) A))
def fullOp (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) :
    FullTuple L m S → FullTuple L m S
  | (A, v, w, σ, p, q, r, ω) =>
    let W := firstMemberRestriction S Ω U
    (constrainedOp S Ω 𝔸 U A - covGradAt S Ω W (w + p) - currentTerm S Ω W J v -
        secondOrderOp S Ω W j (A - covGradAt S Ω W v) - expansionValuesAdjoint S Ω W ω,
      weightedSiteOp S Ω W v + w - covDivAt S Ω W A,
      weightedSiteOp S Ω W w - topSiteAdjoint S Ω W σ,
      topSiteValues S Ω W v,
      weightedSiteOp S Ω W p + topSiteAdjoint S Ω W r - siteSourceTerm S Ω W J j A v,
      p + weightedSiteOp S Ω W q,
      -topSiteValues S Ω W q,
      expansionValuesOfForm S Ω W A)
def reducedOp (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : SeparatedRegions.LeveledBond L m S → Matrices.ComplexMatrix2) :
    ReducedTuple L m S → ReducedTuple L m S
  | (A, v, w, σ, p, q, r) =>
    let W := firstMemberRestriction S Ω U
    (constrainedOp S Ω 𝔸 U A - covGradAt S Ω W (w + p) - currentTerm S Ω W J v -
        secondOrderOp S Ω W j (A - covGradAt S Ω W v),
      weightedSiteOp S Ω W v + w - covDivAt S Ω W A,
      weightedSiteOp S Ω W w - topSiteAdjoint S Ω W σ,
      topSiteValues S Ω W v,
      weightedSiteOp S Ω W p + topSiteAdjoint S Ω W r - siteSourceTerm S Ω W J j A v,
      p + weightedSiteOp S Ω W q,
      -topSiteValues S Ω W q)
end Operators
end SequenceTriples
end YangMills.Construction
end
