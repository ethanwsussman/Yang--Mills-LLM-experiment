import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set Matrices PeriodicLattice SeparatedSequences SeparatedRegions
noncomputable section
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def fieldDiff {α : Type*} [Sub α] (T : (FineBond L m S → ComplexMatrix2) → α)
    (W : FineBond L m S → ComplexMatrix2) : α :=
  T W - T trivialGaugeField
abbrev trivialForwardDiff (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (ν : Fin 4) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  covariantForwardDiff S Y P trivialGaugeField ν f x
abbrev trivialBackwardDiff (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (ν : Fin 4) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  covariantBackwardDiff S Y P trivialGaugeField ν f x
abbrev trivialFormDivergence (Y : Set (FourTorus L m))
    (X : FineBond L m S × Fin 4 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  formCovariantDivergence S Y trivialGaugeField X
abbrev trivialSourceEmbedding (g : SourceTuple L m S) : FullTuple L m S :=
  sourceEmbedding S Ω trivialGaugeField g
abbrev trivialReducedSourceEmbedding (g : ReducedSourceTuple L m S) : ReducedTuple L m S :=
  reducedSourceEmbedding S Ω trivialGaugeField g
def forwardTransportCoeff (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (x : SiteAtLevel L m S.levels 0) (a : ComplexMatrix2) : ComplexMatrix2 :=
  (((S.finestMesh L)⁻¹ : ℝ) : ℂ) • (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν)) a - a)
def backwardTransportCoeff (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (x : SiteAtLevel L m S.levels 0) (a : ComplexMatrix2) : ComplexMatrix2 :=
  (((S.finestMesh L)⁻¹ : ℝ) : ℂ) • (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν))⁻¹ a - a)
open Classical in
def transportFlux (P : Set (SiteAtLevel L m S.levels 0)) (U : FineBond L m S → ComplexMatrix2)
    (ν : Fin 4) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  if x + unitStep L m (levelDepth S.levels 0) ν ∈ P then
    forwardTransportCoeff S U ν x (f (x + unitStep L m (levelDepth S.levels 0) ν)) -
      backwardTransportCoeff S U ν x (f x)
  else 0
open Classical in
def transportDiagonal (P : Set (SiteAtLevel L m S.levels 0)) (U : FineBond L m S → ComplexMatrix2)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  -((((S.finestMesh L)⁻¹ : ℝ) : ℂ) •
    ((∑ ν : Fin 4, if x - unitStep L m (levelDepth S.levels 0) ν ∈ P then
        forwardTransportCoeff S U ν (x - unitStep L m (levelDepth S.levels 0) ν) (f x) else 0) +
      ∑ ν : Fin 4, if x + unitStep L m (levelDepth S.levels 0) ν ∈ P then
        backwardTransportCoeff S U ν x (f x) else 0))
def siteTransportFlux (Y : Set (FourTorus L m)) (U : FineBond L m S → ComplexMatrix2)
    (p : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun b =>
    transportFlux S (siteIndexSet S Y) U b.axis p b.source)
def formTransportFlux (Y : Set (FourTorus L m)) (U A : FineBond L m S → ComplexMatrix2) :
    FineBond L m S × Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S Y).indicator fun i =>
    transportFlux S (axisBaseSites S Y i.1.axis) U i.2
      (bondFormComponent A i.1.axis) i.1.source
def formTransportDiagonal (Y : Set (FourTorus L m)) (U A : FineBond L m S → ComplexMatrix2) :
    FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun b =>
    transportDiagonal S (axisBaseSites S Y b.axis) U
      (bondFormComponent A b.axis) b.source)
def formDirichletLap (Y : Set (FourTorus L m)) (W A : FineBond L m S → ComplexMatrix2) :
    FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun b =>
    componentDirichletCovariantLaplacian S Y W A b.axis b.source)
def compressedOpExcess (𝔸 : Set (FourTorus L m)) (U A : FineBond L m S → ComplexMatrix2) :
    FineBond L m S → ComplexMatrix2 :=
  compressedOp S Ω 𝔸 U A -
    formDirichletLap S (Ω 0) (firstMemberRestriction S Ω U) A
def topAveragingTerm (W : FineBond L m S → ComplexMatrix2)
    (l : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  layerValueAdjoint S Ω W
    (weightSmul S Ω (topWeight S Ω) (layerValueOnTops S Ω W l))
def siteOpDiff (W : FineBond L m S → ComplexMatrix2) :
    (SiteAtLevel L m S.levels 0 → ComplexMatrix2) → SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  fieldDiff S (dirichletLapAt S Ω) W +
    fieldDiff S (topAveragingTerm S Ω) W
def firstVariationMap (U : FineBond L m S → ComplexMatrix2)
    (w : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  -siteOpDiff S Ω (firstMemberRestriction S Ω U) w
def siteVariationMap (U : FineBond L m S → ComplexMatrix2) : SiteTriple L m S → SiteTriple L m S
  | (v, w, σ) =>
    let W := firstMemberRestriction S Ω U
    (-siteOpDiff S Ω W v,
      -siteOpDiff S Ω W w + fieldDiff S (topSiteAdjoint S Ω) W σ,
      -fieldDiff S (topSiteValues S Ω) W v)
def sourceCorrection (W : FineBond L m S → ComplexMatrix2) : SourceTuple L m S → SourceTuple L m S
  | (_, X₅) =>
    ((0, 0, 0, 0, fieldDiff S (covDivAt S Ω) W X₅, 0, 0, 0), 0)
def reducedSourceCorrection (W : FineBond L m S → ComplexMatrix2) :
    ReducedSourceTuple L m S → ReducedSourceTuple L m S
  | (_, X₅) =>
    ((0, 0, 0, 0, fieldDiff S (covDivAt S Ω) W X₅, 0, 0), 0)
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def rowAveragingTerm (W A : FineBond L m S → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  rowAverageTranspose S Ω W (spacingWeightSMul S (rowAverage S Ω W A))
def variationMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) : FullTuple L m S → SourceTuple L m S
  | (A, v, w, σ, p, q, r, ω) =>
    let W := firstMemberRestriction S Ω U
    ((-fieldDiff S (formDirichletLap S (Ω 0)) W A -
          compressedOpExcess S Ω 𝔸 U A -
          fieldDiff S (rowAveragingTerm S Ω) W A +
          fieldDiff S (covGradAt S Ω) W (w + p) + currentTerm S Ω W J v +
          secondOrderOp S Ω W j (A - covGradAt S Ω W v) +
          fieldDiff S (expansionValuesAdjoint S Ω) W ω,
        -siteOpDiff S Ω W v +
          fieldDiff S (covDivAt S Ω) W A,
        -siteOpDiff S Ω W w + fieldDiff S (topSiteAdjoint S Ω) W σ,
        -fieldDiff S (topSiteValues S Ω) W v,
        -transportDiagonal S (siteIndexSet S (Ω 0)) U p -
          fieldDiff S (topAveragingTerm S Ω) W p -
          fieldDiff S (topSiteAdjoint S Ω) W r +
          siteCurrentSource S Ω W J A v +
          fieldDiff S (covDivAt S Ω) W
            (bondCurrentSource S Ω W J j A v),
        -siteOpDiff S Ω W q,
        fieldDiff S (topSiteValues S Ω) W q,
        -fieldDiff S (expansionValuesOfForm S Ω) W A),
      -siteTransportFlux S (Ω 0) U p + bondCurrentSource S Ω W J j A v)
def reducedVariationMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) : ReducedTuple L m S → ReducedSourceTuple L m S
  | (A, v, w, σ, p, q, r) =>
    let W := firstMemberRestriction S Ω U
    ((-fieldDiff S (formDirichletLap S (Ω 0)) W A -
          compressedOpExcess S Ω 𝔸 U A -
          fieldDiff S (rowAveragingTerm S Ω) W A +
          fieldDiff S (covGradAt S Ω) W (w + p) + currentTerm S Ω W J v +
          secondOrderOp S Ω W j (A - covGradAt S Ω W v),
        -siteOpDiff S Ω W v +
          fieldDiff S (covDivAt S Ω) W A,
        -siteOpDiff S Ω W w + fieldDiff S (topSiteAdjoint S Ω) W σ,
        -fieldDiff S (topSiteValues S Ω) W v,
        -transportDiagonal S (siteIndexSet S (Ω 0)) U p -
          fieldDiff S (topAveragingTerm S Ω) W p -
          fieldDiff S (topSiteAdjoint S Ω) W r +
          siteCurrentSource S Ω W J A v +
          fieldDiff S (covDivAt S Ω) W
            (bondCurrentSource S Ω W J j A v),
        -siteOpDiff S Ω W q,
        fieldDiff S (topSiteValues S Ω) W q),
      -siteTransportFlux S (Ω 0) U p + bondCurrentSource S Ω W J j A v)
end Operators
end SequenceTriples
end
end YangMills.Construction
