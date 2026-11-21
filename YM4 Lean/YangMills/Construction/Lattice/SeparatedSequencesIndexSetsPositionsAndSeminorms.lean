import YangMills.Construction.Lattice.BareLatticeSpacesAndOperators
import YangMills.Construction.Lattice.CoordinateCombs
import YangMills.Construction.Lattice.FlatDeterminingSetOfASeparatedSequence
import YangMills.Construction.Lattice.HoelderSeminormsAtAScale
import YangMills.Construction.Lattice.SeparatedSequenceInLastUnits
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedSequences.BondKinds YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedRegions
variable {L m : ℕ} (S : SeparatedSequences.ScaleData)
def IsSeparatedWithGap (g : ℝ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (L : ℝ) ^ 2 ≤ g ∧ (∀ n ≤ S.top, IsBlockUnion S n (Ω n)) ∧
    ∀ n < S.top, Ω (n + 1) ⊆ Ω n ∧
      ENNReal.ofReal (g * S.levelMesh L n) <
        supDistInLevelUnits S.levels S.unitLevel
          (complementRegion (S.blockPartitionIndex n) (Ω n)) (Ω (n + 1))
abbrev regionSiteSpace (Y : Set (FourTorus L m)) :
    Set (SiteAtLevel L m S.levels 0 → ComplexMatrix2) :=
  Bare.siteSpace Y
abbrev regionBondFormSpace (Y : Set (FourTorus L m)) :
    Set (FineBond L m S → ComplexMatrix2) :=
  Bare.bondFormSpace Y
def cubeOfPoint (Ω : ℕ → Set (FourTorus L m)) (y : FourTorus L m) : Set (FourTorus L m) :=
  ⋃ z ∈ {z : SiteAtLevel L m S.levels (layerLevel S Ω y) | (z : FourTorus L m) = y},
    siteBlock S z
def enlargedCube (Ω : ℕ → Set (FourTorus L m)) (y : FourTorus L m) : Set (FourTorus L m) :=
  closedSupCube y (3 / 2 * meshSize L (levelDepth S.levels (layerLevel S Ω y)))
def AreAdjacentPoints (Ω : ℕ → Set (FourTorus L m)) (y z : FourTorus L m) : Prop :=
  y ∈ layerPoints S Ω ∧ z ∈ layerPoints S Ω ∧
    (cubeOfPoint S Ω y ∩ cubeOfPoint S Ω z).Nonempty
abbrev LeveledBond (L m : ℕ) (S : SeparatedSequences.ScaleData) : Type :=
  Σ j : ℕ, BondAtLevel L m S.levels j
def siteIndexSet (Y : Set (FourTorus L m)) : Set (SiteAtLevel L m S.levels 0) := sitesIn Y
def bondIndexSet (Y : Set (FourTorus L m)) : Set (FineBond L m S) := positiveBondsInside S Y
def bondAxisIndexSet (Y : Set (FourTorus L m)) : Set (FineBond L m S × Fin 4) :=
  {i | i.1 ∈ bondIndexSet S Y}
def leveledIndexSet (Ω : ℕ → Set (FourTorus L m)) : Set (LeveledBond L m S) :=
  {q | q ∈ interiorOutwardSet S Ω ∧ q.2.IsPositivelyOriented}
def pointFunctionSpace (Ω : ℕ → Set (FourTorus L m)) : Set (FourTorus L m → ComplexMatrix2) :=
  {f | (∀ y, f y ∈ complexLieAlgebra) ∧ ∀ y ∉ layerPoints S Ω, f y = 0}
def leveledFunctionSpace (Ω : ℕ → Set (FourTorus L m)) :
    Set (LeveledBond L m S → ComplexMatrix2) :=
  {f | (∀ q, f q ∈ complexLieAlgebra) ∧ ∀ q ∉ leveledIndexSet S Ω, f q = 0}
def siteLocation (Ω : ℕ → Set (FourTorus L m)) (x : SiteAtLevel L m S.levels 0) :
    FourTorus L m :=
  Classical.epsilon fun y => y ∈ layerPoints S Ω ∧ (x : FourTorus L m) ∈ cubeOfPoint S Ω y
def bondLocation (Ω : ℕ → Set (FourTorus L m)) (b : FineBond L m S) : FourTorus L m :=
  siteLocation S Ω b.source
def bondAxisLocation (Ω : ℕ → Set (FourTorus L m)) (i : FineBond L m S × Fin 4) :
    FourTorus L m :=
  bondLocation S Ω i.1
def leveledLocation (Ω : ℕ → Set (FourTorus L m)) (q : LeveledBond L m S) : FourTorus L m :=
  open Classical in
  if q.2.source ∈ layerLatticeSites S Ω q.1 then (q.2.source : FourTorus L m)
  else (q.2.target : FourTorus L m)
def bondAxisAnchor (i : FineBond L m S × Fin 4) : FourTorus L m := i.1.centre
def leveledAnchor (q : LeveledBond L m S) : FourTorus L m := q.2.centre
def localMax {ι : Type*} (I : Set ι) (loc : ι → FourTorus L m) (f : ι → ComplexMatrix2)
    (y : FourTorus L m) : ℝ≥0∞ :=
  ⨆ i ∈ I, ⨆ _ : loc i = y, ENNReal.ofReal (ComplexMatrix2.operatorNorm (f i))
def scaledLocalMax {ι : Type*} (Ω : ℕ → Set (FourTorus L m)) (I : Set ι)
    (loc : ι → FourTorus L m) (s : ℝ) (f : ι → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  ENNReal.ofReal (layerPointMesh S Ω y ^ (-s)) * localMax I loc f y
def forwardNeighbourTerm (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  open Classical in
  if x + unitStep L m (levelDepth S.levels 0) ν ∈ P ∧
      Bond.forwardFrom x ν ∈ (bondsInside Y : Set (FineBond L m S)) then
    ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν))
      (f (x + unitStep L m (levelDepth S.levels 0) ν))
  else 0
def backwardNeighbourTerm (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  open Classical in
  if x - unitStep L m (levelDepth S.levels 0) ν ∈ P ∧
      Bond.forwardFrom (x - unitStep L m (levelDepth S.levels 0) ν) ν ∈
        (bondsInside Y : Set (FineBond L m S)) then
    ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m (levelDepth S.levels 0) ν) ν))⁻¹
      (f (x - unitStep L m (levelDepth S.levels 0) ν))
  else 0
def covariantForwardDiff (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  (((S.finestMesh L)⁻¹ : ℝ) : ℂ) • (forwardNeighbourTerm S Y P U ν f x - P.indicator f x)
def covariantBackwardDiff (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  (((S.finestMesh L)⁻¹ : ℝ) : ℂ) • (backwardNeighbourTerm S Y P U ν f x - P.indicator f x)
def covariantLaplacianOn (Y : Set (FourTorus L m)) (P : Set (SiteAtLevel L m S.levels 0))
    (U : FineBond L m S → ComplexMatrix2) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  ((((S.finestMesh L)⁻¹) ^ 2 : ℝ) : ℂ) • ((8 : ℂ) • P.indicator f x -
    ∑ ν : Fin 4, (forwardNeighbourTerm S Y P U ν f x + backwardNeighbourTerm S Y P U ν f x))
def axisBaseSites (Y : Set (FourTorus L m)) (μ : Fin 4) : Set (SiteAtLevel L m S.levels 0) :=
  {x | Bond.forwardFrom x μ ∈ (bondsInside Y : Set (FineBond L m S))}
def formCovariantGradient (Y : Set (FourTorus L m)) (U A : FineBond L m S → ComplexMatrix2) :
    FineBond L m S × Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S Y).indicator fun i =>
    covariantForwardDiff S Y (axisBaseSites S Y i.1.axis) U i.2
      (bondFormComponent A i.1.axis) i.1.source
def formCovariantHessian (Y : Set (FourTorus L m)) (U : FineBond L m S → ComplexMatrix2)
    (X : FineBond L m S × Fin 4 → ComplexMatrix2) :
    FineBond L m S × Fin 4 → Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S Y).indicator fun i ν =>
    covariantForwardDiff S Y (axisBaseSites S Y i.1.axis) U ν
      (fun z => X (Bond.forwardFrom z i.1.axis, i.2)) i.1.source
def formCovariantDivergence (Y : Set (FourTorus L m)) (U : FineBond L m S → ComplexMatrix2)
    (X : FineBond L m S × Fin 4 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun b =>
    ∑ ν : Fin 4, covariantBackwardDiff S Y (axisBaseSites S Y b.axis) U ν
      (fun z => X (Bond.forwardFrom z b.axis, ν)) b.source)
def componentDirichletCovariantLaplacian (Y : Set (FourTorus L m))
    (U A : FineBond L m S → ComplexMatrix2) (μ : Fin 4) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  covariantLaplacianOn S Y (axisBaseSites S Y μ) U (bondFormComponent A μ) x
def transportedHoelderRatio (Ω : ℕ → Set (FourTorus L m)) (β : ℝ)
    (U : FineBond L m S → ComplexMatrix2) (y : FourTorus L m) (x z : SiteAtLevel L m S.levels 0)
    (v w : ComplexMatrix2) : ℝ≥0∞ :=
  ENNReal.ofReal ((layerPointMesh S Ω y / unitL1Dist S (x : FourTorus L m) z) ^ β *
    ComplexMatrix2.operatorNorm
      (ComplexMatrix2.conjugateBy (pathHolonomy U (coordinateComb x z)) w - v))
def localHoelder {ι : Type*} (Ω : ℕ → Set (FourTorus L m)) (I : Set ι)
    (anchor : ι → FourTorus L m) (origin : ι → SiteAtLevel L m S.levels 0)
    (alike : ι → ι → Prop) (β : ℝ) (U : FineBond L m S → ComplexMatrix2)
    (f : ι → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  ⨆ i ∈ I, ⨆ j ∈ I,
    ⨆ _ : i ≠ j ∧ alike i j ∧ anchor i ∈ enlargedCube S Ω y ∧ anchor j ∈ enlargedCube S Ω y,
      transportedHoelderRatio S Ω β U y (origin i) (origin j) (f i) (f j)
def enlargedCubeSup {ι : Type*} (Ω : ℕ → Set (FourTorus L m)) (I : Set ι)
    (anchor : ι → FourTorus L m) (f : ι → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  ⨆ i ∈ I, ⨆ _ : anchor i ∈ enlargedCube S Ω y,
    ENNReal.ofReal (ComplexMatrix2.operatorNorm (f i))
def scaledLocalHoelder {ι : Type*} (Ω : ℕ → Set (FourTorus L m)) (I : Set ι)
    (anchor : ι → FourTorus L m) (origin : ι → SiteAtLevel L m S.levels 0)
    (alike : ι → ι → Prop) (β s : ℝ) (U : FineBond L m S → ComplexMatrix2)
    (f : ι → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  ENNReal.ofReal (layerPointMesh S Ω y ^ (-s)) *
    (enlargedCubeSup S Ω I anchor f y + localHoelder S Ω I anchor origin alike β U f y)
def IsParallelBond (b c : FineBond L m S) : Prop := b.target - b.source = c.target - c.source
def IsParallelAxisIndex (i j : FineBond L m S × Fin 4) : Prop :=
  IsParallelBond S i.1 j.1 ∧ i.2 = j.2
abbrev bondScaledLocalHoelder (Ω : ℕ → Set (FourTorus L m)) (β s : ℝ)
    (U f : FineBond L m S → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  scaledLocalHoelder S Ω (bondIndexSet S (Ω 0)) Bond.centre Bond.source (IsParallelBond S)
    β s U f y
abbrev bondAxisScaledLocalHoelder (Ω : ℕ → Set (FourTorus L m)) (β s : ℝ)
    (U : FineBond L m S → ComplexMatrix2) (f : FineBond L m S × Fin 4 → ComplexMatrix2)
    (y : FourTorus L m) : ℝ≥0∞ :=
  scaledLocalHoelder S Ω (bondAxisIndexSet S (Ω 0)) (bondAxisAnchor S) (fun i => i.1.source)
    (IsParallelAxisIndex S) β s U f y
end YangMills.Construction.SeparatedRegions
