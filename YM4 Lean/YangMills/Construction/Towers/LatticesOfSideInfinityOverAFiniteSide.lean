import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.FullLatticeOverTorus
open InfiniteLattice (AmbientSpace)
open Tower
open PeriodicOperators (castVec intShift shiftEdge shiftFace)
abbrev periodLattice (L n : ℕ) : AddSubgroup AmbientSpace :=
  InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L n)
abbrev torusQuotient (L n : ℕ) : AmbientSpace → PeriodicLattice.FourTorus L n :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L n)
def fundamentalCube (L n : ℕ) : Set AmbientSpace :=
  {y | ∀ μ, y μ ∈ Ico 0 (PeriodicLattice.torusSide L n)}
def PeriodsInSublattice (L n k j : ℕ) : Prop :=
  InfiniteLattice.latticeSubgroup 1 ≤ InfiniteLattice.latticeSubgroup (meshAt L k j) ∧
    periodLattice L n ≤ InfiniteLattice.latticeSubgroup (meshAt L k j)
def TorusQuotientMapsVerticesAndEdges (L n k j : ℕ) : Prop :=
  torusQuotient L n '' (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) =
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) ∧
    ∀ e : FullSpace.Edge L k j, ∃ e' : Edge L n k j,
      (e'.source : PeriodicLattice.FourTorus L n) = torusQuotient L n e.initial ∧
      (e'.target : PeriodicLattice.FourTorus L n) = torusQuotient L n e.terminal ∧
      (e.IsPositivelyOriented → e'.IsPositivelyOriented)
def ShiftSurjectiveOnVertices (L k j : ℕ) (m : Fin 4 → ℤ) : Prop :=
  FullSpace.MapsSublatticeOnto (meshAt L k j) (intShift m) ∧
    ∀ x : FullSpace.Vertex L k j,
      ((FullSpace.vertexImage (intShift m) x : FullSpace.Vertex L k j) : AmbientSpace) =
        x + castVec m
def ShiftSurjectiveOnEdges (L k j : ℕ) (m : Fin 4 → ℤ) : Prop :=
  Function.Surjective (shiftEdge m : PeriodicOperators.PosEdge L k j → _) ∧
    ∀ e : PeriodicOperators.PosEdge L k j,
      ((shiftEdge m e).1.initial : AmbientSpace) = e.1.initial + castVec m ∧
      ((shiftEdge m e).1.terminal : AmbientSpace) = e.1.terminal + castVec m
def ShiftSurjectiveOnFaces (L k j : ℕ) (m : Fin 4 → ℤ) : Prop :=
  Function.Surjective (shiftFace m : FullSpace.Face L k j → _) ∧
    ∀ f : FullSpace.Face L k j,
      ((shiftFace m f).corner : AmbientSpace) = f.corner + castVec m ∧
      (shiftFace m f).lowAxis = f.lowAxis ∧
      (shiftFace m f).highAxis = f.highAxis ∧
      intShift m '' ((↑) '' FullSpace.faceCorners f : Set AmbientSpace) =
        (↑) '' FullSpace.faceCorners (shiftFace m f)
def LocallyFiniteCells (L k j : ℕ) : Prop :=
  ∀ S : Set AmbientSpace, Bornology.IsBounded S →
    {x : FullSpace.Vertex L k j | (x : AmbientSpace) ∈ S}.Finite ∧
    {e : PeriodicOperators.PosEdge L k j | (e.1.initial : AmbientSpace) ∈ S}.Finite ∧
    {f : FullSpace.Face L k j | (f.corner : AmbientSpace) ∈ S}.Finite
def LocallyFiniteEdgesAtVertex (L k j : ℕ) : Prop :=
  ∀ x : FullSpace.Vertex L k j,
    {e : FullSpace.Edge L k j | e.initial = x ∨ e.terminal = x}.Finite
def ShiftedFromFundamentalCube (L n k j : ℕ) : Prop :=
  (∀ x : FullSpace.Vertex L k j, ∃ (y : FullSpace.Vertex L k j) (m : Fin 4 → ℤ),
    (y : AmbientSpace) ∈ fundamentalCube L n ∧ castVec m ∈ periodLattice L n ∧
      FullSpace.vertexImage (intShift m) y = x) ∧
  (∀ e : PeriodicOperators.PosEdge L k j,
    ∃ (e₀ : PeriodicOperators.PosEdge L k j) (m : Fin 4 → ℤ),
      (e₀.1.initial : AmbientSpace) ∈ fundamentalCube L n ∧ castVec m ∈ periodLattice L n ∧
        shiftEdge m e₀ = e) ∧
  (∀ f : FullSpace.Face L k j, ∃ (f₀ : FullSpace.Face L k j) (m : Fin 4 → ℤ),
    (f₀.corner : AmbientSpace) ∈ fundamentalCube L n ∧ castVec m ∈ periodLattice L n ∧
      shiftFace m f₀ = f)
def TorusQuotientPeriodic (L n : ℕ) : Prop :=
  ∀ x v : AmbientSpace, v ∈ periodLattice L n → torusQuotient L n (x + v) = torusQuotient L n x
def FullLatticeOverTorusClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k → ∀ n : ℕ, 0 < n →
    PeriodsInSublattice L n k j ∧
    TorusQuotientMapsVerticesAndEdges L n k j ∧
    (∀ m : Fin 4 → ℤ, ShiftSurjectiveOnVertices L k j m ∧ ShiftSurjectiveOnEdges L k j m ∧
      ShiftSurjectiveOnFaces L k j m) ∧
    LocallyFiniteCells L k j ∧
    LocallyFiniteEdgesAtVertex L k j ∧
    ShiftedFromFundamentalCube L n k j ∧
    TorusQuotientPeriodic L n
end YangMills.Construction.FullLatticeOverTorus
end
