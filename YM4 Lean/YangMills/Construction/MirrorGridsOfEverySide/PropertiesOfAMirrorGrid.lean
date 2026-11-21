import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.ChessboardTori (ReflectionGrid orientationSign)
noncomputable section
namespace YangMills.Construction
namespace MirrorGridsAllSides
def wallLevel {D : GridSetup} (g : ReflectionGrid D) (μ : Fin 4) (k : ℤ) : ℝ :=
  g.origin μ + k * g.cellSide
def torusWallReflection {D : GridSetup} (g : ReflectionGrid D) (μ : Fin 4) (s : ℤ) :
    D.Torus → D.Torus :=
  (D.mirrors μ).reflect (wallLevel g μ s)
def IsStarHomOn {X Y : Type*} (T : (X → ℂ) → Y → ℂ) (A : Set (X → ℂ)) (Q : Set Y) : Prop :=
  ∀ F ∈ A, ∀ F' ∈ A, ∀ c : ℂ,
    EqOn (T (F + F')) (T F + T F') Q ∧
    EqOn (T fun U => c * F U) (fun U => c * T F U) Q ∧
    EqOn (T (F * F')) (T F * T F') Q ∧
    EqOn (T (conjFun F)) (conjFun (T F)) Q
section Requirements
variable {D : GridSetup} (g : ReflectionGrid D)
def CellSideOddMultiple : Prop :=
  (∃ m : ℤ, Odd m ∧ g.cellSide / D.mesh = m) ∧ (D.L : ℝ) ^ 2 ≤ g.cellSide / D.mesh
def WallsBisectLinks : Prop :=
  ∀ (μ : Fin 4) (k : ℤ),
    g.wall μ k = {x : AmbientSpace | x μ = wallLevel g μ k} ∧
    (D.mirrors μ).IsLinkLevel (wallLevel g μ k) ∧
    (∃ P : InfiniteLattice.LatticeMirror D.mesh, P.cls = .axial μ ∧
      P.plane = g.wall μ k ∧ P.BisectsLinks) ∧
    (∀ x ∈ D.gridPoints, x ∉ g.wall μ k) ∧
    (∀ b : D.Link,
      (segment ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace) ∩ g.wall μ k).Nonempty →
      ((b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = D.mesh • Pi.single μ 1 ∨
        (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = (-D.mesh) • Pi.single μ 1) ∧
      segment ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace) ∩ g.wall μ k =
        {midpoint ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace)}) ∧
    ∃ r : D.LatticeSym, r.toFun = (D.mirrors μ).reflectVec (wallLevel g μ k)
def CellCentresInLattice : Prop :=
  (∀ k, g.cellCentre k ∈ D.gridPoints) ∧
    ∀ x ∈ D.gridPoints, ∃! G : Set (Set AmbientSpace),
      ∃ g' : ReflectionGrid D, g'.cellSide = g.cellSide ∧ g'.cellSet = G ∧ ∃ k, g'.cellCentre k = x
def ReflectionGroupActsOnCells : Prop :=
  (∀ r ∈ g.reflectionGroup,
    (∃ s : D.LatticeSym, s.toFun = r) ∧
    (∃ ε : Fin 4 → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
      ChessboardTori.HasLinearComponent r (Matrix.toLin' (Matrix.diagonal ε))) ∧
    BijOn (fun S => r '' S) g.cellSet g.cellSet) ∧
  (∀ k k' : Fin 4 → ℤ, ∃! r : g.reflectionGroup, r.1 '' g.cell k = g.cell k') ∧
  (∀ (k k' : Fin 4 → ℤ) (r : g.reflectionGroup), r.1 '' g.cell k = g.cell k' →
    orientationSign r.1 = (-1 : ℤˣ) ^ (∑ μ, (k' μ - k μ))) ∧
  (∀ r s : g.reflectionGroup, orientationSign (r * s).1 = orientationSign r.1 * orientationSign s.1) ∧
  ∀ t : Fin 4 → ℤ, ∃ r : g.reflectionGroup,
    (r.1 : AmbientSpace → AmbientSpace) = ChessboardTori.translate (fun μ => 2 * g.cellSide * t μ) ∧
      g.IsEvenElement r
def TorusCellStructure : Prop :=
  (∃ m : ℤ, Even m ∧ g.cellsAcross = m) ∧
  (∀ k, InjOn D.proj (g.cell k)) ∧
  (∀ k k' : Fin 4 → ℤ, D.proj '' g.cell k = D.proj '' g.cell k' ↔
    ∃ j : Fin 4 → ℤ, ∀ μ, ((k μ - k' μ : ℤ) : ℝ) = g.cellsAcross * j μ) ∧
  (Nat.card g.torusCellSet : ℝ) = g.cellNumber ∧
  ∀ k k' : Fin 4 → ℤ, D.proj '' g.cell k = D.proj '' g.cell k' →
    D.proj '' interior (g.cell k) = D.proj '' interior (g.cell k') ∧
    g.torusCellInterior (D.proj '' g.cell k) = D.proj '' interior (g.cell k) ∧
    g.torusCellCentre k = g.torusCellCentre k'
def TorusGroupActsOnCells : Prop :=
  (∀ r ∈ g.reflectionGroup, ∃ s : D.TorusSymmetry, D.Descends r s.toFun) ∧
  (∀ (r s : g.reflectionGroup) (r' s' : D.Torus → D.Torus), D.Descends r.1 r' → D.Descends s.1 s' →
    (r' = s' ↔ ∃ t : g.reflectionGroup, g.IsEvenElement t ∧ r = t * s ∧
      ∃ k : Fin 4 → ℤ, (t.1 : AmbientSpace → AmbientSpace) =
        ChessboardTori.translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k))) ∧
  (∃ H : Subgroup (Equiv.Perm D.Torus),
    (fun e : Equiv.Perm D.Torus => (e : D.Torus → D.Torus)) '' (H : Set (Equiv.Perm D.Torus)) =
      g.inducedTorusMaps) ∧
  (∀ r' ∈ g.inducedTorusMaps, g.HasTorusParity r' (g.torusSign r')) ∧
  (∀ r' ∈ g.inducedTorusMaps, ∀ s' ∈ g.inducedTorusMaps,
    g.torusSign (r' ∘ s') = g.torusSign r' * g.torusSign s') ∧
  (∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet, ∃! r', r' ∈ g.inducedTorusMaps ∧ r' '' C = C') ∧
  (Nat.card g.inducedTorusMaps : ℝ) = g.cellNumber ∧
  ∀ ε : ℤˣ,
    (Nat.card {r' // r' ∈ g.inducedTorusMaps ∧ g.torusSign r' = ε} : ℝ) = g.cellNumber / 2
def TorusWallReflections : Prop :=
  ∀ (μ : Fin 4) (s : ℤ),
    D.Descends (g.reflect μ s) (torusWallReflection g μ s) ∧
    {y | torusWallReflection g μ s y = y} = (D.mirrors μ).mirrorSet (wallLevel g μ s) ∧
    (∃ P ∈ g.torusWallFamily, ∃ P' ∈ g.torusWallFamily, P ≠ P' ∧
      (D.mirrors μ).mirrorSet (wallLevel g μ s) = P ∪ P') ∧
    (∀ (k : Fin 4 → ℤ) (i : ℤ), 0 ≤ i → (i : ℝ) ≤ g.cellsAcross - 1 →
      (∃ j : ℤ, ((k μ - s - i : ℤ) : ℝ) = g.cellsAcross * j) →
      ((i : ℝ) ≤ g.cellsAcross / 2 - 1 → D.proj '' interior (g.cell k) ⊆
        (D.mirrors μ).openSlab (wallLevel g μ s) .pos) ∧
      (g.cellsAcross / 2 ≤ (i : ℝ) → D.proj '' interior (g.cell k) ⊆
        (D.mirrors μ).openSlab (wallLevel g μ s) .neg)) ∧
    (∀ k : Fin 4 → ℤ, torusWallReflection g μ s '' (D.proj '' g.cell k) =
      D.proj '' g.cell (Function.update k μ (2 * s - 1 - k μ))) ∧
    torusWallReflection g μ s ∈ g.inducedTorusMaps ∧ g.torusSign (torusWallReflection g μ s) = -1
def ActsOnCellObservables : Prop :=
  (∀ (r s : g.reflectionGroup) (F : D.GaugeField → ℂ),
    (g.toLatticeSym (r * s)).actOn F =
      (g.toLatticeSym r).actOn ((g.toLatticeSym s).actOn F)) ∧
  ∀ (r : g.reflectionGroup), ∀ S ∈ g.cellSet,
    (g.toLatticeSym r).actOn '' ChessboardTori.ReflectionGrid.cellObservables (D := D) S =
      ChessboardTori.ReflectionGrid.cellObservables (D := D) (r.1 '' S) ∧
    IsStarHomOn (g.toLatticeSym r).actOn
      (ChessboardTori.ReflectionGrid.cellObservables (D := D) S) univ
def TransportLaws : Prop :=
  ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∀ S'' ∈ g.cellSet,
    ∀ F ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D) S,
      g.transportTo S S' F ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D) S' ∧
      g.transportTo S S F = F ∧
      g.transportTo S' S'' (g.transportTo S S' F) = g.transportTo S S'' F ∧
      (∀ r : g.reflectionGroup, g.transportTo S (r.1 '' S') F =
        Conventions.signedConjFun (orientationSign r.1)
          ((g.toLatticeSym r).actOn (g.transportTo S S' F))) ∧
      (∀ F' ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D) S,
        g.transportTo S S' (F + F') = g.transportTo S S' F + g.transportTo S S' F' ∧
        g.transportTo S S' (F * F') = g.transportTo S S' F * g.transportTo S S' F') ∧
      g.transportTo S S' (conjFun F) = conjFun (g.transportTo S S' F) ∧
      ∀ (r : g.reflectionGroup) (c : ℂ), g.transportTo S (r.1 '' S) (fun U => c * F U) =
        fun U => Conventions.signedConj (orientationSign r.1) c * g.transportTo S (r.1 '' S) F U
def TorusActsOnCellObservables : Prop :=
  (∀ r' ∈ g.inducedTorusMaps, ∀ s' ∈ g.inducedTorusMaps,
    ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
    EqOn (D.pullbackObservable (r' ∘ s') F)
      (D.pullbackObservable r' (D.pullbackObservable s' F)) D.torusFields) ∧
  ∀ r' ∈ g.inducedTorusMaps, ∀ C ∈ g.torusCellSet,
    D.pullbackObservable r' '' g.torusCellObservables C = g.torusCellObservables (r' '' C) ∧
    IsStarHomOn (D.pullbackObservable r') (g.torusCellObservables C) D.torusFields
def TorusTransportLaws : Prop :=
  ∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet, ∀ C'' ∈ g.torusCellSet,
    ∀ F ∈ g.torusCellObservables C,
      g.torusTransportTo C C' F ∈ g.torusCellObservables C' ∧
      EqOn (g.torusTransportTo C C F) F D.torusFields ∧
      EqOn (g.torusTransportTo C' C'' (g.torusTransportTo C C' F)) (g.torusTransportTo C C'' F)
        D.torusFields ∧
      (∀ r' ∈ g.inducedTorusMaps, EqOn (g.torusTransportTo C (r' '' C') F)
        (Conventions.signedConjFun (g.torusSign r')
          (D.pullbackObservable r' (g.torusTransportTo C C' F))) D.torusFields) ∧
      (∀ F' ∈ g.torusCellObservables C,
        EqOn (g.torusTransportTo C C' (F + F'))
          (g.torusTransportTo C C' F + g.torusTransportTo C C' F') D.torusFields ∧
        EqOn (g.torusTransportTo C C' (F * F'))
          (g.torusTransportTo C C' F * g.torusTransportTo C C' F') D.torusFields) ∧
      EqOn (g.torusTransportTo C C' (conjFun F)) (conjFun (g.torusTransportTo C C' F))
        D.torusFields ∧
      (∀ r' ∈ g.inducedTorusMaps, ∀ c : ℂ,
        EqOn (g.torusTransportTo C (r' '' C) (fun U => c * F U))
        (fun U => Conventions.signedConj (g.torusSign r') c * g.torusTransportTo C (r' '' C) F U)
        D.torusFields) ∧
      EqOn (g.cellProduct C' (g.torusTransportTo C C' F)) (g.cellProduct C F) D.torusFields
def LiftCompatibleWithTransport : Prop :=
  ∀ S ∈ g.cellSet, ∀ F ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D) S,
    D.liftedObservable F ∈ g.torusCellObservables (D.proj '' S) ∧
    (∀ (r : g.reflectionGroup) (r' : D.Torus → D.Torus), D.Descends r.1 r' →
      EqOn (D.liftedObservable ((g.toLatticeSym r).actOn F))
        (D.pullbackObservable r' (D.liftedObservable F)) D.torusFields) ∧
    ∀ S' ∈ g.cellSet, EqOn (D.liftedObservable (g.transportTo S S' F))
      (g.torusTransportTo (D.proj '' S) (D.proj '' S') (D.liftedObservable F))
      D.torusFields
def WallPreservingSymmetries : Prop :=
  (∀ s : D.TorusSymmetry,
    (fun P => s.toFun '' P) '' g.torusWallFamily = g.torusWallFamily →
      BijOn (fun C => s.toFun '' C) g.torusCellSet g.torusCellSet ∧
      (∀ C ∈ g.torusCellSet, GridSetup.TorusSymmetry.precompose s '' g.torusCellObservables C =
        g.torusCellObservables (s.toFun '' C)) ∧
      BijOn (fun t => s.toFun ∘ t ∘ Function.invFun s.toFun) g.inducedTorusMaps
        g.inducedTorusMaps ∧
      ∀ t ∈ g.inducedTorusMaps,
        g.torusSign (s.toFun ∘ t ∘ Function.invFun s.toFun) = g.torusSign t) ∧
  ∀ r' ∈ g.inducedTorusMaps, ∃ s : D.TorusSymmetry, s.toFun = r' ∧
    (fun P => s.toFun '' P) '' g.torusWallFamily = g.torusWallFamily
def CoarseningOnSpace (g' : ReflectionGrid D) (k₀ : ℕ) : Prop :=
  (∀ S' ∈ g'.cellSet,
    S' = ⋃₀ {S | S ∈ g.cellSet ∧ S ⊆ S'} ∧
    {S | S ∈ g.cellSet ∧ S ⊆ S'}.ncard = D.L ^ (4 * k₀) ∧
    ∀ S ∈ g.cellSet, S ⊆ S' → ChessboardTori.ReflectionGrid.cellObservables (D := D) S ⊆
      ChessboardTori.ReflectionGrid.cellObservables (D := D) S') ∧
  g'.reflectionGroup ≤ g.reflectionGroup
def CoarseningOnTorus (g' : ReflectionGrid D) (k₀ : ℕ) : Prop :=
  (∀ C' ∈ g'.torusCellSet,
    C' = ⋃₀ {C | C ∈ g.torusCellSet ∧ C ⊆ C'} ∧
    {C | C ∈ g.torusCellSet ∧ C ⊆ C'}.ncard = D.L ^ (4 * k₀) ∧
    ∀ C ∈ g.torusCellSet, C ⊆ C' → g.torusCellObservables C ⊆ g'.torusCellObservables C') ∧
  g'.inducedTorusMaps ⊆ g.inducedTorusMaps ∧
  (∀ r' ∈ g'.inducedTorusMaps, g'.torusSign r' = g.torusSign r') ∧
  (∀ C' ∈ g'.torusCellSet, ∀ C₁ ∈ g.torusCellSet,
    ∃! p : (D.Torus → D.Torus) × Set D.Torus,
      p.1 ∈ g'.inducedTorusMaps ∧ p.2 ∈ g.torusCellSet ∧ p.2 ⊆ C' ∧ p.1 '' p.2 = C₁) ∧
  ∀ C' ∈ g'.torusCellSet, ∀ r' ∈ g'.inducedTorusMaps, ∀ C ∈ g.torusCellSet, C ⊆ C' →
    ∀ F ∈ g.torusCellObservables C,
      EqOn (g'.torusTransportTo C' (r' '' C') F) (g.torusTransportTo C (r' '' C) F) D.torusFields
def FiniteCellsInCoarserCell : Prop :=
  ∀ O : Set (Set AmbientSpace), O.Finite → O ⊆ g.cellSet →
    ∃ g' : ReflectionGrid D, g'.HasAdmissibleSide ∧ g'.IsCoarsening g ∧
      ∃ S' ∈ g'.cellSet, ∀ S ∈ O, S ⊆ S'
end Requirements
end MirrorGridsAllSides
end YangMills.Construction
end
