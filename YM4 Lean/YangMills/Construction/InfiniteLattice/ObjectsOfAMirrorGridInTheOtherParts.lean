import YangMills.Construction.ChessboardTori.ChessboardValueWhereTheSideVaries
import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.InfiniteLattice.MirrorGridsCopiesAndChessboardValuesOfMultipleReflections
import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (AmbientSpace)
namespace Setup
variable (D : Setup)
abbrev toChessboardSetup : ChessboardTori.ChessboardSetup := ⟨D.toStandingParameters, D.β, D.β_pos⟩
abbrev toGluingSetup (i : ℕ) : SourcesAndGluing.GluingSetup := ⟨D.toStandingParameters, D.β, D.β_pos, i⟩
abbrev liftToLinks (F : D.GaugeField → ℂ) :
    (D.toChessboardSetup.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  D.toChessboardSetup.liftedObservable F
abbrev coveringMap : AmbientSpace → D.Torus := D.projection
namespace Grid
variable {D} (G : D.Grid)
def edgeExp : ℤ := G.edge_admissible.1.choose
theorem edge_eq_zpow_edgeExp : G.edge = (D.L : ℝ) ^ G.edgeExp := G.edge_admissible.1.choose_spec
theorem two_sub_K_le_edgeExp : 2 - ((D.K : ℕ) : ℤ) ≤ G.edgeExp := by
  have hedge := G.isTileEdge_edge
  rw [G.edge_eq_zpow_edgeExp] at hedge
  exact (D.isTileEdge_zpow_iff _).1 hedge
def toChessboardGrid : ChessboardTori.ReflectionGrid D.toChessboardSetup where
  q := G.edgeExp
  one_sub_K_le_q := by
    have hexp := G.two_sub_K_le_edgeExp
    change 1 - ((D.K : ℕ) : ℤ) ≤ G.edgeExp
    omega
  origin := G.shift
  origin_mem := G.shift_mem
theorem cellSide_toChessboardGrid : G.toChessboardGrid.cellSide = G.edge :=
  G.edge_eq_zpow_edgeExp.symm
theorem two_mul_cellSide_le_torusSide (hfit : 2 * G.edge ≤ D.side) :
    2 * G.toChessboardGrid.cellSide ≤ PeriodicLattice.torusSide D.L D.m := by
  rw [G.cellSide_toChessboardGrid]
  exact hfit
theorem isGridScale_edge (i : ℕ) (hfit : 2 * G.edge ≤ D.side) :
    (D.toGluingSetup i).IsGridScale G.edge := by
  refine ⟨⟨G.edgeExp, G.edge_eq_zpow_edgeExp⟩, ?_, ?_⟩
  · have hlow := G.isTileEdge_edge.2
    have hL := D.one_lt_L
    have hmesh : 0 < D.mesh := (D.toGluingSetup i).mesh_pos
    have hsq : D.mesh ≤ (D.L : ℝ) ^ 2 * D.mesh := le_mul_of_one_le_left hmesh.le (one_le_pow₀ hL.le)
    exact hsq.trans hlow
  · change G.edge ≤ D.side / 2
    linarith
def toCubicGrid (i : ℕ) (hfit : 2 * G.edge ≤ D.side) : SourcesAndGluing.CubicGrid (D.toGluingSetup i) where
  edge := G.edge
  isGridScale := G.isGridScale_edge i hfit
  origin := G.shift
  origin_ne μ n hn := by
    obtain ⟨p, hp⟩ := G.shift_mem μ
    have hne : (D.toGluingSetup i).mesh ≠ 0 := (D.toGluingSetup i).mesh_pos.ne'
    have heq : (D.toGluingSetup i).mesh * ((p : ℝ) + 1 / 2) = (D.toGluingSetup i).mesh * n := hp.symm.trans hn
    have hcancel : (p : ℝ) + 1 / 2 = n := mul_left_cancel₀ hne heq
    have hcast : ((2 * p + 1 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by
      push_cast
      linarith
    have hint : 2 * p + 1 = 2 * n := by exact_mod_cast hcast
    omega
def tileObservables (k : Fin 4 → ℤ) : Set (D.GaugeField → ℂ) :=
  SetLike.coe (InfiniteLattice.ReflectionGrid.tileAlgebra G k)
def torusImage (D : Setup) (S : Set AmbientSpace) : Set D.Torus := D.coveringMap '' S
def ChessboardObjectsAgree : Prop :=
  G.toChessboardGrid.cellSide = G.edge ∧ G.toChessboardGrid.origin = G.shift ∧
  (∀ (μ : Fin 4) (n : ℤ), G.toChessboardGrid.wall μ n = G.wall μ n) ∧
  (fun r : Equiv.Perm AmbientSpace => (r : AmbientSpace → AmbientSpace)) '' (G.toChessboardGrid.reflectionGroup : Set _) =
    (fun r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace => (r : AmbientSpace → AmbientSpace)) ''
      (InfiniteLattice.ReflectionGrid.reflectionGroup G : Set _) ∧
  (∀ (r : G.toChessboardGrid.reflectionGroup) (r' : InfiniteLattice.ReflectionGrid.reflectionGroup G),
    ((r.1 : Equiv.Perm AmbientSpace) : AmbientSpace → AmbientSpace) =
      ((r'.1 : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) →
      (((ChessboardTori.orientationSign r.1 : ℤˣ) : ℤ) : ℝ) = InfiniteLattice.ReflectionGrid.orientation G r') ∧
  (∀ k : Fin 4 → ℤ, G.toChessboardGrid.cell k = G.tile k) ∧
  (∀ k : Fin 4 → ℤ, interior (G.toChessboardGrid.cell k) = G.tileInterior k) ∧
  (∀ k : Fin 4 → ℤ, ChessboardTori.ReflectionGrid.cellObservables (D := D.toChessboardSetup)
    (G.toChessboardGrid.cell k) = G.tileObservables k) ∧
  ∀ (k k' : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
    G.toChessboardGrid.transportTo (G.toChessboardGrid.cell k) (G.toChessboardGrid.cell k') F =
      G.reflectedCopy k k' F
def GluingObjectsAgree (i : ℕ) (hfit : 2 * G.edge ≤ D.side) : Prop :=
  (D.toGluingSetup i).IsCellScale G.edge ∧
  (G.toCubicGrid i hfit).edge = G.edge ∧ (G.toCubicGrid i hfit).origin = G.shift ∧
  (G.toCubicGrid i hfit).toMirror = G.toCubicGrid i hfit ∧
  (∀ k : Fin 4 → ℤ, (G.toCubicGrid i hfit).cube k = G.tile k) ∧
  ∀ k : Fin 4 → ℤ, (G.toCubicGrid i hfit).cubeAlgebra k = G.tileObservables k
def TorusCellsEqImages (i : ℕ) (hfit : 2 * G.edge ≤ D.side) : Prop :=
  G.toChessboardGrid.torusCellSet = torusImage D '' G.tiling ∧
  range (G.toCubicGrid i hfit).torusCube = torusImage D '' G.tiling ∧
  (∀ S S' : Set AmbientSpace, G.AreCongruent S S' → torusImage D S = torusImage D S') ∧
  BijOn (torusImage D) G.boxTiles (torusImage D '' G.tiling)
def LiftsCommuteWithCopies : Prop :=
  ∀ (k k' : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
    D.liftToLinks F ∈ G.toChessboardGrid.torusCellObservables (torusImage D (G.tile k)) ∧
    ∀ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      D.liftToLinks (G.reflectedCopy k k' F) U.1 =
        G.toChessboardGrid.torusTransportTo (torusImage D (G.tile k)) (torusImage D (G.tile k'))
          (D.liftToLinks F) U.1
def ProductLiftsToTorus (hfit : 2 * G.edge ≤ D.side) : Prop :=
  ∀ (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
    (∀ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      D.liftToLinks (G.reflectedProduct k F) U.1 =
        G.toChessboardGrid.torusProduct (D.liftToLinks F) U.1) ∧
    ∃ (hC : torusImage D (G.tile k) ∈ G.toChessboardGrid.torusCellSet)
      (hF : D.liftToLinks F ∈
        G.toChessboardGrid.torusCellObservables (torusImage D (G.tile k))),
      G.chessboardNorm k F =
        G.toChessboardGrid.torusChessboardNormAtSide (G.two_mul_cellSide_le_torusSide hfit) hC
          (D.liftToLinks F) hF
def TorusGroupInduced (i : ℕ) (hfit : 2 * G.edge ≤ D.side) : Prop :=
  (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
      ((G.toCubicGrid i hfit).reflectionGroup : Set _) =
    {r' : D.Torus → D.Torus | PeriodicLattice.IsTorusIsometry r' ∧
      ∃ r ∈ InfiniteLattice.ReflectionGrid.reflectionGroup G, D.coveringMap ∘ r = r' ∘ D.coveringMap} ∧
  ∀ r' ∈ (G.toCubicGrid i hfit).reflectionGroup, ∀ r : InfiniteLattice.ReflectionGrid.reflectionGroup G,
    D.coveringMap ∘ (r.1 : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) = r' ∘ D.coveringMap →
      (((SourcesAndGluing.orientationSign (D := D.toGluingSetup i) r' : ℤˣ) : ℤ) : ℝ) =
        InfiniteLattice.ReflectionGrid.orientation G r
def GluingNormAgrees (i : ℕ) (hfit : 2 * G.edge ≤ D.side) : Prop :=
  ∀ (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
    (D.toGluingSetup i).pullToTorus F = D.liftToLinks F ∧
    (∀ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      (G.toCubicGrid i hfit).reflectionProduct F U.1 = D.liftToLinks (G.reflectedProduct k F) U.1) ∧
    (G.toCubicGrid i hfit).chessboardNorm F = G.chessboardNorm k F
def EstimateNormAgrees : Prop :=
  ∀ (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileObservables k →
    G.toChessboardGrid.chessboardExpectation (G.toChessboardGrid.cell k) (G.toChessboardGrid.block 0) F =
      D.torusExpectation (G.reflectedProduct k F) ∧
    G.toChessboardGrid.chessboardNorm (G.toChessboardGrid.cell k) F = G.chessboardNorm k F ∧
    (1 ≤ G.edge → G.toChessboardGrid.IsCoarse ∧
      G.toChessboardGrid.normAtExponent D.m (G.toChessboardGrid.cell k) F = G.chessboardNorm k F)
end Grid
end Setup
end YangMills.Construction.MultipleReflections
end
