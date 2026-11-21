import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def ChessboardSetup.toGluingSetup (D : ChessboardSetup) (m' : ℕ+) (i : ℕ) :
    SourcesAndGluing.GluingSetup :=
  ⟨⟨D.L, D.isAdmissible, D.K, m'⟩, D.β, D.beta_pos, i⟩
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D) (m' : ℕ+) (i : ℕ)
def toCubicGrid (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) :
    SourcesAndGluing.CubicGrid (D.toGluingSetup m' i) where
  edge := g.cellSide
  isGridScale := h
  origin := g.origin
  origin_ne μ j hj := by
    obtain ⟨n, hn⟩ := g.origin_mem μ
    have e1 : D.mesh * ((n : ℝ) + 1 / 2) = D.mesh * (j : ℝ) := hn.symm.trans hj
    have e2 : (n : ℝ) + 1 / 2 = j := mul_left_cancel₀ D.mesh_pos.ne' e1
    have e3 : ((2 * n + 1 : ℤ) : ℝ) = ((2 * j : ℤ) : ℝ) := by
      push_cast
      linarith
    have e4 : 2 * n + 1 = 2 * j := by exact_mod_cast e3
    omega
def CubicGridObjectsAgree (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) : Prop :=
  (∀ k, (g.toCubicGrid m' i h).cube k = g.cell k) ∧
    (∀ μ n, (g.toCubicGrid m' i h).wall μ n = g.wall μ n) ∧
    (∀ k, (g.toCubicGrid m' i h).cubeAlgebra k = cellObservables (D := D) (g.cell k)) ∧
    (g.toCubicGrid m' i h).IsMirrorGrid ∧
    (g.toCubicGrid m' i h).toMirror = g.toCubicGrid m' i h
def CubicGridGroupAgrees (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) : Prop :=
  (fun r : Equiv.Perm (D.toGluingSetup m' i).Torus =>
      (r : (D.toGluingSetup m' i).Torus → (D.toGluingSetup m' i).Torus)) ''
      ((g.toCubicGrid m' i h).reflectionGroup : Set _) = (g.withExponent m').inducedTorusMaps ∧
    ∀ r ∈ (g.toCubicGrid m' i h).reflectionGroup,
      SourcesAndGluing.orientationSign r = (g.withExponent m').torusSign r
def ReflectionProductEqDescent (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) : Prop :=
  ∀ S ∈ g.cellSet, ∀ F ∈ cellObservables (D := D) S,
    (∀ U ∈ (D.toGluingSetup m' i).gaugeFields,
      (g.toCubicGrid m' i h).reflectionProduct F U =
        (D.toGluingSetup m' i).pullToTorus
          ((g.withExponent m').productOfTransports S (g.withExponent m').fundamentalBlock F) U) ∧
      (g.toCubicGrid m' i h).chessboardNorm F = g.normAtExponent m' S F
end ReflectionGrid
def ChessboardNormComparison.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D) (m' : ℕ+) (i : ℕ), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
    ((D.L : ℝ) ^ 2 * D.mesh ≤ g.cellSide → (D.toGluingSetup m' i).IsCellScale g.cellSide) ∧
    (¬ (D.L : ℝ) ^ 2 * D.mesh ≤ g.cellSide → (D.K : ℕ) = 1 ∧ g.cellSide = 1) ∧
    ∃ h : (D.toGluingSetup m' i).IsGridScale g.cellSide,
      g.CubicGridObjectsAgree m' i h ∧ g.CubicGridGroupAgrees m' i h ∧
        g.ReflectionProductEqDescent m' i h
end YangMills.Construction.ChessboardTori
end
