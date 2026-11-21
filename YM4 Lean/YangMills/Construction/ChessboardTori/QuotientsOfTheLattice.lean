import YangMills.Construction.ChessboardTori.StandingConventions
import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def gridVector (n : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨fun μ => (n μ : ℝ) * D.mesh, n, fun _ => rfl⟩
def periodLengths (s : Fin 4 → ℤ) (μ : Fin 4) : ℝ := (s μ : ℝ) * D.mesh
def periodGroup (s : Fin 4 → ℤ) : AddSubgroup AmbientSpace :=
  BoxTorus.periods (D.periodLengths s)
theorem periodGroup_le_gridPoints (s : Fin 4 → ℤ) : D.periodGroup s ≤ D.gridPoints := by
  intro x hx
  have hcoord : ∀ μ, ∃ k : ℤ, k • D.periodLengths s μ = x μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hx) μ (mem_univ μ))
  choose k hk using hcoord
  refine ⟨fun μ => k μ * s μ, fun μ => ?_⟩
  rw [← hk μ, periodLengths, zsmul_eq_mul]
  push_cast
  ring
def periodSubgroupOfGrid (s : Fin 4 → ℤ) : AddSubgroup (InfiniteLattice.LatticePoint D.mesh) :=
  (D.periodGroup s).comap D.gridPoints.subtype
def signedAxisStep {G : Type} [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G)
    (ε : ℤˣ) (μ : Fin 4) : G :=
  (ε : ℤ) • q (InfiniteLattice.axisStep D.mesh μ)
def nearNeighbourhood {G : Type} [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G) :
    Option (ℤˣ × Fin 4) → G
  | none => 0
  | some (ε, μ) => D.signedAxisStep q ε μ
def faceVertices {G : Type} [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G) (x : G)
    (μ ν : Fin 4) : Fin 4 → G :=
  ![x, x + D.signedAxisStep q 1 μ, x + D.signedAxisStep q 1 μ + D.signedAxisStep q 1 ν,
    x + D.signedAxisStep q 1 ν]
def QuotientRegularity {G : Type} [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G) :
    Prop :=
  (∀ n : Fin 4 → ℤ, n ≠ 0 → (∀ μ, |n μ| ≤ 3) → q (D.gridVector n) ≠ 0) ∧
  (Function.Injective (D.nearNeighbourhood q) ∧
    (∀ (x x' : G) (ε ε' : ℤˣ) (μ μ' : Fin 4), x' - x = D.signedAxisStep q ε μ →
      x' - x = D.signedAxisStep q ε' μ' → ε = ε' ∧ μ = μ') ∧
    ∀ (x x' : G) (ε : ℤˣ) (μ : Fin 4), x' - x = D.signedAxisStep q ε μ →
      x - x' = D.signedAxisStep q (-ε) μ ∧
        Xor (∃ ν, x' - x = D.signedAxisStep q 1 ν) (∃ ν, x - x' = D.signedAxisStep q 1 ν)) ∧
  ((∀ (x : G) (μ ν : Fin 4), μ < ν → Function.Injective (D.faceVertices q x μ ν)) ∧
    ∀ (x x' : G) (μ ν μ' ν' : Fin 4), μ < ν → μ' < ν' →
      range (D.faceVertices q x μ ν) = range (D.faceVertices q x' μ' ν') →
        x = x' ∧ μ = μ' ∧ ν = ν')
def periodicDistance (s : Fin 4 → ℤ) (y y' : AmbientSpace) : ℝ :=
  sInf ((fun v : AmbientSpace => TorusMetric.euclidNormVec (y - y' + v)) ''
    (D.periodGroup s : Set AmbientSpace))
end ChessboardSetup
def LatticeQuotients.Statement : Prop :=
  ∀ (D : ChessboardSetup) (s : Fin 4 → ℤ), (∀ μ, 4 ≤ s μ) →
    (∀ (G : Type) [AddCommGroup G] (q : InfiniteLattice.LatticePoint D.mesh →+ G),
      Function.Surjective q →
      (q.ker = D.periodSubgroupOfGrid s ∨ q.ker = ⊥) → D.QuotientRegularity q) ∧
    ((∀ y y' : AmbientSpace, IsLeast
        ((fun v : AmbientSpace => TorusMetric.euclidNormVec (y - y' + v)) ''
          (D.periodGroup s : Set AmbientSpace)) (D.periodicDistance s y y')) ∧
      (∀ y₁ y₂ y₁' y₂' : AmbientSpace, y₁ - y₂ ∈ D.periodGroup s → y₁' - y₂' ∈ D.periodGroup s →
        D.periodicDistance s y₁ y₁' = D.periodicDistance s y₂ y₂') ∧
      ∀ y y' : AmbientSpace, D.periodicDistance s y y' = 0 → y - y' ∈ D.periodGroup s) ∧
    (Nat.card (InfiniteLattice.LatticePoint D.mesh ⧸ D.periodSubgroupOfGrid s) : ℤ) = ∏ μ, s μ
end ChessboardTori
end YangMills.Construction
end
