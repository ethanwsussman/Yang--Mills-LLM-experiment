import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def cellOffsetVector (k : Fin 4 → ℤ) : AmbientSpace := fun μ => g.cellSide * k μ
theorem cellOffsetVector_mem (k : Fin 4 → ℤ) : g.cellOffsetVector k ∈ D.gridPoints :=
  ⟨fun μ => g.cellRatio * k μ, fun μ => by
    simp only [cellOffsetVector, g.cellSide_eq]
    push_cast
    ring⟩
def cellOffsetPoint (k : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨g.cellOffsetVector k, g.cellOffsetVector_mem k⟩
def sparseCells (q : ℕ) : Set (Set AmbientSpace) :=
  g.cell '' {k | (∀ μ, 0 ≤ k μ ∧ (k μ : ℝ) ≤ g.cellsAcross - 1) ∧ ∀ μ, 2 * (q : ℤ) ∣ k μ}
end ReflectionGrid
def PeriodicStatesAndGridTranslations.Statement : Prop :=
  ∀ (D : ChessboardSetup) (ν : Measure D.GaugeField), ν ∈ D.periodicStates →
    (∃ Γ : AddSubgroup (InfiniteLattice.LatticePoint D.mesh), Γ.FiniteIndex ∧
      ∀ v ∈ Γ, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)) ∧
    ∀ (Γ : AddSubgroup (InfiniteLattice.LatticePoint D.mesh)) (q : ℕ), Γ.FiniteIndex →
      Γ.index = q →
      (∀ v ∈ Γ, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)) →
      ∀ g : ReflectionGrid D, g.IsCoarse →
        ((∀ v : InfiniteLattice.LatticePoint D.mesh, q • v ∈ Γ) ∧
          ∀ v : InfiniteLattice.LatticePoint D.mesh,
            InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift (q • v))) ∧
        (∀ k : Fin 4 → ℤ, (∀ μ, 2 * (q : ℤ) ∣ k μ) →
          ∃ r : g.reflectionGroup, (r.1 : AmbientSpace → AmbientSpace) = translate (g.cellOffsetVector k) ∧
            orientationSign r.1 = 1 ∧
            ∀ r' : g.reflectionGroup, r'.1 '' g.baseCell = g.cell k ↔ r' = r) ∧
        (∀ k : Fin 4 → ℤ, (∀ μ, 2 * (q : ℤ) ∣ k μ) →
          g.cellOffsetPoint k ∈ Γ ∧
            InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift (g.cellOffsetPoint k))) ∧
        ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
          (g.withExponent m').sparseCells q ⊆
              (g.withExponent m').cellsWithin (g.withExponent m').fundamentalBlock ∧
            ((g.withExponent m').sparseCells q).Finite ∧
            ((g.withExponent m').cellsAcross / (2 * q)) ^ 4 ≤
              (((g.withExponent m').sparseCells q).ncard : ℝ)
end YangMills.Construction.ChessboardTori
end
