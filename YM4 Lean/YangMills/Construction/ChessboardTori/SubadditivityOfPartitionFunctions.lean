import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
def scaleCoord (n : Fin 4 → ℤ) (μ : Fin 4) (j : ℕ) : Fin 4 → ℤ :=
  Function.update n μ ((j : ℤ) * n μ)
theorem two_le_scaleCoord {n : Fin 4 → ℤ} (hn : ∀ ν, 2 ≤ n ν) (μ : Fin 4) {j : ℕ} (hj : 1 ≤ j)
    (ν : Fin 4) : 2 ≤ scaleCoord n μ j ν := by
  by_cases h : ν = μ
  · subst h
    simp only [scaleCoord, Function.update_self]
    nlinarith [hn ν]
  · simpa [scaleCoord, Function.update_of_ne h] using hn ν
def PartitionFunctionSubmultiplicativity.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D) (W : AmbientSpace → ℂ), g.IsReflectionPeriodic W →
    (∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      W (x + TestFunctions.latticeTranslate (2 * g.cellSide) k) = W x) ∧
    (∀ (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ), (∀ μ, Even (n μ)) →
      (∀ x, ∀ v ∈ (g.boxPeriods n hn).subgroup, W (x + v) = W x) ∧
      ∀ (μ : Fin 4) (j : ℕ) (hj : 1 ≤ j),
        ((g.boxPeriods n hn).weightedPartition W).im = 0 ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).im = 0 ∧
        0 ≤ ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ≤
          ((g.boxPeriods n hn).weightedPartition W).re ^ j) ∧
    ∀ m' : ℕ+, PeriodicLattice.torusSide D.L m' ≤ PeriodicLattice.torusSide D.L D.m →
      2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
      (D.partitionFunctionOfPeriodic W).im = 0 ∧
      ((D.withExponent m').partitionFunctionOfPeriodic W).im = 0 ∧
      0 ≤ (D.partitionFunctionOfPeriodic W).re ∧
      (D.partitionFunctionOfPeriodic W).re ≤
        ((D.withExponent m').partitionFunctionOfPeriodic W).re ^
          ((PeriodicLattice.torusSide D.L D.m / PeriodicLattice.torusSide D.L m') ^ 4 : ℝ)
end ChessboardTori
end YangMills.Construction
end
