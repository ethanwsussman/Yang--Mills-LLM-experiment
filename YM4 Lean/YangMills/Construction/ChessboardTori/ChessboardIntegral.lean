import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.CouplingAndGrid
import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
structure EvenIndexVector where
  coord : Fin 4 → ℤ
  two_le : ∀ i, 2 ≤ coord i
  even : ∀ i, Even (coord i)
namespace EvenIndexVector
def indexBox (n : EvenIndexVector) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun i => Finset.Ico 0 (n.coord i)
theorem update_mem_indexBox (n : EvenIndexVector) {j : Fin 4 → ℤ} (hj : j ∈ n.indexBox) (μ : Fin 4)
    {k : ℤ} (hk : k ∈ Finset.Ico 0 (n.coord μ)) : Function.update j μ k ∈ n.indexBox := by
  rw [indexBox, Fintype.mem_piFinset] at hj ⊢
  intro i
  by_cases h : i = μ
  · subst h
    simpa using hk
  · simpa [Function.update_of_ne h] using hj i
end EvenIndexVector
namespace CoupledGrid
variable (O : CoupledGrid)
def periodSubgroupOf (n : EvenIndexVector) : PeriodSubgroup O.toChessboardSetup :=
  O.grid.boxPeriods n.coord n.two_le
def IsCellFamily (n : EvenIndexVector)
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  ∀ k ∈ n.indexBox, F k ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) (O.grid.cell k)
def cellFamilyIntegral (n : EvenIndexVector)
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : ℂ :=
  ∫ U, (∏ k ∈ n.indexBox, F k ((O.periodSubgroupOf n).liftGaugeField U)) *
      Complex.exp (-(O.β : ℂ) * ((O.periodSubgroupOf n).wilsonAction U : ℂ))
      ∂(O.periodSubgroupOf n).haarMeasure
def chessboardPartitionOn (n : EvenIndexVector) (S : Set InfiniteLattice.AmbientSpace)
    (F : O.toChessboardSetup.GaugeField → ℂ) : ℂ :=
  ∫ U, (∏ k ∈ n.indexBox, O.grid.transportTo S (O.grid.cell k) F
        ((O.periodSubgroupOf n).liftGaugeField U)) *
      Complex.exp (-(O.β : ℂ) * ((O.periodSubgroupOf n).wilsonAction U : ℂ))
      ∂(O.periodSubgroupOf n).haarMeasure
theorem chessboardPartitionOn_eq_cellFamilyIntegral (n : EvenIndexVector)
    (S : Set InfiniteLattice.AmbientSpace) (F : O.toChessboardSetup.GaugeField → ℂ) :
    O.chessboardPartitionOn n S F =
      O.cellFamilyIntegral n fun k => O.grid.transportTo S (O.grid.cell k) F :=
  rfl
def diagonalCounts : EvenIndexVector where
  coord _ := O.grid.cellsPerTorusSide
  two_le _ := by
    have hL : 0 < (O.L : ℤ) := by
      have := O.toChessboardSetup.isAdmissible.2
      exact_mod_cast (by omega : 0 < O.L)
    have h : 1 ≤ (O.L : ℤ) ^ (((O.m : ℕ) : ℤ) - O.grid.q).toNat :=
      Int.add_one_le_iff.mpr (pow_pos hL _)
    simp only [ReflectionGrid.cellsPerTorusSide]
    omega
  even _ := even_two_mul _
def chessboardPartition (S : Set InfiniteLattice.AmbientSpace)
    (F : O.toChessboardSetup.GaugeField → ℂ) : ℂ :=
  O.chessboardPartitionOn O.diagonalCounts S F
end CoupledGrid
end ChessboardTori
end YangMills.Construction
end
