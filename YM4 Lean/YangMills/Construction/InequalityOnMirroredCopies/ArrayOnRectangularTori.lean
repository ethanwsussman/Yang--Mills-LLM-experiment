import YangMills.Construction.ChessboardTori.ChessboardIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
variable {D : ChessboardSetup}
abbrev gridPeriods (g : ReflectionGrid D) (n : EvenIndexVector) : PeriodSubgroup D :=
  g.boxPeriods n.coord n.two_le
def tiledIntegral (g : ReflectionGrid D) (n : EvenIndexVector) (S : Set AmbientSpace)
    (F : D.GaugeField → ℂ) : ℂ :=
  ∫ U, (∏ k ∈ n.indexBox, g.transportTo S (g.cell k) F ((gridPeriods g n).liftGaugeField U)) *
      Complex.exp (-(D.β : ℂ) * ((gridPeriods g n).wilsonAction U : ℂ)) ∂(gridPeriods g n).haarMeasure
def torusPartition (g : ReflectionGrid D) (n : EvenIndexVector) : ℝ :=
  ∫ U, Real.exp (-D.β * (gridPeriods g n).wilsonAction U) ∂(gridPeriods g n).haarMeasure
def tiledMean (g : ReflectionGrid D) (n : EvenIndexVector) (S : Set AmbientSpace)
    (F : D.GaugeField → ℂ) : ℂ :=
  tiledIntegral g n S F / (torusPartition g n : ℂ)
def cellCount (n : EvenIndexVector) : ℕ := n.indexBox.card
def setTwo (n : EvenIndexVector) (μ : Fin 4) : EvenIndexVector where
  coord := Function.update n.coord μ 2
  two_le κ := by
    by_cases h : κ = μ
    · subst h
      simp
    · simpa [Function.update_of_ne h] using n.two_le κ
  even κ := by
    by_cases h : κ = μ
    · subst h
      simp
    · simpa [Function.update_of_ne h] using n.even κ
def cubicCounts (D : ChessboardSetup) (j : ℕ) : EvenIndexVector where
  coord _ := 2 * (D.L : ℤ) ^ j
  two_le _ := by
    have hL : 0 < (D.L : ℤ) := by
      have := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    have h : 1 ≤ (D.L : ℤ) ^ j := Int.add_one_le_iff.mpr (pow_pos hL _)
    omega
  even _ := even_two_mul _
abbrev minimalCounts (D : ChessboardSetup) : EvenIndexVector := cubicCounts D 0
def torusPartitionRatio (g : ReflectionGrid D) (j : ℕ) : ℝ :=
  torusPartition g (minimalCounts D) ^ (1 / 16 : ℝ) /
    torusPartition g (cubicCounts D j) ^ (1 / (cellCount (cubicCounts D j) : ℝ))
end ReflectedCopies
end YangMills.Construction
end
