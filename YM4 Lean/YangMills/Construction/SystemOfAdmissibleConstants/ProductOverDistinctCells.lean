import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open MeasureTheory ChessboardTori ReflectedCopies
open InfiniteLattice (periodicGibbsSet)
def DistinctCellProductBound : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → ∀ (n : ℕ) (k : Fin n → Fin 4 → ℤ),
    Function.Injective k → ∀ (F : Fin n → D.GaugeField → ℂ) (q : Fin n → ℝ),
      (∀ i, F i ∈ ReflectionGrid.cellObservables (D := D) (g.cell (k i))) →
      (∀ i, ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
        (g.withExponent m').chessboardNormOfCell (g.cell (k i)) (F i) ≤ q i) →
      (∀ ν ∈ periodicGibbsSet D.L D.K D.β, ‖∫ U, ∏ i, F i U ∂ν‖ ≤ ∏ i, q i) ∧
      ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
        Function.Injective (fun i => (D.withExponent m').proj '' g.cell (k i)) →
        ‖torusAverage D m' (fun U => ∏ i, F i U)‖ ≤ ∏ i, q i
end YangMills.Construction.AdmissibleConstants
end
