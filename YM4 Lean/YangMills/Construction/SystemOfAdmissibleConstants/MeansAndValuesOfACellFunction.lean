import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open ChessboardTori ReflectedCopies
open InfiniteLattice (periodicGibbsSet smearedEnergy)
def CellFunctionMeanBounds : Prop :=
  ∀ (D : ChessboardSetup) (A b : ℝ), 0 ≤ A → 0 ≤ b → CopyInequality D A b →
    ∀ (c : GridCell D) (ϱ : ℝ) (h : InfiniteLattice.AmbientSpace → ℝ), SupportedInCell c ϱ h →
      ∃ κ : ℝ,
        (∀ ν ∈ periodicGibbsSet D.L D.K D.β,
          |(∫ U, smearedEnergy h U ∂ν) - κ| ≤ copyBound A b c.side ϱ h) ∧
        (∀ m' : ℕ+, 2 * c.side ≤ PeriodicLattice.torusSide D.L m' →
          ‖torusAverage D m' (ReflectionsAndOneInsertion.complexSmeared D h) - (κ : ℂ)‖ ≤
            copyBound A b c.side ϱ h) ∧
        ∀ e : ℝ, |e - κ| ≤ copyBound A b c.side ϱ h →
          centredSmeared D h e ∈ ReflectionGrid.cellObservables (D := D) c.cell ∧
          ∀ m' : ℕ+, 2 * c.side ≤ PeriodicLattice.torusSide D.L m' →
            (c.grid.withExponent m').chessboardNormOfCell c.cell (centredSmeared D h e) ≤
              2 * copyBound A b c.side ϱ h
end YangMills.Construction.AdmissibleConstants
end
