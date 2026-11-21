import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def SlabRestrictionOfCellFunctions.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D) (m : SlabCount),
    2 * T.grid.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ((m : ℕ) : ℝ) = T.grid.cellsAcross →
    (∀ i, T.transverseCells i = ((m : ℕ) : ℤ)) →
    ∀ (k : Fin 4 → ℤ) (F : D.GaugeField → ℂ),
      F ∈ ReflectionGrid.cellObservables (D := D) (T.grid.cell k) →
      ∃ Ψ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Ψ ∧
        ∀ V : (T.torusPeriods m).GaugeConfig,
          F ((T.torusPeriods m).liftGaugeField V) =
            Ψ (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) V)
end YangMills.Construction.ChessboardTori
end
