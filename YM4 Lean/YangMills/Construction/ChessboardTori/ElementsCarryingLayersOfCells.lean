import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def LayerCarryingElements.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D) (m : SlabCount),
    2 * T.grid.cellSide ≤ PeriodicLattice.torusSide D.L D.m → ((m : ℕ) : ℝ) = T.grid.cellsAcross →
    (∀ ν, T.transverseCells ν = ((m : ℕ) : ℤ)) →
    ∀ j j' : ℤ, ∃ (r : T.grid.reflectionGroup)
        (s : (T.torusPeriods m).GaugeConfig → (T.torusPeriods m).GaugeConfig),
      (∀ k : Fin 4 → ℤ, r.1 '' T.grid.cell (Function.update k T.axis j) =
        T.grid.cell (Function.update k T.axis j')) ∧
      orientationSign r.1 = (j' - j).negOnePow ∧
      (∀ U, (T.grid.toLatticeSym r).pullbackField
          ((T.torusPeriods m).liftGaugeField U) =
        (T.torusPeriods m).liftGaugeField (s U)) ∧
      ∀ U, T.slabRestriction m ((j : ℤ) : ZMod (m : ℕ)) (s U) =
        if Even (j' - j) then T.slabRestriction m ((j' : ℤ) : ZMod (m : ℕ)) U
        else T.slabReverse (T.slabRestriction m ((j' : ℤ) : ZMod (m : ℕ)) U)
end YangMills.Construction.ChessboardTori
end
