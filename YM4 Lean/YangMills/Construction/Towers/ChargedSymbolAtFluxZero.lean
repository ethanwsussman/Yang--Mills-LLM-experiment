import YangMills.Construction.Towers.ChargedFormOfTheConstantFieldDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def ChargedSymbolFluxZeroClaim : Prop :=
  ∀ q : InfiniteLattice.AmbientSpace,
    chargedSymbolExplicit 0 q =
      Massive.latticeSymbol (PeriodicOperators.toComplexVec q) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)
end YangMills.Construction.Tower.ConstantFieldSymbols
end
