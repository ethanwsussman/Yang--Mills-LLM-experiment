import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace SymbolPointwise
def Properties : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ), IsPeriodicKernel I I' T →
      SymbolSummableAt I I' T κ →
        (∀ κ' : Fin 4 → ℂ, imVec κ' = imVec κ → SymbolSummableAt I I' T κ') ∧
        FactorsThroughQuot (fourierSymbol I I' T κ) ∧
        (∀ i' i, carrierEntry (symbolHom I I' T κ) i' i = fourierSymbol I I' T κ i' i) ∧
        (∀ e : Fin 4 → ℤ, symbolHom I I' T (addTwoPiInt κ e) =
          (quotHomInverse (phaseMul I' e)).comp
            ((symbolHom I I' T κ).comp (phaseMul I e))) ∧
        (∀ e : Fin 4 → ℤ, quotHomNorm (symbolHom I I' T (addTwoPiInt κ e)) =
          quotHomNorm (symbolHom I I' T κ)) ∧
        IsPeriodicKernel I' I (kernelTranspose I I' T) ∧
        SymbolSummableAt I' I (kernelTranspose I I' T) (-κ) ∧
        quotSymbol I' I (kernelTranspose I I' T) (-κ) =
          quotTranspose I I' (quotSymbol I I' T κ)
end SymbolPointwise
end YangMills.Construction.PeriodicOperators
end
