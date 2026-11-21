import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolAtPoint
def LinCombSymbol : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (A B : I'.Carrier → I.Carrier → ℂ) (z : Fin 4 → ℂ) (a b : ℂ),
      IsPeriodicKernel I I' A → SymbolSummableAt I I' A z →
      IsPeriodicKernel I I' B → SymbolSummableAt I I' B z →
        IsPeriodicKernel I I' (fun y x => a * A y x + b * B y x) ∧
        SymbolSummableAt I I' (fun y x => a * A y x + b * B y x) z ∧
        symbolHom I I' (fun y x => a * A y x + b * B y x) z =
          a • symbolHom I I' A z + b • symbolHom I I' B z
def CompSymbol : Prop :=
  ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
    ∀ (A : I'.Carrier → I.Carrier → ℂ) (B : I.Carrier → I''.Carrier → ℂ) (z : Fin 4 → ℂ),
      IsPeriodicKernel I I' A → SymbolSummableAt I I' A z →
      IsPeriodicKernel I'' I B → SymbolSummableAt I'' I B z →
        (∀ y w, CompSummableAt A B y w) ∧ IsPeriodicKernel I'' I' (compKernel A B) ∧
        SymbolSummableAt I'' I' (compKernel A B) z ∧
        symbolHom I'' I' (compKernel A B) z = (symbolHom I I' A z).comp (symbolHom I'' I B z)
def Claim : Prop := LinCombSymbol ∧ CompSymbol
end YangMills.Construction.PeriodicOperators.SymbolAtPoint
end
