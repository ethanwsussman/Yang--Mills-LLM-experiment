import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace TorusAction
def Claim : Prop :=
  ∀ I J : PeriodicData, IsPeriodic I → IsPeriodic J → ∀ s : ℕ, 1 ≤ s →
    ∀ T : J.Carrier → I.Carrier → ℂ, IsPeriodicKernel I J T →
      (∀ f : I.Carrier → ℂ, (∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) →
        (∀ (n : Fin 4 → ℤ) i, f (I.translate (s • n) i) = f i) →
          (∀ j, ApplySummableAt T f j) ∧
          (∀ (n : Fin 4 → ℤ) j, applyKernel T f (J.translate (s • n) j) = applyKernel T f j) ∧
          ∀ g : I.QuotMod s → ℂ, (∀ i, g (I.mkQuot s i) = f i) → ∀ j,
            applyKernel (periodicMatrix I J T s) g (J.mkQuot s j) = applyKernel T f j) ∧
      ∀ K : PeriodicData, IsPeriodic K → ∀ S : I.Carrier → K.Carrier → ℂ,
        IsPeriodicKernel K I S →
          periodicMatrix K J (compKernel T S) s =
            compKernel (periodicMatrix I J T s) (periodicMatrix K I S s)
end TorusAction
end PeriodicOperators
end YangMills.Construction
end
