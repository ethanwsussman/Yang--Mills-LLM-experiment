import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace QuotOrbits
def Claim : Prop :=
  ∀ A : PeriodicData, IsPeriodic A →
    (∀ (N : ℕ) (x y : A.Carrier),
      A.mkQuot N x = A.mkQuot N y ↔ ∃ v : Fin 4 → ℤ, y = A.translate (N • v) x) ∧
    ∀ N : ℕ, 0 < N → ∀ rep : A.QuotMod N → A.Carrier, (∀ q, A.mkQuot N (rep q) = q) →
      Function.Bijective fun p : A.QuotMod N × (Fin 4 → ℤ) => A.translate (N • p.2) (rep p.1)
end QuotOrbits
end YangMills.Construction.PeriodicOperators
end
