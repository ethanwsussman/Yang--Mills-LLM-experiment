import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LogNormaliserIsFunctional
open PeriodicOperators.Tempered (IsLatticeFunctional)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLatticeFunctional L (logNormaliserFamily L k)
end YangMills.Construction.Tower.LogNormaliserIsFunctional
end
