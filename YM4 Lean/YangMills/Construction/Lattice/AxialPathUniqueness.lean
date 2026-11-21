import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
def AxialPathUniqueness : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ j : ℤ, -(m : ℤ) ≤ j →
  ∀ (x x' : Site L m j) (μ μ' : Fin 4) (n n' : ℤ),
    IsAxialDisplacement x x' μ n → IsAxialDisplacement x x' μ' n' →
      flowAlong x μ n = flowAlong x μ' n' ∧ axialPath x x' = flowAlong x μ n
end YangMills.Construction.PeriodicLattice
