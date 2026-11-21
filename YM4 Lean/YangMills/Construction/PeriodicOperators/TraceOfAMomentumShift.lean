import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ShiftTrace
def TraceVanishes : Prop :=
  ∀ X : PeriodicData, IsPeriodic X →
    ∀ s, 0 < s → ∀ q ∈ dualLattice s, q ∉ RiemannSums.periodLattice →
      ∀ A : (X.QuotMod s → ℂ) →ₗ[ℂ] (X.QuotMod s → ℂ),
        (∀ k ∈ dualLattice s, ∀ g ∈ blochWaveSubspace X s k, A g ∈ blochWaveSubspace X s (k + q)) →
          LinearMap.trace ℂ (X.QuotMod s → ℂ) A = 0
end YangMills.Construction.PeriodicOperators.ShiftTrace
end
