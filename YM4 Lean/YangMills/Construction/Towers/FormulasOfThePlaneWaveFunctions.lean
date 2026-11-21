import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaveSymbolFormulas
def Holds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PlaneWaveCalculus.SymbolFormulas L k
end PlaneWaveSymbolFormulas
end Tower
end YangMills.Construction
end
