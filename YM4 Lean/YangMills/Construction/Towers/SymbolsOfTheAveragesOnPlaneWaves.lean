import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaveSmoothingSymbols
def SmoothingSymbolsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PlaneWaveCalculus.SmoothingSymbols L k
end PlaneWaveSmoothingSymbols
end Tower
end YangMills.Construction
end
