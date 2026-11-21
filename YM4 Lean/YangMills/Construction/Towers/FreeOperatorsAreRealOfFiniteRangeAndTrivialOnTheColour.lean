import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FreeOperatorsRealLocal
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PlaneWaveCalculus.FreeOpsRealFiniteRange L k
end YangMills.Construction.Tower.FreeOperatorsRealLocal
end
