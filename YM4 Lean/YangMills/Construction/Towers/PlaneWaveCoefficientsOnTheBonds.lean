import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def PlaneWaveEdgeCoefficientsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PlaneWaveCalculus.EdgeCoeffFacts L k
end YangMills.Construction.Tower
end
