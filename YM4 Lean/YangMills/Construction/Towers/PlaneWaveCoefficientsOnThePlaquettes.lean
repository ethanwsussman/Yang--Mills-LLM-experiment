import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaveCalculus
def FaceCoeffsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → FaceCoeffFacts L k
end PlaneWaveCalculus
end Tower
end YangMills.Construction
end
