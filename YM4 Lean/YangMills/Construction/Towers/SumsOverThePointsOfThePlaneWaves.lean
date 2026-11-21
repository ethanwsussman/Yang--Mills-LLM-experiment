import YangMills.Construction.Towers.PlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace PlaneWaveSums
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ ϰ : Fin 4 → ℝ,
    (∀ μ : Fin 4, ∑ m ∈ PlaneWaves.freqBox L k,
      ‖PlaneWaves.edgeWeight L k (PlaneWaves.shiftedFreq (fun ν => (ϰ ν : ℂ)) m) μ‖ ^ 2 ≤ 1) ∧
    ∑ m ∈ PlaneWaves.freqBox L k,
      PlaneWaves.vertexWeight L k (PlaneWaves.shiftedFreq (fun ν => (ϰ ν : ℂ)) m) ^ 2 = 1
end PlaneWaveSums
end YangMills.Construction.Tower
end
