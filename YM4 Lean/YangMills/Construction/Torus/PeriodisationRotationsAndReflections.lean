import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrix TorusMetric PeriodicLattice
namespace PeriodicFunctions
variable {L m : ℕ}
def axisMirror (L m K : ℕ) (μ : Fin 4) (c : ℝ)
    (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * meshSize L (K : ℤ)) :
    InfiniteLattice.PeriodicMirror L m (K : ℤ) where
  axis := μ
  level := c
  level_mem := by
    obtain ⟨q, hq⟩ := hc
    exact ⟨q, by linarith⟩
def axisReflection (L m K : ℕ) (μ : Fin 4) (c : ℝ)
    (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * meshSize L (K : ℤ)) : FourTorus L m ≃ FourTorus L m :=
  (axisMirror L m K μ c hc).reflectEquiv
theorem axisReflection_torusProj (L m K : ℕ) (μ : Fin 4) (c : ℝ)
    (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * meshSize L (K : ℤ)) (x : Fin 4 → ℝ) :
    axisReflection L m K μ c hc (torusProj (torusSide L m) x) =
      torusProj (torusSide L m) (x - (2 * (x μ - c)) • Pi.single μ 1) :=
  (axisMirror L m K μ c hc).reflectEquiv_torusProj x
end PeriodicFunctions
end YangMills.Construction
