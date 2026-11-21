import YangMills.Construction.HoleBesideASecondHole.LinesAndStripsOfALatticeField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace LatticeGauge
def FlatGaugeOnBoxBoundary : Prop :=
  ∀ (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi : Fin 4 → ℤ) (M : ℕ) (e : ℝ),
    (∀ i, lo i + 2 ≤ hi i ∧ hi i - lo i ≤ M) → 0 ≤ e →
    (∀ a μ ν, μ ≠ ν → a ∈ boxBoundary lo hi → a + unitVec μ ∈ boxBoundary lo hi →
      a + unitVec ν ∈ boxBoundary lo hi → a + unitVec μ + unitVec ν ∈ boxBoundary lo hi →
      ‖((plaquetteHolonomy X a μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e) →
    ∃ γ : (Fin 4 → ℤ) → UnitQuaternion, ∀ a i, a ∈ boxBoundary lo hi → a + unitVec i ∈ boxBoundary lo hi →
      ‖((γ a * X a i * (γ (a + unitVec i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 40 * (M : ℝ) ^ 2 * e
end LatticeGauge
end YangMills.Construction
end
