import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeCohomology
def FlatConnectionIsPureGauge : Prop :=
  ∀ (G : Type) [Group G] (U : (Fin 4 → ℤ) → Fin 4 → G),
    (∀ x μ ν, μ < ν → U x μ * U (x + Pi.single μ 1) ν = U x ν * U (x + Pi.single ν 1) μ) →
    ∃ g : (Fin 4 → ℤ) → G, ∀ x i, U x i = g x * (g (x + Pi.single i 1))⁻¹
end YangMills.Construction.LatticeCohomology
end
