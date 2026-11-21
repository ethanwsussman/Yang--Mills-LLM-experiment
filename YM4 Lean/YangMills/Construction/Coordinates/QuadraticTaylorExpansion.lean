import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
namespace YangMills.Construction.Coordinates.QuadraticTaylor
def IsSecondOrderExpansion {l : ℕ} (h : ComplexCoordinates l → ℂ)
    (φ : ComplexCoordinates l →ₗ[ℂ] ℂ)
    (β : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ) : Prop :=
  (∀ z z' : ComplexCoordinates l, β z z' = β z' z) ∧
    (fun z : ComplexCoordinates l => h z - (h 0 + φ z + (1 / 2 : ℂ) * β z z))
      =O[𝓝 0] fun z : ComplexCoordinates l => ‖z‖ ^ 3
def UniqueExpansion : Prop :=
  ∀ (l : ℕ) (ρ : ℝ), 0 < ρ → ∀ h : ComplexCoordinates l → ℂ,
    ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk 0 ρ)
      (fun z _ => h z) →
    ∃! p : (ComplexCoordinates l →ₗ[ℂ] ℂ) ×
        (ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion h p.1 p.2
end YangMills.Construction.Coordinates.QuadraticTaylor
