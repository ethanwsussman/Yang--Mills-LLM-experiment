import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealAnalyticity
open Coordinates.ComplexCoordinates
def CoordRealAnalyticIffAnalytic : Prop :=
  ∀ (N : ℕ) (D : Set (Coordinates.ComplexCoordinates N)) (G : Coordinates.ComplexCoordinates N → ℂ),
    D ⊆ realLocus N →
    (IsRealAnalyticIn (N' := 1) D (fun z _ => G z) ↔
      IsOpen ((fun (u : Fin N → ℝ) (j : Fin N) => (u j : ℂ)) ⁻¹' D) ∧
        AnalyticOnNhd ℝ (fun u : Fin N → ℝ => G fun j => (u j : ℂ))
          ((fun (u : Fin N → ℝ) (j : Fin N) => (u j : ℂ)) ⁻¹' D))
end YangMills.Construction.RealAnalyticity
