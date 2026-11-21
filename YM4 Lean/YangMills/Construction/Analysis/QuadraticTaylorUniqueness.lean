import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
namespace YangMills.Construction.Taylor
def QuadraticTaylorUniqueness : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →ₗ[ℂ] ℂ) (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ),
    (fun x : E => L x + B x x) =O[𝓝 0] (fun x : E => ‖x‖ ^ 3) →
      L = 0 ∧ ∀ x : E, B x x = 0
end YangMills.Construction.Taylor
