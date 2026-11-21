import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence
open Dirichlet NestedRegions
variable (𝒮 : NestedRegions)
structure HodgeFacts : Prop where
  curl_add_grad : ∀ A : 𝒮.FineBond → ℝ,
    curlTorusAdj (curlTorus A) + dTorus (dTorusAdj A) = bondLap A
  comp_bondLap : ∀ (A : 𝒮.FineBond → ℝ) (μ : Fin 4),
    comp (bondLap A) μ = latticeLaplacian (comp A μ)
  form_bounds : ∀ A : 𝒮.FineBond → ℝ, 0 ≤ bondInner A (curlTorusAdj (curlTorus A)) ∧
    bondInner A (curlTorusAdj (curlTorus A)) ≤ bondInner A (bondLap A) ∧
    bondInner A (bondLap A) ≤ 4 * 4 * (𝒮.ξ ^ 2)⁻¹ * bondInner A A
def HodgeFactsHold : Prop := ∀ 𝒮 : NestedRegions, HodgeFacts 𝒮
end YangMills.Construction.RegionSequence
