import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction
namespace Calculus
def FderivFinsetSum : Prop :=
  ∀ (P ι : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (s : Finset ι) (g : ι → P → ℝ) (x : P),
    (∀ c ∈ s, ContDiffAt ℝ 3 (g c) x) →
    ContDiffAt ℝ 3 (fun ζ => ∑ c ∈ s, g c ζ) x ∧
    ∀ u v : P, fderiv ℝ (fun ζ => ∑ c ∈ s, g c ζ) x u = ∑ c ∈ s, fderiv ℝ (g c) x u ∧
      fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => ∑ c ∈ s, g c ξ) ζ u) x v =
        ∑ c ∈ s, fderiv ℝ (fun ζ => fderiv ℝ (g c) ζ u) x v
end Calculus
end YangMills.Construction
end
