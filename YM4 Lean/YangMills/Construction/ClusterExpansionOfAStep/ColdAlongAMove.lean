import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.TorusFields
open BlockAverages
def ColdNearStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ₀ : Fin k → ℝ) (s : ℝ),
    IsCold s (perturb c X τ₀ V) → ∀ᶠ τ in 𝓝 τ₀, IsCold s (perturb c X τ V)
end YangMills.Construction.TorusFields
end
