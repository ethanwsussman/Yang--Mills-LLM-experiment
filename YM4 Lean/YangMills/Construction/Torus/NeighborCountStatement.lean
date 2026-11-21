import YangMills.Construction.Dirichlet.LatticeCalculus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus
def NeighborCountStatement : Prop :=
  ∀ (d : ℕ) (S ξ : ℝ), 0 < ξ → 2 * ξ < S → ∀ x : Dirichlet.LatticeSite d S ξ,
    {y | Dirichlet.IsNeighbor x y}.ncard = 2 * d
end YangMills.Construction.Torus
end
