import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeCalculus
structure BlockIdentities {d : ℕ} {S ξ : ℝ}
    (f h ψ : YangMills.Construction.Dirichlet.LatticeSite d S ξ → ℝ)
    (F : YangMills.Construction.Dirichlet.BondField d S ξ)
    (x : YangMills.Construction.Dirichlet.LatticeSite d S ξ) : Prop where
  laplacian_eq_sum : YangMills.Construction.Dirichlet.latticeLaplacian f x =
    (ξ ^ 2)⁻¹ * ∑ᶠ y ∈ {y | YangMills.Construction.Dirichlet.IsNeighbor x y}, (f x - f y)
  laplacian_mul : YangMills.Construction.Dirichlet.latticeLaplacian (h * ψ) x =
    h x * YangMills.Construction.Dirichlet.latticeLaplacian ψ x -
      (ξ ^ 2)⁻¹ * ∑ᶠ y ∈ {y | YangMills.Construction.Dirichlet.IsNeighbor x y}, (h y - h x) * ψ y
  neighbor_sum_eq :
    (ξ ^ 2)⁻¹ * ∑ᶠ y ∈ {y | YangMills.Construction.Dirichlet.IsNeighbor x y}, (h y - h x) * ψ y =
      -∑ μ, YangMills.Construction.Dirichlet.backwardDiff μ
          (YangMills.Construction.Dirichlet.forwardDiff μ h *
            (ψ + YangMills.Construction.Dirichlet.translateForward μ ψ)) x +
        ψ x * YangMills.Construction.Dirichlet.latticeLaplacian h x
  mul_backwardDiff : ∀ μ, h x * YangMills.Construction.Dirichlet.backwardDiff μ (F μ) x =
    YangMills.Construction.Dirichlet.backwardDiff μ (h * F μ) x +
      YangMills.Construction.Dirichlet.translateBackward μ
        (YangMills.Construction.Dirichlet.forwardDiff μ h * F μ) x
end LatticeCalculus
end YangMills.Construction
