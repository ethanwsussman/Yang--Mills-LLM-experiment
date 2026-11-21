import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTreesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Lattice.CochainLaplacian
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
theorem latticeDivergence_apply [IsCommensurateSpacing ℓ ε] (A : Cochain1 ℓ ε)
    (x : LatticeSite ℓ ε) :
    latticeDivergence ℓ ε A x = ε⁻¹ * ∑ μ, (A (x - latticeStep ℓ ε μ, μ) - A (x, μ)) := by apply _root_.YangMills.Construction.BlockSpin.BlockGeometry.latticeDivergence_apply <;> assumption
end YangMills.Construction.Lattice.CochainLaplacian
