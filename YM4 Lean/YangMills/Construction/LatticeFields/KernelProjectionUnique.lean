import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.KernelProjectionUnique
def Claim : Prop :=
  ∀ (d N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ)
    (f : ScalarField N (LatticeShape.torus ℓ hℓ)),
    IsOrthProj (laplacianImageKer N ℓ hℓ) f (kerLaplacianProj f) ∧
      ∀ g : ScalarField N (LatticeShape.torus ℓ hℓ),
        IsOrthProj (laplacianImageKer N ℓ hℓ) f g → g = kerLaplacianProj f
end YangMills.Construction.LatticeFields.KernelProjectionUnique
