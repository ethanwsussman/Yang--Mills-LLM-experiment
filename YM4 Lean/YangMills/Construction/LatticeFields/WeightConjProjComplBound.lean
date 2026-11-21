import YangMills.Construction.LatticeFields.DirichletBlockOps
import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def WeightConjProjComplBound : Prop :=
  ∀ (P : ScaleData) (ℓ : Fin P.d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (δ : ℝ)
    (θ : LatticeSite P.N (LatticeShape.torus ℓ hℓ) → ℝ),
    δ ≤ 1 / (2 * ((P.d : ℝ) + 1)) → LipschitzWeight δ θ →
    2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) * (2 * ((P.d : ℝ) + 1) * δ) ≤ 1 →
    ∀ Y : Set (LatticeSite 1 (LatticeShape.torus ℓ hℓ)), Y.Nonempty →
      ∀ f ∈ fieldsSupportedIn (blockUnion P.N Y),
        fieldNorm (weightConj θ .fine .fine
            (dirichletProjCompl (blockUnion P.N Y) Y) f -
          dirichletProjCompl (blockUnion P.N Y) Y f) ≤
        2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) * (2 * ((P.d : ℝ) + 1) * δ) *
          fieldNorm f
end YangMills.Construction.LatticeFields
