import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N : ℕ} {κ : LatticeShape d}
def VanishesOutside (Ω : Set (LatticeSite N κ)) (f : ScalarField N κ) : Prop :=
  ∀ x, x ∉ Ω → ScalarField.eval f x = 0
def compressedSiteOp (a : ℝ) (Ω : Set (LatticeSite N κ)) (f : ScalarField N κ) :
    ScalarField N κ :=
  restrictSites Ω
    (tensorLaplacian (restrictSites Ω f) +
      a • siteBlockAvgAdj (siteBlockAvg (restrictSites Ω f)))
def CompressedSiteOperator.Claim : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (a : ℝ), 0 < a →
    ∀ Ω : Set (LatticeSite (L ^ k) (LatticeShape.torus ℓ hℓ)),
      (∀ u v : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ), VanishesOutside Ω u →
        VanishesOutside Ω v →
        fieldInner v (compressedSiteOp a Ω u) = fieldInner (compressedSiteOp a Ω v) u) ∧
      (∀ v : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ), VanishesOutside Ω v →
        min (2 / (d : ℝ)) a * fieldNorm v ^ 2 ≤ fieldInner v (compressedSiteOp a Ω v)) ∧
      (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ), VanishesOutside Ω f →
        ∃! u : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
          VanishesOutside Ω u ∧ compressedSiteOp a Ω u = f)
end YangMills.Construction.LatticeFields
