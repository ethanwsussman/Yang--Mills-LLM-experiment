import YangMills.Construction.LatticeFields.BlockAveraging
import YangMills.Construction.LatticeFields.MetricAdjointCubeLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.TorusLaws
variable {d : ℕ}
structure TorusMetricProps (N : ℕ) (κ : LatticeShape d) : Prop where
  dist_self : ∀ x : LatticeSite N κ, siteDist x x = 0
  eq_of_dist_eq_zero : ∀ x y : LatticeSite N κ, siteDist x y = 0 → x = y
  dist_comm : ∀ x y : LatticeSite N κ, siteDist x y = siteDist y x
  dist_triangle : ∀ x y z : LatticeSite N κ,
    siteDist x z ≤ siteDist x y + siteDist y z
  spacing_le_dist : ∀ x y : LatticeSite N κ, x ≠ y → latticeSpacing N ≤ siteDist x y
  dist_add_step_le : ∀ (x : LatticeSite N κ) (μ : Fin d),
    siteDist x (x + unitStep N κ μ) ≤ latticeSpacing N
  dist_sub_step_le : ∀ (x : LatticeSite N κ) (μ : Fin d),
    siteDist x (x - unitStep N κ μ) ≤ latticeSpacing N
  abs_setDist_sub_le : ∀ (V : Set (LatticeSite N κ)), V.Nonempty → ∀ x y : LatticeSite N κ,
    |siteSetDist {x} V - siteSetDist {y} V| ≤ siteDist x y
structure TorusAdjointProps (N : ℕ) (κ : LatticeShape d) : Prop where
  shift_adjoint : ∀ (I : Type) [Finite I] (μ : Fin d) (F G : LatticeField N κ I),
    fieldInner (shiftForward μ F) G = fieldInner F (shiftBackward μ G)
  forwardDiff_adjoint : ∀ (I : Type) [Finite I] (μ : Fin d) (F G : LatticeField N κ I),
    fieldInner (forwardDiff μ F) G = fieldInner F (backwardDiff μ G)
  grad_adjoint : ∀ (f : ScalarField N κ) (A : LatticeOneForm N κ),
    fieldInner (latticeGrad f) A = fieldInner f (latticeDiv A)
  tensorGrad_adjoint : ∀ (r : ℕ) (F : LatticeTensor N κ r) (G : LatticeTensor N κ (r + 1)),
    fieldInner (tensorGrad F) G = fieldInner F (tensorGradAdjoint G)
  laplacian_eq_sum : ∀ (r : ℕ) (F : LatticeTensor N κ r) (x : LatticeSite N κ) (i : Fin r → Fin d),
    tensorLaplacian F x i = ∑ μ, backwardDiff μ (forwardDiff μ F) x i
structure TorusBlockProps (N : ℕ) (κ : LatticeShape d) : Prop where
  ncard_eq : ∀ y : LatticeSite 1 κ, (coarseBlock N y).ncard = N ^ d
  volume_eq_one : ∀ y : LatticeSite 1 κ, ∑ᶠ _x ∈ coarseBlock N y, latticeSpacing N ^ d = 1
  existsUnique_mem : ∀ x : LatticeSite N κ, ∃! y : LatticeSite 1 κ, x ∈ coarseBlock N y
  adj_eq_on_block : ∀ (ω : ScalarField 1 κ) (y : LatticeSite 1 κ) (x : LatticeSite N κ),
    x ∈ coarseBlock N y →
    ScalarField.eval (siteBlockAvgAdj ω : ScalarField N κ) x = ScalarField.eval ω y
def TorusLatticeFacts : Prop :=
  ∀ (d L k N : ℕ) [NeZero N], 2 ≤ d → 2 ≤ L → N = L ^ k →
    ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
      TorusMetricProps N (LatticeShape.torus ℓ hℓ) ∧
      TorusAdjointProps N (LatticeShape.torus ℓ hℓ) ∧
      TorusAdjointProps 1 (LatticeShape.torus ℓ hℓ) ∧
      MetricAdjointCubes.DoubledCubeProps N (LatticeShape.torus ℓ hℓ) ∧
      TorusBlockProps N (LatticeShape.torus ℓ hℓ)
end YangMills.Construction.LatticeFields.TorusLaws
