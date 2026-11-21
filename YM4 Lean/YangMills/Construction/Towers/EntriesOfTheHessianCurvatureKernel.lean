import YangMills.Construction.Towers.PartsOfTheHessianOfTheWilsonAction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CurvatureKernelEntries : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U : Edge L k 0 → Matrices.ComplexMatrix2,
    ∀ i' i : Fin 3 × PositiveEdge (meshAt L k 0),
      curvatureKernel U i' i = (1 / 2 : ℂ) * (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) *
        (curvatureBilinear U (basisForm i'.1 i'.2) (basisForm i.1 i.2) +
          curvatureBilinear U (basisForm i.1 i.2) (basisForm i'.1 i'.2))
end YangMills.Construction.Tower.FullSpace
end
