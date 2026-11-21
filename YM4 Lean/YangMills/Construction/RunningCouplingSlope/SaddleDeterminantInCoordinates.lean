import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def SaddleDetInOrthonormalCoords : Prop :=
  ∀ (V V' I T : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup V']
    [Module ℝ V'] [FiniteDimensional ℝ V'] [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ V')
    (Φ : V ≃ₗ[ℝ] (I → ℝ)) (Φ' : V' ≃ₗ[ℝ] (T → ℝ)),
    (∀ x y, c.inner x y = ∑ i, Φ x i * Φ y i) → (∀ x y, c'.inner x y = ∑ t, Φ' x t * Φ' y t) →
    ∀ (X : V →ₗ[ℝ] V) (M : V →ₗ[ℝ] V') (Xm : Matrix I I ℂ) (Mm : Matrix T I ℂ),
      (∀ x i, ((Φ (X x) i : ℝ) : ℂ) = ∑ j, Xm i j * ((Φ x j : ℝ) : ℂ)) →
      (∀ x t, ((Φ' (M x) t : ℝ) : ℂ) = ∑ j, Mm t j * ((Φ x j : ℝ) : ℂ)) →
      |YangMills.Construction.GaussianConstraint.saddleDetOfCores c c' X M| =
        ‖Matrix.det (Matrix.fromBlocks Xm Mm.transpose Mm 0)‖
end YangMills.Construction.RunningCouplingSlope
end
