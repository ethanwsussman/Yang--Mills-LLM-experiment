import YangMills.Construction.RotationInvariance.ScalarProductsOfBumpVectorsAtRealPoints
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace EuclideanFunctionals.MollifierInnerAtComplexPoints
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (η : ℝ),
    η ∈ Set.Ioc (0 : ℝ) 1 → ∀ δ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier η δ →
    ∀ (j : ℕ+) (n n' : ℕ) (φ : Fin n → realLabels) (φ' : Fin n' → realLabels),
    ∀ x ∈ shiftedForwardTube n η, ∀ y ∈ shiftedForwardTube n' η,
      ⟪d.mollifierVector η δ j φ x, d.mollifierVector η δ j φ' y⟫_ℂ =
        d.mollifierGramValue η δ j φ φ' x y
end EuclideanFunctionals.MollifierInnerAtComplexPoints
end YangMills.Construction
end
