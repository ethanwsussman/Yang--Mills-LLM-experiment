import YangMills.Construction.RotationInvariance.PlaneKernelsOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace EuclideanFunctionals.LabelLinearity
variable {q : ℕ}
def FunctionalLinearInLabel (S : ConnFamily) (φ : Fin (q + 1) → realLabels) (j : Fin (q + 1))
    (ψ : realLabels) (a b : ℝ) : Prop :=
  ∀ f : Fin (q + 1) → RealPlane → ℂ, (∀ l, f l ∈ complexProfiles) →
    (Pairwise fun k l => Disjoint (tsupport (f k)) (tsupport (f l))) →
    ComplexComponents (fun l => productFunction (f l) (φ l)) ∧
    centeredFnAtProducts S f (Function.update φ j (labelLinComb a (φ j) b ψ)) =
      a * centeredFnAtProducts S f φ + b * centeredFnAtProducts S f (Function.update φ j ψ) ∧
    ((∃ l, f l = 0) → centeredFnAtProducts S f φ = 0)
def PlaneKernelLinearInLabel (S : ConnFamily) (φ : Fin (q + 1) → realLabels) (j : Fin (q + 1))
    (ψ : realLabels) (a b : ℝ) : Prop :=
  ∀ v ∈ forwardTubePow q,
    planeKernel S (Function.update φ j (labelLinComb a (φ j) b ψ)) v =
      a * planeKernel S φ v + b * planeKernel S (Function.update φ j ψ) v
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (_d : PlaneDataWithAperture m S) (q : ℕ), 1 ≤ q →
    ∀ (φ : Fin (q + 1) → realLabels) (j : Fin (q + 1)) (ψ : realLabels) (a b : ℝ),
      FunctionalLinearInLabel S φ j ψ a b ∧ PlaneKernelLinearInLabel S φ j ψ a b
end EuclideanFunctionals.LabelLinearity
end YangMills.Construction
end
