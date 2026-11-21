import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductMotions
open RealPlane
def RotationsSpecialOrthogonal : Prop :=
  ∀ t : ℝ,
    (∀ x : R4, rotateMotion t x = rotateLin t x) ∧
    (∀ x : R4, TorusMetric.euclidNormVec (rotateLin t x) = TorusMetric.euclidNormVec x) ∧
    LinearMap.det (rotateLin t) = 1 ∧
    LinearMap.toMatrix' (rotateLin t) ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ∧
    (rotateMotion t)⁻¹ = rotateMotion (-t)
def RightAngleRotationsHyperoctahedral : Prop :=
  ∀ k : ℤ, rotateMotion ((k : ℝ) * (Real.pi / 2)) ∈ hyperoctahedral
def ProductFunctionsCompactC1 : Prop :=
  ∀ a ∈ complexProfiles, ∀ b ∈ realLabels,
    productFunction a b ∈ C1c ℂ ∧
    supp (productFunction a b) ⊆
      {x | planeComponent x ∈ tsupport a ∧ orthogonalComponent x ∈ tsupport b}
def MotionsActOnPlaneFactor : Prop :=
  ∀ a ∈ complexProfiles, ∀ b ∈ realLabels, ∀ (v : RealPlane) (t : ℝ),
    (planeShift v).actFn (productFunction a b) = productFunction (translateProfile v a) b ∧
    (rotateMotion t).actFn (productFunction a b) = productFunction (a ∘ rotate (-t)) b ∧
    timeFlip.actFn (fun x => conj (productFunction a b x)) =
      productFunction ((fun y => conj (a y)) ∘ reflectFirst) b
def MotionImagesAreProducts : Prop :=
  ∀ a ∈ complexProfiles, ∀ b ∈ realLabels, ∀ (v : RealPlane) (t : ℝ),
    translateProfile v a ∈ complexProfiles ∧
    a ∘ rotate (-t) ∈ complexProfiles ∧
    (fun y => conj (a y)) ∘ reflectFirst ∈ complexProfiles ∧
    IsProductFunction (productFunction (translateProfile v a) b) ∧
    IsProductFunction (productFunction (a ∘ rotate (-t)) b) ∧
    IsProductFunction (productFunction ((fun y => conj (a y)) ∘ reflectFirst) b)
def MotionFacts : Prop :=
  RotationsSpecialOrthogonal ∧ RightAngleRotationsHyperoctahedral ∧
    ProductFunctionsCompactC1 ∧ MotionsActOnPlaneFactor ∧ MotionImagesAreProducts
end YangMills.Construction.EuclideanFunctionals.ProductMotions
end
