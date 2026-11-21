import YangMills.Construction.RotationInvariance.KernelOfTheHarmonicsTopHarmonicAndLinesOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LineSidesViaRotations
open RealPlane
def IsNormalAngle (l P : Set RealPlane) (ϑ : ℝ) : Prop :=
  NormalPointsInto l (rotate ϑ unitX) P
def Holds : Prop :=
  ∀ (l P Q : Set RealPlane) (u : RealPlane),
    IsLine l → AreOpenSides l P Q → u ∈ l →
      ((∃ ϑ : ℝ, IsNormalAngle l P ϑ) ∧
        ∀ ϑ ϑ' : ℝ, IsNormalAngle l P ϑ → IsNormalAngle l P ϑ' →
          ∃ m : ℤ, ϑ - ϑ' = (m : ℝ) * (2 * Real.pi)) ∧
      (∀ ϑ : ℝ, IsNormalAngle l P ϑ → ∀ y : RealPlane,
        (y ∈ P ↔ rotate (-ϑ) (y - u) ∈ openRightHalf) ∧
        (y ∈ Q ↔ rotate (-ϑ) (y - u) ∈ openLeftHalf) ∧
        lineReflection l y = u + rotate ϑ (reflectFirst (rotate (-ϑ) (y - u)))) ∧
      (lineReflection l ∘ lineReflection l = id ∧
        Function.Bijective (lineReflection l) ∧
        lineReflection l '' P = Q ∧ lineReflection l '' Q = P ∧
        IsOpen P ∧ IsOpen Q ∧ Disjoint P Q ∧ P.Infinite ∧ Q.Infinite)
end YangMills.Construction.LineSidesViaRotations
end
