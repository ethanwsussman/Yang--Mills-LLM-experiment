import YangMills.Construction.EuclideanFunctionals.GapWidthAndFractions
import YangMills.Construction.EuclideanFunctionals.InsertionForm
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanFunctionals.InsertionRoom
open RealPlane
def BallInGap : Prop :=
  ∀ η ∈ gapWidthRange, ∀ c ∈ ballFractionRange, ∀ x : R4, |x 3| ≤ η / 8 →
    TestFunctions.closedBallR4 x (c * η) ⊆ {y | |y 3| < η / 4}
def ProductInGap : Prop :=
  ∀ η ∈ gapWidthRange, ∀ c ∈ stripFractionRange, ∀ α ∈ complexProfiles, ∀ φ ∈ realLabels,
    tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    supp (productFunction α φ) ⊆ {x | |x 3| < η / 4}
def StripHeightOnBall : Prop :=
  ∀ η ∈ gapWidthRange, ∀ c ∈ ballFractionRange, ∀ x : R4, |x 3| ≤ η / 8 →
    ∀ h ∈ C1c ℂ, supp h ⊆ TestFunctions.closedBallR4 x (c * η) →
    ∀ F ∈ freeSpanIn {y | η / 4 < y 3}, ∀ G ∈ freeSpanIn {y | η / 4 < y 3},
      IsStripHeight (η / 4) F h G
def StripHeightOnProduct : Prop :=
  ∀ η ∈ gapWidthRange, ∀ c ∈ stripFractionRange, ∀ α ∈ complexProfiles, ∀ φ ∈ realLabels,
    tsupport α ⊆ {y : RealPlane | |y 0| < c * η} →
    ∀ F ∈ freeSpanIn {y | η / 4 < y 3}, ∀ G ∈ freeSpanIn {y | η / 4 < y 3},
      IsStripHeight (η / 4) F (productFunction α φ) G
def Holds : Prop :=
  BallInGap ∧ ProductInGap ∧ StripHeightOnBall ∧ StripHeightOnProduct
end YangMills.Construction.EuclideanFunctionals.InsertionRoom
