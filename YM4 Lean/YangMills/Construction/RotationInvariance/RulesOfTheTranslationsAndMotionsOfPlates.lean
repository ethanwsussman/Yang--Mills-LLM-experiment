import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TranslationRules
open RealPlane
def TranslationLaws : Prop :=
  (∀ (z : R4) (m m' : ℕ) (A : TestSpaces.PointTuple m → ℂ) (B : TestSpaces.PointTuple m' → ℂ),
    translateArgs z (TestSpaces.tensorFun A B) =
      TestSpaces.tensorFun (translateArgs z A) (translateArgs z B)) ∧
  (∀ (z : R4) (c : ℂ) (m : ℕ) (A : TestSpaces.PointTuple m → ℂ),
    translateArgs z (TestSpaces.scalarTensorLeft c A) =
      TestSpaces.scalarTensorLeft c (translateArgs z A) ∧
    translateArgs z (TestSpaces.scalarTensorRight A c) =
      TestSpaces.scalarTensorRight (translateArgs z A) c) ∧
  (∀ (z w : R4) (m : ℕ) (A : TestSpaces.PointTuple m → ℂ),
    translateArgs z (translateArgs w A) = translateArgs (z + w) A) ∧
  ∀ t : ℝ,
    planeShift (t • unitX) = EuclidMotion.transl (t • timeVec) ∧
    ∀ (m : ℕ) (A : TestSpaces.PointTuple m → ℂ),
      translateArgs (embedFour (t • unitX)) A = translateArgs (t • timeVec) A
def MotionsOnPlaneFactor : Prop :=
  ∀ a ∈ complexProfiles, ∀ b ∈ realLabels, ∀ (v : RealPlane) (t : ℝ),
    (planeShift v).actFn (productFunction a b) = productFunction (translateProfile v a) b ∧
    (rotateMotion t).actFn (productFunction a b) = productFunction (a ∘ rotate (-t)) b ∧
    timeFlip.actFn (fun x => conj (productFunction a b x)) =
      productFunction ((fun y => conj (a y)) ∘ reflectFirst) b ∧
    translateProfile v a ∈ complexProfiles ∧
    a ∘ rotate (-t) ∈ complexProfiles ∧
    (fun y => conj (a y)) ∘ reflectFirst ∈ complexProfiles
def ProductFunctionsInC1c : Prop :=
  ∀ a ∈ complexProfiles, ∀ b ∈ realLabels,
    productFunction a b ∈ C1c ℂ ∧
    supp (productFunction a b) ⊆
      {x | planeComponent x ∈ tsupport a ∧ orthogonalComponent x ∈ tsupport b}
def PlaneMotionsAffineIsometric : Prop :=
  (∀ t : ℝ, Euclidean.IsAffineIsometryR4 (liftFour (rotate t))) ∧
  Euclidean.IsAffineIsometryR4 (liftFour reflectFirst) ∧
  (∀ v : RealPlane,
    Euclidean.IsAffineIsometryR4 (liftFour fun y => y + v)) ∧
  (∀ t : ℝ, ∃ Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ,
    ∀ x, liftFour (rotate t) x = (Q : Matrix _ _ ℝ).mulVec x) ∧
  (∀ x : R4, liftFour reflectFirst x = timeFlip x) ∧
  ∀ (v : RealPlane) (x : R4),
    liftFour (fun y => y + v) x =
      x + (v 0 • timeVec + v 1 • PeriodicLattice.coordVec 0)
def TranslationAndMotionFacts : Prop :=
  TranslationLaws ∧ MotionsOnPlaneFactor ∧ ProductFunctionsInC1c ∧ PlaneMotionsAffineIsometric
end YangMills.Construction.EuclideanFunctionals.TranslationRules
end
