import YangMills.Construction.Conventions.OneLoopLawDefs
import YangMills.Construction.EuclideanFunctionals.FormsOfTheOperatorsOverTheWedge
import YangMills.Construction.ForwardTube.RotatedDirectionsAndSeparatedSets
import YangMills.Construction.ForwardTube.SuccessiveTubeDomainsAndLabelledPoints
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeSemigroup
open YangMills.Construction.HilbertSpaceBasics (ofBounded)
open YangMills.Construction.ForwardTube
open YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon
def pairRe (w : ℂ × ℂ) : RealPlane :=
  WithLp.toLp 2 (OneLoopNotation.reVec ![w.1, w.2])
def IsOpenConvexConeSet (C : Set (ℂ × ℂ)) : Prop :=
  IsOpen C ∧ Convex ℝ C ∧ ∀ w ∈ C, ∀ t : ℝ, 0 < t → t • w ∈ C
def ForwardTubeConeFacts : Prop :=
  {w : ℂ × ℂ | (lightConePlus w).re > 0 ∧ (lightConeMinus w).re > 0} =
      {w : ℂ × ℂ | w.1.re > |w.2.im|} ∧
  IsOpenConvexConeSet forwardTube ∧
  forwardTube ∩ realVectors = embedPlane '' RealPlane.openRightHalf ∧
  conjPair '' forwardTube = forwardTube ∧
  (∀ w ∈ forwardTube, embedPlane (pairRe w) ∈ forwardTube) ∧
  ∀ t : ℝ, imagBoost t '' forwardTube = forwardTube
def TubeStarFacts : Prop :=
  (∀ w w' : ℂ × ℂ, tubeStar (w + w') = tubeStar w + tubeStar w') ∧
  (∀ (z : ℂ) (w : ℂ × ℂ), tubeStar (z • w) = conj z • tubeStar w) ∧
  tubeStar '' forwardTube = forwardTube ∧
  tubeStar (embedPlane RealPlane.unitX) = embedPlane RealPlane.unitX ∧
  (∀ w : ℂ × ℂ, lightConePlus (tubeStar w) = conj (lightConePlus w) ∧
    lightConeMinus (tubeStar w) = conj (lightConeMinus w)) ∧
  (∀ (t : ℝ) (w : ℂ × ℂ), tubeStar (imagBoost t w) = imagBoost t (tubeStar w)) ∧
  ∀ p : RealPlane, tubeStar (embedPlane p) = embedPlane (-RealPlane.reflectFirst p)
def RotatedTubeConeFacts : Prop :=
  ∀ θ : rightAngleMultiples,
    IsOpenConvexConeSet (rotatedForwardTube θ) ∧
    (∀ t : ℝ, imagBoost t '' rotatedForwardTube θ = rotatedForwardTube θ) ∧
    (∀ w ∈ rotatedForwardTube θ, embedPlane (pairRe w) ∈ rotatedForwardTube θ) ∧
    rotatedForwardTube θ ∩ realVectors =
      embedPlane '' {p | 0 < inner ℝ (rotatedDirection θ) p}
def LightConeExponentIdentity : Prop :=
  ∀ (w : ℂ × ℂ) (E : ℝ) (k : Fin 3 → ℝ),
    -(w.1 * (E : ℂ)) + Complex.I * w.2 * (k 0 : ℂ) =
      -(lightConePlus w * (((E - k 0) / 2 : ℝ) : ℂ)) - lightConeMinus w * (((E + k 0) / 2 : ℝ) : ℂ)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def TubeOpsHolomorphicSemigroup : Prop :=
  (∀ w ∈ closedForwardTube,
    σ.tubeOp w = ofBounded (σ.wedgeIntegralOp w) ∧ ‖σ.wedgeIntegralOp w‖ ≤ 1) ∧
  σ.tubeOp 0 = ofBounded 1 ∧
  (∀ w ∈ closedForwardTube, ∀ w' ∈ closedForwardTube,
    σ.tubeOp (w + w') = ofBounded (σ.wedgeIntegralOp w * σ.wedgeIntegralOp w')) ∧
  (∀ w ∈ closedForwardTube,
    σ.tubeOp (tubeStar w) = ofBounded (star (σ.wedgeIntegralOp w))) ∧
  BanachValued.IsOperatorHolomorphicOn (n := 2) {z | (z 0, z 1) ∈ forwardTube}
    fun z => σ.wedgeIntegralOp (z 0, z 1)
def TubeOpsTranslateClasses : Prop :=
  ∀ p : RealPlane, 0 ≤ p 0 → ∀ F : finCombIn upperHalf,
    (planeShift p).actFree F.1 ∈ finCombIn upperHalf ∧
    σ.wedgeIntegralOp (embedPlane p) (σ.recon.cls F) =
      readClass σ.recon.cls ((planeShift p).actFree F.1)
def ForwardTubeSemigroupFacts : Prop :=
  ForwardTubeConeFacts ∧ TubeStarFacts ∧ RotatedTubeConeFacts ∧
  LightConeExponentIdentity ∧
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S),
    σ.ConeCondition → TubeOpsHolomorphicSemigroup σ ∧ TubeOpsTranslateClasses σ
end YangMills.Construction.EuclideanFunctionals.TubeSemigroup
