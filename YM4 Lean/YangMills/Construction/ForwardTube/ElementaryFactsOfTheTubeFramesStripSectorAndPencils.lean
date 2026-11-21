import YangMills.Construction.EuclideanFunctionals.PlateBoundOfAFunctionalWithReconstruction
import YangMills.Construction.ForwardTube.ClosedTubeAndShiftedTuples
import YangMills.Construction.ForwardTube.TubeStarAndBoostFacts
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import YangMills.Construction.RotationInvariance.OrderedTuplesOfFunctionsAndTheCosineOfAnAperture
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
def TubeFrameStripSectorPencilFacts : Prop :=
  ((∀ w : ℂ × ℂ, w.1 = 1 / 2 * (lightConePlus w + lightConeMinus w) ∧
      w.2 = 1 / (2 * I) * (lightConePlus w - lightConeMinus w)) ∧
    IsLinearMap ℂ (fun w : ℂ × ℂ => (lightConePlus w, lightConeMinus w)) ∧
    Function.Bijective (fun w : ℂ × ℂ => (lightConePlus w, lightConeMinus w)) ∧
    ∀ w : ℂ × ℂ, (lightConePlus w).re = w.1.re - w.2.im ∧ (lightConeMinus w).re = w.1.re + w.2.im) ∧
  ((∀ t s : ℝ,
      (∃! L : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ), ∀ w : ℂ × ℂ,
        lightConePlus (L w) = Complex.exp (I * (t + I * s)) * lightConePlus w ∧
          lightConeMinus (L w) = Complex.exp (-(I * (t + I * s))) * lightConeMinus w) ∧
      IsLinearMap ℂ (complexBoost (t + I * s)) ∧
      ∀ w : ℂ × ℂ,
        lightConePlus (complexBoost (t + I * s) w) = Complex.exp (I * (t + I * s)) * lightConePlus w ∧
          lightConeMinus (complexBoost (t + I * s) w) =
            Complex.exp (-(I * (t + I * s))) * lightConeMinus w) ∧
    (∀ (z : ℂ) (w : ℂ × ℂ), complexBoost z w =
      (complexBoostMatrix z 0 0 * w.1 + complexBoostMatrix z 0 1 * w.2,
        complexBoostMatrix z 1 0 * w.1 + complexBoostMatrix z 1 1 * w.2)) ∧
    (∀ i j : Fin 2, YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn
      (N := 1) (N' := 1) Set.univ fun u _ => complexBoostMatrix (u 0) i j) ∧
    (∀ (t : ℝ) (x : YangMills.Construction.RealPlane),
      complexBoost (t : ℂ) (embedPlane x) = embedPlane (YangMills.Construction.RealPlane.rotate t x)) ∧
    (∀ (z z' : ℂ) (w : ℂ × ℂ),
      complexBoost z (complexBoost z' w) = complexBoost (z + z') w) ∧
    ∀ (s : ℝ) (w : ℂ × ℂ),
      lightConePlus (complexBoost (I * s) w) = (Real.exp (-s) : ℂ) * lightConePlus w ∧
        lightConeMinus (complexBoost (I * s) w) = (Real.exp s : ℂ) * lightConeMinus w) ∧
  ({w : ℂ × ℂ | (lightConePlus w).re > 0 ∧ (lightConeMinus w).re > 0} = {w : ℂ × ℂ | w.1.re > |w.2.im|} ∧
    {w : ℂ × ℂ | (lightConePlus w).re ≥ 0 ∧ (lightConeMinus w).re ≥ 0} = {w : ℂ × ℂ | w.1.re ≥ |w.2.im|} ∧
    (fun w : ℂ × ℂ => (lightConePlus w, lightConeMinus w)) '' forwardTube =
      {a : ℂ | a.re > 0} ×ˢ {b : ℂ | b.re > 0} ∧
    (fun w : ℂ × ℂ => (lightConePlus w, lightConeMinus w)) '' closedForwardTube =
      closure {a : ℂ | a.re > 0} ×ˢ closure {b : ℂ | b.re > 0} ∧
    IsOpen forwardTube ∧
    Convex ℝ forwardTube ∧
    (∀ w ∈ forwardTube, ∀ a : ℝ, 0 < a → a • w ∈ forwardTube) ∧
    closure forwardTube = closedForwardTube ∧
    interior closedForwardTube = forwardTube ∧
    (∀ w ∈ forwardTube, ∀ w' ∈ forwardTube, w + w' ∈ forwardTube) ∧
    (∀ w ∈ closedForwardTube, ∀ w' ∈ closedForwardTube, w + w' ∈ closedForwardTube) ∧
    forwardTube ∩ realVectors = embedPlane '' {x : YangMills.Construction.RealPlane | x 0 > 0} ∧
    {x : YangMills.Construction.RealPlane | x 0 > 0} = YangMills.Construction.RealPlane.openRightHalf ∧
    closedForwardTube ∩ realVectors = embedPlane '' {x : YangMills.Construction.RealPlane | x 0 ≥ 0}) ∧
  ((∀ w : ℂ × ℂ, lightConePlus (tubeStar w) = conj (lightConePlus w) ∧
      lightConeMinus (tubeStar w) = conj (lightConeMinus w)) ∧
    tubeStar '' forwardTube = forwardTube ∧
    tubeStar '' closedForwardTube = closedForwardTube ∧
    (∀ w : ℂ × ℂ,
      lightConePlus (conjPair w) = conj (lightConeMinus w) ∧
        lightConeMinus (conjPair w) = conj (lightConePlus w)) ∧
    conjPair '' forwardTube = forwardTube) ∧
  ((∀ s : ℝ, complexBoost (I * s) '' forwardTube = forwardTube) ∧
    (∀ (s : ℝ) (w : ℂ × ℂ),
      tubeStar (complexBoost (I * s) w) = complexBoost (I * s) (tubeStar w)) ∧
    ∀ x : YangMills.Construction.RealPlane,
      tubeStar (embedPlane x) = embedPlane (-YangMills.Construction.RealPlane.reflectFirst x)) ∧
  (∀ k : rightAngleMultiples,
    rotatedDirection k ∈ ({YangMills.Construction.RealPlane.unitX, -YangMills.Construction.RealPlane.unitX,
      YangMills.Construction.RealPlane.unitY, -YangMills.Construction.RealPlane.unitY} :
        Set YangMills.Construction.RealPlane) ∧
    ∀ x : YangMills.Construction.RealPlane,
      embedPlane x ∈ rotatedForwardTube k ↔ inner ℝ (rotatedDirection k) x > 0) ∧
  (∀ c ∈ YangMills.Construction.EuclideanFunctionals.productBoundFractions,
    ∀ η ∈ YangMills.Construction.EuclideanFunctionals.gapWidthRange,
    YangMills.Construction.RealPlane.openDiscAt 0 (c * η) ⊆
      YangMills.Construction.EuclideanFunctionals.planeStrip c η) ∧
  (∀ φ : YangMills.Construction.RealPlane.openingAngles,
    YangMills.Construction.RealPlane.coneSector φ =
      {x : YangMills.Construction.RealPlane | |x 1| < x 0 * Real.tan φ} ∧
    IsOpen (YangMills.Construction.RealPlane.coneSector φ) ∧
    Convex ℝ (YangMills.Construction.RealPlane.coneSector φ) ∧
    (∀ x ∈ YangMills.Construction.RealPlane.coneSector φ, ∀ a : ℝ, 0 < a →
      a • x ∈ YangMills.Construction.RealPlane.coneSector φ) ∧
    YangMills.Construction.RealPlane.coneSector φ ⊆ YangMills.Construction.RealPlane.openRightHalf ∧
    (∀ x ∈ YangMills.Construction.RealPlane.coneSector φ,
      -YangMills.Construction.RealPlane.reflectFirst x ∈ YangMills.Construction.RealPlane.coneSector φ) ∧
    (∀ x : YangMills.Construction.RealPlane,
      (-YangMills.Construction.RealPlane.reflectFirst x) 0 = x 0 ∧
        (-YangMills.Construction.RealPlane.reflectFirst x) 1 = -x 1) ∧
    (∀ n : ℕ, 2 ≤ n → IsOpen (YangMills.Construction.RealPlane.pencilSet φ n)) ∧
    YangMills.Construction.RealPlane.openingAngleCos φ = Real.cos ((φ : ℝ) + Real.pi / 4) ∧
    YangMills.Construction.RealPlane.openingAngleCos φ > 0)
end YangMills.Construction.ForwardTube
end
