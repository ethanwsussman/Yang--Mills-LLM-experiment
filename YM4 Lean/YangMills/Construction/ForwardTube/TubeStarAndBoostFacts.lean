import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.ForwardTube.RotatedDirectionsAndSeparatedSets
import YangMills.Construction.Rotation.FourthFirstCoordinatePlane
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
def complexBoostMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos z, -Complex.sin z; Complex.sin z, Complex.cos z]
def TubeStarAndBoostFacts : Prop :=
  ((∀ v : ℂ × ℂ, (lightConePlus v).re = v.1.re - v.2.im ∧
      (lightConeMinus v).re = v.1.re + v.2.im) ∧
    {v : ℂ × ℂ | (lightConePlus v).re > 0 ∧ (lightConeMinus v).re > 0} =
      {v : ℂ × ℂ | v.1.re > |v.2.im|}) ∧
  (IsOpen forwardTube ∧
    (∀ v ∈ forwardTube, ∀ w ∈ forwardTube, v + w ∈ forwardTube) ∧
    (∀ v ∈ forwardTube, ∀ a : ℝ, 0 < a → a • v ∈ forwardTube) ∧
    forwardTube ∩ realVectors = embedPlane '' RealPlane.openRightHalf) ∧
  ((∀ v : ℂ × ℂ, lightConePlus (tubeStar v) = conj (lightConePlus v) ∧
      lightConeMinus (tubeStar v) = conj (lightConeMinus v)) ∧
    ∀ y : RealPlane, tubeStar (embedPlane y) = embedPlane (-RealPlane.reflectFirst y)) ∧
  ((∀ t s : ℝ,
      Complex.exp (I * (t + I * s)) = (Real.exp (-s) : ℂ) * Complex.exp (I * t) ∧
      Complex.exp (-(I * (t + I * s))) = (Real.exp s : ℂ) * Complex.exp (-(I * t))) ∧
    (∀ z : ℂ, IsLinearMap ℂ (complexBoost z)) ∧
    (∀ (z : ℂ) (v : ℂ × ℂ), complexBoost z v =
      (complexBoostMatrix z 0 0 * v.1 + complexBoostMatrix z 0 1 * v.2,
        complexBoostMatrix z 1 0 * v.1 + complexBoostMatrix z 1 1 * v.2)) ∧
    (∀ (z : ℂ) (v : ℂ × ℂ), complexBoost z v =
      (v.1 * Complex.cos z - v.2 * Complex.sin z, v.1 * Complex.sin z + v.2 * Complex.cos z)) ∧
    (∀ (t : ℝ) (y : RealPlane),
      complexBoost (t : ℂ) (embedPlane y) = embedPlane (RealPlane.rotate t y)) ∧
    (∀ i j : Fin 2, Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 1) (N' := 1) Set.univ
      fun w _ => complexBoostMatrix (w 0) i j) ∧
    (∀ (z w : ℂ) (v : ℂ × ℂ),
      complexBoost z (complexBoost w v) = complexBoost (z + w) v) ∧
    ∀ v : ℂ × ℂ, complexBoost 0 v = v)
end YangMills.Construction.ForwardTube
end
