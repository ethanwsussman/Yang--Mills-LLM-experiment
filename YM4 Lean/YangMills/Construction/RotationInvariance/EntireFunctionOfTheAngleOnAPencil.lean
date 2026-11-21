import YangMills.Construction.RotationInvariance.PlaneKernelsOfTheFunctional
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace ForwardTube
def complexBoostTuple (z : ℂ) {q : ℕ} (v : Fin q → ℂ × ℂ) : Fin q → ℂ × ℂ :=
  fun i => complexBoost z (v i)
def planeTupleDiffs {q : ℕ} (y : Fin (q + 1) → RealPlane) : Fin q → ℂ × ℂ :=
  embedPlaneTuple (successiveDifferences y)
end ForwardTube
namespace EuclideanFunctionals
open ForwardTube
structure IsAngleFunction (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) (f : ℂ → ℂ) : Prop where
  entire : Entire f
  apply_eq_planeKernel : ∀ (k : rightAngleMultiples) (t s : ℝ),
    |t - (k : ℝ)| < Real.pi / 2 - (θ₀ : ℝ) →
    f ((t : ℂ) + I * (s : ℂ)) =
      planeKernel S φ (complexBoostTuple ((t : ℂ) + I * (s : ℂ) - ((k : ℝ) : ℂ))
        (planeTupleDiffs y))
def angleFunction (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : ℂ → ℂ :=
  Classical.epsilon (IsAngleFunction S θ₀ y φ)
namespace AngleFunctionOnPencil
variable {m : SharpScale} {S : ConnFamily}
def BoostedDiffsInTube (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) : Prop :=
  ∀ (k : rightAngleMultiples) (t s : ℝ), |t - (k : ℝ)| < Real.pi / 2 - (θ₀ : ℝ) →
    complexBoostTuple ((t : ℂ) + I * (s : ℂ) - ((k : ℝ) : ℂ))
      (planeTupleDiffs y) ∈ forwardTubePow q
def SpecialValues (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  (∀ t : ℝ, |t| < Real.pi / 2 - (θ₀ : ℝ) →
    angleFunction S θ₀ y φ (t : ℂ) =
        planeKernel S φ (planeTupleDiffs (mapPoints (rotate t) y)) ∧
      (angleFunction S θ₀ y φ (t : ℂ)).im = 0) ∧
  (∀ s : ℝ, angleFunction S θ₀ y φ (I * (s : ℂ)) =
    planeKernel S φ (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs y))) ∧
  (fun ζ : ℂ => angleFunction S θ₀ y φ (ζ + ((Real.pi / 2 : ℝ) : ℂ))) =
    angleFunction S θ₀ y φ ∧
  ∀ t : ℝ, (angleFunction S θ₀ y φ (t : ℂ)).im = 0
def MarginBound (θ₀ : openingAngles) {q : ℕ} (hq : 1 ≤ q)
    (y : Fin (q + 1) → RealPlane) : Prop :=
  ∀ (k : rightAngleMultiples) (t s : ℝ), |t - (k : ℝ)| ≤ Real.pi / 4 → ∀ i : Fin q,
    openingAngleCos θ₀ * minGapLength (Nat.succ_le_succ hq) y * Real.exp (-|s|) ≤
        (lightConePlus (complexBoostTuple ((t : ℂ) + I * (s : ℂ) - ((k : ℝ) : ℂ))
          (planeTupleDiffs y) i)).re ∧
      openingAngleCos θ₀ * minGapLength (Nat.succ_le_succ hq) y * Real.exp (-|s|) ≤
        (lightConeMinus (complexBoostTuple ((t : ℂ) + I * (s : ℂ) - ((k : ℝ) : ℂ))
          (planeTupleDiffs y) i)).re
def GrowthBound (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) : Prop :=
  ∀ t s : ℝ,
    ‖angleFunction S d.angle y φ ((t : ℂ) + I * (s : ℂ))‖ ≤
        (∏ i, d.base.labelConst (φ i)) *
          RealPower.rpowPos
            (min 1 (openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y *
              Real.exp (-|s|)))
            (-(d.base.expo * ((q + 1 : ℕ) : ℝ))) ∧
      (∏ i, d.base.labelConst (φ i)) *
          RealPower.rpowPos
            (min 1 (openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y *
              Real.exp (-|s|)))
            (-(d.base.expo * ((q + 1 : ℕ) : ℝ))) ≤
        (∏ i, d.base.labelConst (φ i)) *
          max 1 (RealPower.rpowPos
            (openingAngleCos d.angle * minGapLength (Nat.succ_le_succ hq) y)
            (-(d.base.expo * ((q + 1 : ℕ) : ℝ)))) *
          Real.exp (d.base.expo * ((q + 1 : ℕ) : ℝ) * |s|)
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (q : ℕ) (hq : 1 ≤ q),
    ∀ y ∈ pencilSet d.angle (q + 1), ∀ φ : Fin (q + 1) → realLabels,
      BoostedDiffsInTube d.angle y ∧
      IsAngleFunction S d.angle y φ (angleFunction S d.angle y φ) ∧
      (∀ f : ℂ → ℂ, IsAngleFunction S d.angle y φ f →
        f = angleFunction S d.angle y φ) ∧
      SpecialValues S d.angle y φ ∧
      MarginBound d.angle hq y ∧
      GrowthBound d hq y φ
end AngleFunctionOnPencil
end EuclideanFunctionals
end YangMills.Construction
end
