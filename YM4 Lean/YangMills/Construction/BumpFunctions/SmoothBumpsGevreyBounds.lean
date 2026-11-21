import YangMills.Construction.BumpFunctions.ExpNegInvDerivedFunctions
import Mathlib
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.BumpFunctions
def SmoothBumpsGevreyBounds : Prop :=
  (ContDiff ℝ ∞ bumpProfile ∧
    ∀ (n : ℕ) (s : ℝ), |iteratedDeriv n bumpProfile s| ≤ gevreyConst ^ n * (n.factorial : ℝ) ^ 2) ∧
  (ContDiff ℝ ∞ smoothStep ∧
    Monotone smoothStep ∧
    (∀ s ∈ Iic (0 : ℝ), smoothStep s = 0) ∧
    (∀ s ∈ Ici (1 : ℝ), smoothStep s = 1) ∧
    (∀ s : ℝ, 0 < s → 0 < smoothStep s)) ∧
  (ContDiff ℝ ∞ evenSmoothStep ∧
    (∀ s : ℝ, evenSmoothStep (-s) = evenSmoothStep s) ∧
    (∀ s : ℝ, evenSmoothStep s ∈ Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (-1 : ℝ) 1, evenSmoothStep s = 0) ∧
    (∀ s : ℝ, 1 < |s| → 0 < evenSmoothStep s) ∧
    (∀ s : ℝ, s ∉ Ioo (-2 : ℝ) 2 → evenSmoothStep s = 1) ∧
    (∀ s s' : ℝ, |s| ≤ |s'| → evenSmoothStep s ≤ evenSmoothStep s')) ∧
  (ContDiff ℝ ∞ mollifiedUnitIndicator ∧
    (∀ s : ℝ, 0 ≤ mollifiedUnitIndicator s ∧ mollifiedUnitIndicator s ≤ 1) ∧
    tsupport mollifiedUnitIndicator ⊆ Icc (-(3 / 4) : ℝ) (3 / 4) ∧
    (∀ s : ℝ, ∑' k : ℤ, mollifiedUnitIndicator (s - k) = 1) ∧
    (∀ s : ℝ, (Function.support fun k : ℤ => mollifiedUnitIndicator (s - k)).encard ≤ 2)) ∧
  (ContDiff ℝ ∞ productCubeCutoff ∧
    HasCompactSupport productCubeCutoff ∧
    (∀ y : Fin 4 → ℝ, 0 ≤ productCubeCutoff y ∧ productCubeCutoff y ≤ 1) ∧
    (∀ y ∈ (univ.pi fun _ : Fin 4 => Icc (-(3 / 4) : ℝ) (3 / 4)), productCubeCutoff y = 1) ∧
    tsupport productCubeCutoff ⊆ (univ.pi fun _ : Fin 4 => Icc (-1 : ℝ) 1) ∧
    (∀ y : Fin 4 → ℝ,
      Real.sqrt (∑ i : Fin 4, (fderiv ℝ productCubeCutoff y (Pi.single i 1)) ^ 2) ≤
        cutoffConst)) ∧
  (∀ (n : ℕ) (s : ℝ),
    |iteratedDeriv n smoothStep s| ≤
        integralConstBound * blockConst ^ n * (n.factorial : ℝ) ^ 2 ∧
      |iteratedDeriv n evenSmoothStep s| ≤
        integralConstBound * blockConst ^ n * (n.factorial : ℝ) ^ 2 ∧
      |iteratedDeriv n mollifiedUnitIndicator s| ≤
        integralConstBound * blockConst ^ n * (n.factorial : ℝ) ^ 2)
end YangMills.Construction.BumpFunctions
