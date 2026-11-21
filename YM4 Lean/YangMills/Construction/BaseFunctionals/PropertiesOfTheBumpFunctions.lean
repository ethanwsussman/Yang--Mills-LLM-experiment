import YangMills.Construction.BaseFunctionals.BumpFunctionsRadialMollifierAndRiemannSums
import YangMills.Construction.Euclidean.OrthogonalIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
open EuclideanFour Mollifiers Euclidean
namespace Mollifiers.BumpProperties
def ExpBumpFacts : Prop :=
  ContDiff ℝ ∞ expBump ∧ (∀ t, 0 ≤ expBump t ∧ expBump t < 1) ∧ ∀ t, 0 < expBump t ↔ 0 < t
def RescaledMollifierFacts (δ : ℝ) : Prop :=
  (fun y => (rescaledMollifier δ y : ℂ)) ∈ smoothCompact 4 ∧
    (∀ y, 0 ≤ rescaledMollifier δ y) ∧
    (∫ y : R4Point, rescaledMollifier δ y) = 1 ∧
    closedSupport (rescaledMollifier δ) = closedBallAt 0 δ ∧
    ∀ g : O4,
      (RigidMotion.ofO4 g).actFun (rescaledMollifier δ) =
        rescaledMollifier δ
def RescaledMollifierLineFacts (δ : ℝ) : Prop :=
  (fun s : Fin 1 → ℝ => (rescaledMollifierLine δ (s 0) : ℂ)) ∈ smoothCompact 1 ∧
    (∀ s, 0 ≤ rescaledMollifierLine δ s) ∧
    (∫ s : ℝ, rescaledMollifierLine δ s) = 1 ∧
    closedSupport (fun s : Fin 1 → ℝ => rescaledMollifierLine δ (s 0)) =
      (fun s : Fin 1 → ℝ => s 0) ⁻¹' Set.Icc (-δ) δ
def ShellCutoffFacts : Prop :=
  (fun y => (shellCutoff y : ℂ)) ∈ smoothCompact 4 ∧
    (∀ y, 0 ≤ shellCutoff y ∧ shellCutoff y ≤ 1) ∧
    (∀ y ∈ closedBallAt 0 (1 / 2), shellCutoff y = 1) ∧
    closedSupport shellCutoff ⊆ closedBallAt 0 (1 / 2 * Real.sqrt 3) ∧
    closedBallAt 0 (1 / 2 * Real.sqrt 3) ⊆ openBallAt 0 1
def bumpFacts : Prop :=
  ExpBumpFacts ∧
    (∀ δ : ℝ, 0 < δ → RescaledMollifierFacts δ ∧ RescaledMollifierLineFacts δ) ∧
    (rescaledMollifier 1 = stdMollifier ∧ rescaledMollifierLine 1 = stdMollifierLine) ∧
    ShellCutoffFacts
end Mollifiers.BumpProperties
end YangMills.Construction
