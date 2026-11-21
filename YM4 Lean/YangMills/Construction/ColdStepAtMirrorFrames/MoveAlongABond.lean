import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def firstOrderSize {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (p : P → imaginaryQuaternions)
    (q : P →L[ℝ] imaginaryQuaternions) (u : P) : ℝ :=
  ‖iteratedFDeriv ℝ 1 p 0 ![u]‖ + ‖q u‖
def IsExpProductLog {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (C : ℝ) (p : P → imaginaryQuaternions)
    (q : P →L[ℝ] imaginaryQuaternions) (A : P → imaginaryQuaternions) : Prop :=
  ContDiffAt ℝ 3 A 0 ∧ A 0 = 0 ∧
    (∀ᶠ τ in 𝓝 (0 : P), expUnit (A τ) * expUnit (p 0) = expUnit (p τ) * expUnit (q τ)) ∧
    (∀ u, ‖iteratedFDeriv ℝ 1 A 0 ![u] - (iteratedFDeriv ℝ 1 p 0 ![u] + q u)‖ ≤ C * ‖p 0‖ * firstOrderSize p q u) ∧
    (∀ u, ‖iteratedFDeriv ℝ 1 A 0 ![u]‖ ≤ C * firstOrderSize p q u) ∧
    (∀ u v, ‖iteratedFDeriv ℝ 2 A 0 ![u, v]‖ ≤
      C * (firstOrderSize p q u * firstOrderSize p q v + ‖iteratedFDeriv ℝ 2 p 0 ![u, v]‖)) ∧
    ∀ u v w, ‖iteratedFDeriv ℝ 3 A 0 ![u, v, w]‖ ≤
      C * (firstOrderSize p q u * firstOrderSize p q v * firstOrderSize p q w +
        ‖iteratedFDeriv ℝ 2 p 0 ![u, v]‖ * firstOrderSize p q w +
        ‖iteratedFDeriv ℝ 2 p 0 ![u, w]‖ * firstOrderSize p q v +
        ‖iteratedFDeriv ℝ 2 p 0 ![v, w]‖ * firstOrderSize p q u + ‖iteratedFDeriv ℝ 3 p 0 ![u, v, w]‖)
def ExpProductLogBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (p : P → imaginaryQuaternions)
    (q : P →L[ℝ] imaginaryQuaternions),
    ContDiffAt ℝ 3 p 0 → ‖p 0‖ ≤ 1 → ∃ A : P → imaginaryQuaternions, IsExpProductLog C p q A
end YangMills.Construction.ColdStepAtMirrorFrames
end
