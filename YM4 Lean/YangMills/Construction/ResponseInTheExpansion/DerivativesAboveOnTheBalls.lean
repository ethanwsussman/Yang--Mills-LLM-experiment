import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates
namespace ResponseInTheExpansion
variable {F : BlockFrame}
structure MixedDerivativeFacts (ρ : ℝ) (V : F.GaugeField F.top)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop where
  fieldDeriv_zero : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k = 0 →
    fieldDeriv G V c X = fun ζ => G ζ V
  contDiffAt_three : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ 3 (fun ζ' => G ζ' V) ζ
  contDiffAt_one : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F)), k ≤ 2 →
    (∀ b, ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ 1 (fieldDeriv G V c X) ζ
  fderiv_eq : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)), k ≤ 2 → (∀ b, ‖ζ b‖ ≤ ρ) →
    fderiv ℝ (fieldDeriv G V c X) ζ (Pi.single b u) = jointMixedDeriv G ζ V ![b] ![u] c X
  fderiv_fderiv_eq : ∀ (ζ : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F)))
    (u u' : EuclideanSpace ℝ (Fin 3)), (∀ b, ‖ζ b‖ ≤ ρ) →
    fderiv ℝ (fderiv ℝ (fun ζ' => G ζ' V)) ζ (Pi.single b u) (Pi.single b' u') =
      jointMixedDeriv G ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)
  abs_sub_le : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (D : ↥(chordBonds (finiteCells F)) → ℝ)
    (ζ ζ' : StepVariable (finiteCells F)), k ≤ 2 →
    (∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ ρ) → ∀ (b : ↥(chordBonds (finiteCells F)))
      (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 → |jointMixedDeriv G ξ V ![b] ![u] c X| ≤ D b) →
    (∀ b, ‖ζ b‖ ≤ ρ) → (∀ b, ‖ζ' b‖ ≤ ρ) →
    |fieldDeriv G V c X ζ' - fieldDeriv G V c X ζ| ≤ ∑ b, ‖ζ' b - ζ b‖ * D b
  bondGradNorm_le : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (D : ℝ), k ≤ 2 → 0 ≤ D → (∀ b, ‖ζ b‖ ≤ ρ) →
    (∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → |jointMixedDeriv G ζ V ![b] ![u] c X| ≤ D) →
    bondGradNorm (fieldDeriv G V c X) b ζ ≤ D
structure MixedDerivativeSum (ρ : ℝ) (V : F.GaugeField F.top) : Prop where
  sum_one : ∀ (α : Type) (S : Finset α) (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)),
    (∀ a ∈ S, JointlyContDiffOnBalls ρ V (G a)) → k ≤ 2 →
    (∀ b, ‖ζ b‖ ≤ ρ) →
    jointMixedDeriv (fun ζ' V' => ∑ a ∈ S, G a ζ' V') ζ V ![b] ![u] c X =
      ∑ a ∈ S, jointMixedDeriv (G a) ζ V ![b] ![u] c X
  sum_two : ∀ (α : Type) (S : Finset α) (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (ζ : StepVariable (finiteCells F)) (b b' : ↥(chordBonds (finiteCells F))) (u u' : EuclideanSpace ℝ (Fin 3)),
    (∀ a ∈ S, JointlyContDiffOnBalls ρ V (G a)) → (∀ b, ‖ζ b‖ ≤ ρ) →
    jointMixedDeriv (fun ζ' V' => ∑ a ∈ S, G a ζ' V') ζ V ![b, b'] ![u, u']
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
      ∑ a ∈ S, jointMixedDeriv (G a) ζ V ![b, b'] ![u, u'] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)
def mixedDerivativesOnBallsStatement : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (V : F.GaugeField F.top), MixedDerivativeSum ρ V ∧
    ∀ G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ, JointlyContDiffOnBalls ρ V G →
      MixedDerivativeFacts ρ V G
end ResponseInTheExpansion
end YangMills.Construction
end
