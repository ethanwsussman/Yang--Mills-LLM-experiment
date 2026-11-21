import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace YangMills.Construction.WeightedResponses
variable {F : BlockFrame}
def IsLocalExponentAt (P : StepParameters) (Cq : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (i₀ : Fin k), IsAdmissibleAt P t x f F V →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f → k ≤ 2 → AreUnitVectors X →
    ContDiffOn ℝ 1 (fun η => bondDeriv (fun W => (coldHalfLawAt P x f).exponent W η) V c X)
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < P.ballRadius} ∧
      (coldHalfLawAt P x f).HasSize Cq V (A * Real.exp (-(2 ^ 3 * P.κ * bondListDiameter c))) (c i₀).1
        fun η => bondDeriv (fun W => (coldHalfLawAt P x f).exponent W η) V c X
def sizeParameters (P : StepParameters) : StepParameters :=
  { P with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }
def parametersBeforeSide (P : StepParameters) : StepParameters :=
  { P with n₀ := 0, CE := 0, coupling := 0 }
def exponentLocalityStatement : Prop :=
  ∃ (Cq : StepParameters → ℕ → ℝ) (A : StepParameters → ℝ), (∀ P q, 0 < Cq P q) ∧ (∀ P, 0 ≤ A P) ∧
    EventuallyInParameters fun P => IsLocalExponentAt P (Cq (sizeParameters P)) (A (parametersBeforeSide P))
end YangMills.Construction.WeightedResponses
end
