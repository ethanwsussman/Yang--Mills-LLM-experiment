import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
def dilationRemainderDensity (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (t : ℕ) (x : ℝ)
    (f : LocalFamily) : LocalDensity :=
  densityOfTopFamily P.L t fun _ Y V => (coldHalfLawAt P x f).dilationRemainder Y V
def doublePotentialSum (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑' p : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4), ‖linearPotential A p.1‖ * ‖linearPotential A p.2‖ *
    Real.exp (-(P.κ / 2 ^ 5 * max (max (offsetNorm p.1.1) (offsetNorm p.2.1)) (offsetNorm (p.1.1 - p.2.1))))
def dilationRemainderAtCurvatureBound (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ), P.coupling ≤ x →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f → ‖X‖ = 1 → (∀ i j, ω i j = - ω j i) →
    ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], 8 * Real.log (1 / γ) ^ 2 ≤ n →
        ∀ (V : TorusField n) (Y : TorusSite n),
        IsAbelianWithCurvature X ω γ V →
        |centered (dilationRemainderDensity P t x f) n Y V| ≤
          γ ^ 2 * (P.CE * doublePotentialSum P (curvatureAlong X ω) * x ^ (-(3 / 2) : ℝ) + ε)
def dilationRemainderAtCurvatureStatement : Prop := EventuallyInParameters dilationRemainderAtCurvatureBound
end YangMills.Construction.WeightedResponses
end
