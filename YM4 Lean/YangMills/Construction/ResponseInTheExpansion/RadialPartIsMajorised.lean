import YangMills.Construction.ResponseInTheExpansion.MajorisedObservablesAreAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison Interpolation WeightedResponses
namespace ResponseInTheExpansion
variable {F : BlockFrame}
def radialPart (S : Finset ↥(chordBonds (finiteCells F))) (G : StepVariable (finiteCells F) → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b ∈ S, bondPartialDeriv G b η (η b)
end ResponseInTheExpansion
namespace WeightedResponses
variable {F : BlockFrame}
open Classical in
def ColdHalfLaw.exponentRadialPart (Q : ColdHalfLaw) (Y : F.Cell) : AboveFrames F := fun η V =>
  ResponseInTheExpansion.radialPart
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y)
    (interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V) η
end WeightedResponses
namespace ResponseInTheExpansion
def radialPartDominatedStatement : Prop :=
  ∀ (N : ℕ) (ρ κ : ℝ), 0 < ρ → 0 < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : BlockFrame) (Y : F.Cell) (p : ℝ → ℝ) (q : ℕ)
    (S : Finset ↥(chordBonds (finiteCells F))) (G : StepVariable (finiteCells F) → ℝ) (A : ℝ),
    (∀ z : F.Cell, (open Classical in
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card) ≤ N) →
    0 ≤ A → (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 2 G η) →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b ∈ S, ∀ e : BondVector,
      |bondPartialDeriv G b η e| ≤ A * Real.exp (-(16 * κ * bondDistToCell Y b)) * ‖e‖) →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → ∀ b ∈ S,
      ∀ (b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |secondDerivAlong G η (bondVariation b e) (bondVariation b' e')| ≤
        A * Real.exp (-(16 * κ * bondDistToCell Y b)) * Real.exp (-(16 * κ * bondDistToCell Y b')) * ‖e‖ * ‖e'‖) →
    IsCutoffDominated ρ κ (C * A) p q Y (radialPart S G)
end ResponseInTheExpansion
end YangMills.Construction
end
