import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames
variable {F : BlockAverages.BlockFrame}
def cutoffMajorant (p : ℝ → ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) : ℝ :=
  1 + WeightedResponses.ColdHalfLaw.sumOverBlock Y fun b => |deriv p ‖η b‖| + |deriv (deriv p) ‖η b‖|
structure IsCutoffDominated (ρ κ M : ℝ) (p : ℝ → ℝ) (q : ℕ) (Y : F.Cell) (A : StepVariable (finiteCells F) → ℝ) :
    Prop where
  smooth : ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ}
  abs_le : ∀ η, (∀ b, ‖η b‖ < ρ) → |A η| ≤ M * cutoffMajorant p Y η
  gradient_le : ∀ η, (∀ b, ‖η b‖ < ρ) → ∀ b,
    bondGradNorm A b η ≤ M * Real.exp (-(2 * κ * TorusComparison.bondDistToCell Y b)) * cutoffMajorant p Y η
  freeze_le : ∀ η, (∀ b, ‖η b‖ < ρ) →
    |A η - A (TorusComparison.freezeOutside (TorusComparison.bondsNearCell Y q) η)| ≤ M * Real.exp (-(4 * κ * q))
def DominatedObservablesComparableWith (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockAverages.BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (j : ι → ↥(BlockAverages.chordBonds (finiteCells F)))
    (K : WeightedResponses.AboveFrames F) (M : ℝ), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' → TorusComparison.IsShortPairing Y Y q j j →
    0 ≤ M →
    IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η V) →
    IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η V') →
    (T.blockIndex ≤ q → ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < T.ballRadius) →
      |K (TorusComparison.toTorus j ζ) V - K (TorusComparison.toTorus j ζ) V'| ≤ M * Real.exp (-(4 * T.κ * q))) →
    IsComparablePair T x f (C * M) q Y Y j j K K V V'
def DominatedObservablesComparable : Prop :=
  EventuallyInParameters fun T => ∃ C : ℝ, 0 ≤ C ∧ DominatedObservablesComparableWith T C
end YangMills.Construction.ResponseInTheExpansion
end
