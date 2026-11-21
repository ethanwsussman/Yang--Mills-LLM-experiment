import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.TiltsOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open Dobrushin StepSettings StepGas TorusFields CoreColumns WeightedResponses FreeEnergies
variable {R : StepSetup} {n : ℕ} [NeZero n]
def spinScore (A : ResponseSetup R) (G : GasGround R n) (S : Finset (TorusSite (n * R.params.side)))
    (σ : G.Config) : ℝ :=
  1 + (S.card : ℝ)⁻¹ * ∑ y ∈ S, (recordedSiteScore A G y + ∑ i, spinLabelScore A.score G i y (σ i))
def GasSupportMeanFarSpinBound : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
    weightNorm R.params.side (R.depth + 1) f ≤ 1 → (upperSites f).Nonempty →
    (open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then gasSupportMean A G f σ else 0) ∧
    (∀ σ, G.pairConstraint.IsAdmissible σ →
      |gasSupportMean A G f σ| ≤ 4 * lowerSizeConst A f * spinScore A G (lowerSites f) σ) ∧
    ∀ (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) (m : ℕ),
      G.pairConstraint.IsAdmissible (Function.update σ i v) →
      (R.range : ℝ) / (4 * R.params.side) ≤ m → (∀ Y ∈ upperSites f, m + 2 ≤ setGap {Y} i.1.core) →
      |gasSupportMean A G f (Function.update σ i v) -
          gasSupportMean A G f (Function.update σ i (G.pairConstraint.vacant i))| ≤
        4 * lowerSizeConst A f * spinScore A G (lowerSites f) (Function.update σ i (G.pairConstraint.vacant i)) *
          Real.exp (-(R.params.rt * m / 2 ^ 5))
end ResponseInTheExpansion
end YangMills.Construction
end
