import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps FreeEnergies
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def classResponsePart (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (σ : G.Config) : ℝ :=
  if G.pairConstraint.IsAdmissible σ ∧ ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i then
    chartResponse A (configSetting G σ) y h else 0
def classResponsePartFarTiltStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side))
      (Q : Finset (TorusSite n)) (B : Finset (TorusSite (n * R.params.side))) (e : ℝ) (Yt : G.Config → ℝ) (D : ℕ),
      weightNorm R.params.side R.depth h ≤ 1 → 2 ^ 10 * R.range ≤ D → Q.Nonempty →
      (∀ Y' ∈ Q, D ≤ supDist (parentBlock R.params.side y) Y') → y ∉ B → 1 ≤ e →
      IsGasTilt G A.score Q B e Yt →
      Integrable (classResponsePart A G y h) (tiltedGibbsLaw G Yt) ∧
      Integrable (classResponsePart A G y h) (G.gibbsLaw ∅) ∧
      |∫ σ, classResponsePart A G y h σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (classResponsePart A G y h)| ≤
        C * e * (Q.card : ℝ) * Real.exp (-(6 * T.gasRate * R.coupling) - R.params.rt * D / 2 ^ 6)
end YangMills.Construction.ResponseInTheExpansion
end
