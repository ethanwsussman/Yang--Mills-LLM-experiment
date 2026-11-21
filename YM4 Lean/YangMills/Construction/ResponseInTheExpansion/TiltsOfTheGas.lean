import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCores
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open Dobrushin StepSettings StepGas TorusFields CoreColumns
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def spinLabelScore (s : R.labels.Ω → ℝ) (G : GasGround R n) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    G.SpinValue i → ℝ :=
  Sum.elim (fun _ => 0) fun w => if h : y ∈ i.1.2 then s (w.1.2.1 ⟨y, h⟩) else 0
structure IsGasTilt (G : GasGround R n) (s : R.labels.Ω → ℝ) (Q : Finset (TorusSite n))
    (B : Finset (TorusSite (n * R.params.side))) (e : ℝ) (F : G.Config → ℝ) : Prop where
  measurable : Measurable F
  pos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < F σ
  update_le : ∀ (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i),
    G.pairConstraint.IsAdmissible (Function.update σ i v) →
    F (Function.update σ i v) ≤
      3 * Real.exp (∑ y ∈ B, spinLabelScore s G i y v) * F (Function.update σ i (G.pairConstraint.vacant i))
  abs_update_sub_le : ∀ (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) (m : ℕ),
    G.pairConstraint.IsAdmissible (Function.update σ i v) →
    (R.range : ℝ) / (4 * R.params.side) ≤ m → (∀ Y ∈ Q, m + 2 ≤ setGap {Y} i.1.core) →
    |F (Function.update σ i v) - F (Function.update σ i (G.pairConstraint.vacant i))| ≤
      e * Real.exp (-(R.params.rt * m / 2 ^ 5)) * F (Function.update σ i (G.pairConstraint.vacant i))
def tiltedGibbsLaw (G : GasGround R n) (F : G.Config → ℝ) : Measure G.Config :=
  G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) fun σ => G.weight σ * F σ
end ResponseInTheExpansion
end YangMills.Construction
end
