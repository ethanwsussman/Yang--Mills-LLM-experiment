import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.FormsOnATorus.ChainMeansAreCarried
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields FieldHaar BlockAverages
variable {p : StepParameters}
private theorem stepExpectation_transported (hI : IsometriesPreserveAveragedKernel)
    (hH : HaarInvariantUnderSymmetries) (hB : BondKernelBorel) (hadm : p.Admissible) (x : ℝ) {n : ℕ} [NeZero n]
    (hn : p.n₀ ≤ n) (g : TorusIsometry)
    {F F' : TorusField n → ENNReal} (hF' : Measurable F') (hFF : ∀ V V', g.Transports V V' → F' V' = F V)
    {W W' : TorusField (n * p.side)} (hW : (g.scaledLift p.side).Transports W W') :
    stepExpectation p x F' W' = stepExpectation p x F W := by
  obtain ⟨Ψ, hmp, hc⟩ := (hH n).2 g
  have hmeas : Measurable fun V : TorusField n =>
      ENNReal.ofReal (averagedKernel p x (fineLevelField p n W') (coarseLevelField p n V)) * F' V :=
    (measurable_averagedKernel_right hB x W').ennreal_ofReal.mul hF'
  unfold stepExpectation
  rw [← hmp.lintegral_comp hmeas]
  refine lintegral_congr fun V => ?_
  rw [hI p hadm x n hn g W W' V (Ψ V) hW (hc V), hFF V (Ψ V) (hc V)]
theorem chainExpectationsTransported_of_isometries (hI : IsometriesPreserveAveragedKernel)
    (hH : HaarInvariantUnderSymmetries) (hB : BondKernelBorel) : ChainExpectationsTransported := by
  intro p hadm x s
  induction s with
  | zero =>
    intro n _ _ g F F' _ _ hFF U U' h
    exact hFF U U' h
  | succ s ih =>
    intro n _ hn g F F' hF hF' hFF U U' h
    have hL : 1 ≤ p.side := by have := hadm.L_ge; omega
    exact ih (n * p.side) (hn.trans (Nat.le_mul_of_pos_right _ hL)) (g.scaledLift p.side)
      (stepExpectation p (x s) F) (stepExpectation p (x s) F')
      (measurable_stepExpectation hB _ hF) (measurable_stepExpectation hB _ hF')
      (fun W W' hW => stepExpectation_transported hI hH hB hadm _ hn g hF' hFF hW) U U' h
end YangMills.Construction.WeightedResponses
end
