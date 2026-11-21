import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOne
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps BlockAverages
variable {ℓ : StepParameters}
def stepExpectation (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] (F : TorusField n → ENNReal)
    (W : TorusField (n * ℓ.side)) : ENNReal :=
  ∫⁻ V, ENNReal.ofReal (averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)) * F V ∂(fieldHaar n)
def chainExpectation (ℓ : StepParameters) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (TorusField n → ENNReal) → TorusField (fineSide ℓ.side s n) → ENNReal
  | 0, _, _, F => F
  | s + 1, n, _, F => chainExpectation ℓ x s (n * ℓ.side) (stepExpectation ℓ (x s) F)
def DependsOnlyNear {n : ℕ} {E : Type} (z : TorusSite n) (r : ℕ) (F : TorusField n → E) : Prop :=
  ∀ V V' : TorusField n, (∀ x, supDist x z ≤ r → ∀ i, V x i = V' x i) → F V = F V'
def iteratedScaledLift (L : ℕ) : ℕ → TorusIsometry → TorusIsometry
  | 0, g => g
  | s + 1, g => iteratedScaledLift L s (g.scaledLift L)
def descendedRadius (L : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | s + 1, r => descendedRadius L s (L * r + 4 * L)
section Facts
variable {n : ℕ} [NeZero n]
theorem measurable_stepExpectation (hB : BondKernelBorel) (x : ℝ) {F : TorusField n → ENNReal}
    (hF : Measurable F) : Measurable (stepExpectation ℓ x F) := by
  have h1 := (hB ℓ x n).2.2.2.2.2.2.1
  have h2 : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      ENNReal.ofReal (averagedKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2)) * F p.2 :=
    h1.ennreal_ofReal.mul (hF.comp measurable_snd)
  exact h2.lintegral_prod_right'
theorem measurable_averagedKernel_right (hB : BondKernelBorel) (x : ℝ) (W : TorusField (n * ℓ.side)) :
    Measurable fun V : TorusField n => averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) := by
  have h0 := (hB ℓ x n).2.2.2.2.2.2.1
  have hp : Measurable fun V : TorusField n => ((W, V) : TorusField (n * ℓ.side) × TorusField n) :=
    measurable_prodMk_left
  have h1 := h0.comp hp
  exact h1
theorem averagedKernel_nonneg (hK : BondKernelProperties) (x : ℝ)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1) :
    0 ≤ averagedKernel ℓ x W V := by
  unfold averagedKernel
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => Finset.prod_nonneg fun c _ => ?_)
  exact (hK.2 ℓ x n W V b c).1.le
theorem lintegral_averagedKernel (hK : BondKernelProperties) (hM : AveragedKernelIntegralOne)
    (hfit : ℓ.Admissible) (hL : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (x : ℝ) (W : TorusField (n * ℓ.side)) :
    ∫⁻ V, ENNReal.ofReal (averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)) ∂(fieldHaar n)
      = 1 := by
  have h1 := hM ℓ hfit hL x n (fineLevelField ℓ n W)
  have hint : Integrable (fun V : TorusField n =>
      averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)) (fieldHaar n) := by
    by_contra hcon
    have h2 := integral_undef hcon
    have h3 : ∫ V : TorusField n, averagedKernel ℓ x (fineLevelField ℓ n W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar n) = 0 := h2
    rw [h3] at h1
    norm_num at h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun V => averagedKernel_nonneg hK x _ _)]
  have h4 : ∫ V : TorusField n, averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)
      ∂(fieldHaar n) = 1 := h1
  rw [h4, ENNReal.ofReal_one]
theorem stepExpectation_le_one (hK : BondKernelProperties) (hM : AveragedKernelIntegralOne)
    (hfit : ℓ.Admissible) (hL : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (x : ℝ)
    {F : TorusField n → ENNReal} (hF : ∀ V, F V ≤ 1) (W : TorusField (n * ℓ.side)) :
    stepExpectation ℓ x F W ≤ 1 := by
  rw [← lintegral_averagedKernel hK hM hfit hL x W]
  refine lintegral_mono fun V => ?_
  calc ENNReal.ofReal _ * F V ≤ ENNReal.ofReal _ * 1 := by gcongr; exact hF V
    _ = _ := mul_one _
end Facts
end YangMills.Construction.WeightedResponses
end
