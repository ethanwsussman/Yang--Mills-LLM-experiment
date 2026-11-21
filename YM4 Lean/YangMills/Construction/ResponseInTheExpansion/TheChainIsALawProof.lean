import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheChainProof
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusLumps TorusFields StepCosts
namespace WeightedResponses.ChainLaw
theorem measurable_finalField (ℓ : StepParameters) : (s n : ℕ) → Measurable (finalField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_snd.comp measurable_snd
theorem measurable_initialField (ℓ : StepParameters) : (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem wilsonWeight_eq_exp (β : ℝ) (m : ℕ) [NeZero m] :
    wilsonWeight β m = fun U => Real.exp (-β * wilsonAction Finset.univ U) := by
  funext U
  simp [wilsonWeight, NeZero.ne m]
theorem continuous_wilsonWeight (β : ℝ) (m : ℕ) [NeZero m] : Continuous (wilsonWeight β m) := by apply _root_.YangMills.Construction.WeightedResponses.continuous_wilsonWeight <;> assumption
theorem wilsonWeight_pos (β : ℝ) (m : ℕ) [NeZero m] (U : TorusField m) : 0 < wilsonWeight β m U := by
  rw [wilsonWeight_eq_exp]
  exact Real.exp_pos _
theorem integral_wilsonWeight_pos (β : ℝ) (m : ℕ) [NeZero m] :
    0 < ∫ U, wilsonWeight β m U ∂(fieldHaar m) := by
  have hc := continuous_wilsonWeight β m
  have hi : Integrable (wilsonWeight β m) (fieldHaar m) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [wilsonWeight_eq_exp] at hi ⊢
  exact integral_exp_pos hi
theorem kernelImage_eq_integral (y : ℝ) (D : TorusFunctional) (V : TorusField n) :
    kernelImage ℓ y D n V = ∫ W : TorusField (n * ℓ.side), D (n * ℓ.side) W *
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar (n * ℓ.side)) := by
  simp only [kernelImage, NeZero.ne n, dite_false]
theorem averagedKernel_eq_sum (y : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n) :
    averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) =
      ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V := by
  classical
  unfold averagedKernel stepTransitionDensity
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
theorem averagedKernel_bounded (hS : StepTransitionDensityBounds) (y : ℝ) :
    ∃ C : ℝ, ∀ (W : TorusField (n * ℓ.side)) (V : TorusField n),
      0 ≤ averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∧
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ≤ C := by
  obtain ⟨C, hC⟩ := (hS ℓ y n).2
  refine ⟨∑ _b : BaseChoice ℓ.side n, C, fun W V => ?_⟩
  rw [averagedKernel_eq_sum]
  exact ⟨Finset.sum_nonneg fun b _ => (hC W b V).1, Finset.sum_le_sum fun b _ => (hC W b V).2⟩
theorem measurable_averagedKernel (hB : BondKernelBorel) (y : ℝ) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 p.2) :=
  (hB ℓ y n).2.2.2.2.2.2.1
theorem averagedKernel_pos (hBs : BaseChoicesNonempty) (hK : BondKernelProperties)
    (hfit : ℓ.Admissible) (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (y : ℝ)
    (W : TorusField (n * ℓ.side)) (V : TorusField n) :
    0 < averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by
  have hne := hBs ℓ hfit hLam n (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
  unfold averagedKernel
  refine mul_pos (by positivity) (Finset.sum_pos (fun b _ => Finset.prod_pos fun c _ => ?_) hne)
  exact (hK.2 ℓ y n _ _ b c).1
theorem chainFunctional_measurable_pos_bounded (hS : StepTransitionDensityBounds)
    (hB : BondKernelBorel) (hBs : BaseChoicesNonempty) (hK : BondKernelProperties)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (β : ℝ) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → Measurable (chainFunctional ℓ β x s n) ∧
      (∀ V, 0 < chainFunctional ℓ β x s n V) ∧ ∃ C : ℝ, ∀ V, chainFunctional ℓ β x s n V ≤ C
  | 0, n, _ => by
    refine ⟨(continuous_wilsonWeight β n).measurable, fun V => wilsonWeight_pos β n V, ?_⟩
    obtain ⟨C, hC⟩ :=
      isCompact_univ.exists_bound_of_continuousOn (continuous_wilsonWeight β n).continuousOn
    refine ⟨C, fun V => ?_⟩
    have h := hC V (Set.mem_univ V)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  | s + 1, n, _ => by
    obtain ⟨hm, h0, C, hC⟩ :=
      chainFunctional_measurable_pos_bounded hS hB hBs hK ℓ hfit hLam β x s (n * ℓ.side)
    obtain ⟨K, hKb⟩ := averagedKernel_bounded (ℓ := ℓ) (n := n) hS (x s)
    have hform : chainFunctional ℓ β x (s + 1) n = fun V =>
        ∫ W : TorusField (n * ℓ.side), chainFunctional ℓ β x s (n * ℓ.side) W *
          averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar (n * ℓ.side)) := by
      funext V
      exact kernelImage_eq_integral _ _ V
    have hs : Measurable (Prod.snd : TorusField n × TorusField (n * ℓ.side) → TorusField (n * ℓ.side)) :=
      measurable_snd
    have hsw : Measurable (Prod.swap : TorusField n × TorusField (n * ℓ.side) →
        TorusField (n * ℓ.side) × TorusField n) := measurable_swap
    have hjoint : Measurable (Function.uncurry fun (V : TorusField n) (W : TorusField (n * ℓ.side)) =>
        chainFunctional ℓ β x s (n * ℓ.side) W *
          averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) := by
      have h1 := hm.comp hs
      have h2 := (measurable_averagedKernel (ℓ := ℓ) (n := n) hB (x s)).comp hsw
      exact h1.mul h2
    have hC0 : 0 ≤ C := (h0 (trivialField _)).le.trans (hC _)
    have hb : ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)),
        ‖chainFunctional ℓ β x s (n * ℓ.side) W *
          averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V)‖ ≤ C * K := by
      intro V W
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 W).le (hKb W V).1)]
      exact mul_le_mul (hC W) (hKb W V).2 (hKb W V).1 hC0
    refine ⟨?_, fun V => ?_, C * K, fun V => ?_⟩
    · rw [hform]
      exact hjoint.stronglyMeasurable.integral_prod_right.measurable
    · rw [hform]
      have hi : Integrable (fun W : TorusField (n * ℓ.side) => chainFunctional ℓ β x s (n * ℓ.side) W *
          averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
          (fieldHaar (n * ℓ.side)) := by
        refine Integrable.of_bound ?_ (C * K) (Filter.Eventually.of_forall (hb V))
        have hpk : Measurable fun W : TorusField (n * ℓ.side) => (V, W) := measurable_prodMk_left
        exact (hjoint.comp hpk).aestronglyMeasurable
      refine (integral_pos_iff_support_of_nonneg
        (fun W => mul_nonneg (h0 W).le (hKb W V).1) hi).2 ?_
      have hsup : Function.support (fun W : TorusField (n * ℓ.side) =>
          chainFunctional ℓ β x s (n * ℓ.side) W *
            averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) = Set.univ := by
        ext W
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact (mul_pos (h0 W) (averagedKernel_pos hBs hK hfit hLam (x s) W V)).ne'
      rw [hsup]
      simp
    · rw [hform]
      have h := norm_integral_le_of_norm_le_const (μ := fieldHaar (n * ℓ.side))
        (Filter.Eventually.of_forall (hb V))
      simp only [probReal_univ, mul_one] at h
      exact (le_abs_self _).trans h
theorem sum_integral_stepTransitionDensity (hO : ScoreProductStepMean) (hfit : ℓ.Admissible) (y : ℝ)
    (W : TorusField (n * ℓ.side)) :
    ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n, stepTransitionDensity ℓ y W b V ∂(fieldHaar n) = 1 := by
  have h := hO ℓ hfit hfit.depth_lt y n W 0 (fun i => i.elim0) (fun i => i.elim0) (fun _ i => i.elim0)
  simpa using h
theorem integral_chainJointLaw_zero (hM : ChainStepMean) (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ)
    (n : ℕ) [NeZero n] (G : TorusField n → ℝ) : ∫ u, G u ∂(chainJointLaw ℓ β x 0 n) =
      (∫ W, G W * wilsonWeight β n W ∂(fieldHaar n)) / ∫ W, wilsonWeight β n W ∂(fieldHaar n) := by
  rw [(hM ℓ β x).2.1 n G, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only
  ring
theorem integral_initialField (hM : ChainStepMean) (hO : ScoreProductStepMean)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) (β : ℝ) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (G : TorusField (fineSide ℓ.side s n) → ℝ) → Measurable G →
      (∃ C : ℝ, ∀ W, |G W| ≤ C) →
      ∫ u, G (initialField ℓ s n u) ∂(chainJointLaw ℓ β x s n) =
        (∫ W, G W * wilsonWeight β (fineSide ℓ.side s n) W ∂(fieldHaar (fineSide ℓ.side s n))) /
          initialMass ℓ β s n
  | 0, n, _, G, _, _ => integral_chainJointLaw_zero hM ℓ β x n G
  | s + 1, n, _, G, hG, hb => by
    obtain ⟨C, hC⟩ := hb
    have hstep : ∫ u, G (initialField ℓ (s + 1) n u) ∂(chainJointLaw ℓ β x (s + 1) n) =
        ∫ u, G (initialField ℓ s (n * ℓ.side) u) ∂(chainJointLaw ℓ β x s (n * ℓ.side)) := by
      refine (hM ℓ β x).2.2 s n _ _ (hG.comp (measurable_initialField ℓ (s + 1) n))
        ⟨C, fun u => hC _⟩ fun u => ?_
      show ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n, G (initialField ℓ s (n * ℓ.side) u) *
        stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) u) b V ∂(fieldHaar n) = _
      simp only [integral_const_mul]
      rw [← Finset.mul_sum, sum_integral_stepTransitionDensity hO hfit, mul_one]
    rw [hstep]
    exact integral_initialField hM hO ℓ hfit β x s (n * ℓ.side) G hG ⟨C, hC⟩
theorem integral_finalField (hM : ChainStepMean) (hS : StepTransitionDensityBounds)
    (hB : BondKernelBorel) (hBs : BaseChoicesNonempty) (hK : BondKernelProperties)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (β : ℝ) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (G : TorusField n → ℝ) → Measurable G → (∃ C : ℝ, ∀ V, |G V| ≤ C) →
      ∫ u, G (finalField ℓ s n u) ∂(chainJointLaw ℓ β x s n) =
        (∫ V, G V * chainFunctional ℓ β x s n V ∂(fieldHaar n)) / initialMass ℓ β s n
  | 0, n, _, G, _, _ => integral_chainJointLaw_zero hM ℓ β x n G
  | s + 1, n, _, G, hG, hb => by
    obtain ⟨C, hC⟩ := hb
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (trivialField n))
    obtain ⟨hm, h0, Dm, hD⟩ :=
      chainFunctional_measurable_pos_bounded hS hB hBs hK ℓ hfit hLam β x s (n * ℓ.side)
    have hD0 : 0 ≤ Dm := (h0 (trivialField _)).le.trans (hD _)
    obtain ⟨K, hKb⟩ := averagedKernel_bounded (ℓ := ℓ) (n := n) hS (x s)
    have hK0 : 0 ≤ K := (hKb (trivialField _) (trivialField _)).1.trans (hKb (trivialField _) (trivialField _)).2
    have hker := measurable_averagedKernel (ℓ := ℓ) (n := n) hB (x s)
    have hs : Measurable (Prod.snd : TorusField (n * ℓ.side) × TorusField n → TorusField n) :=
      measurable_snd
    have hfst : Measurable (Prod.fst : TorusField (n * ℓ.side) × TorusField n →
        TorusField (n * ℓ.side)) := measurable_fst
    have hGK : Measurable (Function.uncurry fun (W : TorusField (n * ℓ.side)) (V : TorusField n) =>
        G V * averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) := by
      have h1 := hG.comp hs
      exact h1.mul hker
    set H : TorusField (n * ℓ.side) → ℝ := fun W => ∫ V, G V *
      averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar n) with hH
    have hHm : Measurable H := hGK.stronglyMeasurable.integral_prod_right.measurable
    have hGKb : ∀ (W : TorusField (n * ℓ.side)) (V : TorusField n), ‖G V *
        averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V)‖ ≤ C * K := by
      intro W V
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKb W V).1]
      exact mul_le_mul (hC V) (hKb W V).2 (hKb W V).1 hC0
    have hHb : ∀ W, |H W| ≤ C * K := by
      intro W
      have h := norm_integral_le_of_norm_le_const (μ := fieldHaar n) (Filter.Eventually.of_forall (hGKb W))
      simp only [probReal_univ, mul_one] at h
      exact h
    have hstep : ∫ u, G (finalField ℓ (s + 1) n u) ∂(chainJointLaw ℓ β x (s + 1) n) =
        ∫ u, H (finalField ℓ s (n * ℓ.side) u) ∂(chainJointLaw ℓ β x s (n * ℓ.side)) := by
      refine (hM ℓ β x).2.2 s n _ _ (hG.comp (measurable_finalField ℓ (s + 1) n))
        ⟨C, fun u => hC _⟩ fun u => ?_
      show ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n, G V *
        stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) u) b V ∂(fieldHaar n) = _
      obtain ⟨C', hC'⟩ := (hS ℓ (x s) n).2
      have hint : ∀ b : BaseChoice ℓ.side n, Integrable (fun V : TorusField n => G V *
          stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) u) b V) (fieldHaar n) := by
        intro b
        have hpk : Measurable fun V : TorusField n => (finalField ℓ s (n * ℓ.side) u, V) :=
          measurable_prodMk_left
        have h1 := ((hS ℓ (x s) n).1 b).comp hpk
        refine Integrable.of_bound (hG.mul h1).aestronglyMeasurable (C * C')
          (Filter.Eventually.of_forall fun V => ?_)
        have h2 := hC' (finalField ℓ s (n * ℓ.side) u) b V
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
        exact mul_le_mul (hC V) h2.2 h2.1 hC0
      rw [← integral_finset_sum _ fun b _ => hint b]
      show _ = ∫ V, G V * averagedKernel ℓ (x s)
        (readAtLevel (stepBlockFrame ℓ.side n) 0 (finalField ℓ s (n * ℓ.side) u))
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar n)
      refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      show ∑ b : BaseChoice ℓ.side n, G V * stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) u) b V =
        G V * averagedKernel ℓ (x s)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 (finalField ℓ s (n * ℓ.side) u))
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
      rw [averagedKernel_eq_sum, Finset.mul_sum]
    rw [hstep, integral_finalField hM hS hB hBs hK ℓ hfit hLam β x s (n * ℓ.side) H hHm ⟨C * K, hHb⟩]
    have hswap : ∫ W, H W * chainFunctional ℓ β x s (n * ℓ.side) W ∂(fieldHaar (n * ℓ.side)) =
        ∫ V, G V * chainFunctional ℓ β x (s + 1) n V ∂(fieldHaar n) := by
      have hjoint : Measurable (Function.uncurry fun (W : TorusField (n * ℓ.side)) (V : TorusField n) =>
          G V * averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V) *
              chainFunctional ℓ β x s (n * ℓ.side) W) := by
        have h1 := hm.comp hfst
        exact hGK.mul h1
      have hint : Integrable (Function.uncurry fun (W : TorusField (n * ℓ.side)) (V : TorusField n) =>
          G V * averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V) *
              chainFunctional ℓ β x s (n * ℓ.side) W)
          ((fieldHaar (n * ℓ.side)).prod (fieldHaar n)) := by
        refine Integrable.of_bound hjoint.aestronglyMeasurable (C * K * Dm)
          (Filter.Eventually.of_forall fun p => ?_)
        have h1 := hGKb p.1 p.2
        have h2 := hD p.1
        have h3 := (h0 p.1).le
        simp only [Function.uncurry]
        rw [norm_mul, Real.norm_eq_abs (chainFunctional ℓ β x s (n * ℓ.side) p.1), abs_of_nonneg h3]
        exact mul_le_mul h1 h2 h3 (by positivity)
      calc ∫ W, H W * chainFunctional ℓ β x s (n * ℓ.side) W ∂(fieldHaar (n * ℓ.side))
          = ∫ W, ∫ V, G V * averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V) *
              chainFunctional ℓ β x s (n * ℓ.side) W ∂(fieldHaar n) ∂(fieldHaar (n * ℓ.side)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            simp only [hH]
            rw [integral_mul_const]
        _ = ∫ V, ∫ W, G V * averagedKernel ℓ (x s) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V) *
              chainFunctional ℓ β x s (n * ℓ.side) W ∂(fieldHaar (n * ℓ.side)) ∂(fieldHaar n) :=
            integral_integral_swap hint
        _ = ∫ V, G V * chainFunctional ℓ β x (s + 1) n V ∂(fieldHaar n) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
            show _ = G V * kernelImage ℓ (x s) (chainFunctional ℓ β x s) n V
            rw [kernelImage_eq_integral, ← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            simp only
            ring
    rw [hswap]
    rfl
theorem chainIsProbabilityLaw (hM : ChainStepMean) (hO : ScoreProductStepMean)
    (hS : StepTransitionDensityBounds) (hB : BondKernelBorel) (hBs : BaseChoicesNonempty)
    (hK : BondKernelProperties) : ChainIsProbabilityLaw := by
  intro ℓ hfit hLam β x s n _
  have hZ : 0 < initialMass ℓ β s n := integral_wilsonWeight_pos β _
  have hbot := integral_initialField hM hO ℓ hfit β x s n
  have htop := integral_finalField hM hS hB hBs hK ℓ hfit hLam β x s n
  have hone : ∫ _u, (1 : ℝ) ∂(chainJointLaw ℓ β x s n) = 1 := by
    have h := hbot (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    simp only [one_mul] at h
    rw [h]
    exact div_self hZ.ne'
  obtain ⟨hm, h0, hb⟩ := chainFunctional_measurable_pos_bounded hS hB hBs hK ℓ hfit hLam β x s n
  refine ⟨?_, hZ, hm, h0, hb, ?_, ?_, htop, hbot⟩
  · refine ⟨?_⟩
    have h : (chainJointLaw ℓ β x s n).real Set.univ = 1 := by
      simpa using hone
    have h2 := (ENNReal.toReal_eq_one_iff _).mp h
    exact h2
  · intro V
    obtain ⟨hm', h0', Dm, hD⟩ :=
      chainFunctional_measurable_pos_bounded hS hB hBs hK ℓ hfit hLam β x s (n * ℓ.side)
    obtain ⟨K, hKb⟩ := averagedKernel_bounded (ℓ := ℓ) (n := n) hS (x s)
    have hker := measurable_averagedKernel (ℓ := ℓ) (n := n) hB (x s)
    have hpk : Measurable fun W : TorusField (n * ℓ.side) => (W, V) := measurable_prodMk_right
    have h1 := hker.comp hpk
    refine Integrable.of_bound (hm'.mul h1).aestronglyMeasurable (Dm * K)
      (Filter.Eventually.of_forall fun W => ?_)
    have hk := hKb W V
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0' W).le hk.1)]
    exact mul_le_mul (hD W) hk.2 hk.1 ((h0' W).le.trans (hD W))
  · have h := htop (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    simp only [one_mul] at h
    rw [hone] at h
    have := (eq_div_iff hZ.ne').mp h
    linarith
end WeightedResponses.ChainLaw
end YangMills.Construction
end
