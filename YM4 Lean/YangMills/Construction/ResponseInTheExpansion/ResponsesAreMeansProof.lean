import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreMeans
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALawProof
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps WeightedResponses StepCosts
namespace ConditionalMeans
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem averagedKernel_eq_sum_stepTransitionDensity (y : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n) :
    averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) =
      ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V := by apply _root_.YangMills.Construction.WeightedResponses.ChainLaw.averagedKernel_eq_sum <;> assumption
theorem integral_weighted_mean_bounds (hS : StepTransitionDensityBounds) (y : ℝ)
    (D : TorusField (n * ℓ.side) → ℝ) (hDm : Measurable D)
    (hD0 : ∀ W, 0 < D W) (hDb : ∃ C : ℝ, ∀ W, D W ≤ C)
    (Φ : TorusField (n * ℓ.side) → BaseChoice ℓ.side n → TorusField n → ℝ)
    (hΦ : ∀ b, Measurable fun p : TorusField (n * ℓ.side) × TorusField n => Φ p.1 b p.2) {B : ℝ}
    (hB : ∀ W b V, |Φ W b V| ≤ B) :
    (∀ V, Integrable (fun W => D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V)
      (fieldHaar (n * ℓ.side))) ∧
    Measurable (fun V : TorusField n => ∫ W, D W * ∑ b : BaseChoice ℓ.side n,
      stepTransitionDensity ℓ y W b V * Φ W b V ∂(fieldHaar (n * ℓ.side))) ∧
    ∀ V, |∫ W, D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V
        ∂(fieldHaar (n * ℓ.side))| ≤
      B * ∫ W, D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V ∂(fieldHaar (n * ℓ.side)) := by
  obtain ⟨Dc, hDc⟩ := hDb
  obtain ⟨hSm, C', hC'⟩ := hS ℓ y n
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (trivialField _) (Classical.arbitrary _) (trivialField _))
  have hsw : Measurable fun q : TorusField n × TorusField (n * ℓ.side) =>
      ((q.2, q.1) : TorusField (n * ℓ.side) × TorusField n) :=
    measurable_snd.prodMk measurable_fst
  have hsnd : Measurable (Prod.snd : TorusField n × TorusField (n * ℓ.side) → TorusField (n * ℓ.side)) :=
    measurable_snd
  have hst : ∀ b, Measurable fun q : TorusField n × TorusField (n * ℓ.side) =>
      stepTransitionDensity ℓ y q.2 b q.1 := fun b => by
    have h2 := (hSm b).comp hsw
    exact h2
  have hph : ∀ b, Measurable fun q : TorusField n × TorusField (n * ℓ.side) => Φ q.2 b q.1 := fun b => by
    have h3 := (hΦ b).comp hsw
    exact h3
  have hjoint : Measurable (Function.uncurry fun (V : TorusField n) (W : TorusField (n * ℓ.side)) =>
      D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V) := by
    have h1 := hDm.comp hsnd
    have h4 : Measurable fun q : TorusField n × TorusField (n * ℓ.side) =>
        ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y q.2 b q.1 * Φ q.2 b q.1 :=
      Finset.measurable_sum _ fun b _ => (hst b).mul (hph b)
    exact h1.mul h4
  have hjoint1 : Measurable (Function.uncurry fun (V : TorusField n) (W : TorusField (n * ℓ.side)) =>
      D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V) := by
    have h1 := hDm.comp hsnd
    have h4 : Measurable fun q : TorusField n × TorusField (n * ℓ.side) =>
        ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y q.2 b q.1 :=
      Finset.measurable_sum _ fun b _ => hst b
    exact h1.mul h4
  have hbase : ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)),
      ‖D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V‖ ≤
        B * (D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V) := by
    intro V W
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hD0 W)]
    have h1 : |∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V| ≤
        B * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [abs_mul, abs_of_nonneg (hC' W b V).1, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB W b V) (hC' W b V).1
    calc D W * |∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V|
        ≤ D W * (B * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V) :=
          mul_le_mul_of_nonneg_left h1 (hD0 W).le
      _ = _ := by ring
  have hD00 : 0 ≤ Dc := (hD0 (trivialField _)).le.trans (hDc _)
  have hsum : ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)),
      ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V ≤ ∑ _b : BaseChoice ℓ.side n, C' :=
    fun V W => Finset.sum_le_sum fun b _ => (hC' W b V).2
  have hsum0 : ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)),
      0 ≤ ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V :=
    fun V W => Finset.sum_nonneg fun b _ => (hC' W b V).1
  have hint1 : ∀ V, Integrable (fun W => D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V)
      (fieldHaar (n * ℓ.side)) := by
    intro V
    have hpk : Measurable fun W : TorusField (n * ℓ.side) => (V, W) := measurable_prodMk_left
    refine Integrable.of_bound (hjoint1.comp hpk).aestronglyMeasurable
      (Dc * ∑ _b : BaseChoice ℓ.side n, C') (Filter.Eventually.of_forall fun W => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hD0 W).le (hsum0 V W))]
    exact mul_le_mul (hDc W) (hsum V W) (hsum0 V W) hD00
  have hint : ∀ V, Integrable
      (fun W => D W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V * Φ W b V)
      (fieldHaar (n * ℓ.side)) := by
    intro V
    have hpk : Measurable fun W : TorusField (n * ℓ.side) => (V, W) := measurable_prodMk_left
    refine Integrable.of_bound (hjoint.comp hpk).aestronglyMeasurable
      (B * (Dc * ∑ _b : BaseChoice ℓ.side n, C')) (Filter.Eventually.of_forall fun W => (hbase V W).trans ?_)
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hDc W) (hsum V W) (hsum0 V W) hD00) hB0
  refine ⟨hint, hjoint.stronglyMeasurable.integral_prod_right.measurable, fun V => ?_⟩
  have h := norm_integral_le_of_norm_le ((hint1 V).const_mul B)
    (Filter.Eventually.of_forall (hbase V))
  rw [integral_const_mul] at h
  exact h
theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ z ∈ sitesInBlocks L {Y}, f z = ∑ z, f z := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
theorem sum_site_weighted_bond_pairs (A : TorusSite n → ℝ) (S : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, A Y * ∑ i : Fin 4, (S (Y, i) + S (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (A c.1 + A (c.1 + unitStep n c.2)) * S c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
def responseIntegrand (ℓ : StepParameters) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n)) (W : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) (V : TorusField n) : ℝ :=
  ∑ z ∈ sitesInBlocks ℓ.side {Y}, coldResponseChain ℓ β x al t (n * ℓ.side) z W h +
    ℓ.coupling / 2 * al t * blockMean ℓ.side (t + 1) n Y h * bondScoresAtSite ℓ (x t) W V b Y
theorem coldResponseChain_succ (ℓ : StepParameters) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (Y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n)) (V : TorusField n) :
    coldResponseChain ℓ β x al (t + 1) n Y V h =
      (∫ W, chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n,
        stepTransitionDensity ℓ (x t) W b V * responseIntegrand ℓ β x al t n Y h W b V
          ∂(fieldHaar (n * ℓ.side))) / chainFunctional ℓ β x (t + 1) n V := rfl
theorem chainFunctional_succ (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) :
    chainFunctional ℓ β x (t + 1) n V =
      ∫ W, chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n,
        stepTransitionDensity ℓ (x t) W b V ∂(fieldHaar (n * ℓ.side)) := by
  show kernelImage ℓ (x t) (chainFunctional ℓ β x t) n V = _
  simp only [kernelImage, NeZero.ne n, dite_false, averagedKernel_eq_sum_stepTransitionDensity]
theorem responseIntegrand_measurable_bounded (hT : BondScoreProperties) (ℓ : StepParameters)
    (hfit : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ)
    [NeZero n] (Y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n))
    (hP : ∀ z : TorusSite (n * ℓ.side),
      Measurable (fun W : TorusField (n * ℓ.side) => coldResponseChain ℓ β x al t (n * ℓ.side) z W h) ∧
      ∃ C : ℝ, ∀ W, |coldResponseChain ℓ β x al t (n * ℓ.side) z W h| ≤ C) :
    (∀ b, Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      responseIntegrand ℓ β x al t n Y h p.1 b p.2) ∧
    ∃ B : ℝ, ∀ W b V, |responseIntegrand ℓ β x al t n Y h W b V| ≤ B := by
  have hfst : Measurable (Prod.fst : TorusField (n * ℓ.side) × TorusField n → TorusField (n * ℓ.side)) :=
    measurable_fst
  choose C hC using fun z => (hP z).2
  refine ⟨fun b => ?_, ?_⟩
  · have h1 : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        ∑ z ∈ sitesInBlocks ℓ.side {Y}, coldResponseChain ℓ β x al t (n * ℓ.side) z p.1 h :=
      Finset.measurable_sum _ fun z _ => by
        have := (hP z).1.comp hfst
        exact this
    have h2 : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        bondScoresAtSite ℓ (x t) p.1 p.2 b Y :=
      Finset.measurable_sum _ fun i _ =>
        ((hT ℓ hfit (x t) n b (Y, i)).2.2.2.2).add ((hT ℓ hfit (x t) n b (Y - unitStep n i, i)).2.2.2.2)
    exact h1.add (h2.const_mul _)
  · refine ⟨∑ z ∈ sitesInBlocks ℓ.side {Y}, C z +
      |ℓ.coupling / 2 * al t * blockMean ℓ.side (t + 1) n Y h| * 16, fun W b V => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hC z W)
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hb : ∀ c : TorusBond n, |bondScore ℓ (x t) W V b c| ≤ 2 := fun c =>
        (hT ℓ hfit (x t) n b c).2.2.1 W V
      unfold bondScoresAtSite
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i : Fin 4,
          |bondScore ℓ (x t) W V b (Y, i) + bondScore ℓ (x t) W V b (Y - unitStep n i, i)| ≤ 4 := fun i =>
        (abs_add_le _ _).trans (by linarith [hb (Y, i), hb (Y - unitStep n i, i)])
      calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
        _ = 16 := by simp; norm_num
theorem coldResponseChain_measurable_bounded (hS : StepTransitionDensityBounds) (hT : BondScoreProperties)
    (hL : ChainIsProbabilityLaw) (ℓ : StepParameters) (hfit : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) :
    (t n : ℕ) → [NeZero n] → (Y : TorusSite n) → (h : PlaquetteWeight (fineSide ℓ.side t n)) →
      Measurable (fun W : TorusField n => coldResponseChain ℓ β x al t n Y W h) ∧
      ∃ C : ℝ, ∀ W, |coldResponseChain ℓ β x al t n Y W h| ≤ C
  | 0, n, _, Y, h => by
    have hc : Continuous fun W : TorusField n => coldResponseChain ℓ β x al 0 n Y W h := by
      show Continuous fun W : TorusField n => siteResponse Y W h
      unfold siteResponse plaquetteEnergyOf
      exact continuous_finsetSum _ fun p _ => continuous_const.mul
        (continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2))
    refine ⟨hc.measurable, ?_⟩
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨C, fun W => by simpa using hC W (Set.mem_univ W)⟩
  | t + 1, n, _, Y, h => by
    obtain ⟨-, -, hDm, hD0, hDb, -, -, -, -⟩ := hL ℓ hfit hfit.depth_lt β x t (n * ℓ.side)
    obtain ⟨-, -, hDm', hD0', -, -, -, -, -⟩ := hL ℓ hfit hfit.depth_lt β x (t + 1) n
    obtain ⟨hphi, B, hB⟩ := responseIntegrand_measurable_bounded hT ℓ hfit β x al t n Y h
      fun z => coldResponseChain_measurable_bounded hS hT hL ℓ hfit β x al t (n * ℓ.side) z h
    obtain ⟨-, hnum, hbound⟩ := integral_weighted_mean_bounds hS (x t)
      (chainFunctional ℓ β x t (n * ℓ.side)) hDm hD0 hDb
      (responseIntegrand ℓ β x al t n Y h) hphi hB
    refine ⟨?_, B, fun V => ?_⟩
    · simp only [coldResponseChain_succ]
      exact hnum.div hDm'
    · rw [coldResponseChain_succ, abs_div, abs_of_pos (hD0' V), div_le_iff₀ (hD0' V)]
      have h1 := hbound V
      rw [← chainFunctional_succ] at h1
      exact h1
theorem responseConditionalMean (hS : StepTransitionDensityBounds) (hT : BondScoreProperties)
    (hL : ChainIsProbabilityLaw) : ResponseConditionalMeanStatement := by
  intro ℓ hfit β x al
  refine ⟨fun t n _ Y h => coldResponseChain_measurable_bounded hS hT hL ℓ hfit β x al t n Y h,
    fun t n _ h V => ?_⟩
  obtain ⟨-, -, hDm, hD0, hDb, -, -, -, -⟩ := hL ℓ hfit hfit.depth_lt β x t (n * ℓ.side)
  obtain ⟨-, -, -, hD0', -, -, -, -, -⟩ := hL ℓ hfit hfit.depth_lt β x (t + 1) n
  have hne := (hD0' V).ne'
  simp only [coldResponseChain_succ]
  rw [Finset.sum_mul]
  simp only [div_mul_cancel₀ _ hne]
  have hint : ∀ Y : TorusSite n, Integrable (fun W : TorusField (n * ℓ.side) =>
      chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n,
        stepTransitionDensity ℓ (x t) W b V * responseIntegrand ℓ β x al t n Y h W b V)
      (fieldHaar (n * ℓ.side)) := by
    intro Y
    obtain ⟨hphi, B, hB⟩ := responseIntegrand_measurable_bounded hT ℓ hfit β x al t n Y h
      fun z => coldResponseChain_measurable_bounded hS hT hL ℓ hfit β x al t (n * ℓ.side) z h
    exact (integral_weighted_mean_bounds hS (x t) _ hDm hD0 hDb
      (responseIntegrand ℓ β x al t n Y h) hphi hB).1 V
  rw [← integral_finset_sum _ fun Y _ => hint Y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show ∑ Y : TorusSite n, chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n,
      stepTransitionDensity ℓ (x t) W b V * responseIntegrand ℓ β x al t n Y h W b V = _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [responseIntegrand, bondScoresAtSite, Finset.sum_add_distrib]
  rw [sum_sitesInBlocks ℓ.side fun z => coldResponseChain ℓ β x al t (n * ℓ.side) z W h]
  congr 1
  have h1 := sum_site_weighted_bond_pairs
    (fun Y : TorusSite n => ℓ.coupling / 2 * al t * blockMean ℓ.side (t + 1) n Y h)
    (fun c => bondScore ℓ (x t) W V b c)
  simp only [Finset.sum_add_distrib] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold bondBlockMean
  ring
end ConditionalMeans
end YangMills.Construction.ResponseInTheExpansion
end
