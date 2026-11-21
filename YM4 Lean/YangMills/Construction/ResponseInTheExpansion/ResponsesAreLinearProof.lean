import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreLinear
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreMeans
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps StepCosts
def responseIntegrand (ℓ : StepParameters) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n)) (V : TorusField n) (W : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ z ∈ sitesInBlocks ℓ.side {Y}, coldResponseChain ℓ β x al t (n * ℓ.side) z W h +
    ℓ.coupling / 2 * al t * blockMean ℓ.side (t + 1) n Y h * bondScoresAtSite ℓ (x t) W V b Y
theorem coldResponseChain_succ_eq_conditionalMean (ℓ : StepParameters) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (Y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n)) (V : TorusField n) :
    coldResponseChain ℓ β x al (t + 1) n Y V h =
      conditionalMean ℓ (x t) (chainFunctional ℓ β x t) V (responseIntegrand ℓ β x al t n Y h V) := rfl
theorem integrable_responseIntegrand (hA : ResponseConditionalMeanStatement) (hS : StepTransitionDensityBounds)
    (hT : BondScoreProperties) (hL : ChainIsProbabilityLaw) (ℓ : StepParameters) (hfit : ℓ.Admissible) (β : ℝ)
    (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (Y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n))
    (V : TorusField n) :
    Integrable (fun W => chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n,
      stepTransitionDensity ℓ (x t) W b V * responseIntegrand ℓ β x al t n Y h V W b) (fieldHaar (n * ℓ.side)) := by
  obtain ⟨-, -, hDm, hD0, ⟨Dc, hDc⟩, -⟩ := hL ℓ hfit hfit.depth_lt β x t (n * ℓ.side)
  obtain ⟨hRm, -⟩ := hA ℓ hfit β x al
  obtain ⟨hSm, C', hC'⟩ := hS ℓ (x t) n
  have hsec : Measurable fun W : TorusField (n * ℓ.side) => (W, V) := measurable_prodMk_right
  choose C hC using fun z : TorusSite (n * ℓ.side) => (hRm t (n * ℓ.side) z h).2
  have hsm : ∀ b, Measurable fun W : TorusField (n * ℓ.side) => bondScoresAtSite ℓ (x t) W V b Y := fun b =>
    Finset.measurable_sum _ fun i _ => by
      have h1 := ((hT ℓ hfit (x t) n b (Y, i)).2.2.2.2).comp hsec
      have h2 := ((hT ℓ hfit (x t) n b (Y - unitStep n i, i)).2.2.2.2).comp hsec
      exact h1.add h2
  have hpm : ∀ b, Measurable fun W : TorusField (n * ℓ.side) => responseIntegrand ℓ β x al t n Y h V W b := fun b =>
    (Finset.measurable_sum _ fun z _ => (hRm t (n * ℓ.side) z h).1).add ((hsm b).const_mul _)
  set B : ℝ := ∑ z ∈ sitesInBlocks ℓ.side {Y}, C z +
    |ℓ.coupling / 2 * al t * blockMean ℓ.side (t + 1) n Y h| * 16 with hB
  have hpb : ∀ W b, |responseIntegrand ℓ β x al t n Y h V W b| ≤ B := by
    intro W b
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hC z W)
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hb : ∀ c : TorusBond n, |bondScore ℓ (x t) W V b c| ≤ 2 := fun c => (hT ℓ hfit (x t) n b c).2.2.1 W V
      unfold bondScoresAtSite
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i : Fin 4, |bondScore ℓ (x t) W V b (Y, i) + bondScore ℓ (x t) W V b (Y - unitStep n i, i)| ≤ 4 :=
        fun i => (abs_add_le _ _).trans (by linarith [hb (Y, i), hb (Y - unitStep n i, i)])
      calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
        _ = 16 := by simp; norm_num
  have hmeas : Measurable fun W : TorusField (n * ℓ.side) => chainFunctional ℓ β x t (n * ℓ.side) W *
      ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V * responseIntegrand ℓ β x al t n Y h V W b := by
    refine hDm.mul (Finset.measurable_sum _ fun b _ => ?_)
    have h1 := (hSm b).comp hsec
    exact h1.mul (hpm b)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpb (trivialField _) (Classical.arbitrary _))
  have hDc0 : 0 ≤ Dc := (hD0 (trivialField _)).le.trans (hDc _)
  have hC0' : 0 ≤ C' := (hC' (trivialField _) (Classical.arbitrary _) V).1.trans
    (hC' (trivialField _) (Classical.arbitrary _) V).2
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Dc * ∑ _b : BaseChoice ℓ.side n, C' * B)
    (Filter.Eventually.of_forall fun W => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hD0 W)]
  refine mul_le_mul (hDc W) ?_ (abs_nonneg _) hDc0
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_of_nonneg (hC' W b V).1]
  exact mul_le_mul (hC' W b V).2 (hpb W b) (abs_nonneg _) hC0'
theorem coldResponseChain_linear (hA : ResponseConditionalMeanStatement) (hW : BlockMeanIsLinearAndLocal)
    (hS : StepTransitionDensityBounds) (hT : BondScoreProperties) (hL : ChainIsProbabilityLaw)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) :
    (t n : ℕ) → [NeZero n] → (Y : TorusSite n) → (r r' : ℝ) → (h h' : PlaquetteWeight (fineSide ℓ.side t n)) →
    (W : TorusField n) → coldResponseChain ℓ β x al t n Y W (fun p => r * h p + r' * h' p) =
      r * coldResponseChain ℓ β x al t n Y W h + r' * coldResponseChain ℓ β x al t n Y W h'
  | 0, n, _, Y, r, r', h, h', W => by
    show siteResponse Y W (fun p => r * h p + r' * h' p) = r * siteResponse Y W h + r' * siteResponse Y W h'
    unfold siteResponse
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  | t + 1, n, _, Y, r, r', h, h', V => by
    have hodd : Odd ℓ.side := hfit.L_odd
    simp only [coldResponseChain_succ_eq_conditionalMean]
    unfold conditionalMean
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    congr 1
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((integrable_responseIntegrand hA hS hT hL ℓ hfit β x al t n Y h V).const_mul r)
        ((integrable_responseIntegrand hA hS hT hL ℓ hfit β x al t n Y h' V).const_mul r')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    show chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V *
        responseIntegrand ℓ β x al t n Y (fun p => r * h p + r' * h' p) V W b =
      r * (chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V *
        responseIntegrand ℓ β x al t n Y h V W b) +
      r' * (chainFunctional ℓ β x t (n * ℓ.side) W * ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V *
        responseIntegrand ℓ β x al t n Y h' V W b)
    have hphi : ∀ b, responseIntegrand ℓ β x al t n Y (fun p => r * h p + r' * h' p) V W b =
        r * responseIntegrand ℓ β x al t n Y h V W b + r' * responseIntegrand ℓ β x al t n Y h' V W b := by
      intro b
      unfold responseIntegrand
      rw [(hW ℓ.side hodd (t + 1) n Y).2.1 r r' h h']
      have h1 : ∀ z ∈ sitesInBlocks ℓ.side {Y},
          coldResponseChain ℓ β x al t (n * ℓ.side) z W (fun p => r * h p + r' * h' p) =
          r * coldResponseChain ℓ β x al t (n * ℓ.side) z W h + r' * coldResponseChain ℓ β x al t (n * ℓ.side) z W h' :=
        fun z _ => coldResponseChain_linear hA hW hS hT hL ℓ hfit β x al t (n * ℓ.side) z r r' h h' W
      have hs : ∑ z ∈ sitesInBlocks ℓ.side {Y},
          coldResponseChain ℓ β x al t (n * ℓ.side) z W (fun p => r * h p + r' * h' p) =
          r * ∑ z ∈ sitesInBlocks ℓ.side {Y}, coldResponseChain ℓ β x al t (n * ℓ.side) z W h +
            r' * ∑ z ∈ sitesInBlocks ℓ.side {Y}, coldResponseChain ℓ β x al t (n * ℓ.side) z W h' := by
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      refine (congrArg (fun q => q + ℓ.coupling / 2 * al t *
        (r * blockMean ℓ.side (t + 1) n Y h + r' * blockMean ℓ.side (t + 1) n Y h') *
        bondScoresAtSite ℓ (x t) W V b Y) hs).trans ?_
      ring
    simp only [hphi, mul_add, Finset.sum_add_distrib]
    have e1 : ∀ (c : ℝ) (f : BaseChoice ℓ.side n → ℝ), ∑ b, stepTransitionDensity ℓ (x t) W b V * (c * f b) =
        c * ∑ b, stepTransitionDensity ℓ (x t) W b V * f b := fun c f => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e1, e1]
    ring
theorem coldResponseChain_local (hW : BlockMeanIsLinearAndLocal) (ℓ : StepParameters) (hfit : ℓ.Admissible) (β : ℝ)
    (x al : ℕ → ℝ) :
    (t n : ℕ) → [NeZero n] → (Y : TorusSite n) → (h h' : PlaquetteWeight (fineSide ℓ.side t n)) →
    (∀ p, IsPlaquetteAt ℓ.side t Y p → h p = h' p) →
    ∀ W, coldResponseChain ℓ β x al t n Y W h = coldResponseChain ℓ β x al t n Y W h'
  | 0, n, _, Y, h, h', hh, W => by
    show siteResponse Y W h = siteResponse Y W h'
    unfold siteResponse
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases hc : Y ∈ plaquetteVertices p.1 p.2.1 p.2.2
    · have hlt : p.2.1 < p.2.2 := by
        simp only [plaquettesIn, Finset.mem_filter] at hp
        exact hp.2.1
      have : h p = h' p := hh p ⟨hlt, Y, hc, Finset.mem_singleton_self Y⟩
      rw [this]
    · have h0 : vertexMultiplicity Y p = 0 := by
        simp only [vertexMultiplicity]
        rw [List.count_eq_zero_of_not_mem hc]
        simp
      simp [h0]
  | t + 1, n, _, Y, h, h', hh, V => by
    have hodd : Odd ℓ.side := hfit.L_odd
    simp only [coldResponseChain_succ_eq_conditionalMean]
    unfold conditionalMean
    congr 2
    funext W
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    unfold responseIntegrand
    rw [(hW ℓ.side hodd (t + 1) n Y).2.2 h h' hh]
    congr 1
    refine Finset.sum_congr rfl fun z hz => ?_
    refine coldResponseChain_local hW ℓ hfit β x al t (n * ℓ.side) z h h' (fun p hp => hh p ⟨hp.1, ?_⟩) W
    obtain ⟨c, hc, hcz⟩ := hp.2
    exact ⟨c, hc, Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩
theorem responseLinearLocal (hA : ResponseConditionalMeanStatement) (hW : BlockMeanIsLinearAndLocal)
    (hS : StepTransitionDensityBounds) (hT : BondScoreProperties) (hL : ChainIsProbabilityLaw) :
    ResponseLinearLocalStatement := by
  intro ℓ hfit β x al t n _ Y
  refine ⟨fun r r' h h' W => coldResponseChain_linear hA hW hS hT hL ℓ hfit β x al t n Y r r' h h' W,
    fun h h' hh W => coldResponseChain_local hW ℓ hfit β x al t n Y h h' hh W, fun h V => ?_⟩
  have hodd : Odd ℓ.side := hfit.L_odd
  set c := blockMean ℓ.side (t + 1) n Y h with hc
  have hone : blockMean ℓ.side (t + 1) n Y (constOneWeight _) = 1 := (hW ℓ.side hodd (t + 1) n Y).1
  have hlin := coldResponseChain_linear hA hW hS hT hL ℓ hfit β x al (t + 1) n Y 1 (-c) h (constOneWeight _) V
  have hg : (fun p => 1 * h p + -c * constOneWeight (fineSide ℓ.side (t + 1) n) p) = fun p => h p - c := by
    funext p
    simp only [constOneWeight]
    ring
  rw [hg] at hlin
  have hrem : responseRemainder (coldResponseChain ℓ β x al (t + 1)) n Y h V =
      coldResponseChain ℓ β x al (t + 1) n Y V fun p => h p - c := by
    rw [hlin]
    show coldResponseChain ℓ β x al (t + 1) n Y V h -
      c * coldResponseChain ℓ β x al (t + 1) n Y V (constOneWeight _) = _
    ring
  rw [hrem, coldResponseChain_succ_eq_conditionalMean]
  have hzero : blockMean ℓ.side (t + 1) n Y (fun p => h p - c) = 0 := by
    have h1 := (hW ℓ.side hodd (t + 1) n Y).2.1 1 (-c) h (constOneWeight _)
    rw [hg, hone] at h1
    rw [h1, ← hc]
    ring
  unfold conditionalMean
  congr 2
  funext W
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  unfold responseIntegrand
  rw [hzero, mul_zero, zero_mul, add_zero]
  rfl
end YangMills.Construction.ResponseInTheExpansion
end
