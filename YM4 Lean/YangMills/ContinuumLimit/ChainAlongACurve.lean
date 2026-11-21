import Mathlib
import YangMills.ContinuumLimit.KernelAlongTheCoupling
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreMeans
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreMeansProof
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.ResponseInTheExpansion.ConditionalMeans

def chainResponseSum (ℓ : StepParameters) (γ : ℝ) (ξ a : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) : ℝ :=
  ∑ y : TorusSite n, coldResponseChain ℓ γ ξ a t n y V (constOneWeight _)

namespace ChainAlongACurve

def stepMass (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n] (V : TorusField n)
    (W : TorusField (n * ℓ.side)) : ℝ :=
  chainFunctional ℓ β x t (n * ℓ.side) W *
    ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V

def stepResponse (ℓ : StepParameters) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) (W : TorusField (n * ℓ.side)) : ℝ :=
  chainFunctional ℓ β x t (n * ℓ.side) W *
    ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ (x t) W b V *
      (chainResponseSum ℓ β x al t (n * ℓ.side) W +
        ℓ.coupling * al t * ∑ c : TorusBond n, bondScore ℓ (x t) W V b c)

theorem chainResponseSum_measurable_bounded (hS : StepTransitionDensityBounds)
    (hT : BondScoreProperties) (hL : ChainIsProbabilityLaw) {ℓ : StepParameters}
    (hℓ : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] :
    Measurable (fun V : TorusField n => chainResponseSum ℓ β x al t n V) ∧
      ∃ C : ℝ, ∀ V, |chainResponseSum ℓ β x al t n V| ≤ C := by
  have h := fun y : TorusSite n =>
    coldResponseChain_measurable_bounded hS hT hL ℓ hℓ β x al t n y (constOneWeight _)
  choose C hC using fun y => (h y).2
  refine ⟨?_, ∑ y : TorusSite n, C y, fun V => ?_⟩
  · unfold chainResponseSum
    exact Finset.measurable_sum _ fun y _ => (h y).1
  · unfold chainResponseSum
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hC y V)

theorem measurable_stepTransitionDensity_left (hS : StepTransitionDensityBounds)
    (ℓ : StepParameters) (y : ℝ) {n : ℕ} [NeZero n] (b : BaseChoice ℓ.side n)
    (V : TorusField n) :
    Measurable fun W : TorusField (n * ℓ.side) => stepTransitionDensity ℓ y W b V := by
  have hpair : Measurable fun W : TorusField (n * ℓ.side) => (W, V) := measurable_prodMk_right
  have h2 := ((hS ℓ y n).1 b).comp hpair
  exact h2

theorem measurable_bondScore_left (hT : BondScoreProperties) {ℓ : StepParameters}
    (hℓ : ℓ.Admissible) (y : ℝ) {n : ℕ} [NeZero n] (b : BaseChoice ℓ.side n)
    (V : TorusField n) :
    Measurable fun W : TorusField (n * ℓ.side) => ∑ c : TorusBond n, bondScore ℓ y W V b c := by
  have hpair : Measurable fun W : TorusField (n * ℓ.side) => (W, V) := measurable_prodMk_right
  refine Finset.measurable_sum _ fun c _ => ?_
  have h2 := ((hT ℓ hℓ y n b c).2.2.2.2).comp hpair
  exact h2

theorem measurable_stepMass (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    {ℓ : StepParameters} (hℓ : ℓ.Admissible) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) :
    Measurable fun W => stepMass ℓ β x t n V W := by
  unfold stepMass
  exact (hL ℓ hℓ hℓ.depth_lt β x t (n * ℓ.side)).2.2.1.mul
    (Finset.measurable_sum _ fun b _ => measurable_stepTransitionDensity_left hS ℓ (x t) b V)

theorem measurable_stepResponse (hS : StepTransitionDensityBounds) (hT : BondScoreProperties)
    (hL : ChainIsProbabilityLaw) {ℓ : StepParameters} (hℓ : ℓ.Admissible) (β : ℝ)
    (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (V : TorusField n) :
    Measurable fun W => stepResponse ℓ β x al t n V W := by
  unfold stepResponse
  exact (hL ℓ hℓ hℓ.depth_lt β x t (n * ℓ.side)).2.2.1.mul
    (Finset.measurable_sum _ fun b _ =>
      (measurable_stepTransitionDensity_left hS ℓ (x t) b V).mul
        ((chainResponseSum_measurable_bounded hS hT hL hℓ β x al t (n * ℓ.side)).1.add
          (measurable_const.mul (measurable_bondScore_left hT hℓ (x t) b V))))

theorem integral_stepResponse (hR : ResponseConditionalMeanStatement) {ℓ : StepParameters}
    (hℓ : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (V : TorusField n) :
    chainResponseSum ℓ β x al (t + 1) n V * chainFunctional ℓ β x (t + 1) n V =
      ∫ W, stepResponse ℓ β x al t n V W ∂(fieldHaar (n * ℓ.side)) := by
  have h := (hR ℓ hℓ β x al).2 t n (constOneWeight _) V
  unfold chainResponseSum
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  have hsc : ∀ b : BaseChoice ℓ.side n,
      ∑ c : TorusBond n, ℓ.coupling * al t *
        bondBlockMean ℓ.side (t + 1) n (constOneWeight _) c * bondScore ℓ (x t) W V b c =
      ℓ.coupling * al t * ∑ c : TorusBond n, bondScore ℓ (x t) W V b c := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [bondBlockMean_constOne ℓ.side hℓ.L_odd]
    ring
  simp only [hsc]
  unfold stepResponse chainResponseSum
  rfl

theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (τ Φ : ι → ℝ) (B : ℝ) (hτ : ∀ i, 0 ≤ τ i)
    (hΦ : ∀ i, |Φ i| ≤ B) : |∑ i, τ i * Φ i| ≤ B * ∑ i, τ i := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (hτ i), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hΦ i) (hτ i)

theorem sum_mul_add_eq {ι : Type*} [Fintype ι] (τ s : ι → ℝ) (θ c a : ℝ) :
    ∑ i, τ i * (θ + c * a * s i) = θ * ∑ i, τ i - ∑ i, -c * s i * τ i * a := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem abs_stepResponse_le (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    {ℓ : StepParameters} (hℓ : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (V : TorusField n) (W : TorusField (n * ℓ.side)) {B : ℝ}
    (hB : ∀ b : BaseChoice ℓ.side n, |chainResponseSum ℓ β x al t (n * ℓ.side) W +
      ℓ.coupling * al t * ∑ c : TorusBond n, bondScore ℓ (x t) W V b c| ≤ B) :
    |stepResponse ℓ β x al t n V W| ≤ B * stepMass ℓ β x t n V W := by
  obtain ⟨-, C, hC⟩ := hS ℓ (x t) n
  have hG := (hL ℓ hℓ hℓ.depth_lt β x t (n * ℓ.side)).2.2.2.1 W
  have hs := abs_sum_mul_le (fun b => stepTransitionDensity ℓ (x t) W b V)
    (fun b => chainResponseSum ℓ β x al t (n * ℓ.side) W +
      ℓ.coupling * al t * ∑ c : TorusBond n, bondScore ℓ (x t) W V b c) B
    (fun b => (hC W b V).1) hB
  unfold stepResponse stepMass
  rw [abs_mul, abs_of_pos hG]
  calc _ ≤ chainFunctional ℓ β x t (n * ℓ.side) W * (B * ∑ b : BaseChoice ℓ.side n,
        stepTransitionDensity ℓ (x t) W b V) := mul_le_mul_of_nonneg_left hs hG.le
    _ = _ := by ring

end ChainAlongACurve

open ChainAlongACurve in
theorem chain_along_curve (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) {ℓ : StepParameters} (hℓ : ℓ.Admissible)
    {I : Set ℝ} (hI : IsOpen I) (ξ a : ℝ → ℕ → ℝ) (A : ℝ) (t : ℕ)
    (h1 : ∀ j < t, ∀ γ ∈ I, HasDerivAt (fun γ' => ξ γ' j) (a γ j) γ)
    (h2 : ∀ j < t, ∀ γ ∈ I, |a γ j| ≤ A)
    (h3 : ∀ j < t, ContinuousOn (fun γ => a γ j) I) :
    ∀ (n : ℕ) [NeZero n],
      (∃ M : ℝ, ∀ γ ∈ I, ∀ V : TorusField n, |chainResponseSum ℓ γ (ξ γ) (a γ) t n V| ≤ M) ∧
      (∀ V : TorusField n, ∀ γ ∈ I,
        HasDerivAt (fun γ' => chainFunctional ℓ γ' (ξ γ') t n V)
          (-chainFunctional ℓ γ (ξ γ) t n V * chainResponseSum ℓ γ (ξ γ) (a γ) t n V) γ) ∧
      (∀ V : TorusField n, ContinuousOn (fun γ => chainResponseSum ℓ γ (ξ γ) (a γ) t n V) I) := by
  revert h1 h2 h3
  induction t with
  | zero =>
    intro _ _ _ n _
    obtain ⟨-, C, hC⟩ :=
      chainResponseSum_measurable_bounded hS hT hL hℓ 0 (fun _ => 0) (fun _ => 0) 0 n
    refine ⟨⟨C, fun γ _ V => hC V⟩, fun V γ _ => hasDerivAt_wilsonWeight ℓ.side V γ, fun V => ?_⟩
    exact (continuousOn_const (c := chainResponseSum ℓ 0 (fun _ => 0) (fun _ => 0) 0 n V)).congr
      fun γ _ => rfl
  | succ t ih =>
    intro h1 h2 h3 n _
    obtain ⟨⟨M, hM⟩, hG, hΘc⟩ := ih (fun j hj => h1 j (Nat.lt_succ_of_lt hj))
      (fun j hj => h2 j (Nat.lt_succ_of_lt hj)) (fun j hj => h3 j (Nat.lt_succ_of_lt hj))
      (n * ℓ.side)
    have ht : t < t + 1 := Nat.lt_succ_self t
    have hGpos : ∀ (γ : ℝ) (s k : ℕ) [NeZero k] (W : TorusField k),
        0 < chainFunctional ℓ γ (ξ γ) s k W :=
      fun γ s k _ W => (hL ℓ hℓ hℓ.depth_lt γ (ξ γ) s k).2.2.2.1 W
    have hsc : ∀ (y : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
        (b : BaseChoice ℓ.side n),
        |∑ c : TorusBond n, bondScore ℓ y W V b c| ≤ 2 * (Fintype.card (TorusBond n) : ℝ) := by
      intro y W V b
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ c : TorusBond n, |bondScore ℓ y W V b c| ≤ ∑ _c : TorusBond n, (2 : ℝ) :=
            Finset.sum_le_sum fun c _ => (hT ℓ hℓ y n b c).2.2.1 W V
        _ = 2 * (Fintype.card (TorusBond n) : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    obtain ⟨B, hΦ⟩ : ∃ B : ℝ, ∀ γ ∈ I, ∀ (W : TorusField (n * ℓ.side)) (V : TorusField n)
        (b : BaseChoice ℓ.side n),
        |chainResponseSum ℓ γ (ξ γ) (a γ) t (n * ℓ.side) W +
          ℓ.coupling * a γ t * ∑ c : TorusBond n, bondScore ℓ (ξ γ t) W V b c| ≤ B := by
      refine ⟨M + |ℓ.coupling| * A * (2 * (Fintype.card (TorusBond n) : ℝ)), ?_⟩
      intro γ hγ W V b
      have ha := h2 t ht γ hγ
      refine (abs_add_le _ _).trans (add_le_add (hM γ hγ W) ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha (abs_nonneg _)) (hsc _ W V b) (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans ha))
    have hB0 : ∀ γ ∈ I, 0 ≤ B := fun γ hγ =>
      (abs_nonneg _).trans (hΦ γ hγ (trivialField _) (trivialField _) (Classical.arbitrary _))
    have hC1 : ∀ γ ∈ I, ∀ V : TorusField n,
        |chainResponseSum ℓ γ (ξ γ) (a γ) (t + 1) n V| ≤ B := by
      intro γ hγ V
      obtain ⟨-, -, hDm, hD0, hDb, -, -, -, -⟩ := hL ℓ hℓ hℓ.depth_lt γ (ξ γ) t (n * ℓ.side)
      have hΘm := (chainResponseSum_measurable_bounded hS hT hL hℓ γ (ξ γ) (a γ) t
        (n * ℓ.side)).1
      obtain ⟨-, -, hb⟩ := integral_weighted_mean_bounds hS (ξ γ t)
        (chainFunctional ℓ γ (ξ γ) t (n * ℓ.side)) hDm hD0 hDb
        (fun W b V => chainResponseSum ℓ γ (ξ γ) (a γ) t (n * ℓ.side) W +
          ℓ.coupling * a γ t * ∑ c : TorusBond n, bondScore ℓ (ξ γ t) W V b c)
        (fun b => (hΘm.comp measurable_fst).add (measurable_const.mul
          (Finset.measurable_sum _ fun c _ => (hT ℓ hℓ (ξ γ t) n b c).2.2.2.2)))
        (fun W b V => hΦ γ hγ W V b)
      have hpos := hGpos γ (t + 1) n V
      have hid := integral_stepResponse hR hℓ γ (ξ γ) (a γ) t n V
      have hmass := chainFunctional_succ ℓ γ (ξ γ) t n V
      refine le_of_mul_le_mul_right ?_ hpos
      calc |chainResponseSum ℓ γ (ξ γ) (a γ) (t + 1) n V| * chainFunctional ℓ γ (ξ γ) (t + 1) n V
          = |∫ W, stepResponse ℓ γ (ξ γ) (a γ) t n V W ∂(fieldHaar (n * ℓ.side))| := by
            rw [← hid, abs_mul, abs_of_pos hpos]
        _ ≤ _ := hb V
        _ = _ := by rw [hmass]
    have hF' : ∀ (V : TorusField n) (W : TorusField (n * ℓ.side)), ∀ γ ∈ I,
        HasDerivAt (fun γ' => stepMass ℓ γ' (ξ γ') t n V W)
          (-stepResponse ℓ γ (ξ γ) (a γ) t n V W) γ := by
      intro V W γ hγ
      have hτd : ∀ b : BaseChoice ℓ.side n,
          HasDerivAt (fun γ' => stepTransitionDensity ℓ (ξ γ' t) W b V)
            (-ℓ.coupling * (∑ c : TorusBond n, bondScore ℓ (ξ γ t) W V b c) *
              stepTransitionDensity ℓ (ξ γ t) W b V * a γ t) γ :=
        fun b => by
          have hd := (hasDerivAt_stepTransitionDensity hK hℓ (ξ γ t) W b V).comp γ (h1 t ht γ hγ)
          exact hd
      have hp := (hG W γ hγ).mul (HasDerivAt.fun_sum (u := Finset.univ) fun b _ => hτd b)
      refine hp.congr_deriv ?_
      unfold stepResponse
      rw [sum_mul_add_eq]
      ring
    have hdom : ∀ (V : TorusField n), ∀ γ₀ ∈ I, ∃ r > 0, Set.Icc (γ₀ - r) (γ₀ + r) ⊆ I ∧
        Integrable (fun W => stepMass ℓ γ₀ (ξ γ₀) t n V W) (fieldHaar (n * ℓ.side)) ∧
        ∀ γ ∈ Set.Icc (γ₀ - r) (γ₀ + r), ∀ W : TorusField (n * ℓ.side),
          |stepResponse ℓ γ (ξ γ) (a γ) t n V W| ≤
            B * (Real.exp (B * r) * stepMass ℓ γ₀ (ξ γ₀) t n V W) := by
      intro V γ₀ hγ₀
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI γ₀ hγ₀
      have hIcc : Set.Icc (γ₀ - ε / 2) (γ₀ + ε / 2) ⊆ I := fun γ hγ =>
        hball (Metric.closedBall_subset_ball (half_lt_self hε)
          (by rw [Real.closedBall_eq_Icc]; exact hγ))
      refine ⟨ε / 2, half_pos hε, hIcc, ?_, fun γ hγ W => ?_⟩
      · have hi := (hL ℓ hℓ hℓ.depth_lt γ₀ (ξ γ₀) t n).2.2.2.2.2.1 V
        simp only [averagedKernel_eq_sum_stepTransitionDensity] at hi
        exact hi
      · have hB := hB0 γ₀ hγ₀
        have hst : ∀ (γ' : ℝ) (W' : TorusField (n * ℓ.side)), 0 ≤ stepMass ℓ γ' (ξ γ') t n V W' := by
          intro γ' W'
          obtain ⟨-, C, hC⟩ := hS ℓ (ξ γ' t) n
          exact mul_nonneg (hGpos γ' t (n * ℓ.side) W').le
            (Finset.sum_nonneg fun b _ => (hC W' b V).1)
        have hγ₀' : γ₀ ∈ Set.Icc (γ₀ - ε / 2) (γ₀ + ε / 2) := ⟨by linarith, by linarith⟩
        have hg : stepMass ℓ γ (ξ γ) t n V W ≤
            Real.exp (B * |γ - γ₀|) * stepMass ℓ γ₀ (ξ γ₀) t n V W :=
          le_exp_mul_of_abs_deriv_le (f := fun γ' => stepMass ℓ γ' (ξ γ') t n V W)
            (f' := fun γ' => -stepResponse ℓ γ' (ξ γ') (a γ') t n V W)
            (fun s hs => hF' V W s (hIcc hs))
            (fun s hs => (abs_neg _).trans_le
              (abs_stepResponse_le hS hL hℓ s (ξ s) (a s) t n V W (hΦ s (hIcc hs) W V)))
            hγ hγ₀'
        have hr : |γ - γ₀| ≤ ε / 2 := abs_sub_le_iff.2 ⟨by linarith [hγ.2], by linarith [hγ.1]⟩
        refine (abs_stepResponse_le hS hL hℓ γ (ξ γ) (a γ) t n V W (hΦ γ (hIcc hγ) W V)).trans ?_
        refine mul_le_mul_of_nonneg_left (hg.trans ?_) hB
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr hB))
          (hst γ₀ W)
    have hC2 : ∀ (V : TorusField n), ∀ γ₀ ∈ I,
        HasDerivAt (fun γ' => chainFunctional ℓ γ' (ξ γ') (t + 1) n V)
          (-chainFunctional ℓ γ₀ (ξ γ₀) (t + 1) n V *
            chainResponseSum ℓ γ₀ (ξ γ₀) (a γ₀) (t + 1) n V) γ₀ := by
      intro V γ₀ hγ₀
      obtain ⟨r, hr, hIcc, hint, hbd⟩ := hdom V γ₀ hγ₀
      have hmem : Set.Icc (γ₀ - r) (γ₀ + r) ∈ 𝓝 γ₀ := Icc_mem_nhds (by linarith) (by linarith)
      obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := fieldHaar (n * ℓ.side))
        (F := fun γ' W => stepMass ℓ γ' (ξ γ') t n V W)
        (F' := fun γ' W => -stepResponse ℓ γ' (ξ γ') (a γ') t n V W)
        (bound := fun W => B * (Real.exp (B * r) * stepMass ℓ γ₀ (ξ γ₀) t n V W)) hmem
        (Filter.Eventually.of_forall fun γ' =>
          (measurable_stepMass hS hL hℓ γ' (ξ γ') t n V).aestronglyMeasurable)
        hint
        (measurable_stepResponse hS hT hL hℓ γ₀ (ξ γ₀) (a γ₀) t n V).neg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun W γ hγ =>
          (norm_neg _).trans_le ((Real.norm_eq_abs _).trans_le (hbd γ hγ W)))
        ((hint.const_mul _).const_mul _)
        (Filter.Eventually.of_forall fun W γ hγ => hF' V W γ (hIcc hγ))
      have hfun : (fun γ' => chainFunctional ℓ γ' (ξ γ') (t + 1) n V) =
          fun γ' => ∫ W, stepMass ℓ γ' (ξ γ') t n V W ∂(fieldHaar (n * ℓ.side)) :=
        funext fun γ' => chainFunctional_succ ℓ γ' (ξ γ') t n V
      rw [hfun]
      refine hd.congr_deriv ?_
      rw [integral_neg, ← integral_stepResponse hR hℓ γ₀ (ξ γ₀) (a γ₀) t n V]
      ring
    refine ⟨⟨B, hC1⟩, hC2, fun V => ?_⟩
    intro γ₀ hγ₀
    obtain ⟨r, hr, hIcc, hint, hbd⟩ := hdom V γ₀ hγ₀
    have hmem : Set.Icc (γ₀ - r) (γ₀ + r) ∈ 𝓝 γ₀ := Icc_mem_nhds (by linarith) (by linarith)
    have hξc : ContinuousAt (fun γ => ξ γ t) γ₀ := (h1 t ht γ₀ hγ₀).continuousAt
    have hac : ContinuousAt (fun γ => a γ t) γ₀ := (h3 t ht).continuousAt (hI.mem_nhds hγ₀)
    have hcont : ∀ W : TorusField (n * ℓ.side),
        ContinuousAt (fun γ => stepResponse ℓ γ (ξ γ) (a γ) t n V W) γ₀ := by
      intro W
      have hGc : ContinuousAt (fun γ => chainFunctional ℓ γ (ξ γ) t (n * ℓ.side) W) γ₀ :=
        (hG W γ₀ hγ₀).continuousAt
      have hΘc' : ContinuousAt (fun γ => chainResponseSum ℓ γ (ξ γ) (a γ) t (n * ℓ.side) W) γ₀ :=
        (hΘc W).continuousAt (hI.mem_nhds hγ₀)
      have hτc : ∀ b : BaseChoice ℓ.side n,
          ContinuousAt (fun γ => stepTransitionDensity ℓ (ξ γ t) W b V) γ₀ := fun b => by
        have hd := (hasDerivAt_stepTransitionDensity hK hℓ (ξ γ₀ t) W b V).comp γ₀ (h1 t ht γ₀ hγ₀)
        exact hd.continuousAt
      have hscc : ∀ b : BaseChoice ℓ.side n,
          ContinuousAt (fun γ => ∑ c : TorusBond n, bondScore ℓ (ξ γ t) W V b c) γ₀ := fun b =>
        tendsto_finsetSum _ fun c _ =>
          ContinuousAt.comp (g := fun x => bondScore ℓ x W V b c)
            (continuous_bondScore_coupling hT hℓ W V b c).continuousAt hξc
      have hsum : ContinuousAt (fun γ => ∑ b : BaseChoice ℓ.side n,
          stepTransitionDensity ℓ (ξ γ t) W b V *
            (chainResponseSum ℓ γ (ξ γ) (a γ) t (n * ℓ.side) W +
              ℓ.coupling * a γ t * ∑ c : TorusBond n, bondScore ℓ (ξ γ t) W V b c)) γ₀ :=
        tendsto_finsetSum _ fun b _ =>
          (hτc b).mul (hΘc'.add ((continuousAt_const.mul hac).mul (hscc b)))
      exact hGc.mul hsum
    have hint' : ContinuousAt
        (fun γ => ∫ W, stepResponse ℓ γ (ξ γ) (a γ) t n V W ∂(fieldHaar (n * ℓ.side))) γ₀ :=
      continuousAt_of_dominated
        (bound := fun W => B * (Real.exp (B * r) * stepMass ℓ γ₀ (ξ γ₀) t n V W))
        (Filter.Eventually.of_forall fun γ =>
          (measurable_stepResponse hS hT hL hℓ γ (ξ γ) (a γ) t n V).aestronglyMeasurable)
        (Filter.eventually_of_mem hmem fun γ hγ => Filter.Eventually.of_forall fun W =>
          (Real.norm_eq_abs _).trans_le (hbd γ hγ W))
        ((hint.const_mul _).const_mul _)
        (Filter.Eventually.of_forall hcont)
    have hfun : (fun γ => chainResponseSum ℓ γ (ξ γ) (a γ) (t + 1) n V) = fun γ =>
        (∫ W, stepResponse ℓ γ (ξ γ) (a γ) t n V W ∂(fieldHaar (n * ℓ.side))) /
          chainFunctional ℓ γ (ξ γ) (t + 1) n V :=
      funext fun γ => eq_div_of_mul_eq (hGpos γ (t + 1) n V).ne'
        (integral_stepResponse hR hℓ γ (ξ γ) (a γ) t n V)
    rw [hfun]
    exact (hint'.div (hC2 V γ₀ hγ₀).continuousAt (hGpos γ₀ (t + 1) n V).ne').continuousWithinAt

end YangMills.ContinuumLimit

end
