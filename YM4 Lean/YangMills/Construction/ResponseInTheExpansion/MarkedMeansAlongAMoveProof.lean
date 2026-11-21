import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfAMarkedIntegralProof
import YangMills.Construction.ResponseInTheExpansion.MarkedMeansAlongAMove
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas StepMarks BondMoves
  MovedTopMarks KernelVariation PolymerCumulant MarkedIntegrals StepCosts TorusBalls WeightedResponses ClusterExpansionOfAStep
namespace ResponseInTheExpansion
namespace PerturbedExpectation
variable {n : ℕ}
def meanKernel (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (W : TorusField (n * R.params.side)) (u : Fin k → ℝ) : ℝ :=
  kernelAlongPerturbation R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) V c X u
def perturbedMark (R : StepSetup) (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * R.params.side))
    (W : TorusField (n * R.params.side)) (u : Fin k → ℝ) : ℝ :=
  R.bondMark (perturb c X u V) W b
theorem perturb_zero_field {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (V : TorusField n) : perturb c X 0 V = V := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
abbrev weightedMass (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions)
    (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ) (A : Finset (TorusSite n)) (u : Fin k → ℝ) : ℝ :=
  bondWeightedIntegral (fieldHaar (n * R.params.side)) (chartBondsInBlocks R.params.side)
    (fun A W => R.avoidingPart A W) K (fun b => perturbedMark R V c X b) A u
theorem bondExpansion_of_perturbation (R : StepSetup) (hrow : R.HasExpansions)
    (hlow : AvoidingParts.AvoidingPartNonnegAntitone) (hmarks : GoodMarkAlongMove)
    [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions)
    (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ)
    (hposK : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), ∀ A : Finset (TorusSite n), 0 < weightedMass R V c X K A u)
    (hhalf : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      weightedMass R V c X K A 0 ≤ 2 * weightedMass R V c X K (insert Y A) 0)
    (hat : ∀ b ∈ chartBonds R.params.side n,
      ContDiffAt ℝ 40 (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0)
    (hsize : ∀ b ∈ chartBonds R.params.side n, ∀ u,
      ‖frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u‖ ≤ 1)
    (q : ℝ → ℝ → ℝ)
    (hq : ∀ (k : ℕ) (U : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℍ[ℝ]),
      IsOpen U → ContDiffOn ℝ 40 f U → (∀ τ ∈ U, ‖f τ‖ ≤ 1) →
      (∀ (Ξ : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions) (g : UnitQuaternion),
        ContDiffOn ℝ 40 (markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖) Ξ g f) U ∧
        ∀ τ ∈ U, ∀ F S : ℝ, ‖Ξ‖ ≤ S → (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
          ∀ j, 1 ≤ j → j ≤ 40 →
            ‖iteratedFDeriv ℝ j
              (markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖) Ξ g f) τ‖ ≤ q F S) ∧
      (∀ a₀ : ℍ[ℝ], ContDiffOn ℝ 40 (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) U ∧
        ∀ τ ∈ U, ∀ F S : ℝ, (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
          ∀ j, 1 ≤ j → j ≤ 40 →
            ‖iteratedFDeriv ℝ j
              (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) τ‖ ≤ q F S))
    {P κ S : ℝ} (hS : ∑ l, ‖X l‖ ≤ S) (hP : 1 ≤ P)
    (hker : ∀ W, ContDiff ℝ 40 (K W) ∧ (∀ u, 0 ≤ K W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (K W) u‖ ≤ P ^ i * K W u) ∧
      ∀ u, K W u ≤ κ * K W 0)
    (hcut : ∀ t : ℝ, 0 ≤ t → 0 ≤ cutoffFactor (R.params.threshold / 64) R.barrierFn t ∧
      cutoffFactor (R.params.threshold / 64) R.barrierFn t ≤ 1)
    (near : Finset (TorusBond (n * R.params.side)))
    (hoff : ∀ b ∈ chartBonds R.params.side n, b ∉ near →
      (∀ᶠ u in 𝓝 (0 : Fin k → ℝ), frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u =
        frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b 0) ∧
      ¬ ∃ l, c l = (parentBlock R.params.side b.1, b.2))
    {F₀ : ℝ} (hF₀ : ∀ b ∈ near, ∀ i, 1 ≤ i → i ≤ 40 →
      ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ ≤ F₀)
    (hnear : near ⊆ chartBonds R.params.side n) :
    ∃ (U : Set (Fin k → ℝ)) (Q : ℝ), ∀ N, N ≤ 40 → BondExpansion (fieldHaar (n * R.params.side)) N U 0
      (fun b : TorusBond (n * R.params.side) => parentBlock R.params.side b.1) (chartBonds R.params.side n) near
      (chartBondsInBlocks R.params.side)
      (fun A W => R.avoidingPart A W) K (fun b => perturbedMark R V c X b) P (max 1 (q F₀ S)) Q κ := by
  classical
  set all := chartBonds R.params.side n with hall
  set f := fun b => frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b with hf
  have hcont : ∀ b ∈ all, ∀ i ∈ Finset.range 41, ∀ᶠ u in 𝓝 (0 : Fin k → ℝ),
      ‖iteratedFDeriv ℝ i (f b) u‖ < ‖iteratedFDeriv ℝ i (f b) 0‖ + 1 := by
    intro b hb i hi
    have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by
      have := Finset.mem_range.mp hi
      exact_mod_cast (by omega : i ≤ 40)
    exact ((hat b hb).continuousAt_iteratedFDeriv hi').norm.eventually_lt continuousAt_const (lt_add_one _)
  have hev : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), (∀ A : Finset (TorusSite n), 0 < weightedMass R V c X K A u) ∧
      (∀ b ∈ all, ContDiffAt ℝ 40 (f b) u) ∧
      (∀ b ∈ all, ∀ i ∈ Finset.range 41, ‖iteratedFDeriv ℝ i (f b) u‖ < ‖iteratedFDeriv ℝ i (f b) 0‖ + 1) ∧
      (∀ b ∈ all, b ∉ near → f b u = f b 0) := by
    refine hposK.and (((Filter.eventually_all_finset all).mpr fun b hb => (hat b hb).eventually (by simp)).and
      (((Filter.eventually_all_finset all).mpr fun b hb =>
        (Filter.eventually_all_finset _).mpr (hcont b hb)).and ?_))
    refine (Filter.eventually_all_finset all).mpr fun b hb => ?_
    by_cases hbn : b ∈ near
    · exact Eventually.of_forall fun u h => absurd hbn h
    · exact (hoff b hb hbn).1.mono fun u h _ => h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set U : Set (Fin k → ℝ) := Metric.ball 0 ε with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : Fin k → ℝ) ∈ U := Metric.mem_ball_self hε
  have hfU : ∀ b ∈ all, ContDiffOn ℝ 40 (f b) U := fun b hb u hu =>
    ((hball u hu).2.1 b hb).contDiffWithinAt
  set Fb : ℝ := ∑ b ∈ all, ∑ i ∈ Finset.range 41, (‖iteratedFDeriv ℝ i (f b) 0‖ + 1) with hFb
  have hFbb : ∀ b ∈ all, ∀ u ∈ U, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (f b) u‖ ≤ Fb := by
    intro b hb u hu i _ hi
    have hmem : i ∈ Finset.range 41 := Finset.mem_range.mpr (by omega)
    have h1 := ((hball u hu).2.2.1 b hb i hmem).le
    have h2 := Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i (f b) 0‖ + 1)
      (fun _ _ => by positivity) hmem
    have h3 := Finset.single_le_sum (f := fun b => ∑ i ∈ Finset.range 41, (‖iteratedFDeriv ℝ i (f b) 0‖ + 1))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hb
    exact h1.trans (h2.trans h3)
  have hmark : ∀ b ∈ all, ∀ W, ContDiffOn ℝ 40 (perturbedMark R V c X b W) U ∧ ∀ u ∈ U, ∀ F : ℝ,
      (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (f b) u‖ ≤ F) → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (perturbedMark R V c X b W) u‖ ≤ q F S := by
    intro b hb W
    obtain ⟨h1, h2⟩ := hq k U (f b) hUo (hfU b hb) (fun u _ => hsize b hb u)
    rcases hmarks R.params R.anchorRadius R.barrierFn R.depth R.frameReach n V W k c X b with ⟨a₀, ha⟩ | ⟨-, g, hg⟩
    · have e : perturbedMark R V c X b W = fun u => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f b u‖ :=
        funext ha
      rw [e]
      exact ⟨(h2 a₀).1, fun u hu F hF j hj1 hj2 => (h2 a₀).2 u hu F S hF j hj1 hj2⟩
    · have e : perturbedMark R V c X b W = markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖)
          (bondMoveLinear c X (parentBlock R.params.side b.1, b.2)) g (f b) := funext hg
      rw [e]
      exact ⟨(h1 _ g).1, fun u hu F hF j hj1 hj2 =>
        (h1 _ g).2 u hu F S ((norm_bondMoveLinear_le c X _).trans hS) hF j hj1 hj2⟩
  have hmark01 : ∀ b W u, 0 ≤ perturbedMark R V c X b W u ∧ perturbedMark R V c X b W u ≤ 1 := fun b W u =>
    hcut _ (norm_nonneg _)
  refine ⟨U, max 1 (q Fb S), fun N hN => ?_⟩
  have hNc : ((N : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hN
  exact
  { isOpen := hUo
    center_mem := h0U
    mem_bonds := fun A b => by simp [chartBondsInBlocks, hall]
    integral_pos := fun A u hu => (hball u hu).1 A
    integral_le_two_mul_insert := hhalf
    weight_nonneg := fun A W => ((hlow R hrow n hn W).1 A)
    weight_antitone := fun A B W h => (hlow R hrow n hn W).2 A B h
    kernel_nonneg := fun W u _ => (hker W).2.1 u
    kernel_contDiffOn := fun W => ((hker W).1.of_le hNc).contDiffOn
    kernel_iteratedFDeriv_le := fun W i hi u _ => (hker W).2.2.1 u i (hi.trans hN)
    kernel_le_center := fun W u _ => (hker W).2.2.2 u
    mark_nonneg := fun b _ W u _ => (hmark01 b W u).1
    mark_le_one := fun b _ W u _ => (hmark01 b W u).2
    mark_contDiffOn := fun b hb W => (hmark b hb W).1.of_le hNc
    mark_iteratedFDeriv_le := fun b hb W i hi1 hi2 u hu =>
      ((hmark b (hnear hb) W).2 u hu Fb (hFbb b (hnear hb) u hu) i hi1 (hi2.trans hN)).trans (le_max_right _ _)
    mark_iteratedFDeriv_center_le := fun b hb W i hi1 hi2 =>
      ((hmark b (hnear hb) W).2 0 h0U F₀ (hF₀ b hb) i hi1 (hi2.trans hN)).trans (le_max_right _ _)
    mark_eq_center := fun b hb hbn W u hu => by
      have hfix := (hball u hu).2.2.2 b hb hbn
      rcases hmarks R.params R.anchorRadius R.barrierFn R.depth R.frameReach n V W k c X b with ⟨a₀, ha⟩ | ⟨hl, -⟩
      · show R.bondMark (perturb c X u V) W b = R.bondMark (perturb c X 0 V) W b
        have e1 := ha u
        have e2 := ha 0
        show goodMark _ _ _ _ _ _ _ _ = goodMark _ _ _ _ _ _ _ _
        rw [e1, e2]
        have : frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u =
            frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b 0 := hfix
        rw [this]
      · exact absurd hl (hoff b hb hbn).2
    one_le_rate := hP
    one_le_centerBound := le_max_left _ _
    one_le_markBound := le_max_left _ _ }
theorem norm_iteratedFDeriv_add_const {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (z : F) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => g y + z) x‖ = ‖iteratedFDeriv ℝ i g x‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.norm_iteratedFDeriv_add_const <;> assumption
theorem norm_imaginaryBasis (i : Fin 3) : ‖imaginaryBasis i‖ = 1 := by apply _root_.YangMills.Construction.MovedTopMarks.UnitFamilies.norm_imaginaryBasis <;> assumption
theorem card_near_le_of_large (hB : BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n] {k m : ℕ}
    (c : Fin k → TorusBond n) (near : Finset (TorusBond (n * L))) {x : ℝ} (hx : 1 ≤ x) (hm : (m : ℝ) ≤ 2 * x)
    (hk : (k : ℝ) ≤ 9) (hin : ∀ b ∈ near, ∃ l, supDist (parentBlock L b.1) (c l).1 ≤ m) :
    (near.card : ℝ) ≤ 9 * (13 * x) ^ 4 * (4 * (2 * (L : ℝ)) ^ 4) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.card_le_of_near_bonds <;> assumption
theorem card_near_le_of_small (hB : BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n] {m : ℕ}
    (near : Finset (TorusBond (n * L))) {x : ℝ} (hx : 1 ≤ x) (hm : (m : ℝ) ≤ 2 * x) (hs : n ≤ 4 * m + 5) :
    (near.card : ℝ) ≤ 9 * (13 * x) ^ 4 * (4 * (2 * (L : ℝ)) ^ 4) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.card_le_of_small_torus <;> assumption
theorem rate_base_le {N G Cp a Q x k : ℝ} (hN : N ≤ 9 * (13 * x) ^ 4 * G) (hx : 1 ≤ x) (hk0 : 0 ≤ k)
    (hk : k ≤ 9) (hCp : 1 ≤ Cp) (ha : 1 ≤ a) (hQ : 1 ≤ Q) (hG : 0 ≤ G) (_hN0 : 0 ≤ N) :
    (N + 1) * (2 * (Cp * (a * x) * (k + 1) ^ 2) * Q) ≤
      ((9 * 13 ^ 4 * G + 1) * (200 * Cp * a * Q)) * x ^ 5 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.rate_product_le <;> assumption
theorem boxRadius_le {x : ℝ} (hx : 1 ≤ x) : ((boxRadius x : ℕ) : ℝ) ≤ 2 * x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.boxRadius_le <;> assumption
def LogDerivConstant (N : ℕ) (C : ℝ) : Prop :=
  ∀ {α ι β : Type} [MeasurableSpace α] [DecidableEq ι] (μ : Measure α) {k : ℕ}
    (U : Set (Fin k → ℝ)) (τ₀ : Fin k → ℝ) (block : β → ι) (all near : Finset β) (bonds : Finset ι → Finset β)
    (d : Finset ι → α → ℝ) (K : α → (Fin k → ℝ) → ℝ) (M : β → α → (Fin k → ℝ) → ℝ) (P Q₀ Q κ : ℝ),
    BondExpansion μ N U τ₀ block all near bonds d K M P Q₀ Q κ → ∀ A : Finset ι,
      ContDiffAt ℝ N (fun τ => Real.log (bondWeightedIntegral μ bonds d K M A τ)) τ₀ ∧
      ‖iteratedFDeriv ℝ N (fun τ => Real.log (bondWeightedIntegral μ bonds d K M A τ)) τ₀‖ ≤
        C * (((near.card : ℝ) + 1) * (2 * P * Q₀)) ^ N
def massRate (R : StepSetup) (Cp Q₀ : ℝ) : ℝ :=
  (9 * 13 ^ 4 * (4 * (2 * (R.params.side : ℝ)) ^ 4) + 1) * (200 * Cp * R.params.coupling * Q₀)
structure Hypotheses (R : StepSetup) (Kf : ℕ → ℝ) (q : ℝ → ℝ → ℝ) (Cp Cs : ℝ) : Prop where
  hasExpansions : R.HasExpansions
  avoiding : AvoidingParts.AvoidingPartNonnegAntitone
  goodMarks : GoodMarkAlongMove
  bondsPerBlock : BondsPerBlockBound
  coldNear : ColdNearStatement
  one_le_coupling : 1 ≤ R.coupling
  threshold_pos : 0 < R.params.threshold
  anchorRadius_le_one : R.anchorRadius ≤ 1
  one_le_paramCoupling : 1 ≤ R.params.coupling
  frameConst_nonneg : ∀ j, 0 ≤ Kf j
  frames : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold (5 / 4 * R.params.threshold) V →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ∀ b ∈ chartBonds R.params.side n,
      ContDiffAt ℝ 40 (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0 ∧
      (∀ u, ‖frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u‖ ≤ R.anchorRadius) ∧
      (∀ i, 1 ≤ i → i ≤ 40 →
        ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ ≤
          (k : ℝ) ^ i * Kf i) ∧
      (4 * R.frameReach + 5 < n → (∀ l h, TorusFields.BondOffsetInBox R.frameReach h →
          c l ≠ bondFrom (parentBlock R.params.side b.1) h) →
        ∀ᶠ u in 𝓝 0, frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u =
          frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b 0)
  markBounds : ∀ (k : ℕ) (U : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℍ[ℝ]),
    IsOpen U → ContDiffOn ℝ 40 f U → (∀ τ ∈ U, ‖f τ‖ ≤ 1) →
    (∀ (Ξ : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions) (g : UnitQuaternion),
      ContDiffOn ℝ 40 (markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖) Ξ g f) U ∧
      ∀ τ ∈ U, ∀ F S : ℝ, ‖Ξ‖ ≤ S → (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
        ∀ j, 1 ≤ j → j ≤ 40 →
          ‖iteratedFDeriv ℝ j
            (markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖) Ξ g f) τ‖ ≤ q F S) ∧
    (∀ a₀ : ℍ[ℝ], ContDiffOn ℝ 40 (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) U ∧
      ∀ τ ∈ U, ∀ F S : ℝ, (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ‖ ≤ F) →
        ∀ j, 1 ≤ j → j ≤ 40 →
          ‖iteratedFDeriv ℝ j
            (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) τ‖ ≤ q F S)
  one_le_kernelRate : 1 ≤ Cp
  kernel : ∀ (n : ℕ) [NeZero n] (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
    ∀ W, ContDiff ℝ 40 (meanKernel R V c X W) ∧ (∀ u, 0 ≤ meanKernel R V c X W u) ∧
    (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (meanKernel R V c X W) u‖ ≤
      (Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2) ^ i * meanKernel R V c X W u) ∧
    ∀ u, meanKernel R V c X W u ≤ Real.exp (2 * (R.params.coupling * R.coupling) * k) * meanKernel R V c X W 0
  integral_pos : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V' : TorusField n,
    IsCold (9 / 8 * R.params.threshold) V' → ∀ A : Finset (TorusSite n), 0 < R.markedIntegral A V'
  gas : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V' : TorusField n, IsCold (9 / 8 * R.params.threshold) V' →
    ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      7 / 8 * R.markedIntegral A V' ≤ R.markedIntegral (insert Y A) V'
  logConst_nonneg : 0 ≤ Cs
  logConst : ∀ j, 1 ≤ j → j ≤ 40 → ∃ C, C ≤ Cs ∧ 0 ≤ C ∧ LogDerivConstant j C
  cutoff_mem : ∀ s : ℝ, 0 ≤ s → 0 ≤ cutoffFactor (R.params.threshold / 64) R.barrierFn s ∧
    cutoffFactor (R.params.threshold / 64) R.barrierFn s ≤ 1
def nearMarkBound (Kf : ℕ → ℝ) (q : ℝ → ℝ → ℝ) : ℝ := max 1 (q (∑ i ∈ Finset.range 41, 9 ^ i * Kf i) 9)
theorem log_weightedMass_bounds {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs)
    (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) (hV : IsCold (9 / 8 * R.params.threshold) V)
    (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hu : AreUnitVectors X)
    (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ) {P κ : ℝ} (hP1 : 1 ≤ P)
    (hker : ∀ W, ContDiff ℝ 40 (K W) ∧ (∀ u, 0 ≤ K W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (K W) u‖ ≤ P ^ i * K W u) ∧ ∀ u, K W u ≤ κ * K W 0)
    (hposK : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), ∀ A : Finset (TorusSite n), 0 < weightedMass R V c X K A u)
    (hhalf0 : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      weightedMass R V c X K A 0 ≤ 2 * weightedMass R V c X K (insert Y A) 0)
    (A : Finset (TorusSite n)) :
    ContDiffAt ℝ 40 (fun u => Real.log (weightedMass R V c X K A u)) 0 ∧
    (k ≤ 9 → P = 4 * Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (fun u => Real.log (weightedMass R V c X K A u)) 0‖ ≤
        Cs * (massRate R (4 * Cp) (nearMarkBound Kf q) * R.coupling ^ 5) ^ j) := by
  obtain ⟨hrow, hL, hMs, hB, -, hx1, hσ, hρA1, ha1, hKf, hfr, hq, hCp1, -, -, -, hCs0, hjc, hcutb⟩ := S
  have hV54 : IsCold (5 / 4 * R.params.threshold) V := fun p μ ν h => (hV p μ ν h).trans (by linarith)
  have hfacts := fun (b : TorusBond (n * R.params.side)) (hb : b ∈ chartBonds R.params.side n) =>
    hfr n hn V hV54 k c X hu b hb
  have hat : ∀ b ∈ chartBonds R.params.side n,
      ContDiffAt ℝ 40 (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0 :=
    fun b hb => (hfacts b hb).1
  have hsize : ∀ b ∈ chartBonds R.params.side n, ∀ u,
      ‖frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u‖ ≤ 1 :=
    fun b hb u => ((hfacts b hb).2.1 u).trans hρA1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hSk : ∑ l, ‖X l‖ ≤ (k : ℝ) := by
    simp only [hu _, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_rfl
  have hcast : ((40 : ℕ) : WithTop ℕ∞) = 40 := by norm_num
  constructor
  · classical
    set F₁ : ℝ := ∑ b ∈ chartBonds R.params.side n, ∑ i ∈ Finset.range 41,
      ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ with hF₁
    have hF₁b : ∀ b ∈ chartBonds R.params.side n, ∀ i, 1 ≤ i → i ≤ 40 →
        ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ ≤ F₁ := by
      intro b hb i _ hi
      have h2 := Finset.single_le_sum
        (f := fun i => ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (show i < 41 by omega))
      have h3 := Finset.single_le_sum (f := fun b => ∑ i ∈ Finset.range 41,
        ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hb
      exact h2.trans h3
    obtain ⟨U, Q, hfam⟩ := bondExpansion_of_perturbation R hrow hL hMs hn V c X K hposK hhalf0 hat hsize q hq
      hSk hP1 hker hcutb (chartBonds R.params.side n) (fun b hb hbn => absurd hb hbn) hF₁b subset_rfl
    obtain ⟨C, -, -, hC40⟩ := hjc 40 (by norm_num) le_rfl
    have h40 := (hC40 (fieldHaar _) U 0 _ _ _ _ _ _ _ _ _ _ _ (hfam 40 le_rfl) A).1
    rw [hcast] at h40
    exact h40
  · intro hk9 hPe j hj1 hj40
    classical
    subst hPe
    have hk9' : (k : ℝ) ≤ 9 := by exact_mod_cast hk9
    let near : Finset (TorusBond (n * R.params.side)) := if 4 * R.frameReach + 5 < n then
        (chartBonds R.params.side n).filter fun b => ∃ l,
          (∃ h, TorusFields.BondOffsetInBox R.frameReach h ∧ c l = bondFrom (parentBlock R.params.side b.1) h) ∨
            c l = (parentBlock R.params.side b.1, b.2)
      else chartBonds R.params.side n
    have hnear : near ⊆ chartBonds R.params.side n := by
      simp only [near]
      split_ifs
      · exact Finset.filter_subset _ _
      · exact subset_rfl
    have hoff : ∀ b ∈ chartBonds R.params.side n, b ∉ near →
        (∀ᶠ u in 𝓝 (0 : Fin k → ℝ), frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u =
          frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b 0) ∧
          ¬ ∃ l, c l = (parentBlock R.params.side b.1, b.2) := by
      intro b hb hbn
      by_cases hs : 4 * R.frameReach + 5 < n
      · have hno : ∀ l, ¬ ((∃ h, TorusFields.BondOffsetInBox R.frameReach h ∧
              c l = bondFrom (parentBlock R.params.side b.1) h) ∨
            c l = (parentBlock R.params.side b.1, b.2)) := by
          intro l hl
          apply hbn
          simp only [near, if_pos hs]
          exact Finset.mem_filter.mpr ⟨hb, l, hl⟩
        exact ⟨(hfacts b hb).2.2.2 hs (fun l h hh he => hno l (Or.inl ⟨h, hh, he⟩)),
          fun ⟨l, hl⟩ => hno l (Or.inr hl)⟩
      · apply absurd hb
        simpa [near, if_neg hs] using hbn
    have hF₀b : ∀ b ∈ near, ∀ i, 1 ≤ i → i ≤ 40 →
        ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ ≤
          ∑ i ∈ Finset.range 41, 9 ^ i * Kf i := by
      intro b hb i hi1 hi2
      have h1 := (hfacts b (hnear hb)).2.2.1 i hi1 hi2
      have h2 : (k : ℝ) ^ i * Kf i ≤ 9 ^ i * Kf i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0 hk9' i) (hKf i)
      have h3 := Finset.single_le_sum (f := fun i => (9 : ℝ) ^ i * Kf i)
        (fun i _ => mul_nonneg (by positivity) (hKf i)) (Finset.mem_range.mpr (show i < 41 by omega))
      exact h1.trans (h2.trans h3)
    have hS9 : ∑ l, ‖X l‖ ≤ (9 : ℝ) := hSk.trans hk9'
    obtain ⟨U, Q, hfam⟩ := bondExpansion_of_perturbation R hrow hL hMs hn V c X K hposK hhalf0 hat hsize q hq
      hS9 hP1 hker hcutb near hoff hF₀b hnear
    obtain ⟨C, hCle, hC0, hCj⟩ := hjc j hj1 hj40
    have hbnd := (hCj (fieldHaar _) U 0 _ _ _ _ _ _ _ _ _ _ _ (hfam j hj40) A).2
    have hm : ((R.frameReach : ℕ) : ℝ) ≤ 2 * R.coupling := boxRadius_le hx1
    have hcard : (near.card : ℝ) ≤ 9 * (13 * R.coupling) ^ 4 * (4 * (2 * (R.params.side : ℝ)) ^ 4) := by
      by_cases hs : 4 * R.frameReach + 5 < n
      · refine card_near_le_of_large hB R.params.side c near hx1 hm hk9' fun b hb => ?_
        simp only [near, if_pos hs] at hb
        obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hb).2
        refine ⟨l, ?_⟩
        rcases hl with ⟨h, hh, he⟩ | he
        · rw [he]
          exact supDist_add_siteOfInt_le _ h.1 _ fun i => by
            have := abs_le.mp (hh.1 i)
            omega
        · rw [he]
          show supDist (parentBlock R.params.side b.1) (parentBlock R.params.side b.1) ≤ _
          rw [supDist_self]
          exact Nat.zero_le _
      · exact card_near_le_of_small hB R.params.side near hx1 hm (not_lt.mp hs)
    have hQ1 : (1 : ℝ) ≤ nearMarkBound Kf q := le_max_left _ _
    have hCp4 : 1 ≤ 4 * Cp := by linarith
    have hBle := rate_base_le hcard hx1 hk0 hk9' hCp4 ha1 hQ1 (by positivity) (Nat.cast_nonneg _)
    have hB0 : 0 ≤ ((near.card : ℝ) + 1) *
        (2 * (4 * Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2) * nearMarkBound Kf q) := by
      have h1 : (0 : ℝ) ≤ (near.card : ℝ) + 1 := by
        have : (0 : ℝ) ≤ near.card := Nat.cast_nonneg _
        linarith
      have h2 : 0 ≤ 4 * Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 := by linarith
      exact mul_nonneg h1 (mul_nonneg (by linarith) (by linarith))
    refine hbnd.trans ?_
    exact mul_le_mul hCle (pow_le_pow_left₀ hB0 hBle j) (pow_nonneg hB0 j) hCs0
theorem kernel_mul_weight {k : ℕ} {K w : (Fin k → ℝ) → ℝ} {P κ E : ℝ} (hP : 1 ≤ P) (hE : 1 ≤ E)
    (hK : ContDiff ℝ 40 K) (hK0 : ∀ u, 0 ≤ K u)
    (hKj : ∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i K u‖ ≤ P ^ i * K u) (hKr : ∀ u, K u ≤ κ * K 0)
    (hw : ContDiff ℝ 40 w) (hw1 : ∀ u, 1 / 2 ≤ w u) (hw2 : ∀ u, w u ≤ 1)
    (hwj : ∀ u, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i w u‖ ≤ E) :
    ContDiff ℝ 40 (fun u => K u * w u) ∧ (∀ u, 0 ≤ K u * w u) ∧
    (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (fun u => K u * w u) u‖ ≤ (4 * E * P) ^ i * (K u * w u)) ∧
    ∀ u, K u * w u ≤ 2 * κ * (K 0 * w 0) := by
  have hw0 : ∀ u, 0 ≤ w u := fun u => by linarith [hw1 u]
  refine ⟨hK.mul hw, fun u => mul_nonneg (hK0 u) (hw0 u), fun u i hi => ?_, fun u => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hK0 u) (hw0 u))]
    · have hic : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
      have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hK hw u hic
      have hterm : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * ‖iteratedFDeriv ℝ m K u‖ *
          ‖iteratedFDeriv ℝ (i - m) w u‖ ≤ P ^ m * 1 ^ (i - m) * (i.choose m : ℝ) * (E * K u) := by
        intro m hm
        have hm' : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hwE : ‖iteratedFDeriv ℝ (i - m) w u‖ ≤ E := by
          rcases Nat.eq_zero_or_pos (i - m) with h0 | h0
          · rw [h0, norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hw0 u)]
            exact (hw2 u).trans hE
          · exact hwj u _ h0 (by omega)
        have hKm := hKj u m (hm'.trans hi)
        have hc0 : (0 : ℝ) ≤ i.choose m := Nat.cast_nonneg _
        calc (i.choose m : ℝ) * ‖iteratedFDeriv ℝ m K u‖ * ‖iteratedFDeriv ℝ (i - m) w u‖
            ≤ (i.choose m : ℝ) * (P ^ m * K u) * E :=
              mul_le_mul (mul_le_mul_of_nonneg_left hKm hc0) hwE (norm_nonneg _)
                (mul_nonneg hc0 (mul_nonneg (by positivity) (hK0 u)))
          _ = P ^ m * 1 ^ (i - m) * (i.choose m : ℝ) * (E * K u) := by
              rw [one_pow]
              ring
      have h2 := h1.trans (Finset.sum_le_sum hterm)
      rw [← Finset.sum_mul, ← add_pow] at h2
      have h3 : (P + 1) ^ i ≤ (2 * P) ^ i := pow_le_pow_left₀ (by linarith) (by linarith) i
      have hEK : 0 ≤ E * K u := mul_nonneg (by linarith) (hK0 u)
      have h4 : 2 * E * (2 * P) ^ i ≤ (4 * E * P) ^ i := by
        have e : (4 * E * P) ^ i = (2 * E) ^ i * (2 * P) ^ i := by
          rw [← mul_pow]
          congr 1
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by omega)) (by positivity)
      have h5 : K u ≤ 2 * (K u * w u) := by nlinarith [hK0 u, hw1 u]
      have hP2 : 0 ≤ (2 * P) ^ i := by positivity
      calc ‖iteratedFDeriv ℝ i (fun u => K u * w u) u‖ ≤ (P + 1) ^ i * (E * K u) := h2
        _ ≤ (2 * P) ^ i * (E * K u) := mul_le_mul_of_nonneg_right h3 hEK
        _ ≤ (2 * P) ^ i * (E * (2 * (K u * w u))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (by linarith)) hP2
        _ = 2 * E * (2 * P) ^ i * (K u * w u) := by ring
        _ ≤ (4 * E * P) ^ i * (K u * w u) :=
            mul_le_mul_of_nonneg_right h4 (mul_nonneg (hK0 u) (hw0 u))
  · have hκK : 0 ≤ κ * K 0 := (hK0 u).trans (hKr u)
    calc K u * w u ≤ K u * 1 := mul_le_mul_of_nonneg_left (hw2 u) (hK0 u)
      _ = K u := mul_one _
      _ ≤ κ * K 0 := hKr u
      _ ≤ κ * K 0 * (2 * w 0) := le_mul_of_one_le_right hκK (by linarith [hw1 0])
      _ = 2 * κ * (K 0 * w 0) := by ring
section Weights
variable {α : Type} [MeasurableSpace α] {μ : Measure α}
theorem integrable_of_integral_pos {f : α → ℝ} (h : 0 < ∫ a, f a ∂μ) : Integrable f μ := by
  by_contra hn
  rw [integral_undef hn] at h
  exact lt_irrefl _ h
theorem integrable_mul_weight {f w : α → ℝ} (hf : Integrable f μ) (hw : Measurable w)
    (hw1 : ∀ a, 1 / 2 ≤ w a) (hw2 : ∀ a, w a ≤ 1) : Integrable (fun a => f a * w a) μ :=
  hf.mul_bdd (c := 1) hw.aestronglyMeasurable (ae_of_all _ fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hw1 a])]
    exact hw2 a)
theorem integral_mul_weight_between {f w : α → ℝ} (hf : Integrable f μ) (hw : Measurable w)
    (hw1 : ∀ a, 1 / 2 ≤ w a) (hw2 : ∀ a, w a ≤ 1) (h0 : ∀ a, 0 ≤ f a) :
    1 / 2 * ∫ a, f a ∂μ ≤ ∫ a, f a * w a ∂μ ∧ ∫ a, f a * w a ∂μ ≤ ∫ a, f a ∂μ := by
  have hi := integrable_mul_weight hf hw hw1 hw2
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hf.const_mul _) hi fun a => by
      show 1 / 2 * f a ≤ f a * w a
      nlinarith [h0 a, hw1 a]
  · exact integral_mono hi hf fun a => by
      show f a * w a ≤ f a
      nlinarith [h0 a, hw2 a]
theorem integral_mul_weight_le_two_mul {f f' w : α → ℝ} (hf : Integrable f μ) (hf' : Integrable f' μ)
    (hw : Measurable w) (hw1 : ∀ a, 1 / 2 ≤ w a) (hw2 : ∀ a, w a ≤ 1) (h0 : ∀ a, 0 ≤ f a)
    (hle : ∀ a, f' a ≤ f a) (hZ : 7 / 8 * ∫ a, f a ∂μ ≤ ∫ a, f' a ∂μ) :
    ∫ a, f a * w a ∂μ ≤ 2 * ∫ a, f' a * w a ∂μ := by
  have hi := integrable_mul_weight hf hw hw1 hw2
  have hi' := integrable_mul_weight hf' hw hw1 hw2
  have hsub : ∫ a, (f a * w a - f' a * w a) ∂μ ≤ ∫ a, (f a - f' a) ∂μ :=
    integral_mono (hi.sub hi') (hf.sub hf') fun a => by
      show f a * w a - f' a * w a ≤ f a - f' a
      nlinarith [hle a, hw2 a]
  rw [integral_sub hi hi', integral_sub hf hf'] at hsub
  have hb := (integral_mul_weight_between hf hw hw1 hw2 h0).1
  have hZ0 : 0 ≤ ∫ a, f a ∂μ := integral_nonneg h0
  linarith
theorem integral_mul_affine_weight {f g : α → ℝ} (hf : Integrable f μ) (hg : Measurable g) {B : ℝ}
    (hB : 0 < B) (hb : ∀ a, |g a| ≤ B) :
    ∫ a, f a * ((3 + g a / B) / 4) ∂μ = 3 / 4 * ∫ a, f a ∂μ + (∫ a, f a * g a ∂μ) / (4 * B) := by
  have hfg : Integrable (fun a => f a * g a) μ :=
    hf.mul_bdd (c := B) hg.aestronglyMeasurable (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs]
      exact hb a)
  have e : (fun a => f a * ((3 + g a / B) / 4)) = fun a => 3 / 4 * f a + 1 / (4 * B) * (f a * g a) := by
    funext a
    field_simp
  rw [e, integral_add (hf.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
  ring
end Weights
theorem norm_iteratedFDeriv_comp_le_of_vanish {k k' : ℕ} (Lz : (Fin k' → ℝ) → ℝ) (Af : (Fin k → ℝ) → (Fin k' → ℝ))
    (τ : Fin k → ℝ) (hz1 : ContDiffAt ℝ 40 Lz 0) (hAc : ContDiffAt ℝ 40 Af τ) (hA0 : Af τ = 0) {CC Dd : ℝ}
    (hCC : 0 ≤ CC) (hLz : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i Lz 0‖ ≤ CC)
    (hAf : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i Af τ‖ ≤ Dd ^ i) :
    ‖iteratedFDeriv ℝ 40 (Lz ∘ Af) τ‖ ≤ (Nat.factorial 40 : ℝ) * CC * Dd ^ 40 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogMarkedIntegral.norm_iteratedFDeriv_comp_le_of_vanish <;> assumption
theorem norm_iteratedFDeriv_exp_le {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hc : ContDiffAt ℝ 40 h 0) (h0 : h 0 ≤ 0)
    {D : ℝ} (hD : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i h 0‖ ≤ D ^ i) {j : ℕ} (hj : j ≤ 40) :
    ‖iteratedFDeriv ℝ j (fun u => Real.exp (h u)) 0‖ ≤ (Nat.factorial j : ℝ) * 1 * D ^ j := by
  have hne : (40 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  obtain ⟨u2, hu2, hAon⟩ := hc.contDiffOn (m := 40) le_rfl (fun h => absurd h hne)
  obtain ⟨s1, hs1sub, hs1o, h0s⟩ := mem_nhds_iff.mp hu2
  have hAs : ContDiffOn ℝ 40 h s1 := hAon.mono hs1sub
  have hCi : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Real.exp Set.univ (h 0)‖ ≤ 1 := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr h0
  have hDi : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i h s1 0‖ ≤ D ^ i := by
    intro i h1 h2
    rw [iteratedFDerivWithin_of_isOpen i hs1o h0s]
    exact hD i h1 (h2.trans hj)
  have hm := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := h) (n := j) (s := s1) (t := Set.univ)
    (x := 0) (N := 40) (C := 1) (D := D) Real.contDiff_exp.contDiffOn hAs (by exact_mod_cast hj)
    uniqueDiffOn_univ hs1o.uniqueDiffOn (Set.mapsTo_univ _ _) h0s hCi hDi
  rw [iteratedFDerivWithin_of_isOpen j hs1o h0s] at hm
  exact hm
theorem norm_iteratedFDeriv_affine {k : ℕ} (f : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) (hf : ContDiffAt ℝ 40 f u)
    (a b : ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 40) :
    ‖iteratedFDeriv ℝ i (fun v => a * f v + b) u‖ = |a| * ‖iteratedFDeriv ℝ i f u‖ := by
  have hic : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast h2
  rw [norm_iteratedFDeriv_add_const (fun v => a * f v) b h1 u]
  have e : (fun v => a * f v) = a • f := by
    funext v
    simp [smul_eq_mul]
  rw [e, iteratedFDeriv_const_smul_apply (hf.of_le hic), norm_smul, Real.norm_eq_abs]
def affineWeight (R : StepSetup) (g : TorusField n → TorusField (n * R.params.side) → ℝ) (B : ℝ)
    (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField (n * R.params.side)) (u : Fin k → ℝ) : ℝ :=
  (3 + g (perturb c X u V) W / B) / 4
def integrand (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ)
    (A : Finset (TorusSite n)) (u : Fin k → ℝ) (W : TorusField (n * R.params.side)) : ℝ :=
  R.avoidingPart A W * K W u * ∏ b ∈ chartBondsInBlocks R.params.side A, perturbedMark R V c X b W u
theorem weightedMass_mul (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (K w : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ)
    (A : Finset (TorusSite n)) (u : Fin k → ℝ) :
    weightedMass R V c X (fun W u => K W u * w W u) A u =
      ∫ W, integrand R V c X K A u W * w W u ∂(fieldHaar (n * R.params.side)) := by
  show ∫ W, _ ∂(fieldHaar (n * R.params.side)) = _
  refine integral_congr_ae (ae_of_all _ fun W => ?_)
  simp only [integrand]
  ring
theorem perturbedMark_mem_unit {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * R.params.side)) (W : TorusField (n * R.params.side))
    (u : Fin k → ℝ) : 0 ≤ perturbedMark R V c X b W u ∧ perturbedMark R V c X b W u ≤ 1 :=
  S.cutoff_mem _ (norm_nonneg _)
theorem integrand_nonneg {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs) [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ) (hK : ∀ W u, 0 ≤ K W u) (A : Finset (TorusSite n))
    (u : Fin k → ℝ) (W : TorusField (n * R.params.side)) : 0 ≤ integrand R V c X K A u W :=
  mul_nonneg (mul_nonneg ((S.avoiding R S.hasExpansions n hn W).1 A) (hK W u))
    (Finset.prod_nonneg fun b _ => (perturbedMark_mem_unit S V c X b W u).1)
theorem integrand_insert_le {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs) [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (K : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ) (hK : ∀ W u, 0 ≤ K W u) (A : Finset (TorusSite n))
    (Y : TorusSite n) (u : Fin k → ℝ) (W : TorusField (n * R.params.side)) :
    integrand R V c X K (insert Y A) u W ≤ integrand R V c X K A u W := by
  classical
  have hsub : chartBondsInBlocks R.params.side A ⊆ chartBondsInBlocks R.params.side (insert Y A) := by
    intro b hb
    simp only [chartBondsInBlocks, Finset.mem_filter, Finset.mem_insert] at hb ⊢
    exact ⟨hb.1, Or.inr hb.2⟩
  have hprod : ∏ b ∈ chartBondsInBlocks R.params.side (insert Y A), perturbedMark R V c X b W u ≤
      ∏ b ∈ chartBondsInBlocks R.params.side A, perturbedMark R V c X b W u := by
    rw [← Finset.prod_sdiff hsub]
    refine mul_le_of_le_one_left (Finset.prod_nonneg fun b _ => (perturbedMark_mem_unit S V c X b W u).1) ?_
    exact Finset.prod_le_one (fun b _ => (perturbedMark_mem_unit S V c X b W u).1)
      fun b _ => (perturbedMark_mem_unit S V c X b W u).2
  have hd := (S.avoiding R S.hasExpansions n hn W).2 (insert Y A) A (Finset.subset_insert _ _)
  simp only [integrand]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hd (hK W u)) hprod
    (Finset.prod_nonneg fun b _ => (perturbedMark_mem_unit S V c X b W u).1)
    (mul_nonneg ((S.avoiding R S.hasExpansions n hn W).1 A) (hK W u))
theorem expectation_eq_exp_log_sub (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (g : TorusField n → TorusField (n * R.params.side) → ℝ) {B : ℝ} (hB : 0 < B) (hgb : ∀ V' W, |g V' W| ≤ B)
    (hgm : ∀ V', Measurable (g V')) (u : Fin k → ℝ)
    (hZ : 0 < weightedMass R V c X (meanKernel R V c X) Finset.univ u)
    (hZ' : 0 < weightedMass R V c X (fun W u => meanKernel R V c X W u * affineWeight R g B V c X W u)
      Finset.univ u) :
    fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V)) =
      4 * B * Real.exp (Real.log (weightedMass R V c X
          (fun W u => meanKernel R V c X W u * affineWeight R g B V c X W u) Finset.univ u) -
        Real.log (weightedMass R V c X (meanKernel R V c X) Finset.univ u)) + -(3 * B) := by
  set Z := weightedMass R V c X (meanKernel R V c X) Finset.univ u with hZd
  set Z' := weightedMass R V c X (fun W u => meanKernel R V c X W u * affineWeight R g B V c X W u)
    Finset.univ u with hZ'd
  have hf : Integrable (integrand R V c X (meanKernel R V c X) Finset.univ u) (fieldHaar (n * R.params.side)) :=
    integrable_of_integral_pos (μ := fieldHaar (n * R.params.side))
      (f := integrand R V c X (meanKernel R V c X) Finset.univ u) hZ
  have hw := integral_mul_affine_weight hf (hgm (perturb c X u V)) hB (hgb _)
  have e1 : Z' = ∫ W, integrand R V c X (meanKernel R V c X) Finset.univ u W *
      ((3 + g (perturb c X u V) W / B) / 4) ∂(fieldHaar (n * R.params.side)) :=
    weightedMass_mul R V c X (meanKernel R V c X) (affineWeight R g B V c X) Finset.univ u
  have e2 : ∫ W, integrand R V c X (meanKernel R V c X) Finset.univ u W ∂(fieldHaar (n * R.params.side)) = Z := rfl
  have e3 : fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V)) =
      (∫ W, integrand R V c X (meanKernel R V c X) Finset.univ u W * g (perturb c X u V) W
        ∂(fieldHaar (n * R.params.side))) / Z := by
    show (∫ W, _ ∂(fieldHaar (n * R.params.side))) / _ = _ / _
    congr 1
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    simp only [integrand, meanKernel, kernelAlongPerturbation, perturbedMark]
    ring
  set Nn := ∫ W, integrand R V c X (meanKernel R V c X) Finset.univ u W * g (perturb c X u V) W
    ∂(fieldHaar (n * R.params.side))
  rw [e3, Real.exp_sub, Real.exp_log hZ, Real.exp_log hZ', e1, hw, e2]
  field_simp
  ring
theorem expectation_bounds_at_zero_of_pos {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs)
    (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n) (g : TorusField n → TorusField (n * R.params.side) → ℝ) (B : ℝ)
    (qg : ℕ → ℝ) (hB : 0 < B) (hgb : ∀ V' W, |g V' W| ≤ B) (hgm : ∀ V', Measurable (g V'))
    (hgd : ∀ (k' : ℕ) (c' : Fin k' → TorusBond n) (X' : Fin k' → imaginaryQuaternions), AreUnitVectors X' →
      ∀ (V' : TorusField n) (W : TorusField (n * R.params.side)),
      ContDiff ℝ 40 (fun τ => g (perturb c' X' τ V') W) ∧
      ∀ τ, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c' X' τ' V') W) τ‖ ≤ qg k')
    (hq9 : ∀ k', k' ≤ 9 → qg k' ≤ B) (V : TorusField n) (hV : IsCold (9 / 8 * R.params.threshold) V)
    (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hu : AreUnitVectors X) :
    ContDiffAt ℝ 40 (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0 ∧
    (k ≤ 9 → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0‖ ≤
        B * ((4 * (Nat.factorial 40 : ℝ)) *
          (((1 + 2 * Cs) * massRate R (4 * Cp) (nearMarkBound Kf q)) * R.coupling ^ 5) ^ j)) := by
  classical
  have ha1 := S.one_le_paramCoupling
  have hx1 := S.one_le_coupling
  have hCp1 := S.one_le_kernelRate
  have hCs0 := S.logConst_nonneg
  set K := meanKernel R V c X with hKd
  set w := affineWeight R g B V c X with hwd
  set E := max 1 (qg k / B) with hEd
  set P0 := Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 with hP0d
  set κ0 := Real.exp (2 * (R.params.coupling * R.coupling) * k) with hκd
  have hE1 : 1 ≤ E := le_max_left _ _
  have hP01 : 1 ≤ P0 := by
    have h1 : 1 ≤ R.params.coupling * R.coupling := one_le_mul_of_one_le_of_one_le ha1 hx1
    have h2 : 1 ≤ Cp * (R.params.coupling * R.coupling) := one_le_mul_of_one_le_of_one_le hCp1 h1
    have h3 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le h2 h3
  have hPP : 1 ≤ 4 * E * P0 := by nlinarith
  have hP0P : P0 ≤ 4 * E * P0 := by nlinarith
  have hker := S.kernel n V k c X hu
  have hw_eq : ∀ W, w W = fun u => 1 / (4 * B) * g (perturb c X u V) W + 3 / 4 := fun W => by
    funext u
    simp only [hwd, affineWeight]
    field_simp
    ring
  have hwc : ∀ W, ContDiff ℝ 40 (w W) := fun W => by
    rw [hw_eq]
    exact (contDiff_const.mul (hgd k c X hu V W).1).add contDiff_const
  have hw1 : ∀ W u, 1 / 2 ≤ w W u := fun W u => by
    have h1 : -B ≤ g (perturb c X u V) W := (abs_le.mp (hgb _ W)).1
    have h2 : -1 ≤ g (perturb c X u V) W / B := by
      rw [le_div_iff₀ hB]
      linarith
    simp only [hwd, affineWeight]
    linarith
  have hw2 : ∀ W u, w W u ≤ 1 := fun W u => by
    have h1 : g (perturb c X u V) W ≤ B := (abs_le.mp (hgb _ W)).2
    have h2 : g (perturb c X u V) W / B ≤ 1 := by
      rw [div_le_iff₀ hB]
      linarith
    simp only [hwd, affineWeight]
    linarith
  have hwm : ∀ u, Measurable fun W => w W u := fun u =>
    ((measurable_const.add ((hgm _).div_const B)).div_const 4)
  have hwj : ∀ W u, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (w W) u‖ ≤ E := by
    intro W u i h1 h2
    rw [hw_eq, norm_iteratedFDeriv_affine _ u ((hgd k c X hu V W).1.contDiffAt) _ _ h1 h2]
    have hb := (hgd k c X hu V W).2 u i h1 h2
    rw [abs_of_pos (by positivity)]
    have e1 : 1 / (4 * B) * ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c X τ' V) W) u‖ ≤
        ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c X τ' V) W) u‖ / B := by
      rw [mul_comm, ← div_eq_mul_one_div, mul_comm 4 B, ← div_div]
      exact div_le_self (by positivity) (by norm_num)
    have e2 : ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c X τ' V) W) u‖ / B ≤ qg k / B :=
      div_le_div_of_nonneg_right hb hB.le
    exact e1.trans (e2.trans (le_max_right _ _))
  let K' : TorusField (n * R.params.side) → (Fin k → ℝ) → ℝ := fun W u => K W u * w W u
  have hker' : ∀ W, ContDiff ℝ 40 (K' W) ∧ (∀ u, 0 ≤ K' W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (K' W) u‖ ≤ (4 * E * P0) ^ i * K' W u) ∧
      ∀ u, K' W u ≤ 2 * κ0 * K' W 0 := fun W =>
    kernel_mul_weight hP01 hE1 (hker W).1 (hker W).2.1 (hker W).2.2.1 (hker W).2.2.2 (hwc W) (hw1 W) (hw2 W)
      (hwj W)
  have hκ0 : 0 ≤ κ0 := (Real.exp_pos _).le
  have hkerK : ∀ W, ContDiff ℝ 40 (K W) ∧ (∀ u, 0 ≤ K W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (K W) u‖ ≤ (4 * E * P0) ^ i * K W u) ∧
      ∀ u, K W u ≤ 2 * κ0 * K W 0 := fun W =>
    ⟨(hker W).1, (hker W).2.1, fun u i hi => ((hker W).2.2.1 u i hi).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hP0P i) ((hker W).2.1 u)),
      fun u => ((hker W).2.2.2 u).trans (mul_le_mul_of_nonneg_right (by linarith) ((hker W).2.1 0))⟩
  have hK0 : ∀ W u, 0 ≤ K W u := fun W u => (hker W).2.1 u
  have hcnear : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), IsCold (9 / 8 * R.params.threshold) (perturb c X u V) :=
    S.coldNear n V k c X 0 _ (by rw [perturb_zero_field]; exact hV)
  have hposZ : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), ∀ A : Finset (TorusSite n), 0 < weightedMass R V c X K A u :=
    hcnear.mono fun u hu' A => S.integral_pos n hn _ hu' A
  have hintg : ∀ A u, 0 < weightedMass R V c X K A u →
      Integrable (integrand R V c X K A u) (fieldHaar (n * R.params.side)) := fun A u h =>
    integrable_of_integral_pos (μ := fieldHaar (n * R.params.side)) (f := integrand R V c X K A u) h
  have hbetween : ∀ A u, 0 < weightedMass R V c X K A u →
      1 / 2 * weightedMass R V c X K A u ≤ weightedMass R V c X K' A u ∧
        weightedMass R V c X K' A u ≤ weightedMass R V c X K A u := by
    intro A u h
    have h1 := integral_mul_weight_between (hintg A u h) (hwm u) (fun W => hw1 W u) (fun W => hw2 W u)
      (integrand_nonneg S hn V c X K hK0 A u)
    rw [show weightedMass R V c X K' A u = _ from weightedMass_mul R V c X K w A u]
    exact h1
  have hposZ' : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), ∀ A : Finset (TorusSite n), 0 < weightedMass R V c X K' A u :=
    hposZ.mono fun u h A => by
      have h1 := (hbetween A u (h A)).1
      have h2 := h A
      linarith
  have hZ0 : ∀ A, 0 < weightedMass R V c X K A 0 := hposZ.self_of_nhds
  have hgas0 : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      7 / 8 * weightedMass R V c X K A 0 ≤ weightedMass R V c X K (insert Y A) 0 := fun A Y => by
    have h := S.gas n hn V hV A Y
    rw [← perturb_zero_field c X V] at h
    exact h
  have hhalfK : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      weightedMass R V c X K A 0 ≤ 2 * weightedMass R V c X K (insert Y A) 0 := fun A Y => by
    have h1 := hgas0 A Y
    have h2 := hZ0 A
    linarith
  have hhalfK' : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n),
      weightedMass R V c X K' A 0 ≤ 2 * weightedMass R V c X K' (insert Y A) 0 := fun A Y => by
    rw [show weightedMass R V c X K' A 0 = _ from weightedMass_mul R V c X K w A 0,
      show weightedMass R V c X K' (insert Y A) 0 = _ from weightedMass_mul R V c X K w (insert Y A) 0]
    exact integral_mul_weight_le_two_mul (hintg A 0 (hZ0 A)) (hintg _ 0 (hZ0 _)) (hwm 0) (fun W => hw1 W 0)
      (fun W => hw2 W 0) (integrand_nonneg S hn V c X K hK0 A 0) (integrand_insert_le S hn V c X K hK0 A Y 0)
      (hgas0 A Y)
  obtain ⟨hZc, hZb⟩ := log_weightedMass_bounds S n hn V hV k c X hu K hPP hkerK hposZ hhalfK Finset.univ
  obtain ⟨hZc', hZb'⟩ := log_weightedMass_bounds S n hn V hV k c X hu K' hPP hker' hposZ' hhalfK' Finset.univ
  let a : (Fin k → ℝ) → ℝ := fun u => Real.log (weightedMass R V c X K' Finset.univ u)
  let b : (Fin k → ℝ) → ℝ := fun u => Real.log (weightedMass R V c X K Finset.univ u)
  have hac : ContDiffAt ℝ 40 a 0 := hZc'
  have hbc : ContDiffAt ℝ 40 b 0 := hZc
  have hhc : ContDiffAt ℝ 40 (a - b) 0 := hac.sub hbc
  have hev : (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) =ᶠ[𝓝 0]
      fun u => 4 * B * Real.exp ((a - b) u) + -(3 * B) :=
    (hposZ.and hposZ').mono fun u h =>
      expectation_eq_exp_log_sub R V c X g hB hgb hgm u (h.1 Finset.univ) (h.2 Finset.univ)
  have hexpc : ContDiffAt ℝ 40 (fun u => Real.exp ((a - b) u)) 0 := hhc.exp
  refine ⟨((contDiffAt_const.mul hexpc).add contDiffAt_const).congr_of_eventuallyEq hev,
    fun hk9 j hj1 hj40 => ?_⟩
  have hE : E = 1 := max_eq_left ((div_le_one hB).mpr (hq9 k hk9))
  have hPe : 4 * E * P0 = 4 * Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 := by
    rw [hE, hP0d]
    ring
  have hb1 := hZb hk9 hPe
  have hb2 := hZb' hk9 hPe
  set rr := massRate R (4 * Cp) (nearMarkBound Kf q) * R.coupling ^ 5 with hrr
  have hr1 : 0 ≤ rr := by
    have h1 : (0 : ℝ) ≤ nearMarkBound Kf q := zero_le_one.trans (le_max_left _ _)
    simp only [hrr, massRate]
    have : (0 : ℝ) ≤ R.params.coupling := by linarith
    have : (0 : ℝ) ≤ Cp := by linarith
    have : (0 : ℝ) ≤ R.coupling := by linarith
    positivity
  have hD : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (a - b) 0‖ ≤ ((1 + 2 * Cs) * rr) ^ i := by
    intro i h1 h2
    have hic : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast h2
    rw [iteratedFDeriv_sub_apply (hac.of_le hic) (hbc.of_le hic)]
    refine (norm_sub_le _ _).trans ?_
    have h3 := hb2 i h1 h2
    have h4 := hb1 i h1 h2
    have h5 : 1 + 2 * Cs ≤ (1 + 2 * Cs) ^ i := le_self_pow₀ (by linarith) (by omega)
    have h6 : 0 ≤ rr ^ i := pow_nonneg hr1 i
    rw [mul_pow]
    have h7 : 2 * Cs * rr ^ i ≤ (1 + 2 * Cs) ^ i * rr ^ i :=
      mul_le_mul_of_nonneg_right (by linarith) h6
    linarith
  have hneg : (a - b) 0 ≤ 0 := by
    have h1 := (hbetween Finset.univ 0 (hZ0 _)).2
    have h2 := (hposZ'.self_of_nhds) Finset.univ
    have h3 : a 0 ≤ b 0 := Real.log_le_log h2 h1
    simp only [Pi.sub_apply]
    linarith
  have hje := norm_iteratedFDeriv_exp_le (a - b) hhc hneg hD hj40
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j).eq_of_nhds]
  rw [norm_iteratedFDeriv_affine (fun u => Real.exp ((a - b) u)) 0 hexpc _ _ hj1 hj40, abs_of_pos (by positivity)]
  have hf : (Nat.factorial j : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hj40
  have hDn : 0 ≤ ((1 + 2 * Cs) * rr) ^ j := pow_nonneg (mul_nonneg (by linarith) hr1) j
  have e5 : ‖iteratedFDeriv ℝ j (fun u => Real.exp ((a - b) u)) 0‖ ≤
      (Nat.factorial 40 : ℝ) * ((1 + 2 * Cs) * rr) ^ j := by
    refine hje.trans ?_
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right hf hDn
  have e6 : ((1 + 2 * Cs) * massRate R (4 * Cp) (nearMarkBound Kf q)) * R.coupling ^ 5 = (1 + 2 * Cs) * rr := by
    rw [hrr]
    ring
  rw [e6]
  calc 4 * B * ‖iteratedFDeriv ℝ j (fun u => Real.exp ((a - b) u)) 0‖
      ≤ 4 * B * ((Nat.factorial 40 : ℝ) * ((1 + 2 * Cs) * rr) ^ j) :=
        mul_le_mul_of_nonneg_left e5 (by positivity)
    _ = B * (4 * (Nat.factorial 40 : ℝ) * ((1 + 2 * Cs) * rr) ^ j) := by ring
theorem expectation_of_abs_le_zero (R : StepSetup) [NeZero n] (g : TorusField (n * R.params.side) → ℝ)
    (hg : ∀ W, |g W| ≤ 0) (V : TorusField n) : fullyMarkedExpectation R V g = 0 := by
  have e : g = fun _ => 0 := funext fun W => abs_nonpos_iff.mp (hg W)
  subst e
  simp [fullyMarkedExpectation]
theorem expectation_bounds_at_zero {R : StepSetup} {Kf : ℕ → ℝ} {q : ℝ → ℝ → ℝ} {Cp Cs : ℝ}
    (S : Hypotheses R Kf q Cp Cs)
    (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n) (g : TorusField n → TorusField (n * R.params.side) → ℝ) (B : ℝ)
    (qg : ℕ → ℝ) (hB : 0 ≤ B) (hgb : ∀ V' W, |g V' W| ≤ B) (hgm : ∀ V', Measurable (g V'))
    (hgd : ∀ (k' : ℕ) (c' : Fin k' → TorusBond n) (X' : Fin k' → imaginaryQuaternions), AreUnitVectors X' →
      ∀ (V' : TorusField n) (W : TorusField (n * R.params.side)),
      ContDiff ℝ 40 (fun τ => g (perturb c' X' τ V') W) ∧
      ∀ τ, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c' X' τ' V') W) τ‖ ≤ qg k')
    (hq9 : ∀ k', k' ≤ 9 → qg k' ≤ B) (V : TorusField n) (hV : IsCold (9 / 8 * R.params.threshold) V)
    (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hu : AreUnitVectors X) :
    ContDiffAt ℝ 40 (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0 ∧
    (k ≤ 9 → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0‖ ≤
        B * ((4 * (Nat.factorial 40 : ℝ)) *
          (((1 + 2 * Cs) * massRate R (4 * Cp) (nearMarkBound Kf q)) * R.coupling ^ 5) ^ j)) := by
  rcases hB.eq_or_lt with h0 | h0
  · subst h0
    have e : (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) = fun _ => 0 :=
      funext fun u => expectation_of_abs_le_zero R _ (hgb _) _
    rw [e]
    refine ⟨contDiffAt_const, fun _ j hj1 _ => ?_⟩
    rw [iteratedFDeriv_const_of_ne (by omega)]
    simp
  · exact expectation_bounds_at_zero_of_pos S n hn g B qg h0 hgb hgm hgd hq9 V hV k c X hu
theorem smooth_of_bounds_at_zero (R : StepSetup) {ay : ℕ → ℝ}
    (hAy : ∀ (n : ℕ) (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
      (τ₀ : Fin k → ℝ),
      ∃ A : (Fin k → ℝ) → (Fin (k * 3) → ℝ), ContDiffAt ℝ 40 A τ₀ ∧ A τ₀ = 0 ∧
        (∀ᶠ τ in 𝓝 τ₀, perturb c X τ V =
          perturb (repeatBondsThrice c) (basisAtEachBond k) (A τ) (perturb c X τ₀ V)) ∧
        (k ≤ 3 → AreUnitVectors X → ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j A τ₀‖ ≤ ay j))
    {Cs cB Dd : ℝ} (hCs0 : 0 ≤ Cs) (hcB1 : 1 ≤ cB) (hDd1 : 1 ≤ Dd) (hay : ∀ i, i ≤ 40 → ay i ≤ Dd)
    (hx1 : 1 ≤ R.coupling)
    (hc₃ : (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 ≤ R.coupling)
    (hzero : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (g : TorusField n → TorusField (n * R.params.side) → ℝ)
      (B : ℝ) (qg : ℕ → ℝ), 0 ≤ B →
      (∀ V' W, |g V' W| ≤ B) → (∀ V', Measurable (g V')) →
      (∀ (k' : ℕ) (c' : Fin k' → TorusBond n) (X' : Fin k' → imaginaryQuaternions), AreUnitVectors X' →
        ∀ (V' : TorusField n) (W : TorusField (n * R.params.side)),
        ContDiff ℝ 40 (fun τ => g (perturb c' X' τ V') W) ∧
        ∀ τ, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c' X' τ' V') W) τ‖ ≤ qg k') →
      (∀ k', k' ≤ 9 → qg k' ≤ B) → ∀ V : TorusField n, IsCold (9 / 8 * R.params.threshold) V →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ContDiffAt ℝ 40 (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0 ∧
      (k ≤ 9 → ∀ j, 1 ≤ j → j ≤ 40 →
        ‖iteratedFDeriv ℝ j (fun u => fullyMarkedExpectation R (perturb c X u V) (g (perturb c X u V))) 0‖ ≤
          B * (Cs * (cB * R.coupling ^ 5) ^ j))) :
    FullyMarkedExpectationsSmooth R 201 := by
  intro n _ hn g B qg hB0 hgb hgm hgd hq9 V k c X τ hcold
  obtain ⟨Af, hAc, hA0, hAev, hAj⟩ := hAy n V k c X τ
  have hu3 : AreUnitVectors (basisAtEachBond k) := fun l => norm_imaginaryBasis _
  obtain ⟨hz1, hz2⟩ := hzero n hn g B qg hB0 hgb hgm hgd hq9 (perturb c X τ V) hcold (k * 3)
    (repeatBondsThrice c) (basisAtEachBond k) hu3
  set Lz : (Fin (k * 3) → ℝ) → ℝ := fun w =>
    fullyMarkedExpectation R (perturb (repeatBondsThrice c) (basisAtEachBond k) w (perturb c X τ V))
      (g (perturb (repeatBondsThrice c) (basisAtEachBond k) w (perturb c X τ V))) with hLz
  have hev : (fun τ' => fullyMarkedExpectation R (perturb c X τ' V) (g (perturb c X τ' V))) =ᶠ[𝓝 τ] Lz ∘ Af :=
    hAev.mono fun τ' h => by
      simp only [Function.comp, hLz]
      rw [h]
  have hz1' : ContDiffAt ℝ 40 Lz (Af τ) := by
    rw [hA0]
    exact hz1
  refine ⟨(hz1'.comp τ hAc).congr_of_eventuallyEq hev, fun hk hu => ?_⟩
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 40).eq_of_nhds]
  have hk9 : k * 3 ≤ 9 := by omega
  have hbase1 : 1 ≤ cB * R.coupling ^ 5 := one_le_mul_of_one_le_of_one_le hcB1 (one_le_pow₀ hx1)
  have hx0 : 0 ≤ R.coupling := by linarith
  have hm := norm_iteratedFDeriv_comp_le_of_vanish Lz Af τ hz1 hAc hA0
    (CC := B * (Cs * (cB * R.coupling ^ 5) ^ 40)) (Dd := Dd) (by positivity)
    (fun i hi1 hi => (hz2 hk9 i hi1 hi).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase1 hi) hCs0) hB0))
    (fun i h1 h2 => (hAj hk hu i h1 h2).trans ((hay i h2).trans (le_self_pow₀ hDd1 (by omega))))
  refine hm.trans ?_
  have e : (Nat.factorial 40 : ℝ) * (B * (Cs * (cB * R.coupling ^ 5) ^ 40)) * Dd ^ 40 =
      (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 * R.coupling ^ 200 * B := by
    rw [mul_pow, ← pow_mul]
    ring
  rw [e]
  have e2 : R.coupling ^ (201 : ℝ) = R.coupling ^ 201 := by
    rw [show (201 : ℝ) = ((201 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e2]
  refine mul_le_mul_of_nonneg_right ?_ hB0
  calc (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 * R.coupling ^ 200 ≤ R.coupling * R.coupling ^ 200 :=
        mul_le_mul_of_nonneg_right hc₃ (by positivity)
    _ = R.coupling ^ 201 := by ring
theorem exp_neg_le_eighth {c x : ℝ} (h : 1 ≤ c * x) : Real.exp (-(7 * c * x)) ≤ 1 / 8 := by
  have h1 : (8 : ℝ) ≤ Real.exp (7 * c * x) := by
    have := Real.add_one_le_exp (7 * c * x)
    nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h1
theorem seven_eighths_le_of_gas {Z Z' e : ℝ} (hZ : 0 < Z) (he : e ≤ 1 / 8) (h : (1 - e) * Z ≤ Z') :
    7 / 8 * Z ≤ Z' := by
  nlinarith
end PerturbedExpectation
open PerturbedExpectation in
theorem fullyMarkedExpectationAlongPerturbation_holds (hG : ColdGasBounds) (hF : FrameAlongMoveBounds)
    (hJ : LogIteratedDerivBoundStatement) (hMk : LogMarkSmoothness) (hMs : GoodMarkAlongMove)
    (hK : KernelAlongPerturbationBounds) (hL : AvoidingParts.AvoidingPartNonnegAntitone)
    (hA : PerturbLocallyReparametrized) (hC : ColdNearStatement) (hCut : QuaternionCutoffSmoothBounded)
    (hB : BondsPerBlockBound) :
    FullyMarkedExpectationAlongPerturbation := by
  obtain ⟨rt₀, hrt₀, hgas⟩ := hG
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨yg, hgasT⟩ := hgas T hT hrt
  obtain ⟨Kf, yf, hKf, hfr⟩ := hF T hT
  obtain ⟨ay, hAy⟩ := hA
  obtain ⟨Cp, hCp1, hKer⟩ := hK
  have hσ : 0 < T.threshold := hT.σ_pos
  have hρ0 : 0 < T.threshold / 64 := by positivity
  have hcutT : IsCutoff (T.threshold / 64) T.cutoff := hT.cut
  obtain ⟨hψs, hψb⟩ := hCut (T.threshold / 64) T.cutoff hρ0 hcutT
  have hρ64 : T.threshold / 64 ≤ 1 / 64 := by
    have := hT.σ_one
    linarith
  have hz : ∀ v : ℍ[ℝ], T.threshold / 64 ≤ ‖v‖ → cutoffFactor (T.threshold / 64) T.cutoff ‖v‖ = 0 :=
    fun v hv => by
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hv)]
  obtain ⟨q, hq⟩ := hMk (fun v => cutoffFactor (T.threshold / 64) T.cutoff ‖v‖) (T.threshold / 64) hρ64
    (by
      have h40 := contDiff_infty.mp hψs 40
      have hc : ((40 : ℕ) : WithTop ℕ∞) = 40 := by norm_num
      rwa [hc] at h40) hψb hz
  have hJ' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → LogDerivConstant j C) := by
    intro j
    by_cases h : 1 ≤ j
    · obtain ⟨C, h0, h1⟩ := hJ j h
      exact ⟨C, h0, fun _ => h1⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose Cd hCd0 hCd using hJ'
  have hCs0 : 0 ≤ ∑ j ∈ Finset.range 41, Cd j := Finset.sum_nonneg fun j _ => hCd0 j
  have hCjs : ∀ j, j ≤ 40 → Cd j ≤ ∑ j ∈ Finset.range 41, Cd j := fun j hj =>
    Finset.single_le_sum (f := Cd) (fun j _ => hCd0 j) (Finset.mem_range.mpr (show j < 41 by omega))
  have hDd1 : 1 ≤ 1 + ∑ i ∈ Finset.range 41, |ay i| := by
    have : 0 ≤ ∑ i ∈ Finset.range 41, |ay i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hay : ∀ i, i ≤ 40 → ay i ≤ 1 + ∑ i ∈ Finset.range 41, |ay i| := fun i hi => by
    have h3 := Finset.single_le_sum (f := fun i => |ay i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (show i < 41 by omega))
    have h4 := le_abs_self (ay i)
    linarith
  have ha1 : 1 ≤ T.coupling := hT.a_ge
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ₁ := lt_min (by have := hT.κ_pos; positivity)
      (div_pos hT.cE_pos (by positivity))
    have h2 : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min hT.cE_pos (lt_min (mul_pos hT.κ_pos (by positivity)) (mul_pos h1 (by positivity)))
    exact mul_pos (by positivity) h2
  let Q₀ : ℝ := nearMarkBound Kf q
  have hQ₀1 : 1 ≤ Q₀ := le_max_left _ _
  let Cs₁ : ℝ := ∑ j ∈ Finset.range 41, Cd j
  let cB : ℝ := (1 + 2 * Cs₁) *
    ((9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) + 1) * (200 * (4 * Cp) * T.coupling * Q₀))
  have hcB1 : 1 ≤ cB := by
    have h0 : 0 ≤ 9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) := by positivity
    have h1 : 1 ≤ 9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) + 1 := by linarith
    have h2 : 1 ≤ Cp * T.coupling * Q₀ := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCp1 ha1) hQ₀1
    have h3 : 1 ≤ 200 * (4 * Cp) * T.coupling * Q₀ := by
      have e : 200 * (4 * Cp) * T.coupling * Q₀ = 800 * (Cp * T.coupling * Q₀) := by ring
      rw [e]
      linarith
    have h4 : 1 ≤ 1 + 2 * Cs₁ := by
      have : 0 ≤ Cs₁ := hCs0
      linarith
    exact one_le_mul_of_one_le_of_one_le h4 (one_le_mul_of_one_le_of_one_le h1 h3)
  let c₃ : ℝ := (Nat.factorial 40 : ℝ) * ((4 * (Nat.factorial 40 : ℝ)) * cB ^ 40) *
    (1 + ∑ i ∈ Finset.range 41, |ay i|) ^ 40
  refine ⟨201, max (max yg yf) (max 1 (max (1 / T.gasRate) c₃)), by norm_num, fun y hy R hR hArr => ?_⟩
  have hyg : yg ≤ y := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hy
  have hbc := (hgasT y hyg R hR hArr).1
  have hyx : y ≤ R.coupling := hR.le_coupling
  have hmax := le_trans hy hyx
  have hxf : yf ≤ R.coupling := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hmax
  have hx1 : 1 ≤ R.coupling := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hmax
  have hxch : 1 / T.gasRate ≤ R.coupling :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hmax
  have hxc₃ : c₃ ≤ R.coupling :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hmax
  have hrow : R.HasExpansions := hR.isStep.1
  have hchx : 1 ≤ T.gasRate * R.coupling := by
    have h := (div_le_iff₀ hch).mp hxch
    rwa [mul_comm] at h
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have hl : ℓ = T.stepParameters y := hR.params_eq
  have hr : ρA = T.ρA := hR.anchorRadius_eq
  have hc : p = T.cutoff := hR.barrierFn_eq
  subst hl hr hc
  have S : Hypotheses ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩ Kf q Cp Cs₁ :=
    { hasExpansions := hrow
      avoiding := hL
      goodMarks := hMs
      bondsPerBlock := hB
      coldNear := hC
      one_le_coupling := hx1
      threshold_pos := hσ
      anchorRadius_le_one := hT.chain.2.2.2.2.1
      one_le_paramCoupling := ha1
      frameConst_nonneg := hKf
      frames := fun n _ hn V hV k c X hu b hb => hfr x y hxf t n hn V hV k c X hu b hb
      markBounds := fun k U f a b c => hq k U f a b c
      one_le_kernelRate := hCp1
      kernel := fun n _ V k c X hu W =>
        hKer (T.stepParameters y) x ha1 hx1 n (readAtLevel (stepBlockFrame (T.stepParameters y).side n) 0 W)
          V k c X hu
      integral_pos := fun n _ hn V' hV' A => (hbc n hn V' hV' A 0).1
      gas := fun n _ hn V' hV' A Y => by
        obtain ⟨h0, h1, -⟩ := hbc n hn V' hV' A Y
        exact seven_eighths_le_of_gas h0 (exp_neg_le_eighth hchx) h1
      logConst_nonneg := hCs0
      logConst := fun j hj1 hj2 => ⟨Cd j, hCjs j hj2, hCd0 j, hCd j hj1⟩
      cutoff_mem := fun s hs => ⟨cutoffFactor_nonneg s, cutoffFactor_le_one hρ0 hcutT hs⟩ }
  have hC4 : (0 : ℝ) ≤ 4 * (Nat.factorial 40 : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  exact smooth_of_bounds_at_zero _ hAy hC4 hcB1 hDd1 hay hx1 hxc₃ (expectation_bounds_at_zero S)
end ResponseInTheExpansion
end YangMills.Construction
end
