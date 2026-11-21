import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.CutOnTheQuaternions
import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfAMarkedIntegral
import YangMills.Construction.ClusterExpansionOfAStep.FramesAlongUnitsProof
import YangMills.Construction.ClusterExpansionOfAStep.GasAtColdTops
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfAMarkedFamily
import YangMills.Construction.ClusterExpansionOfAStep.KernelAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.LowerPartsOfAStep
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps TorusBalls StepSettings RenormalizationStepParameters
  StepMarks StepCosts MarkedIntegrals MovedTopMarks BondMoves PolymerCumulant KernelVariation StepGas AvoidingParts
namespace ClusterExpansionOfAStep
namespace LogMarkedIntegral
variable {n : ℕ}
def kernelAtField (R : StepSetup) [NeZero n] (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (W : TorusField (n * R.params.side)) (u : Fin k → ℝ) : ℝ :=
  kernelAlongPerturbation R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) V c X u
def markAtField (R : StepSetup) (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * R.params.side))
    (W : TorusField (n * R.params.side)) (u : Fin k → ℝ) : ℝ :=
  R.bondMark (perturb c X u V) W b
theorem perturb_zero_eq {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (V : TorusField n) :
    perturb c X 0 V = V := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
theorem bondExpansion_of_units (R : StepSetup) (hrow : R.HasExpansions) (hlow : AvoidingPartNonnegAntitone)
    (hmarks : GoodMarkAlongMove)
    [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions)
    (hcnear : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), IsCold (9 / 8 * R.params.threshold) (perturb c X u V))
    (hpos : ∀ V' : TorusField n, IsCold (9 / 8 * R.params.threshold) V' →
      ∀ A : Finset (TorusSite n), 0 < R.markedIntegral A V')
    (hhalf : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n), R.markedIntegral A (perturb c X 0 V) ≤
      2 * R.markedIntegral (insert Y A) (perturb c X 0 V))
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
            ‖iteratedFDeriv ℝ j (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) τ‖ ≤
              q F S))
    {P κ S : ℝ} (hS : ∑ l, ‖X l‖ ≤ S) (hP : 1 ≤ P)
    (hker : ∀ W, ContDiff ℝ 40 (kernelAtField R V c X W) ∧ (∀ u, 0 ≤ kernelAtField R V c X W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (kernelAtField R V c X W) u‖ ≤ P ^ i * kernelAtField R V c X W u) ∧
      ∀ u, kernelAtField R V c X W u ≤ κ * kernelAtField R V c X W 0)
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
      (fun A W => R.avoidingPart A W) (kernelAtField R V c X) (fun b => markAtField R V c X b) P
      (max 1 (q F₀ S)) Q κ := by
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
  have hev : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), IsCold (9 / 8 * R.params.threshold) (perturb c X u V) ∧
      (∀ b ∈ all, ContDiffAt ℝ 40 (f b) u) ∧
      (∀ b ∈ all, ∀ i ∈ Finset.range 41, ‖iteratedFDeriv ℝ i (f b) u‖ < ‖iteratedFDeriv ℝ i (f b) 0‖ + 1) ∧
      (∀ b ∈ all, b ∉ near → f b u = f b 0) := by
    refine hcnear.and (((Filter.eventually_all_finset all).mpr fun b hb => (hat b hb).eventually (by simp)).and
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
  have hmark : ∀ b ∈ all, ∀ W, ContDiffOn ℝ 40 (markAtField R V c X b W) U ∧ ∀ u ∈ U, ∀ F : ℝ,
      (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (f b) u‖ ≤ F) → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (markAtField R V c X b W) u‖ ≤ q F S := by
    intro b hb W
    obtain ⟨h1, h2⟩ := hq k U (f b) hUo (hfU b hb) (fun u _ => hsize b hb u)
    rcases hmarks R.params R.anchorRadius R.barrierFn R.depth R.frameReach n V W k c X b with
      ⟨a₀, ha⟩ | ⟨-, g, hg⟩
    · have e : markAtField R V c X b W = fun u => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f b u‖ :=
        funext ha
      rw [e]
      exact ⟨(h2 a₀).1, fun u hu F hF j hj1 hj2 => (h2 a₀).2 u hu F S hF j hj1 hj2⟩
    · have e : markAtField R V c X b W = markAlongLog (fun v => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖v‖)
          (bondMoveLinear c X (parentBlock R.params.side b.1, b.2)) g (f b) := funext hg
      rw [e]
      exact ⟨(h1 _ g).1, fun u hu F hF j hj1 hj2 =>
        (h1 _ g).2 u hu F S ((norm_bondMoveLinear_le c X _).trans hS) hF j hj1 hj2⟩
  have hmark01 : ∀ b W u, 0 ≤ markAtField R V c X b W u ∧ markAtField R V c X b W u ≤ 1 := fun b W u =>
    hcut _ (norm_nonneg _)
  refine ⟨U, max 1 (q Fb S), fun N hN => ?_⟩
  have hNc : ((N : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hN
  exact
  { isOpen := hUo
    center_mem := h0U
    mem_bonds := fun A b => by simp [chartBondsInBlocks, hall]
    integral_pos := fun A u hu => hpos _ (hball u hu).1 A
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
      rcases hmarks R.params R.anchorRadius R.barrierFn R.depth R.frameReach n V W k c X b with
        ⟨a₀, ha⟩ | ⟨hl, -⟩
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
theorem card_le_of_parentBlock_mem (hB : BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n]
    (D : Finset (TorusSite n)) (S : Finset (TorusBond (n * L))) (hS : ∀ b ∈ S, parentBlock L b.1 ∈ D) :
    (S.card : ℝ) ≤ D.card * (4 * (2 * L) ^ 4) := by
  classical
  have h1 : S ⊆ D.biUnion fun Y => Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y := by
    intro b hb
    exact Finset.mem_biUnion.mpr ⟨_, hS b hb, by simp⟩
  have h2 := (Finset.card_le_card h1).trans Finset.card_biUnion_le
  have h3 : (S.card : ℝ) ≤
      ∑ Y ∈ D, ((Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y).card : ℝ) := by
    exact_mod_cast h2
  refine h3.trans ?_
  have h4 : ∀ Y ∈ D, ((Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y).card : ℝ) ≤
      4 * (2 * L) ^ 4 :=
    fun Y _ => by simpa using hB L n Y
  refine (Finset.sum_le_sum h4).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
theorem norm_iteratedFDeriv_add_const {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (z : F) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => g y + z) x‖ = ‖iteratedFDeriv ℝ i g x‖ := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv]
  congr 2
  funext y
  exact fderiv_add_const _
theorem norm_imaginaryBasis (i : Fin 3) : ‖imaginaryBasis i‖ = 1 := by apply _root_.YangMills.Construction.MovedTopMarks.UnitFamilies.norm_imaginaryBasis <;> assumption
theorem clusterRange_le {x : ℝ} (hx : 1 ≤ x) : ((clusterRange x : ℕ) : ℝ) ≤ 2 * x := by apply _root_.YangMills.SharedProofs.p24708 <;> assumption
theorem exp_neg_le_half {c x : ℝ} (h : 1 ≤ c * x) : Real.exp (-(7 * c * x)) ≤ 1 / 2 := by
  have h2 : Real.exp (-(7 * c * x)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
  have h3 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h4 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h3
  exact h2.trans h4
theorem le_two_mul_of_one_sub_mul_le {Z Z' e : ℝ} (hZ : 0 < Z) (he : e ≤ 1 / 2) (h : (1 - e) * Z ≤ Z') :
    Z ≤ 2 * Z' := by
  nlinarith
theorem card_le_of_near_bonds (hB : BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n] {k m : ℕ}
    (c : Fin k → TorusBond n) (near : Finset (TorusBond (n * L))) {x : ℝ} (hx : 1 ≤ x) (hm : (m : ℝ) ≤ 2 * x)
    (hk : (k : ℝ) ≤ 9) (hin : ∀ b ∈ near, ∃ l, supDist (parentBlock L b.1) (c l).1 ≤ m) :
    (near.card : ℝ) ≤ 9 * (13 * x) ^ 4 * (4 * (2 * (L : ℝ)) ^ 4) := by
  classical
  let Db : Finset (TorusSite n) := Finset.univ.biUnion fun l : Fin k => thickening m {(c l).1}
  have hDb : (Db.card : ℝ) ≤ k * (2 * (m : ℝ) + 1) ^ 4 := by
    have h1 : Db.card ≤ ∑ l : Fin k, (thickening m {(c l).1}).card := Finset.card_biUnion_le
    have h2 : ∑ l : Fin k, (thickening m {(c l).1}).card ≤ k * (2 * m + 1) ^ 4 := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun l : Fin k => (thickening m {(c l).1}).card)
        ((2 * m + 1) ^ 4) (fun l _ => card_thickening_singleton_le _ _)
      simpa using this
    exact_mod_cast h1.trans h2
  have hin' : ∀ b ∈ near, parentBlock L b.1 ∈ Db := by
    intro b hb
    obtain ⟨l, hl⟩ := hin b hb
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, (mem_thickening _ _ _).mpr
      ⟨(c l).1, Finset.mem_singleton_self _, hl⟩⟩
  have h1 := card_le_of_parentBlock_mem hB L Db near hin'
  have h2 : (2 * (m : ℝ) + 1) ≤ 13 * x := by linarith
  have h3 : (2 * (m : ℝ) + 1) ^ 4 ≤ (13 * x) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
  have h4 : (Db.card : ℝ) ≤ 9 * (13 * x) ^ 4 :=
    hDb.trans (mul_le_mul hk h3 (by positivity) (by norm_num))
  exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
theorem card_le_of_small_torus (hB : BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n] {m : ℕ}
    (near : Finset (TorusBond (n * L))) {x : ℝ} (hx : 1 ≤ x) (hm : (m : ℝ) ≤ 2 * x) (hs : n ≤ 4 * m + 5) :
    (near.card : ℝ) ≤ 9 * (13 * x) ^ 4 * (4 * (2 * (L : ℝ)) ^ 4) := by
  have hin : ∀ b ∈ near, parentBlock L b.1 ∈ (Finset.univ : Finset (TorusSite n)) := fun b _ => Finset.mem_univ _
  have h1 := card_le_of_parentBlock_mem hB L Finset.univ near hin
  have hcu : ((Finset.univ : Finset (TorusSite n)).card : ℝ) = (n : ℝ) ^ 4 := by
    simp [Finset.card_univ, ZMod.card]
  have hn' : (n : ℝ) ≤ 13 * x := by
    have h3 : (n : ℝ) ≤ 4 * (m : ℝ) + 5 := by exact_mod_cast hs
    linarith
  have h4 : (n : ℝ) ^ 4 ≤ 9 * (13 * x) ^ 4 := by
    have h5 : (n : ℝ) ^ 4 ≤ (13 * x) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 4
    linarith
  rw [hcu] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
theorem rate_product_le {N G Cp a Q x k : ℝ} (hN : N ≤ 9 * (13 * x) ^ 4 * G) (hx : 1 ≤ x) (hk0 : 0 ≤ k)
    (hk : k ≤ 9) (hCp : 1 ≤ Cp) (ha : 1 ≤ a) (hQ : 1 ≤ Q) (hG : 0 ≤ G) (_hN0 : 0 ≤ N) :
    (N + 1) * (2 * (Cp * (a * x) * (k + 1) ^ 2) * Q) ≤ ((9 * 13 ^ 4 * G + 1) * (200 * Cp * a * Q)) * x ^ 5 := by
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hN1 : N + 1 ≤ (9 * 13 ^ 4 * G + 1) * x ^ 4 := by
    have e : 9 * (13 * x) ^ 4 * G = 9 * 13 ^ 4 * G * x ^ 4 := by ring
    rw [e] at hN
    have : (9 * 13 ^ 4 * G + 1) * x ^ 4 = 9 * 13 ^ 4 * G * x ^ 4 + x ^ 4 := by ring
    linarith
  have hk10 : (k + 1) ^ 2 ≤ 100 := by nlinarith
  have hCa : 0 ≤ Cp * (a * x) := by positivity
  have hP : Cp * (a * x) * (k + 1) ^ 2 ≤ Cp * (a * x) * 100 := mul_le_mul_of_nonneg_left hk10 hCa
  have hP2 : 2 * (Cp * (a * x) * (k + 1) ^ 2) * Q ≤ (200 * Cp * a * Q) * x := by
    calc 2 * (Cp * (a * x) * (k + 1) ^ 2) * Q ≤ 2 * (Cp * (a * x) * 100) * Q :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = (200 * Cp * a * Q) * x := by ring
  calc (N + 1) * (2 * (Cp * (a * x) * (k + 1) ^ 2) * Q)
      ≤ ((9 * 13 ^ 4 * G + 1) * x ^ 4) * ((200 * Cp * a * Q) * x) :=
        mul_le_mul hN1 hP2 (by positivity) (by positivity)
    _ = _ := by ring
theorem boxRadius_le {x : ℝ} (hx : 1 ≤ x) : ((boxRadius x : ℕ) : ℝ) ≤ 2 * x := by
  have h1 : boxRadius x ≤ clusterRange x := Nat.div_le_self _ _
  have h2 : ((boxRadius x : ℕ) : ℝ) ≤ ((clusterRange x : ℕ) : ℝ) := by exact_mod_cast h1
  exact h2.trans (clusterRange_le hx)
def LogJetConstant (N : ℕ) (C : ℝ) : Prop :=
  ∀ {α ι β : Type} [MeasurableSpace α] [DecidableEq ι] (μ : Measure α) {k : ℕ}
    (U : Set (Fin k → ℝ)) (τ₀ : Fin k → ℝ) (block : β → ι) (all near : Finset β) (bonds : Finset ι → Finset β)
    (d : Finset ι → α → ℝ) (K : α → (Fin k → ℝ) → ℝ) (M : β → α → (Fin k → ℝ) → ℝ) (P Q₀ Q κ : ℝ),
    BondExpansion μ N U τ₀ block all near bonds d K M P Q₀ Q κ → ∀ A : Finset ι,
      ContDiffAt ℝ N (fun τ => Real.log (bondWeightedIntegral μ bonds d K M A τ)) τ₀ ∧
      ‖iteratedFDeriv ℝ N (fun τ => Real.log (bondWeightedIntegral μ bonds d K M A τ)) τ₀‖ ≤
        C * (((near.card : ℝ) + 1) * (2 * P * Q₀)) ^ N
def rateCoefficient (R : StepSetup) (Cp Q₀ : ℝ) : ℝ :=
  (9 * 13 ^ 4 * (4 * (2 * (R.params.side : ℝ)) ^ 4) + 1) * (200 * Cp * R.params.coupling * Q₀)
theorem log_markedIntegral_at_zero (R : StepSetup) (hrow : R.HasExpansions) (hL : AvoidingPartNonnegAntitone)
    (hMs : GoodMarkAlongMove) (hB : BondsPerBlockBound) (hC : ColdNearStatement)
    (hx1 : 1 ≤ R.coupling) (hσ : 0 < R.params.threshold) (hρA1 : R.anchorRadius ≤ 1) (ha1 : 1 ≤ R.params.coupling)
    {Kf : ℕ → ℝ} (hKf : ∀ j, 0 ≤ Kf j)
    (hfr : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold (5 / 4 * R.params.threshold) V →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ∀ b ∈ chartBonds R.params.side n,
        ContDiffAt ℝ 40 (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0 ∧
        (∀ u, ‖frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u‖ ≤ R.anchorRadius) ∧
        (∀ i, 1 ≤ i → i ≤ 40 →
          ‖iteratedFDeriv ℝ i (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0‖ ≤
            (k : ℝ) ^ i * Kf i) ∧
        (4 * R.frameReach + 5 < n →
          (∀ l h, BondOffsetInBox R.frameReach h → c l ≠ bondFrom (parentBlock R.params.side b.1) h) →
          ∀ᶠ u in 𝓝 0, frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u =
            frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b 0))
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
            ‖iteratedFDeriv ℝ j (fun τ => cutoffFactor (R.params.threshold / 64) R.barrierFn ‖a₀ - f τ‖) τ‖ ≤
              q F S))
    {Cp : ℝ} (hCp1 : 1 ≤ Cp)
    (hKer : ∀ (n : ℕ) [NeZero n] (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n)
      (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ∀ W, ContDiff ℝ 40 (kernelAtField R V c X W) ∧ (∀ u, 0 ≤ kernelAtField R V c X W u) ∧
      (∀ u, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (kernelAtField R V c X W) u‖ ≤
        (Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2) ^ i * kernelAtField R V c X W u) ∧
      ∀ u, kernelAtField R V c X W u ≤
        Real.exp (2 * (R.params.coupling * R.coupling) * k) * kernelAtField R V c X W 0)
    (hpos : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V' : TorusField n, IsCold (9 / 8 * R.params.threshold) V' →
      ∀ A : Finset (TorusSite n), 0 < R.markedIntegral A V')
    (hhalf : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V' : TorusField n,
      IsCold (9 / 8 * R.params.threshold) V' →
      ∀ (A : Finset (TorusSite n)) (Y : TorusSite n), R.markedIntegral A V' ≤ 2 * R.markedIntegral (insert Y A) V')
    {Cs : ℝ} (hCs0 : 0 ≤ Cs) (hjc : ∀ j, 1 ≤ j → j ≤ 40 → ∃ C, C ≤ Cs ∧ 0 ≤ C ∧ LogJetConstant j C)
    (hcutb : ∀ s : ℝ, 0 ≤ s → 0 ≤ cutoffFactor (R.params.threshold / 64) R.barrierFn s ∧
      cutoffFactor (R.params.threshold / 64) R.barrierFn s ≤ 1)
    (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n) (A : Finset (TorusSite n)) (V : TorusField n)
    (hV : IsCold (9 / 8 * R.params.threshold) V)
    (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hu : AreUnitVectors X) :
    ContDiffAt ℝ 40 (fun u => Real.log (R.markedIntegral A (perturb c X u V))) 0 ∧
    (k ≤ 9 → ∀ j, 1 ≤ j → j ≤ 40 →
      ‖iteratedFDeriv ℝ j (fun u => Real.log (R.markedIntegral A (perturb c X u V))) 0‖ ≤
        Cs * (rateCoefficient R Cp (max 1 (q (∑ i ∈ Finset.range 41, 9 ^ i * Kf i) 9)) * R.coupling ^ 5) ^ j) := by
  have hV54 : IsCold (5 / 4 * R.params.threshold) V := fun p μ ν h => (hV p μ ν h).trans (by linarith)
  have hfacts := fun (b : TorusBond (n * R.params.side)) (hb : b ∈ chartBonds R.params.side n) =>
    hfr n hn V hV54 k c X hu b hb
  have hcnear : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), IsCold (9 / 8 * R.params.threshold) (perturb c X u V) :=
    hC n V k c X 0 _ (by rw [perturb_zero_eq]; exact hV)
  have hhalf0 : ∀ (A : Finset (TorusSite n)) (Y : TorusSite n), R.markedIntegral A (perturb c X 0 V) ≤
      2 * R.markedIntegral (insert Y A) (perturb c X 0 V) := fun A Y => by
    rw [perturb_zero_eq]
    exact hhalf n hn V hV A Y
  have hat : ∀ b ∈ chartBonds R.params.side n,
      ContDiffAt ℝ 40 (frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b) 0 :=
    fun b hb => (hfacts b hb).1
  have hsize : ∀ b ∈ chartBonds R.params.side n, ∀ u,
      ‖frameAlongMove R.params R.anchorRadius R.depth R.frameReach V c X b u‖ ≤ 1 :=
    fun b hb u => ((hfacts b hb).2.1 u).trans hρA1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hP1 : 1 ≤ Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 := by
    have h1 : 1 ≤ R.params.coupling * R.coupling := one_le_mul_of_one_le_of_one_le ha1 hx1
    have h2 : 1 ≤ Cp * (R.params.coupling * R.coupling) := one_le_mul_of_one_le_of_one_le hCp1 h1
    have h3 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le h2 h3
  have hker := hKer n V k c X hu
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
    obtain ⟨U, Q, hfam⟩ := bondExpansion_of_units R hrow hL hMs hn V c X hcnear (hpos n hn) hhalf0 hat hsize q hq
      hSk hP1 hker hcutb (chartBonds R.params.side n) (fun b hb hbn => absurd hb hbn) hF₁b subset_rfl
    obtain ⟨C, -, -, hC40⟩ := hjc 40 (by norm_num) le_rfl
    have h40 := (hC40 (fieldHaar _) U 0 _ _ _ _ _ _ _ _ _ _ _ (hfam 40 le_rfl) A).1
    rw [hcast] at h40
    exact h40
  · intro hk9 j hj1 hj40
    classical
    have hk9' : (k : ℝ) ≤ 9 := by exact_mod_cast hk9
    let near : Finset (TorusBond (n * R.params.side)) := if 4 * R.frameReach + 5 < n then
        (chartBonds R.params.side n).filter fun b => ∃ l, (∃ h, BondOffsetInBox R.frameReach h ∧
          c l = bondFrom (parentBlock R.params.side b.1) h) ∨ c l = (parentBlock R.params.side b.1, b.2)
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
      · have hno : ∀ l, ¬ ((∃ h, BondOffsetInBox R.frameReach h ∧
            c l = bondFrom (parentBlock R.params.side b.1) h) ∨ c l = (parentBlock R.params.side b.1, b.2)) := by
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
    obtain ⟨U, Q, hfam⟩ := bondExpansion_of_units R hrow hL hMs hn V c X hcnear (hpos n hn) hhalf0 hat hsize q hq
      hS9 hP1 hker hcutb near hoff hF₀b hnear
    obtain ⟨C, hCle, hC0, hCj⟩ := hjc j hj1 hj40
    have hbnd := (hCj (fieldHaar _) U 0 _ _ _ _ _ _ _ _ _ _ _ (hfam j hj40) A).2
    have hm : ((R.frameReach : ℕ) : ℝ) ≤ 2 * R.coupling := boxRadius_le hx1
    have hcard : (near.card : ℝ) ≤ 9 * (13 * R.coupling) ^ 4 * (4 * (2 * (R.params.side : ℝ)) ^ 4) := by
      by_cases hs : 4 * R.frameReach + 5 < n
      · refine card_le_of_near_bonds hB R.params.side c near hx1 hm hk9' fun b hb => ?_
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
      · exact card_le_of_small_torus hB R.params.side near hx1 hm (not_lt.mp hs)
    have hQ1 : (1 : ℝ) ≤ max 1 (q (∑ i ∈ Finset.range 41, 9 ^ i * Kf i) 9) := le_max_left _ _
    have hBle := rate_product_le hcard hx1 hk0 hk9' hCp1 ha1 hQ1 (by positivity) (Nat.cast_nonneg _)
    have hB0 : 0 ≤ ((near.card : ℝ) + 1) * (2 * (Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2) *
        max 1 (q (∑ i ∈ Finset.range 41, 9 ^ i * Kf i) 9)) := by
      have h1 : (0 : ℝ) ≤ (near.card : ℝ) + 1 := by
        have : (0 : ℝ) ≤ near.card := Nat.cast_nonneg _
        linarith
      have h2 : 0 ≤ Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 := by linarith
      exact mul_nonneg h1 (mul_nonneg (by linarith) (by linarith))
    refine hbnd.trans ?_
    exact mul_le_mul hCle (pow_le_pow_left₀ hB0 hBle j) (pow_nonneg hB0 j) hCs0
theorem norm_iteratedFDeriv_comp_le_of_vanish {k k' : ℕ} (Lz : (Fin k' → ℝ) → ℝ) (Af : (Fin k → ℝ) → (Fin k' → ℝ))
    (τ : Fin k → ℝ) (hz1 : ContDiffAt ℝ 40 Lz 0) (hAc : ContDiffAt ℝ 40 Af τ) (hA0 : Af τ = 0) {CC Dd : ℝ}
    (hCC : 0 ≤ CC) (hLz : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i Lz 0‖ ≤ CC)
    (hAf : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i Af τ‖ ≤ Dd ^ i) :
    ‖iteratedFDeriv ℝ 40 (Lz ∘ Af) τ‖ ≤ (Nat.factorial 40 : ℝ) * CC * Dd ^ 40 := by
  have hne : (40 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  set z := Lz 0 with hzdef
  let L2 : (Fin k' → ℝ) → ℝ := fun w => Lz w + (-z)
  have hL2at : ContDiffAt ℝ 40 L2 0 := hz1.add contDiffAt_const
  have hL20 : L2 0 = 0 := by simp [L2, hzdef]
  have e0 : Lz ∘ Af = fun τ' => (L2 ∘ Af) τ' + z := funext fun τ' => by simp [L2]
  rw [e0, norm_iteratedFDeriv_add_const _ _ (by norm_num) τ]
  obtain ⟨u1, hu1, hL2on⟩ := hL2at.contDiffOn (m := 40) le_rfl (fun h => absurd h hne)
  obtain ⟨t1, ht1sub, ht1o, h0t1⟩ := mem_nhds_iff.mp hu1
  have hL2t : ContDiffOn ℝ 40 L2 t1 := hL2on.mono ht1sub
  obtain ⟨u2, hu2, hAon⟩ := hAc.contDiffOn (m := 40) le_rfl (fun h => absurd h hne)
  have hpre : Af ⁻¹' t1 ∈ 𝓝 τ :=
    hAc.continuousAt.preimage_mem_nhds (by rw [hA0]; exact ht1o.mem_nhds h0t1)
  obtain ⟨s1, hs1sub, hs1o, hτs1⟩ := mem_nhds_iff.mp (Filter.inter_mem hu2 hpre)
  have hAs : ContDiffOn ℝ 40 Af s1 := hAon.mono fun w hw => (hs1sub hw).1
  have hmaps : Set.MapsTo Af s1 t1 := fun w hw => (hs1sub hw).2
  have hCi : ∀ i, i ≤ 40 → ‖iteratedFDerivWithin ℝ i L2 t1 (Af τ)‖ ≤ CC := by
    intro i hi
    rw [hA0, iteratedFDerivWithin_of_isOpen i ht1o h0t1]
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero, hL20, norm_zero]
      exact hCC
    · rw [norm_iteratedFDeriv_add_const _ _ hi1 0]
      exact hLz i hi1 hi
  have hDi : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDerivWithin ℝ i Af s1 τ‖ ≤ Dd ^ i := by
    intro i h1 h2
    rw [iteratedFDerivWithin_of_isOpen i hs1o hτs1]
    exact hAf i h1 h2
  have hm := norm_iteratedFDerivWithin_comp_le (g := L2) (f := Af) (n := 40) (s := s1) (t := t1) (x := τ)
    (N := 40) (C := CC) (D := Dd) hL2t hAs (by norm_num) ht1o.uniqueDiffOn hs1o.uniqueDiffOn hmaps hτs1 hCi hDi
  rw [iteratedFDerivWithin_of_isOpen 40 hs1o hτs1] at hm
  exact hm
theorem logMarkedIntegralSmooth_of_at_zero (R : StepSetup) {ay : ℕ → ℝ}
    (hAy : ∀ (n : ℕ) (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
      (τ₀ : Fin k → ℝ),
      ∃ A : (Fin k → ℝ) → (Fin (k * 3) → ℝ), ContDiffAt ℝ 40 A τ₀ ∧ A τ₀ = 0 ∧
        (∀ᶠ τ in 𝓝 τ₀, perturb c X τ V =
          perturb (repeatBondsThrice c) (basisAtEachBond k) (A τ) (perturb c X τ₀ V)) ∧
        (k ≤ 3 → AreUnitVectors X → ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j A τ₀‖ ≤ ay j))
    {Cs cB Dd : ℝ} (hCs0 : 0 ≤ Cs) (hcB1 : 1 ≤ cB) (hDd1 : 1 ≤ Dd) (hay : ∀ i, i ≤ 40 → ay i ≤ Dd)
    (hx1 : 1 ≤ R.coupling)
    (hc₃ : (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 ≤ R.coupling)
    (hzero : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (A : Finset (TorusSite n)) (V : TorusField n),
      IsCold (9 / 8 * R.params.threshold) V → ∀ (k : ℕ) (c : Fin k → TorusBond n)
      (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ContDiffAt ℝ 40 (fun u => Real.log (R.markedIntegral A (perturb c X u V))) 0 ∧
      (k ≤ 9 → ∀ j, 1 ≤ j → j ≤ 40 →
        ‖iteratedFDeriv ℝ j (fun u => Real.log (R.markedIntegral A (perturb c X u V))) 0‖ ≤
          Cs * (cB * R.coupling ^ 5) ^ j)) :
    R.LogMarkedIntegralSmooth 201 := by
  intro n _ hn A V k c X τ hcold
  obtain ⟨Af, hAc, hA0, hAev, hAj⟩ := hAy n V k c X τ
  have hu3 : AreUnitVectors (basisAtEachBond k) := fun l => norm_imaginaryBasis _
  obtain ⟨hz1, hz2⟩ := hzero n hn A (perturb c X τ V) hcold (k * 3) (repeatBondsThrice c) (basisAtEachBond k) hu3
  set Lz : (Fin (k * 3) → ℝ) → ℝ := fun w =>
    Real.log (R.markedIntegral A (perturb (repeatBondsThrice c) (basisAtEachBond k) w (perturb c X τ V))) with hLz
  have hev : (fun τ' => Real.log (R.markedIntegral A (perturb c X τ' V))) =ᶠ[𝓝 τ] Lz ∘ Af :=
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
  have hm := norm_iteratedFDeriv_comp_le_of_vanish Lz Af τ hz1 hAc hA0 (CC := Cs * (cB * R.coupling ^ 5) ^ 40)
    (Dd := Dd) (by positivity)
    (fun i hi1 hi => (hz2 hk9 i hi1 hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase1 hi) hCs0))
    (fun i h1 h2 => (hAj hk hu i h1 h2).trans ((hay i h2).trans (le_self_pow₀ hDd1 (by omega))))
  refine hm.trans ?_
  have e : (Nat.factorial 40 : ℝ) * (Cs * (cB * R.coupling ^ 5) ^ 40) * Dd ^ 40 =
      (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 * R.coupling ^ 200 := by
    rw [mul_pow, ← pow_mul]
    ring
  rw [e]
  have e2 : R.coupling ^ (201 : ℝ) = R.coupling ^ 201 := by
    rw [show (201 : ℝ) = ((201 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e2]
  calc (Nat.factorial 40 : ℝ) * (Cs * cB ^ 40) * Dd ^ 40 * R.coupling ^ 200 ≤ R.coupling * R.coupling ^ 200 :=
        mul_le_mul_of_nonneg_right hc₃ (by positivity)
    _ = R.coupling ^ 201 := by ring
end LogMarkedIntegral
open LogMarkedIntegral in
theorem logMarkedIntegralDerivativesBounded_proof (hG : ColdGasBounds) (hF : FrameAlongMoveBounds)
    (hJ : LogIteratedDerivBoundStatement) (hMk : LogMarkSmoothness) (hMs : GoodMarkAlongMove)
    (hK : KernelAlongPerturbationBounds) (hL : AvoidingPartNonnegAntitone) (hA : PerturbLocallyReparametrized)
    (hC : ColdNearStatement) (hCut : QuaternionCutoffSmoothBounded) (hB : BondsPerBlockBound) :
    LogMarkedIntegralDerivativesBounded := by
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
  have hz : ∀ v : ℍ[ℝ], T.threshold / 64 ≤ ‖v‖ → cutoffFactor (T.threshold / 64) T.cutoff ‖v‖ = 0 := fun v hv => by
    unfold cutoffFactor
    rw [if_neg (not_lt.mpr hv)]
  obtain ⟨q, hq⟩ := hMk (fun v => cutoffFactor (T.threshold / 64) T.cutoff ‖v‖) (T.threshold / 64) hρ64
    (by
      have h40 := contDiff_infty.mp hψs 40
      have hc : ((40 : ℕ) : WithTop ℕ∞) = 40 := by norm_num
      rwa [hc] at h40) hψb hz
  have hJ' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → LogJetConstant j C) := by
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
  let Q₀ : ℝ := max 1 (q (∑ i ∈ Finset.range 41, 9 ^ i * Kf i) 9)
  have hQ₀1 : 1 ≤ Q₀ := le_max_left _ _
  let cB : ℝ := (9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) + 1) * (200 * Cp * T.coupling * Q₀)
  have hcB1 : 1 ≤ cB := by
    have h0 : 0 ≤ 9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) := by positivity
    have h1 : 1 ≤ 9 * 13 ^ 4 * (4 * (2 * (T.side : ℝ)) ^ 4) + 1 := by linarith
    have h2 : 1 ≤ Cp * T.coupling * Q₀ := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCp1 ha1) hQ₀1
    have h3 : 1 ≤ 200 * Cp * T.coupling * Q₀ := by
      have e : 200 * Cp * T.coupling * Q₀ = 200 * (Cp * T.coupling * Q₀) := by ring
      rw [e]
      linarith
    exact one_le_mul_of_one_le_of_one_le h1 h3
  let c₃ : ℝ := (Nat.factorial 40 : ℝ) * ((∑ j ∈ Finset.range 41, Cd j) * cB ^ 40) *
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
    rw [div_le_iff₀ hch] at hxch
    linarith
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have hl : ℓ = T.stepParameters y := hR.params_eq
  have hr : ρA = T.ρA := hR.anchorRadius_eq
  have hc : p = T.cutoff := hR.barrierFn_eq
  subst hl hr hc
  refine logMarkedIntegralSmooth_of_at_zero _ hAy hCs0 hcB1 hDd1 hay hx1 hxc₃ ?_
  intro n _ hn A V hV k c X hu
  refine log_markedIntegral_at_zero _ hrow hL hMs hB hC hx1 hσ hT.chain.2.2.2.2.1 ha1 hKf
    (fun n _ hn V hV k c X hu b hb => hfr x y hxf t n hn V hV k c X hu b hb) q
    (fun k U f a b c => hq k U f a b c) hCp1
    (fun n _ V k c X hu W => hKer (T.stepParameters y) x ha1 hx1 n
      (readAtLevel (stepBlockFrame (T.stepParameters y).side n) 0 W) V k c X hu)
    (fun n _ hn V' hV' A => (hbc n hn V' hV' A 0).1)
    (fun n _ hn V' hV' A Y => by
      obtain ⟨h0, h1, -⟩ := hbc n hn V' hV' A Y
      exact le_two_mul_of_one_sub_mul_le h0 (exp_neg_le_half hchx) h1)
    hCs0 (fun j hj1 hj2 => ⟨Cd j, hCjs j hj2, hCd0 j, hCd j hj1⟩)
    (fun s hs => ⟨cutoffFactor_nonneg s, cutoffFactor_le_one hρ0 hcutT hs⟩) n hn A V hV k c X hu
end ClusterExpansionOfAStep
end YangMills.Construction
end
