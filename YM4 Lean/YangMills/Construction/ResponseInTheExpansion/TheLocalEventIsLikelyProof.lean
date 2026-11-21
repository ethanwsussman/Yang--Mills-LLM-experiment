import YangMills.Construction.CellOfTheFlow.TheChanceOfACellHasItsValueProof
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import YangMills.Construction.ResponseInTheExpansion.TheHullIsRareAtASite
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikely
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps TorusFields TorusCounting StepSettings RenormalizationStepParameters StepReturn StepFloors WeightedResponses CellWindows
namespace LocalEventLikely
section Laws
theorem measureReal_preimage_le_of_measurePreserving {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν] {f : α → β} (hf : MeasurePreserving f μ ν) (E : Set β) :
    μ.real (f ⁻¹' E) ≤ ν.real E := by
  have h := Measure.le_map_apply (μ := μ) hf.measurable.aemeasurable E
  rw [hf.map_eq] at h
  exact ENNReal.toReal_mono (measure_ne_top ν E) h
variable {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) (hD : forgetLastStepStatement) (T : StageTower ℓ)
  (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable) (β : ℝ)
include hfit hD hcut hco in
theorem isProbabilityMeasure_markedSampleLaw (s n : ℕ) [NeZero n] :
    IsProbabilityMeasure (markedSampleLaw T β s n) :=
  (hD ℓ hfit hfit.depth_lt T hcut hco β s n).1
include hfit hD hcut hco in
theorem measureReal_sampleBelow_preimage_le (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (E : Set (MarkedSample ℓ s (fineSide ℓ.side d n))),
    (markedSampleLaw T β (s + d) n).real (sampleBelow ℓ s d n ⁻¹' E) ≤
      (markedSampleLaw T β s (fineSide ℓ.side d n)).real E := by
  intro d
  induction d with
  | zero =>
    intro n _ E
    exact le_rfl
  | succ d ih =>
    intro n _ E
    have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (s + d) (n * ℓ.side)
    have h1 := measureReal_preimage_le_of_measurePreserving (hD ℓ hfit hfit.depth_lt T hcut hco β (s + d) n).2
      (sampleBelow ℓ s d (n * ℓ.side) ⁻¹' E)
    exact h1.trans (ih (n * ℓ.side) E)
theorem isBlockTorusSide_mul {n : ℕ} (hb : IsBlockTorusSide ℓ n) (h0 : 0 < ℓ.side) :
    IsBlockTorusSide ℓ (n * ℓ.side) := by
  have h1 : ℓ.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ h0) hb.2
  exact ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ h1⟩
theorem isBlockTorusSide_fineSide (h0 : 0 < ℓ.side) :
    ∀ (d : ℕ) {n : ℕ}, IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ (fineSide ℓ.side d n)
  | 0, _, hb => hb
  | d + 1, _, hb => isBlockTorusSide_fineSide h0 d (isBlockTorusSide_mul hb h0)
include hfit hD hcut hco in
theorem measureReal_not_stepsAvoidOrigin_le (h0 : 0 < ℓ.side) (k₀ : ℕ) (m b : ℝ) :
    ∀ (d n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
      (∀ j < d, ∀ (n' : ℕ) [NeZero n'], IsBlockTorusSide ℓ n' → ∀ o' : TorusSite n',
        (markedSampleLaw T β (k₀ + j + 1) n').real {u | ¬ StepAvoids T (k₀ + j) m o' u} ≤ b) →
      ∀ o : TorusSite (fineSide ℓ.side d n),
        (markedSampleLaw T β (k₀ + d) n).real {u | ¬ StepsAvoidOrigin T k₀ m d n u o} ≤ d * b := by
  intro d
  induction d with
  | zero =>
    intro n _ hb hs o
    simp [StepsAvoidOrigin]
  | succ d ih =>
    intro n _ hb hs o
    have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (k₀ + d + 1) n
    have h1 := ih (n * ℓ.side) (isBlockTorusSide_mul hb h0) (fun j hj => hs j (Nat.lt_succ_of_lt hj)) o
    have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (k₀ + d) (n * ℓ.side)
    have h2 := measureReal_preimage_le_of_measurePreserving (hD ℓ hfit hfit.depth_lt T hcut hco β (k₀ + d) n).2
      {u | ¬ StepsAvoidOrigin T k₀ m d (n * ℓ.side) u o}
    have h3 := hs d (Nat.lt_succ_self d) n hb (siteAbove ℓ.side (d + 1) n o)
    have hsub : {u : MarkedSample ℓ (k₀ + (d + 1)) n | ¬ StepsAvoidOrigin T k₀ m (d + 1) n u o} ⊆
        ((fun u : MarkedSample ℓ (k₀ + d + 1) n => u.1) ⁻¹'
          {u | ¬ StepsAvoidOrigin T k₀ m d (n * ℓ.side) u o}) ∪
          {u | ¬ StepAvoids T (k₀ + d) m (siteAbove ℓ.side (d + 1) n o) u} := by
      intro u hu
      by_contra hc
      refine hu ?_
      simp only [Set.mem_union, not_or] at hc
      exact ⟨not_not.mp hc.1, not_not.mp hc.2⟩
    calc (markedSampleLaw T β (k₀ + (d + 1)) n).real {u | ¬ StepsAvoidOrigin T k₀ m (d + 1) n u o}
        ≤ (markedSampleLaw T β (k₀ + d + 1) n).real (((fun u : MarkedSample ℓ (k₀ + d + 1) n => u.1) ⁻¹'
          {u | ¬ StepsAvoidOrigin T k₀ m d (n * ℓ.side) u o}) ∪
          {u | ¬ StepAvoids T (k₀ + d) m (siteAbove ℓ.side (d + 1) n o) u}) := measureReal_mono hsub
      _ ≤ (markedSampleLaw T β (k₀ + d + 1) n).real ((fun u : MarkedSample ℓ (k₀ + d + 1) n => u.1) ⁻¹'
          {u | ¬ StepsAvoidOrigin T k₀ m d (n * ℓ.side) u o}) +
          (markedSampleLaw T β (k₀ + d + 1) n).real
            {u | ¬ StepAvoids T (k₀ + d) m (siteAbove ℓ.side (d + 1) n o) u} :=
          measureReal_union_le _ _
      _ ≤ d * b + b := add_le_add (h2.trans h1) h3
      _ = ((d + 1 : ℕ) : ℝ) * b := by
          push_cast
          ring
include hfit hD hcut hco in
theorem measureReal_not_isLocalEvent_le (h0 : 0 < ℓ.side) (k M N : ℕ) [NeZero N] (hN : IsBlockTorusSide ℓ N)
    (m b t : ℝ) (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (htop : (markedSampleLaw T β (k + M + M) N).real {u | ¬ Disjoint (stageState T (k + M + M) N u).2.1
      (supBall (siteAbove ℓ.side M N (siteAbove ℓ.side M (fineSide ℓ.side M N) o)) m)} ≤ t)
    (hstep : ∀ j < M + M, ∀ (n' : ℕ) [NeZero n'], IsBlockTorusSide ℓ n' → ∀ o' : TorusSite n',
      (markedSampleLaw T β (k + j + 1) n').real {u | ¬ StepAvoids T (k + j) m o' u} ≤ b) :
    (markedSampleLaw T β (k + M + M) N).real {u | ¬ IsLocalEvent T k M m N u o} ≤ t + (M + M) * b := by
  have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (k + M + M) N
  have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (k + M) (fineSide ℓ.side M N)
  have hup := measureReal_not_stepsAvoidOrigin_le hfit hD T hcut hco β h0 (k + M) m b M N hN
    (fun j hj n' _ hb o' => by
      have h := hstep (M + j) (by omega) n' hb o'
      rwa [show k + (M + j) = k + M + j by omega] at h)
    (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
  have hlo := measureReal_not_stepsAvoidOrigin_le hfit hD T hcut hco β h0 k m b M (fineSide ℓ.side M N)
    (isBlockTorusSide_fineSide h0 M hN) (fun j hj n' _ hb o' => hstep j (by omega) n' hb o') o
  have hlo' := (measureReal_sampleBelow_preimage_le hfit hD T hcut hco β (k + M) M N
    {u | ¬ StepsAvoidOrigin T k m M (fineSide ℓ.side M N) u o}).trans hlo
  have hsub : {u : MarkedSample ℓ (k + M + M) N | ¬ IsLocalEvent T k M m N u o} ⊆
      {u | ¬ Disjoint (stageState T (k + M + M) N u).2.1
        (supBall (siteAbove ℓ.side M N (siteAbove ℓ.side M (fineSide ℓ.side M N) o)) m)} ∪
      ({u | ¬ StepsAvoidOrigin T (k + M) m M N u (siteAbove ℓ.side M (fineSide ℓ.side M N) o)} ∪
        (sampleBelow ℓ (k + M) M N ⁻¹' {u | ¬ StepsAvoidOrigin T k m M (fineSide ℓ.side M N) u o})) := by
    intro u hu
    by_contra hc
    refine hu ?_
    simp only [Set.mem_union, not_or] at hc
    exact ⟨not_not.mp hc.1, not_not.mp hc.2.1, not_not.mp hc.2.2⟩
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have h3 := measureReal_union_le (μ := markedSampleLaw T β (k + M + M) N)
    {u | ¬ StepsAvoidOrigin T (k + M) m M N u (siteAbove ℓ.side M (fineSide ℓ.side M N) o)}
    (sampleBelow ℓ (k + M) M N ⁻¹' {u | ¬ StepsAvoidOrigin T k m M (fineSide ℓ.side M N) u o})
  have e : ((M : ℝ) + M) * b = M * b + M * b := by ring
  rw [e]
  exact add_le_add htop (h3.trans (add_le_add hup hlo'))
end Laws
section Counts
variable {n : ℕ} [NeZero n]
theorem card_supBall_le (o : TorusSite n) {m : ℝ} (hm : 0 ≤ m) : (supBall o m).card ≤ (2 * ⌊m⌋₊ + 1) ^ 4 := by
  classical
  refine (Finset.card_le_card ?_).trans (card_thickening_singleton_le ⌊m⌋₊ o)
  intro z hz
  have h := (Finset.mem_filter.mp hz).2
  exact (mem_thickening _ _ _).mpr ⟨o, Finset.mem_singleton.mpr rfl, Nat.le_floor h⟩
private theorem mem_sitesInBlocks {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
theorem card_sitesInBlocks_le (L : ℕ) [NeZero L] (Z : Finset (TorusSite n)) :
    (sitesInBlocks L Z).card ≤ Z.card * (2 * L + 1) ^ 4 := by
  classical
  have hsub : sitesInBlocks L Z ⊆ Z.biUnion fun Y => sitesInBlocks L {Y} := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨parentBlock L x, mem_sitesInBlocks.mp hx,
      mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr rfl)⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul _ _ _ fun Y _ => card_sitesInBlocks_singleton_le Y)
theorem card_blocksNearFreeCores_le (L r : ℕ) [NeZero L] (Z : Finset (TorusSite n)) :
    (blocksNearFreeCores L r Z).card ≤ Z.card * (2 * L + 1) ^ 4 * (8 * r + 1) ^ 4 := by
  classical
  refine Finset.card_image_le.trans ((card_thickening_le (4 * r) _).trans ?_)
  have e : 2 * (4 * r) + 1 = 8 * r + 1 := by ring
  rw [e]
  exact Nat.mul_le_mul_right _ (card_sitesInBlocks_le L Z)
end Counts
section Floors
theorem eventually_floor_bounds (B : ℝ) (L n₀ : ℕ) (c₂ x₂ Cp : ℝ) (hc₂ : 0 < c₂) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 1 ≤ x ∧ 2 * x₂ ≤ x ∧ 4 * B * Real.log x ^ 2 ≤ x / 2 ∧ Real.log x ^ 2 ≤ x ∧
      L * n₀ ≤ 2 ^ 10 * ⌊x ^ ((1 : ℝ) / 20)⌋₊ ∧
      2 * (L * (2 ^ 7 * ⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊)) ≤ 2 ^ 10 * ⌊x ^ ((1 : ℝ) / 20)⌋₊ ∧
      Cp * x ^ 9 ≤ Real.exp (c₂ / 2 * x) := by
  have hlog := Real.isLittleO_pow_log_id_atTop (n := 2)
  have h3 := hlog.def (show (0 : ℝ) < 1 / (8 * (|B| + 1)) by positivity)
  have h4 := hlog.def (show (0 : ℝ) < 1 by norm_num)
  have h7 := (isLittleO_pow_exp_pos_mul_atTop (k := 9) (show 0 < c₂ / 2 by positivity)).def
    (show (0 : ℝ) < 1 / (|Cp| + 1) by positivity)
  have h5 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).eventually_ge_atTop
    ((L : ℝ) * n₀ + 2 ^ 10 * L + 2 ^ 10)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((((h3.and h4).and (h5.and h7)).and
    ((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop (2 * x₂)))))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨⟨⟨a3, a4⟩, a5, a7⟩, a1, a2⟩ := hx₀ x hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos a1
  simp only [id, Real.norm_eq_abs, abs_of_pos hx0, abs_pow, sq_abs] at a3 a4
  set w := x ^ ((1 : ℝ) / 100) with hw
  have hLn : (0 : ℝ) ≤ (L : ℝ) * n₀ := by positivity
  have hLr : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hw5 : x ^ ((1 : ℝ) / 20) = w ^ 5 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h2w : (2 * x) ^ ((1 : ℝ) / 100) ≤ 2 * w := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    have : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hfl : w ^ 5 - 1 ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
    rw [hw5]
    have := Nat.lt_floor_add_one (w ^ 5)
    linarith
  have hce : (⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ 2 * w + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (2 * x) ^ ((1 : ℝ) / 100) by positivity)
    linarith
  have hw2 : w ^ 2 ≤ w ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hww : w * 2 ^ 10 ≤ w ^ 2 := by nlinarith
  refine ⟨a1, a2, ?_, ?_, ?_, ?_, ?_⟩
  · have hB : B ≤ |B| + 1 := by linarith [le_abs_self B]
    have hB1 : 0 < |B| + 1 := by positivity
    have h0 : 0 ≤ Real.log x ^ 2 := by positivity
    have e : (|B| + 1) * Real.log x ^ 2 ≤ x / 8 := by
      have := mul_le_mul_of_nonneg_left a3 hB1.le
      have e2 : (|B| + 1) * (1 / (8 * (|B| + 1)) * x) = x / 8 := by
        field_simp
      linarith
    have := mul_le_mul_of_nonneg_right hB h0
    linarith
  · linarith
  · have : (((L * n₀ : ℕ) : ℝ)) ≤ ((2 ^ 10 * ⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  · have : (((2 * (L * (2 ^ 7 * ⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊)) : ℕ) : ℝ)) ≤
        ((2 ^ 10 * ⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ) := by
      push_cast
      have e1 : (L : ℝ) * (⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ L * (2 * w + 1) :=
        mul_le_mul_of_nonneg_left hce hLr
      have e2 : (L : ℝ) * w ≤ w ^ 2 / 2 ^ 10 := by
        have : (L : ℝ) * 2 ^ 10 ≤ w := by nlinarith
        nlinarith
      nlinarith
    exact_mod_cast this
  · have hn : |x ^ 9| ≤ 1 / (|Cp| + 1) * |Real.exp (c₂ / 2 * x)| := by
      simpa only [Real.norm_eq_abs] using a7
    rw [abs_of_pos (by positivity : 0 < x ^ 9), abs_of_pos (Real.exp_pos _)] at hn
    have h1 : 0 < |Cp| + 1 := by positivity
    have h2 : (|Cp| + 1) * x ^ 9 ≤ Real.exp (c₂ / 2 * x) := by
      have := mul_le_mul_of_nonneg_left hn h1.le
      have e2 : (|Cp| + 1) * (1 / (|Cp| + 1) * Real.exp (c₂ / 2 * x)) = Real.exp (c₂ / 2 * x) := by
        field_simp
      linarith
    have h3' : Cp ≤ |Cp| + 1 := by linarith [le_abs_self Cp]
    have := mul_le_mul_of_nonneg_right h3' (show 0 ≤ x ^ 9 by positivity)
    linarith
theorem baseCellSide_le {L r : ℕ} (hL : 2 ≤ L) (hr : 1 ≤ r) : CellWindows.baseCellSide L r ≤ L * (2 ^ 7 * r) := by apply _root_.YangMills.SharedProofs.p1293 <;> assumption
end Floors
section ScaleFlow
variable {ℓ : TorusLumps.StepParameters}
theorem hasExpansion_expansionCoupling (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
theorem hasExpansion_couplingFlow (hR : ExpansionReturnsAt ℓ) {β : ℝ} (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2
  | 0, _ => h0
  | t + 1, hj => (hasExpansion_expansionCoupling hR (hj t (Nat.lt_succ_self t))
      (hasExpansion_couplingFlow hR h0 t fun j hjt => hj j (Nat.lt_succ_of_lt hjt))).1
theorem abs_couplingFlow_succ_sub_le (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) {t : ℕ}
    (hj : ∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
theorem abs_couplingFlow_add_sub_le (β : ℝ) (k K : ℕ)
    (hm : ∀ j ≤ K, |(couplingFlow ℓ β (j + 1)).1 - (couplingFlow ℓ β j).1| ≤ 2 * ℓ.B) :
    ∀ i : ℕ, k + i ≤ K + 1 → |(couplingFlow ℓ β (k + i)).1 - (couplingFlow ℓ β k).1| ≤ 2 * ℓ.B * i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hm (k + i) (by omega)
    have e : (couplingFlow ℓ β (k + (i + 1))).1 - (couplingFlow ℓ β k).1 =
        ((couplingFlow ℓ β (k + i + 1)).1 - (couplingFlow ℓ β (k + i)).1) +
          ((couplingFlow ℓ β (k + i)).1 - (couplingFlow ℓ β k).1) := by
      rw [show k + (i + 1) = k + i + 1 by omega]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith
theorem stage_functional_eq (T : StageTower ℓ) {β : ℝ} (hW : T.base.functional = wilsonWeight β) {K : ℕ}
    (hc : ∀ j ≤ K, (T.stage j).coupling = (couplingFlow ℓ β j).1) :
    ∀ j ≤ K + 1, (T.stage j).functional = (couplingFlow ℓ β j).2 := by
  intro j
  induction j with
  | zero => exact fun _ => hW
  | succ j ih =>
    intro hj
    show kernelImage ℓ (T.stage j).coupling (T.stage j).functional =
      kernelImage ℓ (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2
    rw [ih (by omega), hc j (by omega)]
theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y) (hy₁ : 1 ≤ y)
    {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
end ScaleFlow
section Core
open Classical in
theorem measureReal_not_isLocalEvent_le_exp (hD : forgetLastStepStatement) {Tb : ParameterAssignment} (hTb : Tb.Admissible)
    {y : ℝ} (hy₀ : Tb.floorMin ≤ y)
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hwil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hFl : ∀ x : ℝ, y ≤ x → Tb.FloorConditions (2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17) 1 x)
    (hFr : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
      IsTowerAtParameters Tb y T β s →
      ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn →
      T.MarksMeasurable → (T.stage s).toStepSetup.IsWellPosed →
      (T.stage s).nextCoupling ≤ 1.01 * (T.stage s).coupling → IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (m : ℝ) (o : TorusSite n),
        (markedSampleLaw T β (s + 1) n).real {u | ¬ StepAvoids T s m o u} ≤
          ((blocksNearFreeCores (Tb.stepParameters y).side (T.stage s).toStepSetup.range (supBall o m)).card : ℝ) *
            Real.exp (-(7 * Tb.gasRate * (T.stage s).coupling)))
    (hHr : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N],
      N = 2 * (Tb.stepParameters y).side ^ e → IsTowerAtParameters Tb y T β k → T.MarksMeasurable →
      2 * CellWindows.baseCellSide (Tb.stepParameters y).side (clusterRange (T.stage k).coupling) ≤ N →
      ∀ v : TorusSite N,
        (markedSampleLaw T β k N).real {u | v ∈ (stageState T k N u).2.1} ≤
          Real.exp (-((T.stage k).coupling * (Tb.stepParameters y).κ₁ * (Tb.stepParameters y).threshold ^ 2 / 2 ^ 5))) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N] (nn : ℝ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
      N = 2 * (Tb.stepParameters y).side ^ e → IsLocalChainAbove Tb y T β k N nn x₀ →
      Measure.real (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
          chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        {u | ¬ IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ≤
        Real.exp (-(c * (couplingFlow (Tb.stepParameters y) β k).1)) := by
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y hy₀
  have hκ := hfit.κ₁_pos
  have hσ := hfit.σ_pos
  have hB : (0 : ℝ) < Tb.B := hfit.B_pos
  have hy1 : 1 ≤ y := hfit.y₁_ge
  have hch : 0 < Tb.gasRate := by
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate
    have h1 := hTb.cE_pos
    have h2 := hTb.κ_pos
    have h3 : 0 < Tb.threshold := hσ
    have h4 : 0 < Tb.κ₁ := hκ
    have : 0 < min Tb.cE (min (Tb.κ * Tb.threshold ^ 2) (Tb.κ₁ * Tb.threshold ^ 2)) :=
      lt_min h1 (lt_min (by positivity) (by positivity))
    positivity
  set kσ : ℝ := (Tb.stepParameters y).κ₁ * (Tb.stepParameters y).threshold ^ 2 / 2 ^ 5 with hkσ
  have hkσ0 : 0 < kσ := by positivity
  set c₂ : ℝ := min (kσ / 2) (7 * Tb.gasRate / 2) with hc₂
  have hc₂0 : 0 < c₂ := lt_min (by positivity) (by positivity)
  have hL0 : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hL2 : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  set Cp : ℝ := 3 ^ 4 + 2 * 3 ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 * 25 ^ 4 with hCp
  obtain ⟨x₀, hx₀⟩ := eventually_floor_bounds Tb.B (Tb.stepParameters y).side (Tb.stepParameters y).n₀ c₂ 0 Cp hc₂0
  refine ⟨c₂ / 2, x₀, by positivity, fun T β k e N _ nn o hNe hLoc => ?_⟩
  have hfloor := hLoc.floor_le
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hx₀ _ hfloor
  have hcut := hLoc.cutoff
  have hco := hLoc.measurable
  have hst := hLoc.onFamily
  have hyrun := hLoc.coupling_ge
  have hside := hLoc.side_ge
  revert o
  set x := (couplingFlow (Tb.stepParameters y) β k).1 with hxdef
  set M := chainDepth x with hMdef
  intro o
  have hx0 : 0 < x := lt_of_lt_of_le one_pos a1
  have hMl : (M : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (by positivity)
  have hβ : y ≤ β := hyrun 0 (Nat.zero_le _)
  have h0 := hwil β hβ
  have hmove : ∀ j ≤ k + 2 * M,
      |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 - (couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B :=
    fun j hj => abs_couplingFlow_succ_sub_le hret h0 fun i hi => hyrun i (hi.trans hj)
  have hband : ∀ i ≤ 2 * M, x / 2 ≤ (couplingFlow (Tb.stepParameters y) β (k + i)).1 ∧
      (couplingFlow (Tb.stepParameters y) β (k + i)).1 ≤ 2 * x := by
    intro i hi
    have h1 := abs_couplingFlow_add_sub_le (ℓ := Tb.stepParameters y) β k (k + 2 * M) hmove i (by omega)
    have h2 : (i : ℝ) ≤ 2 * M := by exact_mod_cast hi
    have h3 : 2 * Tb.B * i ≤ x / 2 := by
      have e1 : 2 * Tb.B * i ≤ 2 * Tb.B * (2 * M) := mul_le_mul_of_nonneg_left h2 (by positivity)
      have e2 : 4 * Tb.B * M ≤ 4 * Tb.B * Real.log x ^ 2 := mul_le_mul_of_nonneg_left hMl (by positivity)
      linarith
    have h4 := abs_le.mp (h1.trans h3)
    constructor <;> linarith [h4.1, h4.2]
  have hcoup : ∀ j ≤ k + 2 * M + 1, (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 :=
    hst.coupling_eq
  have hlev := stage_functional_eq T hst.startsAtWilson.functional_eq (K := k + 2 * M)
    fun j hj => hcoup j (by omega)
  have hstep : ∀ i < 2 * M, (T.stage (k + i)).toStepSetup.IsWellPosed ∧
      (T.stage (k + i)).nextCoupling ≤ 1.01 * (T.stage (k + i)).coupling := by
    intro i hi
    have hon := hst.onFamily (k + i) (by omega)
    have hxj : (T.stage (k + i)).coupling = (couplingFlow (Tb.stepParameters y) β (k + i)).1 := hcoup _ (by omega)
    have hxj' : (T.stage (k + i)).nextCoupling = (couplingFlow (Tb.stepParameters y) β (k + i + 1)).1 :=
      hcoup (k + i + 1) (by omega)
    have hmv : |(T.stage (k + i)).toStepSetup.nextCoupling - (T.stage (k + i)).toStepSetup.coupling| ≤ 2 * Tb.B := by
      show |(T.stage (k + i)).nextCoupling - (T.stage (k + i)).coupling| ≤ 2 * Tb.B
      rw [hxj, hxj']
      exact hmove _ (by omega)
    have hrow := hasExpansion_couplingFlow hret h0 (k + i) fun j hj => hyrun j (by omega)
    have hArr : (T.stage (k + i)).toStepSetup.IsSymmetricWeight := by
      intro n _ hn
      have := hrow.1 n hn
      show Measurable ((T.stage (k + i)).functional n) ∧ _
      have e := hlev (k + i) (by omega)
      simpa only [StepSetup.IsSymmetricWeight, e] using this
    have hF := hFl _ hon.le_coupling
    exact ⟨isWellPosed_of_onParameters hTb hy₀ hy1 hon hmv hArr hF, (hF.stable_nearby.2 _ hmv).2.1⟩
  have hstm : ∀ j ≤ k + 2 * M, IsTowerAtParameters Tb y T β j := fun j hj =>
    ⟨hst.startsAtWilson, fun i hi => hst.coupling_eq i (by omega), fun i hi => hst.onFamily i (by omega)⟩
  have hfloorN : 2 ^ 10 * ⌊x ^ ((1 : ℝ) / 20)⌋₊ ≤ N := by
    have h : (2 : ℝ) ^ 10 * (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ (N : ℝ) := hside
    exact_mod_cast h
  have hN : IsBlockTorusSide (Tb.stepParameters y) N := by
    have hge := a5.trans hfloorN
    refine ⟨?_, hge⟩
    rcases e with _ | e
    · exfalso
      have h1 := hfit.L_ge
      have h2 := hfit.n₀_ge
      rw [hNe] at hge
      have : 1 * 1 ≤ (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ := Nat.mul_le_mul (by omega) (by omega)
      have h3 : 2 ^ 16 * 4096 ≤ (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ := Nat.mul_le_mul h1 h2
      simp at hge
      omega
    · rw [hNe, pow_succ]
      exact ⟨2 * (Tb.stepParameters y).side ^ e, by ring⟩
  have hm0 : (0 : ℝ) ≤ localBoxRadius x := by
    unfold localBoxRadius
    positivity
  have hmx : 2 * (⌊localBoxRadius x⌋₊ : ℝ) + 1 ≤ 3 * x := by
    unfold localBoxRadius
    rw [Nat.floor_natCast]
    have h1 : (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ x ^ ((1 : ℝ) / 20) := Nat.floor_le (by positivity)
    have h2 : x ^ ((1 : ℝ) / 20) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le a1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hrx : ∀ z : ℝ, 1 ≤ z → z ≤ 2 * x → 8 * (clusterRange z : ℝ) + 1 ≤ 25 * x := by
    intro z h1 h2
    have h3 : (clusterRange z : ℝ) ≤ z ^ ((1 : ℝ) / 100) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h4 : z ^ ((1 : ℝ) / 100) ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_one] at h4
    linarith
  set b : ℝ := (3 * x) ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 * (25 * x) ^ 4 *
    Real.exp (-(c₂ * x)) with hbdef
  have hbound : ∀ j < M + M, ∀ (n' : ℕ) [NeZero n'], IsBlockTorusSide (Tb.stepParameters y) n' →
      ∀ o' : TorusSite n',
        (markedSampleLaw T β (k + j + 1) n').real {u | ¬ StepAvoids T (k + j) (localBoxRadius x) o' u} ≤ b := by
    intro j hj n' _ hb' o'
    have hj2 : j < 2 * M := by omega
    obtain ⟨hf, hx'⟩ := hstep j hj2
    refine (hFr T β (k + j) n' (hstm _ (by omega)) hcut hco hf hx' hb' (localBoxRadius x) o').trans ?_
    have hxj : (T.stage (k + j)).coupling = (couplingFlow (Tb.stepParameters y) β (k + j)).1 := hcoup _ (by omega)
    have hbd := hband j hj2.le
    have hyj : 1 ≤ (T.stage (k + j)).coupling := hy1.trans (hst.onFamily (k + j) (by omega)).le_coupling
    have hc1 := card_blocksNearFreeCores_le (Tb.stepParameters y).side (T.stage (k + j)).toStepSetup.range
      (supBall o' (localBoxRadius x))
    have hc2 := card_supBall_le o' hm0
    have hc3 : ((blocksNearFreeCores (Tb.stepParameters y).side (T.stage (k + j)).toStepSetup.range
        (supBall o' (localBoxRadius x))).card : ℝ) ≤
        (2 * (⌊localBoxRadius x⌋₊ : ℝ) + 1) ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 *
          (8 * (clusterRange (T.stage (k + j)).coupling : ℝ) + 1) ^ 4 := by
      have := hc1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc2))
      exact_mod_cast this
    have hr := hrx _ hyj (by rw [hxj]; exact hbd.2)
    have hc4 : ((blocksNearFreeCores (Tb.stepParameters y).side (T.stage (k + j)).toStepSetup.range
        (supBall o' (localBoxRadius x))).card : ℝ) ≤
        (3 * x) ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 * (25 * x) ^ 4 := by
      refine hc3.trans ?_
      gcongr
    have he : Real.exp (-(7 * Tb.gasRate * (T.stage (k + j)).coupling)) ≤ Real.exp (-(c₂ * x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : c₂ ≤ 7 * Tb.gasRate / 2 := min_le_right _ _
      rw [hxj]
      have h2 : 7 * Tb.gasRate * (x / 2) ≤ 7 * Tb.gasRate * (couplingFlow (Tb.stepParameters y) β (k + j)).1 :=
        mul_le_mul_of_nonneg_left hbd.1 (by positivity)
      have h3 : c₂ * x ≤ 7 * Tb.gasRate / 2 * x := mul_le_mul_of_nonneg_right h1 hx0.le
      linarith
    exact mul_le_mul hc4 he (Real.exp_pos _).le (by positivity)
  set t : ℝ := (3 * x) ^ 4 * Real.exp (-(c₂ * x)) with htdef
  have hkM : k + 2 * M = k + M + M := by omega
  have hbt := hband (2 * M) le_rfl
  rw [hkM] at hbt
  have hxt : (T.stage (k + M + M)).coupling = (couplingFlow (Tb.stepParameters y) β (k + M + M)).1 :=
    hcoup _ (by omega)
  have htop : (markedSampleLaw T β (k + M + M) N).real {u | ¬ Disjoint (stageState T (k + M + M) N u).2.1
      (supBall (siteAbove (Tb.stepParameters y).side M N
        (siteAbove (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N) o))
        (localBoxRadius x))} ≤ t := by
    have := isProbabilityMeasure_markedSampleLaw hfit hD T hcut hco β (k + M + M) N
    set Z := supBall (siteAbove (Tb.stepParameters y).side M N
      (siteAbove (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N) o))
      (localBoxRadius x) with hZ
    have hsub : {u : MarkedSample (Tb.stepParameters y) (k + M + M) N |
        ¬ Disjoint (stageState T (k + M + M) N u).2.1 Z} ⊆
        ⋃ v ∈ Z, {u | v ∈ (stageState T (k + M + M) N u).2.1} := by
      intro u hu
      obtain ⟨v, h1, h2⟩ := Finset.not_disjoint_iff.mp hu
      exact Set.mem_biUnion (Finset.mem_coe.mpr h2) h1
    have hrng1 : 1 ≤ clusterRange (T.stage (k + M + M)).coupling := by
      have : 0 < (T.stage (k + M + M)).coupling := by
        rw [hxt]
        linarith [hbt.1]
      exact Nat.ceil_pos.mpr (by positivity)
    have hrng2 : clusterRange (T.stage (k + M + M)).coupling ≤ ⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊ := by
      refine Nat.ceil_mono (Real.rpow_le_rpow ?_ ?_ (by norm_num))
      · rw [hxt]
        linarith [hbt.1]
      · rw [hxt]
        exact hbt.2
    have hcell : 2 * CellWindows.baseCellSide (Tb.stepParameters y).side
        (clusterRange (T.stage (k + M + M)).coupling) ≤ N := by
      have h1 := baseCellSide_le hL2 hrng1
      have h2 : (Tb.stepParameters y).side * (2 ^ 7 * clusterRange (T.stage (k + M + M)).coupling) ≤
          (Tb.stepParameters y).side * (2 ^ 7 * ⌈(2 * x) ^ ((1 : ℝ) / 100)⌉₊) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrng2)
      omega
    have hone := hHr T β (k + M + M) e N hNe (hstm _ (by omega)) hco hcell
    have hε : Real.exp (-((T.stage (k + M + M)).coupling * (Tb.stepParameters y).κ₁ *
        (Tb.stepParameters y).threshold ^ 2 / 2 ^ 5)) ≤ Real.exp (-(c₂ * x)) := by
      apply Real.exp_le_exp.mpr
      have h1 : c₂ ≤ kσ / 2 := min_le_left _ _
      have e1 : (T.stage (k + M + M)).coupling * (Tb.stepParameters y).κ₁ * (Tb.stepParameters y).threshold ^ 2 / 2 ^ 5 =
          kσ * (T.stage (k + M + M)).coupling := by
        rw [hkσ]
        ring
      rw [e1, hxt]
      have h2 : kσ * (x / 2) ≤ kσ * (couplingFlow (Tb.stepParameters y) β (k + M + M)).1 :=
        mul_le_mul_of_nonneg_left hbt.1 hkσ0.le
      have h3 : c₂ * x ≤ kσ / 2 * x := mul_le_mul_of_nonneg_right h1 hx0.le
      linarith
    have hcard : (Z.card : ℝ) ≤ (3 * x) ^ 4 := by
      have h1 := card_supBall_le (siteAbove (Tb.stepParameters y).side M N
        (siteAbove (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N) o)) hm0
      have h2 : (Z.card : ℝ) ≤ (2 * (⌊localBoxRadius x⌋₊ : ℝ) + 1) ^ 4 := by exact_mod_cast h1
      refine h2.trans ?_
      gcongr
    calc (markedSampleLaw T β (k + M + M) N).real {u | ¬ Disjoint (stageState T (k + M + M) N u).2.1 Z}
        ≤ (markedSampleLaw T β (k + M + M) N).real (⋃ v ∈ Z, {u | v ∈ (stageState T (k + M + M) N u).2.1}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ v ∈ Z, (markedSampleLaw T β (k + M + M) N).real {u | v ∈ (stageState T (k + M + M) N u).2.1} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ Z, Real.exp (-(c₂ * x)) := Finset.sum_le_sum fun v _ => (hone v).trans hε
      _ = (Z.card : ℝ) * Real.exp (-(c₂ * x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ t := mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
  refine (measureReal_not_isLocalEvent_le hfit hD T hcut hco β hL0 k M N hN (localBoxRadius x) b t o htop
    hbound).trans ?_
  have hMM : (M : ℝ) + M ≤ 2 * x := by linarith
  have hE : 0 < Real.exp (-(c₂ * x)) := Real.exp_pos _
  have hx4 : x ^ 4 ≤ x ^ 9 := pow_le_pow_right₀ a1 (by norm_num)
  have hsum : t + ((M : ℝ) + M) * b ≤ Cp * x ^ 9 * Real.exp (-(c₂ * x)) := by
    have h1 : ((M : ℝ) + M) * b ≤ 2 * x * b := mul_le_mul_of_nonneg_right hMM (by positivity)
    have e1 : t + 2 * x * b = (3 ^ 4 * x ^ 4 + 2 * 3 ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 *
        25 ^ 4 * x ^ 9) * Real.exp (-(c₂ * x)) := by
      rw [htdef, hbdef]
      ring
    have h2 : (3 ^ 4 * x ^ 4 + 2 * 3 ^ 4 * (2 * ((Tb.stepParameters y).side : ℝ) + 1) ^ 4 * 25 ^ 4 * x ^ 9) ≤
        Cp * x ^ 9 := by
      rw [hCp]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hE.le
    linarith
  refine hsum.trans ?_
  have h4 := mul_le_mul_of_nonneg_right a7 hE.le
  refine h4.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring
end Core
end LocalEventLikely
open LocalEventLikely in
theorem localEventLikely_holds (hFree : freeCoresRareStatement)
    (hHull : hullRareAtSiteStatement) (hD : forgetLastStepStatement)
    (hFl : StepFloors.EventuallyFloorConditions) : localEventLikelyStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, hF⟩ := hFree a ha
  obtain ⟨L₂, r₂, hr₂, hH⟩ := hHull a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), 0, fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hodd hL Tb h1 h2 hTb hCold hHalf hrt hC => ?_⟩
  obtain ⟨yF, hyF⟩ := hF L hodd ((le_max_left _ _).trans hL) Tb h1 h2 hTb (hrt.trans (min_le_left _ _))
  obtain ⟨yH, hyH⟩ := hH L hodd ((le_max_right _ _).trans hL) Tb h1 h2 hTb (hrt.trans (min_le_right _ _))
  obtain ⟨yL, hyL⟩ := hFl Tb hTb (2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨max (max yF yH) (max yL Tb.floorMin), fun y hy hret hwil => ?_⟩
  have e1 : yF ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have e2 : yH ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have e3 : yL ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have e4 : Tb.floorMin ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  exact measureReal_not_isLocalEvent_le_exp hD hTb e4 hret hwil (fun x hx => hyL x (e3.trans hx))
    (hyF y e1 hret hwil) (hyH y e2 hret hwil)
end YangMills.Construction.ResponseInTheExpansion
end
