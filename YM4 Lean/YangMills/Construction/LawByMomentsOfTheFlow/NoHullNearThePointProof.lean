import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.HullsInEveryVolume.ClassesOfAHullAreShort
import YangMills.Construction.LawByMomentsOfTheFlow.HullsClearOfThePointInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.NoHullNearThePoint
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem coupling_eq_flow {j : ℕ} (hj : j ≤ S.data.windowLevel + 1) :
    (S.tower.stage j).coupling = (TorusLumps.couplingFlow (Λ.table.stepParameters Λ.floor) S.β j).1 := by apply _root_.YangMills.SharedProofs.p30777 <;> assumption
private theorem hullChain (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) :
    HullTrees.HullChain Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower := by apply _root_.YangMills.SharedProofs.p4319 <;> assumption
private theorem levelSide_eq (u : ℕ) :
    S.levelSide u = HullTrees.torusSideAtLevel Λ.table.side S.data.windowLevel S.data.sideExponent u := by
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) =
    WeightedResponses.fineSide Λ.table.side (S.data.windowLevel - u) (2 * Λ.table.side ^ S.data.sideExponent)
  rw [WeightedResponses.fineSide_eq]
  rfl
private theorem levelSide_succ_mul {v : ℕ} (hv : v + 1 ≤ S.data.windowLevel) :
    S.levelSide (v + 1) * Λ.stepParams.side = S.levelSide v := by
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (v + 1)) * Λ.stepParams.side =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - v)
  have : S.data.windowLevel - v = S.data.windowLevel - (v + 1) + 1 := by omega
  rw [this, pow_succ]
  ring
end Point
private theorem card_supBall_le {n : ℕ} [NeZero n] (o : TorusFields.TorusSite n) (b : ℕ) :
    (ResponseInTheExpansion.supBall o (b : ℝ)).card ≤ (2 * b + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p9908 <;> assumption
private theorem hullDecayRate_pos {Tb : RenormalizationStepParameters.ParameterAssignment} (h : Tb.Admissible) :
    0 < HullTrees.hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p22298 <;> assumption
private theorem exists_threshold_count (b c : ℝ) (hb : 0 < b) :
    ∃ X : ℝ, ∀ x, X ≤ x → 1 ≤ x ∧ c * Real.log x ≤ x / 2 ∧
      (2 * (⌈4 * Real.log x⌉₊ : ℝ) + 5) * (2 * (TorusLumps.clusterRange x : ℝ) ^ 3 + 1) ^ 4 * Real.exp (-(b * x)) ≤ 1 := by apply _root_.YangMills.SharedProofs.p58793 <;> assumption
section Bounds
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem measure_hit_supBall_le (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹)
    (H : ∀ (g β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (Λ.table.stepParameters Λ.floor)) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor g β K m T u n → ∀ (z : TorusFields.TorusSite n) (D : ℝ), 0 ≤ D →
        (WeightedResponses.markedSampleLaw T β u n).real {w | z ∈ HullTrees.hullSet T u n w ∧
            D ≤ (HullTrees.supDiam (HullTrees.hullClass (HullTrees.stageRange T u)
              (HullTrees.hullSet T u n w) z) : ℝ)} ≤
          Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u *
            (1 + D / (HullTrees.stageRange T u : ℝ)))))
    (hprob : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (S.law s n))
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (n : ℕ) [NeZero n] (hn : n = S.levelSide u) (b : ℕ) :
    S.law u n {w | ¬ Disjoint (WeightedResponses.stageState S.tower u n w).2.1
        (ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ))} ≤
      ENNReal.ofReal ((2 * (b : ℝ) + 1) ^ 4 * Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u))) := by
  classical
  have hAt : HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u n :=
    ⟨hullChain S hg hy, hu, hn.trans (levelSide_eq S u)⟩
  have := hprob u n
  have hsite : ∀ z : TorusFields.TorusSite n, S.law u n {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1} ≤
      ENNReal.ofReal (Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u))) := by
    intro z
    have h := H Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u n hAt z 0 le_rfl
    have hc : HullTrees.stageCoupling S.tower u = S.coupling u := coupling_eq_flow S (by omega)
    have hset : {w | z ∈ HullTrees.hullSet S.tower u n w ∧
        (0 : ℝ) ≤ (HullTrees.supDiam (HullTrees.hullClass (HullTrees.stageRange S.tower u)
          (HullTrees.hullSet S.tower u n w) z) : ℝ)} = {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1} := by
      ext w
      simp [HullTrees.hullSet]
    rw [hset, hc] at h
    simp only [zero_div, add_zero, mul_one] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (S.law u n) {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1})]
    exact ENNReal.ofReal_le_ofReal h
  have hsub : {w | ¬ Disjoint (WeightedResponses.stageState S.tower u n w).2.1
      (ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ))} ⊆
      ⋃ z ∈ ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ),
        {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1} := by
    intro w hw
    obtain ⟨z, hz, hz'⟩ := Finset.not_disjoint_iff.1 hw
    exact Set.mem_biUnion (Finset.mem_coe.2 hz') hz
  have hcard : ((ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ)).card : ENNReal) ≤
      ENNReal.ofReal ((2 * (b : ℝ) + 1) ^ 4) := by
    have h := card_supBall_le (S.originSite u n) b
    have h' : (((ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ)).card : ℕ) : ℝ) ≤ (2 * (b : ℝ) + 1) ^ 4 := by
      exact_mod_cast h
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h'
  calc S.law u n {w | ¬ Disjoint (WeightedResponses.stageState S.tower u n w).2.1
          (ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ))}
      ≤ S.law u n (⋃ z ∈ ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ),
          {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1}) := measure_mono hsub
    _ ≤ ∑ z ∈ ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ),
          S.law u n {w | z ∈ (WeightedResponses.stageState S.tower u n w).2.1} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ),
          ENNReal.ofReal (Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u))) :=
        Finset.sum_le_sum fun z _ => hsite z
    _ = ((ResponseInTheExpansion.supBall (S.originSite u n) (b : ℝ)).card : ENNReal) *
          ENNReal.ofReal (Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((2 * (b : ℝ) + 1) ^ 4) *
          ENNReal.ofReal (Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u))) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
private theorem measure_not_noLumpNear_le
    (hmp : ∀ (s n : ℕ) [NeZero n], MeasurePreserving (fun w : WeightedResponses.MarkedSample Λ.stepParams (s + 1) n => w.1)
      (S.law (s + 1) n) (S.law s (n * Λ.stepParams.side)))
    (ρ : ℝ) (E : ENNReal) (v D : ℕ) (hK : v + D ≤ S.data.windowLevel)
    (hb : ∀ j ≤ D, ∀ (n : ℕ) [NeZero n], n = S.levelSide (v + j) →
      S.law (v + j) n {w | ¬ Disjoint (WeightedResponses.stageState S.tower (v + j) n w).2.1
        (ResponseInTheExpansion.supBall (S.originSite (v + j) n) ρ)} ≤ E) :
    ∀ d ≤ D, ∀ (n : ℕ) [NeZero n], n = S.levelSide (v + d) →
      S.law (v + d) n {w | ¬ S.NoLumpNear v ρ d n w} ≤ ((d : ENNReal) + 1) * E := by
  intro d
  induction d with
  | zero =>
    intro _ n _ hn
    have h := hb 0 (Nat.zero_le _) n hn
    calc S.law (v + 0) n {w | ¬ S.NoLumpNear v ρ 0 n w} ≤ E := h
      _ = (((0 : ℕ) : ENNReal) + 1) * E := by simp
  | succ d ih =>
    intro hd n _ hn
    have hnL : n * Λ.stepParams.side = S.levelSide (v + d) := by
      rw [hn]
      exact levelSide_succ_mul S (v := v + d) (by omega)
    have h1 := hb (d + 1) hd n hn
    have h2 := ih (by omega) (n * Λ.stepParams.side) hnL
    have mp := hmp (v + d) n
    have hsub : {w | ¬ S.NoLumpNear v ρ (d + 1) n w} ⊆
        {w | ¬ Disjoint (WeightedResponses.stageState S.tower (v + (d + 1)) n w).2.1
          (ResponseInTheExpansion.supBall (S.originSite (v + (d + 1)) n) ρ)} ∪
          (fun w : WeightedResponses.MarkedSample Λ.stepParams (v + d + 1) n => w.1) ⁻¹'
            {w | ¬ S.NoLumpNear v ρ d (n * Λ.stepParams.side) w} := by
      intro w hw
      by_cases hA : Disjoint (WeightedResponses.stageState S.tower (v + (d + 1)) n w).2.1
          (ResponseInTheExpansion.supBall (S.originSite (v + (d + 1)) n) ρ)
      · exact Or.inr fun hB => hw ⟨hA, hB⟩
      · exact Or.inl hA
    have hB : S.law (v + d + 1) n ((fun w : WeightedResponses.MarkedSample Λ.stepParams (v + d + 1) n => w.1) ⁻¹'
        {w | ¬ S.NoLumpNear v ρ d (n * Λ.stepParams.side) w}) ≤ ((d : ENNReal) + 1) * E := by
      refine (Measure.le_map_apply mp.measurable.aemeasurable _).trans ?_
      rw [mp.map_eq]
      exact h2
    calc S.law (v + (d + 1)) n {w | ¬ S.NoLumpNear v ρ (d + 1) n w}
        ≤ S.law (v + d + 1) n ({w | ¬ Disjoint (WeightedResponses.stageState S.tower (v + (d + 1)) n w).2.1
            (ResponseInTheExpansion.supBall (S.originSite (v + (d + 1)) n) ρ)} ∪
          (fun w : WeightedResponses.MarkedSample Λ.stepParams (v + d + 1) n => w.1) ⁻¹'
            {w | ¬ S.NoLumpNear v ρ d (n * Λ.stepParams.side) w}) := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ E + ((d : ENNReal) + 1) * E := add_le_add h1 hB
      _ = (((d + 1 : ℕ) : ENNReal) + 1) * E := by
          push_cast
          ring
private theorem bounds_at_point (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hDr : Λ.table.Admissible)
    (hfit : Λ.stepParams.Admissible)
    (hDraw : WeightedResponses.forgetLastStepStatement)
    (H : ∀ (g β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (Λ.table.stepParameters Λ.floor)) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor g β K m T u n → ∀ (z : TorusFields.TorusSite n) (D : ℝ), 0 ≤ D →
        (WeightedResponses.markedSampleLaw T β u n).real {w | z ∈ HullTrees.hullSet T u n w ∧
            D ≤ (HullTrees.supDiam (HullTrees.hullClass (HullTrees.stageRange T u)
              (HullTrees.hullSet T u n w) z) : ℝ)} ≤
          Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u *
            (1 + D / (HullTrees.stageRange T u : ℝ)))))
    (Cw : ℝ) (hwin : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel)
    (hx : ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      |S.coupling u - S.scaleCoupling| ≤ Cw * Real.log S.scaleCoupling)
    (hlog : Cw * Real.log S.scaleCoupling ≤ S.scaleCoupling / 2)
    (hcount : (2 * (S.logIndex : ℝ) + 5) * (2 * (S.range : ℝ) ^ 3 + 1) ^ 4 *
      Real.exp (-(HullTrees.hullDecayRate Λ.table / 4 * S.scaleCoupling)) ≤ 1) :
    (∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      S.law u (S.levelSide u) {w | ¬ Disjoint (S.state u (S.levelSide u) w).2.1
        (ResponseInTheExpansion.supBall (S.originSite u (S.levelSide u)) ((S.range : ℝ) ^ 3))} ≤
        ENNReal.ofReal (1 * Real.exp (-(HullTrees.hullDecayRate Λ.table / 4 * S.scaleCoupling)))) ∧
    ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u + d = S.lastSeparated + 2 * S.logIndex + 3 →
      n = S.levelSide (u + d) →
      S.law (u + d) n {w | ¬ S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w} ≤
        ENNReal.ofReal (1 * Real.exp (-(HullTrees.hullDecayRate Λ.table / 4 * S.scaleCoupling))) := by
  have hgt : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hDr.L_gt
  have hprob : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (S.law s n) := fun s n _ =>
    (hDraw _ hfit hgt S.tower S.isCutoff S.marksMeasurable S.β s n).1
  have hmp : ∀ (s n : ℕ) [NeZero n], MeasurePreserving (fun w : WeightedResponses.MarkedSample Λ.stepParams (s + 1) n => w.1)
      (S.law (s + 1) n) (S.law s (n * Λ.stepParams.side)) := fun s n _ =>
    (hDraw _ hfit hgt S.tower S.isCutoff S.marksMeasurable S.β s n).2
  have hc5 : 0 < HullTrees.hullDecayRate Λ.table := hullDecayRate_pos hDr
  set c5 := HullTrees.hullDecayRate Λ.table with hc5def
  set A : ℝ := (2 * (S.range : ℝ) ^ 3 + 1) ^ 4 with hA
  set Ec : ℝ := Real.exp (-(c5 / 4 * S.scaleCoupling)) with hEc
  have hA0 : 0 ≤ A := by positivity
  have hEc0 : 0 < Ec := Real.exp_pos _
  have hcast : ((S.range : ℝ) ^ 3) = ((S.range ^ 3 : ℕ) : ℝ) := by push_cast; rfl
  have hlevel : ∀ v, S.lastSeparated ≤ v → v ≤ S.lastSeparated + 2 * S.logIndex + 3 → ∀ (n : ℕ) [NeZero n],
      n = S.levelSide v →
      S.law v n {w | ¬ Disjoint (WeightedResponses.stageState S.tower v n w).2.1
        (ResponseInTheExpansion.supBall (S.originSite v n) ((S.range : ℝ) ^ 3))} ≤
        ENNReal.ofReal (A * (Ec * Ec)) := by
    intro v h1 h2 n _ hn
    have hb := measure_hit_supBall_le S hg hy H hprob (h2.trans hwin) n hn (S.range ^ 3)
    rw [← hcast] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hxv : S.scaleCoupling / 2 ≤ S.coupling v := by
      have := abs_le.1 ((hx v h1 h2).trans hlog)
      linarith [this.1]
    have hcc : Ec * Ec = Real.exp (-(c5 * (S.scaleCoupling / 2))) := by
      rw [hEc, ← Real.exp_add]
      congr 1
      ring
    rw [hcc]
    rw [← hA]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA0
    have := mul_le_mul_of_nonneg_left hxv hc5.le
    linarith
  have hsmall : ∀ e : ℝ, 0 ≤ e → e ≤ 2 * (S.logIndex : ℝ) + 5 → e * A * Ec ≤ 1 := by
    intro e he he'
    have : e * A * Ec ≤ (2 * (S.logIndex : ℝ) + 5) * A * Ec := by
      have := mul_le_mul_of_nonneg_right he' hA0
      exact mul_le_mul_of_nonneg_right this hEc0.le
    exact this.trans hcount
  refine ⟨fun u h1 h2 => ?_, fun u d n _ h1 h2 h3 => ?_⟩
  · refine (hlevel u h1 h2 _ rfl).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hsmall 1 zero_le_one (by have : (0 : ℝ) ≤ (S.logIndex : ℝ) := Nat.cast_nonneg _
                                     linarith)
    rw [one_mul]
    nlinarith
  · have hb : ∀ j ≤ d, ∀ (n : ℕ) [NeZero n], n = S.levelSide (u + j) →
        S.law (u + j) n {w | ¬ Disjoint (WeightedResponses.stageState S.tower (u + j) n w).2.1
          (ResponseInTheExpansion.supBall (S.originSite (u + j) n) ((S.range : ℝ) ^ 3))} ≤
          ENNReal.ofReal (A * (Ec * Ec)) := fun j hj n _ hn =>
      hlevel (u + j) (by omega) (by omega) n hn
    have h := measure_not_noLumpNear_le S hmp ((S.range : ℝ) ^ 3) _ u d (by omega) hb d le_rfl n h3
    refine h.trans ?_
    have hd1 : ((d : ENNReal) + 1) = ENNReal.ofReal ((d : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [hd1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdle : (d : ℝ) + 1 ≤ 2 * (S.logIndex : ℝ) + 5 := by
      have : d ≤ 2 * S.logIndex + 3 := by omega
      have : (d : ℝ) ≤ 2 * (S.logIndex : ℝ) + 3 := by exact_mod_cast this
      linarith
    have := hsmall ((d : ℝ) + 1) (by positivity) hdle
    rw [one_mul]
    calc ((d : ℝ) + 1) * (A * (Ec * Ec)) = (((d : ℝ) + 1) * A * Ec) * Ec := by ring
      _ ≤ 1 * Ec := mul_le_mul_of_nonneg_right this hEc0.le
      _ = Ec := one_mul _
end Bounds
theorem noLumpNearPoint (hH : HullTrees.hullClassDiameterTailStatement)
    (hW : scaleWindowStatement) (hR : WeightedResponses.responseReturnsStatement)
    (hDraw : WeightedResponses.forgetLastStepStatement) : noLumpNearPointStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hH a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hW a ha
  obtain ⟨L₃, r₃, hr₃, H₃⟩ := hR a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ C₂,
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hDr hCold hOn hrt hCd Kr hKr
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL2 : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL3 : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hrt1 : Tb.rt ≤ r₁ Tb.toChainParameters := hrt.trans (min_le_left _ _)
  have hrt2 : Tb.rt ≤ r₂ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt3 : Tb.rt ≤ r₃ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨M, H₁⟩ := H₁ L hodd hL1 Tb hTa hTL hDr hCold hOn hrt1 ((le_max_left _ _).trans hCd)
  obtain ⟨K', hM, hη, hN, hfit', Cs, y₃, hCs, hret⟩ := H₃ Tb hTa (hTL ▸ hL3) hDr hCold hOn hrt3 M
  obtain ⟨y₁, H₁⟩ := H₁ K' hM hη hN hfit' ⟨Cs, y₃, hCs, hret⟩
  obtain ⟨y₂, H₂⟩ := H₂ L hodd hL2 Tb hTa hTL hDr hCold hOn hrt2 ((le_max_right _ _).trans hCd) Kr hKr
  refine ⟨max y₁ (max y₂ Tb.floorMin), ?_⟩
  intro y hy hRet hRow g hg hgy k _ hk2 hk8 R d hd
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : Tb.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  obtain ⟨Cw, cw, Xw, _, _, Hw⟩ := H₂ y hy2 hRet hRow g hg hgy k hk2 hk8 R d hd
  have hc5 := hullDecayRate_pos hDr
  obtain ⟨X, hX⟩ := exists_threshold_count (HullTrees.hullDecayRate Tb / 4) (Cw 0) (by positivity)
  refine ⟨fun _ => 1, HullTrees.hullDecayRate Tb / 4, max X (max Xw y), by positivity,
    (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  intro S hXs
  have hXw : Xw ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hXs
  obtain ⟨_, _, _, _, _, hwin, hall⟩ := Hw S hXw
  obtain ⟨_, hlog, hcount⟩ := hX S.scaleCoupling ((le_max_left _ _).trans hXs)
  exact bounds_at_point (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) S hg hgy hDr (hDr.fits y hy3) hDraw (H₁ y hy1 hRet hRow) (Cw 0) hwin
    (fun u h1 h2 => (hall u h1 h2).1) hlog hcount
end YangMills.Construction.MomentLaw
end
