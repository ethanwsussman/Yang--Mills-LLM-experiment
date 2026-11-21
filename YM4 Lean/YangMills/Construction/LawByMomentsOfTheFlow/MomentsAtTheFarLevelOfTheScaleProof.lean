import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion ColdStepAtMirrorFrames LevelTestFunctions StepCosts
variable {ℓ : TorusLumps.StepParameters}
private theorem sum_mul_sum_bond_ends {n : ℕ} [NeZero n] (f : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, f Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (f c.1 + f (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private def scoreCoeff (ℓ : TorusLumps.StepParameters) (α : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (w : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * α * (blockMean ℓ.side (s + 1) n c.1 w + blockMean ℓ.side (s + 1) n (c.1 + unitStep n c.2) w)
private theorem stepSourceTerm_eq_sum (x α : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (w : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (U : TorusField (n * ℓ.side)) (o : StepOutcome ℓ n) :
    stepSourceTerm ℓ x α s w U o = ∑ c : TorusBond n, scoreCoeff ℓ α s w c * bondScore ℓ x U o.2.1 o.1 c := by
  unfold stepSourceTerm scoreCoeff
  rw [sum_mul_sum_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y w) (fun c => bondScore ℓ x U o.2.1 o.1 c),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
private def scoreWeightsOf (ℓ : TorusLumps.StepParameters) (α : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → ScoreWeights ℓ m s n
  | 0, _, _, _ => ()
  | s + 1, n, _, w => (scoreWeightsOf ℓ α s (n * ℓ.side) w, fun i c => scoreCoeff ℓ (α s) s (w i) c)
private theorem initialField_forgetMarks (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → (u : MarkedSample ℓ s n) →
    initialField ℓ s n (forgetMarks ℓ s n u) = bottomField ℓ s n u
  | 0, _, _ => rfl
  | s + 1, n, u => initialField_forgetMarks ℓ s (n * ℓ.side) u.1
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem weightedScoreSum_forgetMarks (T : StageTower ℓ) (α : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (w : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → (j : Fin m) → (u : MarkedSample ℓ s n) →
    weightedScoreSum ℓ (fun j => (T.stage j).coupling) s n (scoreWeightsOf ℓ α s n w) j (forgetMarks ℓ s n u) =
      cumulativeSource T α s n (w j) u
  | 0, _, _, _, _, _ => rfl
  | s + 1, n, _, w, j, u => by
    have ih := weightedScoreSum_forgetMarks T α s (n * ℓ.side) w j u.1
    show weightedScoreSum ℓ (fun j => (T.stage j).coupling) s (n * ℓ.side)
        (scoreWeightsOf ℓ α s (n * ℓ.side) w) j (forgetMarks ℓ s (n * ℓ.side) u.1) +
      ∑ c : TorusBond n, scoreCoeff ℓ (α s) s (w j) c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
          u.2.2.1 u.2.1 c =
      cumulativeSource T α s (n * ℓ.side) (w j) u.1 + sourceTerm T α s n (w j) u
    rw [ih, finalField_forgetMarks]
    congr 1
    exact (stepSourceTerm_eq_sum (T.stage s).coupling (α s) s (w j) (topField ℓ s (n * ℓ.side) u.1) u.2).symm
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n]
    (y : TorusSite n) (w : PlaquetteWeight (fineSide L t n)), blockMean L t n y w ≠ 0 →
    y ∈ weightSupportSites L t n w := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
private theorem supDist_bond_ends_le_one {n : ℕ} [NeZero n] (c : TorusBond n) {y y' : TorusSite n}
    (hy : y = c.1 ∨ y = c.1 + unitStep n c.2) (hy' : y' = c.1 ∨ y' = c.1 + unitStep n c.2) :
    TorusFields.supDist y y' ≤ 1 := by apply _root_.YangMills.SharedProofs.p28905 <;> assumption
private theorem exists_end_of_scoreCoeff_ne_zero (α : ℝ) (s n : ℕ) [NeZero n]
    (w : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) (hc : scoreCoeff ℓ α s w c ≠ 0) :
    ∃ y : TorusSite n, (y = c.1 ∨ y = c.1 + unitStep n c.2) ∧ blockMean ℓ.side (s + 1) n y w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hc
  unfold scoreCoeff
  rw [hcon c.1 (Or.inl rfl), hcon _ (Or.inr rfl)]
  simp
private theorem sideAt_succ_mul {k : ℕ} (P : LevelData k) (L v : ℕ) (hv : v + 1 ≤ P.windowLevel) :
    P.sideAt L (v + 1) * L = P.sideAt L v := by apply _root_.YangMills.SharedProofs.p32891 <;> assumption
private theorem scoreWeightsOf_disjoint {k m : ℕ} (P : LevelData k) (α : ℕ → ℝ) (idx : Fin m → Fin k)
    (hidx : Function.Injective idx) :
    ∀ (v : ℕ), v ≤ P.windowLevel → ∀ (N : ℕ) [NeZero N], N = P.sideAt ℓ.side v →
      (∀ u < v, 8 < P.separation ℓ.side u) →
      ScoreWeights.Disjoint v N
        (scoreWeightsOf ℓ α v N fun j => P.testWeight ℓ.side (idx j) (fineSide ℓ.side v N)) := by
  intro v
  induction v with
  | zero =>
    intro _ N _ _ _
    exact trivial
  | succ v ih =>
    intro hv N _ hN hsep
    refine ⟨ih (by omega) (N * ℓ.side) (by rw [hN]; exact sideAt_succ_mul P ℓ.side v hv)
      fun u hu => hsep u (by omega), ?_⟩
    intro c j j' hjj
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    subst hN
    obtain ⟨y, hy, hyn⟩ := exists_end_of_scoreCoeff_ne_zero _ _ _ _ c h1
    obtain ⟨y', hy', hyn'⟩ := exists_end_of_scoreCoeff_ne_zero _ _ _ _ c h2
    have hA := mem_weightSupportSites_of_blockMean_ne_zero ℓ.side _ _ _ _ hyn
    have hA' := mem_weightSupportSites_of_blockMean_ne_zero ℓ.side _ _ _ _ hyn'
    have hle : P.separation ℓ.side v ≤ TorusFields.supDist y y' := by
      refine Nat.sInf_le ⟨idx j, idx j', fun h => hjj (hidx h), y, ?_, y', ?_, rfl⟩
      · simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hA, by rw [TorusFields.supDist_self]; exact Nat.zero_le _⟩
      · simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y', hA', by rw [TorusFields.supDist_self]; exact Nat.zero_le _⟩
    have := supDist_bond_ends_le_one c hy hy'
    have h8 := hsep v (Nat.lt_succ_self v)
    omega
private theorem measurable_initialField (ℓ : TorusLumps.StepParameters) :
    (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
private theorem measurable_forgetMarks (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by apply _root_.YangMills.SharedProofs.p23598 <;> assumption
private theorem measurable_bondScore_sample (hB : BondScoreProperties) (ℓ : TorusLumps.StepParameters)
    (hadm : ℓ.Admissible) (y : ℝ) (s n : ℕ) [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by apply _root_.YangMills.SharedProofs.p2216 <;> assumption
private theorem measurable_weightedScoreSum (hB : BondScoreProperties) (ℓ : TorusLumps.StepParameters)
    (hadm : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      Measurable (weightedScoreSum ℓ x s n w i)
  | 0, _, _, _, _ => measurable_const
  | s + 1, n, _, w, i =>
    ((measurable_weightedScoreSum hB ℓ hadm x s (n * ℓ.side) w.1 i).comp measurable_fst).add
      (Finset.measurable_sum _ fun c _ =>
        (measurable_bondScore_sample hB ℓ hadm (x s) s n c).const_mul (w.2 i c))
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (w : PlaquetteWeight m) :
    Continuous (curvatureObservable w) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private theorem integral_prod_centered_eq (hS : ScoresPreserveCorrelations)
    (hT : TwoPointByTotalCovarianceStatement) (hB : BondScoreProperties) (ℓ : TorusLumps.StepParameters)
    (hf : ℓ.Admissible) (T : StageTower ℓ) (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn)
    (hmarks : T.MarksMeasurable) (k : ℕ) (P : LevelData k) (β : ℝ)
    (α : ℕ → ℝ) (κ : Fin k → ℝ) (B : Finset (Fin k)) (t : ℕ) (hKle : t ≤ P.windowLevel)
    (hsep : ∀ u < t, 8 < P.separation ℓ.side u) :
    ∫ u, ∏ i ∈ B, (curvatureObservable (P.testWeight ℓ.side i _) (bottomField ℓ t (P.sideAt ℓ.side t) u) - κ i)
        ∂(markedSampleLaw T β t (P.sideAt ℓ.side t)) =
      ∫ u, conditionalCenteredProduct T β α t (P.sideAt ℓ.side t) (fun i => P.testWeight ℓ.side i _) B κ u
        ∂(markedSampleLaw T β t (P.sideAt ℓ.side t)) := by
  have hL := hf.depth_lt
  obtain ⟨hprob, hle, -, hchain, -, -⟩ := hT ℓ hf hL T hcut hmarks β α t (P.sideAt ℓ.side t)
  have hmf := measurable_forgetMarks (ℓ := ℓ) t (P.sideAt ℓ.side t)
  let e : Fin B.card ≃ {i // i ∈ B} := B.equivFin.symm
  let idx : Fin B.card → Fin k := fun j => (e j).1
  have hidx : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
  let w : Fin B.card → PlaquetteWeight (fineSide ℓ.side t (P.sideAt ℓ.side t)) :=
    fun j => P.testWeight ℓ.side (idx j) _
  let sw := scoreWeightsOf ℓ α t (P.sideAt ℓ.side t) w
  have hdisj : ScoreWeights.Disjoint t (P.sideAt ℓ.side t) sw :=
    scoreWeightsOf_disjoint P α idx hidx t hKle _ rfl hsep
  let X : Fin B.card → TorusField (fineSide ℓ.side t (P.sideAt ℓ.side t)) → ℝ :=
    fun j => curvatureObservable (w j)
  have hXm : ∀ j, Measurable (X j) := fun j => (continuous_curvatureObservable (w j)).measurable
  have hXb : ∀ j, ∃ C : ℝ, ∀ U, |X j U| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ :=
      isCompact_univ.exists_bound_of_continuousOn (continuous_curvatureObservable (w j)).continuousOn
    exact ⟨C, fun U => by simpa using hC U (Set.mem_univ _)⟩
  have hmain := hS ℓ hf hL β (fun j => (T.stage j).coupling) t (P.sideAt ℓ.side t) B.card X sw
    (fun j => κ (idx j)) hXm hXb hdisj
  have hprod : ∀ g : Fin k → ℝ, ∏ i ∈ B, g i = ∏ j : Fin B.card, g (idx j) := by
    intro g
    rw [← Finset.prod_coe_sort B g]
    exact (Equiv.prod_comp e fun i : {i // i ∈ B} => g i.1).symm
  have hxm : ∀ j, Measurable fun v : ChainSample ℓ t (P.sideAt ℓ.side t) => X j (initialField ℓ t _ v) :=
    fun j => (hXm j).comp (measurable_initialField ℓ _ _)
  have hF₀ : Measurable fun v : ChainSample ℓ t (P.sideAt ℓ.side t) =>
      ∏ j, (X j (initialField ℓ t _ v) - κ (idx j)) :=
    Finset.measurable_fun_prod _ fun j _ => (hxm j).sub measurable_const
  have hF₁ : Measurable fun v : ChainSample ℓ t (P.sideAt ℓ.side t) =>
      ∏ j, (X j (initialField ℓ t _ v) +
        weightedScoreSum ℓ (fun j => (T.stage j).coupling) t _ sw j v - κ (idx j)) :=
    Finset.measurable_fun_prod _ fun j _ =>
      ((hxm j).add (measurable_weightedScoreSum hB ℓ hf _ t _ sw j)).sub measurable_const
  have hl : ∫ u, ∏ i ∈ B, (curvatureObservable (P.testWeight ℓ.side i _)
      (bottomField ℓ t (P.sideAt ℓ.side t) u) - κ i) ∂(markedSampleLaw T β t (P.sideAt ℓ.side t)) =
      ∫ v, ∏ j, (X j (initialField ℓ t _ v) - κ (idx j))
        ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) t (P.sideAt ℓ.side t)) := by
    rw [← hchain, integral_map hmf.aemeasurable hF₀.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ∏ i ∈ B, (curvatureObservable (P.testWeight ℓ.side i _)
      (bottomField ℓ t (P.sideAt ℓ.side t) u) - κ i) = _
    rw [hprod fun i => curvatureObservable (P.testWeight ℓ.side i _) (bottomField ℓ t (P.sideAt ℓ.side t) u) - κ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_forgetMarks]
  have hr : ∫ u, conditionalCenteredProduct T β α t (P.sideAt ℓ.side t) (fun i => P.testWeight ℓ.side i _) B κ u
      ∂(markedSampleLaw T β t (P.sideAt ℓ.side t)) =
      ∫ v, ∏ j, (X j (initialField ℓ t _ v) +
        weightedScoreSum ℓ (fun j => (T.stage j).coupling) t _ sw j v - κ (idx j))
        ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) t (P.sideAt ℓ.side t)) := by
    unfold conditionalCenteredProduct
    have := hprob
    rw [integral_condExp hle, ← hchain, integral_map hmf.aemeasurable hF₁.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ∏ i ∈ B, (WeightedResponses.completedObservable T α t (P.sideAt ℓ.side t) (P.testWeight ℓ.side i _) u - κ i) = _
    rw [hprod fun i => WeightedResponses.completedObservable T α t (P.sideAt ℓ.side t) (P.testWeight ℓ.side i _) u - κ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_forgetMarks, weightedScoreSum_forgetMarks T α t (P.sideAt ℓ.side t) w j u]
    rfl
  rw [hl, hr, hmain]
open Classical in
private theorem lastSeparated_facts {Λ : MomentParameters} (S : MomentPoint Λ) :
    S.lastSeparated ≤ S.data.windowLevel ∧ S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
  unfold MomentPoint.lastSeparated
  refine ⟨(Nat.findGreatest_le _).trans S.supAdmissible.scaleLevel_le,
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ?_⟩
  intro u hu
  exact absurd hu (Nat.not_lt_zero u)
theorem separatedLevelMomentsStatement_holds (hS : ScoresPreserveCorrelations)
    (hT : TwoPointByTotalCovarianceStatement) (hB : BondScoreProperties) :
    separatedLevelMomentsStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  refine ⟨Tb.floorMin, fun y hy _ _ g _ _ k _ _ _ R d _ => ?_⟩
  refine ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S B κ => ?_⟩
  obtain ⟨hKle, hsep⟩ := lastSeparated_facts S
  exact integral_prod_centered_eq hS hT hB _ (hD.fits y hy) S.tower S.isCutoff S.marksMeasurable k S.data
    S.β S.coeff κ B S.lastSeparated hKle fun u hu => (hsep u hu).2
end YangMills.Construction.MomentLaw
end
