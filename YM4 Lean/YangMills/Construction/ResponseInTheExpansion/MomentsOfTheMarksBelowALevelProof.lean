import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheMarksBelowALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.StepCosts
variable {ℓ : StepParameters}
private theorem sum_mul_sum_bond_ends {n : ℕ} [NeZero n] (f : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, f Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (f c.1 + f (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private def bondCoefficient (ℓ : StepParameters) (al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * al * (blockMean ℓ.side (s + 1) n c.1 h + blockMean ℓ.side (s + 1) n (c.1 + unitStep n c.2) h)
private theorem stepSourceTerm_eq_sum (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, bondCoefficient ℓ al s h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm bondCoefficient
  rw [sum_mul_sum_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y h)
    (fun c => bondScore ℓ x W d.2.1 d.1 c), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
private def weightCoefficients (ℓ : StepParameters) (al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → ScoreWeights ℓ m s n
  | 0, _, _, _ => ()
  | s + 1, n, _, h => (weightCoefficients ℓ al s (n * ℓ.side) h, fun i c => bondCoefficient ℓ (al s) s (h i) c)
private theorem initialField_forgetMarks (ℓ : StepParameters) : (s n : ℕ) → (u : MarkedSample ℓ s n) →
    initialField ℓ s n (forgetMarks ℓ s n u) = bottomField ℓ s n u
  | 0, _, _ => rfl
  | s + 1, n, u => initialField_forgetMarks ℓ s (n * ℓ.side) u.1
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem weightedScoreSum_forgetMarks (T : StageTower ℓ) (al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → (j : Fin m) → (u : MarkedSample ℓ s n) →
    weightedScoreSum ℓ (fun j => (T.stage j).coupling) s n (weightCoefficients ℓ al s n h) j (forgetMarks ℓ s n u) =
      cumulativeSource T al s n (h j) u
  | 0, _, _, _, _, _ => rfl
  | s + 1, n, _, h, j, u => by
    have ih := weightedScoreSum_forgetMarks T al s (n * ℓ.side) h j u.1
    show weightedScoreSum ℓ (fun j => (T.stage j).coupling) s (n * ℓ.side)
        (weightCoefficients ℓ al s (n * ℓ.side) h) j (forgetMarks ℓ s (n * ℓ.side) u.1) +
      ∑ c : TorusBond n, bondCoefficient ℓ (al s) s (h j) c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
          u.2.2.1 u.2.1 c =
      cumulativeSource T al s (n * ℓ.side) (h j) u.1 + sourceTerm T al s n (h j) u
    rw [ih, finalField_forgetMarks]
    congr 1
    exact (stepSourceTerm_eq_sum (T.stage s).coupling (al s) s (h j) (topField ℓ s (n * ℓ.side) u.1) u.2).symm
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
private theorem supDist_unitStep_le_one {n : ℕ} [NeZero n] (c : TorusBond n) :
    supDist c.1 (c.1 + unitStep n c.2) ≤ 1 := by apply _root_.YangMills.SharedProofs.p29700 <;> assumption
private theorem supDist_bond_ends_le_one {n : ℕ} [NeZero n] (c : TorusBond n) {y y' : TorusSite n}
    (hy : y = c.1 ∨ y = c.1 + unitStep n c.2) (hy' : y' = c.1 ∨ y' = c.1 + unitStep n c.2) :
    supDist y y' ≤ 1 := by
  rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
  · simp [supDist_self]
  · exact supDist_unitStep_le_one c
  · rw [supDist_comm]
    exact supDist_unitStep_le_one c
  · simp [supDist_self]
abbrev _root_.YangMills.SharedProofs.p28905 := @supDist_bond_ends_le_one
private theorem exists_end_of_coefficient_ne_zero (al : ℝ) (s n : ℕ) [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n)
    (hc : bondCoefficient ℓ al s h c ≠ 0) :
    ∃ y : TorusSite n, (y = c.1 ∨ y = c.1 + unitStep n c.2) ∧ blockMean ℓ.side (s + 1) n y h ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hc
  unfold bondCoefficient
  rw [hcon c.1 (Or.inl rfl), hcon _ (Or.inr rfl)]
  simp
private theorem weightCoefficients_disjoint {m : ℕ} (al : ℕ → ℝ) (x D : ℕ → ℝ) : ∀ (v : ℕ) (N : ℕ) [NeZero N]
    (h : Fin m → PlaquetteWeight (fineSide ℓ.side v N)), TransfersOffTheWalk.SeparatedAlongTower ℓ x D v N h →
      ScoreWeights.Disjoint v N (weightCoefficients ℓ al v N h) := by
  intro v
  induction v with
  | zero =>
    intro N _ _ _
    exact trivial
  | succ v ih =>
    intro N _ h hap
    obtain ⟨⟨-, h8, hs⟩, hrest⟩ := hap
    refine ⟨ih (N * ℓ.side) h hrest, ?_⟩
    intro c j j' hjj
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨y, hy, hyn⟩ := exists_end_of_coefficient_ne_zero _ _ _ _ c h1
    obtain ⟨y', hy', hyn'⟩ := exists_end_of_coefficient_ne_zero _ _ _ _ c h2
    have hA := mem_weightSupportSites_of_blockMean_ne_zero ℓ.side _ _ _ _ hyn
    have hA' := mem_weightSupportSites_of_blockMean_ne_zero ℓ.side _ _ _ _ hyn'
    have hle := hs j j' hjj y hA y' hA'
    have hn := supDist_bond_ends_le_one c hy hy'
    have hn' : (supDist y y' : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
private theorem measurable_finalField (ℓ : StepParameters) : (s n : ℕ) → Measurable (finalField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_snd.comp measurable_snd
private theorem measurable_initialField (ℓ : StepParameters) : (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
private theorem measurable_forgetMarks (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by apply _root_.YangMills.SharedProofs.p23598 <;> assumption
private theorem measurable_bondScore_outcome (hT : BondScoreProperties) (ℓ : StepParameters)
    (hfit : ℓ.Admissible) (y : ℝ) (s n : ℕ) [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by
  classical
  have hsum : (fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c) = fun u =>
      ∑ b : BaseChoice ℓ.side n, if u.2.1 = b then
        bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 b c else 0 := by
    funext u
    simp
  rw [hsum]
  refine Finset.measurable_sum _ fun b _ => ?_
  have hset : MeasurableSet
      {u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n | u.2.1 = b} :=
    (measurable_fst.comp measurable_snd) (show MeasurableSet ({b} : Set (BaseChoice ℓ.side n)) from trivial)
  have h1 : Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      (finalField ℓ s (n * ℓ.side) u.1, u.2.2) :=
    ((measurable_finalField ℓ s (n * ℓ.side)).comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have h2 := (hT ℓ hfit y n b c).2.2.2.2.comp h1
  exact Measurable.ite hset h2 measurable_const
abbrev _root_.YangMills.SharedProofs.p2216 := @measurable_bondScore_outcome
private theorem measurable_weightedScoreSum (hT : BondScoreProperties) (ℓ : StepParameters)
    (hfit : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      Measurable (weightedScoreSum ℓ x s n w i)
  | 0, _, _, _, _ => measurable_const
  | s + 1, n, _, w, i =>
    ((measurable_weightedScoreSum hT ℓ hfit x s (n * ℓ.side) w.1 i).comp measurable_fst).add
      (Finset.measurable_sum _ fun c _ =>
        (measurable_bondScore_outcome hT ℓ hfit (x s) s n c).const_mul (w.2 i c))
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
theorem separatedMarkedMoments (hS : ScoresPreserveCorrelations)
    (hT : TwoPointByTotalCovarianceStatement) (hSc : BondScoreProperties) :
    separatedMarkedMomentsStatement := by
  intro ℓ hf T hcut hcoin p t N _ β al κ x D h hap
  have hL := hf.depth_lt
  obtain ⟨hprob, hle, -, hchain, -, -⟩ := hT ℓ hf hL T hcut hcoin β al t N
  have hmw := measurable_forgetMarks (ℓ := ℓ) t N
  let w := weightCoefficients ℓ al t N h
  have hsep : ScoreWeights.Disjoint t N w := weightCoefficients_disjoint al x D t N h hap
  let X : Fin p → TorusField (fineSide ℓ.side t N) → ℝ := fun j => curvatureObservable (h j)
  have hXm : ∀ j, Measurable (X j) := fun j => (continuous_curvatureObservable (h j)).measurable
  have hXb : ∀ j, ∃ C : ℝ, ∀ W, |X j W| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ :=
      isCompact_univ.exists_bound_of_continuousOn (continuous_curvatureObservable (h j)).continuousOn
    exact ⟨C, fun W => by simpa using hC W (Set.mem_univ _)⟩
  have hmain := hS ℓ hf hL β (fun j => (T.stage j).coupling) t N p X w κ hXm hXb hsep
  have hxm : ∀ j, Measurable fun v : ChainSample ℓ t N => X j (initialField ℓ t _ v) := fun j =>
    (hXm j).comp (measurable_initialField ℓ _ _)
  have hF₀ : Measurable fun v : ChainSample ℓ t N => ∏ j, (X j (initialField ℓ t _ v) - κ j) :=
    Finset.measurable_fun_prod _ fun j _ => (hxm j).sub measurable_const
  have hF₁ : Measurable fun v : ChainSample ℓ t N =>
      ∏ j, (X j (initialField ℓ t _ v) +
        weightedScoreSum ℓ (fun j => (T.stage j).coupling) t _ w j v - κ j) :=
    Finset.measurable_fun_prod _ fun j _ =>
      ((hxm j).add (measurable_weightedScoreSum hSc ℓ hf _ t _ w j)).sub measurable_const
  have hl : ∫ u, ∏ i, (curvatureObservable (h i) (bottomField ℓ t N u) - κ i) ∂(markedSampleLaw T β t N) =
      ∫ v, ∏ j, (X j (initialField ℓ t _ v) - κ j)
        ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) t N) := by
    rw [← hchain, integral_map hmw.aemeasurable hF₀.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ∏ i, (curvatureObservable (h i) (bottomField ℓ t N u) - κ i) = _
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_forgetMarks]
  have hr : ∫ u, ∏ i, (completedObservable T al t N (h i) u - κ i) ∂(markedSampleLaw T β t N) =
      ∫ v, ∏ j, (X j (initialField ℓ t _ v) +
          weightedScoreSum ℓ (fun j => (T.stage j).coupling) t _ w j v - κ j)
        ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) t N) := by
    rw [← hchain, integral_map hmw.aemeasurable hF₁.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ∏ i, (completedObservable T al t N (h i) u - κ i) = _
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_forgetMarks, weightedScoreSum_forgetMarks T al t N h j u]
    rfl
  rw [hl, hr, hmain]
end YangMills.Construction.ResponseInTheExpansion
end
