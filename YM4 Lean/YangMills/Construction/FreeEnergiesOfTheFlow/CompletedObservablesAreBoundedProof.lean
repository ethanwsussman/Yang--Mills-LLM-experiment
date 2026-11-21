import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps StepCosts WeightedResponses StepSettings
section Samples
variable {ℓ : StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_outcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by
  have h1 : Measurable fun z : (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n) =>
      f (z.2.1, (z.1.1, z.2.2, z.1.2)) :=
    measurable_from_prod_countable_right fun x => h x.1 x.2
  have h2 : Measurable fun u : X × StepOutcome ℓ n =>
      (((u.2.1, u.2.2.2), (u.1, u.2.2.1)) :
        (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact h1.comp h2
abbrev _root_.YangMills.SharedProofs.p21057 := @measurable_of_outcome
private theorem sum_over_bond_ends {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private def bondSourceCoeff (ℓ : StepParameters) (al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * al * (blockMean ℓ.side (s + 1) n c.1 h + blockMean ℓ.side (s + 1) n (c.1 + unitStep n c.2) h)
private theorem stepSourceTerm_eq_sum (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, bondSourceCoeff ℓ al s h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm bondSourceCoeff
  rw [sum_over_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y h)
    (fun c => bondScore ℓ x W d.2.1 d.1 c), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
private theorem measurable_stepSourceTerm (hSc : BondScoreProperties) (hf : ℓ.Admissible) (x al : ℝ) (s : ℕ)
    {n : ℕ} [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    Measurable fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepSourceTerm ℓ x al s h p.1 p.2 := by
  refine measurable_of_outcome fun b bad => ?_
  have e : (fun p : TorusField (n * ℓ.side) × TorusField n => stepSourceTerm ℓ x al s h p.1 (b, p.2, bad)) =
      fun p => ∑ c : TorusBond n, bondSourceCoeff ℓ al s h c * bondScore ℓ x p.1 p.2 b c := by
    funext p
    exact stepSourceTerm_eq_sum x al s h p.1 (b, p.2, bad)
  rw [e]
  exact Finset.measurable_sum _ fun c _ => ((hSc ℓ hf x n b c).2.2.2.2).const_mul _
private theorem abs_stepSourceTerm_le (hSc : BondScoreProperties) (hf : ℓ.Admissible) (x al : ℝ) (s : ℕ)
    {n : ℕ} [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    |stepSourceTerm ℓ x al s h W d| ≤ ∑ c : TorusBond n, |bondSourceCoeff ℓ al s h c| * 2 := by
  rw [stepSourceTerm_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hSc ℓ hf x n d.1 c).2.2.1 W d.2.1) (abs_nonneg _)
private theorem measurable_topField_succ (s n : ℕ) :
    Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1 :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by
  cases s with
  | zero => exact measurable_id
  | succ s => exact measurable_topField_succ s n
abbrev _root_.YangMills.SharedProofs.p12845 := @measurable_topField
private theorem measurable_bottomField (s : ℕ) : ∀ n : ℕ, Measurable (bottomField ℓ s n) := by apply _root_.YangMills.SharedProofs.p4086 <;> assumption
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private theorem sourceTerm_measurable_bounded (hSc : BondScoreProperties) (hf : ℓ.Admissible) (T : StageTower ℓ)
    (al : ℕ → ℝ) (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    Measurable (sourceTerm T al s n h) ∧ ∃ C : ℝ, ∀ u, |sourceTerm T al s n h u| ≤ C := by
  refine ⟨?_, _, fun u => abs_stepSourceTerm_le hSc hf (T.stage s).coupling (al s) s h _ _⟩
  have h1 := measurable_stepSourceTerm hSc hf (T.stage s).coupling (al s) s (n := n) h
  have h2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
  have h3 := h1.comp h2
  exact h3
private theorem cumulativeSource_measurable_bounded (hSc : BondScoreProperties) (hf : ℓ.Admissible)
    (T : StageTower ℓ) (al : ℕ → ℝ) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      Measurable (cumulativeSource T al s n h) ∧ ∃ C : ℝ, ∀ u, |cumulativeSource T al s n h u| ≤ C := by
  induction s with
  | zero =>
    intro n _ h
    exact ⟨measurable_const, 0, fun _ => by simp [cumulativeSource]⟩
  | succ s ih =>
    intro n _ h
    obtain ⟨hm1, C₁, hC₁⟩ := ih (n * ℓ.side) h
    obtain ⟨hm2, C₂, hC₂⟩ := sourceTerm_measurable_bounded hSc hf T al s n h
    have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        cumulativeSource T al s (n * ℓ.side) h u.1 :=
      hm1.comp measurable_fst
    refine ⟨?_, C₁ + C₂, fun u => ?_⟩
    · have h3 := hm.add hm2
      exact h3
    · show |cumulativeSource T al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u| ≤ _
      exact (abs_add_le _ _).trans (add_le_add (hC₁ _) (hC₂ _))
end Samples
theorem completedObservablesBounded_holds (hSc : BondScoreProperties) : completedObservablesBounded := by
  intro ℓ hf T al s n _
  refine ⟨fun h => ?_, fun h => sourceTerm_measurable_bounded hSc hf T al s n h,
    fun x a h => measurable_stepSourceTerm hSc hf x a s h⟩
  obtain ⟨hm, C, hC⟩ := cumulativeSource_measurable_bounded hSc hf T al s n h
  have hc := continuous_curvatureObservable h
  obtain ⟨C', hC'⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨(hc.measurable.comp (measurable_bottomField s n)).add hm, C' + C, fun u => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add ?_ (hC u))
  have := hC' (bottomField ℓ s n u) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this
end YangMills.Construction.FreeEnergies
end
