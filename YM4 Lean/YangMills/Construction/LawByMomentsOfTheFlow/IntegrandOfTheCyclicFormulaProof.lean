import YangMills.Construction.LawByMomentsOfTheFlow.FactsOfAReflection
import YangMills.Construction.LawByMomentsOfTheFlow.IntegrandOfTheCyclicFormula
import YangMills.Construction.LawByMomentsOfTheFlow.TorusSumNearTheLatticeNumberProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CyclicFormula
private theorem self_ne_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by apply _root_.YangMills.SharedProofs.p48899 <;> assumption
private def EntrywiseMeasurable {X : Type} [MeasurableSpace X] (F : X → Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ a b, Measurable fun x => F x a b
private theorem EntrywiseMeasurable.mul {X : Type} [MeasurableSpace X] {F G : X → Matrix (Fin 4) (Fin 4) ℝ}
    (hF : EntrywiseMeasurable F) (hG : EntrywiseMeasurable G) : EntrywiseMeasurable fun x => F x * G x := by
  intro a b
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun e _ => (hF a e).mul (hG e b)
private theorem entrywiseMeasurable_list_prod {X : Type} [MeasurableSpace X] :
    ∀ (n : ℕ) (f : Fin n → X → Matrix (Fin 4) (Fin 4) ℝ),
    (∀ c, EntrywiseMeasurable (f c)) → EntrywiseMeasurable fun x => (List.ofFn fun c => f c x).prod := by
  intro n
  induction n with
  | zero =>
    intro f _ a b
    simp only [List.ofFn_zero, List.prod_nil]
    exact measurable_const
  | succ n ih =>
    intro f hf
    simp only [List.ofFn_succ, List.prod_cons]
    exact EntrywiseMeasurable.mul (hf 0) (ih _ fun c => hf c.succ)
private theorem measurable_coordinate (a : Fin 4) : Measurable fun x : TestFunctions.EuclideanFourSpace => x a :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.measurable
private theorem entrywiseMeasurable_inversionMatrix {X : Type} [MeasurableSpace X]
    (v : X → TestFunctions.EuclideanFourSpace) (hv : Measurable v) :
    EntrywiseMeasurable fun x => inversionMatrix (v x) := by
  intro a b
  simp only [inversionMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  refine measurable_const.sub ?_
  refine ((measurable_const.div (hv.norm.pow_const 2))).mul
    (((measurable_coordinate a).comp hv).mul ((measurable_coordinate b).comp hv))
private theorem measurable_exteriorSquareTrace {X : Type} [MeasurableSpace X] {F : X → Matrix (Fin 4) (Fin 4) ℝ}
    (hF : EntrywiseMeasurable F) : Measurable fun x => exteriorSquareTrace (F x) := by
  simp only [exteriorSquareTrace, Matrix.trace, Matrix.diag, exteriorSquareMap]
  exact Finset.measurable_sum _ fun p _ => ((hF _ _).mul (hF _ _)).sub ((hF _ _).mul (hF _ _))
private theorem list_prod_mul_transpose
    (hT : ∀ x : TestFunctions.EuclideanFourSpace, (inversionMatrix x).transpose = inversionMatrix x)
    (hI : ∀ x : TestFunctions.EuclideanFourSpace, inversionMatrix x * inversionMatrix x = 1) :
    ∀ l : List (Matrix (Fin 4) (Fin 4) ℝ), (∀ A ∈ l, A * A.transpose = 1) → l.prod * l.prod.transpose = 1 := by
  intro l
  induction l with
  | nil => simp
  | cons A t ih =>
    intro h
    have h1 := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
    simp only [List.prod_cons, Matrix.transpose_mul]
    calc A * t.prod * (t.prod.transpose * A.transpose)
        = A * (t.prod * t.prod.transpose) * A.transpose := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one]; exact h A List.mem_cons_self
private theorem abs_entry_le_one (A : Matrix (Fin 4) (Fin 4) ℝ) (h : A * A.transpose = 1) (a b : Fin 4) :
    |A a b| ≤ 1 := by
  have h1 : ∑ e, A a e * A a e = 1 := by
    have := congrFun (congrFun h a) a
    simpa [Matrix.mul_apply] using this
  have h2 : A a b * A a b ≤ ∑ e, A a e * A a e :=
    Finset.single_le_sum (f := fun e => A a e * A a e) (fun e _ => mul_self_nonneg _) (Finset.mem_univ b)
  rw [h1] at h2
  exact abs_le_one_iff_mul_self_le_one.mpr h2
private theorem abs_exteriorSquareTrace_le (A : Matrix (Fin 4) (Fin 4) ℝ) (h : A * A.transpose = 1) :
    |exteriorSquareTrace A| ≤ ∑ _p : OrderedDirectionPair, (2 : ℝ) := by
  simp only [exteriorSquareTrace, Matrix.trace, Matrix.diag, exteriorSquareMap]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have h1 := abs_entry_le_one A h p.1.1 p.1.1
  have h2 := abs_entry_le_one A h p.1.2 p.1.2
  have h3 := abs_entry_le_one A h p.1.1 p.1.2
  have h4 := abs_entry_le_one A h p.1.2 p.1.1
  have h5 : |A p.1.1 p.1.1 * A p.1.2 p.1.2| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ h1 (abs_nonneg _) h2
  have h6 : |A p.1.1 p.1.2 * A p.1.2 p.1.1| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ h3 (abs_nonneg _) h4
  calc |A p.1.1 p.1.1 * A p.1.2 p.1.2 - A p.1.1 p.1.2 * A p.1.2 p.1.1|
      ≤ |A p.1.1 p.1.1 * A p.1.2 p.1.2| + |A p.1.1 p.1.2 * A p.1.2 p.1.1| := abs_sub _ _
    _ ≤ 2 := by linarith
theorem cycleIntegrand_integrable (hF : InversionMatrixProperties) :
    CycleIntegrandIntegrable := by
  obtain ⟨hT, hI, -, -, -, -, -⟩ := hF
  intro n _ hn R d φ hd hTF σ
  have hpi : 0 < Real.pi ^ 2 * d ^ 4 := by positivity
  set S : Set (Fin n → TestFunctions.EuclideanFourSpace) := Set.pi Set.univ fun _ => Metric.closedBall 0 R with hS
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 R
  have hSm : MeasurableSet S := hSc.measurableSet
  set M : ℝ := ((Real.pi ^ 2 * d ^ 4)⁻¹) ^ n * ∑ _p : OrderedDirectionPair, (2 : ℝ) with hM
  have hM0 : 0 ≤ M := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by norm_num)
  have hv : ∀ c : Fin n, Measurable fun x : Fin n → TestFunctions.EuclideanFourSpace => x (σ c) - x (σ (c + 1)) :=
    fun c => (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hmeas : Measurable fun x : Fin n → TestFunctions.EuclideanFourSpace => (∏ i, φ i (x i)) * cycleKernel σ x := by
    simp only [cycleKernel]
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact Finset.measurable_fun_prod _ fun i _ =>
        (hTF.lipschitzWith_one i).continuous.measurable.comp (measurable_pi_apply i)
    · exact Finset.measurable_fun_prod _ fun c _ =>
        (measurable_const.mul ((hv c).norm.pow_const 4)).inv
    · exact measurable_exteriorSquareTrace
        (entrywiseMeasurable_list_prod n _ fun c => entrywiseMeasurable_inversionMatrix _ (hv c))
  have hb : ∀ x, ‖(∏ i, φ i (x i)) * cycleKernel σ x‖ ≤ S.indicator (fun _ => M) x := by
    intro x
    by_cases hp : ∏ i, φ i (x i) = 0
    · rw [hp, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hM0) x
    have hall : ∀ i, φ i (x i) ≠ 0 := fun i h => hp (Finset.prod_eq_zero (Finset.mem_univ i) h)
    have hxS : x ∈ S := fun i _ => hTF.tsupport_subset_closedBall i (subset_tsupport _ (hall i))
    rw [Set.indicator_of_mem hxS, Real.norm_eq_abs, abs_mul]
    have h1 : |∏ i, φ i (x i)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => hTF.abs_le_one i _
    have hdist : ∀ c : Fin n, d ≤ ‖x (σ c) - x (σ (c + 1))‖ := by
      intro c
      have hneq : σ c ≠ σ (c + 1) := fun h' => self_ne_add_one hn c (σ.injective h')
      have h3 := hTF.le_dist_of_ne _ _ hneq (x (σ c)) (subset_tsupport _ (hall _)) (x (σ (c + 1)))
        (subset_tsupport _ (hall _))
      rwa [dist_eq_norm] at h3
    have h2 : |∏ c : Fin n, (Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹| ≤
        ((Real.pi ^ 2 * d ^ 4)⁻¹) ^ n := by
      rw [Finset.abs_prod]
      calc ∏ c : Fin n, |(Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹|
          ≤ ∏ _c : Fin n, (Real.pi ^ 2 * d ^ 4)⁻¹ := by
            refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun c _ => ?_
            rw [abs_of_nonneg (by positivity)]
            refine inv_anti₀ hpi ?_
            have := pow_le_pow_left₀ hd.le (hdist c) 4
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = ((Real.pi ^ 2 * d ^ 4)⁻¹) ^ n := by simp
    have h3 : |exteriorSquareTrace (List.ofFn fun c : Fin n => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod| ≤
        ∑ _p : OrderedDirectionPair, (2 : ℝ) := by
      refine abs_exteriorSquareTrace_le _ (list_prod_mul_transpose hT hI _ fun A hA => ?_)
      obtain ⟨c, rfl⟩ := (List.mem_ofFn' _ _).mp hA
      rw [hT, hI]
    simp only [cycleKernel]
    rw [abs_mul]
    calc |∏ i, φ i (x i)| * (|∏ c : Fin n, (Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹| *
          |exteriorSquareTrace (List.ofFn fun c : Fin n => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod|)
        ≤ 1 * (((Real.pi ^ 2 * d ^ 4)⁻¹) ^ n * ∑ _p : OrderedDirectionPair, (2 : ℝ)) := by
          refine mul_le_mul h1 ?_ (by positivity) zero_le_one
          exact mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
      _ = M := one_mul _
  have hg : Integrable (S.indicator fun _ => M) :=
    (integrable_indicator_iff hSm).mpr (integrableOn_const hSc.measure_lt_top.ne)
  exact hg.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hb)
end YangMills.Construction.CyclicFormula
end
