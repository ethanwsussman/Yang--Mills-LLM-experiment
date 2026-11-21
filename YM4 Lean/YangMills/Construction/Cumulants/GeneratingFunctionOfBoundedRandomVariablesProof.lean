import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Cumulants.GeneratingFunctionIsEntireWithItsPrincipalLogarithm
import YangMills.Construction.Cumulants.GeneratingFunctionOfBoundedRandomVariables
import YangMills.Construction.Cumulants.HolomorphicLogsOfMomentGeneratingFunction
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.BoundedVariables
open YangMills.Construction.Coordinates
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.ComplexVariables (IsHolomorphicScalar partialDeriv iteratedPartials diffQuot
  HasIteratedPartials HasPartialDeriv partialOverFinset)
open YangMills.Construction.Cumulants.TupleLogMGF (iteratedRealPartial HasIteratedRealPartial)
set_option linter.unusedSectionVars false
variable {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
private theorem continuousOn_of_isHolomorphicScalar_aux {U : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar U F) : ContinuousOn F U :=
  (continuous_apply (0 : Fin 1)).comp_continuousOn hF.2.1
private theorem sum_add_smul_stdBasisVector (t : ComplexCoordinates n) (ζ : ℂ) (j : Fin n)
    (c : Fin n → ℂ) :
    ∑ i, (t + ζ • ComplexCoordinates.stdBasisVector j) i * c i = ∑ i, t i * c i + ζ * c j := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  simp [ComplexCoordinates.stdBasisVector, Pi.single_apply]
private theorem measurable_expLinearCombination_aux {X : Fin n → Ω → ℝ}
    (hX : ∀ i, IsBoundedRealRV (X i)) (t : ComplexCoordinates n) :
    Measurable (expLinearCombination X t) :=
  Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (Complex.measurable_ofReal.comp (hX i).measurable))
private theorem norm_expLinearCombination_le_aux {X : Fin n → Ω → ℝ} {B : ℝ}
    (hB : ∀ i ω, |X i ω| ≤ B) (t : ComplexCoordinates n) (ω : Ω) :
    ‖expLinearCombination X t ω‖ ≤ Real.exp (B * ∑ i, ‖t i‖) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB i ω) (norm_nonneg _)
private def weightedMGF (μ : Measure Ω) (X : Fin n → Ω → ℝ) (Y : Ω → ℂ)
    (t : ComplexCoordinates n) : ℂ :=
  ∫ ω, Y ω * expLinearCombination X t ω ∂μ
private theorem hasDerivAt_weightedMGF_line (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, IsBoundedRealRV (X i)) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ i ω, |X i ω| ≤ B) {Y : Ω → ℂ} (hY : Measurable Y) {C : ℝ} (hC : ∀ ω, ‖Y ω‖ ≤ C)
    (t : ComplexCoordinates n) (j : Fin n) :
    HasDerivAt (fun ζ : ℂ => weightedMGF μ X Y (t + ζ • ComplexCoordinates.stdBasisVector j))
      (weightedMGF μ X (fun ω => Y ω * (X j ω : ℂ)) t) 0 := by
  have hXj : Measurable fun ω => (X j ω : ℂ) :=
    Complex.measurable_ofReal.comp (hX j).measurable
  have hC0 : 0 ≤ C := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
    exact (norm_nonneg _).trans (hC ω)
  let F : ℂ → Ω → ℂ := fun ζ ω =>
    Y ω * expLinearCombination X (t + ζ • ComplexCoordinates.stdBasisVector j) ω
  let F' : ℂ → Ω → ℂ := fun ζ ω =>
    Y ω * (X j ω : ℂ) * expLinearCombination X (t + ζ • ComplexCoordinates.stdBasisVector j) ω
  have hFm : ∀ ζ, Measurable (F ζ) := fun ζ => hY.mul (measurable_expLinearCombination_aux hX _)
  have hF'm : ∀ ζ, Measurable (F' ζ) := fun ζ =>
    (hY.mul hXj).mul (measurable_expLinearCombination_aux hX _)
  have hsum : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      ∑ i, ‖(t + ζ • ComplexCoordinates.stdBasisVector j) i‖ ≤ ∑ i, ‖t i‖ + n := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ 1 := by
      have := Metric.mem_ball.1 hζ
      simpa using this.le
    calc ∑ i, ‖(t + ζ • ComplexCoordinates.stdBasisVector j) i‖ ≤ ∑ i : Fin n, (‖t i‖ + 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          by_cases hij : i = j
          · subst hij
            simpa [ComplexCoordinates.stdBasisVector] using hζ'
          · simp [ComplexCoordinates.stdBasisVector, hij]
      _ = ∑ i, ‖t i‖ + n := by simp [Finset.sum_add_distrib]
  have hbound : ∀ ω, ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      ‖F' ζ ω‖ ≤ C * B * Real.exp (B * (∑ i, ‖t i‖ + n)) := by
    intro ω ζ hζ
    have h1 : ‖expLinearCombination X (t + ζ • ComplexCoordinates.stdBasisVector j) ω‖ ≤
        Real.exp (B * (∑ i, ‖t i‖ + n)) :=
      (norm_expLinearCombination_le_aux hB _ ω).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hsum ζ hζ) hB0.le))
    have h2 : ‖(X j ω : ℂ)‖ ≤ B := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hB j ω
    simp only [F', norm_mul]
    exact mul_le_mul (mul_le_mul (hC ω) h2 (norm_nonneg _) hC0) h1 (norm_nonneg _)
      (mul_nonneg hC0 hB0.le)
  have hFint : Integrable (F 0) μ := by
    refine Integrable.of_bound (hFm 0).aestronglyMeasurable
      (C * Real.exp (B * ∑ i, ‖(t + (0 : ℂ) • ComplexCoordinates.stdBasisVector j) i‖)) ?_
    refine Eventually.of_forall fun ω => ?_
    simp only [F, norm_mul]
    exact mul_le_mul (hC ω) (norm_expLinearCombination_le_aux hB _ ω) (norm_nonneg _) hC0
  have hdiff : ∀ ω, ∀ ζ ∈ Metric.ball (0 : ℂ) 1, HasDerivAt (F · ω) (F' ζ ω) ζ := by
    intro ω ζ _
    have hfun : (F · ω) = fun ζ : ℂ =>
        Y ω * Complex.exp (∑ i, t i * (X i ω : ℂ) + ζ * (X j ω : ℂ)) := by
      funext ζ'
      simp only [F, expLinearCombination]
      rw [sum_add_smul_stdBasisVector t ζ' j fun i => (X i ω : ℂ)]
    have hval : F' ζ ω = Y ω * (Complex.exp (∑ i, t i * (X i ω : ℂ) + ζ * (X j ω : ℂ)) *
        (1 * (X j ω : ℂ))) := by
      simp only [F', expLinearCombination]
      rw [sum_add_smul_stdBasisVector t ζ j fun i => (X i ω : ℂ)]
      ring
    rw [hfun, hval]
    exact ((((hasDerivAt_id ζ).mul_const (X j ω : ℂ)).const_add _).cexp).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball (0 : ℂ) 1)
    (bound := fun _ => C * B * Real.exp (B * (∑ i, ‖t i‖ + n)))
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun ζ => (hFm ζ).aestronglyMeasurable) hFint
    (hF'm 0).aestronglyMeasurable (Eventually.of_forall hbound) (integrable_const _)
    (Eventually.of_forall hdiff)
  have hgoal := key.2
  have hF0 : (fun a => F' 0 a) = fun ω =>
      Y ω * (X j ω : ℂ) * expLinearCombination X t ω := by
    funext ω
    simp [F']
  simp only [hF0] at hgoal
  exact hgoal
private def monomialOfList (X : Fin n → Ω → ℝ) (l : List (Fin n)) : Ω → ℂ :=
  fun ω => (l.map fun a => (X a ω : ℂ)).prod
private theorem measurable_monomialOfList {X : Fin n → Ω → ℝ}
    (hX : ∀ i, IsBoundedRealRV (X i)) (l : List (Fin n)) :
    Measurable (monomialOfList X l) := by
  induction l with
  | nil =>
    have : monomialOfList X [] = fun _ => 1 := by
      funext ω
      simp [monomialOfList]
    rw [this]
    exact measurable_const
  | cons a l ih =>
    have : monomialOfList X (a :: l) = fun ω => (X a ω : ℂ) * monomialOfList X l ω := by
      funext ω
      simp [monomialOfList]
    rw [this]
    exact (Complex.measurable_ofReal.comp (hX a).measurable).mul ih
private theorem norm_monomialOfList_le {X : Fin n → Ω → ℝ} {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ i ω, |X i ω| ≤ B) (l : List (Fin n)) (ω : Ω) :
    ‖monomialOfList X l ω‖ ≤ B ^ l.length := by
  induction l with
  | nil => simp [monomialOfList]
  | cons a l ih =>
    have : monomialOfList X (a :: l) ω = (X a ω : ℂ) * monomialOfList X l ω := by
      simp [monomialOfList]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, List.length_cons, pow_succ']
    exact mul_le_mul (hB a ω) ih (norm_nonneg _) hB0.le
private theorem partialDeriv_weightedMGF (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, IsBoundedRealRV (X i)) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ i ω, |X i ω| ≤ B) {Y : Ω → ℂ} (hY : Measurable Y) {C : ℝ} (hC : ∀ ω, ‖Y ω‖ ≤ C)
    (j : Fin n) :
    HasPartialDeriv univ (weightedMGF μ X Y) j ∧
      partialDeriv j (weightedMGF μ X Y) =
        weightedMGF μ X fun ω => Y ω * (X j ω : ℂ) := by
  have hlim : ∀ t : ComplexCoordinates n,
      Tendsto (diffQuot (weightedMGF μ X Y) t j) (𝓝[≠] 0)
        (𝓝 (weightedMGF μ X (fun ω => Y ω * (X j ω : ℂ)) t)) := by
    intro t
    have h := (hasDerivAt_iff_tendsto_slope_zero.1
      (hasDerivAt_weightedMGF_line μ hX hB0 hB hY hC t j))
    refine h.congr fun ζ => ?_
    simp [diffQuot]
  refine ⟨⟨isOpen_univ, fun t _ => ⟨_, hlim t⟩⟩, ?_⟩
  funext t
  exact (hlim t).limUnder_eq
private theorem iteratedPartials_weightedMGF (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin n → Ω → ℝ} (hX : ∀ i, IsBoundedRealRV (X i)) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ i ω, |X i ω| ≤ B) (l : List (Fin n)) :
    HasIteratedPartials univ l (weightedMGF μ X fun _ => 1) ∧
      iteratedPartials l (weightedMGF μ X fun _ => 1) =
        weightedMGF μ X (monomialOfList X l) := by
  induction l with
  | nil =>
    refine ⟨isOpen_univ, ?_⟩
    have : monomialOfList X [] = fun _ => 1 := by
      funext ω
      simp [monomialOfList]
    rw [this]
    rfl
  | cons a l ih =>
    obtain ⟨hl, he⟩ := ih
    have hp := partialDeriv_weightedMGF μ hX hB0 hB (measurable_monomialOfList hX l)
      (norm_monomialOfList_le hB0 hB l) a
    have hstep : iteratedPartials (a :: l) (weightedMGF μ X fun _ => 1) =
        partialDeriv a (iteratedPartials l (weightedMGF μ X fun _ => 1)) := rfl
    refine ⟨⟨hl, ?_⟩, ?_⟩
    · rw [he]
      exact hp.1
    · rw [hstep, he, hp.2]
      congr 1
      funext ω
      simp only [monomialOfList, List.map_cons, List.prod_cons]
      ring
private theorem iteratedRealPartial_im_eq_zero {W : Set (ComplexCoordinates n)} (hW : IsOpen W)
    {φ : ComplexCoordinates n → ℂ}
    (hφ : ∀ t ∈ W ∩ ComplexCoordinates.realLocus n, (φ t).im = 0) (l : List (Fin n))
    (h : HasIteratedRealPartial (W ∩ ComplexCoordinates.realLocus n) l φ) :
    ∀ t ∈ W ∩ ComplexCoordinates.realLocus n, (iteratedRealPartial l φ t).im = 0 := by
  induction l with
  | nil => exact hφ
  | cons j l ih =>
    obtain ⟨hl, -, hlim⟩ := h
    have ih' := ih hl
    intro t ht
    obtain ⟨L, hL⟩ := hlim t ht
    have hval : iteratedRealPartial (j :: l) φ t = L := hL.limUnder_eq
    rw [hval]
    have hcont : Continuous fun ζ : ℝ => t + (ζ : ℂ) • ComplexCoordinates.stdBasisVector j := by
      fun_prop
    have hnear : ∀ᶠ ζ : ℝ in 𝓝 0, t + (ζ : ℂ) • ComplexCoordinates.stdBasisVector j ∈ W := by
      refine hcont.continuousAt.eventually_mem (hW.mem_nhds ?_)
      simpa using ht.1
    have hzero : ∀ᶠ ζ : ℝ in 𝓝[≠] 0,
        (diffQuot (iteratedRealPartial l φ) t j ζ).im = 0 := by
      filter_upwards [nhdsWithin_le_nhds hnear] with ζ hζ
      have hreal : t + (ζ : ℂ) • ComplexCoordinates.stdBasisVector j ∈
          ComplexCoordinates.realLocus n := by
        intro i
        have h0 := ht.2 i
        by_cases hij : i = j
        · subst hij
          simp [ComplexCoordinates.stdBasisVector, h0]
        · simp [ComplexCoordinates.stdBasisVector, hij, h0]
      have h1 := ih' _ ⟨hζ, hreal⟩
      have h2 := ih' t ht
      change ((ζ : ℂ)⁻¹ * (iteratedRealPartial l φ (t + (ζ : ℂ) • ComplexCoordinates.stdBasisVector j) -
        iteratedRealPartial l φ t)).im = 0
      rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, Complex.sub_im, h1, h2]
      simp
    have ht1 := (Complex.continuous_im.tendsto L).comp hL
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' (hzero.mono fun ζ h => h.symm))
private def permuteCoords (σ : Equiv.Perm (Fin n)) (t : ComplexCoordinates n) :
    ComplexCoordinates n :=
  fun j => t (σ.symm j)
private theorem partialDeriv_comp_permuteCoords (σ : Equiv.Perm (Fin n))
    (F : ComplexCoordinates n → ℂ) (i : Fin n) :
    partialDeriv i (F ∘ permuteCoords σ) = partialDeriv (σ i) F ∘ permuteCoords σ := by
  funext t
  have hq : diffQuot (F ∘ permuteCoords σ) t i = diffQuot F (permuteCoords σ t) (σ i) := by
    funext ζ
    have hm : permuteCoords σ (t + ζ • ComplexCoordinates.stdBasisVector i) =
        permuteCoords σ t + ζ • ComplexCoordinates.stdBasisVector (σ i) := by
      funext j
      by_cases hj : j = σ i
      · subst hj
        simp [permuteCoords, ComplexCoordinates.stdBasisVector]
      · have : σ.symm j ≠ i := fun h => hj (by rw [← h]; simp)
        simp [permuteCoords, ComplexCoordinates.stdBasisVector, hj, this]
    simp only [diffQuot, Function.comp_apply, hm]
  simp only [partialDeriv, Function.comp_apply]
  rw [hq]
private theorem iteratedPartials_comp_permuteCoords (σ : Equiv.Perm (Fin n))
    (F : ComplexCoordinates n → ℂ) (l : List (Fin n)) :
    iteratedPartials l (F ∘ permuteCoords σ) = iteratedPartials (l.map σ) F ∘ permuteCoords σ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 : iteratedPartials (a :: l) (F ∘ permuteCoords σ) =
        partialDeriv a (iteratedPartials l (F ∘ permuteCoords σ)) := rfl
    have h2 : iteratedPartials ((a :: l).map σ) F =
        partialDeriv (σ a) (iteratedPartials (l.map σ) F) := rfl
    rw [h1, h2, ih, partialDeriv_comp_permuteCoords]
private theorem momentGeneratingFunction_permute (μ : Measure Ω) (X : Fin n → Ω → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    momentGeneratingFunction μ (fun i => X (σ i)) =
      momentGeneratingFunction μ X ∘ permuteCoords σ := by
  funext t
  simp only [momentGeneratingFunction, Function.comp_apply]
  congr 1
  funext ω
  congr 1
  rw [← Equiv.sum_comp σ fun j => permuteCoords σ t j * (X j ω : ℂ)]
  simp [permuteCoords]
private theorem entireWithIntegralDerivatives_of_bounded
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (B : ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) (hB0 : 0 < B) (hB : ∀ i ω, |X i ω| ≤ B) :
    EntireWithIntegralDerivatives μ X := by
  obtain ⟨hE, -, hR, -, -⟩ := hTuple Ω μ n X hn hX
  have hM : momentGeneratingFunction μ X = weightedMGF μ X fun _ => 1 := by
    funext t
    simp [momentGeneratingFunction, weightedMGF, expLinearCombination]
  have hmono : ∀ {k : ℕ} (i : Fin k → Fin n) (ω : Ω),
      monomialOfList X (List.ofFn i) ω = ∏ a, (X (i a) ω : ℂ) := by
    intro k i ω
    simp [monomialOfList, List.map_ofFn, List.prod_ofFn]
  have hint : ∀ (Y : Ω → ℂ), Measurable Y → ∀ C : ℝ, (∀ ω, ‖Y ω‖ ≤ C) →
      ∀ t : ComplexCoordinates n, Integrable (fun ω => Y ω * expLinearCombination X t ω) μ := by
    intro Y hY C hC t
    have hC0 : 0 ≤ C := by
      obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
      exact (norm_nonneg _).trans (hC ω)
    refine Integrable.of_bound (hY.mul (measurable_expLinearCombination_aux hX t)).aestronglyMeasurable
      (C * Real.exp (B * ∑ i, ‖t i‖)) (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul]
    exact mul_le_mul (hC ω) (norm_expLinearCombination_le_aux hB t ω) (norm_nonneg _) hC0
  refine
    { integrable := fun t => ?_
      entire := hE.entire
      value_at_zero := hE.apply_zero
      positive := hR.pos
      has_partials := fun k _ i => ?_
      integrable_under := fun k _ i t => ?_
      under_integral := fun k _ i t => ?_ }
  · have := hint (fun _ => 1) measurable_const 1 (by simp) t
    simpa using this
  · rw [hM]
    exact (iteratedPartials_weightedMGF μ hX hB0 hB _).1
  · have := hint _ (measurable_monomialOfList hX (List.ofFn i)) _
      (norm_monomialOfList_le hB0 hB (List.ofFn i)) t
    have he : monomialMulExp X i t =
        fun ω => monomialOfList X (List.ofFn i) ω * expLinearCombination X t ω := by
      funext ω
      simp only [monomialMulExp, hmono]
    rw [he]
    exact this
  · rw [hM, (iteratedPartials_weightedMGF μ hX hB0 hB _).2]
    simp only [weightedMGF, monomialMulExp, hmono]
private theorem logDomain_isOpen_aux (B : ℝ) : IsOpen (logDomain n B) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm) continuous_const
private theorem zero_mem_logDomain_aux {B : ℝ} (hB0 : 0 < B) :
    (0 : ComplexCoordinates n) ∈ logDomain n B := by
  change ∑ i, ‖(0 : ComplexCoordinates n) i‖ < B⁻¹ * Real.log 2
  simpa using mul_pos (inv_pos.2 hB0) (Real.log_pos one_lt_two)
private theorem logDomain_convex_aux (B : ℝ) : Convex ℝ (logDomain n B) := by
  intro s hs t ht a c ha hc hac
  change ∑ i, ‖(a • s + c • t) i‖ < B⁻¹ * Real.log 2
  have hle : ∑ i, ‖(a • s + c • t) i‖ ≤ a * ∑ i, ‖s i‖ + c * ∑ i, ‖t i‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => (norm_add_le _ _).trans ?_
    simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc, le_refl]
  have hlt := (convex_Iio (B⁻¹ * Real.log 2)) (Set.mem_Iio.2 hs) (Set.mem_Iio.2 ht) ha hc hac
  exact lt_of_le_of_lt hle hlt
private theorem logDomain_subset_aux
    (hHol : HolomorphicLog.HolomorphicLogsOfMomentGeneratingFunction)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (B : ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) (hB0 : 0 < B) (hB : ∀ i ω, |X i ω| ≤ B) :
    logDomain n B ⊆ YangMills.Construction.Cumulants.logDomain μ X := by
  intro t ht
  obtain ⟨hS, -⟩ := hHol Ω μ n X hn hX
  refine hS.subset_logDomain ?_
  change ∑ i, ‖t i‖ * Probability.supModulus (fun ω => (X i ω : ℂ)) < Real.log 2
  have hsup : ∀ i, Probability.supModulus (fun ω => (X i ω : ℂ)) ≤ B := by
    intro i
    change (⨆ ω, ‖((X i ω : ℝ) : ℂ)‖) ≤ B
    refine Real.iSup_le (fun ω => ?_) hB0.le
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hB i ω
  have ht' : ∑ i, ‖t i‖ < B⁻¹ * Real.log 2 := ht
  calc ∑ i, ‖t i‖ * Probability.supModulus (fun ω => (X i ω : ℂ))
      ≤ ∑ i, ‖t i‖ * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsup i) (norm_nonneg _)
    _ = B * ∑ i, ‖t i‖ := by rw [← Finset.sum_mul, mul_comm]
    _ < B * (B⁻¹ * Real.log 2) := mul_lt_mul_of_pos_left ht' hB0
    _ = Real.log 2 := by field_simp
private theorem holomorphic_on_logDomain_aux
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (hFacts : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hHol : HolomorphicLog.HolomorphicLogsOfMomentGeneratingFunction)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (B : ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) (hB0 : 0 < B) (hB : ∀ i ω, |X i ω| ≤ B) :
    IsHolomorphicScalar (logDomain n B) (logMomentGeneratingFunction μ X) ∧
      ∀ J : Finset (Fin n), ComplexVariables.HasPartialOverFinset (logDomain n B) J
        (logMomentGeneratingFunction μ X) := by
  obtain ⟨-, hLog, -, -, -⟩ := hTuple Ω μ n X hn hX
  have hsub := logDomain_subset_aux hHol μ X B hn hX hB0 hB
  have hopen : IsOpen (logDomain n B) := logDomain_isOpen_aux B
  obtain ⟨hF, -⟩ := hFacts n hn _ hLog.isOpen
  obtain ⟨-, -, -, -, -, -, -, hres⟩ := hF _ hLog.holomorphic
  have hhol := (hres _ hopen hsub _ fun _ _ => rfl).1
  obtain ⟨hF', -⟩ := hFacts n hn _ hopen
  obtain ⟨-, -, hJ, -⟩ := hF' _ hhol
  exact ⟨hhol, fun J => (hJ J).1⟩
private theorem logOnLogDomain_of_bounded
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (hFacts : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hHol : HolomorphicLog.HolomorphicLogsOfMomentGeneratingFunction)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (B : ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) (hB0 : 0 < B) (hB : ∀ i ω, |X i ω| ≤ B) :
    LogOnLogDomain μ X B := by
  obtain ⟨-, hLog, -, -, -⟩ := hTuple Ω μ n X hn hX
  have hsub := logDomain_subset_aux hHol μ X B hn hX hB0 hB
  obtain ⟨hhol, hJ⟩ := holomorphic_on_logDomain_aux hTuple hFacts hHol μ X B hn hX hB0 hB
  obtain ⟨-, -, -, -, hPL, hConn⟩ := hFacts n hn _ (logDomain_isOpen_aux B)
  obtain ⟨-, -, -, -, -, -, hDisc, -⟩ := hPL
  obtain ⟨-, hConst, hExp⟩ := hConn
  have hnear : ∀ t ∈ logDomain n B, ‖momentGeneratingFunction μ X t - 1‖ < 1 :=
    fun t ht => hsub ht
  refine
    { near_one := hnear
      maps_to := fun t ht => hDisc (hnear t ht)
      holomorphic := hhol
      has_mixed_partial := hJ Finset.univ
      cumulant_eq := hLog.mixedCumulant_eq
      unique := ?_ }
  intro U' F hconv hopen' h0 hcont hF0 hexp t ht
  have hWopen : IsOpen (logDomain n B ∩ U') := (logDomain_isOpen_aux B).inter hopen'
  have h0W : (0 : ComplexCoordinates n) ∈ logDomain n B ∩ U' := ⟨zero_mem_logDomain_aux hB0, h0⟩
  have hWconn : IsConnected (logDomain n B ∩ U') :=
    ⟨⟨0, h0W⟩, ((logDomain_convex_aux B).inter hconv).isPreconnected⟩
  have hc : ContinuousOn (fun z => F z - logMomentGeneratingFunction μ X z) (logDomain n B ∩ U') :=
    (hcont.mono inter_subset_right).sub
      ((continuousOn_of_isHolomorphicScalar_aux hhol).mono inter_subset_left)
  have hmult : ∀ z ∈ logDomain n B ∩ U',
      F z - logMomentGeneratingFunction μ X z ∈ ComplexVariables.twoPiIMultiples := by
    intro z hz
    refine hExp _ ?_
    rw [Complex.exp_sub, hexp z hz.2, hLog.exp_log z (hsub hz.1)]
    exact div_self (hLog.mgf_ne_zero z (hsub hz.1))
  obtain ⟨c, hc'⟩ := (hConst _ hWopen hWconn).2 _ hc hmult
  have hc0 : c = 0 := by
    have := hc' 0 h0W
    rw [hF0, hLog.apply_zero, sub_zero] at this
    exact this.symm
  have := hc' t ht
  rw [hc0] at this
  exact sub_eq_zero.1 this
private theorem subfamilyCumulants_of_bounded
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (hFacts : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hHol : HolomorphicLog.HolomorphicLogsOfMomentGeneratingFunction)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (B : ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) (hB0 : 0 < B) (hB : ∀ i ω, |X i ω| ≤ B) :
    SubfamilyCumulants μ X B := by
  obtain ⟨-, -, -, hSub, -⟩ := hTuple Ω μ n X hn hX
  exact
    { has_partial := fun J _ =>
        (holomorphic_on_logDomain_aux hTuple hFacts hHol μ X B hn hX hB0 hB).2 J
      cumulant_eq := fun J hJ => (hSub.finsetCumulant_eq J hJ.ne_empty).symm }
private theorem cumulantRealSymmetric_of_bounded
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (hFacts : ComplexVariables.HolomorphicFacts.StandardFacts)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) : CumulantRealSymmetric μ X := by
  obtain ⟨-, hLog, hR, -, -⟩ := hTuple Ω μ n X hn hX
  refine ⟨?_, fun σ => ?_⟩
  · rw [hR.mixedCumulant_eq]
    exact iteratedRealPartial_im_eq_zero hLog.isOpen (fun t _ => Complex.ofReal_im _) _
      hR.hasPartials 0 hR.zero_mem
  · obtain ⟨-, hLog', -, -, -⟩ := hTuple Ω μ n (fun i => X (σ i)) hn fun i => hX _
    have hL : logMomentGeneratingFunction μ (fun i => X (σ i)) =
        logMomentGeneratingFunction μ X ∘ permuteCoords σ := by
      funext t
      change ComplexVariables.logPrincipal (momentGeneratingFunction μ (fun i => X (σ i)) t) =
        ComplexVariables.logPrincipal (momentGeneratingFunction μ X (permuteCoords σ t))
      rw [momentGeneratingFunction_permute]
      rfl
    have hperm : ((Finset.univ : Finset (Fin n)).sort.map σ).Perm
        (Finset.univ : Finset (Fin n)).sort := by
      refine (List.perm_ext_iff_of_nodup
        ((Finset.sort_nodup _ _).map σ.injective) (Finset.sort_nodup _ _)).2 fun a => ?_
      simp only [List.mem_map, Finset.mem_sort, Finset.mem_univ, true_and, iff_true]
      exact ⟨σ.symm a, by simp⟩
    obtain ⟨hF, -⟩ := hFacts n hn _ hLog.isOpen
    obtain ⟨-, -, -, -, hord, -⟩ := hF _ hLog.holomorphic
    have hm0 : permuteCoords σ (0 : ComplexCoordinates n) = 0 := rfl
    rw [hLog'.mixedCumulant_eq, hLog.mixedCumulant_eq, hL]
    unfold ComplexVariables.partialOverFinset
    rw [iteratedPartials_comp_permuteCoords, Function.comp_apply, hm0]
    exact (hord Finset.univ _ hperm).2 hLog.zero_mem
private theorem cumulantSpecialValues_of_bounded
    (hRel : MomentCumulantRelations.Holds)
    (hEnt : GeneratingLog.EntireAndLogCumulant)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (hn : 1 ≤ n)
    (hX : ∀ i, IsBoundedRealRV (X i)) : CumulantSpecialValues μ X := by
  obtain ⟨-, h1, h2, -⟩ := hRel Ω μ
  refine ⟨fun hn1 i => ?_, fun h c => h2 n X c h hX, fun i hi => (hEnt Ω μ n X hn hX).2 i hi⟩
  subst hn1
  have hconst : X = fun _ => X i := by
    funext k
    rw [Subsingleton.elim k i]
  have := h1 (X i) (hX i)
  rw [← hconst] at this
  exact this
theorem boundedGeneratingFunctionTheorem_of_facts
    (hTuple : TupleLogMGF.TupleMGFAndLogTheorem)
    (hFacts : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hHol : HolomorphicLog.HolomorphicLogsOfMomentGeneratingFunction)
    (hRel : MomentCumulantRelations.Holds)
    (hEnt : GeneratingLog.EntireAndLogCumulant) : BoundedGeneratingFunctionTheorem := by
  intro Ω _ μ _ n X B hn hX hB0 hB
  exact ⟨entireWithIntegralDerivatives_of_bounded hTuple μ X B hn hX hB0 hB,
    logOnLogDomain_of_bounded hTuple hFacts hHol μ X B hn hX hB0 hB,
    subfamilyCumulants_of_bounded hTuple hFacts hHol μ X B hn hX hB0 hB,
    cumulantRealSymmetric_of_bounded hTuple hFacts μ X hn hX,
    cumulantSpecialValues_of_bounded hRel hEnt μ X hn hX⟩
end YangMills.Construction.Cumulants.BoundedVariables
