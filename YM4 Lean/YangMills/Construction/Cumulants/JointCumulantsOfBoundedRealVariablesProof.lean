import YangMills.Construction.Cumulants.JointCumulantsAreRealSymmetricAndMultilinearProof
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.JointCumulantsOfBoundedRealVariables
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.RealVariables
open YangMills.Construction.Probability (IsBoundedRealRV complexExpectation)
section Weighted
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def weightedMGF (ν : Measure Ω) (ξ : Fin n → Ω → ℝ) (w : Ω → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun t => ∫ ω, w ω * expLinearCombinationAt ξ ω t ∂ν
theorem isBoundedRealRV_mul {x y : Ω → ℝ} (hx : IsBoundedRealRV x)
    (hy : IsBoundedRealRV y) : IsBoundedRealRV fun ω => x ω * y ω := by
  obtain ⟨C, hC⟩ := hx.bounded
  obtain ⟨D, hD⟩ := hy.bounded
  refine ⟨hx.measurable.mul hy.measurable, C * D, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC ω) (hD ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
theorem exists_uniform_bound {ξ : Fin n → Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |ξ i ω| ≤ B := by
  choose C hC using fun i => (hξ i).bounded
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i ω => ?_⟩
  exact (hC i ω).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
theorem expLinearCombinationAt_pos (ξ : Fin n → Ω → ℝ) (ω : Ω) (t : Fin n → ℝ) :
    0 < expLinearCombinationAt ξ ω t :=
  Real.exp_pos _
theorem expLinearCombinationAt_le {ξ : Fin n → Ω → ℝ} {B ρ : ℝ} (hB : ∀ i ω, |ξ i ω| ≤ B)
    {t : Fin n → ℝ} (ht : ‖t‖ ≤ ρ) (ω : Ω) :
    expLinearCombinationAt ξ ω t ≤ Real.exp (n * (ρ * B)) := by
  refine Real.exp_le_exp.2 ?_
  have h : ∀ i, t i * ξ i ω ≤ ρ * B := fun i =>
    calc t i * ξ i ω ≤ |t i * ξ i ω| := le_abs_self _
      _ = |t i| * |ξ i ω| := abs_mul _ _
      _ ≤ ρ * B := mul_le_mul ((norm_le_pi_norm t i).trans ht) (hB i ω) (abs_nonneg _)
          ((norm_nonneg t).trans ht)
  calc ∑ i, t i * ξ i ω ≤ ∑ _i : Fin n, ρ * B := Finset.sum_le_sum fun i _ => h i
    _ = n * (ρ * B) := by simp
theorem measurable_expLinearCombinationAt {ξ : Fin n → Ω → ℝ}
    (hξ : ∀ i, IsBoundedRealRV (ξ i)) (t : Fin n → ℝ) :
    Measurable fun ω => expLinearCombinationAt ξ ω t := by
  have h : ∀ i, Measurable (ξ i) := fun i => (hξ i).measurable
  unfold expLinearCombinationAt
  fun_prop
theorem integrable_weightedMGF_integrand {ν : Measure Ω} [IsFiniteMeasure ν]
    {ξ : Fin n → Ω → ℝ} {w : Ω → ℝ}
    (hξ : ∀ i, IsBoundedRealRV (ξ i)) (hw : IsBoundedRealRV w)
    (t : Fin n → ℝ) : Integrable (fun ω => w ω * expLinearCombinationAt ξ ω t) ν := by
  obtain ⟨B, -, hB⟩ := exists_uniform_bound hξ
  obtain ⟨M, hM⟩ := hw.bounded
  refine Integrable.of_bound
    (hw.measurable.mul (measurable_expLinearCombinationAt hξ t)).aestronglyMeasurable
    (M * Real.exp (n * (‖t‖ * B))) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (expLinearCombinationAt_pos ξ ω t)]
  exact mul_le_mul (hM ω) (expLinearCombinationAt_le hB le_rfl ω)
    (expLinearCombinationAt_pos ξ ω t).le ((abs_nonneg _).trans (hM ω))
def pairingForm (ξ : Fin n → Ω → ℝ) (ω : Ω) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ξ i ω • ContinuousLinearMap.proj i
theorem pairingForm_apply (ξ : Fin n → Ω → ℝ) (ω : Ω) (s : Fin n → ℝ) :
    pairingForm ξ ω s = ∑ i, s i * ξ i ω := by
  simp [pairingForm, mul_comm]
theorem hasFDerivAt_const_mul_expLinearCombinationAt (ξ : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω)
    (t : Fin n → ℝ) :
    HasFDerivAt (fun s => c * expLinearCombinationAt ξ ω s)
      ((c * expLinearCombinationAt ξ ω t) • pairingForm ξ ω) t := by
  have h : HasFDerivAt (fun s => pairingForm ξ ω s) (pairingForm ξ ω) t :=
    (pairingForm ξ ω).hasFDerivAt
  have h2 := h.exp.const_mul c
  simp only [pairingForm_apply] at h2
  rw [smul_smul] at h2
  exact h2
theorem hasFDerivAt_weightedMGF {ν : Measure Ω} [IsFiniteMeasure ν] {ξ : Fin n → Ω → ℝ}
    {w : Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) (hw : IsBoundedRealRV w)
    (t : Fin n → ℝ) :
    HasFDerivAt (weightedMGF ν ξ w)
      (∑ i, weightedMGF ν ξ (fun ω => w ω * ξ i ω) t •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) t := by
  obtain ⟨B, -, hB⟩ := exists_uniform_bound hξ
  obtain ⟨M, hM⟩ := hw.bounded
  have hsum : ∀ ω, (w ω * expLinearCombinationAt ξ ω t) • pairingForm ξ ω =
      ∑ i, (w ω * ξ i ω * expLinearCombinationAt ξ ω t) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := fun ω => by
    simp only [pairingForm, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have hint : ∀ i, Integrable (fun ω => (w ω * ξ i ω * expLinearCombinationAt ξ ω t) •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) ν := fun i =>
    (integrable_weightedMGF_integrand hξ (isBoundedRealRV_mul hw (hξ i)) t).smul_const _
  have hmeas : AEStronglyMeasurable
      (fun ω => (w ω * expLinearCombinationAt ξ ω t) • pairingForm ξ ω) ν := by
    have hI : Integrable (fun ω => ∑ i, (w ω * ξ i ω * expLinearCombinationAt ξ ω t) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) ν :=
      integrable_finsetSum Finset.univ
        (f := fun i ω => (w ω * ξ i ω * expLinearCombinationAt ξ ω t) •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) fun i _ => hint i
    rw [funext hsum]
    exact hI.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂ν, ∀ s ∈ Metric.ball t 1,
      ‖(w ω * expLinearCombinationAt ξ ω s) • pairingForm ξ ω‖ ≤
        M * Real.exp (n * ((‖t‖ + 1) * B)) *
          ∑ i, B * ‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ := by
    refine ae_of_all _ fun ω s hs => ?_
    have hs' : ‖s‖ ≤ ‖t‖ + 1 := by
      have h1 : ‖s - t‖ < 1 := by simpa [dist_eq_norm] using hs
      calc ‖s‖ = ‖(s - t) + t‖ := by simp
        _ ≤ ‖s - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ ‖t‖ + 1 := by linarith
    have hA : ‖pairingForm ξ ω‖ ≤
        ∑ i, B * ‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB i ω) (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (expLinearCombinationAt_pos ξ ω s)]
    refine mul_le_mul (mul_le_mul (hM ω) (expLinearCombinationAt_le hB hs' ω)
      (expLinearCombinationAt_pos ξ ω s).le ((abs_nonneg _).trans (hM ω))) hA (norm_nonneg _) ?_
    exact mul_nonneg ((abs_nonneg _).trans (hM ω)) (Real.exp_pos _).le
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (𝕜 := ℝ)
    (F := fun s ω => w ω * expLinearCombinationAt ξ ω s)
    (F' := fun s ω => (w ω * expLinearCombinationAt ξ ω s) • pairingForm ξ ω)
    (x₀ := t) (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s =>
      (hw.measurable.mul (measurable_expLinearCombinationAt hξ s)).aestronglyMeasurable)
    (integrable_weightedMGF_integrand hξ hw t) hmeas hbound (integrable_const _)
    (ae_of_all _ fun ω s _ => hasFDerivAt_const_mul_expLinearCombinationAt ξ (w ω) ω s)
  have hval : ∫ ω, (w ω * expLinearCombinationAt ξ ω t) • pairingForm ξ ω ∂ν =
      ∑ i, weightedMGF ν ξ (fun ω => w ω * ξ i ω) t •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
    rw [funext hsum, integral_finsetSum Finset.univ (f := fun i ω =>
      (w ω * ξ i ω * expLinearCombinationAt ξ ω t) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const]
    rfl
  rw [hval] at hmain
  exact hmain
theorem contDiff_weightedMGF_nat {ν : Measure Ω} [IsFiniteMeasure ν] {ξ : Fin n → Ω → ℝ}
    (hξ : ∀ i, IsBoundedRealRV (ξ i)) (k : ℕ) :
    ∀ w : Ω → ℝ, IsBoundedRealRV w →
      ContDiff ℝ k (weightedMGF ν ξ w) := by
  induction k with
  | zero =>
    intro w hw
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun t => (hasFDerivAt_weightedMGF hξ hw t).continuousAt
  | succ k ih =>
    intro w hw
    have hfd : fderiv ℝ (weightedMGF ν ξ w) =
        fun t => ∑ i, weightedMGF ν ξ (fun ω => w ω * ξ i ω) t •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) :=
      funext fun t => (hasFDerivAt_weightedMGF hξ hw t).fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun t => (hasFDerivAt_weightedMGF hξ hw t).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [hfd]
      exact ContDiff.sum fun i _ => (ih _ (isBoundedRealRV_mul hw (hξ i))).smul contDiff_const
theorem contDiff_weightedMGF {ν : Measure Ω} [IsFiniteMeasure ν] {ξ : Fin n → Ω → ℝ}
    {w : Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) (hw : IsBoundedRealRV w) :
    ContDiff ℝ (⊤ : ℕ∞) (weightedMGF ν ξ w) :=
  contDiff_infty.2 fun k => contDiff_weightedMGF_nat hξ k w hw
theorem realPartialDeriv_weightedMGF {ν : Measure Ω} [IsFiniteMeasure ν] {ξ : Fin n → Ω → ℝ}
    {w : Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) (hw : IsBoundedRealRV w)
    (j : Fin n) :
    realPartialDeriv j (weightedMGF ν ξ w) =
      weightedMGF ν ξ fun ω => w ω * ξ j ω := by
  funext t
  unfold realPartialDeriv
  rw [(hasFDerivAt_weightedMGF hξ hw t).fderiv]
  simp [Pi.single_apply]
def listProductWeight (ξ : Fin n → Ω → ℝ) (l : List (Fin n)) : Ω → ℝ :=
  fun ω => (l.map fun j => ξ j ω).prod
theorem isBoundedRealRV_listProductWeight {ξ : Fin n → Ω → ℝ}
    (hξ : ∀ i, IsBoundedRealRV (ξ i)) (l : List (Fin n)) :
    IsBoundedRealRV (listProductWeight ξ l) := by
  induction l with
  | nil =>
    have h : listProductWeight ξ [] = fun _ => 1 := funext fun ω => by simp [listProductWeight]
    rw [h]
    exact ⟨measurable_const, 1, by simp⟩
  | cons j l ih =>
    have h : listProductWeight ξ (j :: l) = fun ω => ξ j ω * listProductWeight ξ l ω :=
      funext fun ω => by simp [listProductWeight]
    rw [h]
    exact isBoundedRealRV_mul (hξ j) ih
theorem iteratedRealPartialDeriv_weightedMGF {ν : Measure Ω} [IsFiniteMeasure ν]
    {ξ : Fin n → Ω → ℝ} {w : Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i))
    (hw : IsBoundedRealRV w) (l : List (Fin n)) :
    iteratedRealPartialDeriv l (weightedMGF ν ξ w) =
      weightedMGF ν ξ fun ω => w ω * listProductWeight ξ l ω := by
  induction l with
  | nil => simp [iteratedRealPartialDeriv, listProductWeight]
  | cons j l ih =>
    change realPartialDeriv j (iteratedRealPartialDeriv l _) = _
    rw [ih, realPartialDeriv_weightedMGF hξ
      (isBoundedRealRV_mul hw (isBoundedRealRV_listProductWeight hξ l))]
    congr 1
    funext ω
    simp only [listProductWeight, List.map_cons, List.prod_cons]
    ring
theorem iteratedRealPartialDeriv_expLinearCombinationAt (ξ : Fin n → Ω → ℝ) (ω : Ω)
    (l : List (Fin n)) :
    iteratedRealPartialDeriv l (expLinearCombinationAt ξ ω) =
      fun t => listProductWeight ξ l ω * expLinearCombinationAt ξ ω t := by
  induction l with
  | nil => simp [iteratedRealPartialDeriv, listProductWeight]
  | cons j l ih =>
    change realPartialDeriv j (iteratedRealPartialDeriv l _) = _
    rw [ih]
    funext t
    unfold realPartialDeriv
    rw [(hasFDerivAt_const_mul_expLinearCombinationAt ξ (listProductWeight ξ l ω) ω t).fderiv]
    simp only [_root_.smul_apply, pairingForm_apply, smul_eq_mul, listProductWeight,
      List.map_cons, List.prod_cons]
    simp [Pi.single_apply]
    ring
theorem weightedMGF_one (ν : Measure Ω) (ξ : Fin n → Ω → ℝ) :
    weightedMGF ν ξ (fun _ => 1) = realMomentGeneratingFunction ν ξ := by
  funext t
  simp [weightedMGF, realMomentGeneratingFunction]
theorem isBoundedRealRV_one : IsBoundedRealRV fun _ : Ω => (1 : ℝ) :=
  ⟨measurable_const, 1, by simp⟩
theorem contDiff_realMomentGeneratingFunction {ν : Measure Ω} [IsFiniteMeasure ν]
    {ξ : Fin n → Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) :
    ContDiff ℝ (⊤ : ℕ∞) (realMomentGeneratingFunction ν ξ) := by
  rw [← weightedMGF_one]
  exact contDiff_weightedMGF hξ isBoundedRealRV_one
theorem realMomentGeneratingFunction_pos {ν : Measure Ω} [IsProbabilityMeasure ν]
    {ξ : Fin n → Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) (t : Fin n → ℝ) :
    0 < realMomentGeneratingFunction ν ξ t := by
  have h : Integrable (fun ω => Real.exp (∑ i, t i * ξ i ω)) ν := by
    simpa [expLinearCombinationAt] using
      integrable_weightedMGF_integrand (ν := ν) hξ isBoundedRealRV_one t
  exact integral_exp_pos h
theorem contDiff_realLogMomentGeneratingFunction {ν : Measure Ω} [IsProbabilityMeasure ν]
    {ξ : Fin n → Ω → ℝ} (hξ : ∀ i, IsBoundedRealRV (ξ i)) :
    ContDiff ℝ (⊤ : ℕ∞) (realLogMomentGeneratingFunction ν ξ) :=
  (contDiff_realMomentGeneratingFunction hξ).log fun t =>
    (realMomentGeneratingFunction_pos hξ t).ne'
end Weighted
section Chain
variable {n r : ℕ}
theorem contDiff_realPartialDeriv {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (realPartialDeriv j F) :=
  ((contDiff_infty_iff_fderiv.1 hF).2).clm_apply contDiff_const
theorem contDiff_iteratedRealPartialDeriv {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (l : List (Fin n)) : ContDiff ℝ (⊤ : ℕ∞) (iteratedRealPartialDeriv l F) := by
  induction l with
  | nil => exact hF
  | cons j l ih => exact contDiff_realPartialDeriv ih j
theorem differentiable_of_contDiff_top {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Differentiable ℝ F :=
  (contDiff_infty_iff_fderiv.1 hF).1
def coordinateEmbedding (e : Fin r → Fin n) : (Fin r → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑ a, (ContinuousLinearMap.proj a : (Fin r → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (e a) (1 : ℝ))
theorem coordinateEmbedding_apply (e : Fin r → Fin n) (s : Fin r → ℝ) :
    coordinateEmbedding e s = ∑ a, s a • (Pi.single (e a) (1 : ℝ) : Fin n → ℝ) := by
  simp [coordinateEmbedding]
theorem coordinateEmbedding_single (e : Fin r → Fin n) (a : Fin r) :
    coordinateEmbedding e (Pi.single a 1) = Pi.single (e a) 1 := by
  rw [coordinateEmbedding_apply]
  simp [Pi.single_apply]
theorem realPartialDeriv_comp_coordinateEmbedding (e : Fin r → Fin n) {F : (Fin n → ℝ) → ℝ}
    (hF : Differentiable ℝ F) (a : Fin r) :
    realPartialDeriv a (F ∘ coordinateEmbedding e) =
      realPartialDeriv (e a) F ∘ coordinateEmbedding e := by
  funext t
  unfold realPartialDeriv
  rw [((hF _).hasFDerivAt.comp t (coordinateEmbedding e).hasFDerivAt).fderiv]
  simp [coordinateEmbedding_single]
theorem iteratedRealPartialDeriv_comp_coordinateEmbedding (e : Fin r → Fin n)
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (l : List (Fin r)) :
    iteratedRealPartialDeriv l (F ∘ coordinateEmbedding e) =
      iteratedRealPartialDeriv (l.map e) F ∘ coordinateEmbedding e := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change realPartialDeriv a (iteratedRealPartialDeriv l _) =
      realPartialDeriv (e a) (iteratedRealPartialDeriv _ F) ∘ _
    rw [ih, realPartialDeriv_comp_coordinateEmbedding e
      (differentiable_of_contDiff_top (contDiff_iteratedRealPartialDeriv hF _))]
def realPoint (t : Fin n → ℝ) : Coordinates.ComplexCoordinates n := fun i => (t i : ℂ)
theorem complexRealPartialDeriv_of_lift {Φ : Coordinates.ComplexCoordinates n → ℂ}
    {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) (hΦ : ∀ s, Φ (realPoint s) = (f s : ℂ))
    (j : Fin n) (t : Fin n → ℝ) :
    ComplexVariables.realPartialDeriv j Φ (realPoint t) = (realPartialDeriv j f t : ℂ) := by
  have hd : HasDerivAt (fun ζ : ℝ => f (t + ζ • Pi.single j (1 : ℝ)))
      (fderiv ℝ f t (Pi.single j 1)) 0 :=
    (hf t).hasFDerivAt.hasLineDerivAt (Pi.single j 1)
  have hs := (Complex.continuous_ofReal.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hd)
  refine Tendsto.limUnder_eq (hs.congr fun ζ => ?_)
  have hpt : realPoint t + (ζ : ℂ) • Coordinates.ComplexCoordinates.stdBasisVector j =
      realPoint (t + ζ • Pi.single j (1 : ℝ)) := by
    funext i
    by_cases h : i = j
    · subst h
      simp [realPoint, Coordinates.ComplexCoordinates.stdBasisVector]
    · simp [realPoint, Coordinates.ComplexCoordinates.stdBasisVector, h]
  simp only [Function.comp, ComplexVariables.diffQuot, hpt, hΦ, slope]
  simp
theorem iteratedRealPartial_of_lift {Φ : Coordinates.ComplexCoordinates n → ℂ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hΦ : ∀ s, Φ (realPoint s) = (f s : ℂ))
    (l : List (Fin n)) (t : Fin n → ℝ) :
    TupleLogMGF.iteratedRealPartial l Φ (realPoint t) =
      (iteratedRealPartialDeriv l f t : ℂ) := by
  induction l generalizing t with
  | nil => exact hΦ t
  | cons j l ih =>
    exact complexRealPartialDeriv_of_lift
      (differentiable_of_contDiff_top (contDiff_iteratedRealPartialDeriv hf l)) ih j t
theorem finRange_map_orderEmbOfFin (J : Finset (Fin n)) :
    (List.finRange J.card).map (J.orderEmbOfFin rfl) = J.sort := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
end Chain
section SubFamily
variable {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ}
theorem realMomentGeneratingFunction_comp_coordinateEmbedding (ν : Measure Ω)
    (ξ : Fin n → Ω → ℝ) (e : Fin r → Fin n) (s : Fin r → ℝ) :
    realMomentGeneratingFunction ν (fun a => ξ (e a)) s =
      realMomentGeneratingFunction ν ξ (coordinateEmbedding e s) := by
  unfold realMomentGeneratingFunction expLinearCombinationAt
  congr 1
  funext ω
  congr 1
  rw [coordinateEmbedding_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
theorem tupleMomentGeneratingFunction_realPoint (ν : Measure Ω) (ξ : Fin n → Ω → ℝ)
    (s : Fin n → ℝ) :
    tupleMomentGeneratingFunction ν ξ (realPoint s) =
      (realMomentGeneratingFunction ν ξ s : ℂ) := by apply _root_.YangMills.Construction.Cumulants.RealSymmetricMultilinear.momentGeneratingFunction_ofReal <;> assumption
theorem finsetCumulant_eq_realPartialDerivOverFinset (hGen : TupleLogMGF.TupleMGFAndLogTheorem)
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {n : ℕ}
    (ξ : Fin n → Ω → ℝ) (hξ : ∀ i, IsBoundedRealRV (ξ i)) (J : Finset (Fin n))
    (hJ : J.Nonempty) :
    finsetCumulant ν ξ J =
      ((realPartialDerivOverFinset J (realLogMomentGeneratingFunction ν ξ) 0 : ℝ) : ℂ) := by
  have hy : ∀ a, IsBoundedRealRV (restrictTuple ξ J a) := fun a => hξ _
  obtain ⟨-, -, hS, -, -⟩ := hGen Ω ν J.card (restrictTuple ξ J) (Finset.card_pos.2 hJ) hy
  have hΦ : ∀ s, TupleLogMGF.realLogTupleMGF ν (restrictTuple ξ J)
      (realPoint s) = (realLogMomentGeneratingFunction ν (restrictTuple ξ J) s : ℂ) := fun s => by
    unfold TupleLogMGF.realLogTupleMGF realLogMomentGeneratingFunction
    rw [tupleMomentGeneratingFunction_realPoint, Complex.ofReal_re]
  have hcomp : realLogMomentGeneratingFunction ν (restrictTuple ξ J) =
      realLogMomentGeneratingFunction ν ξ ∘ coordinateEmbedding (J.orderEmbOfFin rfl) := by
    funext s
    simp only [realLogMomentGeneratingFunction, Function.comp]
    rw [← realMomentGeneratingFunction_comp_coordinateEmbedding]
    rfl
  have hzero : (0 : Coordinates.ComplexCoordinates J.card) = realPoint 0 := by
    funext i
    simp [realPoint]
  change mixedCumulant ν (restrictTuple ξ J) = _
  rw [hS.mixedCumulant_eq, hzero, iteratedRealPartial_of_lift (contDiff_realLogMomentGeneratingFunction hy) hΦ,
    hcomp, iteratedRealPartialDeriv_comp_coordinateEmbedding _
      (contDiff_realLogMomentGeneratingFunction hξ), finRange_map_orderEmbOfFin]
  simp [realPartialDerivOverFinset]
end SubFamily
theorem complexExpectation_ofReal {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ) :
    (complexExpectation ν fun ω => (f ω : ℂ)) = ((∫ ω, f ω ∂ν : ℝ) : ℂ) :=
  integral_complex_ofReal
theorem boundedRealCumulantTheorem_holds (hMoments : CumulantMomentRelations)
    (hGen : TupleLogMGF.TupleMGFAndLogTheorem) : BoundedRealCumulantTheorem := by
  intro Ω _ ν _ n ξ hn hξ
  obtain ⟨hA, -, -, -, -, hCentred, -⟩ := hMoments Ω ν n ξ hξ
  obtain ⟨hreal, hperm, -⟩ := hA n ξ (ξ ⟨0, hn⟩) hn hξ (hξ _)
  refine ⟨⟨?_, realMomentGeneratingFunction_pos hξ, ?_, ?_,
    contDiff_realLogMomentGeneratingFunction hξ,
    finsetCumulant_eq_realPartialDerivOverFinset hGen ν ξ hξ, hreal⟩, hperm, ?_, ?_⟩
  · exact contDiff_realMomentGeneratingFunction hξ
  · intro l t
    rw [show (fun ω => iteratedRealPartialDeriv l (expLinearCombinationAt ξ ω) t) =
        fun ω => listProductWeight ξ l ω * expLinearCombinationAt ξ ω t from
      funext fun ω => congrFun (iteratedRealPartialDeriv_expLinearCombinationAt ξ ω l) t]
    exact integrable_weightedMGF_integrand hξ (isBoundedRealRV_listProductWeight hξ l) t
  · intro l t
    rw [← weightedMGF_one, iteratedRealPartialDeriv_weightedMGF hξ isBoundedRealRV_one]
    simp only [iteratedRealPartialDeriv_expLinearCombinationAt, weightedMGF, one_mul]
  · intro i₀ η η' α α' hη hη' hi
    have hupd : ∀ i, IsBoundedRealRV (Function.update ξ i₀ η i) := fun i => by
      by_cases h : i = i₀
      · subst h
        simpa using hη
      · simpa [h] using hξ i
    obtain ⟨-, -, hlin⟩ := hA n (Function.update ξ i₀ η) η' hn hupd hη'
    have h := hlin i₀ α α'
    have hξeq : Function.update (Function.update ξ i₀ η) i₀
        (fun ω => α * Function.update ξ i₀ η i₀ ω + α' * η' ω) = ξ := by
      rw [Function.update_idem, Function.update_self]
      have : (fun ω => α * η ω + α' * η' ω) = ξ i₀ := funext fun ω => (hi ω).symm
      rw [this, Function.update_eq_self]
    rw [hξeq, Function.update_idem] at h
    exact h
  · intro _
    rw [← SetPartition.singletonFree_eq_nonSingletonPartitions, ← hCentred,
      ← complexExpectation_ofReal]
    refine congrArg (complexExpectation ν) (funext fun ω => ?_)
    simp only [complexExpectation_ofReal]
    push_cast
    rfl
end YangMills.Construction.Cumulants.RealVariables
