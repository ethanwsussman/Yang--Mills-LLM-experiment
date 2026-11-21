import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.Continuum.CutoffNearTheComplementOfAnOpenSetProof
import YangMills.Construction.Continuum.IntegratingArgumentsOutOfFlatSchwartzFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
namespace IntegrateOut
open DerivRules
variable {n : ℕ}
def basisIdx (i : Fin n) (μ : Fin 4) : MultiIdx4 n := Pi.single i (Pi.single μ 1)
theorem multiDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : PointTuple n → F) : multiDeriv (0 : MultiIdx4 n) g = g := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.multiDeriv_zero <;> assumption
theorem multiDeriv_basisIdx {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (μ : Fin 4) (g : PointTuple n → F) :
    multiDeriv (basisIdx i μ) g = coordDeriv i μ g := by apply _root_.YangMills.Construction.TestSpaces.CompactSuppCutoff.multiDeriv_coordIdx <;> assumption
theorem idxOrder_add (α γ : MultiIdx4 n) : idxOrder (α + γ) = idxOrder α + idxOrder γ := by
  simp [idxOrder, Finset.sum_add_distrib]
theorem idxOrder_basisIdx (i : Fin n) (μ : Fin 4) : idxOrder (basisIdx i μ) = 1 := by
  unfold idxOrder basisIdx
  rw [Finset.sum_eq_single i, Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [hν]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
theorem coordDeriv_multiDeriv (hC : RulesOver ℂ) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin n) (μ : Fin 4) (β : MultiIdx4 n) :
    coordDeriv i μ (multiDeriv β φ) = multiDeriv (basisIdx i μ + β) φ := by
  rw [← (hC n φ hφ).2.2.2.2.1 (basisIdx i μ) β, multiDeriv_basisIdx]
theorem eq_sum_basis (v : PointTuple n) :
    v = ∑ i, ∑ μ, v i μ • (Pi.single i (Pi.single μ 1) : PointTuple n) := by apply _root_.YangMills.Construction.TestSpaces.CompactSuppCutoff.eq_sum_smul_single <;> assumption
theorem clm_apply_eq_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : PointTuple n →L[ℝ] F) (v : PointTuple n) :
    T v = ∑ i, ∑ μ, v i μ • T (Pi.single i (Pi.single μ 1)) := by
  conv_lhs => rw [eq_sum_basis v]
  simp only [map_sum, map_smul]
theorem norm_clm_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : PointTuple n →L[ℝ] F) : ‖T‖ ≤ ∑ i, ∑ μ, ‖T (Pi.single i (Pi.single μ 1))‖ := by
  refine T.opNorm_le_bound
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => norm_nonneg _) fun v => ?_
  rw [clm_apply_eq_sum_basis T v, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (v i) μ).trans (norm_le_pi_norm v i))
    (norm_nonneg _)
def radialWeight (k : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  (1 + TorusMetric.euclidNormVec u ^ 2) ^ (-(k : ℝ) / 2)
theorem euclidNormVec_sq (u : Fin 4 → ℝ) : TorusMetric.euclidNormVec u ^ 2 = ∑ μ, u μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem radialWeight_nonneg (k : ℕ) (u : Fin 4 → ℝ) : 0 ≤ radialWeight k u := by
  unfold radialWeight
  positivity
theorem continuous_radialWeight (k : ℕ) : Continuous (radialWeight k) := by
  have h : radialWeight k = fun u : Fin 4 → ℝ => (1 + ∑ μ, u μ ^ 2) ^ (-(k : ℝ) / 2) := by
    funext u
    simp only [radialWeight, euclidNormVec_sq]
  rw [h]
  refine Continuous.rpow_const (by fun_prop) fun u => Or.inl ?_
  positivity
theorem norm_le_euclidNormVec (u : Fin 4 → ℝ) : ‖u‖ ≤ TorusMetric.euclidNormVec u := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem integrable_radialWeight {k : ℕ} (hk : 4 < k) : Integrable (radialWeight k) := by
  have hk' : ((Module.finrank ℝ (Fin 4 → ℝ) : ℕ) : ℝ) < k := by
    simpa using (by exact_mod_cast hk : (4 : ℝ) < k)
  have h := integrable_rpow_neg_one_add_norm_sq (E := Fin 4 → ℝ) (μ := volume) hk'
  refine h.mono' (continuous_radialWeight k).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (radialWeight_nonneg k u)]
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
  · have := pow_le_pow_left₀ (norm_nonneg u) (norm_le_euclidNormVec u) 2
    linarith
  · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
theorem weightIntegral_eq {k : ℕ} (hk : 4 < k) :
    weightIntegral k = ENNReal.ofReal (∫ u, radialWeight k u) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_radialWeight hk)
    (Eventually.of_forall (radialWeight_nonneg k))]
  rfl
def productWeight (k : ℕ) {a : ℕ} (w : PointTuple a) : ℝ := ∏ t, radialWeight k (w t)
theorem productWeight_nonneg (k : ℕ) {a : ℕ} (w : PointTuple a) : 0 ≤ productWeight k w :=
  Finset.prod_nonneg fun t _ => radialWeight_nonneg k (w t)
theorem integrable_productWeight {k : ℕ} (hk : 4 < k) (a : ℕ) :
    Integrable (productWeight k : PointTuple a → ℝ) :=
  Integrable.fintype_prod_dep (f := fun _ : Fin a => radialWeight k) fun _ =>
    integrable_radialWeight hk
theorem integral_productWeight (k a : ℕ) :
    ∫ w : PointTuple a, productWeight k w = (∫ u, radialWeight k u) ^ a := by
  have h := integral_fintype_prod_volume_eq_pow (ι := Fin a) (radialWeight k)
  simpa [productWeight] using h
section Split
variable (A : Finset (Fin n))
theorem continuous_mergeTuples (y : PointTuple (n - A.card)) :
    Continuous (mergeTuples A y) := by
  refine continuous_pi fun i => ?_
  by_cases h : i ∈ A
  · simp only [mergeTuples, dif_pos h]
    exact continuous_apply _
  · simp only [mergeTuples, dif_neg h]
    exact continuous_const
def fiberEmbedding : PointTuple (n - A.card) →L[ℝ] PointTuple n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => mergeTuples A y 0
      map_add' := fun y y' => by
        funext i
        by_cases h : i ∈ A <;> simp [mergeTuples, h]
      map_smul' := fun c y => by
        funext i
        by_cases h : i ∈ A <;> simp [mergeTuples, h] }
theorem mergeTuples_eq_add (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    mergeTuples A y w = fiberEmbedding A y + mergeTuples A 0 w := by
  funext i
  change mergeTuples A y w i = mergeTuples A y 0 i + mergeTuples A 0 w i
  by_cases h : i ∈ A <;> simp [mergeTuples, h]
theorem hasFDerivAt_fiber {g : PointTuple n → ℂ} (hg : Differentiable ℝ g)
    (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    HasFDerivAt (fun y' => g (mergeTuples A y' w))
      ((fderiv ℝ g (mergeTuples A y w)).comp (fiberEmbedding A)) y := by
  have hP : HasFDerivAt (fun y' => mergeTuples A y' w) (fiberEmbedding A) y := by
    have h : (fun y' => mergeTuples A y' w) =
        fun y' => fiberEmbedding A y' + mergeTuples A 0 w :=
      funext fun y' => mergeTuples_eq_add A y' w
    rw [h]
    exact (fiberEmbedding A).hasFDerivAt.add_const _
  exact (hg _).hasFDerivAt.comp y hP
def complIndex (t : Fin (n - A.card)) : Fin n := Aᶜ.orderEmbOfFin (card_compl_indices A) t
theorem complIndex_notMem (t : Fin (n - A.card)) : complIndex A t ∉ A :=
  Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ t)
theorem complIndex_strictMono : StrictMono (complIndex A) :=
  (Aᶜ.orderEmbOfFin (card_compl_indices A)).strictMono
theorem mergeTuples_complIndex (y : PointTuple (n - A.card)) (w : PointTuple A.card)
    (t : Fin (n - A.card)) : mergeTuples A y w (complIndex A t) = y t :=
  congrFun (restrictToCompl_mergeTuples A y w) t
theorem fiberEmbedding_basis (t : Fin (n - A.card)) (μ : Fin 4) :
    fiberEmbedding A (Pi.single t (Pi.single μ 1)) =
      (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n) := by
  have hrem : restrictToCompl A
      (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n) =
      Pi.single t (Pi.single μ 1) := by
    funext s
    change (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n) (complIndex A s) = _
    by_cases hs : s = t
    · subst hs
      simp
    · rw [Pi.single_eq_of_ne ((complIndex_strictMono A).injective.ne hs),
        Pi.single_eq_of_ne hs]
  have hsel : restrictTo A
      (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n) = 0 := by
    funext s
    change (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n)
      (A.orderEmbOfFin rfl s) = 0
    refine Pi.single_eq_of_ne (fun e => complIndex_notMem A t ?_) _
    rw [← e]
    exact Finset.orderEmbOfFin_mem A rfl s
  have h := mergeTuples_restrictToCompl_restrictTo A
    (Pi.single (complIndex A t) (Pi.single μ 1) : PointTuple n)
  rw [hrem, hsel] at h
  exact h
theorem weight_le_split (k : ℕ) (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    (1 + tupleNorm (mergeTuples A y w) ^ 2) ^ (-((k * n : ℕ) : ℝ) / 2) ≤
      (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) * productWeight k w := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = -(k : ℝ) / 2 := ⟨_, rfl⟩
  have he0 : e ≤ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [he]
    linarith
  have hsq := tupleNorm_sq_eq_compl_add A (mergeTuples A y w)
  rw [restrictToCompl_mergeTuples, restrictTo_mergeTuples] at hsq
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + tupleNorm (mergeTuples A y w) ^ 2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + tupleNorm y ^ 2 := ⟨_, rfl⟩
  rw [← hs, ← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  have hs0 : 0 < s := by rw [hs]; positivity
  have hus : u ≤ s := by
    have := sq_nonneg (tupleNorm w)
    rw [hs, hu, hsq]
    linarith
  have ha : A.card ≤ n := by simpa using A.card_le_univ
  have h1 : s ^ (-((k * n : ℕ) : ℝ) / 2) = (s ^ e) ^ (n - A.card) * (s ^ e) ^ A.card := by
    rw [← pow_add, Nat.sub_add_cancel ha, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    congr 1
    rw [Nat.cast_mul, he]
    ring
  have h2 : u ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) = (u ^ e) ^ (n - A.card) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
    congr 1
    rw [Nat.cast_mul, he]
    ring
  have h3 : (s ^ e) ^ A.card ≤ productWeight k w := by
    have hc : (s ^ e) ^ A.card = ∏ _t : Fin A.card, s ^ e := by simp
    rw [hc]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun t _ => ?_
    unfold radialWeight
    rw [← he]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ he0
    have hle : TorusMetric.euclidNormVec (w t) ^ 2 ≤ tupleNorm w ^ 2 := by
      rw [tupleNorm_sq]
      exact Finset.single_le_sum (f := fun i => TorusMetric.euclidNormVec (w i) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ t)
    have := sq_nonneg (tupleNorm y)
    rw [hs, hsq]
    linarith
  rw [h1, h2]
  exact mul_le_mul
    (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow_of_nonpos hu0 hus he0) _) h3
    (by positivity) (by positivity)
end Split
section Fibers
variable {φ : PointTuple n → ℂ} (A : Finset (Fin n))
theorem norm_multiDeriv_le_of_seminorm {K : ℕ} (hfin : weightedSeminorm K φ ≠ ⊤)
    {α : MultiIdx4 n} (hα : idxOrder α ≤ K) (x : PointTuple n) :
    ‖multiDeriv α φ x‖ ≤
      (weightedSeminorm K φ).toReal * (1 + tupleNorm x ^ 2) ^ (-(K : ℝ) / 2) := by
  have h : ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((K : ℝ) / 2) *
      ‖multiDeriv α φ x‖) ≤ weightedSeminorm K φ := by
    unfold weightedSeminorm
    exact le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
  have h' := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h
  have hpos : 0 < (1 + tupleNorm x ^ 2) ^ ((K : ℝ) / 2) := by positivity
  rw [neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h'
theorem norm_fiber_le {k : ℕ} (hfin : weightedSeminorm (k * n) φ ≠ ⊤) {α : MultiIdx4 n}
    (hα : idxOrder α ≤ k * n) (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    ‖multiDeriv α φ (mergeTuples A y w)‖ ≤
      (weightedSeminorm (k * n) φ).toReal *
        ((1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) * productWeight k w) :=
  (norm_multiDeriv_le_of_seminorm hfin hα _).trans
    (mul_le_mul_of_nonneg_left (weight_le_split A k y w) ENNReal.toReal_nonneg)
theorem norm_fiber_le_productWeight {k : ℕ} (hfin : weightedSeminorm (k * n) φ ≠ ⊤)
    {α : MultiIdx4 n} (hα : idxOrder α ≤ k * n) (y : PointTuple (n - A.card))
    (w : PointTuple A.card) :
    ‖multiDeriv α φ (mergeTuples A y w)‖ ≤
      (weightedSeminorm (k * n) φ).toReal * productWeight k w := by
  refine (norm_fiber_le A hfin hα y w).trans
    (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  have hU : (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
    · have := sq_nonneg (tupleNorm y)
      linarith
    · have : (0 : ℝ) ≤ ((k * (n - A.card) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  exact (mul_le_mul_of_nonneg_right hU (productWeight_nonneg k w)).trans_eq (one_mul _)
theorem weightedSeminorm_ne_top (hφ : φ ∈ schwartzSet n) {K : ℕ} (hK : 0 < K) :
    weightedSeminorm K φ ≠ ⊤ :=
  (hφ.2 K hK).ne
theorem le_shift_mul (hn : 0 < n) (j : ℕ) : j ≤ (5 + j) * n :=
  (by omega : j ≤ 5 + j).trans (Nat.le_mul_of_pos_right _ hn)
variable (hC : RulesOver ℂ) (hφ : φ ∈ schwartzSet n) (hn : 0 < n)
include hC hφ
theorem contDiff_multiDeriv (β : MultiIdx4 n) : ContDiff ℝ ∞ (multiDeriv β φ) :=
  (hC n φ hφ.1).2.2.1 β
include hn
theorem integrable_fiber (β : MultiIdx4 n) (y : PointTuple (n - A.card)) :
    Integrable fun w : PointTuple A.card => multiDeriv β φ (mergeTuples A y w) := by
  have hk : 4 < 5 + idxOrder β := by omega
  have hfin : weightedSeminorm ((5 + idxOrder β) * n) φ ≠ ⊤ :=
    weightedSeminorm_ne_top hφ (Nat.mul_pos (by omega) hn)
  refine ((integrable_productWeight hk A.card).const_mul
    (weightedSeminorm ((5 + idxOrder β) * n) φ).toReal).mono' ?_
    (Eventually.of_forall fun w =>
      norm_fiber_le_productWeight A hfin (le_shift_mul hn _) y w)
  exact ((contDiff_multiDeriv hC hφ β).continuous.comp
    (continuous_mergeTuples A y)).aestronglyMeasurable
theorem hasFDerivAt_integrateOut (β : MultiIdx4 n) (y : PointTuple (n - A.card)) :
    HasFDerivAt (integrateOut A (multiDeriv β φ))
      (∫ w : PointTuple A.card,
        (fderiv ℝ (multiDeriv β φ) (mergeTuples A y w)).comp (fiberEmbedding A)) y ∧
    Integrable fun w : PointTuple A.card =>
      (fderiv ℝ (multiDeriv β φ) (mergeTuples A y w)).comp (fiberEmbedding A) := by
  have hg := contDiff_multiDeriv hC hφ β
  have hdiff : Differentiable ℝ (multiDeriv β φ) := hg.differentiable (by simp)
  have hk : 4 < 5 + (idxOrder β + 1) := by omega
  have hfin : weightedSeminorm ((5 + (idxOrder β + 1)) * n) φ ≠ ⊤ :=
    weightedSeminorm_ne_top hφ (Nat.mul_pos (by omega) hn)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (weightedSeminorm ((5 + (idxOrder β + 1)) * n) φ).toReal :=
    ⟨_, rfl⟩
  have hcont : ∀ y' : PointTuple (n - A.card), Continuous fun w : PointTuple A.card =>
      (fderiv ℝ (multiDeriv β φ) (mergeTuples A y' w)).comp (fiberEmbedding A) :=
    fun y' => ((hg.continuous_fderiv (by simp)).comp
      (continuous_mergeTuples A y')).clm_comp continuous_const
  have hbound : ∀ (y' : PointTuple (n - A.card)) (w : PointTuple A.card),
      ‖(fderiv ℝ (multiDeriv β φ) (mergeTuples A y' w)).comp (fiberEmbedding A)‖ ≤
        ((n : ℝ) * 4) * (M * productWeight (5 + (idxOrder β + 1)) w) *
          ‖fiberEmbedding A‖ := by
    intro y' w
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_clm_le_sum_basis _).trans ?_
    have hterm : ∀ (i : Fin n) (μ : Fin 4),
        ‖fderiv ℝ (multiDeriv β φ) (mergeTuples A y' w)
          (Pi.single i (Pi.single μ 1))‖ ≤ M * productWeight (5 + (idxOrder β + 1)) w := by
      intro i μ
      have hl := (hdiff (mergeTuples A y' w)).lineDeriv_eq_fderiv
        (v := (Pi.single i (Pi.single μ 1) : PointTuple n))
      rw [← hl]
      change ‖coordDeriv i μ (multiDeriv β φ) (mergeTuples A y' w)‖ ≤ _
      rw [coordDeriv_multiDeriv hC hφ.1, hM]
      refine norm_fiber_le_productWeight A hfin ?_ y' w
      rw [idxOrder_add, idxOrder_basisIdx, add_comm]
      exact le_shift_mul hn _
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hterm i μ).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hbi : Integrable fun w : PointTuple A.card =>
      ((n : ℝ) * 4) * (M * productWeight (5 + (idxOrder β + 1)) w) * ‖fiberEmbedding A‖ :=
    (((integrable_productWeight hk A.card).const_mul M).const_mul _).mul_const _
  refine ⟨?_, hbi.mono' (hcont y).aestronglyMeasurable
    (Eventually.of_forall (hbound y))⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y' w => multiDeriv β φ (mergeTuples A y' w))
    (F' := fun y' w =>
      (fderiv ℝ (multiDeriv β φ) (mergeTuples A y' w)).comp (fiberEmbedding A))
    (s := Set.univ) univ_mem
    (Eventually.of_forall fun y' =>
      (hg.continuous.comp (continuous_mergeTuples A y')).aestronglyMeasurable)
    (integrable_fiber A hC hφ hn β y) (hcont y).aestronglyMeasurable
    (Eventually.of_forall fun w y' _ => hbound y' w) hbi
    (Eventually.of_forall fun w y' _ => hasFDerivAt_fiber A hdiff y' w)
theorem coordDeriv_integrateOut (β : MultiIdx4 n) (t : Fin (n - A.card)) (μ : Fin 4) :
    coordDeriv t μ (integrateOut A (multiDeriv β φ)) =
      integrateOut A (multiDeriv (basisIdx (complIndex A t) μ + β) φ) := by
  funext y
  obtain ⟨hd, hi⟩ := hasFDerivAt_integrateOut A hC hφ hn β y
  have hdiff : Differentiable ℝ (multiDeriv β φ) :=
    (contDiff_multiDeriv hC hφ β).differentiable (by simp)
  change lineDeriv ℝ _ y _ = _
  rw [(hd.hasLineDerivAt _).lineDeriv, ContinuousLinearMap.integral_apply hi]
  unfold integrateOut
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change fderiv ℝ (multiDeriv β φ) (mergeTuples A y w)
    (fiberEmbedding A (Pi.single t (Pi.single μ 1))) = _
  rw [fiberEmbedding_basis, ← coordDeriv_multiDeriv hC hφ.1]
  exact ((hdiff (mergeTuples A y w)).lineDeriv_eq_fderiv).symm
theorem contDiff_integrateOut (N : ℕ) : ∀ β : MultiIdx4 n,
    ContDiff ℝ N (integrateOut A (multiDeriv β φ)) := by
  induction N with
  | zero =>
    intro β
    have hdiff : Differentiable ℝ (integrateOut A (multiDeriv β φ)) :=
      fun y => (hasFDerivAt_integrateOut A hC hφ hn β y).1.differentiableAt
    simpa using hdiff.continuous
  | succ N ih =>
    intro β
    have hdiff : Differentiable ℝ (integrateOut A (multiDeriv β φ)) :=
      fun y => (hasFDerivAt_integrateOut A hC hφ hn β y).1.differentiableAt
    have hcast : ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast]
    refine contDiff_succ_iff_fderiv_apply.2 ⟨hdiff, by simp, fun v => ?_⟩
    have hsum : (fun y => fderiv ℝ (integrateOut A (multiDeriv β φ)) y v) =
        fun y => ∑ t, ∑ μ, v t μ • integrateOut A
          (multiDeriv (basisIdx (complIndex A t) μ + β) φ) y := by
      funext y
      rw [clm_apply_eq_sum_basis]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun μ _ => ?_
      rw [← coordDeriv_integrateOut A hC hφ hn β t μ]
      exact congrArg _ ((hdiff y).lineDeriv_eq_fderiv).symm
    rw [hsum]
    exact ContDiff.sum fun t _ => ContDiff.sum fun μ _ => (ih _).const_smul (v t μ)
omit hC hφ hn in
def IsIntegratedDeriv (φ : PointTuple n → ℂ) (A : Finset (Fin n)) (j : ℕ)
    (h : PointTuple (n - A.card) → ℂ) : Prop :=
  ∃ β : MultiIdx4 n, idxOrder β = j ∧ h = integrateOut A (multiDeriv β φ)
theorem IsIntegratedDeriv.deriv_coord {j : ℕ} {h : PointTuple (n - A.card) → ℂ}
    (hh : IsIntegratedDeriv φ A j h) (t : Fin (n - A.card)) (μ : Fin 4) :
    IsIntegratedDeriv φ A (j + 1) (coordDeriv t μ h) := by
  obtain ⟨β, hβ, rfl⟩ := hh
  exact ⟨basisIdx (complIndex A t) μ + β,
    by rw [idxOrder_add, idxOrder_basisIdx, hβ, add_comm], coordDeriv_integrateOut A hC hφ hn β t μ⟩
theorem IsIntegratedDeriv.iterate_coord {j : ℕ} {h : PointTuple (n - A.card) → ℂ}
    (hh : IsIntegratedDeriv φ A j h) (t : Fin (n - A.card)) (μ : Fin 4) (c : ℕ) :
    IsIntegratedDeriv φ A (j + c) ((coordDeriv t μ)^[c] h) := by
  induction c with
  | zero => simpa using hh
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact IsIntegratedDeriv.deriv_coord A hC hφ hn ih t μ
theorem IsIntegratedDeriv.foldr_coords {j : ℕ} {h : PointTuple (n - A.card) → ℂ}
    (hh : IsIntegratedDeriv φ A j h) (α : MultiIdx4 (n - A.card))
    (t : Fin (n - A.card)) (l : List (Fin 4)) :
    IsIntegratedDeriv φ A (j + (l.map (α t)).sum)
      (l.foldr (fun μ h' => (coordDeriv t μ)^[α t μ] h') h) := by
  induction l with
  | nil => simpa using hh
  | cons μ l ih =>
    have h' := IsIntegratedDeriv.iterate_coord A hC hφ hn ih t μ (α t μ)
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    rwa [show j + (α t μ + (l.map (α t)).sum) = j + (l.map (α t)).sum + α t μ by omega]
theorem IsIntegratedDeriv.foldr_points {j : ℕ} {h : PointTuple (n - A.card) → ℂ}
    (hh : IsIntegratedDeriv φ A j h) (α : MultiIdx4 (n - A.card))
    (l : List (Fin (n - A.card))) :
    IsIntegratedDeriv φ A
      (j + (l.map fun t => ((List.finRange 4).map (α t)).sum).sum)
      (l.foldr (fun t h' =>
        (List.finRange 4).foldr (fun μ h'' => (coordDeriv t μ)^[α t μ] h'') h') h) := by
  induction l with
  | nil => simpa using hh
  | cons t l ih =>
    have h' := IsIntegratedDeriv.foldr_coords A hC hφ hn ih α t (List.finRange 4)
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    rwa [show j + (((List.finRange 4).map (α t)).sum +
        (l.map fun t => ((List.finRange 4).map (α t)).sum).sum) =
      j + (l.map fun t => ((List.finRange 4).map (α t)).sum).sum +
        ((List.finRange 4).map (α t)).sum by omega]
theorem exists_multiDeriv_eq (α : MultiIdx4 (n - A.card)) :
    ∃ β : MultiIdx4 n, idxOrder β = idxOrder α ∧
      multiDeriv α (integrateOut A φ) = integrateOut A (multiDeriv β φ) := by
  have h0 : IsIntegratedDeriv φ A 0 (integrateOut A φ) :=
    ⟨0, by simp [idxOrder], by rw [multiDeriv_zero]⟩
  have h := IsIntegratedDeriv.foldr_points A hC hφ hn h0 α (List.finRange (n - A.card))
  have hord : 0 + ((List.finRange (n - A.card)).map
      fun t => ((List.finRange 4).map (α t)).sum).sum = idxOrder α := by
    simp only [idxOrder, Fin.sum_univ_def, zero_add]
  rw [hord] at h
  exact h
omit hC in
theorem norm_integrateOut_le {k : ℕ} (hk : 4 < k) {β : MultiIdx4 n} (hβ : idxOrder β ≤ k * n)
    (y : PointTuple (n - A.card)) :
    ‖integrateOut A (multiDeriv β φ) y‖ ≤
      (weightedSeminorm (k * n) φ).toReal *
        (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) *
        (∫ u, radialWeight k u) ^ A.card := by
  have hfin : weightedSeminorm (k * n) φ ≠ ⊤ :=
    weightedSeminorm_ne_top hφ (Nat.mul_pos (by omega) hn)
  have hi := ((integrable_productWeight hk A.card).const_mul
    ((1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2))).const_mul
    (weightedSeminorm (k * n) φ).toReal
  refine (norm_integral_le_of_norm_le hi
    (Eventually.of_forall fun w => norm_fiber_le A hfin hβ y w)).trans_eq ?_
  rw [integral_const_mul, integral_const_mul, integral_productWeight]
  ring
theorem weighted_multiDeriv_integrateOut_le {k : ℕ} (hk : 4 < k) {α : MultiIdx4 (n - A.card)}
    (hα : idxOrder α ≤ k * n) (y : PointTuple (n - A.card)) :
    (1 + tupleNorm y ^ 2) ^ (((k * (n - A.card) : ℕ) : ℝ) / 2) *
        ‖multiDeriv α (integrateOut A φ) y‖ ≤
      (∫ u, radialWeight k u) ^ A.card * (weightedSeminorm (k * n) φ).toReal := by
  obtain ⟨β, hβ, hEq⟩ := exists_multiDeriv_eq A hC hφ hn α
  rw [hEq]
  have hb := norm_integrateOut_le A hφ hn hk (hβ.le.trans hα) y
  have hu : 0 < 1 + tupleNorm y ^ 2 := by positivity
  have hmul : (1 + tupleNorm y ^ 2) ^ (((k * (n - A.card) : ℕ) : ℝ) / 2) *
      (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hu]
    simp [neg_div]
  calc _ ≤ (1 + tupleNorm y ^ 2) ^ (((k * (n - A.card) : ℕ) : ℝ) / 2) *
        ((weightedSeminorm (k * n) φ).toReal *
          (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2) *
          (∫ u, radialWeight k u) ^ A.card) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((1 + tupleNorm y ^ 2) ^ (((k * (n - A.card) : ℕ) : ℝ) / 2) *
          (1 + tupleNorm y ^ 2) ^ (-((k * (n - A.card) : ℕ) : ℝ) / 2)) *
        ((∫ u, radialWeight k u) ^ A.card * (weightedSeminorm (k * n) φ).toReal) := by ring
    _ = _ := by rw [hmul, one_mul]
end Fibers
section Bounds
variable {φ : PointTuple n → ℂ} (A : Finset (Fin n))
theorem integral_radialWeight_nonneg (k : ℕ) : 0 ≤ ∫ u, radialWeight k u :=
  integral_nonneg (radialWeight_nonneg k)
theorem ofReal_integral_pow_mul {k K : ℕ} (hk : 4 < k) (hfin : weightedSeminorm K φ ≠ ⊤)
    (a : ℕ) :
    ENNReal.ofReal ((∫ u, radialWeight k u) ^ a * (weightedSeminorm K φ).toReal) =
      weightIntegral k ^ a * weightedSeminorm K φ := by
  rw [ENNReal.ofReal_mul (pow_nonneg (integral_radialWeight_nonneg k) a),
    ENNReal.ofReal_pow (integral_radialWeight_nonneg k), ENNReal.ofReal_toReal hfin,
    weightIntegral_eq hk]
variable (hC : RulesOver ℂ) (hφ : φ ∈ flatSchwartzSet n) (hn : 0 < n)
include hC hφ hn
theorem integrateOut_mem_schwartzSet (ha : A.card < n) :
    integrateOut A φ ∈ schwartzSet (n - A.card) := by
  have hS := hφ.1
  refine ⟨contDiff_infty.2 fun N => ?_, fun k' hk' => ?_⟩
  · have h := contDiff_integrateOut A hC hS hn N 0
    rwa [multiDeriv_zero] at h
  · have hk : 4 < 5 + k' := by omega
    have hm : 0 < n - A.card := by omega
    have hle : k' ≤ (5 + k') * (n - A.card) :=
      (by omega : k' ≤ 5 + k').trans (Nat.le_mul_of_pos_right _ hm)
    have hkn : (5 + k') * (n - A.card) ≤ (5 + k') * n := Nat.mul_le_mul_left _ (by omega)
    have hbound : weightedSeminorm k' (integrateOut A φ) ≤
        ENNReal.ofReal ((∫ u, radialWeight (5 + k') u) ^ A.card *
          (weightedSeminorm ((5 + k') * n) φ).toReal) := by
      refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
      refine le_trans ?_ (weighted_multiDeriv_integrateOut_le A hC hS hn hk
        (hα.trans (hle.trans hkn)) x)
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · have := sq_nonneg (tupleNorm x)
        linarith
      · have : (k' : ℝ) ≤ (((5 + k') * (n - A.card) : ℕ) : ℝ) := by exact_mod_cast hle
        linarith
    exact hbound.trans_lt ENNReal.ofReal_lt_top
theorem multiDeriv_integrateOut_eq_zero (α : MultiIdx4 (n - A.card))
    (y : PointTuple (n - A.card)) (hy : y ∈ diagonalLocus (n - A.card)) :
    multiDeriv α (integrateOut A φ) y = 0 := by
  obtain ⟨β, -, hEq⟩ := exists_multiDeriv_eq A hC hφ.1 hn α
  rw [hEq]
  obtain ⟨t, t', htt, hyt⟩ := (mem_diagonalLocus_iff y).1 hy
  unfold integrateOut
  have hz : ∀ w : PointTuple A.card, multiDeriv β φ (mergeTuples A y w) = 0 := by
    intro w
    refine hφ.2 β _ ((mem_diagonalLocus_iff _).2
      ⟨complIndex A t, complIndex A t', complIndex_strictMono A htt, ?_⟩)
    rw [mergeTuples_complIndex, mergeTuples_complIndex, hyt]
  simp [hz]
theorem weightedSeminorm_integrateOut_le {k : ℕ} (hk : 4 < k) :
    weightedSeminorm (k * (n - A.card)) (integrateOut A φ) ≤
      weightIntegral k ^ A.card * weightedSeminorm (k * n) φ := by
  have hfin : weightedSeminorm (k * n) φ ≠ ⊤ :=
    weightedSeminorm_ne_top hφ.1 (Nat.mul_pos (by omega) hn)
  rw [← ofReal_integral_pow_mul hk hfin]
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
  exact weighted_multiDeriv_integrateOut_le A hC hφ.1 hn hk
    (hα.trans (Nat.mul_le_mul_left _ (by omega))) x
theorem integrable_of_flat : Integrable φ := by
  have hy : (fun _ => 0 : PointTuple (n - (Finset.univ : Finset (Fin n)).card)) ∈
      integrableFibers Finset.univ φ := by
    have h := integrable_fiber Finset.univ hC hφ.1 hn 0 (fun _ => 0)
    rw [multiDeriv_zero] at h
    exact h
  exact (mem_integrableFibers_univ φ _).1 hy
omit hC in
theorem norm_integral_le {k : ℕ} (hk : 4 < k) :
    ENNReal.ofReal ‖∫ x, φ x‖ ≤ weightIntegral k ^ n * weightedSeminorm (k * n) φ := by
  have hfin : weightedSeminorm (k * n) φ ≠ ⊤ :=
    weightedSeminorm_ne_top hφ.1 (Nat.mul_pos (by omega) hn)
  rw [← ofReal_integral_pow_mul hk hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := norm_integrateOut_le Finset.univ hφ.1 hn hk (β := 0) (by simp [idxOrder])
    (fun _ => 0)
  rw [multiDeriv_zero, integrateOut_univ] at hb
  refine hb.trans ?_
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hU : ∀ (m c : ℕ) (y : PointTuple m), (1 + tupleNorm y ^ 2) ^ (-(c : ℝ) / 2) ≤ 1 := by
    intro m c y
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
    · have := sq_nonneg (tupleNorm y)
      linarith
    · have : (0 : ℝ) ≤ c := Nat.cast_nonneg _
      linarith
  rw [hcard, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (integral_radialWeight_nonneg k) n)
  exact (mul_le_mul_of_nonneg_left (hU _ _ _) ENNReal.toReal_nonneg).trans_eq (mul_one _)
end Bounds
end IntegrateOut
theorem integrateOutBounds_of_derivRules (h : DerivRules.Combined) : IntegrateOutBounds := by
  intro n k hn hk φ hφ A
  have hC := h.2.1
  refine ⟨fun ha => ⟨fun _ y => ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have hi := IntegrateOut.integrable_fiber A hC hφ.1 hn 0 y
    rw [IntegrateOut.multiDeriv_zero] at hi
    exact hi
  · exact IntegrateOut.integrateOut_mem_schwartzSet A hC hφ hn ha
  · exact fun α x hx => IntegrateOut.multiDeriv_integrateOut_eq_zero A hC hφ hn α x hx
  · exact IntegrateOut.weightedSeminorm_integrateOut_le A hC hφ hn hk
  · exact IntegrateOut.integrable_of_flat hC hφ hn
  · exact IntegrateOut.norm_integral_le hφ hn hk
end YangMills.Construction.TestSpaces
