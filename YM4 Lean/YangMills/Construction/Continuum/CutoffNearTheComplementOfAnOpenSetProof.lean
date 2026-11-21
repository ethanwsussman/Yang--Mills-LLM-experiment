import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinityProof
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.CutoffNearTheComplementOfAnOpenSet
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
namespace CompactSuppCutoff
open DerivRules
variable {n : ℕ}
theorem foldr_eq_self_of_forall_fix {A B : Type*} (f : A → B → B) (b : B) (l : List A)
    (hfix : ∀ c ∈ l, ∀ y, f c y = y) : l.foldr f b = b := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    rw [List.foldr_cons, ih fun d hd => hfix d (List.mem_cons_of_mem _ hd)]
    exact hfix c (by simp) b
theorem foldr_eq_apply_of_unique_nonfix {A B : Type*} (f : A → B → B) (a : A) (b : B)
    (l : List A) (hnd : l.Nodup) (ha : a ∈ l) (hfix : ∀ c ∈ l, c ≠ a → ∀ y, f c y = y) :
    l.foldr f b = f a b := by
  induction l with
  | nil => cases ha
  | cons c t ih =>
    rw [List.foldr_cons]
    by_cases hca : c = a
    · subst hca
      rw [foldr_eq_self_of_forall_fix f b t fun d hd => hfix d (List.mem_cons_of_mem _ hd)
        fun h => (List.nodup_cons.1 hnd).1 (h ▸ hd)]
    · have hat : a ∈ t := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hca
        · exact h
      rw [hfix c (by simp) hca,
        ih (List.nodup_cons.1 hnd).2 hat fun d hd => hfix d (List.mem_cons_of_mem _ hd)]
def coordIdx (i : Fin n) (μ : Fin 4) : MultiIdx4 n := Pi.single i (Pi.single μ 1)
theorem multiDeriv_coordIdx {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (μ : Fin 4) (g : PointTuple n → F) :
    multiDeriv (coordIdx i μ) g = coordDeriv i μ g := by
  unfold multiDeriv
  have hout := foldr_eq_apply_of_unique_nonfix
    (fun i' h => (List.finRange 4).foldr
      (fun μ' h' => (coordDeriv i' μ')^[coordIdx i μ i' μ'] h') h)
    i g (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i)
    (fun j _ hj y => foldr_eq_self_of_forall_fix _ y _ fun ν _ y' => by simp [coordIdx, hj])
  have hin := foldr_eq_apply_of_unique_nonfix
    (fun μ' h' => (coordDeriv i μ')^[coordIdx i μ i μ'] h')
    μ g (List.finRange 4) (List.nodup_finRange 4) (List.mem_finRange μ)
    (fun ν _ hν y => by simp [coordIdx, hν])
  refine hout.trans (hin.trans ?_)
  simp [coordIdx]
theorem norm_le_tupleNorm (v : PointTuple n) : ‖v‖ ≤ tupleNorm v := by apply _root_.YangMills.SharedProofs.p25561 <;> assumption
theorem continuous_tupleNorm : Continuous fun x : PointTuple n => tupleNorm x := by apply _root_.YangMills.Construction.TestSpaces.SchwartzTruncation.continuous_tupleNorm <;> assumption
theorem eq_sum_smul_single (v : PointTuple n) :
    v = ∑ i, ∑ μ, v i μ • (Pi.single i (Pi.single μ 1) : PointTuple n) := by
  ext j ν
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [hμ.symm]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun μ _ => ?_
    simp [hi.symm]
  · simp
theorem idxOrder_mono {γ α : MultiIdx4 n} (h : γ ≤ α) : idxOrder γ ≤ idxOrder α :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => h i μ
theorem multiDeriv_eq_zero_of_notMem_tsupport (Rc : RulesOver ℂ) {φ : PointTuple n → ℂ}
    (hsm : ContDiff ℝ ∞ φ) (α : MultiIdx4 n) {x : PointTuple n} (hx : x ∉ tsupport φ) :
    multiDeriv α φ x = 0 :=
  (Rc n φ hsm).2.2.2.2.2.2.2 (tsupport φ)ᶜ (isClosed_tsupport φ).isOpen_compl
    (fun _ hy => image_eq_zero_of_notMem_tsupport hy) α x hx
theorem exists_bound_multiDeriv (Rc : RulesOver ℂ) {φ : PointTuple n → ℂ}
    (hsm : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) (α : MultiIdx4 n) :
    ∃ C : ℝ, ∀ x, ‖multiDeriv α φ x‖ ≤ C := by
  have hc : Continuous (multiDeriv α φ) := ((Rc n φ hsm).2.2.1 α).continuous
  have hs : HasCompactSupport (multiDeriv α φ) :=
    HasCompactSupport.intro hcs fun x hx => multiDeriv_eq_zero_of_notMem_tsupport Rc hsm α hx
  exact hc.bounded_above_of_compact_support hs
theorem norm_multiDeriv_le_infDist_pow (Rc : RulesOver ℂ) {V : Set (PointTuple n)}
    {φ : PointTuple n → ℂ} (hcs : HasCompactSupport φ) (hflat : VanishesToInfiniteOrderOff φ V)
    (hne : (Vᶜ).Nonempty) (s : ℕ) :
    ∀ α : MultiIdx4 n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖multiDeriv α φ x‖ ≤ C * Metric.infDist x Vᶜ ^ s := by
  have hsm : ContDiff ℝ ∞ φ := hflat.1
  have hclosed : IsClosed Vᶜ := hflat.2.1.isClosed_compl
  induction s with
  | zero =>
    intro α
    obtain ⟨C, hC⟩ := exists_bound_multiDeriv Rc hsm hcs α
    exact ⟨|C|, abs_nonneg C, fun x => by simpa using (hC x).trans (le_abs_self C)⟩
  | succ s ih =>
    intro α
    choose C hC0 hC using fun (i : Fin n) (μ : Fin 4) => ih (coordIdx i μ + α)
    refine ⟨∑ i, ∑ μ, C i μ, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => hC0 i μ,
      fun x => ?_⟩
    have hgs : ContDiff ℝ ∞ (multiDeriv α φ) := (Rc n φ hsm).2.2.1 α
    have hgd : Differentiable ℝ (multiDeriv α φ) := hgs.differentiable (by simp)
    obtain ⟨z, hzV, hz⟩ := hclosed.exists_infDist_eq_dist hne x
    have hgz : multiDeriv α φ z = 0 := (hflat.2.2 z hzV).2.2 α
    have hpart : ∀ (i : Fin n) (μ : Fin 4) (y : PointTuple n),
        fderiv ℝ (multiDeriv α φ) y (Pi.single i (Pi.single μ 1)) =
          multiDeriv (coordIdx i μ + α) φ y := by
      intro i μ y
      rw [← (Rc n φ hsm).2.2.2.2.1 (coordIdx i μ) α, multiDeriv_coordIdx]
      exact ((Rc n _ hgs).1 i μ y).symm
    have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • (x - z)) (x - z) t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const (x - z)).const_add z
    have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => multiDeriv α φ (z + t • (x - z)))
        (fderiv ℝ (multiDeriv α φ) (z + t • (x - z)) (x - z)) t := fun t =>
      (hgd _).hasFDerivAt.comp_hasDerivAt t (hline t)
    have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖fderiv ℝ (multiDeriv α φ) (z + t • (x - z)) (x - z)‖ ≤
          (∑ i, ∑ μ, C i μ) * Metric.infDist x Vᶜ ^ (s + 1) := by
      intro t ht
      set y := z + t • (x - z) with hy
      have hdy : Metric.infDist y Vᶜ ≤ Metric.infDist x Vᶜ := by
        refine (Metric.infDist_le_dist_of_mem hzV).trans ?_
        rw [hz, dist_eq_norm, dist_eq_norm, hy, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      have hcoord : ∀ i μ, ‖(x - z) i μ‖ ≤ Metric.infDist x Vᶜ := by
        intro i μ
        rw [hz, dist_eq_norm]
        exact (norm_le_pi_norm ((x - z) i) μ).trans (norm_le_pi_norm (x - z) i)
      have hexp : fderiv ℝ (multiDeriv α φ) y (x - z) =
          ∑ i, ∑ μ, (x - z) i μ • multiDeriv (coordIdx i μ + α) φ y := by
        conv_lhs => rw [eq_sum_smul_single (x - z)]
        simp only [map_sum, map_smul, hpart]
      rw [hexp, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
      rw [norm_smul, pow_succ]
      have h1 : ‖multiDeriv (coordIdx i μ + α) φ y‖ ≤ C i μ * Metric.infDist x Vᶜ ^ s :=
        (hC i μ y).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ Metric.infDist_nonneg hdy s) (hC0 i μ))
      calc ‖(x - z) i μ‖ * ‖multiDeriv (coordIdx i μ + α) φ y‖
          ≤ Metric.infDist x Vᶜ * (C i μ * Metric.infDist x Vᶜ ^ s) :=
            mul_le_mul (hcoord i μ) h1 (norm_nonneg _) Metric.infDist_nonneg
        _ = C i μ * (Metric.infDist x Vᶜ ^ s * Metric.infDist x Vᶜ) := by ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun t : ℝ => multiDeriv α φ (z + t • (x - z)))
      (fun t _ => (hder t).hasDerivWithinAt) hbound
    simpa [hgz] using hmv
theorem norm_multiDeriv_cutoff_mul_le (k : ℕ) (Rr : RulesOver ℝ) (Leib : LeibnizProp)
    {φ : PointTuple n → ℂ} (hsm : ContDiff ℝ ∞ φ) {μ δ : PointTuple n → ℝ} (hμs : ContDiff ℝ ∞ μ)
    (hδc : Continuous δ) (hδ0 : ∀ x, 0 ≤ δ x) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hzero : ∀ x, 3 * e ≤ δ x → μ x = 0) {c C : MultiIdx4 n → ℝ} (hc0 : ∀ γ, 0 ≤ c γ)
    (hC0 : ∀ β, 0 ≤ C β) (hC : ∀ β x, ‖multiDeriv β φ x‖ ≤ C β * δ x ^ (k + 1))
    (hμd : ∀ γ x, |multiDeriv γ μ x| ≤ c γ * (e ^ idxOrder γ)⁻¹)
    (α : MultiIdx4 n) (x : PointTuple n) (hα : idxOrder α ≤ k) :
    ‖multiDeriv α (fun y => (μ y : ℂ) * φ y) x‖ ≤
      (∑ γ ∈ Finset.Icc 0 α, (idxChoose α γ : ℝ) * (c γ * (C (α - γ) * 3 ^ (k + 1)))) * e := by
  have hterm : ∀ (β γ : MultiIdx4 n), idxOrder γ ≤ k →
      |multiDeriv γ μ x| * ‖multiDeriv β φ x‖ ≤
        c γ * (C β * 3 ^ (k + 1)) * e := by
    intro β γ hγ
    have hcoef : 0 ≤ c γ * (C β * 3 ^ (k + 1)) :=
      mul_nonneg (hc0 γ) (mul_nonneg (hC0 β) (by positivity))
    by_cases hx : 3 * e < δ x
    · have h0 : multiDeriv γ μ x = 0 :=
        (Rr n μ hμs).2.2.2.2.2.2.2 {y | 3 * e < δ y} (isOpen_lt continuous_const hδc)
          (fun y hy => hzero y (le_of_lt hy)) γ x hx
      rw [h0, abs_zero, zero_mul]
      exact mul_nonneg hcoef he0.le
    · have hx' : δ x ≤ 3 * e := not_lt.1 hx
      have h1 := hμd γ x
      have h2 : ‖multiDeriv β φ x‖ ≤ C β * (3 * e) ^ (k + 1) :=
        (hC β x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hδ0 x) hx' _) (hC0 β))
      have h3 : (e ^ idxOrder γ)⁻¹ * e ^ (k + 1) ≤ e := by
        have hsplit : e ^ (k + 1) = e ^ idxOrder γ * (e ^ (k - idxOrder γ) * e) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        rw [hsplit, inv_mul_cancel_left₀ (pow_ne_zero _ he0.ne')]
        exact mul_le_of_le_one_left he0.le (pow_le_one₀ he0.le he1)
      calc |multiDeriv γ μ x| * ‖multiDeriv β φ x‖
          ≤ (c γ * (e ^ idxOrder γ)⁻¹) * (C β * (3 * e) ^ (k + 1)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (hc0 γ) (by positivity))
        _ = c γ * (C β * 3 ^ (k + 1)) * ((e ^ idxOrder γ)⁻¹ * e ^ (k + 1)) := by
            rw [mul_pow]
            ring
        _ ≤ c γ * (C β * 3 ^ (k + 1)) * e := mul_le_mul_of_nonneg_left h3 hcoef
  rw [Leib n μ φ hμs hsm α x]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun γ hγ => ?_
  have hord : idxOrder γ ≤ k := (idxOrder_mono (Finset.mem_Icc.1 hγ).2).trans hα
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, mul_assoc,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (hterm (α - γ) γ hord) (Nat.cast_nonneg _)
theorem exists_bound_of_idxOrder_le (k : ℕ) {M : MultiIdx4 n → ℝ} (hM0 : ∀ α, 0 ≤ M α) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ α, idxOrder α ≤ k → M α ≤ T := by
  refine ⟨∑ α ∈ Finset.Icc (0 : MultiIdx4 n) (fun _ _ => k), M α,
    Finset.sum_nonneg fun α _ => hM0 α, fun α hα => ?_⟩
  refine Finset.single_le_sum (f := M) (fun α _ => hM0 α) (Finset.mem_Icc.2 ⟨?_, ?_⟩)
  · intro i μ
    exact Nat.zero_le _
  · intro i μ
    refine le_trans ?_ hα
    calc α i μ ≤ ∑ ν, α i ν :=
          Finset.single_le_sum (f := fun ν => α i ν) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ μ)
      _ ≤ idxOrder α :=
          Finset.single_le_sum (f := fun i => ∑ ν, α i ν) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
theorem exists_weight_le_of_isCompact (k : ℕ) {K : Set (PointTuple n)} (hK : IsCompact K) :
    ∃ W : ℝ, 0 < W ∧ ∀ x ∈ K, (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) ≤ W := by
  have hcont : Continuous fun x : PointTuple n => (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) :=
    (continuous_const.add (continuous_tupleNorm.pow 2)).rpow_const fun x =>
      Or.inr (by positivity)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|B| + 1, by positivity, fun x hx => ?_⟩
  have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB x hx))
  have h2 := le_abs_self B
  linarith
theorem exists_small_scale {W T ε : ℝ} (hW0 : 0 < W) (hT0 : 0 ≤ T) (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ W * (T * e) ≤ ε := by
  have hWT : 0 < W * (T + 1) := mul_pos hW0 (by linarith)
  refine ⟨min 1 (ε / (W * (T + 1))), lt_min one_pos (div_pos hε hWT), min_le_left _ _, ?_⟩
  have he0 : 0 < min 1 (ε / (W * (T + 1))) := lt_min one_pos (div_pos hε hWT)
  have h1 : min 1 (ε / (W * (T + 1))) ≤ ε / (W * (T + 1)) := min_le_right _ _
  have h2 := (le_div_iff₀ hWT).1 h1
  nlinarith [mul_pos he0 hW0]
theorem exists_smooth_cutoff {j : PointTuple n → ℝ} (hfacts : ∀ Z : Set (PointTuple n),
      MeasurableSet Z → ∀ ε : ℝ, 0 < ε → BumpApprox.RegularizedIndicatorProps j Z ε)
    (V : Set (PointTuple n)) {e : ℝ} (he0 : 0 < e) :
    ∃ μ : PointTuple n → ℝ, ContDiff ℝ ∞ μ ∧ (∀ x, Metric.infDist x Vᶜ ≤ e → μ x = 1) ∧
      (∀ x, 3 * e ≤ Metric.infDist x Vᶜ → μ x = 0) ∧
      ∀ γ x, |multiDeriv γ μ x| ≤ BumpApprox.derivL1Mass j γ * (e ^ idxOrder γ)⁻¹ := by
  have hδc : Continuous fun x : PointTuple n => Metric.infDist x Vᶜ :=
    Metric.continuous_infDist_pt _
  have hZ : MeasurableSet {x : PointTuple n | Metric.infDist x Vᶜ < 2 * e} :=
    (isOpen_lt hδc continuous_const).measurableSet
  obtain ⟨-, hμs, -, hμ1, hμ0, hμd⟩ := hfacts _ hZ e he0
  have hnear : ∀ x y : PointTuple n, tupleNorm (y - x) < e → dist y x < e := fun x y h => by
    rw [dist_eq_norm]
    exact (norm_le_tupleNorm _).trans_lt h
  refine ⟨_, hμs, fun x hx => hμ1 x fun y hy => ?_, fun x hx => hμ0 x ?_, fun γ x => (hμd γ).2 x⟩
  · have h1 := hnear x y hy
    have h2 : Metric.infDist y Vᶜ ≤ Metric.infDist x Vᶜ + dist y x :=
      Metric.infDist_le_infDist_add_dist
    show Metric.infDist y Vᶜ < 2 * e
    linarith
  · refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have h1 := hnear x y hy.1
    have h2 : Metric.infDist x Vᶜ ≤ Metric.infDist y Vᶜ + dist x y :=
      Metric.infDist_le_infDist_add_dist
    have h3 : Metric.infDist y Vᶜ < 2 * e := hy.2
    rw [dist_comm] at h2
    linarith
theorem one_sub_cutoff_mul_mem {V : Set (PointTuple n)} {φ : PointTuple n → ℂ}
    (hsm : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) {μ : PointTuple n → ℝ}
    (hμs : ContDiff ℝ ∞ μ) {e : ℝ} (he0 : 0 < e)
    (hone : ∀ x, Metric.infDist x Vᶜ ≤ e → μ x = 1) :
    (fun y => (((1 - μ y : ℝ)) : ℂ) * φ y) ∈
      (smoothCompactSupp V : Set (PointTuple n → ℂ)) := by
  have hδc : Continuous fun x : PointTuple n => Metric.infDist x Vᶜ :=
    Metric.continuous_infDist_pt _
  refine ⟨(Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hμs)).mul hsm, ?_, ?_⟩
  · exact HasCompactSupport.intro hcs fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  · have hsub : tsupport (fun y => (((1 - μ y : ℝ)) : ℂ) * φ y) ⊆
        {x | e ≤ Metric.infDist x Vᶜ} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const hδc)
      by_contra h
      have h' : Metric.infDist x Vᶜ ≤ e := le_of_lt (not_le.1 h)
      exact hx (by simp [hone x h'])
    intro x hx
    by_contra hxV
    have h0 : Metric.infDist x Vᶜ = 0 := Metric.infDist_zero_of_mem hxV
    have h1 : e ≤ Metric.infDist x Vᶜ := hsub hx
    linarith
theorem exists_approx_of_compl_nonempty {n : ℕ} (k : ℕ) (hn : 0 < n) (Rr : RulesOver ℝ)
    (Rc : RulesOver ℂ) (Leib : LeibnizProp)
    (h₂ : BumpApprox.BumpLemma) {V : Set (PointTuple n)} {φ : PointTuple n → ℂ}
    (hcs : HasCompactSupport φ) (hflat : VanishesToInfiniteOrderOff φ V) (hne : (Vᶜ).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ₂ ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)),
      weightedSeminorm k (φ - φ₂) ≤ ENNReal.ofReal ε ∧
      ((∀ x, (φ x).im = 0) → ∀ x, (φ₂ x).im = 0) := by
  have hsm : ContDiff ℝ ∞ φ := hflat.1
  obtain ⟨⟨j, hj⟩, hfacts, -, -⟩ := h₂ n hn
  choose C hC0 hC using norm_multiDeriv_le_infDist_pow Rc hcs hflat hne (k + 1)
  have hc0 : ∀ γ, 0 ≤ BumpApprox.derivL1Mass j γ :=
    fun γ => integral_nonneg fun x => abs_nonneg _
  obtain ⟨T, hT0, hMT⟩ := exists_bound_of_idxOrder_le (n := n) k
    (M := fun α => ∑ γ ∈ Finset.Icc 0 α, (idxChoose α γ : ℝ) *
      (BumpApprox.derivL1Mass j γ * (C (α - γ) * 3 ^ (k + 1))))
    fun α => Finset.sum_nonneg fun γ _ =>
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hc0 γ) (mul_nonneg (hC0 _) (by positivity)))
  obtain ⟨W, hW0, hW⟩ := exists_weight_le_of_isCompact k hcs
  obtain ⟨e, he0, he1, heW⟩ := exists_small_scale hW0 hT0 hε
  obtain ⟨μ, hμs, hone, hzero, hμd⟩ := exists_smooth_cutoff (hfacts j hj) V he0
  have hnorm := norm_multiDeriv_cutoff_mul_le k Rr Leib hsm hμs (Metric.continuous_infDist_pt Vᶜ)
    (fun _ => Metric.infDist_nonneg) he0 he1 hzero hc0 hC0 hC hμd
  have hμc : ContDiff ℝ ∞ fun y => (μ y : ℂ) := Complex.ofRealCLM.contDiff.comp hμs
  have hdiff : φ - (fun y => (((1 - μ y : ℝ)) : ℂ) * φ y) = fun y => (μ y : ℂ) * φ y := by
    ext y
    simp only [Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  refine ⟨fun y => (((1 - μ y : ℝ)) : ℂ) * φ y, one_sub_cutoff_mul_mem hsm hcs hμs he0 hone, ?_, ?_⟩
  · rw [hdiff]
    refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
    by_cases hx : x ∈ tsupport φ
    · have h1 := (hnorm α x hα).trans (mul_le_mul_of_nonneg_right (hMT α hα) he0.le)
      exact (mul_le_mul (hW x hx) h1 (norm_nonneg _) hW0.le).trans heW
    · have h0 : multiDeriv α (fun y => (μ y : ℂ) * φ y) x = 0 :=
        (Rc n _ (hμc.mul hsm)).2.2.2.2.2.2.2 (tsupport φ)ᶜ (isClosed_tsupport φ).isOpen_compl
          (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy]) α x hx
      rw [h0, norm_zero, mul_zero]
      exact hε.le
  · intro hre x
    simp [Complex.mul_im, hre x]
end CompactSuppCutoff
open DerivRules in
theorem approxByCompactSuppInOpen_holds (h₁ : DerivRules.Combined)
    (h₂ : BumpApprox.BumpLemma) : approxByCompactSuppInOpen := by
  obtain ⟨Rr, Rc, Leib, -⟩ := h₁
  intro n k hn _ V φ hcs hflat ε hε
  by_cases hne : (Vᶜ).Nonempty
  · exact CompactSuppCutoff.exists_approx_of_compl_nonempty k hn Rr Rc Leib h₂ hcs hflat hne hε
  · have hV : V = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      exact Set.compl_empty_iff.1 hne
    refine ⟨φ, ⟨hflat.1, hcs, by simp [hV]⟩, ?_, fun h => h⟩
    rw [sub_self]
    refine iSup_le fun x => iSup_le fun α => iSup_le fun _ => ENNReal.ofReal_le_ofReal ?_
    have h0 : multiDeriv α (0 : PointTuple n → ℂ) x = 0 :=
      (Rc n 0 contDiff_const).2.2.2.2.2.2.2 Set.univ isOpen_univ (fun _ _ => rfl) α x trivial
    rw [h0, norm_zero, mul_zero]
    exact hε.le
end YangMills.Construction.TestSpaces
