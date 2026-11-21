import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Matrices.SeriesWithSummableMatrixCoefficients
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.FourierMatrixSeries
open YangMills.Construction.PeriodicOperators (castVec toComplexVec bilinDot torusAverage)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open scoped Matrix.Norms.L2Operator
theorem character_eq_prod (n : Fin 4 → ℤ) (x : AmbientSpace) :
    character n x = ∏ μ, Complex.exp (Complex.I * (n μ : ℂ) * (x μ : ℂ)) := by
  simp only [character, bilinDot, toComplexVec, castVec, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun μ _ => ?_
  simp [mul_assoc]
theorem character_add (n m : Fin 4 → ℤ) (x : AmbientSpace) :
    character (n + m) x = character n x * character m x := by
  simp only [character_eq_prod, ← Finset.prod_mul_distrib, ← Complex.exp_add]
  refine Finset.prod_congr rfl fun μ _ => ?_
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring
theorem norm_character (n : Fin 4 → ℤ) (x : AmbientSpace) : ‖character n x‖ = 1 := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_fourierChar <;> assumption
theorem continuous_character (n : Fin 4 → ℤ) : Continuous (character n) := by
  have : character n = fun x => ∏ μ, Complex.exp (Complex.I * (n μ : ℂ) * (x μ : ℂ)) :=
    funext (character_eq_prod n)
  rw [this]
  refine continuous_finsetProd _ fun μ _ => ?_
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply μ)))
theorem hasDerivAt_character_update (n : Fin 4 → ℤ) (x : AmbientSpace) (μ : Fin 4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => character n (Function.update x μ s))
      (character n (Function.update x μ t) * (Complex.I * (n μ : ℂ))) t := by
  have hd : HasDerivAt (fun s : ℝ => Complex.I *
      bilinDot (toComplexVec (castVec n)) (toComplexVec (Function.update x μ s)))
      (Complex.I * (n μ : ℂ)) t := by
    refine HasDerivAt.const_mul _ ?_
    have hterm : ∀ ν : Fin 4, HasDerivAt
        (fun s : ℝ => toComplexVec (castVec n) ν * toComplexVec (Function.update x μ s) ν)
        (if ν = μ then (n μ : ℂ) else 0) t := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp only [toComplexVec, castVec, Function.update_self, if_true]
        have := ((hasDerivAt_id t).ofReal_comp).const_mul (((n ν : ℝ) : ℂ))
        simpa using this
      · simp only [toComplexVec, Function.update_of_ne h, if_neg h]
        exact hasDerivAt_const _ _
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun ν _ => hterm ν)
    simpa [bilinDot] using hs
  have hc := (Complex.hasDerivAt_exp (Complex.I *
    bilinDot (toComplexVec (castVec n)) (toComplexVec (Function.update x μ t)))).scomp t hd
  simpa [character, Function.comp_def, smul_eq_mul, mul_comm] using hc
variable {N' N'' : ℕ} [NeZero N'] [NeZero N'']
theorem opNormValue_eq_norm (X : Matrix (Fin N') (Fin N'') ℂ) :
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue X = ‖X‖ :=
  (Matrix.l2_opNorm_def X).symm
omit [NeZero N'] [NeZero N''] in
theorem norm_entry_le_norm (X : Matrix (Fin N') (Fin N'') ℂ) (i : Fin N') (k : Fin N'') :
    ‖X i k‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single k (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single k (1 : ℂ) : EuclideanSpace ℂ (Fin N''))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin N') ℂ).symm
    (X.mulVec (EuclideanSpace.single k (1 : ℂ)))) i
  refine le_trans (le_of_eq ?_) h2
  simp
theorem absSummable_iff {a : CoeffFamily N' N''} : AbsSummable a ↔ Summable fun n => ‖a n‖ := by
  simp only [AbsSummable, opNormValue_eq_norm]
omit [NeZero N'] [NeZero N''] in
theorem norm_character_smul (a : CoeffFamily N' N'') (n : Fin 4 → ℤ) (x : AmbientSpace) :
    ‖character n x • a n‖ = ‖a n‖ := by
  rw [norm_smul, norm_character, one_mul]
omit [NeZero N'] [NeZero N''] in
theorem summable_character_smul {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖)
    (x : AmbientSpace) : Summable fun n => character n x • a n :=
  Summable.of_norm_bounded ha fun n => (norm_character_smul a n x).le
omit [NeZero N'] [NeZero N''] in
theorem hasSum_character_smul {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖)
    (x : AmbientSpace) : HasSum (fun n => character n x • a n) (seriesSum a x) :=
  (summable_character_smul ha x).hasSum
omit [NeZero N'] [NeZero N''] in
theorem hasSum_entry_apply {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖)
    (x : AmbientSpace) (i : Fin N') (k : Fin N'') :
    HasSum (fun n => character n x * a n i k) (seriesSum a x i k) := by
  have h := Pi.hasSum.1 (Pi.hasSum.1 (hasSum_character_smul ha x) i) k
  simpa using h
omit [NeZero N'] [NeZero N''] in
theorem summable_norm_entry {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖)
    (i : Fin N') (k : Fin N'') : Summable fun n => ‖a n i k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_entry_le_norm (a n) i k) ha
theorem seriesUnifConverges_of_summable {a : CoeffFamily N' N''}
    (ha : Summable fun n => ‖a n‖) : SeriesUnifConverges a := by
  intro ε hε
  have h := tendstoUniformly_tsum (f := fun n x => character n x • a n) ha
    (fun n x => (norm_character_smul a n x).le)
  rw [Metric.tendstoUniformly_iff] at h
  obtain ⟨F₀, hF⟩ := Filter.eventually_atTop.1 (h ε hε)
  refine ⟨F₀, fun F hF' x => ?_⟩
  have h' := hF F hF' x
  rw [dist_comm, dist_eq_norm] at h'
  rw [opNormValue_eq_norm]
  exact h'
omit [NeZero N'] [NeZero N''] in
theorem continuous_seriesSum {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖) :
    Continuous (seriesSum a) :=
  continuous_tsum (fun n => (continuous_character n).smul continuous_const) ha
    (fun n x => (norm_character_smul a n x).le)
theorem integral_exp_int_mul_I (k : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, if_true,
      intervalIntegral.integral_const]
    simp only [sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast
    ring
  · have hc : Complex.I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    rw [integral_exp_mul_complex hc, if_neg hk]
    have h1 : Complex.exp (Complex.I * (k : ℂ) * ((Real.pi : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have h2 := Complex.exp_int_mul_two_pi_mul_I k
      have h3 : Complex.I * (k : ℂ) * ((Real.pi : ℝ) : ℂ) =
          Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [h3, Complex.exp_add, h2, mul_one]
    rw [h1, sub_self, zero_div]
theorem torusAverage_character (m : Fin 4 → ℤ) :
    torusAverage (character m) = if m = 0 then 1 else 0 := by
  have hprod : ∫ y in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), character m y =
      ∏ μ, ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.I * (m μ : ℂ) * (t : ℂ)) := by
    rw [← Set.pi_univ_Icc, MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
    simp only [character_eq_prod]
    exact MeasureTheory.integral_fintype_prod_eq_prod
      (fun μ (t : ℝ) => Complex.exp (Complex.I * (m μ : ℂ) * (t : ℂ)))
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [torusAverage, hprod]
  simp only [integral_exp_int_mul_I]
  by_cases hm : m = 0
  · subst hm
    simp only [Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    push_cast at hpi
    field_simp
  · rw [if_neg hm]
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hm
    rw [Finset.prod_eq_zero (Finset.mem_univ μ) (if_neg hμ), mul_zero]
omit [NeZero N'] [NeZero N''] in
theorem coeff_eq_torusAverage {a : CoeffFamily N' N''} (ha : Summable fun n => ‖a n‖)
    (n : Fin 4 → ℤ) (i : Fin N') (k : Fin N'') :
    a n i k = torusAverage fun x => seriesSum a x i k * character (-n) x := by
  set cubeSet : Set AmbientSpace := Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
    with hcubeSet
  set ν : MeasureTheory.Measure AmbientSpace := MeasureTheory.volume.restrict cubeSet with hν
  have : MeasureTheory.IsFiniteMeasure ν :=
    ⟨by simpa [hν] using (isCompact_Icc (a := (fun _ : Fin 4 => -Real.pi))
      (b := fun _ => Real.pi)).measure_lt_top (μ := MeasureTheory.volume)⟩
  let F : (Fin 4 → ℤ) → AmbientSpace → ℂ := fun m x => character (m + -n) x * a m i k
  have hFc : ∀ m, Continuous (F m) := fun m => (continuous_character _).mul continuous_const
  have hFint : ∀ m, MeasureTheory.Integrable (F m) ν := fun m => by
    refine (MeasureTheory.integrable_const (‖a m i k‖)).mono' (hFc m).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp [F, norm_character]
  have hFnorm : ∀ m x, ‖F m x‖ = ‖a m i k‖ := fun m x => by simp [F, norm_character]
  have hFsum : Summable fun m => ∫ x, ‖F m x‖ ∂ν := by
    simp only [hFnorm, MeasureTheory.integral_const]
    exact (summable_norm_entry ha i k).const_smul _
  have hS := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
  have htsum : ∀ x, ∑' m, F m x = seriesSum a x i k * character (-n) x := fun x => by
    have h := (hasSum_entry_apply ha x i k).mul_right (character (-n) x)
    rw [← h.tsum_eq]
    refine tsum_congr fun m => ?_
    simp only [F, character_add]
    ring
  simp only [htsum] at hS
  have hval : ∀ m, (((2 * Real.pi) ^ 4)⁻¹ : ℝ) * ∫ x, F m x ∂ν =
      if m = n then a n i k else 0 := by
    intro m
    have h1 : ∫ x, F m x ∂ν = (∫ x, character (m + -n) x ∂ν) * a m i k :=
      MeasureTheory.integral_mul_const _ _
    have h2 := torusAverage_character (m + -n)
    rw [torusAverage] at h2
    rw [h1, ← mul_assoc, h2]
    by_cases hm : m = n
    · subst hm
      simp
    · have : m + -n ≠ 0 := fun h => hm (add_neg_eq_zero.1 h)
      simp [this, hm]
  have hS' := hS.mul_left ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ)
  simp only [hval] at hS'
  exact (hasSum_ite_eq n (a n i k)).unique hS'
theorem absSummableProps_of_absSummable {a : CoeffFamily N' N''} (ha : AbsSummable a) :
    AbsSummableProps a := by
  have ha' := absSummable_iff.1 ha
  refine ⟨seriesUnifConverges_of_summable ha', continuous_seriesSum ha',
    coeff_eq_torusAverage ha', ?_⟩
  intro b hb hba
  funext n
  ext i k
  rw [coeff_eq_torusAverage (absSummable_iff.1 hb) n i k, coeff_eq_torusAverage ha' n i k, hba]
omit [NeZero N'] [NeZero N''] in
theorem hasContinuousPartialDeriv_seriesSum {a c : CoeffFamily N' N''} (μ : Fin 4)
    (ha : Summable fun n => ‖a n‖) (hc : Summable fun n => ‖c n‖)
    (hac : ∀ n, c n = (Complex.I * (n μ : ℂ)) • a n) :
    HasContinuousPartialDeriv μ (seriesSum a) (seriesSum c) := by
  refine ⟨continuous_seriesSum hc, fun x i k => ?_⟩
  have hsum0 : Summable fun n => character n (Function.update x μ (x μ)) * a n i k :=
    (hasSum_entry_apply ha _ i k).summable
  have h := hasDerivAt_tsum (u := fun n => ‖c n‖)
    (g := fun n (t : ℝ) => character n (Function.update x μ t) * a n i k)
    (g' := fun n (t : ℝ) => character n (Function.update x μ t) * c n i k)
    (y₀ := x μ) hc
    (fun n t => by
      have h1 := (hasDerivAt_character_update n x μ t).mul_const (a n i k)
      have h2 : c n i k = Complex.I * (n μ : ℂ) * a n i k := by
        rw [hac n]
        simp
      rw [h2, ← mul_assoc]
      exact h1)
    (fun n t => by
      rw [norm_mul, norm_character, one_mul]
      exact norm_entry_le_norm (c n) i k)
    hsum0 (x μ)
  have e1 : (fun z : ℝ => ∑' n, character n (Function.update x μ z) * a n i k) =
      fun t : ℝ => seriesSum a (Function.update x μ t) i k :=
    funext fun z => (hasSum_entry_apply ha _ i k).tsum_eq
  have e2 : ∑' n, character n (Function.update x μ (x μ)) * c n i k = seriesSum c x i k := by
    rw [(hasSum_entry_apply hc _ i k).tsum_eq, Function.update_eq_self]
  rw [e1, e2] at h
  exact h
abbrev freqWeight (n : Fin 4 → ℤ) : ℝ := 1 + euclidNormVec (castVec n)
theorem one_le_freqWeight (n : Fin 4 → ℤ) : 1 ≤ freqWeight n := by apply _root_.YangMills.DeltaSharedProofs.p500919 <;> assumption
theorem norm_le_freqWeight (n : Fin 4 → ℤ) (μ : Fin 4) : ‖(n μ : ℂ)‖ ≤ freqWeight n := by
  have h : |castVec n μ| ≤ euclidNormVec (castVec n) := by
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => castVec n ν ^ 2)
      (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
  have h2 : ‖(n μ : ℂ)‖ = |castVec n μ| := by
    simp [castVec]
  rw [h2]
  simp only [freqWeight]
  linarith
omit [NeZero N'] [NeZero N''] in
theorem derivCoeffs_cons (μ : Fin 4) (w : List (Fin 4)) (a : CoeffFamily N' N'')
    (n : Fin 4 → ℤ) :
    derivCoeffs (μ :: w) a n = (Complex.I * (n μ : ℂ)) • derivCoeffs w a n := by
  simp [derivCoeffs, smul_smul]
omit [NeZero N'] [NeZero N''] in
theorem norm_derivCoeffs_le (w : List (Fin 4)) (a : CoeffFamily N' N'') (n : Fin 4 → ℤ) :
    ‖derivCoeffs w a n‖ ≤ ‖a n‖ * freqWeight n ^ w.length := by
  induction w with
  | nil => simp [derivCoeffs_nil]
  | cons μ w ih =>
    rw [derivCoeffs_cons, norm_smul, norm_mul, Complex.norm_I, one_mul, List.length_cons,
      pow_succ]
    have hw : 0 ≤ freqWeight n := zero_le_one.trans (one_le_freqWeight n)
    calc ‖(n μ : ℂ)‖ * ‖derivCoeffs w a n‖
        ≤ freqWeight n * (‖a n‖ * freqWeight n ^ w.length) :=
          mul_le_mul (norm_le_freqWeight n μ) ih (norm_nonneg _) hw
      _ = ‖a n‖ * (freqWeight n ^ w.length * freqWeight n) := by ring
omit [NeZero N'] [NeZero N''] in
theorem summable_norm_derivCoeffs {a : CoeffFamily N' N''} {j : ℕ}
    (hj : Summable fun n => ‖a n‖ * freqWeight n ^ j) (w : List (Fin 4)) (hw : w.length ≤ j) :
    Summable fun n => ‖derivCoeffs w a n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hj
  refine (norm_derivCoeffs_le w a n).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_freqWeight n) hw) (norm_nonneg _)
theorem termwiseDiffProps_of_weighted {a : CoeffFamily N' N''} {j : ℕ} (hj1 : 1 ≤ j)
    (hj : WeightedAbsSummable j a) : TermwiseDiffProps j a := by
  have hj' : Summable fun n => ‖a n‖ * freqWeight n ^ j := by
    simpa only [WeightedAbsSummable, opNormValue_eq_norm] using hj
  have hsum := summable_norm_derivCoeffs hj'
  have ha : Summable fun n => ‖a n‖ := by
    have := hsum [] (Nat.zero_le _)
    simpa [derivCoeffs_nil] using this
  refine ⟨fun μ => ?_, fun μ => ?_, fun w hw => ?_, fun w hw μ => ?_⟩
  · have hc := hsum [μ] (by simpa using hj1)
    refine ⟨seriesSum (derivCoeffs [μ] a),
      hasContinuousPartialDeriv_seriesSum μ ha hc (fun n => ?_), fun x => ?_⟩
    · rw [derivCoeffs_cons, derivCoeffs_nil]
    · have h := (hasSum_character_smul hc x).const_smul (-Complex.I)
      rw [← h.tsum_eq, seriesSum]
      refine tsum_congr fun n => ?_
      rw [derivCoeffs_cons, derivCoeffs_nil, smul_smul, smul_smul, smul_smul]
      congr 1
      linear_combination (-(character n x * (n μ : ℂ))) * Complex.I_mul_I
  · simp only [WeightedAbsSummable, opNormValue_eq_norm]
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg
        (zero_le_one.trans (one_le_freqWeight n)) _)) (fun n => ?_) hj'
    have hw : 0 ≤ freqWeight n := zero_le_one.trans (one_le_freqWeight n)
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [norm_smul, Nat.add_sub_cancel, pow_succ]
    calc ‖(n μ : ℂ)‖ * ‖a n‖ * freqWeight n ^ i
        ≤ freqWeight n * ‖a n‖ * freqWeight n ^ i := by
          gcongr
          exact norm_le_freqWeight n μ
      _ = ‖a n‖ * (freqWeight n ^ i * freqWeight n) := by ring
  · have hs := hsum w hw
    exact ⟨absSummable_iff.2 hs, continuous_seriesSum hs⟩
  · exact hasContinuousPartialDeriv_seriesSum μ (hsum w hw.le)
      (hsum (μ :: w) (by simpa using hw)) (fun n => derivCoeffs_cons μ w a n)
section Product
variable {N''' : ℕ} [NeZero N''']
theorem hasSum_sum_fibres {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : (Fin 4 → ℤ) × (Fin 4 → ℤ) → E} {S : E} (hg : HasSum g S)
    (hs : Summable fun p => ‖g p‖) :
    HasSum (fun n : Fin 4 → ℤ => ∑' p : SumPairs n, g p.1) S := by
  let e := Equiv.sigmaFiberEquiv (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => p.1 + p.2)
  have h1 : HasSum (g ∘ e) S := (Equiv.hasSum_iff e).2 hg
  refine h1.sigma fun n => ?_
  have h2 : Summable fun p : SumPairs n => g p.1 :=
    (hs.of_norm).comp_injective Subtype.val_injective
  exact h2.hasSum
omit [NeZero N'] [NeZero N''] [NeZero N'''] in
theorem summable_norm_mul_norm {a : CoeffFamily N' N''} {a' : CoeffFamily N'' N'''}
    (ha : Summable fun n => ‖a n‖) (ha' : Summable fun n => ‖a' n‖) :
    Summable fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ‖a p.1‖ * ‖a' p.2‖ :=
  Summable.mul_of_nonneg (f := fun n => ‖a n‖) (g := fun n => ‖a' n‖) ha ha'
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
omit [NeZero N'] [NeZero N''] [NeZero N'''] in
theorem seriesSum_mul_seriesSum {a : CoeffFamily N' N''} {a' : CoeffFamily N'' N'''}
    (ha : Summable fun n => ‖a n‖) (ha' : Summable fun n => ‖a' n‖)
    (hco : ∀ n : Fin 4 → ℤ, Summable fun p : SumPairs n => a p.1.1 * a' p.1.2)
    (x : AmbientSpace) :
    seriesSum a x * seriesSum a' x = seriesSum (coeffConv a a') x := by
  have hnorm : Summable fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      ‖(character p.1 x • a p.1) * (character p.2 x • a' p.2)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (summable_norm_mul_norm ha ha')
    refine (Matrix.l2_opNorm_mul _ _).trans (le_of_eq ?_)
    rw [norm_character_smul, norm_character_smul]
  have hY : ∀ p : Fin 4 → ℤ, HasSum (fun r => (character p x • a p) * (character r x • a' r))
      ((character p x • a p) * seriesSum a' x) := fun p => by
    have hc : Continuous fun X : Matrix (Fin N'') (Fin N''') ℂ => (character p x • a p) * X :=
      continuous_const.matrix_mul continuous_id
    let L : Matrix (Fin N'') (Fin N''') ℂ →+ Matrix (Fin N') (Fin N''') ℂ :=
      { toFun := fun X => (character p x • a p) * X
        map_zero' := Matrix.mul_zero _
        map_add' := Matrix.mul_add _ }
    exact (hasSum_character_smul ha' x).map L hc
  have hX : HasSum (fun p => (character p x • a p) * seriesSum a' x)
      (seriesSum a x * seriesSum a' x) := by
    have hc : Continuous fun X : Matrix (Fin N') (Fin N'') ℂ => X * seriesSum a' x :=
      continuous_id.matrix_mul continuous_const
    let L : Matrix (Fin N') (Fin N'') ℂ →+ Matrix (Fin N') (Fin N''') ℂ :=
      { toFun := fun X => X * seriesSum a' x
        map_zero' := Matrix.zero_mul _
        map_add' := fun X Y => Matrix.add_mul X Y _ }
    exact (hasSum_character_smul ha x).map L hc
  have hS := hnorm.of_norm.hasSum
  have hXY := (hS.prod_fiberwise hY).unique hX
  rw [hXY] at hS
  have hF := hasSum_sum_fibres hS hnorm
  have hfib : ∀ n : Fin 4 → ℤ,
      ∑' p : SumPairs n, (character p.1.1 x • a p.1.1) * (character p.1.2 x • a' p.1.2) =
        character n x • coeffConv a a' n := fun n => by
    have h1 := (hco n).hasSum.const_smul (character n x)
    rw [coeffConv, ← h1.tsum_eq]
    refine tsum_congr fun p => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← character_add, p.2]
  simp only [hfib] at hF
  exact hF.tsum_eq.symm
theorem productProps_of_absSummable {a : CoeffFamily N' N''} {a' : CoeffFamily N'' N'''}
    (ha : AbsSummable a) (ha' : AbsSummable a') : ProductProps a a' := by
  have h := absSummable_iff.1 ha
  have h' := absSummable_iff.1 ha'
  have hm := summable_norm_mul_norm h h'
  have hT := h.hasSum.mul h'.hasSum hm
  have hF := hasSum_sum_fibres hT (by simpa only [norm_mul, norm_norm] using hm)
  have hfib : ∀ n : Fin 4 → ℤ, Summable fun p : SumPairs n => ‖a p.1.1‖ * ‖a' p.1.2‖ :=
    fun n => hm.comp_injective (i := (Subtype.val : SumPairs n → _)) Subtype.val_injective
  have hco : ∀ n : Fin 4 → ℤ, Summable fun p : SumPairs n => ‖a p.1.1 * a' p.1.2‖ := fun n =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => Matrix.l2_opNorm_mul _ _) (hfib n)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [opNormValue_eq_norm] using hfib
  · simpa only [opNormValue_eq_norm] using hF
  · simpa only [opNormValue_eq_norm] using hco
  · refine absSummable_iff.2 (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      hF.summable)
    exact (norm_tsum_le_tsum_norm (hco n)).trans
      ((hco n).tsum_le_tsum (fun p => Matrix.l2_opNorm_mul _ _) (hfib n))
  · exact seriesSum_mul_seriesSum h h' (fun n => (hco n).of_norm)
end Product
theorem statement_holds : statement :=
  fun _ _ _ _ _ ha => ⟨absSummableProps_of_absSummable ha,
    fun _ hj1 hj => termwiseDiffProps_of_weighted hj1 hj,
    fun _ _ _ ha' => productProps_of_absSummable ha ha'⟩
end YangMills.Construction.Matrices.FourierMatrixSeries
end
