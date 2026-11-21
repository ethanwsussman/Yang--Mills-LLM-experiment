import YangMills.Construction.Torus.CoefficientsOfATestFunctionOnTheBox
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Conventions AmbientPoints
namespace Torus.FourierBox.Estimates
section Partials
variable {D : ℕ}
theorem foldr_iterate_single_of_notMem (j : Fin D) (n : ℕ) (G : (Fin D → ℝ) → ℂ)
    (l : List (Fin D)) (h : j ∉ l) :
    l.foldr (fun i H => (partialDeriv i)^[(Pi.single j n : PowerSeries.MultiIndex D) i] H) G = G := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a ≠ j := fun e => h (e ▸ List.mem_cons_self)
    have hl : j ∉ l := fun e => h (List.mem_cons_of_mem _ e)
    simp only [List.foldr_cons, Pi.single_eq_of_ne ha, Function.iterate_zero, id_eq]
    exact ih hl
theorem foldr_iterate_single_of_mem (j : Fin D) (n : ℕ) (G : (Fin D → ℝ) → ℂ) (l : List (Fin D))
    (hnd : l.Nodup) (h : j ∈ l) :
    l.foldr (fun i H => (partialDeriv i)^[(Pi.single j n : PowerSeries.MultiIndex D) i] H) G =
      (partialDeriv j)^[n] G := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a = j
    · subst ha
      have hl : a ∉ l := (List.nodup_cons.1 hnd).1
      simp only [List.foldr_cons, Pi.single_eq_same]
      rw [foldr_iterate_single_of_notMem a n G l hl]
    · have hl : j ∈ l := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm ha
        · exact e
      simp only [List.foldr_cons, Pi.single_eq_of_ne ha, Function.iterate_zero, id_eq]
      exact ih (List.nodup_cons.1 hnd).2 hl
theorem iteratedPartial_single (j : Fin D) (n : ℕ) (G : (Fin D → ℝ) → ℂ) :
    iteratedPartial (Pi.single j n : PowerSeries.MultiIndex D) G = (partialDeriv j)^[n] G :=
  foldr_iterate_single_of_mem j n G _ (List.nodup_finRange D) (List.mem_finRange j)
theorem order_single_le (j : Fin D) (n : ℕ) :
    PowerSeries.MultiIndex.order (Pi.single j n : PowerSeries.MultiIndex D) ≤ n := by
  simp [PowerSeries.MultiIndex.order, Finset.sum_pi_single']
end Partials
section Lift
variable {s : StandingParameters} {p : ℕ}
theorem multiDeriv_comp_tupleProj_euclidean (α : PowerSeries.MultiIndex (4 * p))
    (F : Tuple s .euclidean p → ℂ) :
    multiDeriv α F ∘ tupleProj s .euclidean p =
      iteratedPartial α (F ∘ tupleProj s .euclidean p) := by
  refine multiDeriv_comp_tupleProj
    ⟨fun y => iteratedPartial α (F ∘ tupleProj s .euclidean p) (flattenCoords p y), ?_⟩
  funext u
  exact congrArg (iteratedPartial α (F ∘ tupleProj s .euclidean p))
    ((flattenCoords p).apply_symm_apply u)
theorem multiDeriv_single_one_comp (j : Fin (4 * p)) (F : Tuple s .euclidean p → ℂ) :
    multiDeriv (Pi.single j 1) F ∘ tupleProj s .euclidean p =
      partialDeriv j (F ∘ tupleProj s .euclidean p) := by
  rw [multiDeriv_comp_tupleProj_euclidean, iteratedPartial_single]
  rfl
theorem multiDeriv_single_one_multiDeriv_single (j : Fin (4 * p)) (n : ℕ)
    (F : Tuple s .euclidean p → ℂ) :
    multiDeriv (Pi.single j 1) (multiDeriv (Pi.single j n) F) =
      multiDeriv (Pi.single j (n + 1)) F := by
  apply (tupleProj_surjective s .euclidean p).injective_comp_right
  show multiDeriv _ _ ∘ tupleProj s .euclidean p =
    multiDeriv _ _ ∘ tupleProj s .euclidean p
  rw [multiDeriv_single_one_comp, multiDeriv_comp_tupleProj_euclidean,
    multiDeriv_comp_tupleProj_euclidean, iteratedPartial_single,
    iteratedPartial_single, Function.iterate_succ_apply']
theorem tupleSupNorm_multiDeriv_single_le (j : Fin (4 * p)) (ν : ℕ)
    (F : Tuple s .euclidean p → ℂ) :
    tupleSupNorm (multiDeriv (Pi.single j ν) F) ≤ cnNorm ν F :=
  iSup_le fun y => le_iSup_of_le (Pi.single j ν) (le_iSup_of_le (order_single_le j ν)
    (le_iSup (fun y => ENNReal.ofReal ‖multiDeriv (Pi.single j ν) F y‖) y))
end Lift
section Modes
variable {D : ℕ}
theorem norm_fourierMode (P : ℝ) (k : Fin D → ℤ) (u : Fin D → ℝ) : ‖fourierMode P k u‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (intDot k u : ℂ) / (P : ℂ) =
      ((2 * Real.pi * intDot k u / P : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierMode, h, Complex.norm_exp_ofReal_mul_I]
theorem conj_fourierMode (P : ℝ) (k : Fin D → ℤ) (u : Fin D → ℝ) :
    conj (fourierMode P k u) =
      Complex.exp (-(2 * Real.pi * Complex.I) / (P : ℂ) * (intDot k u : ℂ)) := by
  rw [fourierMode, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring
theorem intDot_add_smul_single (k : Fin D → ℤ) (u : Fin D → ℝ) (j : Fin D) (t : ℝ) :
    intDot k (u + t • Pi.single j 1) = intDot k u + t * (k j : ℝ) := by
  unfold intDot
  simp only [Pi.add_apply, Pi.smul_apply, mul_add, Finset.sum_add_distrib, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    ring
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem hasLineDerivAt_conj_fourierMode (P : ℝ) (k : Fin D → ℤ) (j : Fin D) (u : Fin D → ℝ) :
    HasLineDerivAt ℝ (fun v => conj (fourierMode P k v))
      (-(2 * Real.pi * Complex.I) / (P : ℂ) * (k j : ℂ) * conj (fourierMode P k u)) u
      (Pi.single j 1) := by
  set c : ℂ := -(2 * Real.pi * Complex.I) / (P : ℂ) with hc
  have h1 : HasDerivAt (fun t : ℝ => intDot k u + t * (k j : ℝ)) (k j : ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (k j : ℝ)).const_add (intDot k u)
  have h2 : HasDerivAt (fun t : ℝ => ((intDot k u + t * (k j : ℝ) : ℝ) : ℂ))
      ((k j : ℝ) : ℂ) 0 := h1.ofReal_comp
  have h3 := (h2.const_mul c).cexp
  have hf : (fun t : ℝ => conj (fourierMode P k (u + t • Pi.single j 1))) = fun t : ℝ =>
      Complex.exp (c * ((intDot k u + t * (k j : ℝ) : ℝ) : ℂ)) := by
    funext t
    rw [conj_fourierMode, intDot_add_smul_single]
  have hd : c * (k j : ℂ) * conj (fourierMode P k u) =
      Complex.exp (c * ((intDot k u + 0 * (k j : ℝ) : ℝ) : ℂ)) * (c * (((k j : ℝ)) : ℂ)) := by
    rw [conj_fourierMode, ← hc]
    simp only [zero_mul, add_zero, Complex.ofReal_intCast]
    ring
  show HasDerivAt (fun t : ℝ => conj (fourierMode P k (u + t • Pi.single j 1))) _ 0
  rw [hf, hd]
  exact h3
end Modes
section Integrals
variable {s : StandingParameters} {p : ℕ} {P : ℝ}
theorem fundamentalCube_eq_pi (D : ℕ) (P : ℝ) :
    fundamentalCube D P = Set.pi univ fun _ => Ioo (-P / 2) (P / 2) := by
  ext u
  simp [fundamentalCube]
theorem volume_fundamentalCube (D : ℕ) (hP : 0 < P) :
    volume (fundamentalCube D P) = ENNReal.ofReal (P ^ D) := by
  rw [fundamentalCube_eq_pi, Real.volume_pi_Ioo]
  have h : P / 2 - -P / 2 = P := by ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hP.le]
theorem apply_tupleProj_eq_zero_of_not_mem {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P))
    {u : Fin (4 * p) → ℝ} (hu : u ∉ fundamentalCube (4 * p) P) :
    F (tupleProj s .euclidean p u) = 0 := by
  by_contra h
  have h1 : tupleProj s .euclidean p u ∈ closedSupport F := subset_closure h
  exact hu ((tupleProj_mem_fundamentalBoxPow_iff s p P u).1 (hF.2.2 h1))
theorem continuous_comp_tupleProj {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P)) :
    Continuous (F ∘ tupleProj s .euclidean p) :=
  continuousOn_univ.1 (hF.1.2 0 le_top)
theorem norm_le_tupleSupNorm {F : Tuple s .euclidean p → ℂ} (hs : tupleSupNorm F ≠ ⊤)
    (y : Tuple s .euclidean p) : ‖F y‖ ≤ (tupleSupNorm F).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hs).1 (le_iSup (fun y => ENNReal.ofReal ‖F y‖) y)
theorem integrable_comp_tupleProj_mul (hP : 0 < P) {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P)) (hs : tupleSupNorm F ≠ ⊤)
    {φ : (Fin (4 * p) → ℝ) → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ u, ‖φ u‖ ≤ C) :
    Integrable fun u => F (tupleProj s .euclidean p u) * φ u := by
  have hcont : Continuous fun u => F (tupleProj s .euclidean p u) * φ u :=
    (continuous_comp_tupleProj hF).mul hφ
  have hon : IntegrableOn (fun u => F (tupleProj s .euclidean p u) * φ u)
      (fundamentalCube (4 * p) P) := by
    refine Measure.integrableOn_of_bounded (M := (tupleSupNorm F).toReal * C) ?_
      hcont.aestronglyMeasurable ?_
    · rw [volume_fundamentalCube _ hP]
      exact ENNReal.ofReal_ne_top
    · refine Filter.Eventually.of_forall fun u => ?_
      rw [norm_mul]
      exact mul_le_mul (norm_le_tupleSupNorm hs _) (hC u) (norm_nonneg _) ENNReal.toReal_nonneg
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro u hu
  by_contra h
  exact hu (by simp [apply_tupleProj_eq_zero_of_not_mem hF h])
theorem continuous_conj_fourierMode {D : ℕ} (P : ℝ) (k : Fin D → ℤ) :
    Continuous fun u => conj (fourierMode P k u) :=
  Complex.continuous_conj.comp (contDiff_fourierMode P k).continuous
theorem integrable_fourierIntegrand (hP : 0 < P) {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P)) (hs : tupleSupNorm F ≠ ⊤)
    (k : Fin (4 * p) → ℤ) :
    Integrable fun u => F (tupleProj s .euclidean p u) * conj (fourierMode P k u) :=
  integrable_comp_tupleProj_mul hP hF hs (continuous_conj_fourierMode P k) (C := 1) fun u => by
    rw [RCLike.norm_conj, norm_fourierMode]
theorem fourierCoeff_eq_integral {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P)) (k : Fin (4 * p) → ℤ) :
    fourierCoeff P F k = ((P : ℂ) ^ (4 * p))⁻¹ *
      ∫ u, F (tupleProj s .euclidean p u) * conj (fourierMode P k u) := by
  rw [fourierCoeff, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  rw [apply_tupleProj_eq_zero_of_not_mem hF hu, zero_mul]
theorem norm_fourierCoeff_le (hP : 0 < P) {F : Tuple s .euclidean p → ℂ}
    (hs : tupleSupNorm F ≠ ⊤) (k : Fin (4 * p) → ℤ) :
    ‖fourierCoeff P F k‖ ≤ (tupleSupNorm F).toReal := by
  have hvol : volume (fundamentalCube (4 * p) P) < ⊤ := by
    rw [volume_fundamentalCube _ hP]
    exact ENNReal.ofReal_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := (tupleSupNorm F).toReal)
    (f := fun u => F (tupleProj s .euclidean p u) * conj (fourierMode P k u)) hvol
    (fun u _ => by
      rw [norm_mul, RCLike.norm_conj, norm_fourierMode, mul_one]
      exact norm_le_tupleSupNorm hs _)
  have hreal : volume.real (fundamentalCube (4 * p) P) = P ^ (4 * p) := by
    rw [Measure.real, volume_fundamentalCube _ hP, ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at hint
  have hnorm : ‖((P : ℂ) ^ (4 * p))⁻¹‖ = (P ^ (4 * p))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hP.le]
  rw [fourierCoeff, norm_mul, hnorm]
  calc (P ^ (4 * p))⁻¹ * _ ≤ (P ^ (4 * p))⁻¹ * ((tupleSupNorm F).toReal * P ^ (4 * p)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (tupleSupNorm F).toReal := by field_simp
theorem isComplexLinearForm_fourierCoeff (hP : 0 < P)
    (hs : ∀ F ∈ testFns (fundamentalBoxPow s p P), tupleSupNorm F ≠ ⊤) (k : Fin (4 * p) → ℤ) :
    IsComplexLinearForm fun F : testFns (fundamentalBoxPow s p P) => fourierCoeff P F.1 k := by
  refine ⟨fun F G H hH => ?_, fun c F H hH => ?_⟩
  · show fourierCoeff P H.1 k = fourierCoeff P F.1 k + fourierCoeff P G.1 k
    rw [fourierCoeff_eq_integral H.2, fourierCoeff_eq_integral F.2, fourierCoeff_eq_integral G.2,
      ← mul_add, ← integral_add (integrable_fourierIntegrand hP F.2 (hs _ F.2) k)
        (integrable_fourierIntegrand hP G.2 (hs _ G.2) k)]
    congr 2
    funext u
    rw [hH, Pi.add_apply, add_mul]
  · show fourierCoeff P H.1 k = c * fourierCoeff P F.1 k
    rw [fourierCoeff_eq_integral H.2, fourierCoeff_eq_integral F.2, mul_left_comm c,
      ← integral_const_mul c]
    congr 2
    funext u
    rw [hH, Pi.smul_apply, smul_eq_mul, mul_assoc]
theorem fourierCoeff_partial (hP : 0 < P) {F : Tuple s .euclidean p → ℂ}
    (hF : F ∈ testFns (fundamentalBoxPow s p P)) (j : Fin (4 * p))
    (hF' : multiDeriv (Pi.single j 1) F ∈ testFns (fundamentalBoxPow s p P))
    (hs : tupleSupNorm F ≠ ⊤) (hs' : tupleSupNorm (multiDeriv (Pi.single j 1) F) ≠ ⊤)
    (k : Fin (4 * p) → ℤ) :
    fourierCoeff P (multiDeriv (Pi.single j 1) F) k =
      2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ) * fourierCoeff P F k := by
  set G := F ∘ tupleProj s .euclidean p with hG
  set c : ℂ := -(2 * Real.pi * Complex.I) / (P : ℂ) * (k j : ℂ) with hc
  have hpart : ∀ u, multiDeriv (Pi.single j 1) F (tupleProj s .euclidean p u) =
      partialDeriv j G u := fun u => congrFun (multiDeriv_single_one_comp j F) u
  have hline : ∀ x, HasLineDerivAt ℝ G (partialDeriv j G x) x (Pi.single j 1) := fun x =>
    ((hF.1.2 1 le_top).2 j).1 x (mem_univ x) |>.hasLineDerivAt
  have i0 : Integrable fun u => G u * conj (fourierMode P k u) :=
    integrable_fourierIntegrand hP hF hs k
  have i1 := integrable_fourierIntegrand hP hF' hs' k
  simp only [hpart] at i1
  have i2 : Integrable fun u => G u * (c * conj (fourierMode P k u)) := by
    have := i0.const_mul c
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hG, Function.comp_apply]
    ring
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℂ) (f := G) (f' := partialDeriv j G)
    (g := fun v => conj (fourierMode P k v)) (g' := fun v => c * conj (fourierMode P k v))
    (v := Pi.single j 1) (by simpa only [ContinuousLinearMap.mul_apply'] using i1)
    (by simpa only [ContinuousLinearMap.mul_apply'] using i2)
    (by simpa only [ContinuousLinearMap.mul_apply'] using i0)
    (fun x _ => hline x) (fun x _ => hasLineDerivAt_conj_fourierMode P k j x)
  simp only [ContinuousLinearMap.mul_apply'] at hibp
  have hmove : ∫ x, G x * (c * conj (fourierMode P k x)) =
      c * ∫ x, G x * conj (fourierMode P k x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [fourierCoeff_eq_integral hF', fourierCoeff_eq_integral hF]
  simp only [hpart]
  have hfin : ∫ x, partialDeriv j G x * conj (fourierMode P k x) =
      -c * ∫ x, G x * conj (fourierMode P k x) := by
    rw [neg_mul, ← hmove, hibp, neg_neg]
  rw [hfin, hc]
  simp only [hG, Function.comp_apply]
  ring
end Integrals
section Decay
variable {s : StandingParameters} {p : ℕ} {P : ℝ}
theorem fourierCoeff_partial_pow (hP : 0 < P)
    (hT : ∀ F ∈ testFns (fundamentalBoxPow s p P),
      (∀ α : PowerSeries.MultiIndex (4 * p), multiDeriv α F ∈ testFns (fundamentalBoxPow s p P)) ∧
        tupleSupNorm F ≠ ⊤)
    {F : Tuple s .euclidean p → ℂ} (hF : F ∈ testFns (fundamentalBoxPow s p P))
    (j : Fin (4 * p)) (k : Fin (4 * p) → ℤ) (n : ℕ) :
    fourierCoeff P (multiDeriv (Pi.single j n) F) k =
      (2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ)) ^ n * fourierCoeff P F k := by
  induction n with
  | zero => simp [multiDeriv_zero]
  | succ n ih =>
    have h1 := (hT F hF).1 (Pi.single j n)
    have h2 := (hT _ h1).1 (Pi.single j 1)
    rw [← multiDeriv_single_one_multiDeriv_single,
      fourierCoeff_partial hP h1 j h2 (hT _ h1).2 (hT _ h2).2, ih, pow_succ]
    ring
theorem one_le_supNormInt {D : ℕ} {k : Fin D → ℤ} (hk : k ≠ 0) : 1 ≤ supNormInt k := by
  by_contra h
  apply hk
  funext j
  have h1 : (k j).natAbs ≤ supNormInt k :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
  simpa using (by omega : (k j).natAbs = 0)
theorem fourierCoeff_decay (hp : 1 ≤ p) (hP : 0 < P)
    (hT : ∀ F ∈ testFns (fundamentalBoxPow s p P),
      (∀ α : PowerSeries.MultiIndex (4 * p), multiDeriv α F ∈ testFns (fundamentalBoxPow s p P)) ∧
        tupleSupNorm F ≠ ⊤)
    {F : Tuple s .euclidean p → ℂ} (hF : F ∈ testFns (fundamentalBoxPow s p P))
    (k : Fin (4 * p) → ℤ) (hk : k ≠ 0) (ν : ℕ) :
    ENNReal.ofReal ‖fourierCoeff P F k‖ ≤
      ENNReal.ofReal ((P / (2 * Real.pi * (supNormInt k : ℝ))) ^ ν) * cnNorm ν F := by
  obtain ⟨⟨j, hj⟩, -⟩ := isGreatest_supNormInt (by omega : 1 ≤ 4 * p) k
  have hj' : (k j).natAbs = supNormInt k := hj
  have hm : (0 : ℝ) < (supNormInt k : ℝ) := by
    exact_mod_cast one_le_supNormInt hk
  set m : ℝ := (supNormInt k : ℝ) with hmdef
  have hpi := Real.pi_pos
  have hnorm : ‖2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ)‖ = 2 * Real.pi * m / P := by
    have hkj : ‖(k j : ℂ)‖ = m := by
      rw [Complex.norm_intCast, hmdef, ← hj']
      simp
    rw [norm_div, norm_mul, norm_mul, norm_mul, hkj, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hP.le, Real.norm_of_nonneg hpi.le]
    simp
  have h1 := (hT F hF).1 (Pi.single j ν)
  have h2 : ENNReal.ofReal ‖fourierCoeff P (multiDeriv (Pi.single j ν) F) k‖ ≤ cnNorm ν F :=
    ((ENNReal.ofReal_le_iff_le_toReal (hT _ h1).2).2 (norm_fourierCoeff_le hP (hT _ h1).2 k)).trans
      (tupleSupNorm_multiDeriv_single_le j ν F)
  rw [fourierCoeff_partial_pow hP hT hF j k ν, norm_mul, norm_pow, hnorm] at h2
  have hAB : (P / (2 * Real.pi * m)) ^ ν * (2 * Real.pi * m / P) ^ ν = 1 := by
    rw [← mul_pow]
    have : P / (2 * Real.pi * m) * (2 * Real.pi * m / P) = 1 := by field_simp
    rw [this, one_pow]
  calc ENNReal.ofReal ‖fourierCoeff P F k‖
      = ENNReal.ofReal ((P / (2 * Real.pi * m)) ^ ν *
          ((2 * Real.pi * m / P) ^ ν * ‖fourierCoeff P F k‖)) := by
        rw [← mul_assoc, hAB, one_mul]
    _ = ENNReal.ofReal ((P / (2 * Real.pi * m)) ^ ν) *
          ENNReal.ofReal ((2 * Real.pi * m / P) ^ ν * ‖fourierCoeff P F k‖) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr
end Decay
section Shells
variable {D : ℕ}
theorem card_modesWithin (t : ℕ) :
    ((modesWithin (N := D) t).card : ℤ) = (2 * (t : ℤ) + 1) ^ D := by
  have h : (Finset.Icc (-(t : ℤ)) (t : ℤ)).card = 2 * t + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [modesWithin, Fintype.card_piFinset, h, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  ring
theorem modesWithSupNorm_eq_sdiff {m : ℕ} (hm : 1 ≤ m) :
    modesWithSupNorm D m = ↑(modesWithin (N := D) m \ modesWithin (m - 1)) := by
  ext k
  simp only [modesWithSupNorm, Set.mem_ofPred_eq, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
    mem_modesWithin]
  omega
theorem finite_modesWithSupNorm (m : ℕ) : (modesWithSupNorm D m).Finite :=
  (modesWithin (N := D) m).finite_toSet.subset fun k hk => by
    simp only [Finset.mem_coe, mem_modesWithin]
    exact le_of_eq hk
theorem ncard_modesWithSupNorm {m : ℕ} (hm : 1 ≤ m) :
    ((modesWithSupNorm D m).ncard : ℤ) = (2 * (m : ℤ) + 1) ^ D - (2 * (m : ℤ) - 1) ^ D := by
  have hsub : modesWithin (N := D) (m - 1) ⊆ modesWithin m := fun k hk => by
    rw [mem_modesWithin] at hk ⊢
    omega
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [modesWithSupNorm_eq_sdiff hm, Set.ncard_coe_finset]
  have h1 := card_modesWithin (D := D) m
  have h2 := card_modesWithin (D := D) (m - 1)
  have h3 : (((m - 1 : ℕ) : ℤ)) = (m : ℤ) - 1 := by omega
  rw [h3] at h2
  have h4 : 2 * ((m : ℤ) - 1) + 1 = 2 * (m : ℤ) - 1 := by ring
  rw [h4] at h2
  rw [← h1, ← h2]
  omega
theorem pow_succ_sub_pow_succ_le (a b : ℤ) (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ ((n : ℤ) + 1) * (a - b) * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : 0 ≤ a := hb.trans hab
    have h1 := mul_le_mul_of_nonneg_left ih ha
    have h2 : (a - b) * b ^ (n + 1) ≤ (a - b) * a ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hab _) (sub_nonneg.2 hab)
    have h3 : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    have h4 : (((n + 1 : ℕ) : ℤ) + 1) * (a - b) * a ^ (n + 1) =
        a * (((n : ℤ) + 1) * (a - b) * a ^ n) + (a - b) * a ^ (n + 1) := by
      push_cast
      ring
    rw [h3, h4]
    linarith
theorem shell_card_le (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℤ) + 1) ^ D - (2 * (m : ℤ) - 1) ^ D ≤
      2 * (D : ℤ) * (2 * (m : ℤ) + 1) ^ (D - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  have := pow_succ_sub_pow_succ_le (2 * (m : ℤ) + 1) (2 * (m : ℤ) - 1) (by omega) (by omega) n
  have h2 : 2 * (m : ℤ) + 1 - (2 * (m : ℤ) - 1) = 2 := by ring
  rw [h2] at this
  simp only [Nat.add_sub_cancel]
  push_cast
  linarith
theorem shell_bound_le_three {m : ℕ} (hm : 1 ≤ m) :
    2 * (D : ℤ) * (2 * (m : ℤ) + 1) ^ (D - 1) ≤ 2 * (D : ℤ) * (3 * (m : ℤ)) ^ (D - 1) := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by omega) (by omega) _) (by positivity)
end Shells
section Sums
variable {D : ℕ}
theorem summable_inv_one_add_supNormInt_pow (hD : 1 ≤ D) :
    Summable fun k : Fin D → ℤ => (((1 : ℝ) + (supNormInt k : ℝ)) ^ (D + 1))⁻¹ := by
  have hfin : ∀ m : ℕ, Finite {k : Fin D → ℤ // supNormInt k = m} := fun m =>
    (finite_modesWithSupNorm (D := D) m).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (supNormInt (N := D))).summable_iff,
    summable_sigma_of_nonneg fun _ => by simp only [Function.comp_apply]; positivity]
  refine ⟨fun m => Summable.of_finite, ?_⟩
  refine (summable_nat_add_iff 1).1 ?_
  have hinv : Summable fun m : ℕ => (((m + 2 : ℕ) : ℝ) ^ 2)⁻¹ :=
    (summable_nat_add_iff 2).2 (Real.summable_nat_pow_inv.2 (by norm_num))
  refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun _ => ?_) (fun m => ?_)
    (hinv.mul_left (2 * (D : ℝ) * 3 ^ (D - 1)))
  · simp only [Function.comp_apply]
    positivity
  · set M := m + 1 with hM
    have hval : ∀ y : {k : Fin D → ℤ // supNormInt k = M},
        (fun k : Fin D → ℤ => (((1 : ℝ) + (supNormInt k : ℝ)) ^ (D + 1))⁻¹)
          (Equiv.sigmaFiberEquiv (supNormInt (N := D)) ⟨M, y⟩) =
        (((1 : ℝ) + (M : ℝ)) ^ (D + 1))⁻¹ := fun y => by
      simp only [Equiv.sigmaFiberEquiv_apply, y.2]
    simp only [Function.comp_apply, hval]
    rw [tsum_const, nsmul_eq_mul]
    have hcard : ((Nat.card {k : Fin D → ℤ // supNormInt k = M} : ℕ) : ℝ) ≤
        2 * (D : ℝ) * (3 * (M : ℝ)) ^ (D - 1) := by
      have hz : ((modesWithSupNorm D M).ncard : ℤ) ≤ 2 * (D : ℤ) * (3 * (M : ℤ)) ^ (D - 1) := by
        rw [ncard_modesWithSupNorm (by omega)]
        exact (shell_card_le hD (by omega)).trans (shell_bound_le_three (by omega))
      have hc : Nat.card {k : Fin D → ℤ // supNormInt k = M} = (modesWithSupNorm D M).ncard :=
        rfl
      rw [hc]
      exact_mod_cast hz
    have hpos : (0 : ℝ) < 1 + (M : ℝ) := by positivity
    have hsplit : (((1 : ℝ) + (M : ℝ)) ^ (D + 1))⁻¹ * ((1 : ℝ) + (M : ℝ)) ^ (D - 1) =
        (((m + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
      have h1 : D + 1 = (D - 1) + 2 := by omega
      have h2 : ((m + 2 : ℕ) : ℝ) = 1 + (M : ℝ) := by
        rw [hM]
        push_cast
        ring
      rw [h1, pow_add, h2, mul_inv, mul_comm, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hpos.ne'), one_mul]
    have hMle : (3 * (M : ℝ)) ^ (D - 1) ≤ 3 ^ (D - 1) * ((1 : ℝ) + (M : ℝ)) ^ (D - 1) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (by positivity)
    calc ((Nat.card {k : Fin D → ℤ // supNormInt k = M} : ℕ) : ℝ) *
          (((1 : ℝ) + (M : ℝ)) ^ (D + 1))⁻¹
        ≤ (2 * (D : ℝ) * (3 ^ (D - 1) * ((1 : ℝ) + (M : ℝ)) ^ (D - 1))) *
            (((1 : ℝ) + (M : ℝ)) ^ (D + 1))⁻¹ := by
          refine mul_le_mul_of_nonneg_right (hcard.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hMle (by positivity)
      _ = 2 * (D : ℝ) * 3 ^ (D - 1) *
            ((((1 : ℝ) + (M : ℝ)) ^ (D + 1))⁻¹ * ((1 : ℝ) + (M : ℝ)) ^ (D - 1)) := by ring
      _ = 2 * (D : ℝ) * 3 ^ (D - 1) * (((m + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by rw [hsplit]
theorem summable_mul_rpow_of_bound (hD : 1 ≤ D) {c : (Fin D → ℤ) → ℝ} (hc : ∀ k, 0 ≤ c k)
    {a : ℝ} {n : ℕ} (han : a ≤ n) {C : ℝ}
    (hC : ∀ k, c k * ((1 : ℝ) + (supNormInt k : ℝ)) ^ (n + D + 1) ≤ C) :
    Summable fun k : Fin D → ℤ => c k * ((1 : ℝ) + (supNormInt k : ℝ)) ^ a := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_inv_one_add_supNormInt_pow hD).mul_left C)
  · have : (0 : ℝ) ≤ 1 + (supNormInt k : ℝ) := by positivity
    exact mul_nonneg (hc k) (Real.rpow_nonneg this a)
  · set w : ℝ := 1 + (supNormInt k : ℝ) with hw
    have hw1 : 1 ≤ w := by
      rw [hw]
      have : (0 : ℝ) ≤ (supNormInt k : ℝ) := by positivity
      linarith
    have h1 : w ^ a ≤ w ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hw1 han
    have h2 : c k * w ^ n = c k * w ^ (n + D + 1) * (w ^ (D + 1))⁻¹ := by
      have : n + D + 1 = n + (D + 1) := by omega
      rw [this, pow_add]
      field_simp
    calc c k * w ^ a ≤ c k * w ^ n := mul_le_mul_of_nonneg_left h1 (hc k)
      _ = c k * w ^ (n + D + 1) * (w ^ (D + 1))⁻¹ := h2
      _ ≤ C * (w ^ (D + 1))⁻¹ := mul_le_mul_of_nonneg_right (hC k) (by positivity)
end Sums
section Convergence
variable {s : StandingParameters} {p : ℕ} {P : ℝ}
theorem summable_fourierCoeff_mul_rpow (hp : 1 ≤ p) (hP : 0 < P)
    (hT : ∀ F ∈ testFns (fundamentalBoxPow s p P),
      (∀ α : PowerSeries.MultiIndex (4 * p), multiDeriv α F ∈ testFns (fundamentalBoxPow s p P)) ∧
        tupleSupNorm F ≠ ⊤)
    {F : Tuple s .euclidean p → ℂ} (hF : F ∈ testFns (fundamentalBoxPow s p P))
    (hN : ∀ ν, cnNorm ν F ≠ ⊤) (a : ℝ) :
    Summable fun k : Fin (4 * p) → ℤ =>
      ‖fourierCoeff P F k‖ * (1 + (supNormInt k : ℝ)) ^ a := by
  set ν := ⌈a⌉₊ + 4 * p + 1 with hν
  set N := (cnNorm ν F).toReal with hNdef
  refine summable_mul_rpow_of_bound (by omega) (fun _ => norm_nonneg _) (Nat.le_ceil a)
    (C := ‖fourierCoeff P F 0‖ + (P / Real.pi) ^ ν * N) fun k => ?_
  have hB : 0 ≤ (P / Real.pi) ^ ν * N := by positivity
  by_cases hk : k = 0
  · subst hk
    have h0 : supNormInt (0 : Fin (4 * p) → ℤ) = 0 := by
      simp [supNormInt]
    simp only [h0, Nat.cast_zero, add_zero, one_pow, mul_one]
    linarith
  · have h1 : (1 : ℝ) ≤ (supNormInt k : ℝ) := by
      exact_mod_cast one_le_supNormInt hk
    set m : ℝ := (supNormInt k : ℝ) with hm
    have hdec := fourierCoeff_decay hp hP hT hF k hk ν
    have hreal : ‖fourierCoeff P F k‖ ≤ (P / (2 * Real.pi * m)) ^ ν * N := by
      have h2 := (ENNReal.ofReal_le_iff_le_toReal
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN ν))).1 hdec
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    have hpow : ((1 : ℝ) + m) ^ ν ≤ (2 * m) ^ ν :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hprod : (P / (2 * Real.pi * m)) ^ ν * (2 * m) ^ ν = (P / Real.pi) ^ ν := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc ‖fourierCoeff P F k‖ * (1 + m) ^ ν
        ≤ ((P / (2 * Real.pi * m)) ^ ν * N) * (2 * m) ^ ν :=
          mul_le_mul hreal hpow (by positivity) (by positivity)
      _ = (P / Real.pi) ^ ν * N := by rw [← hprod]; ring
      _ ≤ _ := by linarith [norm_nonneg (fourierCoeff P F 0)]
end Convergence
section Product
def coordIndexEquiv (p : ℕ) : Fin p × Fin 4 ≃ Fin (4 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 4))
theorem coordIndexEquiv_val {p : ℕ} (i : Fin p) (μ : Fin 4) :
    (coordIndexEquiv p (i, μ) : ℕ) = 4 * (i : ℕ) + μ := by
  simp [coordIndexEquiv, finProdFinEquiv, Nat.add_comm]
theorem flattenCoords_symm_coordIndex {p : ℕ} (u : Fin (4 * p) → ℝ) (i : Fin p) (μ : Fin 4) :
    (flattenCoords p).symm u i μ = u (coordIndexEquiv p (i, μ)) := by
  have hh : 4 * (i : ℕ) + μ < 4 * p := coordIndexEquiv_val i μ ▸ (coordIndexEquiv p (i, μ)).2
  rw [flattenCoords_symm_apply u i μ hh]
  exact congrArg u (Fin.ext (coordIndexEquiv_val i μ).symm)
def unflattenMeasurableEquiv (p : ℕ) : (Fin (4 * p) → ℝ) ≃ᵐ (Fin p → Fin 4 → ℝ) where
  toEquiv := (flattenCoords p).symm
  measurable_toFun := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => ?_
    have h : (fun u : Fin (4 * p) → ℝ => (flattenCoords p).symm u i μ) =
        fun u => u (coordIndexEquiv p (i, μ)) :=
      funext fun u => flattenCoords_symm_coordIndex u i μ
    simpa only [Equiv.toFun_as_coe, h] using measurable_pi_apply (coordIndexEquiv p (i, μ))
  measurable_invFun := by
    refine measurable_pi_iff.2 fun j => ?_
    obtain ⟨⟨i, μ⟩, rfl⟩ := (coordIndexEquiv p).surjective j
    have h : (fun x : Fin p → Fin 4 → ℝ => flattenCoords p x (coordIndexEquiv p (i, μ))) =
        fun x => x i μ := by
      funext x
      have := flattenCoords_symm_coordIndex (flattenCoords p x) i μ
      rw [Equiv.symm_apply_apply] at this
      exact this.symm
    have hm : Measurable fun x : Fin p → Fin 4 → ℝ => x i μ :=
      (measurable_pi_apply μ).comp (measurable_pi_apply i)
    simpa only [Equiv.invFun_as_coe, Equiv.symm_symm, h] using hm
theorem measurePreserving_unflatten (p : ℕ) :
    MeasurePreserving (unflattenMeasurableEquiv p) volume volume := by
  refine ⟨(unflattenMeasurableEquiv p).measurable, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun _ => Set.pi univ '' Set.pi univ fun _ => {t : Set ℝ | MeasurableSet t})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ =>
      (volume : Measure ℝ).toFiniteSpanningSetsIn) ?_).symm
  intro S hS
  choose t ht hSt using hS
  have hmeas : ∀ i μ, MeasurableSet (t i μ) := fun i μ => ht i μ (mem_univ μ)
  have hpre : (unflattenMeasurableEquiv p) ⁻¹' (Set.pi univ S) =
      Set.pi univ fun j => t ((coordIndexEquiv p).symm j).1 ((coordIndexEquiv p).symm j).2 := by
    ext u
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, ← hSt]
    constructor
    · intro h j
      have := h ((coordIndexEquiv p).symm j).1 ((coordIndexEquiv p).symm j).2
      have h2 := flattenCoords_symm_coordIndex u ((coordIndexEquiv p).symm j).1
        ((coordIndexEquiv p).symm j).2
      simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h2
      rw [← h2]
      exact this
    · intro h i μ
      have := h (coordIndexEquiv p (i, μ))
      simp only [Equiv.symm_apply_apply] at this
      have h2 := flattenCoords_symm_coordIndex u i μ
      show (flattenCoords p).symm u i μ ∈ t i μ
      rw [h2]
      exact this
  have hSm : MeasurableSet (Set.pi univ S) :=
    MeasurableSet.univ_pi fun i => by
      rw [← hSt]
      exact MeasurableSet.univ_pi (hmeas i)
  rw [Measure.map_apply (unflattenMeasurableEquiv p).measurable hSm, hpre, volume_pi_pi]
  rw [← (coordIndexEquiv p).prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSt, Measure.pi_pi]
  simp
theorem integral_prod_blocks {p : ℕ} (ψ : Fin p → (Fin 4 → ℝ) → ℂ) :
    ∫ u : Fin (4 * p) → ℝ, ∏ i, ψ i ((flattenCoords p).symm u i) = ∏ i, ∫ x, ψ i x := by
  rw [← integral_fintype_prod_volume_eq_prod ψ]
  exact (measurePreserving_unflatten p).integral_comp
    (unflattenMeasurableEquiv p).measurableEmbedding (fun x => ∏ i, ψ i (x i))
variable {s : StandingParameters} {P : ℝ}
theorem flattenCoords_one_symm (u : Fin (4 * 1) → ℝ) : (flattenCoords 1).symm u 0 = u := by
  funext μ
  exact (flattenCoords_symm_apply u 0 μ (by have := μ.2; omega)).trans
    (congrArg u (Fin.ext (by simp)))
theorem fourierCoeff_single {g : Pt s .euclidean → ℂ}
    (hg : ofSinglePoint g ∈ testFns (fundamentalBoxPow s 1 P)) (κ : Fin 4 → ℤ) :
    fourierCoeff (n := 1) P (ofSinglePoint g) κ =
      ((P : ℂ) ^ 4)⁻¹ * ∫ x : Fin 4 → ℝ, g x * conj (fourierMode P κ x) := by
  rw [fourierCoeff_eq_integral hg]
  have h : ∀ u : Fin (4 * 1) → ℝ,
      ofSinglePoint g (tupleProj s .euclidean 1 u) = g u := fun u =>
    congrArg g (flattenCoords_one_symm u)
  simp only [h]
theorem fourierCoeff_tensorProd {p : ℕ} (h : Fin p → Pt s .euclidean → ℂ)
    (hh : ∀ i, ofSinglePoint (h i) ∈ testFns (fundamentalBoxPow s 1 P))
    (ht : tensorProd h ∈ testFns (fundamentalBoxPow s p P)) (k : Fin (4 * p) → ℤ) :
    fourierCoeff P (tensorProd h) k =
      ∏ i, fourierCoeff (n := 1) P (ofSinglePoint (h i)) (blockOf k i) := by
  let ψ : Fin p → (Fin 4 → ℝ) → ℂ := fun i x => h i x * conj (fourierMode P (blockOf k i) x)
  have hprod : ∀ u : Fin (4 * p) → ℝ,
      tensorProd h (tupleProj s .euclidean p u) * conj (fourierMode P k u) =
        ∏ i, ψ i ((flattenCoords p).symm u i) := by
    intro u
    have hm : fourierMode P k u =
        ∏ i, fourierMode P (blockOf k i) ((flattenCoords p).symm u i) :=
      fourierMode_eq_tensorProd s P k u
    rw [hm, map_prod]
    exact Finset.prod_mul_distrib.symm
  have hint : ∫ u, tensorProd h (tupleProj s .euclidean p u) * conj (fourierMode P k u) =
      ∏ i, ∫ x, ψ i x := by
    rw [← integral_prod_blocks ψ]
    exact integral_congr_ae (Filter.Eventually.of_forall hprod)
  rw [fourierCoeff_eq_integral ht, hint]
  simp only [fun i => fourierCoeff_single (hh i) (blockOf k i)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    ← pow_mul]
end Product
theorem fourierCoeffBounds_of_testFnOperations (hyp : TestFnOperations) :
    FourierCoeffBounds := by
  intro s p P hp hP
  have hbase := hyp s .euclidean p hp
  have hopen := isOpen_fundamentalBoxPow s p P
  have hparts := (hbase.2.1 _ hopen).2.2.1
  have hN : ∀ F ∈ testFns (fundamentalBoxPow s p P), ∀ ν, cnNorm ν F ≠ ⊤ :=
    fun F hF ν => ((hparts F hF).2.2.2 ν).ne
  have hs : ∀ F ∈ testFns (fundamentalBoxPow s p P), tupleSupNorm F ≠ ⊤ := fun F hF => by
    rw [tupleSupNorm_eq_cnNorm_zero]
    exact hN F hF 0
  have hT : ∀ F ∈ testFns (fundamentalBoxPow s p P),
      (∀ α : PowerSeries.MultiIndex (4 * p), multiDeriv α F ∈ testFns (fundamentalBoxPow s p P)) ∧
        tupleSupNorm F ≠ ⊤ := fun F hF => ⟨fun α => ((hparts F hF).2.2.1 α).1, hs F hF⟩
  refine ⟨fun k => isComplexLinearForm_fourierCoeff hP hs k, fun F hF => ⟨fun k => ?_, fun j k => ?_,
    fun k hk ν => fourierCoeff_decay hp hP hT hF k hk ν,
    fun a _ => summable_fourierCoeff_mul_rpow hp hP hT hF (hN F hF) a⟩, fun m hm => ?_,
    fun h hh => ?_⟩
  · exact (ENNReal.ofReal_le_iff_le_toReal (hs F hF)).2 (norm_fourierCoeff_le hP (hs F hF) k)
  · have h1 := (hT F hF).1 (Pi.single j 1)
    exact fourierCoeff_partial hP hF j h1 (hs F hF) (hs _ h1) k
  · have h1 := shell_card_le (D := 4 * p) (by omega) hm
    have h2 := shell_bound_le_three (D := 4 * p) hm
    push_cast at h1 h2
    exact ⟨finite_modesWithSupNorm m, ncard_modesWithSupNorm hm, h1, h2⟩
  · have hpi : Set.pi univ (fun _ : Fin p => fundamentalBox s P) = fundamentalBoxPow s p P := by
      ext y
      simp [fundamentalBoxPow]
    have hone : fundamentalBoxPow s 1 P = singletonTupleSet (fundamentalBox s P) := by
      ext y
      simp [fundamentalBoxPow, singletonTupleSet, Fin.forall_fin_one]
    have ht := (hbase.2.2.2 (fun _ => fundamentalBox s P) h (fun _ => isOpen_fundamentalBox s P)
      (fun i => hone ▸ hh i)).1
    rw [hpi] at ht
    exact ⟨ht, fun k => fourierCoeff_tensorProd h hh ht k⟩
end Torus.FourierBox.Estimates
end YangMills.Construction
