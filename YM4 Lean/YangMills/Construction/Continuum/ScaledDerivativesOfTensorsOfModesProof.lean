import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Continuum.ScaledDerivativesOfTensorsOfModes
import Mathlib
set_option autoImplicit false
open scoped ContDiff Matrix
noncomputable section
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.Bumps
namespace ModeTensor
variable {n : ℕ}
def IsUnitDirectionalDeriv (g : Config n → ℂ) (k : ℕ) (h : Config n → ℂ) : Prop :=
  ∃ v : Fin k → Config n, (∀ j, ‖v j‖ ≤ 1) ∧ ∀ x, h x = iteratedFDeriv ℝ k g x v
theorem norm_single_single_le (i : Fin n) (μ : Fin 4) :
    ‖(Pi.single i (Pi.single μ 1) : Config n)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = μ
    · subst hb
      simp
    · simp [hb]
  · simp [ha]
theorem IsUnitDirectionalDeriv.partial_succ {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (μ : Fin 4) {k : ℕ} {h : Config n → ℂ}
    (H : IsUnitDirectionalDeriv g k h) :
    IsUnitDirectionalDeriv g (k + 1) (coordPartial i μ h) := by
  obtain ⟨v, hv, hh⟩ := H
  refine ⟨Fin.cons (Pi.single i (Pi.single μ 1)) v, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using norm_single_single_le i μ
    · simpa using hv j
  · intro x
    have hfun : h = fun z => iteratedFDeriv ℝ k g z v := funext hh
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) x :=
      (hg.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k)) x
    rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons, coordPartial, hfun]
    have := (HasFDerivAt.hasLineDerivAt
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Config n) ℂ v).hasFDerivAt.comp x
        hd.hasFDerivAt)
      (Pi.single i (Pi.single μ 1) : Config n)).lineDeriv
    exact this
theorem IsUnitDirectionalDeriv.iterate_partial {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (μ : Fin 4) (r : ℕ) {k : ℕ} {h : Config n → ℂ}
    (H : IsUnitDirectionalDeriv g k h) :
    IsUnitDirectionalDeriv g (k + r) ((coordPartial i μ)^[r] h) := by
  induction r with
  | zero => simpa using H
  | succ r ih =>
    rw [Function.iterate_succ_apply', ← add_assoc]
    exact ih.partial_succ hg i μ
theorem IsUnitDirectionalDeriv.fold_inner {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g)
    (α : MultiIndex n) (i : Fin n) (l : List (Fin 4)) {k : ℕ} {h : Config n → ℂ}
    (H : IsUnitDirectionalDeriv g k h) :
    IsUnitDirectionalDeriv g (k + (l.map fun μ => α i μ).sum)
      (l.foldr (fun μ h' => (coordPartial i μ)^[α i μ] h') h) := by
  induction l with
  | nil => simpa using H
  | cons μ l ih =>
    have := ih.iterate_partial hg i μ (α i μ)
    simpa [add_assoc, add_comm, add_left_comm] using this
theorem IsUnitDirectionalDeriv.fold_outer {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g)
    (α : MultiIndex n) (l : List (Fin n)) :
    IsUnitDirectionalDeriv g (l.map fun i => ∑ μ, α i μ).sum
      (l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordPartial i μ)^[α i μ] h') h) g) := by
  induction l with
  | nil =>
    show IsUnitDirectionalDeriv g 0 g
    exact ⟨Fin.elim0, fun j => j.elim0, fun x => by simp⟩
  | cons i l ih =>
    have := ih.fold_inner hg α i (List.finRange 4)
    have hs : ((List.finRange 4).map fun μ => α i μ).sum = ∑ μ, α i μ :=
      (Fin.sum_univ_def _).symm
    rw [hs] at this
    simpa [add_comm] using this
theorem norm_iteratedPartial_le {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (α : MultiIndex n)
    (x : Config n) : ‖iteratedPartial α g x‖ ≤ ‖iteratedFDeriv ℝ α.order g x‖ := by
  have hsize : ((List.finRange n).map fun i => ∑ μ, α i μ).sum = α.order :=
    (Fin.sum_univ_def _).symm
  have H := IsUnitDirectionalDeriv.fold_outer hg α (List.finRange n)
  rw [hsize] at H
  obtain ⟨v, hv, hh⟩ := H
  have hx : iteratedPartial α g x = iteratedFDeriv ℝ α.order g x v := hh x
  rw [hx]
  calc ‖iteratedFDeriv ℝ α.order g x v‖ ≤ ‖iteratedFDeriv ℝ α.order g x‖ * ∏ j, ‖v j‖ :=
        (iteratedFDeriv ℝ α.order g x).le_opNorm v
    _ ≤ ‖iteratedFDeriv ℝ α.order g x‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hv j)
    _ = _ := mul_one _
theorem norm_iteratedFDeriv_cexp_le (L : Config n →L[ℝ] ℂ) (y : Config n)
    (hL : ∀ v, (L v).re = 0) (k : ℕ) (x : Config n) :
    ‖iteratedFDeriv ℝ k (fun z => Complex.exp (L (z - y))) x‖ ≤ ‖L‖ ^ k := by
  have hsm : ContDiff ℝ ∞ (fun z => Complex.exp (L (z - y))) :=
    (L.contDiff.comp (contDiff_id.sub contDiff_const)).cexp
  induction k generalizing x with
  | zero =>
    simp [Complex.norm_exp, hL]
  | succ k ih =>
    let A : ℂ →L[ℝ] (Config n →L[ℝ] ℂ) :=
      (ContinuousLinearMap.toSpanSingleton ℂ L).restrictScalars ℝ
    have hA : ‖A‖ ≤ ‖L‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun z => ?_
      simp [A, norm_smul, mul_comm]
    have hfd : fderiv ℝ (fun z => Complex.exp (L (z - y))) =
        A ∘ fun z => Complex.exp (L (z - y)) := by
      funext z
      have h1 : HasFDerivAt (fun z => L (z - y)) L z := by
        simpa using L.hasFDerivAt (x := z)
      simpa [A] using h1.cexp.fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd,
      A.iteratedFDeriv_comp_left hsm.contDiffAt (by exact_mod_cast le_top), pow_succ']
    calc _ ≤ ‖A‖ * ‖iteratedFDeriv ℝ k (fun z => Complex.exp (L (z - y))) x‖ :=
          A.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * ‖L‖ ^ k := mul_le_mul hA (ih x) (norm_nonneg _) (norm_nonneg _)
def imagPhase (ξ : Config n) : Config n →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM ∘L
    ∑ i, ∑ c, ξ i c • ((ContinuousLinearMap.proj c : (Fin 4 → ℝ) →L[ℝ] ℝ) ∘L
      (ContinuousLinearMap.proj i : Config n →L[ℝ] (Fin 4 → ℝ))))
theorem imagPhase_apply (ξ v : Config n) :
    imagPhase ξ v = Complex.I * ((configDot ξ v : ℝ) : ℂ) := by
  simp [imagPhase, configDot, dotProduct]
theorem abs_apply_le_coordSupNorm (ξ : Config n) (i : Fin n) (c : Fin 4) :
    |ξ i c| ≤ coordSupNorm ξ := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.abs_apply_le_coordSupNorm <;> assumption
theorem coordSupNorm_nonneg (ξ : Config n) : 0 ≤ coordSupNorm ξ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem norm_imagPhase_le (ξ : Config n) : ‖imagPhase ξ‖ ≤ 4 * n * coordSupNorm ξ := by
  have hn := coordSupNorm_nonneg ξ
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [imagPhase_apply, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hterm : ∀ i c, |ξ i c * v i c| ≤ coordSupNorm ξ * ‖v‖ := fun i c => by
    rw [abs_mul]
    refine mul_le_mul (abs_apply_le_coordSupNorm ξ i c) ?_ (abs_nonneg _) hn
    exact (norm_le_pi_norm (v i) c).trans (norm_le_pi_norm v i)
  calc |configDot ξ v| ≤ ∑ i, ∑ c, |ξ i c * v i c| := by
        simp only [configDot, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _c : Fin 4, coordSupNorm ξ * ‖v‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ => hterm i c
    _ = 4 * n * coordSupNorm ξ * ‖v‖ := by
        simp
        ring
def cutoffProduct (Q : PointSystem n) : Config n → ℂ := fun x =>
  ((∏ i, cubeBump (Q.scale⁻¹ • (x i - Q.base i)) : ℝ) : ℂ)
theorem tensorProd_modeFamily (Q : PointSystem n) (ξ : Config n) :
    tensorProd (Q.modeFamily ξ) =
      fun x => cutoffProduct Q x * Complex.exp (imagPhase ξ (x - Q.base)) := by
  funext x
  simp only [tensorProd, PointSystem.modeFamily, PointSystem.modeFun, Finset.prod_mul_distrib,
    cutoffProduct, imagPhase_apply]
  congr 1
  · push_cast
    rfl
  · rw [← Complex.exp_sum, configDot, Complex.ofReal_sum, Finset.mul_sum]
    rfl
theorem cutoffProduct_contDiff (hχ : ContDiff ℝ ∞ cubeBump) (Q : PointSystem n) :
    ContDiff ℝ ∞ (cutoffProduct Q) := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ContDiff ℝ ∞ fun x : Config n => cubeBump (Q.scale⁻¹ • (x i - Q.base i)) := fun i _ =>
    hχ.comp ((((ContinuousLinearMap.proj i : Config n →L[ℝ] (Fin 4 → ℝ)).contDiff).sub
      contDiff_const).const_smul Q.scale⁻¹)
  exact Complex.ofRealCLM.contDiff.comp (contDiff_prod hi)
theorem cutoffProduct_hasCompactSupport (hχ : HasCompactSupport cubeBump) (Q : PointSystem n) :
    HasCompactSupport (cutoffProduct Q) := by
  have hK : IsCompact (Set.pi Set.univ fun i : Fin n =>
      (fun z : Fin 4 → ℝ => Q.base i + Q.scale • z) '' tsupport cubeBump) :=
    isCompact_univ_pi fun i =>
      IsCompact.image hχ (continuous_const.add (continuous_const_smul _))
  refine HasCompactSupport.intro hK fun x hx => ?_
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Set.univ, x i ∉
      (fun z : Fin 4 → ℝ => Q.base i + Q.scale • z) '' tsupport cubeBump := by
    simpa [Set.mem_pi] using hx
  have hz : Q.scale⁻¹ • (x i - Q.base i) ∉ tsupport cubeBump := by
    intro hmem
    refine hi ⟨_, hmem, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ Q.scale_pos.ne']
  have h0 : cubeBump (Q.scale⁻¹ • (x i - Q.base i)) = 0 := image_eq_zero_of_notMem_tsupport hz
  simp only [cutoffProduct]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, Complex.ofReal_zero]
end ModeTensor
open ModeTensor in
theorem scaledModeTensorDerivBound_of_gevreyBumpBounds (hb : GevreyBumpBounds) :
    ScaledModeTensorDerivBound := by
  obtain ⟨-, -, -, -, ⟨hχ, hχc, -⟩, -⟩ := hb
  intro n _ Q ν
  have hP := cutoffProduct_contDiff hχ Q
  have hPc := cutoffProduct_hasCompactSupport hχc Q
  have hbound : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ j (cutoffProduct Q) x‖ ≤ B := by
    intro j
    obtain ⟨C, hC⟩ := (hPc.iteratedFDeriv j).exists_bound_of_continuous
      (hP.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hbound
  have hm0 := Q.scale_pos
  have hm1 : Q.scale ≤ 1 := Q.scale_le_half.trans (by norm_num)
  refine ⟨2 ^ ν * (1 + 4 * n) ^ ν * ∑ j ∈ Finset.range (ν + 1), B j, ?_, fun ξ _ => ?_⟩
  · have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range (ν + 1)) => hB0 j
    positivity
  have hE : ContDiff ℝ ∞ fun x => Complex.exp (imagPhase ξ (x - Q.base)) :=
    ((imagPhase ξ).contDiff.comp (contDiff_id.sub contDiff_const)).cexp
  have hT : ContDiff ℝ ∞ (tensorProd (Q.modeFamily ξ)) := by
    rw [tensorProd_modeFamily]
    exact hP.mul hE
  refine ⟨hT, fun α hα x => ?_⟩
  have hre : ∀ v, (imagPhase ξ v).re = 0 := fun v => by simp [imagPhase_apply]
  have ht := coordSupNorm_nonneg ξ
  set k := α.order with hk
  set t := coordSupNorm ξ with htdef
  have hleib : ‖iteratedFDeriv ℝ k (tensorProd (Q.modeFamily ξ)) x‖ ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * (4 * n * t) ^ (k - j) := by
    rw [tensorProd_modeFamily]
    refine (norm_iteratedFDeriv_mul_le hP hE x (by exact_mod_cast le_top)).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hB j x) (Nat.cast_nonneg _)) ?_ (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hB0 j))
    exact (norm_iteratedFDeriv_cexp_le (imagPhase ξ) Q.base hre _ x).trans
      (pow_le_pow_left₀ (norm_nonneg _) (norm_imagPhase_le ξ) _)
  have hone : (1 : ℝ) ≤ 1 + Q.scale * t := by
    have := mul_nonneg hm0.le ht
    linarith
  have hn1 : (1 : ℝ) ≤ 1 + 4 * n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hterm : ∀ j ∈ Finset.range (k + 1),
      Q.scale ^ k * ((k.choose j : ℝ) * B j * (4 * n * t) ^ (k - j)) ≤
        2 ^ ν * (1 + 4 * n) ^ ν * B j * (1 + Q.scale * t) ^ ν := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hsplit : Q.scale ^ k * ((k.choose j : ℝ) * B j * (4 * n * t) ^ (k - j)) =
        (k.choose j : ℝ) * Q.scale ^ j * (4 * n : ℝ) ^ (k - j) * B j *
          (Q.scale * t) ^ (k - j) := by
      have : Q.scale ^ k = Q.scale ^ j * Q.scale ^ (k - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjk]
      rw [this, mul_pow, mul_pow]
      ring
    rw [hsplit]
    have h1 : (k.choose j : ℝ) ≤ 2 ^ ν := by
      have h := (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by norm_num) hα)
      exact_mod_cast h
    have h2 : Q.scale ^ j ≤ 1 := pow_le_one₀ hm0.le hm1
    have h3 : (4 * n : ℝ) ^ (k - j) ≤ (1 + 4 * n) ^ ν := by
      calc (4 * n : ℝ) ^ (k - j) ≤ (1 + 4 * n) ^ (k - j) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (1 + 4 * n) ^ ν := pow_le_pow_right₀ hn1 ((Nat.sub_le _ _).trans hα)
    have h4 : (Q.scale * t) ^ (k - j) ≤ (1 + Q.scale * t) ^ ν := by
      calc (Q.scale * t) ^ (k - j) ≤ (1 + Q.scale * t) ^ (k - j) :=
            pow_le_pow_left₀ (mul_nonneg hm0.le ht) (by linarith) _
        _ ≤ (1 + Q.scale * t) ^ ν := pow_le_pow_right₀ hone ((Nat.sub_le _ _).trans hα)
    have h12 : (k.choose j : ℝ) * Q.scale ^ j ≤ 2 ^ ν := by
      calc (k.choose j : ℝ) * Q.scale ^ j ≤ 2 ^ ν * 1 :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 2 ^ ν := mul_one _
    have h123 : (k.choose j : ℝ) * Q.scale ^ j * (4 * n : ℝ) ^ (k - j) ≤
        2 ^ ν * (1 + 4 * n) ^ ν := mul_le_mul h12 h3 (by positivity) (by positivity)
    have h1234 : (k.choose j : ℝ) * Q.scale ^ j * (4 * n : ℝ) ^ (k - j) * B j ≤
        2 ^ ν * (1 + 4 * n) ^ ν * B j := mul_le_mul_of_nonneg_right h123 (hB0 j)
    exact mul_le_mul h1234 h4 (by have := mul_nonneg hm0.le ht; positivity)
      (mul_nonneg (by positivity) (hB0 j))
  have hpow : (0 : ℝ) ≤ (1 + Q.scale * t) ^ ν := by positivity
  calc Q.scale ^ k * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖
      ≤ Q.scale ^ k * ‖iteratedFDeriv ℝ k (tensorProd (Q.modeFamily ξ)) x‖ :=
        mul_le_mul_of_nonneg_left (norm_iteratedPartial_le hT α x) (by positivity)
    _ ≤ Q.scale ^ k * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * B j * (4 * n * t) ^ (k - j) :=
        mul_le_mul_of_nonneg_left hleib (by positivity)
    _ = ∑ j ∈ Finset.range (k + 1),
          Q.scale ^ k * ((k.choose j : ℝ) * B j * (4 * n * t) ^ (k - j)) := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), 2 ^ ν * (1 + 4 * n) ^ ν * B j * (1 + Q.scale * t) ^ ν :=
        Finset.sum_le_sum hterm
    _ = 2 ^ ν * (1 + 4 * n) ^ ν * (∑ j ∈ Finset.range (k + 1), B j) * (1 + Q.scale * t) ^ ν := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 ^ ν * (1 + 4 * n) ^ ν * (∑ j ∈ Finset.range (ν + 1), B j) * (1 + Q.scale * t) ^ ν := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hpow
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hB0 j
        exact Finset.range_subset_range.2 (Nat.succ_le_succ hα)
end YangMills.Construction.ConfigSpace
