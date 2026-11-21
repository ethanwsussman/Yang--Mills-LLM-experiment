import YangMills.Construction.ResponseInTheExpansion.MixedDerivativesAlongSlots
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.DirectionalDerivatives
variable {F : BlockFrame}
private local instance quaternionNormedAlgebraRat : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Quaternion ℝ)
private theorem expUnit_smul_mul_expUnit_smul (a b : ℝ) (X : imaginaryQuaternions) : expUnit (a • X) * expUnit (b • X) = expUnit ((a + b) • X) := by
  apply Subtype.ext
  have hcomm : Commute ((a • X : imaginaryQuaternions) : Quaternion ℝ) ((b • X : imaginaryQuaternions) : Quaternion ℝ) := by
    have ha : ((a • X : imaginaryQuaternions) : Quaternion ℝ) = a • (X : Quaternion ℝ) := rfl
    have hb : ((b • X : imaginaryQuaternions) : Quaternion ℝ) = b • (X : Quaternion ℝ) := rfl
    rw [ha, hb]
    exact ((Commute.refl _).smul_left a).smul_right b
  have hsum : (((a + b) • X : imaginaryQuaternions) : Quaternion ℝ) = ((a • X : imaginaryQuaternions) : Quaternion ℝ) + ((b • X : imaginaryQuaternions) : Quaternion ℝ) := by
    rw [add_smul]
    rfl
  simp only [expUnit]
  show NormedSpace.exp _ * NormedSpace.exp _ = NormedSpace.exp _
  rw [hsum, NormedSpace.exp_add_of_commute hcomm]
private theorem fderiv_fderiv_comp_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [CompleteSpace E] (f : E → ℝ) (J : E' →L[ℝ] E) (x : E') (hf : AnalyticAt ℝ f (J x)) (u v : E') :
    fderiv ℝ (fderiv ℝ (fun y => f (J y))) x u v = fderiv ℝ (fderiv ℝ f) (J x) (J u) (J v) := by
  have hev : ∀ᶠ y in nhds x, fderiv ℝ (fun y => f (J y)) y = (fderiv ℝ f (J y)).comp J := by
    have h1 := hf.eventually_analyticAt
    have h2 := (J.continuous.tendsto x).eventually h1
    filter_upwards [h2] with y hy
    exact (hy.differentiableAt.hasFDerivAt.comp y J.hasFDerivAt).fderiv
  rw [Filter.EventuallyEq.fderiv_eq hev]
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (J x)) (J x) :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y => fderiv ℝ f (J y)) ((fderiv ℝ (fderiv ℝ f) (J x)).comp J) x :=
    h1.comp x J.hasFDerivAt
  have h3 := h2.clm_comp (hasFDerivAt_const J x)
  rw [h3.fderiv]
  simp
abbrev _root_.YangMills.SharedProofs.p70139 := @fderiv_fderiv_comp_clm
private def embedTail : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun l : Fin 3 =>
    (![0, ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1] : Fin 3 → ((Fin 2 → ℝ) →L[ℝ] ℝ)) l
private theorem embedTail_apply (σ : Fin 2 → ℝ) : embedTail σ = ![0, σ 0, σ 1] := by
  ext l
  fin_cases l <;> simp [embedTail]
private theorem evalAlong_pair_eq_triple (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (r : ChartDirection F) (σ : Fin 2 → ℝ) :
    evalAlong Φ w V ![Sum.inl p, Sum.inl q] σ = evalAlong Φ w V ![r, Sum.inl p, Sum.inl q] (embedTail σ) := by
  rw [embedTail_apply]
  unfold evalAlong
  simp [Fin.sum_univ_two, Fin.sum_univ_three, directionMove]
private theorem evalAlong_shift (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (r : ChartDirection F) (θ : ℝ) (σ : Fin 3 → ℝ) :
    evalAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q] σ =
      evalAlong Φ w V ![r, Sum.inl p, Sum.inl q] (σ + ![θ, 0, 0]) := by
  unfold evalAlong shiftCoordinates shiftField
  congr 1
  · funext x i
    simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [add_zero]
    module
  · funext y i
    simp only [leftTranslate, Fin.sum_univ_three, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [add_zero, directionMove, smul_zero, ← mul_assoc, expUnit_smul_mul_expUnit_smul]
private theorem mixedDerivAlong_shift_sub_le (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (r : ChartDirection F) (B t : ℝ) (ht : 0 ≤ t)
    (hk : ∀ θ, 0 ≤ θ → θ ≤ t →
        AnalyticAt ℝ (evalAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q]) 0 ∧
        |mixedDerivAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q]| ≤ B) :
    |mixedDerivAlong Φ (shiftCoordinates r t w) (shiftField r t V) ![Sum.inl p, Sum.inl q] -
        mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q]| ≤ B * t := by
  set g := evalAlong Φ w V ![r, Sum.inl p, Sum.inl q] with hg
  have hshift : ∀ θ, evalAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q] =
      fun σ => g (σ + ![θ, 0, 0]) := fun θ => funext fun σ => evalAlong_shift Φ w V p q r θ σ
  have hanalytic : ∀ θ, 0 ≤ θ → θ ≤ t → AnalyticAt ℝ g ![θ, 0, 0] := by
    intro θ h0 h1
    have h := (hk θ h0 h1).1
    rw [hshift] at h
    have e : g = fun σ => (fun σ => g (σ + ![θ, 0, 0])) (σ - ![θ, 0, 0]) := by
      funext σ
      show g σ = g (σ - ![θ, 0, 0] + ![θ, 0, 0])
      rw [sub_add_cancel]
    rw [e]
    have h3 : AnalyticAt ℝ (fun σ : Fin 3 → ℝ => σ - ![θ, 0, 0]) ![θ, 0, 0] :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℝ (fun σ => g (σ + ![θ, 0, 0])) ((fun σ : Fin 3 → ℝ => σ - ![θ, 0, 0]) ![θ, 0, 0]) := by
      simpa using h
    exact AnalyticAt.comp (g := fun σ => g (σ + ![θ, 0, 0])) (f := fun σ : Fin 3 → ℝ => σ - ![θ, 0, 0]) h2 h3
  set m2 : Fin 2 → (Fin 3 → ℝ) := fun l => Pi.single l.succ 1 with hm2
  have hthird : ∀ θ, mixedDerivAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q] =
      fderiv ℝ (iteratedFDeriv ℝ 2 g) ![θ, 0, 0] (Pi.single 0 1) m2 := by
    intro θ
    unfold mixedDerivAlong
    rw [hshift, iteratedFDeriv_comp_add_right, iteratedFDeriv_succ_apply_left]
    simp only [zero_add]
    rfl
  have hsecond : ∀ θ, 0 ≤ θ → θ ≤ t → mixedDerivAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![Sum.inl p, Sum.inl q] =
      iteratedFDeriv ℝ 2 g ![θ, 0, 0] m2 := by
    intro θ h0 h1
    unfold mixedDerivAlong
    have e1 : evalAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![Sum.inl p, Sum.inl q] =
        fun σ => (fun y => g (y + ![θ, 0, 0])) (embedTail σ) := by
      funext σ
      rw [evalAlong_pair_eq_triple Φ _ _ p q r σ, evalAlong_shift]
    have ha : AnalyticAt ℝ (fun y => g (y + ![θ, 0, 0])) (embedTail 0) := by
      have := (hk θ h0 h1).1
      rw [hshift] at this
      simpa using this
    rw [e1, iteratedFDeriv_two_apply, fderiv_fderiv_comp_clm _ embedTail 0 ha]
    have e2 : (fun y => g (y + ![θ, 0, 0])) = fun y => g (y + ![θ, 0, 0]) := rfl
    have e3 : iteratedFDeriv ℝ 2 (fun y => g (y + ![θ, 0, 0])) 0 = iteratedFDeriv ℝ 2 g ![θ, 0, 0] := by
      rw [iteratedFDeriv_comp_add_right]
      simp
    rw [← e3, iteratedFDeriv_two_apply]
    simp only [map_zero]
    have e4 : ∀ l : Fin 2, embedTail (Pi.single l 1) = m2 l := by
      intro l
      rw [embedTail_apply, hm2]
      fin_cases l <;> ext j <;> fin_cases j <;> simp
    rw [e4 0, e4 1]
  have hline : ∀ θ : ℝ, HasDerivAt (fun u : ℝ => (![u, 0, 0] : Fin 3 → ℝ)) (Pi.single 0 1) θ := by
    intro θ
    have e0 : (fun u : ℝ => (![u, 0, 0] : Fin 3 → ℝ)) = fun u => u • (Pi.single 0 1 : Fin 3 → ℝ) := by
      funext u
      ext l
      fin_cases l <;> simp
    rw [e0]
    simpa using (hasDerivAt_id θ).smul_const (Pi.single 0 1 : Fin 3 → ℝ)
  set D : ℝ → ℝ := fun θ => iteratedFDeriv ℝ 2 g ![θ, 0, 0] m2 with hD
  have hder : ∀ θ ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt D
      (fderiv ℝ (iteratedFDeriv ℝ 2 g) ![θ, 0, 0] (Pi.single 0 1) m2) (Set.Icc 0 t) θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 g) ![θ, 0, 0] :=
      (hanalytic θ hθ.1 hθ.2).contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_top _))
    have h2 := h1.hasFDerivAt.comp_hasDerivAt θ (hline θ)
    have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => (Fin 3 → ℝ)) ℝ m2).hasFDerivAt.comp_hasDerivAt θ h2
    exact h3.hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Ico (0 : ℝ) t,
      ‖fderiv ℝ (iteratedFDeriv ℝ 2 g) ![θ, 0, 0] (Pi.single 0 1) m2‖ ≤ B := by
    intro θ hθ
    have := (hk θ hθ.1 hθ.2.le).2
    rw [hthird] at this
    rwa [Real.norm_eq_abs]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := D) hder hbound t (Set.right_mem_Icc.2 ht)
  rw [sub_zero, Real.norm_eq_abs] at hmv
  have h0 : mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q] = D 0 := by
    have e : mixedDerivAlong Φ (shiftCoordinates r 0 w) (shiftField r 0 V) ![Sum.inl p, Sum.inl q] = mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q] := by
      have e1 : shiftCoordinates r 0 w = w := by
        funext x i
        simp [shiftCoordinates]
      have e2 : shiftField r 0 V = V := by
        funext y i
        apply Subtype.ext
        simp [shiftField, leftTranslate, expUnit]
      rw [e1, e2]
    rw [← e, hsecond 0 le_rfl ht]
  rw [h0, hsecond t ht le_rfl]
  exact hmv
private theorem abs_second_difference_sub_le (f : (Fin 2 → ℝ) → ℝ) (h B E : ℝ) (hh : 0 ≤ h)
    (H : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h → AnalyticAt ℝ f ![s, u] ∧
        |fderiv ℝ (fderiv ℝ f) ![s, u] (Pi.single 0 1) (Pi.single 1 1) - E| ≤ B) :
    |f ![h, h] - f ![h, 0] - f ![0, h] + f ![0, 0] - h ^ 2 * E| ≤ B * h ^ 2 := by
  have hlineFirst : ∀ (u s : ℝ), HasDerivAt (fun s : ℝ => (![s, u] : Fin 2 → ℝ)) (Pi.single 0 1) s := by
    intro u s
    have e0 : (fun s : ℝ => (![s, u] : Fin 2 → ℝ)) = fun s => ![0, u] + s • (Pi.single 0 1 : Fin 2 → ℝ) := by
      funext s
      ext l
      fin_cases l <;> simp
    rw [e0]
    simpa using ((hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin 2 → ℝ)).const_add (![0, u] : Fin 2 → ℝ)
  have hlineSecond : ∀ (s u : ℝ), HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ)) (Pi.single 1 1) u := by
    intro s u
    have e0 : (fun u : ℝ => (![s, u] : Fin 2 → ℝ)) = fun u => ![s, 0] + u • (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext u
      ext l
      fin_cases l <;> simp
    rw [e0]
    simpa using ((hasDerivAt_id u).smul_const (Pi.single 1 1 : Fin 2 → ℝ)).const_add (![s, 0] : Fin 2 → ℝ)
  set d1 : (Fin 2 → ℝ) → ℝ := fun z => fderiv ℝ f z (Pi.single 1 1) with hd1
  have hinner : ∀ u, 0 ≤ u → u ≤ h → |d1 ![h, u] - d1 ![0, u] - h * E| ≤ B * h := by
    intro u hu0 hu1
    set ψ : ℝ → ℝ := fun s => d1 ![s, u] - s * E with hψ
    have hder : ∀ s ∈ Set.Icc (0 : ℝ) h, HasDerivWithinAt ψ
        (fderiv ℝ (fderiv ℝ f) ![s, u] (Pi.single 0 1) (Pi.single 1 1) - E) (Set.Icc 0 h) s := by
      intro s hs
      have h1 : DifferentiableAt ℝ (fderiv ℝ f) ![s, u] :=
        ((H s u hs.1 hs.2 hu0 hu1).1.fderiv).differentiableAt
      have h2 := h1.hasFDerivAt.comp_hasDerivAt s (hlineFirst u s)
      have h3 := h2.clm_apply (hasDerivAt_const s (Pi.single 1 1 : Fin 2 → ℝ))
      simp only [add_zero, ContinuousLinearMap.map_zero] at h3
      have h4 := h3.sub ((hasDerivAt_id s).mul_const E)
      simp only [id, one_mul] at h4
      exact h4.hasDerivWithinAt
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) h,
        ‖fderiv ℝ (fderiv ℝ f) ![s, u] (Pi.single 0 1) (Pi.single 1 1) - E‖ ≤ B := by
      intro s hs
      rw [Real.norm_eq_abs]
      exact (H s u hs.1 hs.2.le hu0 hu1).2
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) hder hbound h (Set.right_mem_Icc.2 hh)
    rw [sub_zero, Real.norm_eq_abs] at hmv
    have e : ψ h - ψ 0 = d1 ![h, u] - d1 ![0, u] - h * E := by
      simp only [hψ]
      ring
    rwa [e] at hmv
  set φ : ℝ → ℝ := fun u => f ![h, u] - f ![0, u] - u * (h * E) with hφ
  have hder : ∀ u ∈ Set.Icc (0 : ℝ) h, HasDerivWithinAt φ (d1 ![h, u] - d1 ![0, u] - h * E) (Set.Icc 0 h) u := by
    intro u hu
    have h1 : DifferentiableAt ℝ f ![h, u] := (H h u hh le_rfl hu.1 hu.2).1.differentiableAt
    have h2 : DifferentiableAt ℝ f ![0, u] := (H 0 u le_rfl hh hu.1 hu.2).1.differentiableAt
    have h3 := h1.hasFDerivAt.comp_hasDerivAt u (hlineSecond h u)
    have h4 := h2.hasFDerivAt.comp_hasDerivAt u (hlineSecond 0 u)
    have h5 := (h3.sub h4).sub ((hasDerivAt_id u).mul_const (h * E))
    simp only [id, one_mul] at h5
    exact h5.hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) h, ‖d1 ![h, u] - d1 ![0, u] - h * E‖ ≤ B * h := by
    intro u hu
    rw [Real.norm_eq_abs]
    exact hinner u hu.1 hu.2.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) hder hbound h (Set.right_mem_Icc.2 hh)
  rw [sub_zero, Real.norm_eq_abs] at hmv
  have e : φ h - φ 0 = f ![h, h] - f ![h, 0] - f ![0, h] + f ![0, 0] - h ^ 2 * E := by
    simp only [hφ]
    ring
  rw [e] at hmv
  calc _ ≤ B * h * h := hmv
    _ = B * h ^ 2 := by ring
theorem mixedDerivLipschitzAndSecondDifference_holds : MixedDerivLipschitzAndSecondDifference :=
  ⟨fun _ Φ w V p q r B t ht hk => mixedDerivAlong_shift_sub_le Φ w V p q r B t ht hk,
    fun f h B E hh H => abs_second_difference_sub_le f h B E hh H⟩
end YangMills.Construction.DirectionalDerivatives
end
