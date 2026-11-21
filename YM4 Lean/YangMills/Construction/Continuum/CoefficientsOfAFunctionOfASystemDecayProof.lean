import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecay
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace FourierDecay
open YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions YangMills.Construction.ShellPieces
variable {n : ℕ}
theorem foldr_eq_of_forall_eq_id {ι X : Type*} (F : ι → X → X) (x₀ : X) (l : List ι)
    (hF : ∀ b ∈ l, F b = id) : l.foldr F x₀ = x₀ := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, ih fun c hc => hF c (List.mem_cons_of_mem b hc),
      hF b List.mem_cons_self]
    rfl
theorem foldr_eq_of_forall_ne_eq_id {ι X : Type*} (F : ι → X → X) (x₀ : X) (l : List ι)
    (hl : l.Nodup) (a : ι) (ha : a ∈ l) (hF : ∀ b ∈ l, b ≠ a → F b = id) :
    l.foldr F x₀ = F a x₀ := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.foldr_cons]
    have hnd := List.nodup_cons.1 hl
    by_cases hba : b = a
    · subst hba
      rw [foldr_eq_of_forall_eq_id F x₀ l fun c hc => hF c (List.mem_cons_of_mem b hc)
        (fun e => hnd.1 (e ▸ hc))]
    · have ha' : a ∈ l := (List.mem_cons.1 ha).resolve_left fun e => hba e.symm
      rw [ih hnd.2 ha' fun c hc => hF c (List.mem_cons_of_mem b hc), hF b List.mem_cons_self hba]
      rfl
theorem iteratedPartial_single (i₀ : Fin n) (μ₀ : Fin 4) (k : ℕ) (g : Config n → ℂ) :
    iteratedPartial (Pi.single i₀ (Pi.single μ₀ k) : MultiIndex n) g =
      (coordPartial i₀ μ₀)^[k] g := by
  unfold iteratedPartial
  rw [foldr_eq_of_forall_ne_eq_id _ g (List.finRange n) (List.nodup_finRange n) i₀
    (List.mem_finRange _)]
  · rw [foldr_eq_of_forall_ne_eq_id _ g (List.finRange 4) (List.nodup_finRange 4) μ₀
      (List.mem_finRange _)]
    · simp
    · intro μ _ hμ
      funext h'
      simp [hμ]
  · intro i _ hi
    funext h
    refine foldr_eq_of_forall_eq_id _ h _ fun μ _ => ?_
    funext h'
    simp [hi]
theorem order_single (i₀ : Fin n) (μ₀ : Fin 4) (k : ℕ) :
    MultiIndex.order (Pi.single i₀ (Pi.single μ₀ k) : MultiIndex n) = k := by
  unfold MultiIndex.order
  rw [Finset.sum_eq_single i₀, Finset.sum_eq_single μ₀]
  · simp
  · intro μ _ hμ
    simp [hμ]
  · simp
  · intro i _ hi
    simp [hi]
  · simp
theorem finite_order_le (ν : ℕ) : Finite {α : MultiIndex n // α.order ≤ ν} := by
  have hrow : {β : Fin 4 → ℕ | ∀ μ, β μ ∈ Set.Iic ν}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Iic ν
  have hall := Set.Finite.pi' (t := fun _ : Fin n => {β : Fin 4 → ℕ | ∀ μ, β μ ∈ Set.Iic ν})
    fun _ => hrow
  refine (hall.subset ?_).to_subtype
  intro α hα i μ
  have hα' : MultiIndex.order α ≤ ν := hα
  have h₁ : α i μ ≤ ∑ μ', α i μ' :=
    Finset.single_le_sum (f := α i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
  have h₂ : ∑ μ', α i μ' ≤ ∑ i', ∑ μ', α i' μ' :=
    Finset.single_le_sum (f := fun i' => ∑ μ', α i' μ') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact h₁.trans (h₂.trans hα')
abbrev axisVector (i : Fin n) (μ : Fin 4) : Config n := Pi.single i (Pi.single μ 1)
theorem coordPartial_eq_fderiv (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    coordPartial i μ g = fun x => fderiv ℝ g x (axisVector i μ) := by
  funext x
  exact (hg.differentiable (by simp) x).lineDeriv_eq_fderiv
theorem contDiff_coordPartial (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (coordPartial i μ g) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.contDiff_coordPartial <;> assumption
theorem tsupport_coordPartial_subset (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) : tsupport (coordPartial i μ g) ⊆ tsupport g := by
  rw [coordPartial_eq_fderiv i μ hg]
  exact tsupport_fderiv_apply_subset ℝ _
theorem contDiff_coordPartial_iterate (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) (k : ℕ) : ContDiff ℝ ∞ ((coordPartial i μ)^[k] g) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_coordPartial i μ ih
theorem tsupport_coordPartial_iterate_subset (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) (k : ℕ) : tsupport ((coordPartial i μ)^[k] g) ⊆ tsupport g := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (tsupport_coordPartial_subset i μ (contDiff_coordPartial_iterate i μ hg k)).trans ih
def phase (ξ y : Config n) : Config n → ℂ := fun x =>
  Complex.exp (-(Complex.I * (configDot ξ (x - y) : ℝ)))
theorem configDot_add_smul_axisVector (ξ a : Config n) (t : ℝ) (i : Fin n) (μ : Fin 4) :
    configDot ξ (a + t • axisVector i μ) = configDot ξ a + t * ξ i μ := by
  simp only [configDot, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i, Finset.sum_eq_single μ]
  · simp
    ring
  · intro c _ hc
    simp [hc]
  · simp
  · intro i' _ hi
    simp [hi]
  · simp
theorem continuous_phase (ξ y : Config n) : Continuous (phase ξ y) := by
  unfold phase configDot dotProduct
  simp only [Pi.sub_apply]
  fun_prop
theorem differentiable_phase (ξ y : Config n) : Differentiable ℝ (phase ξ y) := by
  unfold phase configDot dotProduct
  simp only [Pi.sub_apply]
  fun_prop
theorem norm_phase (ξ y x : Config n) : ‖phase ξ y x‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp
theorem fderiv_phase_axisVector (ξ y x : Config n) (i : Fin n) (μ : Fin 4) :
    fderiv ℝ (phase ξ y) x (axisVector i μ) =
      -(Complex.I * (ξ i μ : ℂ)) * phase ξ y x := by
  rw [← (differentiable_phase ξ y x).lineDeriv_eq_fderiv]
  apply HasLineDerivAt.lineDeriv
  unfold HasLineDerivAt
  have h0 : HasDerivAt (fun t : ℝ => configDot ξ (x - y) + t * ξ i μ) (ξ i μ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ i μ)).const_add (configDot ξ (x - y))
  have h1 : HasDerivAt
      (fun t : ℝ => -(Complex.I * ((configDot ξ (x - y) + t * ξ i μ : ℝ) : ℂ)))
      (-(Complex.I * (ξ i μ : ℂ))) 0 :=
    (h0.ofReal_comp.const_mul Complex.I).neg
  have h2 := h1.cexp
  have hf : (fun t : ℝ => phase ξ y (x + t • axisVector i μ)) =
      fun t : ℝ => Complex.exp (-(Complex.I * ((configDot ξ (x - y) + t * ξ i μ : ℝ) : ℂ))) := by
    funext t
    have hx : x + t • axisVector i μ - y = (x - y) + t • axisVector i μ := by abel
    simp only [phase, hx, configDot_add_smul_axisVector]
  have hE : Complex.exp (-(Complex.I * ((configDot ξ (x - y) + (0 : ℝ) * ξ i μ : ℝ) : ℂ))) =
      phase ξ y x := by
    rw [zero_mul, add_zero]
    rfl
  rw [hf, mul_comm (-(Complex.I * (ξ i μ : ℂ))), ← hE]
  exact h2
theorem integral_coordPartial_mul_phase (i : Fin n) (μ : Fin 4) (ξ y : Config n)
    {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∫ x, coordPartial i μ g x * phase ξ y x =
      Complex.I * (ξ i μ : ℂ) * ∫ x, g x * phase ξ y x := by
  have hcontE := continuous_phase ξ y
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hpf := coordPartial_eq_fderiv i μ hg
  have hcp : Continuous (coordPartial i μ g) := (contDiff_coordPartial i μ hg).continuous
  have hcsp : HasCompactSupport (coordPartial i μ g) :=
    IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_coordPartial_subset i μ hg)
  have h1 : Integrable (fun x => fderiv ℝ g x (axisVector i μ) * phase ξ y x) volume := by
    have : (fun x => fderiv ℝ g x (axisVector i μ) * phase ξ y x) =
        fun x => coordPartial i μ g x * phase ξ y x := by rw [hpf]
    rw [this]
    exact (hcp.mul hcontE).integrable_of_hasCompactSupport hcsp.mul_right
  have h3 : Integrable (fun x => g x * phase ξ y x) volume :=
    (hg.continuous.mul hcontE).integrable_of_hasCompactSupport hc.mul_right
  have h2 : Integrable (fun x => g x * fderiv ℝ (phase ξ y) x (axisVector i μ)) volume := by
    have : (fun x => g x * fderiv ℝ (phase ξ y) x (axisVector i μ)) =
        fun x => -(Complex.I * (ξ i μ : ℂ)) * (g x * phase ξ y x) := by
      funext x
      rw [fderiv_phase_axisVector]
      ring
    rw [this]
    exact h3.const_mul _
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) h1 h2 h3
    (fun x _ => hd x) (fun x _ => differentiable_phase ξ y x)
  have e1 : ∫ x, g x * fderiv ℝ (phase ξ y) x (axisVector i μ) =
      -(Complex.I * (ξ i μ : ℂ)) * ∫ x, g x * phase ξ y x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fderiv_phase_axisVector]
    ring
  have e2 : ∫ x, coordPartial i μ g x * phase ξ y x =
      ∫ x, fderiv ℝ g x (axisVector i μ) * phase ξ y x := by rw [hpf]
  rw [e2]
  rw [e1] at key
  linear_combination key
theorem integral_coordPartial_iterate_mul_phase (i : Fin n) (μ : Fin 4) (ξ y : Config n)
    {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (k : ℕ) :
    ∫ x, (coordPartial i μ)^[k] g x * phase ξ y x =
      (Complex.I * (ξ i μ : ℂ)) ^ k * ∫ x, g x * phase ξ y x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', integral_coordPartial_mul_phase i μ ξ y
      (contDiff_coordPartial_iterate i μ hg k)
      (IsCompact.of_isClosed_subset hc (isClosed_tsupport _)
        (tsupport_coordPartial_iterate_subset i μ hg k)), ih]
    ring
theorem mem_closedBox_iff (z a : Fin 4 → ℝ) (s : ℝ) :
    z ∈ closedBox a s ↔ ∀ c, |z c - a c| ≤ s / 2 := by
  unfold closedBox EuclideanCoords.supCoord
  simp only [Set.mem_ofPred_eq]
  rw [ciSup_le_iff (Set.finite_range _).bddAbove]
  simp
theorem outerBox_cylinder_eq_pi (Q : PointSystem n) :
    cylinderSet Q.outerBox =
      Set.pi univ fun i => Icc (fun c => Q.base i c - Q.scale) (fun c => Q.base i c + Q.scale) := by
  ext x
  simp only [cylinderSet, Set.mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left,
    PointSystem.outerBox, mem_closedBox_iff, mem_Icc, Pi.le_def]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    refine ⟨fun c => ?_, fun c => ?_⟩
    · have := abs_le.1 (h c)
      linarith [this.1]
    · have := abs_le.1 (h c)
      linarith [this.2]
  · rintro ⟨h₁, h₂⟩ c
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [h₁ c]
    · linarith [h₂ c]
theorem isCompact_outerBox_cylinder (Q : PointSystem n) : IsCompact (cylinderSet Q.outerBox) := by
  rw [outerBox_cylinder_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc
theorem volume_outerBox_cylinder (Q : PointSystem n) :
    volume (cylinderSet Q.outerBox) = ENNReal.ofReal ((2 * Q.scale) ^ (4 * n)) := by
  have h2 : (0 : ℝ) ≤ 2 * Q.scale := by linarith [Q.scale_pos]
  rw [outerBox_cylinder_eq_pi, volume_pi_pi]
  simp only [Real.volume_Icc_pi]
  have hc : ∀ (i : Fin n) (c : Fin 4),
      ENNReal.ofReal (Q.base i c + Q.scale - (Q.base i c - Q.scale)) =
        ENNReal.ofReal (2 * Q.scale) := by
    intro i c
    congr 1
    ring
  simp only [hc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ENNReal.ofReal_pow h2, mul_comm]
theorem volumeReal_outerBox_cylinder (Q : PointSystem n) :
    volume.real (cylinderSet Q.outerBox) = (2 * Q.scale) ^ (4 * n) := by
  have h2 : (0 : ℝ) ≤ 2 * Q.scale := by linarith [Q.scale_pos]
  rw [Measure.real, volume_outerBox_cylinder, ENNReal.toReal_ofReal (pow_nonneg h2 _)]
theorem midBox_cylinder_subset (Q : PointSystem n) :
    cylinderSet Q.midBox ⊆ cylinderSet Q.outerBox := by
  intro x hx i
  have hm := Q.scale_pos
  have h := (mem_closedBox_iff _ _ _).1 (hx i)
  refine (mem_closedBox_iff _ _ _).2 fun c => (h c).trans ?_
  linarith
theorem norm_integral_mul_phase_le (Q : PointSystem n) (ξ : Config n) {g : Config n → ℂ}
    (hg : Continuous g) (hs : tsupport g ⊆ cylinderSet Q.outerBox) :
    ‖∫ x, g x * phase ξ Q.base x‖ ≤ uniformNorm g * (2 * Q.scale) ^ (4 * n) := by
  have hc : HasCompactSupport g := IsCompact.of_isClosed_subset (isCompact_outerBox_cylinder Q)
    (isClosed_tsupport _) hs
  have hb : BddAbove (range fun x => ‖g x‖) := by
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hg
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hset : ∫ x in cylinderSet Q.outerBox, g x * phase ξ Q.base x =
      ∫ x, g x * phase ξ Q.base x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    simp [this]
  rw [← hset, ← volumeReal_outerBox_cylinder Q]
  refine norm_setIntegral_le_of_norm_le_const ?_ fun x _ => ?_
  · rw [volume_outerBox_cylinder]
    exact ENNReal.ofReal_lt_top
  · rw [norm_mul, norm_phase, mul_one]
    exact le_ciSup hb x
theorem abs_pow_mul_norm_fourierCoeff_le (Q : PointSystem n) {Φ : Config n → ℂ}
    (hΦ : Φ ∈ Q.supportedClass) (ξ : Config n) (i : Fin n) (μ : Fin 4) (k : ℕ) :
    |ξ i μ| ^ k * ‖Q.fourierCoeff Φ ξ‖ ≤ uniformNorm ((coordPartial i μ)^[k] Φ) := by
  have hs : tsupport Φ ⊆ cylinderSet Q.outerBox := hΦ.2.trans (midBox_cylinder_subset Q)
  have hc : HasCompactSupport Φ := IsCompact.of_isClosed_subset (isCompact_outerBox_cylinder Q)
    (isClosed_tsupport _) hs
  have hV : (0 : ℝ) < (2 * Q.scale) ^ (4 * n) := pow_pos (by linarith [Q.scale_pos]) _
  have hset : ∫ x in cylinderSet Q.outerBox, Φ x * phase ξ Q.base x =
      ∫ x, Φ x * phase ξ Q.base x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : Φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    simp [this]
  have hcoef : Q.fourierCoeff Φ ξ = (((2 * Q.scale) ^ (4 * n))⁻¹ : ℝ) *
      ∫ x, Φ x * phase ξ Q.base x := by
    rw [← hset]
    rfl
  have hbound := norm_integral_mul_phase_le Q ξ (contDiff_coordPartial_iterate i μ hΦ.1 k).continuous
    ((tsupport_coordPartial_iterate_subset i μ hΦ.1 k).trans hs)
  rw [integral_coordPartial_iterate_mul_phase i μ ξ Q.base hΦ.1 hc k, norm_mul, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at hbound
  rw [hcoef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hV.le)]
  calc |ξ i μ| ^ k * (((2 * Q.scale) ^ (4 * n))⁻¹ * ‖∫ x, Φ x * phase ξ Q.base x‖)
      = ((2 * Q.scale) ^ (4 * n))⁻¹ *
          (|ξ i μ| ^ k * ‖∫ x, Φ x * phase ξ Q.base x‖) := by ring
    _ ≤ ((2 * Q.scale) ^ (4 * n))⁻¹ *
          (uniformNorm ((coordPartial i μ)^[k] Φ) * (2 * Q.scale) ^ (4 * n)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hV.le)
    _ = uniformNorm ((coordPartial i μ)^[k] Φ) := by
        field_simp
theorem pow_mul_uniformNorm_le_scaledSupNorm (ν k : ℕ) (hk : k ≤ ν) (m : ℝ) (Φ : Config n → ℂ)
    (i : Fin n) (μ : Fin 4) :
    m ^ k * uniformNorm ((coordPartial i μ)^[k] Φ) ≤ scaledSupNorm ν m Φ := by
  have := finite_order_le (n := n) ν
  have hb : BddAbove (range fun α : {α : MultiIndex n // α.order ≤ ν} =>
      m ^ α.1.order * uniformNorm (iteratedPartial α.1 Φ)) := (Set.finite_range _).bddAbove
  have h := le_ciSup hb ⟨Pi.single i (Pi.single μ k), (order_single i μ k).trans_le hk⟩
  unfold scaledSupNorm
  simpa only [order_single, iteratedPartial_single] using h
end FourierDecay
open FourierDecay YangMills.Construction.TestFunctions in
theorem systemCoeffsDecay_holds : SystemCoeffsDecay := by
  intro n hn Q Φ hΦ ν ξ _
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨆ c, |ξ i c|)
  obtain ⟨μ, hμ⟩ := exists_eq_ciSup_of_finite (f := fun c => |ξ i c|)
  have hmax : coordSupNorm ξ = |ξ i μ| := by
    unfold coordSupNorm
    rw [← hi]
    exact hμ.symm
  rw [hmax]
  have hm := Q.scale_pos
  set a : ℝ := Q.scale * |ξ i μ| with ha
  have ha0 : 0 ≤ a := by positivity
  set N := scaledSupNorm ν Q.scale Φ with hN
  set c := ‖Q.fourierCoeff Φ ξ‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have h₀ : c ≤ N := by
    have h1 := abs_pow_mul_norm_fourierCoeff_le Q hΦ ξ i μ 0
    have h2 := pow_mul_uniformNorm_le_scaledSupNorm ν 0 (Nat.zero_le _) Q.scale Φ i μ
    simp only [pow_zero, one_mul] at h1 h2
    exact h1.trans h2
  have h₁ : a ^ ν * c ≤ N := by
    have h1 := abs_pow_mul_norm_fourierCoeff_le Q hΦ ξ i μ ν
    have h2 := pow_mul_uniformNorm_le_scaledSupNorm ν ν le_rfl Q.scale Φ i μ
    calc a ^ ν * c = Q.scale ^ ν * (|ξ i μ| ^ ν * c) := by rw [ha, mul_pow]; ring
      _ ≤ Q.scale ^ ν * uniformNorm ((coordPartial i μ)^[ν] Φ) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hm.le _)
      _ ≤ N := h2
  have h2ν : (0 : ℝ) ≤ 2 ^ ν := by positivity
  rcases le_total a 1 with hle | hle
  · calc (1 + a) ^ ν * c ≤ 2 ^ ν * c :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) _) hc0
      _ ≤ 2 ^ ν * N := mul_le_mul_of_nonneg_left h₀ h2ν
  · calc (1 + a) ^ ν * c ≤ (2 * a) ^ ν * c :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) _) hc0
      _ = 2 ^ ν * (a ^ ν * c) := by rw [mul_pow]; ring
      _ ≤ 2 ^ ν * N := mul_le_mul_of_nonneg_left h₁ h2ν
end YangMills.Construction.ConfigSpace
