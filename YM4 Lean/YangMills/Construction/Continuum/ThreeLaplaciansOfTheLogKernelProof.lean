import YangMills.Construction.Continuum.ThreeLaplaciansOfTheLogKernel
import YangMills.Construction.TwoPoints.ParametrixOfTheCubedLaplacianProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.Parametrix
open TorusMetric TestFunctions
namespace LogKernelLaplacian
def shiftedSqNorm (ε : ℝ) (x : Fin 4 → ℝ) : ℝ := ∑ μ, x μ ^ 2 + ε
theorem sq_euclidNormVec_add_eq (ε : ℝ) (x : Fin 4 → ℝ) :
    euclidNormVec x ^ 2 + ε = shiftedSqNorm ε x := by
  have h : euclidNormVec x ^ 2 = ∑ μ, x μ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun μ _ => sq_nonneg _)
  rw [h, shiftedSqNorm]
theorem contDiff_shiftedSqNorm (ε : ℝ) : ContDiff ℝ ∞ (shiftedSqNorm ε) := by
  have hr : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => ∑ μ, x μ ^ 2) :=
    ContDiff.sum fun μ _ => (contDiff_apply ℝ ℝ μ).pow 2
  exact hr.add contDiff_const
theorem isOpen_shiftedSqNorm_pos (ε : ℝ) : IsOpen {x | 0 < shiftedSqNorm ε x} :=
  isOpen_lt continuous_const (contDiff_shiftedSqNorm ε).continuous
theorem hasDerivAt_shiftedSqNorm_line (ε : ℝ) (y : Fin 4 → ℝ) (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => shiftedSqNorm ε (y + s • Pi.single μ (1 : ℝ))) (2 * y μ) 0 := by
  have hν : ∀ ν : Fin 4, HasDerivAt
      (fun s : ℝ => (y ν + s * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν) ^ 2)
      (2 * y ν * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν) 0 := by
    intro ν
    have h1 : HasDerivAt (fun s : ℝ => y ν + s * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν)
        ((Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
        ((Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν)).const_add (y ν)
    exact (h1.pow 2).congr_deriv (by simp)
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => hν ν).add_const ε
  have hval : ∑ ν, 2 * y ν * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν = 2 * y μ := by
    simp [Pi.single_apply]
  rw [hval] at hsum
  have hfun : (fun s : ℝ => shiftedSqNorm ε (y + s • Pi.single μ (1 : ℝ))) =
      fun s : ℝ => ∑ ν, (y ν + s * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν) ^ 2 + ε := by
    funext s
    simp [shiftedSqNorm]
  rw [hfun]
  exact hsum
theorem partialDerivR4_eqOn {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) {g h : (Fin 4 → ℝ) → ℝ}
    (hgh : Set.EqOn g h U) (μ : Fin 4) :
    Set.EqOn (partialDerivR4 μ g) (partialDerivR4 μ h) U := by
  intro y hy
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : ContinuousAt (fun s : ℝ => y + s • Pi.single μ (1 : ℝ)) 0 := by fun_prop
  have hn : U ∈ nhds (y + (0 : ℝ) • Pi.single μ (1 : ℝ)) := by
    simpa using hU.mem_nhds hy
  filter_upwards [hc.preimage_mem_nhds hn] with s hs
  exact hgh hs
theorem laplacianR4_eqOn {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) {g h : (Fin 4 → ℝ) → ℝ}
    (hgh : Set.EqOn g h U) : Set.EqOn (laplacianR4 g) (laplacianR4 h) U := by
  intro y hy
  exact Finset.sum_congr rfl fun μ _ =>
    partialDerivR4_eqOn hU (partialDerivR4_eqOn hU hgh μ) μ hy
theorem partialDerivR4_comp_shiftedSqNorm (ε : ℝ) {f F : ℝ → ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (F t) t)
    (μ : Fin 4) {y : Fin 4 → ℝ} (hy : 0 < shiftedSqNorm ε y) :
    partialDerivR4 μ (fun z => f (shiftedSqNorm ε z)) y =
      F (shiftedSqNorm ε y) * (2 * y μ) := by
  have h0 : HasDerivAt f (F (shiftedSqNorm ε y))
      (shiftedSqNorm ε (y + (0 : ℝ) • Pi.single μ (1 : ℝ))) := by
    simpa using hf _ hy
  exact (h0.comp (0 : ℝ) (hasDerivAt_shiftedSqNorm_line ε y μ)).deriv
theorem partialDerivR4_partialDerivR4_comp_shiftedSqNorm (ε : ℝ) {f F G : ℝ → ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (F t) t) (hF : ∀ t, 0 < t → HasDerivAt F (G t) t)
    (μ : Fin 4) {x : Fin 4 → ℝ} (hx : 0 < shiftedSqNorm ε x) :
    partialDerivR4 μ (partialDerivR4 μ fun z => f (shiftedSqNorm ε z)) x =
      2 * F (shiftedSqNorm ε x) + 4 * x μ ^ 2 * G (shiftedSqNorm ε x) := by
  have hEq : Set.EqOn (partialDerivR4 μ fun z => f (shiftedSqNorm ε z))
      (fun y => F (shiftedSqNorm ε y) * (2 * y μ)) {y | 0 < shiftedSqNorm ε y} :=
    fun y hy => partialDerivR4_comp_shiftedSqNorm ε hf μ hy
  rw [partialDerivR4_eqOn (isOpen_shiftedSqNorm_pos ε) hEq μ hx]
  have h0 : HasDerivAt F (G (shiftedSqNorm ε x))
      (shiftedSqNorm ε (x + (0 : ℝ) • Pi.single μ (1 : ℝ))) := by
    simpa using hF _ hx
  have h1 : HasDerivAt (fun s : ℝ => F (shiftedSqNorm ε (x + s • Pi.single μ (1 : ℝ))))
      (G (shiftedSqNorm ε x) * (2 * x μ)) 0 :=
    h0.comp (0 : ℝ) (hasDerivAt_shiftedSqNorm_line ε x μ)
  have h2 : HasDerivAt (fun s : ℝ => 2 * (x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) μ) 2 0 := by
    have h3 : HasDerivAt (fun s : ℝ => 2 * (x μ + s)) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (x μ)).const_mul (2 : ℝ)
    have hfun : (fun s : ℝ => 2 * (x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) μ) =
        fun s : ℝ => 2 * (x μ + s) := by
      funext s
      simp
    rw [hfun]
    exact h3
  have h4 : HasDerivAt (fun s : ℝ => F (shiftedSqNorm ε (x + s • Pi.single μ (1 : ℝ))) *
      (2 * (x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) μ))
      (G (shiftedSqNorm ε x) * (2 * x μ) *
          (2 * (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) μ) +
        F (shiftedSqNorm ε (x + (0 : ℝ) • Pi.single μ (1 : ℝ))) * 2) 0 := h1.mul h2
  simp only [partialDerivR4]
  rw [h4.deriv]
  simp
  ring
theorem laplacianR4_comp_shiftedSqNorm (ε : ℝ) {f F G : ℝ → ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (F t) t) (hF : ∀ t, 0 < t → HasDerivAt F (G t) t)
    {x : Fin 4 → ℝ} (hx : 0 < shiftedSqNorm ε x) :
    laplacianR4 (fun z => f (shiftedSqNorm ε z)) x =
      8 * F (shiftedSqNorm ε x) + 4 * (shiftedSqNorm ε x - ε) * G (shiftedSqNorm ε x) := by
  have hsum : shiftedSqNorm ε x - ε = ∑ μ, x μ ^ 2 := by simp [shiftedSqNorm]
  rw [hsum]
  simp only [laplacianR4]
  rw [Finset.sum_congr rfl fun μ _ =>
    partialDerivR4_partialDerivR4_comp_shiftedSqNorm ε hf hF μ hx]
  simp only [Fin.sum_univ_four]
  ring
theorem hasDerivAt_inv_pow_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s⁻¹ ^ n) (-(n : ℝ) * t⁻¹ ^ (n + 1)) t := by apply _root_.YangMills.Construction.TwoPoints.LaplacianCubeParametrix.hasDerivAt_inv_pow_of_pos <;> assumption
theorem hasDerivAt_mul_self_mul_log (k : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (s * Real.log s)) (k * (Real.log t + 1)) t := by
  have h : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')
  refine (h.const_mul k).congr_deriv ?_
  rw [mul_inv_cancel₀ ht.ne', one_mul]
theorem hasDerivAt_mul_log_add_one (k : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (Real.log s + 1)) (k * t⁻¹) t :=
  ((Real.hasDerivAt_log ht.ne').add_const 1).const_mul k
theorem hasDerivAt_firstProfile (k ε : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (8 * Real.log s + 12 - 4 * ε * s⁻¹ ^ 1))
      (k * (8 * t⁻¹ + 4 * ε * t⁻¹ ^ 2)) t := by
  have h := ((((Real.hasDerivAt_log ht.ne').const_mul 8).add_const 12).sub
    ((hasDerivAt_inv_pow_of_pos 1 ht).const_mul (4 * ε))).const_mul k
  refine h.congr_deriv ?_
  push_cast
  ring
theorem hasDerivAt_firstProfile_deriv (k ε : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (8 * s⁻¹ ^ 1 + 4 * ε * s⁻¹ ^ 2))
      (k * (-8 * t⁻¹ ^ 2 - 8 * ε * t⁻¹ ^ 3)) t := by
  have h := (((hasDerivAt_inv_pow_of_pos 1 ht).const_mul 8).add
    ((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (4 * ε))).const_mul k
  refine h.congr_deriv ?_
  push_cast
  ring
theorem hasDerivAt_secondProfile (k ε : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (32 * s⁻¹ ^ 1 + 32 * ε * s⁻¹ ^ 2 + 32 * ε ^ 2 * s⁻¹ ^ 3))
      (k * (-32 * t⁻¹ ^ 2 - 64 * ε * t⁻¹ ^ 3 - 96 * ε ^ 2 * t⁻¹ ^ 4)) t := by
  have h := ((((hasDerivAt_inv_pow_of_pos 1 ht).const_mul 32).add
    ((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (32 * ε))).add
    ((hasDerivAt_inv_pow_of_pos 3 ht).const_mul (32 * ε ^ 2))).const_mul k
  refine h.congr_deriv ?_
  push_cast
  ring
theorem hasDerivAt_secondProfile_deriv (k ε : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => k * (-32 * s⁻¹ ^ 2 - 64 * ε * s⁻¹ ^ 3 - 96 * ε ^ 2 * s⁻¹ ^ 4))
      (k * (64 * t⁻¹ ^ 3 + 192 * ε * t⁻¹ ^ 4 + 384 * ε ^ 2 * t⁻¹ ^ 5)) t := by
  have h := ((((hasDerivAt_inv_pow_of_pos 2 ht).const_mul (-32)).sub
    ((hasDerivAt_inv_pow_of_pos 3 ht).const_mul (64 * ε))).sub
    ((hasDerivAt_inv_pow_of_pos 4 ht).const_mul (96 * ε ^ 2))).const_mul k
  refine h.congr_deriv ?_
  push_cast
  ring
theorem logKernel_contDiffOn_and_laplacian_iterate (ε : ℝ) :
    ContDiffOn ℝ ∞ (logKernel ε) {x | 0 < euclidNormVec x ^ 2 + ε} ∧
      ∀ x, 0 < euclidNormVec x ^ 2 + ε →
        laplacianR4^[3] (logKernel ε) x =
          12 * ε ^ 3 / Real.pi ^ 2 * (euclidNormVec x ^ 2 + ε) ^ (-5 : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = -(128 * Real.pi ^ 2)⁻¹ := ⟨_, rfl⟩
  have hU := isOpen_shiftedSqNorm_pos ε
  have hset : {x | 0 < euclidNormVec x ^ 2 + ε} = {x | 0 < shiftedSqNorm ε x} := by
    ext x
    simp only [Set.mem_ofPred_eq, sq_euclidNormVec_add_eq]
  have hL : Set.EqOn (logKernel ε)
      (fun z => (fun s => k * (s * Real.log s)) (shiftedSqNorm ε z))
      {x | 0 < shiftedSqNorm ε x} := by
    intro x hx
    have hx' : 0 < euclidNormVec x ^ 2 + ε := by rwa [sq_euclidNormVec_add_eq]
    simp only [logKernel]
    rw [if_pos hx', sq_euclidNormVec_add_eq]
    show _ = k * (shiftedSqNorm ε x * Real.log (shiftedSqNorm ε x))
    rw [hk]
    ring
  constructor
  · rw [hset]
    have hT := (contDiff_shiftedSqNorm ε).contDiffOn (s := {x | 0 < shiftedSqNorm ε x})
    have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (shiftedSqNorm ε x))
        {x | 0 < shiftedSqNorm ε x} :=
      hT.log fun x hx => ne_of_gt hx
    exact (contDiffOn_const.mul (hT.mul hlog)).congr hL
  · intro x hx
    rw [sq_euclidNormVec_add_eq] at hx
    have h1 : Set.EqOn (laplacianR4 (logKernel ε))
        (fun z => (fun s => k * (8 * Real.log s + 12 - 4 * ε * s⁻¹ ^ 1)) (shiftedSqNorm ε z))
        {x | 0 < shiftedSqNorm ε x} := by
      intro y hy
      have hy' : 0 < shiftedSqNorm ε y := hy
      rw [laplacianR4_eqOn hU hL hy,
        laplacianR4_comp_shiftedSqNorm ε (fun t ht => hasDerivAt_mul_self_mul_log k ht)
          (fun t ht => hasDerivAt_mul_log_add_one k ht) hy']
      have : shiftedSqNorm ε y ≠ 0 := hy'.ne'
      field_simp
      ring
    have h2 : Set.EqOn (laplacianR4 (laplacianR4 (logKernel ε)))
        (fun z => (fun s => k * (32 * s⁻¹ ^ 1 + 32 * ε * s⁻¹ ^ 2 + 32 * ε ^ 2 * s⁻¹ ^ 3))
          (shiftedSqNorm ε z)) {x | 0 < shiftedSqNorm ε x} := by
      intro y hy
      have hy' : 0 < shiftedSqNorm ε y := hy
      have hd : ∀ t, 0 < t → HasDerivAt (fun s => k * (8 * s⁻¹ ^ 1 + 4 * ε * s⁻¹ ^ 2))
          (k * (-8 * t⁻¹ ^ 2 - 8 * ε * t⁻¹ ^ 3)) t :=
        fun t ht => hasDerivAt_firstProfile_deriv k ε ht
      have hd0 : ∀ t, 0 < t → HasDerivAt (fun s => k * (8 * Real.log s + 12 - 4 * ε * s⁻¹ ^ 1))
          ((fun s => k * (8 * s⁻¹ ^ 1 + 4 * ε * s⁻¹ ^ 2)) t) t := fun t ht => by
        simpa using hasDerivAt_firstProfile k ε ht
      rw [laplacianR4_eqOn hU h1 hy, laplacianR4_comp_shiftedSqNorm ε hd0 hd hy']
      have : shiftedSqNorm ε y ≠ 0 := hy'.ne'
      field_simp
      ring
    have h3 : Set.EqOn (laplacianR4 (laplacianR4 (laplacianR4 (logKernel ε))))
        (fun z => (fun s => k * (-1536 * ε ^ 3 * s⁻¹ ^ 5)) (shiftedSqNorm ε z))
        {x | 0 < shiftedSqNorm ε x} := by
      intro y hy
      have hy' : 0 < shiftedSqNorm ε y := hy
      rw [laplacianR4_eqOn hU h2 hy,
        laplacianR4_comp_shiftedSqNorm ε (fun t ht => hasDerivAt_secondProfile k ε ht)
          (fun t ht => hasDerivAt_secondProfile_deriv k ε ht) hy']
      have : shiftedSqNorm ε y ≠ 0 := hy'.ne'
      field_simp
      ring
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hx0 : shiftedSqNorm ε x ≠ 0 := hx.ne'
    change laplacianR4 (laplacianR4 (laplacianR4 (logKernel ε))) x = _
    have hz : shiftedSqNorm ε x ^ (-5 : ℤ) = (shiftedSqNorm ε x)⁻¹ ^ 5 := by
      rw [zpow_neg, inv_pow]
      norm_cast
    rw [h3 hx, sq_euclidNormVec_add_eq, hz]
    show k * (-1536 * ε ^ 3 * (shiftedSqNorm ε x)⁻¹ ^ 5) = _
    rw [hk]
    field_simp
    ring
end LogKernelLaplacian
theorem tripleLaplacianLogKernel_holds : TripleLaplacianLogKernel := by
  refine ⟨fun ε _ => LogKernelLaplacian.logKernel_contDiffOn_and_laplacian_iterate ε,
    fun x hx => ?_⟩
  have hpos : 0 < euclidNormVec x ^ 2 + 0 := by
    rw [LogKernelLaplacian.sq_euclidNormVec_add_eq]
    have hne : ∃ μ, x μ ≠ 0 := by
      by_contra h
      exact hx (funext fun μ => by_contra fun hμ => h ⟨μ, hμ⟩)
    obtain ⟨μ, hμ⟩ := hne
    have : 0 < ∑ ν, x ν ^ 2 :=
      Finset.sum_pos' (fun ν _ => sq_nonneg _) ⟨μ, Finset.mem_univ _, by positivity⟩
    simpa [LogKernelLaplacian.shiftedSqNorm] using this
  rw [(LogKernelLaplacian.logKernel_contDiffOn_and_laplacian_iterate 0).2 x hpos]
  simp
end YangMills.Construction.Parametrix
