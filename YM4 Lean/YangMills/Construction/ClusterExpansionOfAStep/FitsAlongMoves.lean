import YangMills.Construction.ClusterExpansionOfAStep.MovesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.TorusPaths
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.LineCalculus YangMills.Construction.QuaternionLogarithm
variable {m k : ℕ} {ι : Type}
def wordAverage (κ : ℝ) (I : Finset ι) (ws : ι → BondWord m) (W : TorusField m) : ℍ[ℝ] :=
  κ • ∑ e ∈ I, ((wordHolonomy W (ws e) : UnitQuaternion) : ℍ[ℝ])
def alignmentDefect (v : UnitQuaternion) (q : ℍ[ℝ]) : ℝ := ‖q‖ - (q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re
def reRightMul (w : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun q : ℍ[ℝ] => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }).comp
    (quaternionRightMul w)
theorem reRightMul_apply (w q : ℍ[ℝ]) : reRightMul w q = (q * w).re := rfl
theorem norm_reRightMul_le (g : UnitQuaternion) : ‖reRightMul (g : ℍ[ℝ])‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [reRightMul_apply, one_mul, Real.norm_eq_abs]
  have habs : |(q * (g : ℍ[ℝ])).re| ≤ ‖q * (g : ℍ[ℝ])‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    have hsq : ‖q * (g : ℍ[ℝ])‖ ^ 2 = Quaternion.normSq (q * (g : ℍ[ℝ])) := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      ring
    rw [hsq, Quaternion.normSq_def']
    nlinarith [sq_nonneg (q * (g : ℍ[ℝ])).imI, sq_nonneg (q * (g : ℍ[ℝ])).imJ, sq_nonneg (q * (g : ℍ[ℝ])).imK]
  rwa [norm_mul, norm_unitQuaternion, mul_one] at habs
def perturbedWordAverage (κ : ℝ) (I : Finset ι) (ws : ι → BondWord m) (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (W : TorusField m) (t : Fin k → ℝ) : ℍ[ℝ] :=
  wordAverage κ I ws (perturb c X t W)
theorem perturbedWordAverage_eq (κ : ℝ) (I : Finset ι) (ws : ι → BondWord m) (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (W : TorusField m) :
    perturbedWordAverage κ I ws c X W = fun t => κ • ∑ e ∈ I, perturbedHolonomy c X W (ws e) t := rfl
theorem contDiff_perturbedWordAverage (κ : ℝ) (I : Finset ι) (ws : ι → BondWord m) (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (W : TorusField m) :
    ContDiff ℝ ⊤ (perturbedWordAverage κ I ws c X W) := by
  rw [perturbedWordAverage_eq]
  exact (ContDiff.sum fun e _ => contDiff_perturbedHolonomy c X W (ws e)).const_smul κ
theorem norm_iteratedFDeriv_perturbedWordAverage_le {κ : ℝ} (hκ : 0 ≤ κ) (I : Finset ι) (ws : ι → BondWord m)
    (hI : κ * I.card ≤ 1) {N : ℕ} (hN : ∀ e ∈ I, (ws e).length ≤ N) (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (hk : k ≤ 3) (W : TorusField m)
    {j : ℕ} (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (perturbedWordAverage κ I ws c X W) 0‖ ≤ (8 * letterDerivBound) ^ N := by
  have hA := one_le_letterDerivBound
  have hS : ContDiffAt ℝ j (fun t => ∑ e ∈ I, perturbedHolonomy c X W (ws e) t) 0 :=
    ((ContDiff.sum fun e _ => contDiff_perturbedHolonomy c X W (ws e)).of_le le_top).contDiffAt
  rw [perturbedWordAverage_eq, iteratedFDeriv_const_smul_apply' hS, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hκ, iteratedFDeriv_fun_sum_apply fun e _ =>
      ((contDiff_perturbedHolonomy c X W (ws e)).of_le le_top).contDiffAt]
  have hEach : ∀ e ∈ I, ‖iteratedFDeriv ℝ j (perturbedHolonomy c X W (ws e)) 0‖ ≤
      (8 * letterDerivBound) ^ N := by
    intro e he
    refine (norm_iteratedFDeriv_perturbedHolonomy_le c X hX hk W (ws e) hj).trans ?_
    exact pow_le_pow_right₀ (by linarith) (hN e he)
  have hSum : ‖∑ e ∈ I, iteratedFDeriv ℝ j (perturbedHolonomy c X W (ws e)) 0‖ ≤
      I.card * (8 * letterDerivBound) ^ N := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hEach).trans ?_
    rw [nsmul_eq_mul]
  have hPow : (0 : ℝ) ≤ (8 * letterDerivBound) ^ N := by positivity
  calc κ * ‖∑ e ∈ I, iteratedFDeriv ℝ j (perturbedHolonomy c X W (ws e)) 0‖
      ≤ κ * (I.card * (8 * letterDerivBound) ^ N) := mul_le_mul_of_nonneg_left hSum hκ
    _ = (κ * I.card) * (8 * letterDerivBound) ^ N := by ring
    _ ≤ 1 * (8 * letterDerivBound) ^ N := mul_le_mul_of_nonneg_right hI hPow
    _ = _ := one_mul _
theorem norm_wordAverage_le {κ : ℝ} (hκ : 0 ≤ κ) (I : Finset ι) (ws : ι → BondWord m) (hI : κ * I.card ≤ 1)
    (W : TorusField m) : ‖wordAverage κ I ws W‖ ≤ 1 := by
  unfold wordAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
  have hSum : ‖∑ e ∈ I, ((wordHolonomy W (ws e) : UnitQuaternion) : ℍ[ℝ])‖ ≤ I.card := by
    refine (norm_sum_le _ _).trans ?_
    simp [norm_unitQuaternion]
  calc _ ≤ κ * I.card := mul_le_mul_of_nonneg_left hSum hκ
    _ ≤ 1 := hI
theorem exists_bound_iteratedFDeriv_norm_annulus : ∃ K : ℝ, 1 ≤ K ∧ ∀ p : ℍ[ℝ], 1 / 2 ≤ ‖p‖ → ‖p‖ ≤ 2 →
    ‖iteratedFDeriv ℝ 1 (norm : ℍ[ℝ] → ℝ) p‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 (norm : ℍ[ℝ] → ℝ) p‖ ≤ K := by
  set U : Set ℍ[ℝ] := {p | p ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  have hc : ContDiffOn ℝ 2 (norm : ℍ[ℝ] → ℝ) U := fun p hp =>
    (contDiffAt_norm ℝ hp).contDiffWithinAt
  set A : Set ℍ[ℝ] := Metric.closedBall 0 2 ∩ {p | 1 / 2 ≤ ‖p‖} with hA
  have hAc : IsCompact A :=
    (isCompact_closedBall (0 : ℍ[ℝ]) 2).inter_right (isClosed_le continuous_const continuous_norm)
  have hsub : A ⊆ U := by
    intro p hp hz
    have hlow := hp.2
    simp only [Set.mem_setOf_eq] at hlow
    rw [hz, norm_zero] at hlow
    norm_num at hlow
  have hcont : ∀ j : ℕ, j ≤ 2 → ContinuousOn (iteratedFDeriv ℝ j (norm : ℍ[ℝ] → ℝ)) A := by
    intro j hj
    have hw := hc.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hUo.uniqueDiffOn
    have hon : ContinuousOn (iteratedFDeriv ℝ j (norm : ℍ[ℝ] → ℝ)) U :=
      hw.congr fun p hp => (iteratedFDerivWithin_of_isOpen j hUo hp).symm
    exact hon.mono hsub
  obtain ⟨K1, hK1⟩ := hAc.exists_bound_of_continuousOn (hcont 1 (by norm_num))
  obtain ⟨K2, hK2⟩ := hAc.exists_bound_of_continuousOn (hcont 2 le_rfl)
  refine ⟨1 + |K1| + |K2|, by linarith [abs_nonneg K1, abs_nonneg K2], fun p hlow hup => ?_⟩
  have hp : p ∈ A := ⟨by simpa using hup, hlow⟩
  exact ⟨(hK1 p hp).trans (by linarith [le_abs_self K1, abs_nonneg K2]),
    (hK2 p hp).trans (by linarith [le_abs_self K2, abs_nonneg K1])⟩
section Defect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem contDiffAt_alignmentDefect (v : UnitQuaternion) {p : ℍ[ℝ]} (hp : p ≠ 0) :
    ContDiffAt ℝ 3 (alignmentDefect v) p :=
  (contDiffAt_norm ℝ hp).sub (reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).contDiff.contDiffAt
theorem norm_fderiv_alignmentDefect_comp_le {K B : ℝ}
    (hK : ∀ p : ℍ[ℝ], 1 / 2 ≤ ‖p‖ → ‖p‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (norm : ℍ[ℝ] → ℝ) p‖ ≤ K)
    (v : UnitQuaternion) {q : E → ℍ[ℝ]} {x : E} (hq : ContDiffAt ℝ 2 q x) (hlow : 1 / 2 ≤ ‖q x‖)
    (hup : ‖q x‖ ≤ 2) (hB : ‖iteratedFDeriv ℝ 1 q x‖ ≤ B) (e : E) :
    ‖fderiv ℝ (alignmentDefect v ∘ q) x e‖ ≤ (K + 1) * B * ‖e‖ := by
  have hne : q x ≠ 0 := fun h => by
    rw [h, norm_zero] at hlow
    norm_num at hlow
  have hf : ContDiffAt ℝ 2 (alignmentDefect v) (q x) := (contDiffAt_alignmentDefect v hne).of_le (by norm_num)
  rw [fderiv_of_eventuallyEq_comp (Filter.EventuallyEq.refl _ _) (hf.differentiableAt (by norm_num))
    (hq.differentiableAt (by norm_num))]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK (q x) hlow hup)
  have hqe : ‖fderiv ℝ q x e‖ ≤ B * ‖e‖ := by
    rw [norm_iteratedFDeriv_one] at hB
    exact ((fderiv ℝ q x).le_opNorm e).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hd : fderiv ℝ (alignmentDefect v) (q x) =
      fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x) - reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have hdiff : DifferentiableAt ℝ (norm : ℍ[ℝ] → ℝ) (q x) :=
      (contDiffAt_norm ℝ hne : ContDiffAt ℝ 1 (norm : ℍ[ℝ] → ℝ) (q x)).differentiableAt (by norm_num)
    exact (hdiff.hasFDerivAt.sub (reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).hasFDerivAt).fderiv
  have hn : ‖fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x)‖ ≤ K := by
    rw [← norm_iteratedFDeriv_one]
    exact hK _ hlow hup
  simp only [ContinuousLinearMap.comp_apply]
  rw [hd]
  have hmain : ‖(fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x) - reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (fderiv ℝ q x e)‖ ≤ (K + 1) * ‖fderiv ℝ q x e‖ := by
    rw [ContinuousLinearMap.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    have b1 := (fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x)).le_opNorm (fderiv ℝ q x e)
    have b2 := (reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).le_opNorm (fderiv ℝ q x e)
    have b3 := mul_le_mul_of_nonneg_right hn (norm_nonneg (fderiv ℝ q x e))
    have b4 := mul_le_mul_of_nonneg_right (norm_reRightMul_le (v⁻¹)) (norm_nonneg (fderiv ℝ q x e))
    linarith
  calc _ ≤ (K + 1) * ‖fderiv ℝ q x e‖ := hmain
    _ ≤ (K + 1) * (B * ‖e‖) := mul_le_mul_of_nonneg_left hqe (by linarith)
    _ = _ := by ring
theorem norm_second_fderiv_alignmentDefect_comp_le {K B : ℝ} (hK : ∀ p : ℍ[ℝ], 1 / 2 ≤ ‖p‖ → ‖p‖ ≤ 2 →
      ‖iteratedFDeriv ℝ 1 (norm : ℍ[ℝ] → ℝ) p‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 (norm : ℍ[ℝ] → ℝ) p‖ ≤ K)
    (v : UnitQuaternion) {q : E → ℍ[ℝ]} {x : E} (hq : ContDiffAt ℝ 2 q x) (hlow : 1 / 2 ≤ ‖q x‖)
    (hup : ‖q x‖ ≤ 2) (hB : ‖iteratedFDeriv ℝ 1 q x‖ ≤ B) (hB2 : ‖iteratedFDeriv ℝ 2 q x‖ ≤ B) (e e' : E) :
    ‖fderiv ℝ (fderiv ℝ (alignmentDefect v ∘ q)) x e e'‖ ≤ (K * B ^ 2 + (K + 1) * B) * ‖e‖ * ‖e'‖ := by
  have hne : q x ≠ 0 := fun h => by
    rw [h, norm_zero] at hlow
    norm_num at hlow
  have hf : ContDiffAt ℝ 2 (alignmentDefect v) (q x) := (contDiffAt_alignmentDefect v hne).of_le (by norm_num)
  rw [second_fderiv_of_eventuallyEq_comp (Filter.EventuallyEq.refl _ _) hf hq e e']
  obtain ⟨hK1, hK2⟩ := hK (q x) hlow hup
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hqe : ∀ u, ‖fderiv ℝ q x u‖ ≤ B * ‖u‖ := fun u => by
    have hB' := hB
    rw [norm_iteratedFDeriv_one] at hB'
    exact ((fderiv ℝ q x).le_opNorm u).trans (mul_le_mul_of_nonneg_right hB' (norm_nonneg _))
  have hnorm : ContDiffAt ℝ 2 (norm : ℍ[ℝ] → ℝ) (q x) := contDiffAt_norm ℝ hne
  have hd1 : fderiv ℝ (alignmentDefect v) =ᶠ[𝓝 (q x)]
      fun p => fderiv ℝ (norm : ℍ[ℝ] → ℝ) p - reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hnorm] with p hp
    exact (hp.hasFDerivAt.sub (reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).hasFDerivAt).fderiv
  have hd2 : fderiv ℝ (fderiv ℝ (alignmentDefect v)) (q x) =
      fderiv ℝ (fderiv ℝ (norm : ℍ[ℝ] → ℝ)) (q x) := by
    rw [hd1.fderiv_eq]
    exact ((hasFDerivAt_fderiv_of_contDiffAt_two hnorm).sub_const _).fderiv
  have hd0 : fderiv ℝ (alignmentDefect v) (q x) =
      fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x) - reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := hd1.self_of_nhds
  rw [hd2, hd0]
  have t1 : ‖fderiv ℝ (fderiv ℝ (norm : ℍ[ℝ] → ℝ)) (q x) (fderiv ℝ q x e) (fderiv ℝ q x e')‖ ≤
      K * (B * ‖e‖) * (B * ‖e'‖) := by
    refine (norm_second_fderiv_apply_le _ _ _ _).trans ?_
    gcongr
    · exact hqe e
    · exact hqe e'
  have t2 : ‖(fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x) - reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (fderiv ℝ (fderiv ℝ q) x e e')‖ ≤ (K + 1) * (B * ‖e‖ * ‖e'‖) := by
    have hn : ‖fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x)‖ ≤ K := by
      rw [← norm_iteratedFDeriv_one]
      exact hK1
    have a2 : ‖fderiv ℝ (fderiv ℝ q) x e e'‖ ≤ B * ‖e‖ * ‖e'‖ := by
      refine (norm_second_fderiv_apply_le _ _ _ _).trans ?_
      gcongr
    rw [ContinuousLinearMap.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    set z := fderiv ℝ (fderiv ℝ q) x e e'
    have b1 := (fderiv ℝ (norm : ℍ[ℝ] → ℝ) (q x)).le_opNorm z
    have b2 := (reRightMul ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).le_opNorm z
    have b3 := mul_le_mul_of_nonneg_right hn (norm_nonneg z)
    have b4 := mul_le_mul_of_nonneg_right (norm_reRightMul_le (v⁻¹)) (norm_nonneg z)
    have b5 : (K + 1) * ‖z‖ ≤ (K + 1) * (B * ‖e‖ * ‖e'‖) := mul_le_mul_of_nonneg_left a2 (by linarith)
    linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ K * (B * ‖e‖) * (B * ‖e'‖) + (K + 1) * (B * ‖e‖ * ‖e'‖) := add_le_add t1 t2
    _ = _ := by ring
end Defect
end YangMills.Construction.TorusPaths
end
