import YangMills.Construction.ConfigurationSpace.TupleEuclideanBallVolume
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
open scoped Pointwise
private def coordListing {J : Type} {D : ℕ} (e : J × Fin 4 ≃ Fin D) (y : J → Fin 4 → ℝ) :
    Fin D → ℝ :=
  fun i => y (e.symm i).1 (e.symm i).2
private theorem measurable_coordListing {J : Type} {D : ℕ} (e : J × Fin 4 ≃ Fin D) :
    Measurable (coordListing e) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)
private theorem map_coordListing {J : Type} [Fintype J] {D : ℕ} (e : J × Fin 4 ≃ Fin D) :
    Measure.map (coordListing e) (volume : Measure (J → Fin 4 → ℝ)) = volume := by
  classical
  symm
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_coordListing e) (MeasurableSet.univ_pi hs)]
  have hpre : coordListing e ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun c => s (e (a, c)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, coordListing]
    constructor
    · intro h a c
      simpa using h (e (a, c))
    · intro h i
      have := h (e.symm i).1 (e.symm i).2
      simpa using this
  rw [hpre, volume_pi, Measure.pi_pi]
  have hin : ∀ a : J, (volume : Measure (Fin 4 → ℝ)) (Set.pi Set.univ fun c => s (e (a, c))) =
      ∏ c, volume (s (e (a, c))) := by
    intro a
    rw [volume_pi, Measure.pi_pi]
  simp only [hin]
  rw [← Fintype.prod_prod_type' (fun a c => volume (s (e (a, c))))]
  exact Equiv.prod_comp e fun i => volume (s i)
private theorem l2Norm_closedBall_eq_smul {D : ℕ} {R : ℝ} (hR : 0 < R) :
    {x : Fin D → ℝ | l2Norm x ≤ R} = R • {x : Fin D → ℝ | l2Norm x ≤ 1} := by
  have hscale : ∀ (c : ℝ) (x : Fin D → ℝ), 0 < c → l2Norm (c • x) = c * l2Norm x := by
    intro c x hc
    unfold l2Norm
    have : ∑ ι, (c • x) ι ^ 2 = c ^ 2 * ∑ ι, x ι ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ι _ => by simp [mul_pow]
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [Set.mem_ofPred_eq]
  rw [hscale _ _ (inv_pos.2 hR), inv_mul_le_iff₀ hR, mul_one]
private theorem volume_l2Norm_unitBall_lt_top (D : ℕ) :
    (volume : Measure (Fin D → ℝ)) {x | l2Norm x ≤ 1} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (measure_closedBall_lt_top (x := (0 : Fin D → ℝ)) (r := 1))
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hsum : x i ^ 2 ≤ ∑ ι, x ι ^ 2 :=
    Finset.single_le_sum (f := fun ι => x ι ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hx' : Real.sqrt (∑ ι, x ι ^ 2) ≤ 1 := hx
  have h1 : ∑ ι, x ι ^ 2 ≤ 1 := by
    have := (Real.sqrt_le_left zero_le_one).1 hx'
    simpa using this
  rw [Real.norm_eq_abs]
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
theorem tupleEuclideanBallVolume_holds : TupleEuclideanBallVolume := by
  intro J _ hJ R hR
  classical
  obtain ⟨D, hD⟩ : ∃ D, 4 * Fintype.card J = D + 1 := ⟨4 * Fintype.card J - 1, by omega⟩
  have hcard : Fintype.card (J × Fin 4) = D + 1 := by
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm, hD]
  let e : J × Fin 4 ≃ Fin (D + 1) := Fintype.equivFinOfCardEq hcard
  have hset : {y : J → Fin 4 → ℝ | Real.sqrt (∑ a, ∑ c, y a c ^ 2) ≤ R} =
      coordListing e ⁻¹' {x | l2Norm x ≤ R} := by
    ext y
    have hsum : ∑ ι, coordListing e y ι ^ 2 = ∑ a, ∑ c, y a c ^ 2 := by
      rw [← Fintype.sum_prod_type' (fun a c => y a c ^ 2)]
      exact Equiv.sum_comp e.symm fun p => y p.1 p.2 ^ 2
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, l2Norm, hsum]
  have hclosed : MeasurableSet {x : Fin (D + 1) → ℝ | l2Norm x ≤ R} := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    unfold l2Norm
    fun_prop
  rw [hset, hD, ← Measure.map_apply (measurable_coordListing e) hclosed, map_coordListing,
    l2Norm_closedBall_eq_smul hR, Measure.addHaar_smul, Module.finrank_fin_fun]
  have hv : 0 ≤ unitBallVol (D + 1) := ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_mul hv, abs_of_pos (pow_pos hR _), mul_comm]
  congr 1
  show _ = ENNReal.ofReal ((volume {x : Fin (D + 1) → ℝ | l2Norm x ≤ 1}).toReal)
  rw [ENNReal.ofReal_toReal (volume_l2Norm_unitBall_lt_top _).ne]
end YangMills.Construction.ConfigurationSpace
end
