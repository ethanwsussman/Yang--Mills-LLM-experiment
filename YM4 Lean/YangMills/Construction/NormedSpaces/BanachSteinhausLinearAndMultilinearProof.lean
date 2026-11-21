import YangMills.Construction.NormedSpaces.BanachSteinhausLinearAndMultilinear
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces.BanachSteinhaus
theorem norm_apply_le_linearOpNorm_mul {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F)
    (hT : BddAbove (normsOnClosedUnitBall T)) (x : E) : ‖T x‖ ≤ linearOpNorm T * ‖x‖ := by
  have hball : ∀ u : E, ‖u‖ ≤ 1 → ‖T u‖ ≤ linearOpNorm T := fun u hu =>
    le_csSup hT ⟨u, hu, rfl⟩
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have hle := hball _ hu
    rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos, mul_comm] at hle
    exact hle
theorem abs_apply_le_multilinearFormNorm_mul_prod {q : ℕ} {E : Fin q → Type}
    [∀ l, NormedAddCommGroup (E l)] [∀ l, NormedSpace ℝ (E l)] (Ψ : MultilinearMap ℝ E ℝ)
    (hΨ : BddAbove (formValuesOnUnitPolyball Ψ)) (v : ∀ l, E l) :
    |Ψ v| ≤ multilinearFormNorm Ψ * ∏ l, ‖v l‖ := by
  have hball : ∀ u : ∀ l, E l, (∀ l, ‖u l‖ ≤ 1) → |Ψ u| ≤ multilinearFormNorm Ψ := fun u hu =>
    le_csSup hΨ ⟨u, hu, rfl⟩
  by_cases hz : ∃ l, v l = 0
  · obtain ⟨l, hl⟩ := hz
    have hb : 0 ≤ multilinearFormNorm Ψ := (abs_nonneg _).trans (hball 0 fun l => by simp)
    rw [Ψ.map_coord_zero l hl, abs_zero]
    exact mul_nonneg hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · have hpos : ∀ l, 0 < ‖v l‖ := fun l => norm_pos_iff.mpr fun hl => hz ⟨l, hl⟩
    have hprod : 0 < ∏ l, ‖v l‖ := Finset.prod_pos fun l _ => hpos l
    have hu : ∀ l, ‖(‖v l‖⁻¹ : ℝ) • v l‖ ≤ 1 := fun l => by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos l).ne']
    have hle := hball (fun l => (‖v l‖⁻¹ : ℝ) • v l) hu
    rw [Ψ.map_smul_univ, smul_eq_mul, abs_mul, Finset.prod_inv_distrib,
      abs_of_pos (inv_pos.mpr hprod), inv_mul_le_iff₀ hprod, mul_comm] at hle
    exact hle
theorem exists_opNorm_bound_of_pointwise_bound (n : ℕ) :
    ∀ (E : Fin n → Type) [∀ l, NormedAddCommGroup (E l)] [∀ l, NormedSpace ℝ (E l)]
      [∀ l, CompleteSpace (E l)] (ι : Type) (g : ι → ContinuousMultilinearMap ℝ E ℝ),
      (∀ v : ∀ l, E l, ∃ C, ∀ j, ‖g j v‖ ≤ C) → ∃ C, ∀ j, ‖g j‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ _ ι g hg
    obtain ⟨C, hC⟩ := hg (fun l => l.elim0)
    refine ⟨max C 0, fun j =>
      ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => ?_⟩
    have hm : m = fun l => l.elim0 := Subsingleton.elim _ _
    rw [hm]
    simpa using (hC j).trans (le_max_left C 0)
  | succ n ih =>
    intro E _ _ _ ι g hg
    have hcurry : ∀ x : E 0, ∃ C, ∀ j, ‖(g j).curryLeft x‖ ≤ C := fun x =>
      ih (fun i => E i.succ) ι (fun j => (g j).curryLeft x) fun m => by
        obtain ⟨C, hC⟩ := hg (Fin.cons x m)
        exact ⟨C, fun j => by rw [ContinuousMultilinearMap.curryLeft_apply]; exact hC j⟩
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun j => (g j).curryLeft) hcurry
    refine ⟨max C 0, fun j =>
      ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => ?_⟩
    have hsplit : g j m = (g j).curryLeft (m 0) (Fin.tail m) := by
      rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
    have hprod : 0 ≤ ∏ i, ‖Fin.tail m i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc ‖g j m‖ = ‖(g j).curryLeft (m 0) (Fin.tail m)‖ := by rw [hsplit]
      _ ≤ ‖(g j).curryLeft (m 0)‖ * ∏ i, ‖Fin.tail m i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (‖(g j).curryLeft‖ * ‖m 0‖) * ∏ i, ‖Fin.tail m i‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) hprod
      _ ≤ (max C 0 * ‖m 0‖) * ∏ i, ‖Fin.tail m i‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((hC j).trans (le_max_left _ _)) (norm_nonneg _)) hprod
      _ = max C 0 * ∏ i, ‖m i‖ := by
        rw [Fin.prod_univ_succ, mul_assoc]
        rfl
theorem linearAndMultilinear_holds : linearAndMultilinear := by
  refine ⟨?_, ?_⟩
  · intro ι E F _ _ _ _ _ _ T hT hpt
    let g : ι → E →L[ℝ] F := fun j =>
      (T j).mkContinuous (linearOpNorm (T j)) (norm_apply_le_linearOpNorm_mul (T j) (hT j))
    obtain ⟨C, hC⟩ := banach_steinhaus (g := g) fun x => by
      obtain ⟨C, hC⟩ := hpt x
      exact ⟨C, fun j => hC ⟨j, rfl⟩⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨j, rfl⟩
    refine csSup_le ⟨‖T j 0‖, 0, by simp, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    calc ‖T j x‖ = ‖g j x‖ := rfl
      _ ≤ ‖g j‖ * ‖x‖ := (g j).le_opNorm x
      _ ≤ ‖g j‖ := mul_le_of_le_one_right (norm_nonneg _) hx
      _ ≤ C := hC j
  · intro ι _ q _ E _ _ _ Ψ hΨ hpt
    let g : ι → ContinuousMultilinearMap ℝ E ℝ := fun j =>
      (Ψ j).mkContinuous (multilinearFormNorm (Ψ j)) fun v => by
        rw [Real.norm_eq_abs]
        exact abs_apply_le_multilinearFormNorm_mul_prod (Ψ j) (hΨ j) v
    obtain ⟨C, hC⟩ := exists_opNorm_bound_of_pointwise_bound q E ι g fun v => by
      obtain ⟨C, hC⟩ := hpt v
      exact ⟨C, fun j => hC ⟨j, rfl⟩⟩
    have hbdd : BddAbove (Set.range fun j => multilinearFormNorm (Ψ j)) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨j, rfl⟩
      refine csSup_le ⟨|Ψ j 0|, 0, fun l => by simp, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      calc |Ψ j v| = ‖g j v‖ := rfl
        _ ≤ ‖g j‖ * ∏ l, ‖v l‖ := (g j).le_opNorm v
        _ ≤ ‖g j‖ := mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => hv l)
        _ ≤ C := hC j
    exact ⟨hbdd, fun j v => (abs_apply_le_multilinearFormNorm_mul_prod (Ψ j) (hΨ j) v).trans
      (mul_le_mul_of_nonneg_right (le_ciSup hbdd j)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))⟩
end YangMills.Construction.NormedSpaces.BanachSteinhaus
