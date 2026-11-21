import YangMills.Construction.ResponseInTheExpansion.SumsOverCellsAreIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LatticeCells
variable {N p : ℕ} [NeZero N]
private theorem measurableSet_unitCell (z : Fin p → Fin 4 → ZMod N) : MeasurableSet (unitCell z) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
private theorem volume_unitCell (z : Fin p → Fin 4 → ZMod N) : volume (unitCell z) = 1 := by
  simp only [unitCell]
  rw [volume_pi_pi]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [volume_pi_pi]
  refine Finset.prod_eq_one fun μ _ => ?_
  simp [Real.volume_Ico]
private theorem disjoint_unitCell (z z' : Fin p → Fin 4 → ZMod N) (hne : z ≠ z') :
    Disjoint (unitCell z) (unitCell z') := by
  rw [Set.disjoint_left]
  intro u hu hu'
  apply hne
  funext i μ
  have h1 := (hu i (Set.mem_univ _)) μ (Set.mem_univ _)
  have h2 := (hu' i (Set.mem_univ _)) μ (Set.mem_univ _)
  have h3 : ((z i μ).val : ℝ) < (z' i μ).val + 1 := lt_of_le_of_lt h1.1 h2.2
  have h4 : ((z' i μ).val : ℝ) < (z i μ).val + 1 := lt_of_le_of_lt h2.1 h1.2
  have h5 : (z i μ).val < (z' i μ).val + 1 := by exact_mod_cast h3
  have h6 : (z' i μ).val < (z i μ).val + 1 := by exact_mod_cast h4
  exact ZMod.val_injective N (by omega)
private theorem exists_unitCell_mem (u : Fin p → Fin 4 → ℝ)
    (hu : u ∈ Set.pi Set.univ (fun _ : Fin p => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) N)) :
    ∃ z : Fin p → Fin 4 → ZMod N, u ∈ unitCell z := by
  refine ⟨fun i μ => ((⌊u i μ⌋₊ : ℕ) : ZMod N), fun i _ μ _ => ?_⟩
  have h1 := (hu i (Set.mem_univ _)) μ (Set.mem_univ _)
  have h2 : ⌊u i μ⌋₊ < N := (Nat.floor_lt h1.1).mpr h1.2
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h2]
  exact ⟨Nat.floor_le h1.1, Nat.lt_floor_add_one _⟩
private theorem unitCell_subset_box (z : Fin p → Fin 4 → ZMod N) :
    unitCell z ⊆ Set.pi Set.univ (fun _ : Fin p => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) N) := by
  intro u hu i _ μ _
  have h1 := (hu i (Set.mem_univ _)) μ (Set.mem_univ _)
  have h2 : (z i μ).val < N := ZMod.val_lt _
  have h3 : ((z i μ).val : ℝ) + 1 ≤ N := by exact_mod_cast h2
  exact ⟨le_trans (Nat.cast_nonneg _) h1.1, lt_of_lt_of_le h1.2 h3⟩
theorem integralNearCellSum_holds : IntegralNearCellSum := by
  intro N p _ F Gz D ε hF hε hnear hzero
  set box : Set (Fin p → Fin 4 → ℝ) := Set.pi Set.univ (fun _ : Fin p => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) N)
    with hbox
  have hboxm : MeasurableSet box := MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hint : ∀ z ∈ D, IntegrableOn F (unitCell z) volume := by
    intro z hz
    refine Measure.integrableOn_of_bounded (M := |Gz z| + ε) (by rw [volume_unitCell]; simp)
      hF.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (measurableSet_unitCell z)).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have := hnear z hz u hu
    have h2 : |F u| ≤ |F u - Gz z| + |Gz z| := by
      have := abs_add_le (F u - Gz z) (Gz z)
      simpa using this
    rw [Real.norm_eq_abs]
    linarith
  have hunion : ∫ u in box, F u = ∫ u in ⋃ z ∈ D, unitCell z, F u := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hboxm ?_ ?_
    · exact Set.iUnion₂_subset fun z _ => unitCell_subset_box z
    · intro u hu
      obtain ⟨z, hz⟩ := exists_unitCell_mem u hu.1
      by_cases hD : z ∈ D
      · exact absurd (Set.mem_iUnion₂.mpr ⟨z, hD, hz⟩) hu.2
      · exact hzero z hD u hz
  rw [hunion, integral_biUnion_finset D (fun z _ => measurableSet_unitCell z)
    (fun z _ z' _ h => disjoint_unitCell z z' h) hint, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hcell : ∀ z ∈ D, |(∫ u in unitCell z, F u) - Gz z| ≤ ε := by
    intro z hz
    have hvol : volume.real (unitCell z) = 1 := by simp [Measure.real, volume_unitCell]
    have hconst : ∫ _u in unitCell z, Gz z = Gz z := by
      rw [setIntegral_const, hvol]
      simp
    have hi2 : IntegrableOn (fun _ => Gz z) (unitCell z) volume := by
      refine integrableOn_const ?_
      rw [volume_unitCell]
      simp
    calc |(∫ u in unitCell z, F u) - Gz z| = ‖∫ u in unitCell z, (F u - Gz z)‖ := by
          rw [integral_sub (hint z hz) hi2, hconst, Real.norm_eq_abs]
      _ ≤ ε * volume.real (unitCell z) := by
          refine norm_setIntegral_le_of_norm_le_const ?_ ?_
          · rw [volume_unitCell]
            simp
          · intro u hu
            exact hnear z hz u hu
      _ = ε := by rw [hvol, mul_one]
  calc _ ≤ ∑ _z ∈ D, ε := Finset.sum_le_sum hcell
    _ = ε * D.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
end YangMills.Construction.LatticeCells
end
