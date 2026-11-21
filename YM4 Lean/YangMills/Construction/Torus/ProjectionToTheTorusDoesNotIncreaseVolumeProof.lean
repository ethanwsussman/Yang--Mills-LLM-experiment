import YangMills.Construction.Torus.ProjectionToTheTorusDoesNotIncreaseVolume
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMeasure TestFunctions
namespace TorusProjection
theorem existsUnique_translate_mem_fundamentalCube {ℓ : ℝ} (hpos : 0 < ℓ) (x : Fin 4 → ℝ) :
    ∃! k : Fin 4 → ℤ, x - latticeTranslate ℓ k ∈ Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ := by
  have hcoord : ∀ μ, ∃! j : ℤ, x μ - j • ℓ ∈ Ico (0 : ℝ) (0 + ℓ) :=
    fun μ => existsUnique_sub_zsmul_mem_Ico hpos (x μ) 0
  have hiff : ∀ (k : Fin 4 → ℤ), x - latticeTranslate ℓ k ∈ (Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ) ↔
      ∀ μ, x μ - k μ • ℓ ∈ Ico (0 : ℝ) (0 + ℓ) := by
    intro k
    simp only [Set.mem_pi, mem_univ, forall_true_left, zero_add, Pi.sub_apply, latticeTranslate,
      zsmul_eq_mul, mul_comm]
  choose k hk using fun μ => (hcoord μ).exists
  refine ⟨k, (hiff k).2 hk, fun k' hk' => ?_⟩
  funext μ
  exact (hcoord μ).unique ((hiff k').1 hk' μ) (hk μ)
theorem tsum_volume_translatedPieces {ι : Type*} [Countable ι] {C A : Set (Fin 4 → ℝ)}
    (hC : MeasurableSet C) (hA : NullMeasurableSet A volume) (v : ι → Fin 4 → ℝ)
    (hv : ∀ x, ∃! k, x - v k ∈ C) :
    ∑' k, volume (C ∩ (fun x => x + v k) ⁻¹' A) = volume A := by
  have hshift : ∀ k, volume (C ∩ (fun x => x + v k) ⁻¹' A) =
      volume ((fun x => x - v k) ⁻¹' C ∩ A) := by
    intro k
    rw [← measure_preimage_add_right volume (v k) ((fun x => x - v k) ⁻¹' C ∩ A)]
    congr 1
    ext x
    simp
  simp_rw [hshift]
  rw [← measure_iUnion₀]
  · congr 1
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right, and_iff_right_iff_imp]
    exact fun _ => (hv x).exists
  · intro i j hij
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro x hi hj
    exact hij ((hv x).unique hi.1 hj.1)
  · intro k
    exact (((measurable_id.sub_const (v k)) hC).nullMeasurableSet).inter hA
theorem preimage_image_proj (s : Conventions.StandingParameters) (A : Set (Fin 4 → ℝ)) :
    proj s ⁻¹' (proj s '' A) =
      ⋃ k : Fin 4 → ℤ, (fun x => x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) ⁻¹' A := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨k, rfl⟩ :=
      exists_latticeTranslate_of_torusProj_eq (ℓ := PeriodicLattice.torusSide s.L s.m) hyx
    exact ⟨k, hy⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, hk, torusProj_add_latticeTranslate _ x k⟩
theorem ofReal_torusVolume_eq_volume_fundamentalCube {s : Conventions.StandingParameters}
    {E : Set s.Torus} (hE : IsMeasurableTorusSet E) :
    ENNReal.ofReal (torusVolume E) =
      volume ((Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) (PeriodicLattice.torusSide s.L s.m)) ∩
        proj s ⁻¹' E) := by
  set C := Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) (PeriodicLattice.torusSide s.L s.m) with hCdef
  have hpre : NullMeasurableSet (proj s ⁻¹' E) volume := hE
  have hind : (fun x => E.indicator (1 : s.Torus → ℝ) (proj s x)) =
      (proj s ⁻¹' E).indicator fun _ => (1 : ℝ) := by
    funext x
    by_cases hx : proj s x ∈ E <;> simp [Set.indicator, hx]
  have hCfin : volume C < ∞ := by
    rw [hCdef, Real.volume_pi_Ico]
    simp
  have hfin : volume (proj s ⁻¹' E ∩ C) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt hCfin).ne
  have heq : torusVolume E = (volume (proj s ⁻¹' E ∩ C)).toReal := by
    unfold TorusMeasure.torusVolume TorusMeasure.torusIntegral
    rw [← hCdef, hind, integral_indicator₀ (hpre.mono Measure.restrict_le_self), setIntegral_const,
      measureReal_def, Measure.restrict_apply₀ (hpre.mono Measure.restrict_le_self)]
    simp
  rw [heq, ENNReal.ofReal_toReal hfin, inter_comm]
theorem volumeNonincreasing_holds : VolumeNonincreasing := by
  intro s A hA
  have hLpos : (0 : ℝ) < s.L := by
    have := s.isAdmissible.2
    exact_mod_cast (by omega : 0 < s.L)
  have hside : 0 < PeriodicLattice.torusSide s.L s.m := by
    unfold PeriodicLattice.torusSide
    positivity
  have hA' : NullMeasurableSet A volume := hA
  have himg : IsMeasurableTorusSet (proj s '' A) := by
    unfold IsMeasurableTorusSet IsNullMeasurableR4
    rw [preimage_image_proj]
    exact NullMeasurableSet.iUnion fun k =>
      hA'.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving
  have hCm : MeasurableSet
      (Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) (PeriodicLattice.torusSide s.L s.m)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hsum := tsum_volume_translatedPieces hCm hA'
    (latticeTranslate (PeriodicLattice.torusSide s.L s.m))
    (existsUnique_translate_mem_fundamentalCube hside)
  have hvol := ofReal_torusVolume_eq_volume_fundamentalCube himg
  rw [preimage_image_proj, inter_iUnion] at hvol
  refine ⟨himg, ?_, fun hinj => ?_⟩
  · rw [hvol]
    exact (measure_iUnion_le _).trans hsum.le
  · rw [hvol]
    unfold volumeR4
    rw [← hsum]
    apply measure_iUnion₀
    · intro i j hij
      apply Disjoint.aedisjoint
      rw [Set.disjoint_left]
      rintro x ⟨-, hi⟩ ⟨-, hj⟩
      have hproj : proj s (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) i) =
          proj s (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) j) :=
        (torusProj_add_latticeTranslate _ x i).trans (torusProj_add_latticeTranslate _ x j).symm
      have hxy := hinj hi hj hproj
      apply hij
      funext μ
      have hμ := congrFun (add_left_cancel hxy) μ
      simp only [latticeTranslate] at hμ
      exact_mod_cast mul_left_cancel₀ hside.ne' hμ
    · intro k
      exact hCm.nullMeasurableSet.inter
        (hA'.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving)
end TorusProjection
end YangMills.Construction
end
