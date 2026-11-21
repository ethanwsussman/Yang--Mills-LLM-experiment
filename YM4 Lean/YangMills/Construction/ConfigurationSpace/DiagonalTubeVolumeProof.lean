import YangMills.Construction.ConfigurationSpace.DiagonalTubeVolume
import YangMills.Construction.ConfigurationSpace.TupleEuclideanBallVolume
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
theorem diagonalTubeVolumeBound_of (hBall : TupleEuclideanBallVolume) :
    DiagonalTubeVolumeBound := by
  classical
  intro n i i' hii s R hs hR
  have hi' : i' ≠ i := hii.symm
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Fin 4 → ℝ)
    (fun a : Fin n => a ≠ i)
  rw [Measure.volume_eq_prod] at he
  set B : Set ({a : Fin n // a ≠ i} → Fin 4 → ℝ) :=
    {y | Real.sqrt (∑ a, ∑ c, y a c ^ 2) ≤ R} with hBdef
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  let k : {a : Fin n // ¬ a ≠ i} := ⟨i, by simp⟩
  have hsub : Subsingleton {a : Fin n // ¬ a ≠ i} :=
    ⟨fun a b => Subtype.ext ((not_not.mp a.2).trans (not_not.mp b.2).symm)⟩
  set T : Set (({a : Fin n // a ≠ i} → Fin 4 → ℝ) × ({a : Fin n // ¬ a ≠ i} → Fin 4 → ℝ)) :=
    {p | p.1 ∈ B ∧ ∀ c, |p.2 k c - p.1 ⟨i', hi'⟩ c| ≤ s} with hTdef
  have hTm : MeasurableSet T := by
    have hT : T = Prod.fst ⁻¹' B ∩ ⋂ c, {p : ({a : Fin n // a ≠ i} → Fin 4 → ℝ) × ({a : Fin n // ¬ a ≠ i} → Fin 4 → ℝ) |
        |p.2 k c - p.1 ⟨i', hi'⟩ c| ≤ s} := by
      ext p
      simp [hTdef]
    rw [hT]
    exact (hBm.preimage measurable_fst).inter
      (MeasurableSet.iInter fun c => measurableSet_le (by fun_prop) measurable_const)
  have hsubset : {x : Config n | maxNorm (x i - x i') ≤ s ∧ configNorm x ≤ R} ⊆
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Fin 4 → ℝ)
        (fun a : Fin n => a ≠ i)) ⁻¹' T := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, fun c => ?_⟩
    · have hsum : ∑ ι : CoordIndex n, coords x ι ^ 2 = ∑ a, ∑ c, x a c ^ 2 := by
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv ofLex _ _ (fun _ => rfl)
      have hle : ∑ a : {a : Fin n // a ≠ i}, ∑ c, x a c ^ 2 ≤ ∑ a, ∑ c, x a c ^ 2 := by
        rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ i)) (by simp)
          (fun a => ∑ c, x a c ^ 2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => Finset.sum_nonneg fun c _ => sq_nonneg _)
      refine le_trans (Real.sqrt_le_sqrt hle) ?_
      rw [← hsum]
      exact hx2
    · have h := le_trans (le_ciSup (f := fun c => |(x i - x i') c|) (Finite.bddAbove_range _) c) hx1
      exact h
  have hsection : ∀ y, volume (Prod.mk y ⁻¹' T) ≤
      B.indicator (fun _ => ENNReal.ofReal ((2 * s) ^ 4)) y := by
    intro y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      have hcube : Prod.mk y ⁻¹' T ⊆ Set.pi Set.univ (fun _ : {a : Fin n // ¬ a ≠ i} =>
          Set.pi Set.univ (fun c : Fin 4 =>
            Set.Icc (y ⟨i', hi'⟩ c - s) (y ⟨i', hi'⟩ c + s))) := by
        intro z hz a _ c _
        have h := abs_le.mp (hz.2 c)
        have ha : a = k := Subsingleton.elim _ _
        rw [ha]
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      refine (measure_mono hcube).trans (le_of_eq ?_)
      rw [volume_pi_pi, Fintype.prod_subsingleton _ k, volume_pi_pi]
      have hside : ∀ c : Fin 4, volume (Set.Icc (y ⟨i', hi'⟩ c - s) (y ⟨i', hi'⟩ c + s)) =
          ENNReal.ofReal (2 * s) := by
        intro c
        rw [Real.volume_Icc]
        congr 1
        ring
      simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow (by positivity)]
    · rw [Set.indicator_of_notMem hy]
      have hempty : Prod.mk y ⁻¹' T = ∅ := by
        ext z
        simp [hTdef, hy]
      simp [hempty]
  have hcardpos : 1 ≤ Fintype.card {a : Fin n // a ≠ i} :=
    Fintype.card_pos_iff.mpr ⟨⟨i', hi'⟩⟩
  have hcard : 4 * Fintype.card {a : Fin n // a ≠ i} = 4 * n - 4 := by
    have h : Fintype.card {a : Fin n // a ≠ i} = n - 1 := by
      simp
    rw [h]
    omega
  have hBvol := hBall {a : Fin n // a ≠ i} hcardpos R hR
  rw [hcard] at hBvol
  calc volume {x : Config n | maxNorm (x i - x i') ≤ s ∧ configNorm x ≤ R}
      ≤ volume ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Fin 4 → ℝ)
          (fun a : Fin n => a ≠ i)) ⁻¹' T) := measure_mono hsubset
    _ = (volume.prod volume) T := he.measure_preimage hTm.nullMeasurableSet
    _ = ∫⁻ y, volume (Prod.mk y ⁻¹' T) := Measure.prod_apply hTm
    _ ≤ ∫⁻ y, B.indicator (fun _ => ENNReal.ofReal ((2 * s) ^ 4)) y :=
        lintegral_mono hsection
    _ = ENNReal.ofReal ((2 * s) ^ 4) * volume B := lintegral_indicator_const hBm _
    _ = ENNReal.ofReal ((2 * s) ^ 4 * unitBallVol (4 * n - 4) * R ^ (4 * n - 4)) := by
        rw [hBvol, ← ENNReal.ofReal_mul (by positivity), mul_assoc]
end YangMills.Construction.ConfigurationSpace
end
