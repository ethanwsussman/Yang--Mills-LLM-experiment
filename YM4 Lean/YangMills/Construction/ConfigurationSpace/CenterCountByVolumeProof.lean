import YangMills.Construction.ConfigurationSpace.CenterCountByVolume
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
open scoped ENNReal
namespace CenterCounting
variable {n : ℕ}
theorem side_pos (j : ℕ) : 0 < WhitneyScales.whitneySide j :=
  mul_pos WhitneyScales.isWhitneyRatio_whitneyRatio.1 (zpow_pos (by norm_num) _)
def openCoreBox (j : ℕ) (z : IntPoint n) : Set (Config n) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun c =>
    Set.Ioo (pieceCenter j z i c - 1 / 4 * WhitneyScales.whitneySide j)
      (pieceCenter j z i c + 1 / 4 * WhitneyScales.whitneySide j)
theorem measurableSet_openCoreBox (j : ℕ) (z : IntPoint n) :
    MeasurableSet (openCoreBox j z) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ioo
theorem openCoreBox_subset (j : ℕ) (z : IntPoint n) :
    openCoreBox j z ⊆ translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Ioo (-(1 / 4 * WhitneyScales.whitneySide j))
        (1 / 4 * WhitneyScales.whitneySide j)} := by
  intro y hy
  refine ⟨y - pieceCenter j z, ?_, (add_sub_cancel _ _).symm⟩
  intro ι
  have h := hy (ofLex ι).1 trivial (ofLex ι).2 trivial
  simp only [Set.mem_Ioo] at h
  simp only [coords, Pi.sub_apply, Set.mem_Ioo]
  constructor <;> linarith [h.1, h.2]
theorem volume_openCoreBox (j : ℕ) (z : IntPoint n) :
    volume (openCoreBox j z) = ENNReal.ofReal (WhitneyScales.whitneySide j / 2) ^ (4 * n) := by
  have hside : ∀ a : ℝ, a + 1 / 4 * WhitneyScales.whitneySide j -
      (a - 1 / 4 * WhitneyScales.whitneySide j) = WhitneyScales.whitneySide j / 2 := by
    intro a; ring
  unfold openCoreBox
  simp only [volume_pi_pi, Real.volume_Ioo, hside, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← pow_mul, mul_comm]
theorem disjoint_openCoreBox (j : ℕ) {z z' : IntPoint n} (hne : z ≠ z') :
    Disjoint (openCoreBox j z) (openCoreBox j z') := by
  obtain ⟨ι, hι⟩ := Function.ne_iff.mp hne
  refine Set.disjoint_left.mpr fun y hy hy' => hι ?_
  have h := hy (ofLex ι).1 trivial (ofLex ι).2 trivial
  have h' := hy' (ofLex ι).1 trivial (ofLex ι).2 trivial
  simp only [Set.mem_Ioo, pieceCenter, Prod.mk.eta, toLex_ofLex] at h h'
  have hu := side_pos j
  have hlt : ((z ι : ℝ) - z' ι) * WhitneyScales.whitneySide j < 1 * WhitneyScales.whitneySide j := by
    nlinarith [h.1, h.2, h'.1, h'.2]
  have hgt : ((z' ι : ℝ) - z ι) * WhitneyScales.whitneySide j < 1 * WhitneyScales.whitneySide j := by
    nlinarith [h.1, h.2, h'.1, h'.2]
  have h1 : (z ι : ℝ) - z' ι < 1 := lt_of_mul_lt_mul_right hlt hu.le
  have h2 : (z' ι : ℝ) - z ι < 1 := lt_of_mul_lt_mul_right hgt hu.le
  have h3 : z ι - z' ι < 1 := by exact_mod_cast h1
  have h4 : z' ι - z ι < 1 := by exact_mod_cast h2
  omega
theorem ofReal_inv_side_pow_mul (j m : ℕ) :
    ENNReal.ofReal ((2 / WhitneyScales.whitneySide j) ^ m) *
      ENNReal.ofReal (WhitneyScales.whitneySide j / 2) ^ m = 1 := by
  have hu := side_pos j
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
    show 2 / WhitneyScales.whitneySide j * (WhitneyScales.whitneySide j / 2) = 1 by field_simp,
    one_pow, ENNReal.ofReal_one]
theorem finset_card_le (j : ℕ) (E : Set (Config n)) (F : Finset (IntPoint n))
    (hF : ∀ z ∈ F, openCoreBox j z ⊆ E) :
    (F.card : ℝ≥0∞) ≤ ENNReal.ofReal ((2 / WhitneyScales.whitneySide j) ^ (4 * n)) * volume E := by
  have hsum : (F.card : ℝ≥0∞) * ENNReal.ofReal (WhitneyScales.whitneySide j / 2) ^ (4 * n) ≤
      volume E := by
    calc (F.card : ℝ≥0∞) * ENNReal.ofReal (WhitneyScales.whitneySide j / 2) ^ (4 * n)
        = ∑ z ∈ F, volume (openCoreBox j z) := by simp [volume_openCoreBox]
      _ = volume (⋃ z ∈ F, openCoreBox j z) :=
          (measure_biUnion_finset
            (fun _ _ _ _ hne => disjoint_openCoreBox j hne)
            (fun z _ => measurableSet_openCoreBox j z)).symm
      _ ≤ volume E := measure_mono (Set.iUnion₂_subset hF)
  calc (F.card : ℝ≥0∞)
      = ENNReal.ofReal ((2 / WhitneyScales.whitneySide j) ^ (4 * n)) *
          ((F.card : ℝ≥0∞) * ENNReal.ofReal (WhitneyScales.whitneySide j / 2) ^ (4 * n)) := by
        rw [mul_left_comm, ofReal_inv_side_pow_mul, mul_one]
    _ ≤ ENNReal.ofReal ((2 / WhitneyScales.whitneySide j) ^ (4 * n)) * volume E := by gcongr
end CenterCounting
open CenterCounting in
theorem centerCountByVolume_holds : CenterCountByVolume := by
  intro n j Z E hZ
  have hbox : ∀ z ∈ Z, openCoreBox j z ⊆ E := fun z hz =>
    (openCoreBox_subset j z).trans (hZ z hz)
  rcases Z.finite_or_infinite with hfin | hinf
  · obtain ⟨F, rfl⟩ := hfin.exists_finset_coe
    have hcard : setCard (F : Set (IntPoint n)) = (F.card : ℕ∞) :=
      Set.encard_coe_eq_coe_finsetCard F
    rw [hcard, ENat.toENNReal_coe]
    exact finset_card_le j E F fun z hz => hbox z hz
  · have htop : ENNReal.ofReal ((2 / WhitneyScales.whitneySide j) ^ (4 * n)) * volume E = ∞ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hne
      obtain ⟨F, hFZ, hFm⟩ := hinf.exists_subset_card_eq m
      have hle := finset_card_le j E F fun z hz => hbox z (hFZ hz)
      rw [hFm] at hle
      exact absurd hle (not_le.mpr hm)
    rw [htop]
    exact le_top
end YangMills.Construction.ConfigurationSpace
end
