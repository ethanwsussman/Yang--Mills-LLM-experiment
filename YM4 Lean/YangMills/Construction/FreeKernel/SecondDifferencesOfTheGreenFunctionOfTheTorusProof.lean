import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.HeatKernelsAndTheGreensFunctions
import YangMills.Construction.FreeKernel.MultipliersSymbolCharactersAndGreensFunctionsOnClasses
import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.VectorClasses YangMills.Construction.FourDimKernel
def TorusGreenSecondDiffBound : Prop :=
  YangMills.Construction.Constants.HeatKernel.fieldConstant ≠ ⊤ ∧
    ∀ L : ℕ, 2 ≤ L → ∀ μ μ' : Fin 4, ∀ c : ℝ, 0 < c → c < 1 / 2 → ∀ x : Fin 4 → ℤ,
      1 ≤ intVecNorm x → intVecNorm x ≤ c * (L : ℝ) →
        ‖mixedSecondDiff μ μ' (greenOnVectors L) x -
            ((mixedSecondPartial μ μ' continuumGreenFunction (fun i => (x i : ℝ)) : ℝ) : ℂ)‖ ≤
          YangMills.Construction.Constants.HeatKernel.fieldConstant.toReal *
            (intVecNorm x ^ (-5 : ℤ) + (L : ℝ) ^ (-4 : ℤ))
end YangMills.Construction.FreeKernel
end

noncomputable section
namespace YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof
open MeasureTheory
open YangMills.Construction.FourDimKernel YangMills.Construction.Constants.HeatKernel
open YangMills.Construction.FreeKernel.HeatKernelGreen
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.VectorClasses
theorem sum_inv_sq_natCast_le_two (A : Finset ℕ) (hA : 0 ∉ A) :
    ∑ m ∈ A, ((m : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have telescope : ∀ M : ℕ, ∑ m ∈ Finset.Icc 1 (M + 1), ((m : ℝ) ^ 2)⁻¹ ≤ 2 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have hstep : ((((M + 1 + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ 1 / ((M : ℝ) + 1) - 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have hsub : A ⊆ Finset.Icc 1 (A.sup id + 1) := by
    intro m hm
    refine Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero fun h => hA (h ▸ hm), ?_⟩
    have : m ≤ A.sup id := Finset.le_sup (f := id) hm
    omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) hsub
    (fun _ _ _ => by positivity)
  have h2 := telescope (A.sup id)
  have h3 : (0 : ℝ) ≤ 1 / (((A.sup id : ℕ) : ℝ) + 1) := by positivity
  linarith
theorem sum_comp_le_card_mul {α : Type*} [DecidableEq α] (S : Finset α) (φ : α → ℕ) (K g : ℕ → ℝ)
    (hg : ∀ m, 0 ≤ g m) (hcard : ∀ m, ((S.filter fun a => φ a = m).card : ℝ) ≤ K m) :
    ∑ a ∈ S, g (φ a) ≤ ∑ m ∈ S.image φ, K m * g m := by
  rw [Finset.sum_comp g φ]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hcard m) (hg m)
theorem sum_inv_sq_natAbs_le_four (T : Finset ℤ) (hT : 0 ∉ T) :
    ∑ l ∈ T, (((l.natAbs : ℕ) : ℝ) ^ 2)⁻¹ ≤ 4 := by
  have h1 := sum_comp_le_card_mul T Int.natAbs (fun _ => 2) (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹)
    (fun _ => by positivity) (fun m => by
      have hsub : (T.filter fun a => a.natAbs = m) ⊆ {(m : ℤ), -(m : ℤ)} := by
        intro a ha
        have := (Finset.mem_filter.1 ha).2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
      exact_mod_cast hc)
  have h2 := sum_inv_sq_natCast_le_two (T.image Int.natAbs) (by
    intro h
    obtain ⟨a, ha, ha0⟩ := Finset.mem_image.1 h
    exact hT (Int.natAbs_eq_zero.1 ha0 ▸ ha))
  rw [← Finset.mul_sum] at h1
  linarith
def supNormInt (w : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun μ => (w μ).natAbs
theorem exists_coord_eq_supNormInt {w : Fin 4 → ℤ} (hw : w ≠ 0) :
    ∃ μ, (w μ).natAbs = supNormInt w ∧ 1 ≤ supNormInt w := by
  obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
    (fun μ => (w μ).natAbs)
  refine ⟨μ, hμ.symm, ?_⟩
  obtain ⟨ν, hν⟩ : ∃ ν, w ν ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have h1 : (w ν).natAbs ≤ supNormInt w :=
    Finset.le_sup (f := fun μ => (w μ).natAbs) (Finset.mem_univ ν)
  have h2 : 0 < (w ν).natAbs := Int.natAbs_pos.2 hν
  omega
theorem sum_inv_supNormInt_pow_six_le (S : Finset (Fin 4 → ℤ)) (hS : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, (((supNormInt w : ℕ) : ℝ) ^ 6)⁻¹ ≤ 162 := by
  have h1 := sum_comp_le_card_mul S supNormInt (fun m : ℕ => (2 * (m : ℝ) + 1) ^ 4)
    (fun m : ℕ => ((m : ℝ) ^ 6)⁻¹) (fun _ => by positivity) (fun m => by
      have hsub : (S.filter fun a => supNormInt a = m) ⊆
          Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) (m : ℤ) := by
        intro a ha
        have hm := (Finset.mem_filter.1 ha).2
        refine Fintype.mem_piFinset.2 fun μ => Finset.mem_Icc.2 ?_
        have : (a μ).natAbs ≤ supNormInt a :=
          Finset.le_sup (f := fun μ => (a μ).natAbs) (Finset.mem_univ μ)
        omega
      have hc := Finset.card_le_card hsub
      rw [Fintype.card_piFinset] at hc
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
      have he : ((m : ℤ) + 1 - (-(m : ℤ))).toNat = 2 * m + 1 := by omega
      rw [he] at hc
      have := (Nat.cast_le (α := ℝ)).2 hc
      push_cast at this
      exact this)
  have h2 := sum_inv_sq_natCast_le_two (S.image supNormInt) (by
    intro h
    obtain ⟨a, ha, ha0⟩ := Finset.mem_image.1 h
    have ha' : a ≠ 0 := fun e => hS (e ▸ ha)
    obtain ⟨μ, -, hμ⟩ := exists_coord_eq_supNormInt ha'
    omega)
  have h3 : ∑ m ∈ S.image supNormInt, (2 * (m : ℝ) + 1) ^ 4 * ((m : ℝ) ^ 6)⁻¹ ≤
      ∑ m ∈ S.image supNormInt, 81 * ((m : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hm
    have ha' : a ≠ 0 := fun e => hS (e ▸ ha)
    obtain ⟨μ, -, hμ⟩ := exists_coord_eq_supNormInt ha'
    have hm1 : (1 : ℝ) ≤ (supNormInt a : ℝ) := by exact_mod_cast hμ
    set x : ℝ := (supNormInt a : ℝ)
    have hx : 0 < x := by linarith
    have hb : (2 * x + 1) ^ 4 ≤ 81 * x ^ 4 := by
      have : 2 * x + 1 ≤ 3 * x := by linarith
      calc (2 * x + 1) ^ 4 ≤ (3 * x) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 81 * x ^ 4 := by ring
    calc (2 * x + 1) ^ 4 * (x ^ 6)⁻¹ ≤ 81 * x ^ 4 * (x ^ 6)⁻¹ :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 81 * (x ^ 2)⁻¹ := by field_simp
  rw [← Finset.mul_sum] at h3
  linarith
theorem sum_prod_coords_le_pow_four (f : ℤ → ℝ) (hf : ∀ l, 0 ≤ f l) (B : ℝ)
    (hB : ∀ T : Finset ℤ, ∑ l ∈ T, f l ≤ B)
    (S : Finset (Fin 4 → ℤ)) : ∑ w ∈ S, ∏ μ, f (w μ) ≤ B ^ 4 := by
  classical
  set T : Finset ℤ := S.biUnion fun w => Finset.univ.image w with hT
  have hsub : S ⊆ Fintype.piFinset fun _ : Fin 4 => T := by
    intro w hw
    refine Fintype.mem_piFinset.2 fun μ => Finset.mem_biUnion.2 ⟨w, hw, ?_⟩
    exact Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩
  calc ∑ w ∈ S, ∏ μ, f (w μ)
      ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin 4 => T), ∏ μ, f (w μ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => hf _)
    _ = ∏ _μ : Fin 4, ∑ l ∈ T, f l := (Finset.prod_univ_sum (fun _ : Fin 4 => T) fun _ l => f l).symm
    _ = (∑ l ∈ T, f l) ^ 4 := by simp
    _ ≤ B ^ 4 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hf _) (hB T) 4
theorem norm_sub_term_le_of_hasSum {ι : Type*} [DecidableEq ι] {F : ι → ℂ} {a : ℂ}
    (hF : HasSum F a) (i₀ : ι) {B : ℝ} (hB : ∀ S : Finset ι, i₀ ∉ S → ∑ i ∈ S, ‖F i‖ ≤ B) :
    ‖a - F i₀‖ ≤ B := by
  have ht0 : Filter.Tendsto (fun S : Finset ι => ∑ i ∈ S, F i) Filter.atTop (nhds a) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using hF
  have ht : Filter.Tendsto (fun S : Finset ι => ‖∑ i ∈ S, F i - F i₀‖) Filter.atTop
      (nhds ‖a - F i₀‖) := (ht0.sub_const _).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with S hS
  have h0 : i₀ ∈ S := hS (by simp)
  rw [← Finset.add_sum_erase S F h0, add_sub_cancel_left]
  exact (norm_sum_le _ _).trans (hB _ (Finset.notMem_erase _ _))
theorem intVecNorm_sq (x : Fin 4 → ℤ) : intVecNorm x ^ 2 = ∑ μ, (x μ : ℝ) ^ 2 := by
  unfold intVecNorm FourVector.euclidNorm
  have h : 0 ≤ FourVector.inner4 (fun μ => (x μ : ℝ)) (fun μ => (x μ : ℝ)) :=
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rw [Real.sq_sqrt h]
  simp [FourVector.inner4, pow_two]
theorem abs_coord_le_intVecNorm (x : Fin 4 → ℤ) (μ : Fin 4) :
    |(x μ : ℝ)| ≤ intVecNorm x := by
  have h0 : 0 ≤ intVecNorm x := Real.sqrt_nonneg _
  have h1 : (x μ : ℝ) ^ 2 ≤ intVecNorm x ^ 2 := by
    rw [intVecNorm_sq]
    exact Finset.single_le_sum (f := fun μ => (x μ : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  exact abs_le_of_sq_le_sq h1 h0
theorem half_mul_abs_le_abs_translate (n : ℕ) {a w : ℤ} (ha : |(a : ℝ)| ≤ (n : ℝ) / 2)
    (hw : w ≠ 0) : (n : ℝ) / 2 * |(w : ℝ)| ≤ |((a + (n : ℤ) * w : ℤ) : ℝ)| := by
  push_cast
  have h1 : (1 : ℝ) ≤ |(w : ℝ)| := by exact_mod_cast Int.one_le_abs hw
  have h2 : |(n : ℝ) * w| = n * |(w : ℝ)| := by rw [abs_mul, Nat.abs_cast]
  have h3 : |(n : ℝ) * w| - |(a : ℝ)| ≤ |(a : ℝ) + n * w| := by
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * w) (-(a : ℝ))
    simpa [add_comm] using this
  nlinarith
theorem bracketOnePlus_pos {y : ℝ} (hy : 0 ≤ y) : 0 < bracketOnePlus y := by
  unfold bracketOnePlus
  linarith
theorem bracketOnePlus_zpow_le_inv_pow {y L : ℝ} (hy : 0 < y) (h : y ≤ L) :
    bracketOnePlus L ^ (-6 : ℤ) ≤ (y ^ 6)⁻¹ := by
  have h1 : y ≤ bracketOnePlus L := by
    unfold bracketOnePlus
    linarith
  rw [zpow_neg]
  have h2 : y ^ 6 ≤ bracketOnePlus L ^ (6 : ℤ) := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact pow_le_pow_left₀ hy.le h1 6
  exact inv_anti₀ (by positivity) h2
theorem bracketOnePlus_zpow_antitone {a b : ℝ} (hb : 0 ≤ b) (h : b ≤ a) :
    bracketOnePlus a ^ (-6 : ℤ) ≤ bracketOnePlus b ^ (-6 : ℤ) := by
  have h1 : bracketOnePlus b ≤ bracketOnePlus a := by
    unfold bracketOnePlus
    linarith
  have h0 := bracketOnePlus_pos hb
  rw [zpow_neg, zpow_neg]
  have h2 : bracketOnePlus b ^ (6 : ℤ) ≤ bracketOnePlus a ^ (6 : ℤ) := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ h0.le h1 6
  exact inv_anti₀ (by positivity) h2
theorem bracketOnePlus_zpow_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ bracketOnePlus y ^ (-6 : ℤ) :=
  (zpow_pos (bracketOnePlus_pos hy) _).le
theorem bracketOnePlus_zpow_le_one {y : ℝ} (hy : 0 ≤ y) : bracketOnePlus y ^ (-6 : ℤ) ≤ 1 := by
  have := bracketOnePlus_zpow_antitone hy (le_refl y)
  have h := bracketOnePlus_zpow_antitone (a := y) (b := 0) le_rfl hy
  simpa [bracketOnePlus] using h
theorem shortTime_image_le {n : ℕ} (hn : 0 < n) {z w : Fin 4 → ℤ}
    (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2) (hw : w ≠ 0) :
    bracketOnePlus (intVecNorm (z + (n : ℤ) • w)) ^ (-6 : ℤ) ≤
      64 * ((n : ℝ) ^ 6)⁻¹ * (((supNormInt w : ℕ) : ℝ) ^ 6)⁻¹ := by
  obtain ⟨μ, hμ, h1⟩ := exists_coord_eq_supNormInt hw
  have hwμ : w μ ≠ 0 := by
    intro h
    rw [h] at hμ
    simp at hμ
    omega
  have hL : (n : ℝ) / 2 * (supNormInt w : ℝ) ≤ intVecNorm (z + (n : ℤ) • w) := by
    have h2 := half_mul_abs_le_abs_translate n (hz μ) hwμ
    have h3 := abs_coord_le_intVecNorm (z + (n : ℤ) • w) μ
    have h4 : ((z + (n : ℤ) • w) μ) = z μ + (n : ℤ) * w μ := by simp
    rw [h4] at h3
    have h5 : |(w μ : ℝ)| = (supNormInt w : ℝ) := by
      rw [← hμ, Nat.cast_natAbs, Int.cast_abs]
    rw [h5] at h2
    linarith
  have h6 := bracketOnePlus_zpow_le_inv_pow (by positivity) hL
  refine h6.trans (le_of_eq ?_)
  field_simp
  norm_num
theorem shortTime_images_sum_le {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) {z : Fin 4 → ℤ}
    (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2) {F : (Fin 4 → ℤ) → ℂ}
    (hF : ∀ w, ‖F w‖ ≤ C * bracketOnePlus (intVecNorm (z + (n : ℤ) • w)) ^ (-6 : ℤ))
    (S : Finset (Fin 4 → ℤ)) (hS : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, ‖F w‖ ≤ 10368 * C * ((n : ℝ) ^ 6)⁻¹ := by
  have h1 : ∀ w ∈ S, ‖F w‖ ≤ (64 * C * ((n : ℝ) ^ 6)⁻¹) * (((supNormInt w : ℕ) : ℝ) ^ 6)⁻¹ := by
    intro w hw
    have hw' : w ≠ 0 := fun e => hS (e ▸ hw)
    refine (hF w).trans ?_
    have := mul_le_mul_of_nonneg_left (shortTime_image_le hn hz hw') hC
    linarith
  have h2 := Finset.sum_le_sum h1
  rw [← Finset.mul_sum] at h2
  have h3 := sum_inv_supNormInt_pow_six_le S hS
  have h4 : 0 ≤ 64 * C * ((n : ℝ) ^ 6)⁻¹ := by positivity
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  linarith
def imageWeight (n : ℕ) (t : ℝ) (l : ℤ) : ℝ :=
  if l = 0 then 1 else bracketOnePlus ((n : ℝ) * |(l : ℝ)| / (2 * Real.sqrt t)) ^ (-6 : ℤ)
theorem imageWeight_nonneg (n : ℕ) {t : ℝ} (l : ℤ) : 0 ≤ imageWeight n t l := by
  unfold imageWeight
  split_ifs
  · norm_num
  · exact bracketOnePlus_zpow_nonneg (by positivity)
theorem imageWeight_le {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) {l : ℤ} (hl : l ≠ 0) :
    imageWeight n t l ≤ 64 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ * (((l.natAbs : ℕ) : ℝ) ^ 2)⁻¹ := by
  have habs : |(l : ℝ)| = (l.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 : (1 : ℝ) ≤ (l.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hl
  unfold imageWeight
  rw [if_neg hl, habs]
  set m : ℝ := (l.natAbs : ℝ)
  have h2 := bracketOnePlus_zpow_le_inv_pow (y := (n : ℝ) * m / (2 * Real.sqrt t))
    (L := (n : ℝ) * m / (2 * Real.sqrt t)) (by positivity) le_rfl
  refine h2.trans ?_
  have h3 : (((n : ℝ) * m / (2 * Real.sqrt t)) ^ 6)⁻¹ =
      64 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ * (m ^ 6)⁻¹ := by
    have hs6 : Real.sqrt t ^ 6 = t ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt ht.le]
    rw [div_pow, mul_pow, mul_pow, hs6]
    field_simp
    norm_num
  rw [h3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine inv_anti₀ (by positivity) ?_
  calc m ^ 2 = m ^ 2 * 1 := (mul_one _).symm
    _ ≤ m ^ 2 * m ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ h1) (by positivity)
    _ = m ^ 6 := by ring
theorem sum_imageWeight_le {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (T : Finset ℤ) :
    ∑ l ∈ T, imageWeight n t l ≤ 1 + 256 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ := by
  classical
  have hc : 0 ≤ 64 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ := by positivity
  have h1 : ∑ l ∈ T, imageWeight n t l ≤ 1 + ∑ l ∈ T.erase 0, imageWeight n t l := by
    by_cases h : (0 : ℤ) ∈ T
    · rw [← Finset.add_sum_erase T _ h]
      simp [imageWeight]
    · rw [Finset.erase_eq_of_notMem h]
      linarith
  have h2 : ∑ l ∈ T.erase 0, imageWeight n t l ≤
      ∑ l ∈ T.erase 0, 64 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ * (((l.natAbs : ℕ) : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum fun l hl => imageWeight_le hn ht (Finset.ne_of_mem_erase hl)
  rw [← Finset.mul_sum] at h2
  have h3 := sum_inv_sq_natAbs_le_four (T.erase 0) (Finset.notMem_erase _ _)
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  linarith
theorem longTime_prod_le_imageWeight {n : ℕ} {t : ℝ} (ht : 0 < t) {z : Fin 4 → ℤ}
    (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2) (w : Fin 4 → ℤ) :
    ∏ μ, bracketOnePlus (|((z + (n : ℤ) • w) μ : ℝ)| / Real.sqrt t) ^ (-6 : ℤ) ≤
      ∏ μ, imageWeight n t (w μ) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  refine Finset.prod_le_prod (fun _ _ => bracketOnePlus_zpow_nonneg (by positivity)) fun μ _ => ?_
  unfold imageWeight
  split_ifs with h
  · exact bracketOnePlus_zpow_le_one (by positivity)
  · refine bracketOnePlus_zpow_antitone (by positivity) ?_
    have h2 := half_mul_abs_le_abs_translate n (hz μ) h
    have h4 : ((z + (n : ℤ) • w) μ) = z μ + (n : ℤ) * w μ := by simp
    rw [h4, div_le_div_iff₀ (by positivity) hs]
    nlinarith
theorem longTime_images_sum_le {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t)
    (htn : t ≤ (n : ℝ) ^ 2) {z : Fin 4 → ℤ} (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2)
    {F : (Fin 4 → ℤ) → ℂ}
    (hF : ∀ w, ‖F w‖ ≤ C * t ^ (-3 : ℤ) *
      ∏ μ, bracketOnePlus (|((z + (n : ℤ) • w) μ : ℝ)| / Real.sqrt t) ^ (-6 : ℤ))
    (S : Finset (Fin 4 → ℤ)) (hS : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, ‖F w‖ ≤ 1024 * 257 ^ 3 * C * ((n : ℝ) ^ 6)⁻¹ := by
  classical
  set s : ℝ := 256 * t ^ 3 * ((n : ℝ) ^ 6)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 256 := by
    have h1 : t ^ 3 ≤ ((n : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ ht.le htn 3
    have h2 : t ^ 3 * ((n : ℝ) ^ 6)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      calc t ^ 3 ≤ ((n : ℝ) ^ 2) ^ 3 := h1
        _ = (n : ℝ) ^ 6 := by ring
    rw [hs]
    nlinarith
  have hprod := sum_prod_coords_le_pow_four (imageWeight n t) (fun l => imageWeight_nonneg n l)
    (1 + s) (fun T => sum_imageWeight_le hn ht T) (insert 0 S)
  rw [Finset.sum_insert hS] at hprod
  have hone : ∏ μ : Fin 4, imageWeight n t ((0 : Fin 4 → ℤ) μ) = 1 := by simp [imageWeight]
  rw [hone] at hprod
  have hB : (1 + s) ^ 4 - 1 ≤ 4 * 257 ^ 3 * s := by
    have hb3 : (1 + s) ^ 3 ≤ 257 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hb2 : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e : (1 + s) ^ 4 - 1 = s * ((1 + s) ^ 3 + (1 + s) ^ 2 + (1 + s) + 1) := by ring
    rw [e]
    have h4 : (1 + s) ^ 3 + (1 + s) ^ 2 + (1 + s) + 1 ≤ 4 * 257 ^ 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hs0]
  have hterm : ∀ w ∈ S, ‖F w‖ ≤ (C * t ^ (-3 : ℤ)) * ∏ μ, imageWeight n t (w μ) := by
    intro w _
    refine (hF w).trans
      (mul_le_mul_of_nonneg_left (longTime_prod_le_imageWeight ht hz w) (by positivity))
  have h2 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at h2
  have hc : 0 ≤ C * t ^ (-3 : ℤ) := by positivity
  have h3 : ∑ w ∈ S, ∏ μ, imageWeight n t (w μ) ≤ 4 * 257 ^ 3 * s := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  refine h2.trans (h4.trans (le_of_eq ?_))
  rw [hs, zpow_neg]
  have e3 : t ^ (3 : ℤ) = t ^ 3 := by norm_cast
  rw [e3]
  field_simp
  ring
theorem mixedSecondDiff_apply {R : Type*} [AddCommGroup R] (ν ν' : Fin 4)
    (f : (Fin 4 → ℤ) → R) (x : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' f x =
      f (x + unitVector ν) - f (x + unitVector ν - unitVector ν') - f x + f (x - unitVector ν') := by
  simp only [mixedSecondDiff, forwardDiff, backwardDiff]
  abel
theorem hasSum_mixedSecondDiff_translates {p P : (Fin 4 → ℤ) → ℂ} (n : ℕ)
    (hp : ∀ x, HasSum (fun w : Fin 4 → ℤ => p (x + (n : ℤ) • w)) (P x)) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) :
    HasSum (fun w : Fin 4 → ℤ => mixedSecondDiff ν ν' p (z + (n : ℤ) • w))
      (mixedSecondDiff ν ν' P z) := by
  have e : (fun w : Fin 4 → ℤ => mixedSecondDiff ν ν' p (z + (n : ℤ) • w)) =
      fun w => p ((z + unitVector ν) + (n : ℤ) • w) -
        p ((z + unitVector ν - unitVector ν') + (n : ℤ) • w) - p (z + (n : ℤ) • w) +
        p ((z - unitVector ν') + (n : ℤ) • w) := by
    funext w
    rw [mixedSecondDiff_apply,
      show z + (n : ℤ) • w + unitVector ν = z + unitVector ν + (n : ℤ) • w by abel,
      show z + unitVector ν + (n : ℤ) • w - unitVector ν' =
        z + unitVector ν - unitVector ν' + (n : ℤ) • w by abel,
      show z + (n : ℤ) • w - unitVector ν' = z - unitVector ν' + (n : ℤ) • w by abel]
  rw [e, mixedSecondDiff_apply]
  exact (((hp _).sub (hp _)).sub (hp _)).add (hp _)
abbrev momentumBox (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ : Fin 4 => momentumRange n
theorem torusHeatKernel_eq_sum {n : ℕ} (hn : n ≠ 0) (t : ℝ) (z : Fin 4 → ℤ) :
    torusHeatKernel n t z = (1 / (n : ℂ) ^ 4) * ∑ N ∈ momentumBox n,
      expWave (momentumVec n N) z *
        ((Real.exp (-t * laplacianSymbol (momentumVec n N)) : ℝ) : ℂ) := by
  unfold torusHeatKernel
  rw [momentumSet_eq_image hn, finsum_mem_image (momentumVec_injective hn).injOn,
    finsum_mem_coe_finset]
theorem mixedSecondDiff_torusHeatKernel {n : ℕ} (hn : n ≠ 0) (t : ℝ) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' (torusHeatKernel n t) z = (1 / (n : ℂ) ^ 4) * ∑ N ∈ momentumBox n,
      mixedSecondDiff ν ν' (expWave (momentumVec n N)) z *
        ((Real.exp (-t * laplacianSymbol (momentumVec n N)) : ℝ) : ℂ) := by
  simp only [mixedSecondDiff_apply, torusHeatKernel_eq_sum hn, sub_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
theorem norm_expWave (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ‖expWave k z‖ = 1 := by
  unfold expWave
  exact Complex.norm_exp_I_mul_ofReal _
theorem norm_cexp_neg_sub_one (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * (θ : ℂ))) - 1‖ = ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  have e : Complex.exp (-(Complex.I * (θ : ℂ))) - 1 =
      -(Complex.exp (-(Complex.I * (θ : ℂ))) * (Complex.exp (Complex.I * (θ : ℂ)) - 1)) := by
    rw [mul_sub, ← Complex.exp_add]
    simp
  have h1 : ‖Complex.exp (-(Complex.I * (θ : ℂ)))‖ = 1 := by
    have : -(Complex.I * (θ : ℂ)) = Complex.I * ((-θ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this]
    exact Complex.norm_exp_I_mul_ofReal _
  rw [e, norm_neg, norm_mul, h1, one_mul]
theorem norm_mixedSecondDiff_expWave_le (hM : ExpWaveMultipliers)
    (hS : LaplacianSymbolModulusFormAndBounds) (ν ν' : Fin 4) (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    ‖mixedSecondDiff ν ν' (expWave k) z‖ ≤ laplacianSymbol k := by
  have hb := (hM k ν').2.1
  have hf := (hM k ν).1
  have e : mixedSecondDiff ν ν' (expWave k) z =
      -(Complex.exp (-(Complex.I * (k ν' : ℂ))) - 1) *
        ((Complex.exp (Complex.I * (k ν : ℂ)) - 1) * expWave k z) := by
    unfold mixedSecondDiff
    rw [hb]
    have h := congrFun hf z
    simp only [forwardDiff] at h ⊢
    rw [← mul_sub, h]
  have hW : ∀ μ, ‖Complex.exp (Complex.I * (k μ : ℂ)) - 1‖ ^ 2 ≤ laplacianSymbol k := by
    intro μ
    rw [hS.1 k]
    exact Finset.single_le_sum
      (f := fun μ => ‖Complex.exp (Complex.I * (k μ : ℂ)) - 1‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ μ)
  rw [e, norm_mul, norm_mul, norm_expWave, mul_one, norm_neg, norm_cexp_neg_sub_one]
  nlinarith [hW ν, hW ν', sq_nonneg (‖Complex.exp (Complex.I * (k ν : ℂ)) - 1‖ -
    ‖Complex.exp (Complex.I * (k ν' : ℂ)) - 1‖)]
abbrev coordSqSum (N : Fin 4 → ℤ) : ℝ := ∑ μ, (N μ : ℝ) ^ 2
theorem one_le_coordSqSum {N : Fin 4 → ℤ} (hN : N ≠ 0) : 1 ≤ coordSqSum N := by
  obtain ⟨μ, hμ⟩ : ∃ μ, N μ ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (funext h)
  have h1 : (1 : ℝ) ≤ (N μ : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (N μ) ^ 2 := by
      have := Int.one_le_abs hμ
      nlinarith [sq_abs (N μ), abs_nonneg (N μ)]
    exact_mod_cast this
  have h2 : (N μ : ℝ) ^ 2 ≤ coordSqSum N :=
    Finset.single_le_sum (f := fun μ => (N μ : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  linarith
theorem laplacianSymbol_momentumVec_bounds {n : ℕ} (hn : 0 < n)
    (hS : LaplacianSymbolModulusFormAndBounds) {N : Fin 4 → ℤ} (hN : N ∈ momentumBox n) :
    16 / (n : ℝ) ^ 2 * coordSqSum N ≤ laplacianSymbol (momentumVec n N) ∧
      laplacianSymbol (momentumVec n N) ≤ 4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * coordSqSum N := by
  have hmem : momentumVec n N ∈ momentumSet n := by
    rw [momentumSet_eq_image hn.ne']
    exact Set.mem_image_of_mem _ (Finset.mem_coe.2 hN)
  have hI : ∀ μ, momentumVec n N μ ∈ Set.Icc (-Real.pi) Real.pi := fun μ =>
    Set.Ioc_subset_Icc_self (hmem.2 μ)
  have hb := hS.2 _ hI
  have hnorm : FourVector.euclidNorm (momentumVec n N) ^ 2 =
      4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * coordSqSum N := by
    have h : 0 ≤ FourVector.inner4 (momentumVec n N) (momentumVec n N) :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    unfold FourVector.euclidNorm
    rw [Real.sq_sqrt h]
    simp only [FourVector.inner4, momentumVec, coordSqSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    field_simp
    ring
  rw [hnorm] at hb
  refine ⟨le_trans (le_of_eq ?_) hb.1, hb.2⟩
  field_simp
  ring
theorem sum_exp_neg_seven_sq_le (T : Finset ℤ) : ∑ l ∈ T, Real.exp (-7 * (l : ℝ) ^ 2) ≤ 2 := by
  classical
  have h1 : ∑ l ∈ T, Real.exp (-7 * (l : ℝ) ^ 2) ≤
      1 + ∑ l ∈ T.erase 0, Real.exp (-7 * (l : ℝ) ^ 2) := by
    by_cases h : (0 : ℤ) ∈ T
    · rw [← Finset.add_sum_erase T _ h]
      simp
    · rw [Finset.erase_eq_of_notMem h]
      linarith
  have h2 : ∑ l ∈ T.erase 0, Real.exp (-7 * (l : ℝ) ^ 2) ≤
      ∑ l ∈ T.erase 0, 1 / 7 * (((l.natAbs : ℕ) : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum fun l hl => ?_
    have hl0 := Finset.ne_of_mem_erase hl
    have hm : (1 : ℝ) ≤ (l.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hl0
    have hsq : (l : ℝ) ^ 2 = (l.natAbs : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hsq]
    set m : ℝ := (l.natAbs : ℝ)
    have hm0 : 0 < m ^ 2 := by positivity
    have he : 7 * m ^ 2 ≤ Real.exp (7 * m ^ 2) := by
      have := Real.add_one_le_exp (7 * m ^ 2)
      linarith
    have e1 : Real.exp (-7 * m ^ 2) = (Real.exp (7 * m ^ 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [e1]
    have e2 : 1 / 7 * (m ^ 2)⁻¹ = (7 * m ^ 2)⁻¹ := by
      field_simp
    rw [e2]
    exact inv_anti₀ (by positivity) he
  rw [← Finset.mul_sum] at h2
  have h3 := sum_inv_sq_natAbs_le_four (T.erase 0) (Finset.notMem_erase _ _)
  linarith
theorem symbol_mul_exp_le {n : ℕ} (hn : 0 < n) (hS : LaplacianSymbolModulusFormAndBounds) {t : ℝ}
    (ht : (n : ℝ) ^ 2 ≤ t) {N : Fin 4 → ℤ} (hN : N ∈ momentumBox n) :
    laplacianSymbol (momentumVec n N) * Real.exp (-t * laplacianSymbol (momentumVec n N)) ≤
      (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 / (n : ℝ) ^ 2 * t)) *
        ∏ μ, Real.exp (-7 * ((N μ : ℤ) : ℝ) ^ 2) := by
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le hn2 ht
  have hc : 0 ≤ (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 / (n : ℝ) ^ 2 * t)) *
      ∏ μ, Real.exp (-7 * ((N μ : ℤ) : ℝ) ^ 2) := by positivity
  by_cases h0 : N = 0
  · have : laplacianSymbol (momentumVec n N) = 0 := by
      subst h0
      simp [laplacianSymbol, momentumVec]
    rw [this, zero_mul]
    exact hc
  obtain ⟨hlo, hhi⟩ := laplacianSymbol_momentumVec_bounds hn hS hN
  set ω : ℝ := laplacianSymbol (momentumVec n N)
  set A : ℝ := coordSqSum N
  have hA : 1 ≤ A := one_le_coordSqSum h0
  have hτ : 1 ≤ t / (n : ℝ) ^ 2 := by rwa [one_le_div hn2]
  set τ : ℝ := t / (n : ℝ) ^ 2 with hτd
  have htτ : t = τ * (n : ℝ) ^ 2 := by
    rw [hτd]
    field_simp
  have hmain : 8 * τ + 8 * A ≤ t * ω := by
    have h1 : t * (16 / (n : ℝ) ^ 2 * A) ≤ t * ω := mul_le_mul_of_nonneg_left hlo ht0.le
    have h2 : t * (16 / (n : ℝ) ^ 2 * A) = 16 * τ * A := by
      rw [htτ]
      field_simp
    nlinarith [mul_nonneg (sub_nonneg.2 hτ) (sub_nonneg.2 hA)]
  have hexp : Real.exp (-t * ω) ≤ Real.exp (-8 * τ) * Real.exp (-8 * A) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hAe : A ≤ Real.exp A := by
    have := Real.add_one_le_exp A
    linarith
  have hprod : ∏ μ, Real.exp (-7 * ((N μ : ℤ) : ℝ) ^ 2) = Real.exp (-7 * A) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  have h8 : -8 / (n : ℝ) ^ 2 * t = -8 * τ := by
    rw [hτd]
    ring
  rw [hprod, h8]
  calc ω * Real.exp (-t * ω)
      ≤ (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * A) * (Real.exp (-8 * τ) * Real.exp (-8 * A)) :=
        mul_le_mul hhi hexp (Real.exp_pos _).le (by positivity)
    _ = (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 * τ)) * (A * Real.exp (-8 * A)) := by ring
    _ ≤ (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 * τ)) * Real.exp (-7 * A) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc A * Real.exp (-8 * A) ≤ Real.exp A * Real.exp (-8 * A) :=
              mul_le_mul_of_nonneg_right hAe (Real.exp_pos _).le
          _ = Real.exp (-7 * A) := by
              rw [← Real.exp_add]
              congr 1
              ring
theorem torusHeatKernel_mixedSecondDiff_decay {n : ℕ} (hn : 0 < n) (hM : ExpWaveMultipliers)
    (hS : LaplacianSymbolModulusFormAndBounds) {t : ℝ} (ht : (n : ℝ) ^ 2 ≤ t) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) :
    ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z‖ ≤
      64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹ * Real.exp (-8 / (n : ℝ) ^ 2 * t) := by
  rw [mixedSecondDiff_torusHeatKernel hn.ne', norm_mul]
  have h1 : ‖(1 / (n : ℂ) ^ 4)‖ = ((n : ℝ) ^ 4)⁻¹ := by
    simp
  rw [h1]
  have h2 : ‖∑ N ∈ momentumBox n, mixedSecondDiff ν ν' (expWave (momentumVec n N)) z *
        ((Real.exp (-t * laplacianSymbol (momentumVec n N)) : ℝ) : ℂ)‖ ≤
      ∑ N ∈ momentumBox n,
        (4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 / (n : ℝ) ^ 2 * t)) *
          ∏ μ, Real.exp (-7 * ((N μ : ℤ) : ℝ) ^ 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun N hN => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans ?_ (symbol_mul_exp_le hn hS ht hN)
    exact mul_le_mul_of_nonneg_right (norm_mixedSecondDiff_expWave_le hM hS ν ν' _ z)
      (Real.exp_pos _).le
  rw [← Finset.mul_sum] at h2
  have h3 := sum_prod_coords_le_pow_four (fun l : ℤ => Real.exp (-7 * (l : ℝ) ^ 2))
    (fun _ => (Real.exp_pos _).le) 2 sum_exp_neg_seven_sq_le (momentumBox n)
  have hc : 0 ≤ 4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * Real.exp (-8 / (n : ℝ) ^ 2 * t) := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  have h5 := h2.trans h4
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ ((n : ℝ) ^ 4)⁻¹)
  refine h6.trans (le_of_eq ?_)
  field_simp
  ring
theorem norm_integral_Ioi_of_exp_bound {f : ℝ → ℂ} {n : ℕ} (hn : 0 < n)
    (hf : ∀ t, (n : ℝ) ^ 2 ≤ t →
      ‖f t‖ ≤ 64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹ * Real.exp (-8 / (n : ℝ) ^ 2 * t)) :
    ‖∫ t in Set.Ioi ((n : ℝ) ^ 2), f t‖ ≤ 8 * Real.pi ^ 2 * ((n : ℝ) ^ 4)⁻¹ := by
  have ha : -8 / (n : ℝ) ^ 2 < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hint := (integrableOn_exp_mul_Ioi ha ((n : ℝ) ^ 2)).const_mul
    (64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹)
  have h1 := norm_integral_le_of_norm_le hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hf t (le_of_lt ht))
  refine h1.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi ha]
  have e : -8 / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = -8 := by
    field_simp
  rw [e]
  have hexp : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have e2 : 64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹ * (-Real.exp (-8) / (-8 / (n : ℝ) ^ 2)) =
      8 * Real.pi ^ 2 * ((n : ℝ) ^ 4)⁻¹ * Real.exp (-8) := by
    field_simp
    ring
  rw [e2]
  have h3 : 0 ≤ 8 * Real.pi ^ 2 * ((n : ℝ) ^ 4)⁻¹ := by positivity
  nlinarith
theorem norm_integral_Ioi_of_cube_bound {g : ℝ → ℝ} {K : ℝ} {n : ℕ} (hn : 0 < n)
    (hg : ∀ t, (n : ℝ) ^ 2 ≤ t → |g t| ≤ K * t ^ (-3 : ℤ)) :
    ‖∫ t in Set.Ioi ((n : ℝ) ^ 2), g t‖ ≤ 1 / 2 * K * ((n : ℝ) ^ 4)⁻¹ := by
  have hc : 0 < (n : ℝ) ^ 2 := by positivity
  have hint := (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) hc).const_mul K
  have h1 := norm_integral_le_of_norm_le hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have h2 : (t : ℝ) ^ (-3 : ℝ) = t ^ (-3 : ℤ) := by
        simp
      rw [h2, Real.norm_eq_abs]
      exact hg t (le_of_lt ht))
  refine h1.trans ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
  have e : ((n : ℝ) ^ 2) ^ ((-3 : ℝ) + 1) = ((n : ℝ) ^ 4)⁻¹ := by
    rw [show ((-3 : ℝ) + 1) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg]
    norm_cast
    rw [← pow_mul]
  rw [e]
  apply le_of_eq
  norm_num
  ring
theorem hasDerivAt_neg_inv_sqrt_add_pow_five {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => -(2 / 5) * ((Real.sqrt x + a) ^ 5)⁻¹)
      ((Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hu := hs.add_const a
  have hp := hu.fun_pow 5
  have hne : (Real.sqrt t + a) ^ 5 ≠ 0 := by positivity
  have hi := hp.fun_inv hne
  have hc := hi.const_mul (-(2 / 5 : ℝ))
  refine hc.congr_deriv ?_
  norm_num
  field_simp
theorem intervalIntegrable_sqrt_weight {a N : ℝ} (ha : 0 < a) (hN : 1 ≤ N) :
    IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹)
      volume 1 N := by
  refine ContinuousOn.intervalIntegrable ?_
  intro t ht
  rw [Set.uIcc_of_le hN] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsc : ContinuousAt Real.sqrt t := Real.continuous_sqrt.continuousAt
  have hne : (Real.sqrt t + a) ^ 6 ≠ 0 := by positivity
  exact ((hsc.inv₀ hs0.ne').mul (((hsc.add continuousAt_const).pow 6).inv₀ hne)).continuousWithinAt
theorem integral_sqrt_weight_le {a N : ℝ} (ha : 0 < a) (hN : 1 ≤ N) :
    ∫ t in (1 : ℝ)..N, (Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹ ≤ 2 / 5 * (a ^ 5)⁻¹ := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
      rw [Set.uIcc_of_le hN] at ht
      exact hasDerivAt_neg_inv_sqrt_add_pow_five ha (by linarith [ht.1]))
    (intervalIntegrable_sqrt_weight ha hN)]
  have h1 : 0 ≤ ((Real.sqrt N + a) ^ 5)⁻¹ := by positivity
  have h2 : ((Real.sqrt 1 + a) ^ 5)⁻¹ ≤ (a ^ 5)⁻¹ := by
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le ?_ 5)
    have := Real.sqrt_nonneg 1
    linarith
  linarith
theorem rpow_mul_bracketOnePlus_eq {R t : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    t ^ (-(7 / 2) : ℝ) * bracketOnePlus (R / (2 * Real.sqrt t)) ^ (-6 : ℤ) =
      (Real.sqrt t)⁻¹ * ((Real.sqrt t + R / 2) ^ 6)⁻¹ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  set s : ℝ := Real.sqrt t with hsd
  have ht2 : t = s ^ 2 := (Real.sq_sqrt ht.le).symm
  have e1 : t ^ (-(7 / 2) : ℝ) = (s ^ 7)⁻¹ := by
    rw [ht2, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * (-(7 / 2)) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs.le,
      Real.rpow_natCast]
  have e2 : bracketOnePlus (R / (2 * s)) = (s + R / 2) / s := by
    unfold bracketOnePlus
    field_simp
  rw [e1, e2, zpow_neg, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast, div_pow]
  field_simp
theorem integral_Ioi_eq_three_pieces {h : ℝ → ℂ} (hh : IntegrableOn h (Set.Ioi 0)) {N : ℝ}
    (hN : 1 ≤ N) :
    ∫ t in Set.Ioi (0 : ℝ), h t =
      (∫ t in Set.Ioc (0 : ℝ) 1, h t) + (∫ t in Set.Ioc (1 : ℝ) N, h t) +
        ∫ t in Set.Ioi N, h t := by
  have e1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have e2 : Set.Ioi (1 : ℝ) = Set.Ioc 1 N ∪ Set.Ioi N := (Set.Ioc_union_Ioi_eq_Ioi hN).symm
  have h1 : IntegrableOn h (Set.Ioi 1) := hh.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h2 : IntegrableOn h (Set.Ioc 0 1) := hh.mono_set Set.Ioc_subset_Ioi_self
  have h3 : IntegrableOn h (Set.Ioc 1 N) := h1.mono_set Set.Ioc_subset_Ioi_self
  have h4 : IntegrableOn h (Set.Ioi N) := h1.mono_set (Set.Ioi_subset_Ioi hN)
  rw [e1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h2 h1,
    e2, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h3 h4]
  ring
theorem norm_integral_sub_integral_le {f : ℝ → ℂ} {g : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioi 0))
    (hg : IntegrableOn g (Set.Ioi 0)) {N a K A₁ c₂ A₃ A₄ : ℝ} (hN : 1 ≤ N) (ha : 0 < a)
    (hK : 0 ≤ K)
    (h₁ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖f t - (g t : ℂ)‖ ≤ A₁)
    (h₂ : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖f t - (g t : ℂ)‖ ≤
      K * ((Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹) + c₂)
    (h₃ : ‖∫ t in Set.Ioi N, f t‖ ≤ A₃) (h₄ : ‖∫ t in Set.Ioi N, g t‖ ≤ A₄) :
    ‖(∫ t in Set.Ioi (0 : ℝ), f t) - ((∫ t in Set.Ioi (0 : ℝ), g t : ℝ) : ℂ)‖ ≤
      A₁ + K * (2 / 5 * (a ^ 5)⁻¹) + c₂ * (N - 1) + A₃ + A₄ := by
  have hgc : IntegrableOn (fun t => (g t : ℂ)) (Set.Ioi 0) := hg.ofReal
  have hcast : ∀ s : Set ℝ, ((∫ t in s, g t : ℝ) : ℂ) = ∫ t in s, (g t : ℂ) :=
    fun s => integral_ofReal.symm
  rw [hcast, integral_Ioi_eq_three_pieces hf hN, integral_Ioi_eq_three_pieces hgc hN]
  have hf1 : IntegrableOn f (Set.Ioc 0 1) := hf.mono_set Set.Ioc_subset_Ioi_self
  have hg1 : IntegrableOn (fun t => (g t : ℂ)) (Set.Ioc 0 1) :=
    hgc.mono_set Set.Ioc_subset_Ioi_self
  have hsub : Set.Ioc (1 : ℝ) N ⊆ Set.Ioi 0 := fun t ht => lt_trans zero_lt_one ht.1
  have hf2 : IntegrableOn f (Set.Ioc 1 N) := hf.mono_set hsub
  have hg2 : IntegrableOn (fun t => (g t : ℂ)) (Set.Ioc 1 N) := hgc.mono_set hsub
  have b1 : ‖∫ t in Set.Ioc (0 : ℝ) 1, (f t - (g t : ℂ))‖ ≤ A₁ := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
      (f := fun t => f t - (g t : ℂ)) (C := A₁) (by simp) h₁
    simpa using this
  have hbi : IntervalIntegrable
      (fun t : ℝ => K * ((Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹) + c₂) volume 1 N :=
    ((intervalIntegrable_sqrt_weight ha hN).const_mul K).add intervalIntegrable_const
  have b2 : ‖∫ t in Set.Ioc (1 : ℝ) N, (f t - (g t : ℂ))‖ ≤
      K * (2 / 5 * (a ^ 5)⁻¹) + c₂ * (N - 1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 1) (b := N)
      (f := fun t => f t - (g t : ℂ)) hN (Filter.Eventually.of_forall h₂) hbi
    rw [intervalIntegral.integral_of_le hN] at h
    refine h.trans ?_
    rw [intervalIntegral.integral_add ((intervalIntegrable_sqrt_weight ha hN).const_mul K)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    have := mul_le_mul_of_nonneg_left (integral_sqrt_weight_le ha hN) hK
    nlinarith
  have b4 : ‖∫ t in Set.Ioi N, (g t : ℂ)‖ ≤ A₄ := by
    rw [← hcast, Complex.norm_real]
    exact h₄
  have e : ((∫ t in Set.Ioc (0 : ℝ) 1, f t) + (∫ t in Set.Ioc (1 : ℝ) N, f t) +
        ∫ t in Set.Ioi N, f t) -
      ((∫ t in Set.Ioc (0 : ℝ) 1, (g t : ℂ)) + (∫ t in Set.Ioc (1 : ℝ) N, (g t : ℂ)) +
        ∫ t in Set.Ioi N, (g t : ℂ)) =
      (∫ t in Set.Ioc (0 : ℝ) 1, (f t - (g t : ℂ))) +
        (∫ t in Set.Ioc (1 : ℝ) N, (f t - (g t : ℂ))) +
        (∫ t in Set.Ioi N, f t) - ∫ t in Set.Ioi N, (g t : ℂ) := by
    rw [integral_sub hf1 hg1, integral_sub hf2 hg2]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add₃_le (a := ∫ t in Set.Ioc (0 : ℝ) 1, (f t - (g t : ℂ)))
    (b := ∫ t in Set.Ioc (1 : ℝ) N, (f t - (g t : ℂ))) (c := ∫ t in Set.Ioi N, f t)
  linarith
theorem fieldConstant_toReal (hC : gaussianComparison 6 ≠ ⊤) :
    fieldConstant.toReal =
      (15 + 10368 + 1024 * 257 ^ 3) * (gaussianComparison 6).toReal + 8 * Real.pi ^ 2 +
        1 / 2 * lowerDiagonalConstant := by
  have hld : 0 ≤ lowerDiagonalConstant := by
    unfold lowerDiagonalConstant
    positivity
  have hcoef : (15 + 10368 + 1024 * 257 ^ 3 : ENNReal) =
      ((15 + 10368 + 1024 * 257 ^ 3 : ℕ) : ENNReal) := by
    norm_num
  unfold fieldConstant
  rw [hcoef, ENNReal.toReal_add (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  push_cast
  ring
theorem torusGreenSecondDiffBound_holds
    (hH : YangMills.Construction.FreeKernel.HeatKernelGreen.HeatKernelGreenProperties)
    (hN : YangMills.Construction.Constants.HeatKernel.finite_and_pos)
    (hT : YangMills.Construction.PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement) :
    YangMills.Construction.FreeKernel.TorusGreenSecondDiffBound := by
  obtain ⟨-, -, -, hLd, -, -, -, -, -, -, hC, hPhi, -⟩ := hN
  refine ⟨hPhi.1, ?_⟩
  intro n hn ν ν' c hc0 hc1 z hz1 hz2
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨hn0.ne'⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨hP, hTI, hCI, hB, hD⟩ := hH n hn ν ν'
  obtain ⟨hM, hS, -, -, -⟩ := hT n hn
  obtain ⟨hSh, hLo⟩ := hB 6
  simp only [ShortTimeBounds, LongTimeBounds, Nat.cast_ofNat] at hSh hLo
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h := intVecNorm_sq 0
    simp only [Pi.zero_apply, Int.cast_zero] at h
    norm_num at h
    rw [h] at hz1
    norm_num at hz1
  have hrv : castVec z ≠ 0 := by
    intro h
    refine hz0 (funext fun μ => ?_)
    have := congrFun h μ
    simpa using this
  have hC0 : 0 ≤ (gaussianComparison 6).toReal := ENNReal.toReal_nonneg
  set C : ℝ := (gaussianComparison 6).toReal with hCd
  set R : ℝ := intVecNorm z with hRd
  have hRn : R < (n : ℝ) / 2 := by nlinarith
  have hR0 : 0 < R := by linarith
  have hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2 := fun μ => (abs_coord_le_intVecNorm z μ).trans hRn.le
  obtain ⟨hfI, hfE⟩ := (hTI z).2
  obtain ⟨hgI, hgE⟩ := (hCI (castVec z) hrv).2
  rw [hfE, show mixedSecondPartial ν ν' continuumGreenFunction (fun μ => (z μ : ℝ)) =
    ∫ t in Set.Ioi (0 : ℝ), mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z)
    from hgE.symm]
  have hsum : ∀ t, 0 < t → HasSum
      (fun w : Fin 4 → ℤ => mixedSecondDiff ν ν' (latticeHeatKernel4 t) (z + (n : ℤ) • w))
      (mixedSecondDiff ν ν' (torusHeatKernel n t) z) := fun t ht =>
    hasSum_mixedSecondDiff_translates n (fun x => (hP t ht).2.2.2 x) ν ν' z
  have hone : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z -
          ((mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z) : ℝ) : ℂ)‖ ≤
        2 * C * (R ^ 5)⁻¹ + 10368 * C * ((n : ℝ) ^ 6)⁻¹ := by
    rintro t ⟨ht0, ht1⟩
    have hA := norm_sub_term_le_of_hasSum (hsum t ht0) 0 (fun S h0 =>
      shortTime_images_sum_le hC0 hn0 hz (fun w => (hSh _ t ht0 ht1).1) S h0)
    simp only [smul_zero, add_zero] at hA
    have hB1 := (hSh z t ht0 ht1).1
    have hB2 := (hSh z t ht0 ht1).2 hz0
    have hR6 : bracketOnePlus R ^ (-6 : ℤ) ≤ (R ^ 5)⁻¹ := by
      refine (bracketOnePlus_zpow_le_inv_pow (y := R) hR0 le_rfl).trans
        (inv_anti₀ (by positivity) ?_)
      exact pow_le_pow_right₀ hz1 (by norm_num)
    have hB3 := mul_le_mul_of_nonneg_left hR6 hC0
    set F₀ := mixedSecondDiff ν ν' (latticeHeatKernel4 t) z
    set G := mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z)
    have e : mixedSecondDiff ν ν' (torusHeatKernel n t) z - (G : ℂ) =
        (mixedSecondDiff ν ν' (torusHeatKernel n t) z - F₀) + (F₀ - (G : ℂ)) := by ring
    rw [e]
    have h1 : ‖F₀ - (G : ℂ)‖ ≤ ‖F₀‖ + ‖(G : ℂ)‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 := norm_add_le (mixedSecondDiff ν ν' (torusHeatKernel n t) z - F₀) (F₀ - (G : ℂ))
    linarith
  have htwo : ∀ t ∈ Set.Ioc (1 : ℝ) ((n : ℝ) ^ 2),
      ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z -
          ((mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z) : ℝ) : ℂ)‖ ≤
        C * ((Real.sqrt t)⁻¹ * ((Real.sqrt t + R / 2) ^ 6)⁻¹) +
          1024 * 257 ^ 3 * C * ((n : ℝ) ^ 6)⁻¹ := by
    rintro t ⟨ht1, htn⟩
    have ht0 : 0 < t := by linarith
    have hA := norm_sub_term_le_of_hasSum (hsum t ht0) 0 (fun S h0 =>
      longTime_images_sum_le hC0 hn0 ht0 htn hz (fun w => (hLo _ t ht1.le).1) S h0)
    simp only [smul_zero, add_zero] at hA
    have hB1 := (hLo z t ht1.le).2.2
    rw [mul_assoc, rpow_mul_bracketOnePlus_eq ht0 hR0.le] at hB1
    have h2 := norm_add_le
      (mixedSecondDiff ν ν' (torusHeatKernel n t) z -
        mixedSecondDiff ν ν' (latticeHeatKernel4 t) z)
      (mixedSecondDiff ν ν' (latticeHeatKernel4 t) z -
        ((mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z) : ℝ) : ℂ))
    rw [sub_add_sub_cancel] at h2
    linarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have main := norm_integral_sub_integral_le hfI hgI hn2 (a := R / 2) (by linarith) hC0 hone htwo
    (norm_integral_Ioi_of_exp_bound hn0 fun t ht =>
      torusHeatKernel_mixedSecondDiff_decay hn0 hM hS ht ν ν' z)
    (norm_integral_Ioi_of_cube_bound (K := lowerDiagonalConstant) hn0 fun t ht => by
      refine hD t (castVec z) (by nlinarith) ?_
      have h : realVecNorm (castVec z) = R := rfl
      rw [h]
      nlinarith)
  refine main.trans ?_
  rw [fieldConstant_toReal (hC 6).1, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  set X : ℝ := (R ^ 5)⁻¹ with hX
  set Y : ℝ := ((n : ℝ) ^ 4)⁻¹ with hY
  set W : ℝ := ((n : ℝ) ^ 6)⁻¹ with hW
  have hW0 : 0 ≤ W := by positivity
  have e1 : ((R / 2) ^ 5)⁻¹ = 32 * X := by
    rw [hX]
    field_simp
    norm_num
  have e2 : W * (n : ℝ) ^ 2 = Y := by
    rw [hW, hY]
    field_simp
  have hWY : W ≤ Y := by
    rw [← e2]
    nlinarith
  rw [e1]
  have h1 : 0 ≤ C * X := by positivity
  have h2 : 0 ≤ C * Y := by positivity
  have h4 : 0 ≤ C * W := by positivity
  have h5 : C * W * (n : ℝ) ^ 2 = C * Y := by rw [← e2]; ring
  have h6 : 0 ≤ Real.pi ^ 2 * X := by positivity
  have h7 : 0 ≤ lowerDiagonalConstant * X := by positivity
  nlinarith
end YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof
end
