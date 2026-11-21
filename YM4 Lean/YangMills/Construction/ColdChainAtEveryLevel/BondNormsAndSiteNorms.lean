import YangMills.Construction.ColdChainAtEveryLevel.FormsInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BondSiteNorms
variable {F : BlockAverages.BlockFrame} {S : Finset F.Cell}
theorem sum_bondsOver_singleton (z : F.Cell) (g : F.Site 0 × Fin 4 → ℝ) :
    ∑ b ∈ BlockAverages.bondsOver S {z} 0, g b =
      ∑ x ∈ BlockAverages.cellSites S z, ∑ i,
        if (x, i) ∈ BlockAverages.innerBonds S 0 then g (x, i) else 0 := by
  classical
  have hset : BlockAverages.bondsOver S {z} 0 =
      (BlockAverages.cellSites S z ×ˢ Finset.univ).filter (fun b => b ∈ BlockAverages.innerBonds S 0) := by
    ext b
    constructor
    · intro hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
      have hb3 : b.1 ∈ BlockAverages.sitesOfCells S 0 :=
        (Finset.mem_product.1 (Finset.mem_filter.1 hb1).1).1
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hb3, Finset.mem_singleton.1 hb2⟩,
        Finset.mem_univ _⟩, hb1⟩
    · intro hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
      have hb3 := (Finset.mem_filter.1 (Finset.mem_product.1 hb1).1).2
      exact Finset.mem_filter.2 ⟨hb2, Finset.mem_singleton.2 hb3⟩
  rw [hset, Finset.sum_filter, Finset.sum_product]
theorem formNormOn_nonneg_at (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) :
    0 ≤ PatchDifferences.formNormOn S f t := by apply _root_.YangMills.Construction.PatchDifferences.formNormOn_nonneg <;> assumption
theorem norm_le_formNormOn (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {t : F.Site 0} {i : Fin 4}
    (hti : (t, i) ∈ BlockAverages.innerBonds S 0) :
    ‖f t i‖ ≤ PatchDifferences.formNormOn S f t := by apply _root_.YangMills.Construction.PatchForms.norm_le_formNormOn <;> assumption
variable {p : ℝ} {w : F.Site 0 → ℝ}
theorem cellBondNorm_le (hp : 1 ≤ p) (hw : ∀ x, 0 ≤ w x) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    BlockAverages.cellBondNorm p S w f z ≤
      4 * BlockAverages.weightedLpNormOnCell p S w (PatchDifferences.formNormOn S f) z := by
  classical
  have hp0 : 0 < p := by linarith
  have hsum : ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p ≤
      4 * ∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p := by
    rw [sum_bondsOver_singleton z (fun b => (w b.1 * ‖f b.1 b.2‖) ^ p), Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hterm : ∀ i : Fin 4, (if (x, i) ∈ BlockAverages.innerBonds S 0 then (w x * ‖f x i‖) ^ p else 0) ≤
        |w x * PatchDifferences.formNormOn S f x| ^ p := by
      intro i
      split_ifs with hxi
      · refine Real.rpow_le_rpow (mul_nonneg (hw x) (norm_nonneg _)) ?_ hp0.le
        rw [abs_of_nonneg (mul_nonneg (hw x) (formNormOn_nonneg_at f x))]
        exact mul_le_mul_of_nonneg_left (norm_le_formNormOn f hxi) (hw x)
      · exact Real.rpow_nonneg (abs_nonneg _) _
    calc _ ≤ ∑ _i : Fin 4, |w x * PatchDifferences.formNormOn S f x| ^ p :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  have hbond0 : 0 ≤ ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p :=
    Finset.sum_nonneg fun b _ => Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _
  have hsite0 : 0 ≤ ∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _
  have hinv : 1 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hp
  have hinv0 : 0 ≤ 1 / p := by positivity
  unfold BlockAverages.cellBondNorm BlockAverages.weightedLpNormOnCell
  calc _ ≤ (4 * ∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow hbond0 hsum hinv0
    _ = (4 : ℝ) ^ (1 / p) *
          (∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p) ^ (1 / p) :=
        Real.mul_rpow (by norm_num) hsite0
    _ ≤ 4 * (∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p) ^ (1 / p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hsite0 _)
        calc (4 : ℝ) ^ (1 / p) ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
          _ = 4 := Real.rpow_one _
theorem weightedLpNormOnCell_formNormOn_le (hp : 1 ≤ p) (hw : ∀ x, 0 ≤ w x) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (z : F.Cell) :
    BlockAverages.weightedLpNormOnCell p S w (PatchDifferences.formNormOn S f) z ≤
      4 * BlockAverages.cellBondNorm p S w f z := by
  classical
  have hp0 : 0 < p := by linarith
  have hsum : ∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p ≤
      (4 : ℝ) ^ p * ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p := by
    rw [sum_bondsOver_singleton z (fun b => (w b.1 * ‖f b.1 b.2‖) ^ p), Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    set c : Fin 4 → ℝ := fun i => if (x, i) ∈ BlockAverages.innerBonds S 0 then w x * ‖f x i‖ else 0 with hc
    have hc0 : ∀ i, 0 ≤ c i := by
      intro i
      simp only [hc]
      split_ifs
      · exact mul_nonneg (hw x) (norm_nonneg _)
      · exact le_refl _
    have hform : w x * PatchDifferences.formNormOn S f x = ∑ i, c i := by
      simp only [PatchDifferences.formNormOn, Finset.mul_sum, hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · rfl
      · simp
    obtain ⟨imax, -, himax⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
    have hmax : ∑ i, c i ≤ 4 * c imax := by
      calc ∑ i, c i ≤ ∑ _i : Fin 4, c imax := Finset.sum_le_sum fun i hi => himax i hi
        _ = _ := by simp
    have hcsum0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc0 i
    have hsingle : (c imax) ^ p ≤
        ∑ i, if (x, i) ∈ BlockAverages.innerBonds S 0 then (w x * ‖f x i‖) ^ p else 0 := by
      have hpow : (c imax) ^ p =
          if (x, imax) ∈ BlockAverages.innerBonds S 0 then (w x * ‖f x imax‖) ^ p else 0 := by
        simp only [hc]
        split_ifs
        · rfl
        · exact Real.zero_rpow hp0.ne'
      rw [hpow]
      refine Finset.single_le_sum
        (f := fun i => if (x, i) ∈ BlockAverages.innerBonds S 0 then (w x * ‖f x i‖) ^ p else 0)
        (fun i _ => ?_) (Finset.mem_univ imax)
      show 0 ≤ if (x, i) ∈ BlockAverages.innerBonds S 0 then (w x * ‖f x i‖) ^ p else 0
      split_ifs
      · exact Real.rpow_nonneg (mul_nonneg (hw x) (norm_nonneg _)) _
      · exact le_refl _
    rw [hform, abs_of_nonneg hcsum0]
    calc (∑ i, c i) ^ p ≤ (4 * c imax) ^ p := Real.rpow_le_rpow hcsum0 hmax hp0.le
      _ = (4 : ℝ) ^ p * (c imax) ^ p := Real.mul_rpow (by norm_num) (hc0 imax)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (by positivity)
  have hsite0 : 0 ≤ ∑ x ∈ BlockAverages.cellSites S z, |w x * PatchDifferences.formNormOn S f x| ^ p :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _
  have hbond0 : 0 ≤ ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p :=
    Finset.sum_nonneg fun b _ => Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _
  unfold BlockAverages.cellBondNorm BlockAverages.weightedLpNormOnCell
  calc _ ≤ ((4 : ℝ) ^ p * ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow hsite0 hsum (by positivity)
    _ = ((4 : ℝ) ^ p) ^ (1 / p) *
          (∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ p) ^ (1 / p) :=
        Real.mul_rpow (by positivity) hbond0
    _ = _ := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hp0.ne', Real.rpow_one]
theorem cellSiteNorm_eq (hw : ∀ x, 0 ≤ w x) (ξ : F.Site 0 → ℍ[ℝ]) (z : F.Cell) :
    BlockAverages.cellSiteNorm p S w ξ z =
      BlockAverages.weightedLpNormOnCell p S w (PatchDifferences.sectionNormOn S ξ) z := by
  classical
  unfold BlockAverages.cellSiteNorm BlockAverages.weightedLpNormOnCell
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxs : x ∈ BlockAverages.sitesOfCells S 0 := (Finset.mem_filter.1 hx).1
  simp only [PatchDifferences.sectionNormOn, if_pos hxs]
  rw [abs_of_nonneg (mul_nonneg (hw x) (norm_nonneg _))]
theorem cellwiseL4Norm_eq (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    BlockAverages.cellwiseL4Norm S w f =
      Real.sqrt (∑ z ∈ S, BlockAverages.cellBondNorm 4 S w f z ^ 2) := by
  unfold BlockAverages.cellwiseL4Norm
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold BlockAverages.cellBondNorm
  have hnat : ∀ t : ℝ, t ^ (4 : ℝ) = t ^ 4 := fun t => by
    rw [← Real.rpow_natCast]
    norm_num
  simp only [hnat]
  have hsum0 : 0 ≤ ∑ b ∈ BlockAverages.bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hsum0]
  norm_num
theorem mem_cellBall_iff {z y : F.Cell} {r : ℕ} :
    y ∈ BlockAverages.cellBall S z r ↔ y ∈ S ∧ BlockAverages.cellSupDist z y ≤ r := by
  classical
  exact Finset.mem_filter
theorem sum_sq_le_of_le_sum_cellBall (hamb : BlockAverages.IsAdmissibleAmbient F) (a b : F.Cell → ℝ)
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z₀ ∈ S, a z₀ ≤ C * ∑ y ∈ BlockAverages.cellBall S z₀ 22, b y) :
    ∑ z ∈ S, a z ^ 2 ≤ (C * 45 ^ 4) ^ 2 * ∑ z ∈ S, b z ^ 2 := by
  have hcard : ∀ z : F.Cell, ((BlockAverages.cellBall S z 22).card : ℝ) ≤ 45 ^ 4 := by
    intro z
    have hnat := PatchDifferences.card_le_of_cellSupDist_le hamb z 22 (BlockAverages.cellBall S z 22)
      fun y hy => (mem_cellBall_iff.1 hy).2
    have hreal : ((BlockAverages.cellBall S z 22).card : ℝ) ≤ (((2 * 22 + 1) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    norm_num at hreal ⊢
    exact hreal
  have hpoint : ∀ z ∈ S, a z ^ 2 ≤ (C ^ 2 * 45 ^ 4) * ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2 := by
    intro z hz
    have hz' := h z hz
    have hb0 : 0 ≤ ∑ y ∈ BlockAverages.cellBall S z 22, b y := Finset.sum_nonneg fun y _ => hb y
    have hcs : (∑ y ∈ BlockAverages.cellBall S z 22, b y) ^ 2 ≤
        (BlockAverages.cellBall S z 22).card * ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsq0 : 0 ≤ ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
    calc a z ^ 2 ≤ (C * ∑ y ∈ BlockAverages.cellBall S z 22, b y) ^ 2 := pow_le_pow_left₀ (ha z) hz' 2
      _ = C ^ 2 * (∑ y ∈ BlockAverages.cellBall S z 22, b y) ^ 2 := by ring
      _ ≤ C ^ 2 * ((45 ^ 4) * ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2) := by
          refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (sq_nonneg C)
          exact mul_le_mul_of_nonneg_right (hcard z) hsq0
      _ = _ := by ring
  have hswap : ∑ z ∈ S, ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2 =
      ∑ y ∈ S, ∑ _z ∈ BlockAverages.cellBall S y 22, b y ^ 2 :=
    Finset.sum_comm' fun z y => by
      rw [mem_cellBall_iff, mem_cellBall_iff, PatchPoints.cellSupDist_symm]
      tauto
  have hcount : ∑ y ∈ S, ∑ _z ∈ BlockAverages.cellBall S y 22, b y ^ 2 ≤ 45 ^ 4 * ∑ y ∈ S, b y ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcard y) (sq_nonneg _)
  calc ∑ z ∈ S, a z ^ 2 ≤ ∑ z ∈ S, (C ^ 2 * 45 ^ 4) * ∑ y ∈ BlockAverages.cellBall S z 22, b y ^ 2 :=
        Finset.sum_le_sum hpoint
    _ = (C ^ 2 * 45 ^ 4) * ∑ y ∈ S, ∑ _z ∈ BlockAverages.cellBall S y 22, b y ^ 2 := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ (C ^ 2 * 45 ^ 4) * (45 ^ 4 * ∑ y ∈ S, b y ^ 2) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring
end YangMills.Construction.BondSiteNorms
end
