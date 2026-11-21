import YangMills.Construction.ColdChainAtEveryLevel.BoundOfTheGluedFirstOrders
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open PatchLocality ChartCoordinates PartitionGluing GluedFirstOrderData EvaluationSums
variable {F : BlockFrame} {S : Finset F.Cell} {A : Finset F.Cell}
theorem sum_sum_cellsNearTerm_comm (T : Finset F.ActionTerm) {A' : Finset F.Cell}
    (hsub : ∀ t ∈ T, cellsNearTerm A t ⊆ A') (f : F.Cell → F.ActionTerm → ℝ) :
    ∑ t ∈ T, ∑ z ∈ cellsNearTerm A t, f z t = ∑ z ∈ A', ∑ t ∈ T with z ∈ cellsNearTerm A t, f z t := by
  classical
  refine Finset.sum_comm' fun t z => ?_
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, hsub t h1 h2⟩
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1, h2⟩
theorem cellSupDist_le_of_mem_cellsNearTerm {z : F.Cell} {t : F.ActionTerm} (h : z ∈ cellsNearTerm A t) :
    cellSupDist z (actionTermCell t) ≤ 4 := by
  classical
  exact (Finset.mem_filter.1 h).2
theorem sum_cellsNearTerm_le_sum_actionTermsNear (T : Finset F.ActionTerm) (hT : T ⊆ actionTerms S)
    {A' : Finset F.Cell} (hsub : ∀ t ∈ T, cellsNearTerm A t ⊆ A')
    (f : F.Cell → F.ActionTerm → ℝ) (hf : ∀ z t, 0 ≤ f z t) :
    ∑ t ∈ T, ∑ z ∈ cellsNearTerm A t, f z t ≤ ∑ z ∈ A', ∑ t ∈ actionTermsNear S {z}, f z t := by
  classical
  rw [sum_sum_cellsNearTerm_comm T hsub]
  refine Finset.sum_le_sum fun z _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => hf z t
  have h1 := Finset.mem_filter.1 ht
  refine Finset.mem_filter.2 ⟨hT h1.1, fun w hw => ?_⟩
  rw [Finset.mem_singleton.1 hw]
  exact cellSupDist_le_of_mem_cellsNearTerm h1.2
theorem sum_cellsNearTerm_pair_le (T : Finset F.ActionTerm) (hT : T ⊆ actionTerms S) {A' : Finset F.Cell}
    (hsub : ∀ t ∈ T, cellsNearTerm A t ⊆ A')
    (f : F.Cell → F.Cell → F.ActionTerm → ℝ) (hf : ∀ z z₀ t, 0 ≤ f z z₀ t) :
    ∑ t ∈ T, ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, f z z₀ t ≤
      ∑ z₀ ∈ A', ∑ z ∈ A, ∑ t ∈ actionTermsNear S {z, z₀}, f z z₀ t := by
  classical
  rw [sum_sum_cellsNearTerm_comm T hsub]
  refine Finset.sum_le_sum fun z₀ _ => ?_
  rw [sum_sum_cellsNearTerm_comm (A' := A) _ fun t _ => Finset.filter_subset _ _]
  refine Finset.sum_le_sum fun z _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => hf z z₀ t
  have h1 := Finset.mem_filter.1 ht
  have h2 := Finset.mem_filter.1 h1.1
  refine Finset.mem_filter.2 ⟨hT h2.1, fun w hw => ?_⟩
  rcases Finset.mem_insert.1 hw with rfl | hw
  · exact cellSupDist_le_of_mem_cellsNearTerm h1.2
  · rw [Finset.mem_singleton.1 hw]
    exact cellSupDist_le_of_mem_cellsNearTerm h2.2
theorem sum_cellsNearTerm_triple_le (T : Finset F.ActionTerm) (hT : T ⊆ actionTerms S)
    (f : F.Cell → F.Cell → F.Cell → F.ActionTerm → ℝ) (hf : ∀ z z₀ z₁ t, 0 ≤ f z z₀ z₁ t) :
    ∑ t ∈ T, ∑ z₁ ∈ cellsNearTerm A t, ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, f z z₀ z₁ t ≤
      ∑ z₁ ∈ A, ∑ z₀ ∈ A, ∑ z ∈ A, ∑ t ∈ actionTermsNear S {z, z₀, z₁}, f z z₀ z₁ t := by
  classical
  rw [sum_sum_cellsNearTerm_comm (A' := A) T fun t _ => Finset.filter_subset _ _]
  refine Finset.sum_le_sum fun z₁ _ => ?_
  rw [sum_sum_cellsNearTerm_comm (A' := A) _ fun t _ => Finset.filter_subset _ _]
  refine Finset.sum_le_sum fun z₀ _ => ?_
  rw [sum_sum_cellsNearTerm_comm (A' := A) _ fun t _ => Finset.filter_subset _ _]
  refine Finset.sum_le_sum fun z _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => hf z z₀ z₁ t
  have h1 := Finset.mem_filter.1 ht
  have h2 := Finset.mem_filter.1 h1.1
  have h3 := Finset.mem_filter.1 h2.1
  refine Finset.mem_filter.2 ⟨hT h3.1, fun w hw => ?_⟩
  rcases Finset.mem_insert.1 hw with rfl | hw
  · exact cellSupDist_le_of_mem_cellsNearTerm h1.2
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact cellSupDist_le_of_mem_cellsNearTerm h2.2
    · rw [Finset.mem_singleton.1 hw]
      exact cellSupDist_le_of_mem_cellsNearTerm h3.2
theorem cellSupDist_le_of_mem_actionTermsNear {Zs : Finset F.Cell} {t : F.ActionTerm}
    (ht : t ∈ actionTermsNear S Zs) {z z' : F.Cell} (hz : z ∈ Zs) (hz' : z' ∈ Zs) :
    cellSupDist z z' ≤ 8 := by
  classical
  have h1 := (Finset.mem_filter.1 ht).2 z hz
  have h2 := (Finset.mem_filter.1 ht).2 z' hz'
  have h3 := cellSupDist_triangle z (actionTermCell t) z'
  rw [cellSupDist_comm (actionTermCell t) z'] at h3
  omega
def neighbourIndicator (z w : F.Cell) : ℝ := if cellSupDist z w ≤ 8 then 1 else 0
theorem neighbourIndicator_nonneg (z w : F.Cell) : 0 ≤ neighbourIndicator z w := by
  unfold neighbourIndicator
  split_ifs <;> norm_num
theorem neighbourIndicator_comm (z w : F.Cell) : neighbourIndicator z w = neighbourIndicator w z := by
  unfold neighbourIndicator
  rw [cellSupDist_comm]
theorem sum_neighbourIndicator_le (A : Finset F.Cell) (w : F.Cell) : ∑ z ∈ A, neighbourIndicator z w ≤ 17 ^ 4 := by
  classical
  unfold neighbourIndicator
  rw [← Finset.sum_filter]
  have h := card_le_of_cellSupDist_le w 8 (A.filter fun z => cellSupDist z w ≤ 8)
    fun z hz => (Finset.mem_filter.1 hz).2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have : ((A.filter fun z => cellSupDist z w ≤ 8).card : ℝ) ≤ ((2 * 8 + 1) ^ 4 : ℕ) := by exact_mod_cast h
  refine this.trans (le_of_eq ?_)
  norm_num
theorem sum_sum_neighbourIndicator_mul_le {D : F.Cell → ℝ} (hD : ∀ z ∈ A, 0 ≤ D z) :
    ∑ w ∈ A, ∑ z ∈ A, neighbourIndicator z w * D z ≤ 17 ^ 4 * ∑ z ∈ A, D z := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hD z hz)
  simp only [neighbourIndicator_comm z]
  exact sum_neighbourIndicator_le A z
theorem sum_pair_energy_le {D : F.Cell → ℝ} (hD : ∀ z ∈ A, 0 ≤ D z) :
    ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z z₀ * (D z + D z₀) ≤ 2 * 17 ^ 4 * ∑ z ∈ A, D z := by
  have h1 := sum_sum_neighbourIndicator_mul_le hD
  have h2 : ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z z₀ * D z₀ ≤ 17 ^ 4 * ∑ z ∈ A, D z := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_neighbourIndicator_le A w) (hD w hw)
  simp only [mul_add, Finset.sum_add_distrib]
  linarith
theorem sum_triple_energy_le {D : F.Cell → ℝ} (hD : ∀ z ∈ A, 0 ≤ D z) :
    ∑ z₁ ∈ A, ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z z₁ * neighbourIndicator z₀ z₁ * (D z + 2 * D z₁ + D z₀) ≤
      4 * (17 ^ 4) ^ 2 * ∑ z ∈ A, D z := by
  have key : ∀ w ∈ A, ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z w * neighbourIndicator z₀ w * (D z + 2 * D w + D z₀) ≤
      2 * 17 ^ 4 * ∑ z ∈ A, neighbourIndicator z w * D z + 2 * (17 ^ 4) ^ 2 * D w := by
    intro w hw
    set c := ∑ z ∈ A, neighbourIndicator z w with hc
    set T := ∑ z ∈ A, neighbourIndicator z w * D z with hT
    have hc0 : 0 ≤ c := Finset.sum_nonneg fun z _ => neighbourIndicator_nonneg z w
    have hc1 : c ≤ 17 ^ 4 := sum_neighbourIndicator_le A w
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun z hz => mul_nonneg (neighbourIndicator_nonneg z w) (hD z hz)
    have e : ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z w * neighbourIndicator z₀ w * (D z + 2 * D w + D z₀) =
        2 * (c * T) + 2 * D w * c ^ 2 := by
      have e1 : ∀ z₀ z, neighbourIndicator z w * neighbourIndicator z₀ w * (D z + 2 * D w + D z₀) =
          (neighbourIndicator z w * D z) * neighbourIndicator z₀ w +
            2 * D w * (neighbourIndicator z w * neighbourIndicator z₀ w) +
            neighbourIndicator z w * (neighbourIndicator z₀ w * D z₀) := by
        intro z₀ z
        ring
      simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hc, ← hT]
      ring
    rw [e]
    have hDw := hD w hw
    have h1 : c * T ≤ 17 ^ 4 * T := mul_le_mul_of_nonneg_right hc1 hT0
    have h2 : c ^ 2 ≤ (17 ^ 4) ^ 2 := pow_le_pow_left₀ hc0 hc1 2
    have h3 : 2 * D w * c ^ 2 ≤ 2 * D w * (17 ^ 4) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  refine (Finset.sum_le_sum key).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_sum_neighbourIndicator_mul_le hD
  have h2 : (0 : ℝ) ≤ 2 * 17 ^ 4 := by norm_num
  have := mul_le_mul_of_nonneg_left h1 h2
  nlinarith
theorem sqrt_add_sqrt_le_two_mul_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √x + √y ≤ 2 * √(x + y) := by
  have h1 : √x ≤ √(x + y) := Real.sqrt_le_sqrt (by linarith)
  have h2 : √y ≤ √(x + y) := Real.sqrt_le_sqrt (by linarith)
  linarith
variable {a C C₂ Cd e0 K ρ : ℝ} {Bd : Finset F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
  {k : F.SiteGauge} {Γ : F.Cell → F.SiteGauge} {D : F.Cell → ℝ}
namespace GluedFirstOrderData
variable (h : GluedFirstOrderData a C C₂ Cd e0 K ρ S A Bd W kW X k Γ D)
include h
theorem sum_actionTermsNear_eq_zero {Zs : Finset F.Cell} {z z' : F.Cell} (hz : z ∈ Zs) (hz' : z' ∈ Zs)
    (hd : ¬ cellSupDist z z' ≤ 8) (f : F.ActionTerm → ℝ) : ∑ t ∈ actionTermsNear S Zs, f t = 0 := by
  refine Finset.sum_eq_zero fun t ht => ?_
  exact absurd (cellSupDist_le_of_mem_actionTermsNear ht hz hz') hd
theorem sum_second_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW (fun u => changeWeight W kW (Γ z) (Γ z₀) u *
        (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u))) t ≤
      nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
        (neighbourIndicator z z₀ * (D z + D z₀)) := by
  have hM := nearSumConstant_nonneg (F := F) h
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  by_cases hd : cellSupDist z z₀ ≤ 8
  · have e1 := h.sum_farPart_second_le hz hz₀ (hd.trans (by norm_num))
    refine e1.trans ?_
    have hnb : neighbourIndicator z z₀ = 1 := by simp [neighbourIndicator, hd]
    rw [hnb, one_mul]
    have hx := h.energy_nonneg z hz
    have hy := h.energy_nonneg z₀ hz₀
    set r := √(D z + D z₀) with hr
    have hr2 : r * r = D z + D z₀ := Real.mul_self_sqrt (by linarith)
    have hs := sqrt_add_sqrt_le_two_mul_sqrt hx hy
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have e2 : nearSumConstant F K * ((51 * (C₂ * r)) * (2 * (2 * (defectConstant F.blockSide * (C * √(D z)) +
        defectConstant F.blockSide * (C * √(D z₀)))))) =
        nearSumConstant F K * (204 * C₂ * defectConstant F.blockSide * C) * (r * (√(D z) + √(D z₀))) := by ring
    rw [e2, ← hr2]
    have hc' : 0 ≤ nearSumConstant F K * (204 * C₂ * defectConstant F.blockSide * C) :=
      mul_nonneg hM (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.changeConst_nonneg) hcG) h.pinConst_nonneg)
    have : r * (√(D z) + √(D z₀)) ≤ r * (2 * r) := mul_le_mul_of_nonneg_left hs hr0
    calc _ ≤ nearSumConstant F K * (204 * C₂ * defectConstant F.blockSide * C) * (r * (2 * r)) :=
          mul_le_mul_of_nonneg_left this hc'
      _ = _ := by ring
  · rw [h.sum_actionTermsNear_eq_zero (z := z) (z' := z₀) (by simp) (by simp) hd]
    have hnb : neighbourIndicator z z₀ = 0 := by simp [neighbourIndicator, hd]
    rw [hnb]
    simp
theorem sum_third_le {z z₀ z₁ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (hz₁ : z₁ ∈ A) :
    ∑ t ∈ actionTermsNear S {z, z₀, z₁}, farContribution a W kW
        (fun u => targetChange (Γ z₁) (Γ z₀) u * scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u) t ≤
      nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) *
        (neighbourIndicator z z₁ * neighbourIndicator z₀ z₁ * (D z + 2 * D z₁ + D z₀)) := by
  have hM := nearSumConstant_nonneg (F := F) h
  have hc : 0 ≤ nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) :=
    mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) partitionBound_pos.le) (sq_nonneg _))
  by_cases hd : cellSupDist z z₁ ≤ 8
  · by_cases hd' : cellSupDist z₀ z₁ ≤ 8
    · have hd2 : cellSupDist z₁ z₀ ≤ 40 := by rw [cellSupDist_comm]; exact hd'.trans (by norm_num)
      have e1 := h.sum_farPart_third_le hz hz₀ hz₁ (hd.trans (by norm_num)) hd2
      refine e1.trans ?_
      have hnb : neighbourIndicator z z₁ = 1 := by simp [neighbourIndicator, hd]
      have hnb' : neighbourIndicator z₀ z₁ = 1 := by simp [neighbourIndicator, hd']
      rw [hnb, hnb', one_mul, one_mul]
      have hx := h.energy_nonneg z hz
      have hy := h.energy_nonneg z₀ hz₀
      have hw := h.energy_nonneg z₁ hz₁
      set r := √(D z₁ + D z₀) with hr
      set r' := √(D z + D z₁) with hr'
      have h1 : r * r = D z₁ + D z₀ := Real.mul_self_sqrt (by linarith)
      have h2 : r' * r' = D z + D z₁ := Real.mul_self_sqrt (by linarith)
      have e2 : nearSumConstant F K * ((51 * (C₂ * r)) * (partitionBound * (51 * (C₂ * r')))) =
          nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) * (r * r') := by ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ hc
      nlinarith [sq_nonneg (r - r'), mul_self_nonneg r, mul_self_nonneg r']
    · rw [h.sum_actionTermsNear_eq_zero (z := z₀) (z' := z₁) (by simp) (by simp) hd']
      have hnb' : neighbourIndicator z₀ z₁ = 0 := by simp [neighbourIndicator, hd']
      rw [hnb']
      simp
  · rw [h.sum_actionTermsNear_eq_zero (z := z) (z' := z₁) (by simp) (by simp) hd]
    have hnb : neighbourIndicator z z₁ = 0 := by simp [neighbourIndicator, hd]
    rw [hnb]
    simp
theorem sqrt_energy_le {z : F.Cell} (hz : z ∈ A) : √(D z) ≤ √Cd * e0 := by
  have h1 : √(D z) ≤ √(Cd * e0 ^ 2) := Real.sqrt_le_sqrt (h.energy_le z hz)
  rwa [Real.sqrt_mul h.energyConst_nonneg, Real.sqrt_sq h.smallScale_nonneg] at h1
theorem sum_framingDefect_le {z : F.Cell} (hz : z ∈ A) :
    ∑ t ∈ actionTermsNear S {z}, farContribution a W kW (framingDefect W kW X k Γ z) t ≤
      nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0) := by
  have hM := nearSumConstant_nonneg (F := F) h
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  refine (h.sum_farPart_framingDefect_le hz).trans ?_
  have e : nearSumConstant F K * (51 * (defectConstant F.blockSide * (C * √(D z)))) =
      nearSumConstant F K * (51 * defectConstant F.blockSide * C) * √(D z) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (h.sqrt_energy_le hz)
    (mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) hcG) h.pinConst_nonneg))
theorem sum_changeVariation_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW
        (fun u => 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) t ≤
      neighbourIndicator z z₀ * (nearSumConstant F K * (612 * defectConstant F.blockSide * C) * (√Cd * e0)) := by
  have hM := nearSumConstant_nonneg (F := F) h
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  by_cases hd : cellSupDist z z₀ ≤ 8
  · refine (h.sum_farPart_changeVariation_le hz hz₀).trans ?_
    have hnb : neighbourIndicator z z₀ = 1 := by simp [neighbourIndicator, hd]
    rw [hnb, one_mul]
    have e : nearSumConstant F K * (51 * (3 * (2 * (defectConstant F.blockSide * (C * √(D z)) +
        defectConstant F.blockSide * (C * √(D z₀)))))) =
        nearSumConstant F K * (306 * defectConstant F.blockSide * C) * (√(D z) + √(D z₀)) := by ring
    have h1 := h.sqrt_energy_le hz
    have h2 := h.sqrt_energy_le hz₀
    rw [e]
    have hc : 0 ≤ nearSumConstant F K * (306 * defectConstant F.blockSide * C) :=
      mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) hcG) h.pinConst_nonneg)
    calc _ ≤ nearSumConstant F K * (306 * defectConstant F.blockSide * C) * (2 * (√Cd * e0)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ = _ := by ring
  · rw [h.sum_actionTermsNear_eq_zero (z := z) (z' := z₀) (by simp) (by simp) hd]
    have hnb : neighbourIndicator z z₀ = 0 := by simp [neighbourIndicator, hd]
    rw [hnb]
    simp
theorem sum_correction_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW
        (fun u => targetChange (Γ z) (Γ z₀) u * partitionScale F u) t ≤
      neighbourIndicator z z₀ * (nearSumConstant F K * (51 * 51 * partitionBound * C₂ * 2) * (√Cd * e0)) := by
  have hM := nearSumConstant_nonneg (F := F) h
  by_cases hd : cellSupDist z z₀ ≤ 8
  · refine (h.sum_farPart_correction_le hz hz₀ (hd.trans (by norm_num))).trans ?_
    have hnb : neighbourIndicator z z₀ = 1 := by simp [neighbourIndicator, hd]
    rw [hnb, one_mul]
    have e : nearSumConstant F K * ((51 * (C₂ * √(D z + D z₀))) * (partitionBound * 51)) =
        nearSumConstant F K * (51 * 51 * partitionBound * C₂) * √(D z + D z₀) := by ring
    rw [e]
    have h1 : √(D z + D z₀) ≤ 2 * (√Cd * e0) := by
      have h2 : D z + D z₀ ≤ 2 ^ 2 * (Cd * e0 ^ 2) := by
        have := h.energy_le z hz
        have := h.energy_le z₀ hz₀
        have : 0 ≤ Cd * e0 ^ 2 := mul_nonneg h.energyConst_nonneg (sq_nonneg _)
        linarith
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), Real.sqrt_mul h.energyConst_nonneg,
        Real.sqrt_sq h.smallScale_nonneg] at h3
    have hc : 0 ≤ nearSumConstant F K * (51 * 51 * partitionBound * C₂) :=
      mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) partitionBound_pos.le) h.changeConst_nonneg)
    calc _ ≤ nearSumConstant F K * (51 * 51 * partitionBound * C₂) * (2 * (√Cd * e0)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by ring
  · rw [h.sum_actionTermsNear_eq_zero (z := z) (z' := z₀) (by simp) (by simp) hd]
    have hnb : neighbourIndicator z z₀ = 0 := by simp [neighbourIndicator, hd]
    rw [hnb]
    simp
theorem sum_abs_residual_inner_le :
    ∑ t ∈ (actionTerms S).filter (fun t => ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A),
      |residual A (actionForms a W kW) (slotPartition S) (termPartition S) (framingVariation W kW X k Γ)
        (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * (nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
          (2 * 17 ^ 4 * ∑ z ∈ A, D z) +
        nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) * (4 * (17 ^ 4) ^ 2 * ∑ z ∈ A, D z)) := by
  classical
  set T := (actionTerms S).filter (fun t => ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A) with hTdef
  have hT : T ⊆ actionTerms S := Finset.filter_subset _ _
  have hM := nearSumConstant_nonneg (F := F) h
  have hgB := termDefectConstant_nonneg (F := F) h
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  set sec : F.Cell → F.Cell → F.ActionTerm → ℝ := fun z z₀ t => farContribution a W kW
      (fun u => changeWeight W kW (Γ z) (Γ z₀) u *
        (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u))) t with hsec
  set thd : F.Cell → F.Cell → F.Cell → F.ActionTerm → ℝ := fun z z₀ z₁ t => farContribution a W kW
      (fun u => targetChange (Γ z₁) (Γ z₀) u * scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u) t
    with hthd
  have hsec0 : ∀ z z₀ t, 0 ≤ sec z z₀ t := fun z z₀ t => farContribution_nonneg h.coupling_nonneg W kW (fun u =>
    mul_nonneg (changeWeight_nonneg W kW _ _ u)
      (mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u)))) t
  have hthd0 : ∀ z z₀ z₁ t, 0 ≤ thd z z₀ z₁ t := fun z z₀ z₁ t => farContribution_nonneg h.coupling_nonneg W kW
    (fun u => mul_nonneg (targetChange_nonneg _ _ u)
      (scaledBondWeight_nonneg partitionBound_pos.le (targetChange_nonneg _ _) u)) t
  have h1 : ∀ t ∈ T, |residual A (actionForms a W kW) (slotPartition S) (termPartition S)
      (framingVariation W kW X k Γ) (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * (∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, sec z z₀ t +
        ∑ z₁ ∈ cellsNearTerm A t, ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, thd z z₀ z₁ t) := by
    intro t ht
    have ht' := Finset.mem_filter.1 ht
    have hcell : actionTermCell t ∈ S := (enclosingCell_actionTermSite h.odd ht'.1).1
    have hself : cellSupDist (actionTermCell t) (actionTermCell t) ≤ 4 := by rw [cellSupDist_self]; norm_num
    have hin : actionTermCell t ∈ cellsNearTerm A t := Finset.mem_filter.2 ⟨ht'.2 _ hcell hself, hself⟩
    refine (h.abs_residual_le_of_inner ht'.1 ht'.2 (actionTermCell t)).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hgB
    exact Finset.single_le_sum
      (f := fun z₁ => ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, thd z z₀ z₁ t)
      (fun z₁ _ => Finset.sum_nonneg fun z₀ _ => Finset.sum_nonneg fun z _ => hthd0 z z₀ z₁ t) hin
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hgB
  · refine (sum_cellsNearTerm_pair_le T hT (A' := A) (fun t _ => Finset.filter_subset _ _) sec hsec0).trans ?_
    have hc : 0 ≤ nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) :=
      mul_nonneg hM (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.changeConst_nonneg) hcG) h.pinConst_nonneg)
    calc _ ≤ ∑ z₀ ∈ A, ∑ z ∈ A, nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
            (neighbourIndicator z z₀ * (D z + D z₀)) :=
          Finset.sum_le_sum fun z₀ hz₀ => Finset.sum_le_sum fun z hz => h.sum_second_le hz hz₀
      _ = nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
            ∑ z₀ ∈ A, ∑ z ∈ A, neighbourIndicator z z₀ * (D z + D z₀) := by
          simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pair_energy_le h.energy_nonneg) hc
  · refine (sum_cellsNearTerm_triple_le T hT thd hthd0).trans ?_
    have hc : 0 ≤ nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) :=
      mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) partitionBound_pos.le) (sq_nonneg _))
    calc _ ≤ ∑ z₁ ∈ A, ∑ z₀ ∈ A, ∑ z ∈ A, nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) *
            (neighbourIndicator z z₁ * neighbourIndicator z₀ z₁ * (D z + 2 * D z₁ + D z₀)) :=
          Finset.sum_le_sum fun z₁ hz₁ => Finset.sum_le_sum fun z₀ hz₀ => Finset.sum_le_sum fun z hz =>
            h.sum_third_le hz hz₀ hz₁
      _ = nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) * ∑ z₁ ∈ A, ∑ z₀ ∈ A, ∑ z ∈ A,
            neighbourIndicator z z₁ * neighbourIndicator z₀ z₁ * (D z + 2 * D z₁ + D z₀) := by
          simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_triple_energy_le h.energy_nonneg) hc
theorem sum_abs_residual_outer_le :
    ∑ t ∈ (actionTerms S).filter (fun t => ¬ ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A),
      |residual A (actionForms a W kW) (slotPartition S) (termPartition S) (framingVariation W kW X k Γ)
        (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * ((97 ^ 4 * Bd.card) *
        (nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0) +
        17 ^ 4 * (nearSumConstant F K * (612 * defectConstant F.blockSide * C) * (√Cd * e0)) +
        17 ^ 4 * (nearSumConstant F K * (51 * 51 * partitionBound * C₂ * 2) * (√Cd * e0)))) := by
  classical
  set T := (actionTerms S).filter (fun t => ¬ ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A)
    with hTdef
  have hT : T ⊆ actionTerms S := Finset.filter_subset _ _
  have hM := nearSumConstant_nonneg (F := F) h
  have hgB := termDefectConstant_nonneg (F := F) h
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  have hδ : 0 ≤ √Cd * e0 := mul_nonneg (Real.sqrt_nonneg _) h.smallScale_nonneg
  set Ab := A.filter fun z => ∃ b ∈ Bd, cellSupDist z b ≤ 48 with hAb
  have hAbA : Ab ⊆ A := Finset.filter_subset _ _
  have hcard : (Ab.card : ℝ) ≤ 97 ^ 4 * Bd.card := by
    have hsub : Ab ⊆ Bd.biUnion fun b => A.filter fun z => cellSupDist z b ≤ 48 := by
      intro z hz
      obtain ⟨hzA, b, hb, hd⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_filter.2 ⟨hzA, hd⟩⟩
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul Bd _ (97 ^ 4) fun b _ => by
      have := card_le_of_cellSupDist_le b 48 (A.filter fun z => cellSupDist z b ≤ 48)
        fun z hz => (Finset.mem_filter.1 hz).2
      simpa using this)
    have h2 : (Ab.card : ℝ) ≤ Bd.card * 97 ^ 4 := by exact_mod_cast h1
    linarith
  have hsub : ∀ t ∈ T, cellsNearTerm A t ⊆ Ab := by
    intro t ht z hz
    have ht' := (Finset.mem_filter.1 ht).2
    simp only [not_forall] at ht'
    obtain ⟨y, hy, hyd, hyA⟩ := ht'
    obtain ⟨b, hb, hd⟩ := h.near_bad y hy hyA
    have hz' := Finset.mem_filter.1 hz
    refine Finset.mem_filter.2 ⟨hz'.1, b, hb, ?_⟩
    have t1 := cellSupDist_triangle z (actionTermCell t) b
    have t2 := cellSupDist_triangle (actionTermCell t) y b
    rw [cellSupDist_comm (actionTermCell t) y] at t2
    have := hz'.2
    omega
  set var : F.Cell → F.ActionTerm → ℝ := fun z t => farContribution a W kW (framingDefect W kW X k Γ z) t with hvar
  set gau : F.Cell → F.Cell → F.ActionTerm → ℝ := fun z z₀ t => farContribution a W kW
      (fun u => 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) t with hgau
  set cor : F.Cell → F.Cell → F.ActionTerm → ℝ := fun z z₀ t => farContribution a W kW
      (fun u => targetChange (Γ z) (Γ z₀) u * partitionScale F u) t with hcor
  have hvar0 : ∀ z t, 0 ≤ var z t := fun z t =>
    farContribution_nonneg h.coupling_nonneg W kW (framingDefect_nonneg h z) t
  have hgau0 : ∀ z z₀ t, 0 ≤ gau z z₀ t := fun z z₀ t => farContribution_nonneg h.coupling_nonneg W kW (fun u =>
    mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u))) t
  have hcor0 : ∀ z z₀ t, 0 ≤ cor z z₀ t := fun z z₀ t => farContribution_nonneg h.coupling_nonneg W kW (fun u =>
    mul_nonneg (targetChange_nonneg _ _ u) (partitionScale_nonneg h u)) t
  have h1 : ∀ t ∈ T, |residual A (actionForms a W kW) (slotPartition S) (termPartition S)
      (framingVariation W kW X k Γ) (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * (∑ z ∈ cellsNearTerm A t, var z t +
        ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, gau z z₀ t +
        ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, cor z z₀ t) :=
    fun t ht => h.abs_residual_le (hT ht)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hgB
  have hpair : ∀ (f : F.Cell → F.Cell → F.ActionTerm → ℝ) (c : ℝ), 0 ≤ c → (∀ z z₀ t, 0 ≤ f z z₀ t) →
      (∀ z ∈ A, ∀ z₀ ∈ A, ∑ t ∈ actionTermsNear S {z, z₀}, f z z₀ t ≤ neighbourIndicator z z₀ * c) →
      ∑ t ∈ T, ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, f z z₀ t ≤
        (97 ^ 4 * Bd.card) * (17 ^ 4 * c) := by
    intro f c hc hf hb
    refine (sum_cellsNearTerm_pair_le T hT hsub f hf).trans ?_
    have h2 : ∀ z₀ ∈ Ab, ∑ z ∈ A, ∑ t ∈ actionTermsNear S {z, z₀}, f z z₀ t ≤ 17 ^ 4 * c := by
      intro z₀ hz₀
      refine (Finset.sum_le_sum fun z hz => hb z hz z₀ (hAbA hz₀)).trans ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_neighbourIndicator_le A z₀) hc
    have h3 := Finset.sum_le_card_nsmul Ab _ _ h2
    rw [nsmul_eq_mul] at h3
    exact h3.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have c1 : 0 ≤ nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0) :=
    mul_nonneg (mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) hcG) h.pinConst_nonneg)) hδ
  have c2 : 0 ≤ nearSumConstant F K * (612 * defectConstant F.blockSide * C) * (√Cd * e0) :=
    mul_nonneg (mul_nonneg hM (mul_nonneg (mul_nonneg (by norm_num) hcG) h.pinConst_nonneg)) hδ
  have c3 : 0 ≤ nearSumConstant F K * (51 * 51 * partitionBound * C₂ * 2) * (√Cd * e0) :=
    mul_nonneg (mul_nonneg hM (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) partitionBound_pos.le)
      h.changeConst_nonneg) (by norm_num))) hδ
  have s1 : ∑ t ∈ T, ∑ z ∈ cellsNearTerm A t, var z t ≤
      (97 ^ 4 * Bd.card) * (nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0)) := by
    refine (sum_cellsNearTerm_le_sum_actionTermsNear T hT hsub var hvar0).trans ?_
    have h3 := Finset.sum_le_card_nsmul Ab _ _ fun z hz => h.sum_framingDefect_le (hAbA hz)
    rw [nsmul_eq_mul] at h3
    exact h3.trans (mul_le_mul_of_nonneg_right hcard c1)
  have s2 := hpair gau _ c2 hgau0 fun z hz z₀ hz₀ => h.sum_changeVariation_le hz hz₀
  have s3 := hpair cor _ c3 hcor0 fun z hz z₀ hz₀ => h.sum_correction_le hz hz₀
  have := add_le_add (add_le_add s1 s2) s3
  refine this.trans (le_of_eq ?_)
  ring
theorem abs_sum_weighted_le :
    |∑ z ∈ A, ∑ t ∈ actionTerms S, termPartition S z t * actionForms a W kW t (framingVariation W kW X k Γ z)| ≤
      termDefectConstant F * (nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
          (2 * 17 ^ 4 * ∑ z ∈ A, D z) +
        nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) * (4 * (17 ^ 4) ^ 2 * ∑ z ∈ A, D z)) +
      termDefectConstant F * ((97 ^ 4 * Bd.card) *
        (nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0) +
        17 ^ 4 * (nearSumConstant F K * (612 * defectConstant F.blockSide * C) * (√Cd * e0)) +
        17 ^ 4 * (nearSumConstant F K * (51 * 51 * partitionBound * C₂ * 2) * (√Cd * e0)))) := by
  classical
  rw [sum_weighted_eq_neg_sum_residual A (actionForms a W kW) (slotPartition S) (termPartition S)
    (framingVariation W kW X k Γ) (correctionOf S A W kW Γ) (actionTerms S) h.critical, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (actionTerms S)
    (fun t => ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A)]
  exact add_le_add h.sum_abs_residual_inner_le h.sum_abs_residual_outer_le
def firstOrderConstant (L : ℕ) (C C₂ Cd : ℝ) : ℝ :=
  partitionBound * (2 * L) * (contourSumConstant L * 81) *
    ((408 * C₂ * defectConstant L * C) * (2 * 17 ^ 4) + (51 * 51 * partitionBound * C₂ ^ 2) * (4 * (17 ^ 4) ^ 2) +
      97 ^ 4 * ((51 * defectConstant L * C) + 17 ^ 4 * (612 * defectConstant L * C) +
        17 ^ 4 * (51 * 51 * partitionBound * C₂ * 2)) * √Cd)
omit h in
theorem firstOrderConstant_nonneg (L : ℕ) {C C₂ Cd : ℝ} (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) :
    0 ≤ firstOrderConstant L C C₂ Cd := by
  have hcG : 0 ≤ defectConstant L := by have := one_le_defectConstant L; linarith
  have hs := partitionBound_pos
  have hc := contourSumConstant_pos L
  unfold firstOrderConstant
  positivity
theorem abs_sum_weighted_le_firstOrderConstant :
    |∑ z ∈ A, ∑ t ∈ actionTerms S, termPartition S z t * actionForms a W kW t (framingVariation W kW X k Γ z)| ≤
      K * firstOrderConstant F.blockSide C C₂ Cd * (∑ z ∈ A, D z + e0 * Bd.card) := by
  refine h.abs_sum_weighted_le.trans ?_
  set U := ∑ z ∈ A, D z with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg h.energy_nonneg
  have hn : (0 : ℝ) ≤ Bd.card := by positivity
  have hK := h.sizeConst_nonneg
  have he := h.smallScale_nonneg
  have hcG : 0 ≤ defectConstant F.blockSide := by have := one_le_defectConstant F.blockSide; linarith
  have hs := partitionBound_pos
  have hc := contourSumConstant_pos F.blockSide
  have hC := h.pinConst_nonneg
  have hC₂ := h.changeConst_nonneg
  set c0 : ℝ := partitionBound * (2 * F.blockSide) * (contourSumConstant F.blockSide * 81) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set c1 : ℝ := (408 * C₂ * defectConstant F.blockSide * C) * (2 * 17 ^ 4) +
      (51 * 51 * partitionBound * C₂ ^ 2) * (4 * (17 ^ 4) ^ 2) with hc1
  set c2 : ℝ := 97 ^ 4 * ((51 * defectConstant F.blockSide * C) + 17 ^ 4 * (612 * defectConstant F.blockSide * C) +
        17 ^ 4 * (51 * 51 * partitionBound * C₂ * 2)) * √Cd with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have e1 : termDefectConstant F * (nearSumConstant F K * (408 * C₂ * defectConstant F.blockSide * C) *
          (2 * 17 ^ 4 * U) +
        nearSumConstant F K * (51 * 51 * partitionBound * C₂ ^ 2) * (4 * (17 ^ 4) ^ 2 * U)) +
      termDefectConstant F * ((97 ^ 4 * Bd.card) *
        (nearSumConstant F K * (51 * defectConstant F.blockSide * C) * (√Cd * e0) +
        17 ^ 4 * (nearSumConstant F K * (612 * defectConstant F.blockSide * C) * (√Cd * e0)) +
        17 ^ 4 * (nearSumConstant F K * (51 * 51 * partitionBound * C₂ * 2) * (√Cd * e0)))) =
      K * c0 * (c1 * U + c2 * (e0 * Bd.card)) := by
    simp only [hc0, hc1, hc2, termDefectConstant, nearSumConstant]
    ring
  rw [e1]
  have e2 : firstOrderConstant F.blockSide C C₂ Cd = c0 * (c1 + c2) := rfl
  rw [e2]
  have h3 : 0 ≤ e0 * Bd.card := mul_nonneg he hn
  have h4 : c1 * U + c2 * (e0 * Bd.card) ≤ (c1 + c2) * (U + e0 * Bd.card) := by
    nlinarith [mul_nonneg hc10 h3, mul_nonneg hc20 hU0]
  calc _ ≤ K * c0 * ((c1 + c2) * (U + e0 * Bd.card)) := mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hc00)
    _ = _ := by ring
end GluedFirstOrderData
end YangMills.Construction.BlockAverages.VariationRates
end
