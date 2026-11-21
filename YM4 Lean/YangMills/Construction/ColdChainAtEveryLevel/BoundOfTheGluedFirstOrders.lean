import YangMills.Construction.ColdChainAtEveryLevel.FramingsOnTheClearCellsForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open YangMills.Construction.EvaluationSums YangMills.Construction.PartitionGluing
  YangMills.Construction.LatticeFractionalIntegration PatchLocality ChartCoordinates
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
structure GluedFirstOrderData (a C C₂ Cd e0 K ρ : ℝ) (S A Bd : Finset F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k : F.SiteGauge) (Γ : F.Cell → F.SiteGauge) (D : F.Cell → ℝ) : Prop where
  ambient : IsAdmissibleAmbient F
  odd : Odd F.blockSide
  covariance : gaugeCovarianceStatement
  coupling_nonneg : 0 ≤ a
  pinConst_nonneg : 0 ≤ C
  changeConst_nonneg : 0 ≤ C₂
  energyConst_nonneg : 0 ≤ Cd
  smallScale_nonneg : 0 ≤ e0
  sizeConst_nonneg : 0 ≤ K
  ratio_nonneg : 0 ≤ ρ
  ratio_le_half : ρ ≤ 1 / 2
  sizes : CellwiseSizes a S W kW K ρ
  averages_ne_zero : ∀ t ∈ actionTerms S, AveragesNeZero W kW t
  critical : ∀ V : VariationSlot F → imaginaryQuaternions, ∑ t ∈ actionTerms S, actionTermRateLinear a W kW t V = 0
  subset : A ⊆ S
  orthant : ∀ z : F.Cell, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1
  energy_eq : ∀ z, D z = relativeEnergy a S z W kW X k (Γ z)
  energy_nonneg : ∀ z ∈ A, 0 ≤ D z
  pinned : ∀ z ∈ A, IsPinnedGauge a C S z W kW X k (Γ z)
  energy_le : ∀ z ∈ A, D z ≤ Cd * e0 ^ 2
  change_le : ∀ z ∈ A, ∀ z' ∈ A, cellSupDist z z' ≤ 40 → ∀ y ∈ S, baseSite y ∈ patchBaseSites S z →
    baseSite y ∈ patchBaseSites S z' →
    ∀ j, j < F.top → levelScale F j ^ 4 * ∑ x ∈ sitesOfCells {y} j, _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z) (Γ z') j x) ^ 4 ≤
      (C₂ * √(D z + D z')) ^ 4
  near_bad : ∀ y ∈ S, y ∉ A → ∃ b ∈ Bd, cellSupDist y b ≤ 40
variable {a C C₂ Cd e0 K ρ : ℝ} {A Bd : Finset F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
  {k : F.SiteGauge} {Γ : F.Cell → F.SiteGauge} {D : F.Cell → ℝ}
namespace GluedFirstOrderData
variable (h : GluedFirstOrderData a C C₂ Cd e0 K ρ S A Bd W kW X k Γ D)
include h
theorem refineSite_injective : ∀ j, j < F.top → Function.Injective (_root_.YangMills.Construction.BlockAverages.refineSite (F := F) (j := j)) :=
  fun j hj => (h.covariance F j hj h.odd.pos).1
theorem quarticBound_framingDefect {z : F.Cell} (hz : z ∈ A) {Zs : Finset F.Cell} (hzZ : z ∈ Zs) :
    QuarticBound S (cellsNear S Zs) (defectConstant F.blockSide * (C * √(D z))) (framingDefect W kW X k Γ z) := by
  have := quarticBound_slotDefect h.ambient h.odd h.refineSite_injective (h.orthant z) h.pinConst_nonneg
    (h.pinned z hz) (mem_cellsNear hzZ) (card_cellsNear_le hzZ)
  rw [← h.energy_eq z] at this
  exact this
theorem baseSite_mem_patchBaseSites {z y : F.Cell} (hy : y ∈ S) (hd : cellSupDist z y ≤ 10) :
    baseSite y ∈ patchBaseSites S z := by
  have e : baseSite y = cellCentre 0 y + siteOfCoords 0 (0 : Lattice4) := by
    rw [siteOfCoords_zero, add_zero]
    conv_lhs => rw [← cellCentre_top y]
    exact baseSite_cellCentre F.top le_rfl y
  rw [e]
  refine mem_patchBaseSites_of_cellSupDist_le h.ambient h.odd (h.orthant z) hy hd ?_
  refine Fintype.mem_piFinset.2 fun i => ?_
  have : 0 < F.blockSide ^ F.top := by have := h.odd.pos; positivity
  simp only [Pi.zero_apply, Finset.mem_Icc]
  omega
theorem gaugeChange_top {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (x : F.Site F.top) :
    gaugeChange (Γ z) (Γ z₀) F.top x = 1 := by
  unfold gaugeChange
  rw [(h.pinned z hz).1 x, (h.pinned z₀ hz₀).1 x]
  simp
theorem scaledQuarticBound_changeWeight_of_near {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A)
    (hd : cellSupDist z z₀ ≤ 40) {Zs : Finset F.Cell} (hzZ : z ∈ Zs) (hz₀Z : z₀ ∈ Zs) :
    ScaledQuarticBound S (cellsNear S Zs) (51 * (C₂ * √(D z + D z₀))) (changeWeight W kW (Γ z) (Γ z₀)) := by
  refine scaledQuarticBound_changeWeight W kW (Γ z) (Γ z₀) h.odd h.refineSite_injective (card_cellsNear_le hzZ)
    (mul_nonneg h.changeConst_nonneg (Real.sqrt_nonneg _)) ?_ (h.gaugeChange_top hz hz₀)
  intro j hj y hy
  have h1 := mem_cellsNear (S := S) hzZ y hy
  have h2 := mem_cellsNear (S := S) hz₀Z y hy
  exact h.change_le z hz z₀ hz₀ hd y h1.1 (h.baseSite_mem_patchBaseSites h1.1 h1.2)
    (h.baseSite_mem_patchBaseSites h2.1 h2.2) j hj
theorem scaledQuarticBound_targetChange {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (hd : cellSupDist z z₀ ≤ 40)
    {Zs : Finset F.Cell} (hzZ : z ∈ Zs) (hz₀Z : z₀ ∈ Zs) :
    ScaledQuarticBound S (cellsNear S Zs) (51 * (C₂ * √(D z + D z₀))) (targetChange (Γ z) (Γ z₀)) :=
  scaledQuarticBound_mono (targetChange_nonneg _ _) (targetChange_le_changeWeight W kW _ _)
    (h.scaledQuarticBound_changeWeight_of_near hz hz₀ hd hzZ hz₀Z)
def nearSumConstant (F : BlockFrame) (K : ℝ) : ℝ := contourSumConstant F.blockSide * (81 * K)
theorem nearSumConstant_nonneg : 0 ≤ nearSumConstant F K :=
  mul_nonneg (contourSumConstant_pos _).le (mul_nonneg (by norm_num) h.sizeConst_nonneg)
theorem framingDefect_nonneg (z : F.Cell) (u : VariationSlot F) : 0 ≤ framingDefect W kW X k Γ z u :=
  distFromOne_nonneg _
theorem defectBound_nonneg (z : F.Cell) : 0 ≤ defectConstant F.blockSide * (C * √(D z)) :=
  mul_nonneg (by have := one_le_defectConstant F.blockSide; linarith)
    (mul_nonneg h.pinConst_nonneg (Real.sqrt_nonneg _))
theorem sum_farPart_framingDefect_le {z : F.Cell} (hz : z ∈ A) :
    ∑ t ∈ actionTermsNear S {z}, farContribution a W kW (framingDefect W kW X k Γ z) t ≤
      nearSumConstant F K * (51 * (defectConstant F.blockSide * (C * √(D z)))) := by
  have hzZ : z ∈ ({z} : Finset F.Cell) := Finset.mem_singleton_self z
  exact sum_farPart_actionTermsNear_le h.ambient h.odd h.refineSite_injective h.coupling_nonneg
    h.sizeConst_nonneg h.ratio_nonneg h.ratio_le_half h.sizes hzZ (by norm_num) (h.defectBound_nonneg z)
    (f := fun _ => 1) (fun _ => zero_le_one) (framingDefect_nonneg h z) (framingDefect_nonneg h z)
    (fun u => by simp) (scaledQuarticBound_one h.odd (card_cellsNear_le hzZ)) (h.quarticBound_framingDefect hz hzZ)
theorem sum_farPart_changeVariation_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW
        (fun u => 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) t ≤
      nearSumConstant F K * (51 * (3 * (2 * (defectConstant F.blockSide * (C * √(D z)) +
        defectConstant F.blockSide * (C * √(D z₀)))))) := by
  have hzZ : z ∈ ({z, z₀} : Finset F.Cell) := by simp
  have hz₀Z : z₀ ∈ ({z, z₀} : Finset F.Cell) := by simp
  have p1 := h.defectBound_nonneg z
  have p2 := h.defectBound_nonneg z₀
  have q : ∀ u, 0 ≤ 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u) := fun u =>
    mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u))
  exact sum_farPart_actionTermsNear_le h.ambient h.odd h.refineSite_injective h.coupling_nonneg
    h.sizeConst_nonneg h.ratio_nonneg h.ratio_le_half h.sizes hzZ (by norm_num) (by positivity)
    (f := fun _ => 1) (fun _ => zero_le_one) q q (fun u => by simp)
    (scaledQuarticBound_one h.odd (card_cellsNear_le hzZ))
    (quarticBound_const_mul (by norm_num) (quarticBound_add p1 p2 (framingDefect_nonneg h z)
      (framingDefect_nonneg h z₀) (h.quarticBound_framingDefect hz hzZ) (h.quarticBound_framingDefect hz₀ hz₀Z)))
def partitionScale (F : BlockFrame) : VariationSlot F → ℝ := scaledBondWeight partitionBound (fun _ => 1)
theorem partitionScale_nonneg (u : VariationSlot F) : 0 ≤ partitionScale F u :=
  scaledBondWeight_nonneg partitionBound_pos.le (fun _ => zero_le_one) u
theorem sum_farPart_correction_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (hd : cellSupDist z z₀ ≤ 40) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW (fun u => targetChange (Γ z) (Γ z₀) u * partitionScale F u) t ≤
      nearSumConstant F K * ((51 * (C₂ * √(D z + D z₀))) * (partitionBound * 51)) := by
  have hzZ : z ∈ ({z, z₀} : Finset F.Cell) := by simp
  have hz₀Z : z₀ ∈ ({z, z₀} : Finset F.Cell) := by simp
  have hP : 0 ≤ 51 * (C₂ * √(D z + D z₀)) :=
    mul_nonneg (by norm_num) (mul_nonneg h.changeConst_nonneg (Real.sqrt_nonneg _))
  have hQ : 0 ≤ partitionBound * 51 := mul_nonneg partitionBound_pos.le (by norm_num)
  exact sum_farPart_actionTermsNear_le h.ambient h.odd h.refineSite_injective h.coupling_nonneg
    h.sizeConst_nonneg h.ratio_nonneg h.ratio_le_half h.sizes hzZ hP hQ (targetChange_nonneg _ _)
    (partitionScale_nonneg h) (fun u => mul_nonneg (targetChange_nonneg _ _ u) (partitionScale_nonneg h u))
    (fun u => le_rfl) (h.scaledQuarticBound_targetChange hz hz₀ hd hzZ hz₀Z)
    (quarticBound_scaledBondWeight partitionBound_pos.le (by norm_num)
      (scaledQuarticBound_one h.odd (card_cellsNear_le hzZ)))
theorem sum_farPart_second_le {z z₀ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (hd : cellSupDist z z₀ ≤ 40) :
    ∑ t ∈ actionTermsNear S {z, z₀}, farContribution a W kW (fun u => changeWeight W kW (Γ z) (Γ z₀) u *
        (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u))) t ≤
      nearSumConstant F K * ((51 * (C₂ * √(D z + D z₀))) *
        (2 * (2 * (defectConstant F.blockSide * (C * √(D z)) + defectConstant F.blockSide * (C * √(D z₀)))))) := by
  have hzZ : z ∈ ({z, z₀} : Finset F.Cell) := by simp
  have hz₀Z : z₀ ∈ ({z, z₀} : Finset F.Cell) := by simp
  have p1 := h.defectBound_nonneg z
  have p2 := h.defectBound_nonneg z₀
  have hP : 0 ≤ 51 * (C₂ * √(D z + D z₀)) :=
    mul_nonneg (by norm_num) (mul_nonneg h.changeConst_nonneg (Real.sqrt_nonneg _))
  have q : ∀ u, 0 ≤ 2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u) := fun u =>
    mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u))
  exact sum_farPart_actionTermsNear_le h.ambient h.odd h.refineSite_injective h.coupling_nonneg
    h.sizeConst_nonneg h.ratio_nonneg h.ratio_le_half h.sizes hzZ hP (by positivity)
    (changeWeight_nonneg W kW _ _) q (fun u => mul_nonneg (changeWeight_nonneg W kW _ _ u) (q u)) (fun u => le_rfl)
    (h.scaledQuarticBound_changeWeight_of_near hz hz₀ hd hzZ hz₀Z)
    (quarticBound_const_mul (by norm_num) (quarticBound_add p1 p2 (framingDefect_nonneg h z)
      (framingDefect_nonneg h z₀) (h.quarticBound_framingDefect hz hzZ) (h.quarticBound_framingDefect hz₀ hz₀Z)))
theorem sum_farPart_third_le {z z₀ z₁ : F.Cell} (hz : z ∈ A) (hz₀ : z₀ ∈ A) (hz₁ : z₁ ∈ A)
    (hd : cellSupDist z z₁ ≤ 40) (hd' : cellSupDist z₁ z₀ ≤ 40) :
    ∑ t ∈ actionTermsNear S {z, z₀, z₁}, farContribution a W kW
        (fun u => targetChange (Γ z₁) (Γ z₀) u * scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u) t ≤
      nearSumConstant F K * ((51 * (C₂ * √(D z₁ + D z₀))) * (partitionBound * (51 * (C₂ * √(D z + D z₁))))) := by
  have hzZ : z ∈ ({z, z₀, z₁} : Finset F.Cell) := by simp
  have hz₀Z : z₀ ∈ ({z, z₀, z₁} : Finset F.Cell) := by simp
  have hz₁Z : z₁ ∈ ({z, z₀, z₁} : Finset F.Cell) := by simp
  have hP : 0 ≤ 51 * (C₂ * √(D z₁ + D z₀)) :=
    mul_nonneg (by norm_num) (mul_nonneg h.changeConst_nonneg (Real.sqrt_nonneg _))
  have hP' : 0 ≤ 51 * (C₂ * √(D z + D z₁)) :=
    mul_nonneg (by norm_num) (mul_nonneg h.changeConst_nonneg (Real.sqrt_nonneg _))
  have hQ : 0 ≤ partitionBound * (51 * (C₂ * √(D z + D z₁))) := mul_nonneg partitionBound_pos.le hP'
  have q := scaledBondWeight_nonneg (F := F) partitionBound_pos.le (targetChange_nonneg (Γ z) (Γ z₁))
  exact sum_farPart_actionTermsNear_le h.ambient h.odd h.refineSite_injective h.coupling_nonneg
    h.sizeConst_nonneg h.ratio_nonneg h.ratio_le_half h.sizes hzZ hP hQ (targetChange_nonneg _ _) q
    (fun u => mul_nonneg (targetChange_nonneg _ _ u) (q u)) (fun u => le_rfl)
    (h.scaledQuarticBound_targetChange hz₁ hz₀ hd' hz₁Z hz₀Z)
    (quarticBound_scaledBondWeight partitionBound_pos.le hP' (h.scaledQuarticBound_targetChange hz hz₁ hd hzZ hz₁Z))
abbrev actionForms (a : ℝ) (W : F.FieldChain) (kW : F.SiteGauge) :
    F.ActionTerm → (VariationSlot F → imaginaryQuaternions) →ₗ[ℝ] ℝ := fun t => actionTermRateLinear a W kW t
abbrev correctionOf (S A : Finset F.Cell) (W : F.FieldChain) (kW : F.SiteGauge) (Γ : F.Cell → F.SiteGauge) :
    F.Cell → VariationSlot F → imaginaryQuaternions :=
  invariantCorrection A (slotPartition S) (changeVariation W kW Γ) (scaledChangeVariation S W kW Γ)
omit h in
theorem correctionOf_bond {j : ℕ} (z₀ : F.Cell) (x : F.Site j) (i : Fin 4) :
    correctionOf S A W kW Γ z₀ (slotOfBond j x i) =
      ∑ z ∈ A, (cellPartition S (baseSite x) z - cellPartition S (baseSite (x + unitStep j i)) z) •
        adjointImaginary (W j x i) (imaginaryOfUnit (gaugeChange (Γ z) (Γ z₀) j (x + unitStep j i))) := by
  unfold correctionOf invariantCorrection
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact slotValues_scaled_bond W kW (fun x => cellPartition S x z) (gaugeChangeRates (Γ z) (Γ z₀)) x i
omit h in
theorem correctionOf_link {j : ℕ} (hj : j + 1 ≤ F.top) (z₀ : F.Cell) (y : F.Site (j + 1)) :
    correctionOf S A W kW Γ z₀ (slotOfLink j y) = 0 := by
  unfold correctionOf invariantCorrection
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  exact slotValues_scaled_link W kW (fun x => cellPartition S x z) (gaugeChangeRates (Γ z) (Γ z₀)) hj y
open Classical in
def cellsNearTerm (A : Finset F.Cell) (t : F.ActionTerm) : Finset F.Cell :=
  A.filter fun z => cellSupDist z (actionTermCell t) ≤ 4
omit h in
theorem sum_cellsNearTerm {M : Type} [AddCommMonoid M] {t : F.ActionTerm} (f : F.Cell → M)
    (hf : ∀ z ∈ A, ¬ cellSupDist z (actionTermCell t) ≤ 4 → f z = 0) :
    ∑ z ∈ A, f z = ∑ z ∈ cellsNearTerm A t, f z := by
  classical
  unfold cellsNearTerm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  split_ifs with hd
  · rfl
  · exact hf z hz hd
theorem norm_correctionOf_le {t : F.ActionTerm} (ht : t ∈ actionTerms S) {u : VariationSlot F} (hu : ReadsSlot t u)
    (z₀ : F.Cell) :
    ‖correctionOf S A W kW Γ z₀ u‖ ≤ ∑ z ∈ cellsNearTerm A t, targetChange (Γ z) (Γ z₀) u * partitionScale F u := by
  have hlev := slotEndLevel_le_top_of_readsSlot ht hu
  obtain ⟨w1, w2, s1, s2⟩ := supClose_of_readsSlot h.odd ht hu
  rcases u with ⟨j, x, i⟩ | ⟨j, y⟩
  · have hj : j ≤ F.top := hlev
    have e := correctionOf_bond (S := S) (A := A) (W := W) (kW := kW) (Γ := Γ) z₀ x i
    have e1 : correctionOf S A W kW Γ z₀ (Sum.inl ⟨j, x, i⟩) = correctionOf S A W kW Γ z₀ (slotOfBond j x i) := rfl
    rw [e1, e, sum_cellsNearTerm (t := t) _ (fun z _ hd => by
      have a1 : cellPartition S (baseSite x) z = 0 := cellPartition_eq_zero_of_far h.ambient h.odd ht w1 hd
      have a2 : cellPartition S (baseSite (x + unitStep j i)) z = 0 :=
        cellPartition_eq_zero_of_far h.ambient h.odd ht w2 hd
      rw [a1, a2, sub_zero, zero_smul])]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, norm_adjointImaginary]
    have b1 : |cellPartition S (baseSite x) z - cellPartition S (baseSite (x + unitStep j i)) z| ≤
        partitionBound * levelScale F j := by
      have hr : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
      have := abs_cellPartition_sub_le h.ambient h.odd hr s1 s2 (supClose_baseSite_bond hj x i) z
      rwa [zpow_div_pow_top_eq_levelScale h.odd.pos hj] at this
    have b2 := norm_imaginaryOfUnit_le (gaugeChange (Γ z) (Γ z₀) j (x + unitStep j i))
    have e2 : targetChange (Γ z) (Γ z₀) (Sum.inl ⟨j, x, i⟩) * partitionScale F (Sum.inl ⟨j, x, i⟩) =
        _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z) (Γ z₀) j (x + unitStep j i)) * (partitionBound * levelScale F j * 1) := rfl
    rw [e2, mul_one, mul_comm]
    exact mul_le_mul b2 b1 (abs_nonneg _) (distFromOne_nonneg _)
  · have hj : j + 1 ≤ F.top := hlev
    have e1 : correctionOf S A W kW Γ z₀ (Sum.inr ⟨j, y⟩) = correctionOf S A W kW Γ z₀ (slotOfLink j y) := rfl
    rw [e1, correctionOf_link hj, norm_zero]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (targetChange_nonneg _ _ _) (partitionScale_nonneg h _)
omit h in
theorem norm_imaginaryOfUnit_gaugeChange_three_le (Γ₁ Γ₂ Γ₃ : F.SiteGauge) {j : ℕ} (x : F.Site j) :
    ‖(imaginaryOfUnit (gaugeChange Γ₁ Γ₂ j x) - imaginaryOfUnit (gaugeChange Γ₁ Γ₃ j x) -
        imaginaryOfUnit (gaugeChange Γ₃ Γ₂ j x) : imaginaryQuaternions)‖ ≤
      _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ₁ Γ₃ j x) * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange Γ₃ Γ₂ j x) := by
  have e : gaugeChange Γ₁ Γ₂ j x = gaugeChange Γ₁ Γ₃ j x * gaugeChange Γ₃ Γ₂ j x := by
    unfold gaugeChange
    group
  rw [e]
  exact norm_imaginaryOfUnit_mul_sub_le _ _
theorem norm_correctionOf_sub_le {t : F.ActionTerm} (ht : t ∈ actionTerms S) {u : VariationSlot F}
    (hu : ReadsSlot t u) (z₀ z₁ : F.Cell)
    (hs1 : ∑ z ∈ A, cellPartition S (slotStart u) z = 1) (hs2 : ∑ z ∈ A, cellPartition S (slotEnd u) z = 1) :
    ‖(correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁) u‖ ≤
      ∑ z ∈ cellsNearTerm A t, targetChange (Γ z₁) (Γ z₀) u *
        scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u := by
  have hlev := slotEndLevel_le_top_of_readsSlot ht hu
  obtain ⟨w1, w2, s1, s2⟩ := supClose_of_readsSlot h.odd ht hu
  rcases u with ⟨j, x, i⟩ | ⟨j, y⟩
  · have hj : j ≤ F.top := hlev
    have hs1' : ∑ z ∈ A, cellPartition S (baseSite x) z = 1 := hs1
    have hs2' : ∑ z ∈ A, cellPartition S (baseSite (x + unitStep j i)) z = 1 := hs2
    set x' := x + unitStep j i with hx'
    set δ : F.Cell → ℝ := fun z => cellPartition S (baseSite x) z - cellPartition S (baseSite x') z with hδ
    set ad : imaginaryQuaternions → imaginaryQuaternions := adjointImaginary (W j x i) with had
    set ξ : F.Cell → F.Cell → imaginaryQuaternions :=
      fun z z' => imaginaryOfUnit (gaugeChange (Γ z) (Γ z') j x') with hξ
    have hz : ∑ z ∈ A, δ z = 0 := by
      simp only [hδ, Finset.sum_sub_distrib, hs1', hs2', sub_self]
    have e : (correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁) (slotOfBond j x i) =
        ∑ z ∈ A, δ z • ad (ξ z z₀ - ξ z z₁ - ξ z₁ z₀) := by
      have e1 : ∀ z, δ z • ad (ξ z z₀ - ξ z z₁ - ξ z₁ z₀) =
          δ z • ad (ξ z z₀) - δ z • ad (ξ z z₁) - δ z • ad (ξ z₁ z₀) := by
        intro z
        have adsub : ∀ v w : imaginaryQuaternions, ad (v - w) = ad v - ad w :=
          fun v w => adjointImaginary_sub _ v w
        rw [adsub, adsub, smul_sub, smul_sub]
      simp only [e1, Finset.sum_sub_distrib, ← Finset.sum_smul, hz, zero_smul, sub_zero]
      rw [Pi.sub_apply, correctionOf_bond, correctionOf_bond]
    have e' : (correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁) (Sum.inl ⟨j, x, i⟩) =
        (correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁) (slotOfBond j x i) := rfl
    rw [e', e, sum_cellsNearTerm (t := t) _ (fun z _ hd => by
      have a1 : cellPartition S (baseSite x) z = 0 := cellPartition_eq_zero_of_far h.ambient h.odd ht w1 hd
      have a2 : cellPartition S (baseSite x') z = 0 := cellPartition_eq_zero_of_far h.ambient h.odd ht w2 hd
      simp only [hδ, a1, a2, sub_zero, zero_smul])]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, norm_adjointImaginary]
    have b1 : |δ z| ≤ partitionBound * levelScale F j := by
      have hr : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
      have := abs_cellPartition_sub_le h.ambient h.odd hr s1 s2 (supClose_baseSite_bond hj x i) z
      rwa [zpow_div_pow_top_eq_levelScale h.odd.pos hj] at this
    have b2 := norm_imaginaryOfUnit_gaugeChange_three_le (Γ z) (Γ z₀) (Γ z₁) x'
    have e2 : targetChange (Γ z₁) (Γ z₀) (Sum.inl ⟨j, x, i⟩) *
        scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) (Sum.inl ⟨j, x, i⟩) =
          _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z₁) (Γ z₀) j x') *
            (partitionBound * levelScale F j * _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z) (Γ z₁) j x')) := rfl
    rw [e2]
    have p1 := distFromOne_nonneg (gaugeChange (Γ z₁) (Γ z₀) j x')
    have p2 := distFromOne_nonneg (gaugeChange (Γ z) (Γ z₁) j x')
    calc _ ≤ (partitionBound * levelScale F j) * (_root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z) (Γ z₁) j x') *
            _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (gaugeChange (Γ z₁) (Γ z₀) j x')) :=
          mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg partitionBound_pos.le (levelScale_nonneg F j))
      _ = _ := by ring
  · have hj : j + 1 ≤ F.top := hlev
    have e1 : (correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁) (Sum.inr ⟨j, y⟩) =
        correctionOf S A W kW Γ z₀ (slotOfLink j y) - correctionOf S A W kW Γ z₁ (slotOfLink j y) := rfl
    rw [e1, correctionOf_link hj, correctionOf_link hj, sub_zero, norm_zero]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (targetChange_nonneg _ _ _)
      (scaledBondWeight_nonneg partitionBound_pos.le (targetChange_nonneg _ _) _)
omit h in
theorem bondSum_add (g g' : F.Site j → Fin 4 → ℝ) (x : F.Site j) (l : List PathStep) :
    bondSum (fun x i => g x i + g' x i) x l = bondSum g x l + bondSum g' x l := by
  induction l generalizing x with
  | nil => simp [bondSum]
  | cons st r ih =>
    simp only [bondSum, ih]
    split_ifs <;> ring
omit h in
theorem contourBondSum_add (g g' : F.Site j → Fin 4 → ℝ) (d : F.Site (j + 1) × Fin 4) :
    contourBondSum (fun x i => g x i + g' x i) d = contourBondSum g d + contourBondSum g' d := by
  unfold contourBondSum
  simp only [bondSum_add, Finset.sum_add_distrib, mul_add]
omit h in
theorem farWeight_add (g g' : VariationSlot F → ℝ) (t : F.ActionTerm) :
    farWeight (fun u => g u + g' u) t = farWeight g t + farWeight g' t := by
  rcases t with p | d
  · exact bondSum_add (restrictToBonds g 0) (restrictToBonds g' 0) _ _
  · simp only [farWeight]
    have : restrictToBonds (fun u => g u + g' u) d.1 =
        fun x i => restrictToBonds g d.1 x i + restrictToBonds g' d.1 x i := rfl
    rw [this, contourBondSum_add]
    ring
omit h in
theorem farWeight_zero (t : F.ActionTerm) : farWeight (fun _ : VariationSlot F => (0 : ℝ)) t = 0 := by
  have := farWeight_const_mul (0 : ℝ) (fun _ : VariationSlot F => (0 : ℝ)) t
  simpa using this
omit h in
theorem farContribution_sum {ι : Type} (s : Finset ι) (g : ι → VariationSlot F → ℝ) (t : F.ActionTerm) :
    farContribution a W kW (fun u => ∑ i ∈ s, g i u) t = ∑ i ∈ s, farContribution a W kW (g i) t := by
  classical
  unfold farContribution
  induction s using Finset.induction_on with
  | empty =>
    simp [farWeight_zero]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [farWeight_add, mul_add, ih]
theorem actionForms_changeVariation {t : F.ActionTerm} (ht : t ∈ actionTerms S) {z z₀ : F.Cell} (hz : z ∈ A)
    (hz₀ : z₀ ∈ A) : actionForms a W kW t (changeVariation W kW Γ z z₀) = 0 := by
  have h1 : ∀ y, gaugeChangeRates (Γ z) (Γ z₀) F.top y = 0 := by
    intro y
    apply Subtype.ext
    show pureComponent _ = _
    rw [h.gaugeChange_top hz hz₀ y]
    exact pureComponent_one
  show actionTermRate a W kW (variationOfSlots (slotValues _)) t = 0
  rw [variationOfSlots_slotValues]
  exact actionTermRate_gaugeVariation h.covariance h.odd.pos W kW _ h1 ht (h.averages_ne_zero t ht)
theorem actionForms_scaledChangeVariation {t : F.ActionTerm} (ht : t ∈ actionTerms S) {z z₀ : F.Cell}
    (hz : z ∈ A) (hz₀ : z₀ ∈ A) : actionForms a W kW t (scaledChangeVariation S W kW Γ z z₀) = 0 := by
  have h1 : ∀ y, scaledRates (fun x => cellPartition S x z) (gaugeChangeRates (Γ z) (Γ z₀)) F.top y = 0 := by
    intro y
    have : gaugeChangeRates (Γ z) (Γ z₀) F.top y = 0 := by
      apply Subtype.ext
      show pureComponent _ = _
      rw [h.gaugeChange_top hz hz₀ y]
      exact pureComponent_one
    show _ • gaugeChangeRates (Γ z) (Γ z₀) F.top y = 0
    rw [this, smul_zero]
  show actionTermRate a W kW (variationOfSlots (slotValues _)) t = 0
  rw [variationOfSlots_slotValues]
  exact actionTermRate_gaugeVariation h.covariance h.odd.pos W kW _ h1 ht (h.averages_ne_zero t ht)
theorem abs_termPartition_le_one {t : F.ActionTerm} {z : F.Cell} (hz : z ∈ A) : |termPartition S z t| ≤ 1 := by
  unfold termPartition
  rw [abs_of_nonneg (cellPartition_nonneg _ _)]
  exact cellPartition_le_one _ (h.subset hz)
theorem termPartition_eq_zero_of_far {t : F.ActionTerm} (ht : t ∈ actionTerms S) {z : F.Cell}
    (hd : ¬ cellSupDist z (actionTermCell t) ≤ 4) : termPartition S z t = 0 := by
  have hr : (0 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t := by positivity
  exact cellPartition_eq_zero_of_far h.ambient h.odd ht (SupClose.refl hr _) hd
def termDefectConstant (F : BlockFrame) : ℝ := partitionBound * (2 * F.blockSide)
theorem termDefectConstant_nonneg : 0 ≤ termDefectConstant F :=
  mul_nonneg partitionBound_pos.le (by positivity)
theorem abs_residual_le {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    |residual A (actionForms a W kW) (slotPartition S) (termPartition S) (framingVariation W kW X k Γ)
        (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * (∑ z ∈ cellsNearTerm A t, farContribution a W kW (framingDefect W kW X k Γ z) t +
        ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
          (fun u => 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) t +
        ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
          (fun u => targetChange (Γ z) (Γ z₀) u * partitionScale F u) t) := by
  classical
  have hNA : cellsNearTerm A t ⊆ A := Finset.filter_subset _ _
  rw [residual_invariantCorrection_eq (fun z hz z₀ hz₀ => h.actionForms_changeVariation ht hz hz₀)
    (fun z hz z₀ hz₀ => h.actionForms_scaledChangeVariation ht hz hz₀)]
  have t1 : |∑ z ∈ A, actionForms a W kW t (weighted (weightGap (slotPartition S) (termPartition S) z t)
      (framingVariation W kW X k Γ z))| ≤
      termDefectConstant F * ∑ z ∈ cellsNearTerm A t, farContribution a W kW (framingDefect W kW X k Γ z) t := by
    rw [sum_cellsNearTerm (t := t) _ (fun z _ hd =>
      actionTermRateLinear_weighted_eq_zero_of_far h.ambient h.odd h.coupling_nonneg ht hd _), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    exact abs_actionTermRateLinear_weighted_le h.ambient h.odd h.coupling_nonneg ht z _
      (framingDefect_nonneg h z) fun u _ => norm_framingVariation_le z u
  have t2 : |∑ z₀ ∈ A, termPartition S z₀ t * ∑ z ∈ A, actionForms a W kW t
      (weighted (weightGap (slotPartition S) (termPartition S) z t) (changeVariation W kW Γ z z₀))| ≤
      termDefectConstant F * ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
        (fun u => 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) t := by
    rw [sum_cellsNearTerm (t := t) _ (fun z₀ _ hd => by rw [h.termPartition_eq_zero_of_far ht hd, zero_mul]),
      Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ hz₀ => ?_)
    rw [abs_mul, sum_cellsNearTerm (t := t) _ (fun z _ hd =>
      actionTermRateLinear_weighted_eq_zero_of_far h.ambient h.odd h.coupling_nonneg ht hd _), Finset.mul_sum]
    refine (mul_le_of_le_one_left (abs_nonneg _) (h.abs_termPartition_le_one (hNA hz₀))).trans ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    exact abs_actionTermRateLinear_weighted_le h.ambient h.odd h.coupling_nonneg ht z _
      (fun u => mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u)))
      fun u _ => norm_changeVariation_le z z₀ u
  have t3 : |∑ z₀ ∈ A, actionForms a W kW t (weighted (weightGap (slotPartition S) (termPartition S) z₀ t)
      (correctionOf S A W kW Γ z₀))| ≤
      termDefectConstant F * ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
        (fun u => targetChange (Γ z) (Γ z₀) u * partitionScale F u) t := by
    rw [sum_cellsNearTerm (t := t) _ (fun z _ hd =>
      actionTermRateLinear_weighted_eq_zero_of_far h.ambient h.odd h.coupling_nonneg ht hd _), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ _ => ?_)
    rw [← farContribution_sum]
    exact abs_actionTermRateLinear_weighted_le h.ambient h.odd h.coupling_nonneg ht z₀ _
      (fun u => Finset.sum_nonneg fun z _ => mul_nonneg (targetChange_nonneg _ _ u) (partitionScale_nonneg h u))
      fun u hu => h.norm_correctionOf_le ht hu z₀
  refine (abs_add_le _ _).trans ?_
  rw [mul_add, mul_add]
  refine add_le_add ((abs_sub _ _).trans (add_le_add t1 t2)) t3
theorem sum_cellPartition_eq_one {t : F.ActionTerm} (ht : t ∈ actionTerms S)
    (hin : ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A) {x : F.Site 0} (hx : x ∈ sitesOfCells S 0)
    (hw : SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t) (actionTermSite t) x) :
    ∑ z ∈ A, cellPartition S x z = 1 := by
  rw [← sum_cellPartition h.ambient h.odd hx]
  refine Finset.sum_subset h.subset fun y hy hn => ?_
  exact cellPartition_eq_zero_of_far h.ambient h.odd ht hw fun hd => hn (hin y hy hd)
theorem abs_residual_le_of_inner {t : F.ActionTerm} (ht : t ∈ actionTerms S)
    (hin : ∀ y ∈ S, cellSupDist y (actionTermCell t) ≤ 4 → y ∈ A) (z₁ : F.Cell) :
    |residual A (actionForms a W kW) (slotPartition S) (termPartition S) (framingVariation W kW X k Γ)
        (correctionOf S A W kW Γ) t| ≤
      termDefectConstant F * (∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
          (fun u => changeWeight W kW (Γ z) (Γ z₀) u *
            (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u))) t +
        ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
          (fun u => targetChange (Γ z₁) (Γ z₀) u *
            scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u) t) := by
  classical
  have hNA : cellsNearTerm A t ⊆ A := Finset.filter_subset _ _
  have hT : ∑ z ∈ A, termPartition S z t = 1 := by
    have hr : (0 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t := by positivity
    exact h.sum_cellPartition_eq_one ht hin (actionTermSite_mem h.odd ht) (SupClose.refl hr _)
  have e := residual_invariantCorrection_eq_of_partition (A := A) (l := actionForms a W kW) (φ := slotPartition S)
    (φt := termPartition S) (Y := framingVariation W kW X k Γ) (G := changeVariation W kW Γ)
    (H := scaledChangeVariation S W kW Γ) (R := ReadsSlot t)
    (fun z hz z₀ hz₀ => h.actionForms_changeVariation ht hz hz₀)
    (fun z hz z₀ hz₀ => h.actionForms_scaledChangeVariation ht hz hz₀)
    (fun V hV => actionTermRateLinear_eq_zero h.odd h.coupling_nonneg W kW hV)
    (fun u hu => h.sum_cellPartition_eq_one ht hin (supClose_of_readsSlot h.odd ht hu).2.2.1
      (supClose_of_readsSlot h.odd ht hu).1) hT z₁
  rw [e]
  have t1 : |∑ z₀ ∈ A, termPartition S z₀ t * ∑ z ∈ A, actionForms a W kW t
      (weighted (weightGap (slotPartition S) (termPartition S) z t)
        (framingVariation W kW X k Γ z - framingVariation W kW X k Γ z₀ - changeVariation W kW Γ z z₀))| ≤
      termDefectConstant F * ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
        (fun u => changeWeight W kW (Γ z) (Γ z₀) u *
          (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u))) t := by
    rw [sum_cellsNearTerm (t := t) _ (fun z₀ _ hd => by rw [h.termPartition_eq_zero_of_far ht hd, zero_mul]),
      Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ hz₀ => ?_)
    rw [abs_mul, sum_cellsNearTerm (t := t) _ (fun z _ hd =>
      actionTermRateLinear_weighted_eq_zero_of_far h.ambient h.odd h.coupling_nonneg ht hd _), Finset.mul_sum]
    refine (mul_le_of_le_one_left (abs_nonneg _) (h.abs_termPartition_le_one (hNA hz₀))).trans ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    exact abs_actionTermRateLinear_weighted_le h.ambient h.odd h.coupling_nonneg ht z _
      (fun u => mul_nonneg (changeWeight_nonneg W kW _ _ u)
        (mul_nonneg (by norm_num) (add_nonneg (framingDefect_nonneg h z u) (framingDefect_nonneg h z₀ u))))
      fun u _ => norm_framingVariation_sub_sub_le z z₀ u
  have t2 : |∑ z₀ ∈ A, actionForms a W kW t (weighted (weightGap (slotPartition S) (termPartition S) z₀ t)
      (correctionOf S A W kW Γ z₀ - correctionOf S A W kW Γ z₁))| ≤
      termDefectConstant F * ∑ z₀ ∈ cellsNearTerm A t, ∑ z ∈ cellsNearTerm A t, farContribution a W kW
        (fun u => targetChange (Γ z₁) (Γ z₀) u *
          scaledBondWeight partitionBound (targetChange (Γ z) (Γ z₁)) u) t := by
    rw [sum_cellsNearTerm (t := t) _ (fun z _ hd =>
      actionTermRateLinear_weighted_eq_zero_of_far h.ambient h.odd h.coupling_nonneg ht hd _), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ _ => ?_)
    rw [← farContribution_sum]
    exact abs_actionTermRateLinear_weighted_le h.ambient h.odd h.coupling_nonneg ht z₀ _
      (fun u => Finset.sum_nonneg fun z _ => mul_nonneg (targetChange_nonneg _ _ u)
        (scaledBondWeight_nonneg partitionBound_pos.le (targetChange_nonneg _ _) u))
      fun u hu => h.norm_correctionOf_sub_le ht hu z₀ z₁
        (h.sum_cellPartition_eq_one ht hin (supClose_of_readsSlot h.odd ht hu).2.2.1
          (supClose_of_readsSlot h.odd ht hu).1)
        (h.sum_cellPartition_eq_one ht hin (supClose_of_readsSlot h.odd ht hu).2.2.2
          (supClose_of_readsSlot h.odd ht hu).2.1)
  refine (abs_add_le _ _).trans ?_
  rw [mul_add]
  exact add_le_add t1 t2
end GluedFirstOrderData
end YangMills.Construction.BlockAverages.VariationRates
end
