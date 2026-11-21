import YangMills.Construction.ColdChainAtEveryLevel.ChangesOnARegion
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesOfTheShares
import YangMills.Construction.ColdChainAtEveryLevel.GluedFirstOrders
import YangMills.Construction.ColdChainAtEveryLevel.TermsNearSomeCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open PatchLocality ChartCoordinates YangMills.Construction.PartitionGluing YangMills.Construction.EvaluationSums
  YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.FiniteDifferences
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
theorem bondSum_const_mul (c : ℝ) (g : F.Site j → Fin 4 → ℝ) (x : F.Site j) (l : List PathStep) :
    bondSum (fun x i => c * g x i) x l = c * bondSum g x l := by
  induction l generalizing x with
  | nil => simp [bondSum]
  | cons st r ih =>
    simp only [bondSum, ih, mul_add]
    split_ifs <;> rfl
theorem contourBondSum_const_mul (c : ℝ) (g : F.Site j → Fin 4 → ℝ) (d : F.Site (j + 1) × Fin 4) :
    contourBondSum (fun x i => c * g x i) d = c * contourBondSum g d := by
  unfold contourBondSum
  simp only [bondSum_const_mul, ← Finset.mul_sum]
  ring
theorem farWeight_const_mul (c : ℝ) (g : VariationSlot F → ℝ) (t : F.ActionTerm) :
    farWeight (fun u => c * g u) t = c * farWeight g t := by
  rcases t with p | d
  · exact bondSum_const_mul c (restrictToBonds g 0) _ _
  · simp only [farWeight]
    have : restrictToBonds (fun u => c * g u) d.1 = fun x i => c * restrictToBonds g d.1 x i := rfl
    rw [this, contourBondSum_const_mul]
    ring
theorem farWeight_mono {g g' : VariationSlot F → ℝ} (t : F.ActionTerm) (h : ∀ u, ReadsSlot t u → g u ≤ g' u) :
    farWeight g t ≤ farWeight g' t := by
  rcases t with p | c
  · exact bondSum_mono _ _ fun b hb => h _ ⟨b, rfl, hb⟩
  · simp only [farWeight]
    refine add_le_add (h _ (Or.inr (Or.inl rfl))) ?_
    exact contourBondSum_mono _ fun a ha π b hb => h _ (Or.inr (Or.inr (Or.inr ⟨a, ha, π, b, rfl, hb⟩)))
def slotEndLevel : VariationSlot F → ℕ
  | Sum.inl b => b.1
  | Sum.inr c => c.1 + 1
theorem slotEndLevel_le_top_of_readsSlot {t : F.ActionTerm} (ht : t ∈ actionTerms S) {u : VariationSlot F}
    (hu : ReadsSlot t u) : slotEndLevel u ≤ F.top := by
  rcases t with p | ⟨j, c⟩
  · obtain ⟨b, rfl, -⟩ := hu
    exact Nat.zero_le _
  · have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)).1
    rcases hu with rfl | rfl | ⟨hlt, rfl⟩ | ⟨a, ha, π, b, rfl, -⟩
    · exact hj
    · exact hj
    · exact hlt.le
    · exact hj.le
theorem supClose_baseSite_bond {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) (i : Fin 4) :
    SupClose ((F.blockSide : ℤ) ^ j) (baseSite x) (baseSite (x + unitStep j i)) := by
  have hpow : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
  refine ⟨fun μ => (F.blockSide : ℤ) ^ j * basisVector i μ, fun μ => ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hpow]
    exact mul_le_of_le_one_right hpow (abs_basisVector_le i μ)
  · rw [unitStep_eq, baseSite_add j hj]
theorem zpow_div_pow_top_eq_levelScale (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) :
    (((F.blockSide : ℤ) ^ j : ℤ) : ℝ) / (F.blockSide : ℝ) ^ F.top = _root_.YangMills.Construction.EvaluationSums.levelScale F j := by
  unfold _root_.YangMills.Construction.EvaluationSums.levelScale
  have e : F.top = j + (F.top - j) := by omega
  push_cast
  conv_lhs => rw [e, pow_add]
  rw [one_div, inv_pow]
  have h1 : (F.blockSide : ℝ) ^ j ≠ 0 := by positivity
  have h2 : (F.blockSide : ℝ) ^ (F.top - j) ≠ 0 := by positivity
  field_simp
section Data
variable (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge) (Γ : F.Cell → F.SiteGauge) (S)
def framingVariation (z : F.Cell) : VariationSlot F → imaginaryQuaternions := gaugeSlots W kW X k (Γ z)
def changeVariation (z z₀ : F.Cell) : VariationSlot F → imaginaryQuaternions :=
  slotValues (gaugeVariation W kW (gaugeChangeRates (Γ z) (Γ z₀)))
def slotPartition (z : F.Cell) : VariationSlot F → ℝ := fun u => cellPartition S (slotStart u) z
def termPartition (z : F.Cell) (t : F.ActionTerm) : ℝ := cellPartition S (actionTermSite t) z
def scaledChangeVariation (z z₀ : F.Cell) : VariationSlot F → imaginaryQuaternions :=
  slotValues (gaugeVariation W kW (scaledRates (fun x => cellPartition S x z) (gaugeChangeRates (Γ z) (Γ z₀))))
def framingDefect (z : F.Cell) : VariationSlot F → ℝ := fun u => _root_.YangMills.Construction.BlockAverages.VariationRates.distFromOne (slotDefect W kW X k (Γ z) u)
end Data
section Forms
variable {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k : F.SiteGauge} {Γ : F.Cell → F.SiteGauge}
theorem norm_framingVariation_le (z : F.Cell) (u : VariationSlot F) :
    ‖framingVariation W kW X k Γ z u‖ ≤ framingDefect W kW X k Γ z u :=
  norm_imaginaryOfUnit_le _
theorem changeVariation_eq (z z₀ : F.Cell) (u : VariationSlot F) : changeVariation W kW Γ z z₀ u =
    imaginaryOfUnit (slotSourceChange (Γ z) (Γ z₀) u) - imaginaryOfUnit (slotTargetChange W kW (Γ z) (Γ z₀) u) :=
  slotValues_gaugeChange W kW (Γ z) (Γ z₀) u
theorem norm_changeVariation_le (z z₀ : F.Cell) (u : VariationSlot F) :
    ‖changeVariation W kW Γ z z₀ u‖ ≤ 3 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u) := by
  rw [changeVariation_eq]
  have h := norm_imaginaryOfUnit_sub_le (slotSourceChange (Γ z) (Γ z₀) u) (slotTargetChange W kW (Γ z) (Γ z₀) u)
    (slotDefect W kW X k (Γ z₀) u)
  rwa [← slotDefect_gaugeChange] at h
theorem norm_framingVariation_sub_sub_le (z z₀ : F.Cell) (u : VariationSlot F) :
    ‖(framingVariation W kW X k Γ z - framingVariation W kW X k Γ z₀ - changeVariation W kW Γ z z₀) u‖ ≤
      changeWeight W kW (Γ z) (Γ z₀) u * (2 * (framingDefect W kW X k Γ z u + framingDefect W kW X k Γ z₀ u)) := by
  have h := norm_imaginaryOfUnit_second_le (slotSourceChange (Γ z) (Γ z₀) u)
    (slotTargetChange W kW (Γ z) (Γ z₀) u) (slotDefect W kW X k (Γ z₀) u)
  rw [← slotDefect_gaugeChange] at h
  have e : (framingVariation W kW X k Γ z - framingVariation W kW X k Γ z₀ - changeVariation W kW Γ z z₀) u =
      imaginaryOfUnit (slotDefect W kW X k (Γ z) u) - imaginaryOfUnit (slotDefect W kW X k (Γ z₀) u) -
        (imaginaryOfUnit (slotSourceChange (Γ z) (Γ z₀) u) -
          imaginaryOfUnit (slotTargetChange W kW (Γ z) (Γ z₀) u)) := by
    rw [← changeVariation_eq]
    rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  unfold changeWeight framingDefect
  ring
end Forms
section OnTerms
variable {W : F.FieldChain} {kW : F.SiteGauge} {a : ℝ}
theorem abs_slotPartition_sub_termPartition_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {t : F.ActionTerm} (ht : t ∈ actionTerms S) {u : VariationSlot F} (hu : ReadsSlot t u) (z : F.Cell) :
    |slotPartition S z u - termPartition S z t| ≤
      (partitionBound * (2 * F.blockSide)) * _root_.YangMills.Construction.EvaluationSums.levelScale F (actionTermLevel t) := by
  obtain ⟨w1, -, s1, -⟩ := supClose_of_readsSlot hodd ht hu
  have hlev : actionTermLevel t ≤ F.top := by
    rcases t with p | ⟨j, c⟩
    · exact Nat.zero_le _
    · exact (Finset.mem_range.1 (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)).1).le
  have hr : (0 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t := by positivity
  have h := abs_cellPartition_sub_le hamb hodd hr (actionTermSite_mem hodd ht) s1 w1 z
  have e : (((2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t : ℤ)) : ℝ) /
      (F.blockSide : ℝ) ^ F.top = (2 * F.blockSide) * _root_.YangMills.Construction.EvaluationSums.levelScale F (actionTermLevel t) := by
    rw [← zpow_div_pow_top_eq_levelScale hodd.pos hlev]
    push_cast
    ring
  rw [e] at h
  unfold slotPartition termPartition
  rw [abs_sub_comm]
  refine h.trans (le_of_eq ?_)
  ring
theorem abs_actionTermRateLinear_weighted_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (ha : 0 ≤ a)
    {t : F.ActionTerm} (ht : t ∈ actionTerms S) (z : F.Cell) (V : VariationSlot F → imaginaryQuaternions)
    {g : VariationSlot F → ℝ} (hg0 : ∀ u, 0 ≤ g u) (hg : ∀ u, ReadsSlot t u → ‖V u‖ ≤ g u) :
    |actionTermRateLinear a W kW t (weighted (weightGap (slotPartition S) (termPartition S) z t) V)| ≤
      (partitionBound * (2 * F.blockSide)) * farContribution a W kW g t := by
  have hc : 0 ≤ partitionBound * (2 * (F.blockSide : ℝ)) * _root_.YangMills.Construction.EvaluationSums.levelScale F (actionTermLevel t) :=
    mul_nonneg (mul_nonneg partitionBound_pos.le (by positivity)) (levelScale_nonneg F _)
  refine (abs_actionTermRateLinear_le hodd ha W kW _ t).trans ?_
  have h1 : readWeight (fun u => ‖weighted (weightGap (slotPartition S) (termPartition S) z t) V u‖) t =
      farWeight (fun u => ‖weighted (weightGap (slotPartition S) (termPartition S) z t) V u‖) t := by
    refine readWeight_eq_farWeight t fun c hc' => ?_
    subst hc'
    constructor
    · simp only [weighted, weightGap]
      have : slotPartition S z (slotOfLink c.1 c.2.1) - termPartition S z (Sum.inr c) = 0 := sub_self _
      rw [this, zero_smul, norm_zero]
    · simp only [weighted, weightGap]
      have : slotPartition S z (slotOfBond (c.1 + 1) c.2.1 c.2.2) - termPartition S z (Sum.inr c) = 0 :=
        sub_self _
      rw [this, zero_smul, norm_zero]
  rw [h1]
  have h2 : farWeight (fun u => ‖weighted (weightGap (slotPartition S) (termPartition S) z t) V u‖) t ≤
      farWeight (fun u => (partitionBound * (2 * (F.blockSide : ℝ)) * _root_.YangMills.Construction.EvaluationSums.levelScale F (actionTermLevel t)) * g u) t := by
    refine farWeight_mono t fun u hu => ?_
    simp only [weighted, weightGap, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_slotPartition_sub_termPartition_le hamb hodd ht hu z) (hg u hu) (norm_nonneg _) hc
  rw [farWeight_const_mul] at h2
  unfold farContribution
  calc _ ≤ actionTermSize a W kW t *
        (partitionBound * (2 * (F.blockSide : ℝ)) * _root_.YangMills.Construction.EvaluationSums.levelScale F (actionTermLevel t) * farWeight g t) :=
        mul_le_mul_of_nonneg_left h2 (actionTermSize_nonneg ha W kW t)
    _ = _ := by ring
theorem cellPartition_eq_zero_of_far (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {t : F.ActionTerm}
    (ht : t ∈ actionTerms S) {x : F.Site 0}
    (hw : SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t) (actionTermSite t) x)
    {z : F.Cell} (hd : ¬ cellSupDist z (actionTermCell t) ≤ 4) : cellPartition S x z = 0 := by
  by_contra h0
  have hb := cellCutoff_ne_zero_of_cellPartition_ne_zero h0
  obtain ⟨-, h, hh, e⟩ := enclosingCell_actionTermSite hodd ht
  obtain ⟨δ, hδ, e2⟩ := SupClose.symm (SupClose.mono (scale_pow_actionTermLevel_le hodd ht) hw)
  apply hd
  exact cellSupDist_le_four_of_cellCutoff_ne_zero hamb hodd hb (δ := -(-δ)) (fun i => by simpa using hδ i) hh (by
    rw [neg_neg, ← e2]; exact e)
theorem actionTermRateLinear_weighted_eq_zero_of_far (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (ha : 0 ≤ a) {t : F.ActionTerm} (ht : t ∈ actionTerms S) {z : F.Cell}
    (hd : ¬ cellSupDist z (actionTermCell t) ≤ 4) (V : VariationSlot F → imaginaryQuaternions) :
    actionTermRateLinear a W kW t (weighted (weightGap (slotPartition S) (termPartition S) z t) V) = 0 := by
  refine actionTermRateLinear_eq_zero hodd ha W kW fun u hu => ?_
  have h1 : slotPartition S z u = 0 :=
    cellPartition_eq_zero_of_far hamb hodd ht (supClose_of_readsSlot hodd ht hu).1 hd
  have h2 : termPartition S z t = 0 := by
    have hr : (0 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t := by positivity
    exact cellPartition_eq_zero_of_far hamb hodd ht (SupClose.refl hr _) hd
  simp [weighted, weightGap, h1, h2]
end OnTerms
end YangMills.Construction.BlockAverages.VariationRates
end
