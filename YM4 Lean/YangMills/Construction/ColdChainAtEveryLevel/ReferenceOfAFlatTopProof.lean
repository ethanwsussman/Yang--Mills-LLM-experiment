import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceOfAFlatTop
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace FlatTopReference
variable {F : BlockFrame}
theorem pathHolonomy_flatTopField (x : F.Site F.top) (l : List PathStep) :
    pathHolonomy (flatTopField : F.GaugeField F.top) x l = 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hs : linkValue (flatTopField : F.GaugeField F.top) x st = 1 := by
      unfold linkValue flatTopField
      split_ifs <;> simp
    simp only [pathHolonomy, hs, ih, one_mul]
theorem cellParallelTransport_flatTopField (S : Finset F.Cell) (y y' : F.Cell) :
    cellParallelTransport S (flatTopField : F.GaugeField F.top) y y' = 1 :=
  pathHolonomy_flatTopField _ _
def rankOneImage (S : Finset F.Cell) (x : F.Site 0) (f : F.Cell → ℍ[ℝ]) : ℍ[ℝ] :=
  ∑ y' ∈ S, ∑ y'' ∈ S, (cellPartition S x y' * Real.sqrt (cellPartition S x y'')) • f y''
theorem localizationOperator_flatTopField (S : Finset F.Cell) (x : F.Site 0) (f : F.Cell → ℍ[ℝ])
    (y : F.Cell) :
    localizationOperator S flatTopField x f y =
      Real.sqrt (cellPartition S x y) • rankOneImage S x f := by
  unfold localizationOperator rankOneImage
  simp only [cellParallelTransport_flatTopField, inv_one, OneMemClass.coe_one, mul_one, one_mul,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y'' _ => ?_
  congr 1
  ring
def IsNonnegReal (q : ℍ[ℝ]) : Prop := ∃ t : ℝ, 0 ≤ t ∧ q = (t : ℍ[ℝ])
theorem smul_mul_smul_star (A B C : ℝ) (T : ℍ[ℝ]) :
    (A • T) * (B • (C • star T)) = ((A * B * C * Quaternion.normSq T : ℝ) : ℍ[ℝ]) := by
  rw [smul_mul_assoc, mul_smul_comm, mul_smul_comm, Quaternion.self_mul_star, smul_smul, smul_smul,
    Quaternion.smul_coe]
theorem leadingFrame_isNonnegReal (S : Finset F.Cell) (x : F.Site 0)
    (hpos : 0 < cellPartition S x (enclosingCell x)) (hz : enclosingCell x ∈ S) {y : F.Cell}
    (hy : y ∈ S) : IsNonnegReal (leadingFrame S flatTopField x y) := by
  classical
  unfold leadingFrame
  by_cases hc : ∃ y ∈ S, x = cellCentre 0 y
  · rw [dif_pos hc]
    by_cases hy' : y = hc.choose
    · show IsNonnegReal (if y = hc.choose then (1 : ℍ[ℝ]) else 0)
      rw [if_pos hy']
      exact ⟨1, zero_le_one, by simp⟩
    · show IsNonnegReal (if y = hc.choose then (1 : ℍ[ℝ]) else 0)
      rw [if_neg hy']
      exact ⟨0, le_rfl, by simp⟩
  rw [dif_neg hc]
  by_cases h : ∃ f, IsLeadingEigenvector S flatTopField x f
  · rw [dif_pos h]
    set f := h.choose with hf
    show IsNonnegReal (f y * (((polarUnit (f (enclosingCell x)))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    obtain ⟨hnorm, l, hl, heq⟩ := h.choose_spec
    have hl0 : 0 < l := by linarith
    set T := rankOneImage S x f with hT
    have hfy : ∀ y' ∈ S, f y' = (Real.sqrt (cellPartition S x y') / l) • T := by
      intro y' hy'
      have := heq y' hy'
      rw [localizationOperator_flatTopField] at this
      rw [div_eq_inv_mul, mul_smul, this, smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
    have hT0 : T ≠ 0 := by
      intro h0
      have : ∑ y ∈ S, ‖f y‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun y' hy' => ?_
        rw [hfy y' hy', h0]
        simp
      rw [this] at hnorm
      norm_num at hnorm
    have hsq : 0 < Real.sqrt (cellPartition S x (enclosingCell x)) / l := by positivity
    have hfz : f (enclosingCell x) ≠ 0 := by
      rw [hfy _ hz]
      exact smul_ne_zero hsq.ne' hT0
    have hunit : (((polarUnit (f (enclosingCell x)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        ‖f (enclosingCell x)‖⁻¹ • star (f (enclosingCell x)) := by
      rw [coe_unitQuaternion_inv, coe_polarUnit hfz, quaternion_star_real_smul]
    rw [hunit, hfy y hy, hfy _ hz, quaternion_star_real_smul]
    refine ⟨_, ?_, smul_mul_smul_star (Real.sqrt (cellPartition S x y) / l)
      (‖(Real.sqrt (cellPartition S x (enclosingCell x)) / l) • T‖⁻¹)
      (Real.sqrt (cellPartition S x (enclosingCell x)) / l) T⟩
    exact mul_nonneg (by positivity) Quaternion.normSq_nonneg
  · rw [dif_neg h]
    exact ⟨0, le_rfl, by simp⟩
theorem polarUnit_quaternionPairing (S : Finset F.Cell) (f g : F.Cell → ℍ[ℝ])
    (hf : ∀ y ∈ S, IsNonnegReal (f y)) (hg : ∀ y ∈ S, IsNonnegReal (g y)) :
    polarUnit (quaternionPairing S f g) = 1 := by
  classical
  have h : ∃ t : ℝ, 0 ≤ t ∧ quaternionPairing S f g = (t : ℍ[ℝ]) := by
    unfold quaternionPairing
    induction S using Finset.induction_on with
    | empty => exact ⟨0, le_rfl, by simp⟩
    | insert y s hy ih =>
      obtain ⟨t, ht, e⟩ := ih (fun y' h' => hf y' (Finset.mem_insert_of_mem h'))
        (fun y' h' => hg y' (Finset.mem_insert_of_mem h'))
      obtain ⟨a, ha, ea⟩ := hf y (Finset.mem_insert_self _ _)
      obtain ⟨b, hb, eb⟩ := hg y (Finset.mem_insert_self _ _)
      refine ⟨a * b + t, by positivity, ?_⟩
      rw [Finset.sum_insert hy, e, ea, eb, Quaternion.star_coe]
      push_cast
      rfl
  obtain ⟨t, ht, e⟩ := h
  rw [e]
  rcases ht.lt_or_eq with h | h
  · exact polarUnit_coe h
  · rw [← h]
    simp [polarUnit]
theorem enclosingCell_baseSite (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) :
    enclosingCell (baseSite x) = enclosingCell x := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.enclosingCell_baseSite <;> assumption
theorem cellPartition_enclosingCell_pos (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (S : Finset F.Cell) (x : F.Site 0) (hz : enclosingCell x ∈ S) :
    0 < cellPartition S x (enclosingCell x) := by
  have hx : x ∈ sitesOfCells {enclosingCell x} 0 :=
    (LumpContours.BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2
      (Finset.mem_singleton_self _)
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  have hb : cellCutoff x (enclosingCell x) = 1 := by
    have hb0 : cellCutoff x y = 1 := by
      rw [e]
      exact cellCutoff_self hamb hL y (by simpa using hh)
    rwa [Finset.mem_singleton.1 hy] at hb0
  unfold cellPartition
  rw [hb]
  refine div_pos (by norm_num) (lt_of_lt_of_le ?_
    (Finset.single_le_sum (f := fun y' => cellCutoff x y' ^ 2) (fun _ _ => sq_nonneg _) hz))
  simp [hb]
end FlatTopReference
theorem flatTopReferenceStatement_holds : flatTopReferenceStatement := by
  intro F S j x i hL hamb hj h1 h2
  rcases hj.lt_or_eq with hlt | rfl
  · have hne : j ≠ F.top := hlt.ne
    have e : referenceFieldChain S flatTopField j x i = referenceGaugeField S flatTopField j x i := by
      unfold referenceFieldChain
      simp [Function.update_of_ne hne]
    rw [e]
    unfold referenceGaugeField
    have z1 : enclosingCell (baseSite x) ∈ S := by
      rwa [FlatTopReference.enclosingCell_baseSite hL hj]
    have z2 : enclosingCell (baseSite (x + unitStep j i)) ∈ S := by
      rwa [FlatTopReference.enclosingCell_baseSite hL hj]
    exact FlatTopReference.polarUnit_quaternionPairing S _ _
      (fun y hy => FlatTopReference.leadingFrame_isNonnegReal S _
        (FlatTopReference.cellPartition_enclosingCell_pos hamb hL S _ z1) z1 hy)
      (fun y hy => FlatTopReference.leadingFrame_isNonnegReal S _
        (FlatTopReference.cellPartition_enclosingCell_pos hamb hL S _ z2) z2 hy)
  · unfold referenceFieldChain
    simp [flatTopField]
end YangMills.Construction.BlockAverages
end
