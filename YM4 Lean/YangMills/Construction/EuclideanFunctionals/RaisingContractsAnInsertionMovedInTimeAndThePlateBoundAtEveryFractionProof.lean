import YangMills.Construction.EuclideanFunctionals.ElementAboveAHeightAndItsPulledDownElement
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.EuclideanFunctionals.RaisingContractsAnInsertionMovedInTimeAndThePlateBoundAtEveryFraction
import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgreeProof
import YangMills.Construction.RotationInvariance.ChangingTheFractionOfThePlateBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.TimeShiftAndFractions
open AboveHeight (IsThinInsert)
theorem finCombIn_mono {O O' : Set R4} (h : O ⊆ O') :
    finCombIn O ≤ finCombIn O' := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.finCombIn_mono <;> assumption
theorem timeVec_three : timeVec 3 = 1 := by
  simp [PeriodicLattice.coordVec]
theorem transl_apply_three (a : ℝ) (x : R4) :
    (EuclidMotion.transl (a • timeVec) x) 3 = x 3 + a := by
  rw [EuclidMotion.transl_apply, Pi.add_apply, Pi.smul_apply, timeVec_three]
  simp
theorem isOpen_setOf_lt_time (c : ℝ) : IsOpen {x : R4 | c < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem actFree_transl_mem (hT : TupleRules.TupleSpanActionRules) {c : ℝ} (a : ℝ) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | c < x 3}) :
    (EuclidMotion.transl (a • timeVec)).actFree F ∈ finCombIn {x : R4 | c + a < x 3} := by
  obtain ⟨-, hImages, -⟩ := hT
  have h := (hImages (EuclidMotion.transl (a • timeVec)) {x | c < x 3} (isOpen_setOf_lt_time c)).2.2.mapsTo hF
  refine finCombIn_mono ?_ h
  rintro _ ⟨x, hx, rfl⟩
  have hx' : c < x 3 := hx
  show c + a < (EuclidMotion.transl (a • timeVec) x) 3
  rw [transl_apply_three]
  linarith
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
theorem actFree_transl_neg_transl (hT : TupleRules.TupleSpanActionRules) (t : ℝ) (A : FreeSep) :
    (EuclidMotion.transl ((-t) • timeVec)).actFree ((EuclidMotion.transl (t • timeVec)).actFree A) = A := by
  have hone : EuclidMotion.transl ((-t) • timeVec) * EuclidMotion.transl (t • timeVec) = 1 :=
    EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
        EuclidMotion.one_apply]
      module
  rw [(hT.2.2.1 _ _ A).1, hone, actFree_one]
theorem transl_neg_mul_timeFlip (a : ℝ) :
    EuclidMotion.transl ((-a) • timeVec) * timeFlip = timeFlip * EuclidMotion.transl (a • timeVec) :=
  EuclidMotion.ext_of_apply fun x => by
    have h3 : (x + a • timeVec) 3 = x 3 + a := transl_apply_three a x
    rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply, timeFlip_apply, timeFlip_apply, h3]
    module
theorem shiftUpContracts (hT : TupleRules.TupleSpanActionRules)
    (hPull : AboveHeight.Holds) {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) : ShiftUpContracts σ := by
  intro t ht A hA
  rcases ht.eq_or_lt with rfl | ht'
  · have hzero : EuclidMotion.transl ((0 : ℝ) • timeVec) = 1 :=
      EuclidMotion.ext_of_apply fun x => by
        rw [EuclidMotion.transl_apply, EuclidMotion.one_apply, zero_smul, add_zero]
    rw [hzero, actFree_one]
    exact ⟨hA, le_rfl⟩
  · have hF : (EuclidMotion.transl (t • timeVec)).actFree A ∈ finCombIn {x : R4 | t < x 3} := by
      have h := actFree_transl_mem hT (c := 0) t hA
      rwa [zero_add] at h
    obtain ⟨hmem, -, hle⟩ := (hPull m S σ t ht').1 _ hF
    refine ⟨hmem, ?_⟩
    have hback : pullDown t ((EuclidMotion.transl (t • timeVec)).actFree A) = A :=
      actFree_transl_neg_transl hT t A
    unfold heightNorm at hle
    rwa [hback] at hle
theorem heightNorm_actFree_transl_le (hT : TupleRules.TupleSpanActionRules)
    (hPull : AboveHeight.Holds) {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) {a c c' t : ℝ} (ht : 0 ≤ t)
    (hat : a - c' = t - c) {F : FreeSep} (hF : F ∈ finCombIn {x : R4 | c < x 3}) :
    heightNorm σ c' ((EuclidMotion.transl (a • timeVec)).actFree F) ≤ heightNorm σ c F := by
  have hG : pullDown c F ∈ finCombIn upperHalf := by
    refine finCombIn_mono ?_ (actFree_transl_mem hT (-c) hF)
    intro x hx
    have hx' : c + -c < x 3 := hx
    show 0 < x 3
    linarith
  have hAct := hT.2.2.1
  have hEq : pullDown c' ((EuclidMotion.transl (a • timeVec)).actFree F) =
      (EuclidMotion.transl (t • timeVec)).actFree (pullDown c F) := by
    unfold pullDown
    rw [(hAct _ _ F).1, (hAct _ _ F).1]
    congr 2
    refine EuclidMotion.ext_of_apply fun x => ?_
    rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      add_assoc, add_assoc, ← add_smul, ← add_smul]
    congr 2
    linarith
  unfold heightNorm
  rw [hEq]
  exact (shiftUpContracts hT hPull σ t ht _ hG).2
theorem insertion_eq_transl (hT : TupleRules.TupleSpanActionRules) {S : ConnFamily}
    (hInv : MomentSymmetry.MotionInvariant S) {c : ℝ}
    (hc : 0 < c) {F A : FreeSep} (hF : F ∈ finCombIn {x : R4 | c < x 3})
    (hA : A ∈ finCombIn {x : R4 | c < x 3}) {h : R4 → ℂ} (hh : IsThinInsert c h)
    (a : ℝ) :
    insertion S F h A =
      insertion S ((EuclidMotion.transl (a • timeVec)).actFree F)
        ((EuclidMotion.transl ((-a) • timeVec)).actFn h)
        ((EuclidMotion.transl ((-a) • timeVec)).actFree A) := by
  obtain ⟨-, -, hAct, -, -, hRules, hAssoc, hCx, -, hRefl, -, -⟩ := hT
  have h3 : TupleRules.MulDefined3 (flipConj F)
      (singleComponent h) A := hRefl.2 c hc F hF A hA h hh.1 hh.2
  have hdef := (hAssoc _ _ _ h3).1
  have h1 := (hRules (EuclidMotion.transl ((-a) • timeVec)) _ _ hdef).2.2.2.2
  have h2 := (hRules (EuclidMotion.transl ((-a) • timeVec)) _ _ h3.1).2.2.2.2
  have hθ : (EuclidMotion.transl ((-a) • timeVec)).actFree (flipConj F) =
      flipConj ((EuclidMotion.transl (a • timeVec)).actFree F) := by
    unfold flipConj
    rw [(hAct _ _ _).1, transl_neg_mul_timeFlip, (hAct (EuclidMotion.transl (a • timeVec)) timeFlip F).2.1,
      (hAct timeFlip (EuclidMotion.transl (a • timeVec)) (freeConj F)).1]
  have hone : (EuclidMotion.transl ((-a) • timeVec)).actFree (singleComponent h) =
      singleComponent ((EuclidMotion.transl ((-a) • timeVec)).actFn h) :=
    (hCx Set.univ isOpen_univ (EuclidMotion.transl ((-a) • timeVec)) 1 (fun _ => h)
      ⟨le_rfl, fun _ => hh.1, fun k l hkl => (hkl (Subsingleton.elim k l)).elim⟩
      (fun _ => Set.subset_univ _)).2.2.2.2.2.2.1
  unfold insertion freeMul3
  rw [← (hInv (freeMul (freeMul (flipConj F) (singleComponent h)) A)).1 ((-a) • timeVec), h1, h2,
    hθ, hone]
theorem insertionTimeShift (hT : TupleRules.TupleSpanActionRules)
    (hPull : AboveHeight.Holds) {m : SharpScale} {S : ConnFamily}
    (hInv : MomentSymmetry.MotionInvariant S)
    (σ : EuclidFunctionalWithRecon m S) : InsertionTimeShift σ := by
  intro c t hc ht F hF F' hF' h hh hsupp
  have hs : supp h ⊆ {x | |x 3| < c} := fun x hx => by
    have h1 : |x 3 - t| < c - |t| := hsupp hx
    have h2 := abs_sub_abs_le_abs_sub (x 3) t
    show |x 3| < c
    linarith
  have hmoved : supp ((EuclidMotion.transl ((-t) • timeVec)).actFn h) ⊆
      {x | |x 3| < c - |t|} := by
    rw [(hT.1 m (EuclidMotion.transl ((-t) • timeVec)) 1 h hh).2.2.2.2.1]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : |x 3 - t| < c - |t| := hsupp hx
    show |(EuclidMotion.transl ((-t) • timeVec) x) 3| < c - |t|
    rw [transl_apply_three, ← sub_eq_add_neg]
    exact h1
  have hF₁ : (EuclidMotion.transl (t • timeVec)).actFree F ∈ finCombIn {x : R4 | c - |t| < x 3} := by
    refine finCombIn_mono (fun x hx => ?_) (actFree_transl_mem hT t hF)
    have hx' : c + t < x 3 := hx
    show c - |t| < x 3
    linarith [neg_abs_le t]
  have hF₂ : (EuclidMotion.transl ((-t) • timeVec)).actFree F' ∈
      finCombIn {x : R4 | c - |t| < x 3} := by
    refine finCombIn_mono (fun x hx => ?_) (actFree_transl_mem hT (-t) hF')
    have hx' : c + -t < x 3 := hx
    show c - |t| < x 3
    linarith [le_abs_self t]
  exact ⟨hs, hmoved, hF₁, hF₂, insertion_eq_transl hT hInv hc hF hF' ⟨hh, hs⟩ t,
    heightNorm_actFree_transl_le hT hPull σ (t := t + |t|) (by linarith [neg_abs_le t]) (by ring) hF,
    heightNorm_actFree_transl_le hT hPull σ (t := |t| - t) (by linarith [le_abs_self t]) (by ring) hF'⟩
theorem rpow_neg_le_div_rpow {p c : ℝ} (hp : 0 < p) (hc : c ∈ productBoundFractions) :
    (1 - 4 * c) ^ (-p) ≤ (2 / (1 - 4 * c)) ^ p := by
  have hb : 0 < 1 - 4 * c := by
    have := hc.2
    linarith
  have hbp : 0 < (1 - 4 * c) ^ p := Real.rpow_pos_of_pos hb p
  have h2 : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) hp.le
  rw [Real.div_rpow (by norm_num) hb.le, Real.rpow_neg hb.le, div_eq_mul_inv]
  exact le_mul_of_one_le_left (inv_nonneg.2 hbp.le) h2
theorem productBoundHolds_fractionConstants {m : SharpScale} {S : ConnFamily}
    {σ : EuclidFunctionalWithRecon m S} {p cS c : ℝ}
    {C : (RealPlane → ℝ) → ℝ} (h : ProductBoundHolds σ p C cS)
    (hc : c ∈ productBoundFractions)
    (h' : ProductBoundHolds σ p
      (FractionChange.productConstantsAt p c C) c) :
    ProductBoundHolds σ p (fractionConstants p c C) c where
  pos_exponent := h.pos_exponent
  nonneg_constant φ hφ :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) (by have := hc.2; linarith)) _)
      (h.nonneg_constant φ hφ)
  pos_fraction := hc.1
  fraction_lt_quarter := hc.2
  le_bound η hη0 hη1 φ hφ α hα hs F hF A hA := by
    refine (h'.le_bound η hη0 hη1 φ hφ α hα hs F hF A hA).trans ?_
    have hK : FractionChange.productConstantsAt p c C φ ≤
        fractionConstants p c C φ :=
      mul_le_mul_of_nonneg_right (rpow_neg_le_div_rpow h.pos_exponent hc) (h.nonneg_constant φ hφ)
    have hη : 0 ≤ η ^ (-p) := Real.rpow_nonneg hη0.le _
    have hα' : 0 ≤ profileL1Norm α := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    have hN₁ : 0 ≤ heightNorm σ (η / 4) F := norm_nonneg _
    have hN₂ : 0 ≤ heightNorm σ (η / 4) A := norm_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hη) hα') hN₁) hN₂
theorem holds_of
    (hPull : AboveHeight.Holds)
    (hT : TupleRules.TupleSpanActionRules)
    (hInv : MomentSymmetry.ReductionHolds)
    (hFraction : FractionChange.Holds) :
    Holds := by
  intro m S σ
  refine ⟨shiftUpContracts hT hPull σ, insertionTimeShift hT hPull (hInv m S σ).2.1 σ,
    fun α _ => rfl, fun p C cS h => ?_⟩
  have hF := hFraction.1 m S σ p C cS h
  exact ⟨fun c hc => productBoundHolds_fractionConstants h hc (hF.1 c hc), fun c hc => hF.2.1 c hc⟩
end EuclideanFunctionals.TimeShiftAndFractions
end YangMills.Construction
end
