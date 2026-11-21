import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.PlateOperatorOfAProfileInADisc
import YangMills.Construction.EuclideanFunctionals.TensorsWithComplexEntriesTranslationsAndTranslatedClasses
import YangMills.Construction.EuclideanFunctionals.TranslationsAndConcatenationsOfTuplesWithComplexComponents
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane
namespace EuclideanFunctionals.SmallDiscProduct
open ProductInsertionOp
variable {m : SharpScale} {S : ConnFamily}
theorem rpowPos_eq_rpow {η : ℝ} (hη : 0 < η) (t : ℝ) : RealPower.rpowPos η t = η ^ t := by
  rw [RealPower.rpowPos, if_pos hη, Real.rpow_def_of_pos hη, mul_comm]
theorem abs_lt_of_mem_openDiscAt {y : RealPlane} {ρ : ℝ} (hy : y ∈ openDiscAt 0 ρ) : |y 0| < ρ := by
  have h : ‖y - 0‖ < ρ := hy
  rw [sub_zero] at h
  exact lt_of_le_of_lt (PiLp.norm_apply_le y 0) h
theorem profileL1Norm_nonneg (f : RealPlane → ℂ) : 0 ≤ profileL1Norm f :=
  MeasureTheory.integral_nonneg fun _ => norm_nonneg _
theorem osForm_nil (hv : CenteredInitialValues.InitialValues) (S : ConnFamily) :
    osForm S (toFree []) (toFree []) = 1 := by
  have hX : ([] : FnList) ∈ sepAll := (Ambient.emptyList defaultMirrorData Ambient.euclidean).2
  have hconj : freeConj (toFree []) = toFree [] := by
    rw [toFree_of_mem hX]
    simp [freeConj]
  have hmir : timeFlip.actFree (toFree []) = toFree [] :=
    liftLin_toFree (fun X : sepAll => toFree (timeFlip.actList X.1)) ⟨[], hX⟩
  have hmul₁ : freeMul (toFree []) =
      liftLin fun Y : sepAll => toFree (listAppend [] Y.1) :=
    liftLin_toFree
      (fun X : sepAll => liftLin fun Y : sepAll => toFree (listAppend X.1 Y.1))
      ⟨[], hX⟩
  have hmul : freeMul (toFree []) (toFree []) = toFree [] := by
    rw [hmul₁]
    exact liftLin_toFree (fun Y : sepAll => toFree (listAppend [] Y.1)) ⟨[], hX⟩
  have hval : centeredFnFree S (toFree []) = ((centeredFn S ⟨[], hX⟩ : ℝ) : ℂ) :=
    liftLin_toFree (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ)) ⟨[], hX⟩
  have hone : centeredFn S ⟨[], hX⟩ = 1 := (hv S).1
  rw [osForm, hconj, hmir, hmul, hval, hone, Complex.ofReal_one]
theorem norm_reconClass_nil (hv : CenteredInitialValues.InitialValues)
    (σ : EuclidFunctionalWithRecon m S) : ‖reconClass σ (toFree [])‖ = 1 := by
  have hmem : toFree [] ∈ finCombIn upperHalf := emptyComb.2
  have hcl : reconClass σ (toFree []) = σ.recon.cls emptyComb := by
    simp only [reconClass, readClass]
    rw [dif_pos hmem]
    rfl
  have hin : ⟪reconClass σ (toFree []), reconClass σ (toFree [])⟫_ℂ = 1 := by
    rw [hcl, σ.recon.inner_cls]
    exact osForm_nil hv S
  have hsq := inner_self_eq_norm_sq (𝕜 := ℂ) (reconClass σ (toFree []))
  rw [hin, RCLike.one_re] at hsq
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq.symm
theorem mulDefined_liftedProduct (ht : TensorTranslation.AllFacts)
    (hr : TupleConcat.TupleFacts)
    (htf : TupleRules.TupleSpanActionRules) (σ : EuclidFunctionalWithRecon m S)
    {c η : ℝ} (hc : c < 1 / 4) (hη : 0 < η) {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels)
    {f : RealPlane → ℂ} (hf : f ∈ complexProfiles) (hs : tsupport f ⊆ openDiscAt 0 (c * η))
    {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    MulDefined (singleComponent (liftedProduct η f φ)) (liftedElement η F) := by
  obtain ⟨hParts, -, -, -, hConc, -, -, hTuples, -⟩ := htf
  have hprod := hr.2.2 f hf φ hφ
  obtain ⟨-, -, -, hmem, hsupp, -⟩ :=
    hParts m (EuclidMotion.transl ((η / 4) • timeVec)) (EuclidMotion.transl ((η / 4) • timeVec))
      (productFunction f φ) hprod.1
  have hx : ∀ x ∈ supp (liftedProduct η f φ), 0 < x 3 ∧ x 3 < η / 2 := by
    intro x hx
    have hx' : x ∈ supp ((EuclidMotion.transl ((η / 4) • timeVec)).actFn (productFunction f φ)) := hx
    rw [hsupp] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    have hy' := abs_lt_of_mem_openDiscAt (hs (hprod.2 y hy))
    have e : (planeComponent y) 0 = y 3 := by simp [planeComponent]
    rw [e] at hy'
    have e' : (y + (η / 4) • timeVec) 3 = y 3 + η / 4 := by
      simp [PeriodicLattice.coordVec]
    change 0 < (y + (η / 4) • timeVec) 3 ∧ (y + (η / 4) • timeVec) 3 < η / 2
    rw [e']
    have hcη : c * η < η / 4 := by nlinarith
    have hb := abs_lt.1 hy'
    constructor <;> linarith [hb.1, hb.2]
  let U : Set R4 := {x | 0 < x 3 ∧ x 3 < η / 2}
  let V : Set R4 := {x | η / 2 < x 3}
  have hc3 : Continuous fun x : R4 => x 3 := continuous_apply 3
  have hU : IsOpen U := (isOpen_lt continuous_const hc3).inter (isOpen_lt hc3 continuous_const)
  have hV : IsOpen V := isOpen_lt continuous_const hc3
  have hd : Disjoint U V :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_lt.2 (le_of_lt hx'))
  have hent : ComplexComponents (fun _ : Fin 1 => liftedProduct η f φ) :=
    ⟨le_rfl, fun _ => hmem, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
  have h1 : singleComponent (liftedProduct η f φ) ∈ finCombIn U :=
    (hTuples U hU 1 1 _ hent fun _ x hx' => hx x hx').1
  have h2 : liftedElement η F ∈ finCombIn V :=
    ((ht m S σ).2.2.1 (η / 2) (half_pos hη)).1.mapsTo hF
  exact ((hConc U V hU hV hd).1 _ h1 _ h2).1
theorem profileL1Norm_eq_zero_of_neg (hv : CenteredInitialValues.InitialValues)
    (ht : TensorTranslation.AllFacts)
    (σ : EuclidFunctionalWithRecon m S) {p c η : ℝ} (hp : 0 < p)
    (hc : c ∈ productBoundFractions) {φ : RealPlane → ℝ} {C : ℝ}
    (hC : ProductBoundWith σ hp hc φ C) (hneg : C < 0) (hη : 0 < η) (hη1 : η ≤ 1)
    {f : RealPlane → ℂ} (hf : f ∈ complexProfiles) (hs : tsupport f ⊆ planeStrip c η) :
    profileL1Norm f = 0 := by
  have hE := (ht m S σ).2.2.1 (η / 4) (by positivity)
  have hnil : toFree [] ∈ finCombIn upperHalf := emptyComb.2
  have hmem := hE.1.mapsTo hnil
  have hn := hE.2.2 (toFree []) hnil
  rw [norm_reconClass_nil hv σ] at hn
  have hb := hC η ⟨hη, hη1⟩ f hf hs _ hmem _ hmem
  rw [hn, mul_one, mul_one] at hb
  have hX : 0 < η ^ (-p) := Real.rpow_pos_of_pos hη _
  by_contra hN
  have hN' : 0 < profileL1Norm f := lt_of_le_of_ne (profileL1Norm_nonneg f) (Ne.symm hN)
  have hlt : C * η ^ (-p) * profileL1Norm f < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hX) hN'
  exact absurd (norm_nonneg _) (not_le.2 (lt_of_le_of_lt hb hlt))
theorem holds (hop : ProductInsertionOp.Holds)
    (hv : CenteredInitialValues.InitialValues)
    (ht : TensorTranslation.AllFacts)
    (hr : TupleConcat.TupleFacts)
    (htf : TupleRules.TupleSpanActionRules) :
    SmallDiscProduct.Holds := by
  intro m S σ p c hp hc C _ hC η hη0 hη1 φ hφ f hf hs
  have hstrip : tsupport f ⊆ planeStrip c η := fun y hy => abs_lt_of_mem_openDiscAt (hs hy)
  have hdatum : IsLiftedProductDatum c η f φ := ⟨hc.1, hc.2, hη0, hη1, hφ, hf, hstrip⟩
  have hbd : ProductBoundHolds σ p (fun ψ => |C ψ|) c := by
    refine ⟨hp, fun _ _ => abs_nonneg _, hc.1, hc.2, ?_⟩
    intro η' h0 h1 ψ hψ f' hf' hs' F hF A hA
    refine (hC ψ hψ η' ⟨h0, h1⟩ f' hf' hs' F hF A hA).trans ?_
    have hX : 0 ≤ η' ^ (-p) := (Real.rpow_pos_of_pos h0 _).le
    have hN := profileL1Norm_nonneg f'
    have hF' : 0 ≤ heightNorm σ (η' / 4) F := norm_nonneg _
    have hA' : 0 ≤ heightNorm σ (η' / 4) A := norm_nonneg _
    have hC' : C ψ ≤ |C ψ| := le_abs_self _
    gcongr
  obtain ⟨hlin, B, hB, hnorm, huniq, -⟩ := hop m S σ p (fun ψ => |C ψ|) c η f φ hbd hdatum
  have hle : |C φ| * η ^ (-p) * profileL1Norm f ≤
      C φ * RealPower.rpowPos η (-p) * profileL1Norm f := by
    rw [rpowPos_eq_rpow hη0]
    rcases le_or_gt 0 (C φ) with h | h
    · rw [abs_of_nonneg h]
    · rw [profileL1Norm_eq_zero_of_neg hv ht σ hp hc (hC φ hφ) h hη0 hη1 hf hstrip]
      simp
  have hAct : ActsWithNormBound σ p (C φ) η f φ B := ⟨hB, hnorm.trans hle⟩
  have heq : productOperator σ φ f η = B := huniq _ (Classical.epsilon_spec ⟨B, hB⟩)
  refine ⟨fun F hF => ⟨mulDefined_liftedProduct ht hr htf σ hc.2 hη0 hφ hf hs hF, hlin.maps_to F hF,
    hlin.tensorCompZero_eq F hF⟩, ⟨B, hAct, fun B' h => huniq B' h.1⟩, ?_⟩
  rw [heq]
  exact hAct
end EuclideanFunctionals.SmallDiscProduct
end YangMills.Construction
