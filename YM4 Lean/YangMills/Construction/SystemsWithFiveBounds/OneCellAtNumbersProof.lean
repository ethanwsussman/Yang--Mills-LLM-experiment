import YangMills.Construction.InfiniteLattice.CalculusOfTheLatticeRepresentativesProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.SystemsWithFiveBounds.FieldOperatorAndFreeSlabAtNumbersProof
import YangMills.Construction.SystemsWithFiveBounds.MovingTuplesAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.OneCellAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.OneInsertionAtNumbers
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open SeparatedTuples
open ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
open R4TupleForms (FinTuple singleTuple realSpanLift toTupleFunctional
  FormalMulDefined formalMulDefined_of_mem formalMul_mem)
open SlabInsertion (timeVec)
open InfiniteLattice (AmbientSpace periodicGibbsSet reflectionSeminorm timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared timeUnitVec spanClassNorm)
open BoundsOnEverySide
private def translatePerm (v : AmbientSpace) : Equiv.Perm AmbientSpace := Equiv.addRight v
private theorem coe_translatePerm (v : AmbientSpace) : ⇑(translatePerm v) = SeparatedTuples.translate v := rfl
private def timeReflectPerm : Equiv.Perm AmbientSpace where
  toFun := TimeAxis.timeReflection
  invFun := TimeAxis.timeReflection
  left_inv := SlabInsertion.timeReflection_timeReflection
  right_inv := SlabInsertion.timeReflection_timeReflection
private theorem isEuclidIsometry_timeReflectPerm : IsEuclidIsometry ⇑timeReflectPerm := by apply _root_.YangMills.DeltaSharedProofs.p502081 <;> assumption
private theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private theorem isC1c_comp_sub {f : RealValued} (hf : IsC1c f) (v : AmbientSpace) :
    IsC1c fun x => f (x - v) := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.isC1c_shift <;> assumption
private theorem push_translate_singleTuple (v : AmbientSpace) {f : RealValued} (hf : IsC1c f) :
    push (translate v) (singleTuple f hf) = singleTuple (fun x => f (x - v)) (isC1c_comp_sub hf v) := by
  have hl : pushList (translate v) (singleTuple f hf).1 = [fun x => f (x - v)] := by
    rw [pushList_translate]
    rfl
  have hsep : IsDisjointlySupported (pushList (translate v) (singleTuple f hf).1) := by
    rw [hl]
    exact (singleTuple _ (isC1c_comp_sub hf v)).2
  unfold push
  rw [dif_pos hsep]
  exact Subtype.ext hl
private theorem centredProductLinear_basisVec_singleTuple (L K : ℕ)
    (ν : Measure (CutoffLattice.FieldsAt L K)) {f : RealValued}
    (hf : IsC1c f) (U : CutoffLattice.FieldsAt L K) :
    InfiniteLattice.CutoffRepresentative.centredProductLinear L K ν (basisVec (singleTuple f hf)) U =
      ((InfiniteLattice.smearedEnergy f U - ∫ V, InfiniteLattice.smearedEnergy f V ∂ν : ℝ) : ℂ) := by apply _root_.YangMills.Construction.InfiniteLattice.CutoffRepresentative.CentredCalculus.centredProductLinear_singleTuple <;> assumption
variable {D : ChessboardTori.ChessboardSetup}
private def conjReflect (v : AmbientSpace) : Equiv.Perm AmbientSpace :=
  translatePerm v * timeReflectPerm * (translatePerm v)⁻¹
private theorem conjReflect_apply (v x : AmbientSpace) :
    conjReflect v x = ![x 0, x 1, x 2, 2 * v 3 - x 3] := by
  have h1 : (translatePerm v)⁻¹ x = x - v := rfl
  have h2 : conjReflect v x = TimeAxis.timeReflection (x - v) + v := by
    simp only [conjReflect, Equiv.Perm.mul_apply, h1]
    rfl
  rw [h2]
  funext i
  fin_cases i <;> simp [TimeAxis.timeReflection] <;> ring
private theorem isEuclidIsometry_conjReflect (v : AmbientSpace) : IsEuclidIsometry ⇑(conjReflect v) := by
  intro x y
  simp only [conjReflect_apply, TorusMetric.euclidNormVec, Fin.sum_univ_four]
  congr 1
  simp
  ring
private theorem conjReflect_eq_timeReflect {a : ℝ} (t : InfiniteLattice.halfSpacingTimes a) {v : AmbientSpace}
    (hv : v 3 = t) : ⇑(conjReflect v) = (InfiniteLattice.timeReflect t).toFun := by
  funext x
  rw [conjReflect_apply, InfiniteLattice.timeReflect_apply, hv]
  funext i
  fin_cases i <;> simp [InfiniteLattice.timeAxis] <;> ring
private theorem pushSpan_mul (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {r r' : Equiv.Perm AmbientSpace} (hr : IsEuclidIsometry r) (hr' : IsEuclidIsometry r') (Ξ : FormalSpan) :
    pushSpan (⇑(r * r')) Ξ = pushSpan r (pushSpan r' Ξ) :=
  ((rules r r' hr hr').2 Ξ 0 (by intro X hX; simp at *)).1
private theorem conjugation_pushSpan (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {r : Equiv.Perm AmbientSpace} (hr : IsEuclidIsometry r) (Ξ : FormalSpan) :
    conjugation (pushSpan r Ξ) = pushSpan r (conjugation Ξ) :=
  ((rules r r hr hr).2 Ξ 0 (by intro X hX; simp at *)).2.2.2
private theorem pushSpan_translate_reflectConj (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (v : AmbientSpace) (W : FormalSpan) :
    pushSpan (translate v) (pushSpan TimeAxis.timeReflection (conjugation W)) =
      pushSpan (conjReflect v) (conjugation (pushSpan (translate v) W)) := by
  have hv : IsEuclidIsometry ⇑(translatePerm v) := isEuclidIsometry_translate v
  have h1 := pushSpan_mul rules hv isEuclidIsometry_timeReflectPerm (conjugation W)
  have h2 := pushSpan_mul rules (isEuclidIsometry_conjReflect v) hv (conjugation W)
  have h3 := conjugation_pushSpan rules hv W
  have h4 : conjReflect v * translatePerm v = translatePerm v * timeReflectPerm := by
    simp [conjReflect]
  rw [h4] at h2
  rw [coe_translatePerm] at h3
  have h5 : pushSpan (translate v) (pushSpan TimeAxis.timeReflection (conjugation W)) =
      pushSpan (⇑(translatePerm v * timeReflectPerm)) (conjugation W) := h1.symm
  rw [h5, h2, h3]
  rfl
private theorem pushSpan_translate_comm (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (v w : AmbientSpace) (W : FormalSpan) :
    pushSpan (translate v) (pushSpan (translate w) W) =
      pushSpan (translate w) (pushSpan (translate v) W) := by
  have hv : IsEuclidIsometry ⇑(translatePerm v) := isEuclidIsometry_translate v
  have hw : IsEuclidIsometry ⇑(translatePerm w) := isEuclidIsometry_translate w
  have h1 := pushSpan_mul rules hv hw W
  have h2 := pushSpan_mul rules hw hv W
  have h3 : translatePerm v * translatePerm w = translatePerm w * translatePerm v := by
    ext x i
    simp [translatePerm, add_right_comm]
  rw [h3] at h1
  exact h1.symm.trans h2
private abbrev centred (ν : Measure D.GaugeField) :
    FormalSpan →ₗ[ℂ] CutoffLattice.FieldsAt D.L (D.K : ℕ) → ℂ :=
  InfiniteLattice.CutoffRepresentative.centredProductLinear D.L (D.K : ℕ) ν
private def insertionSpan (l : ℝ) (h : RealValued) (hh : IsC1c h)
    (P Q : PositiveSpan) : FormalSpan :=
  formalMul (formalMul (reflectConj Q)
    (basisVec (push (translate (timeVec (l / 2))) (singleTuple h hh))))
    (pushSpan (translate (timeVec l)) P.1)
private def reflectionSquare (P : PositiveSpan) : FormalSpan :=
  formalMul (reflectConj P) P.1
private theorem reflectConj_mem_timeBelow (Q : PositiveSpan) :
    reflectConj Q ∈ spanIn (SlabInsertion.timeBelow 0) := by apply _root_.YangMills.SharedProofs.p8728 <;> assumption
private theorem pushSpan_timeVec_mem_timeAbove (l : ℝ) (P : PositiveSpan) :
    pushSpan (translate (timeVec l)) P.1 ∈ spanIn (SlabInsertion.timeAbove l) := by apply _root_.YangMills.SharedProofs.p50971 <;> assumption
private theorem basisVec_insertion_mem_slab {l : ℝ} (hl : 0 < l) {h : RealValued} (hh : IsC1c h)
    {y : Fin 3 → ℝ} (hs : tsupport h ⊆ TestFunctions.closedBallR4 (timeZeroPoint y) (l / 4)) :
    basisVec (push (translate (timeVec (l / 2))) (singleTuple h hh)) ∈
      spanIn {x | 0 < TimeAxis.timeComponent x ∧ TimeAxis.timeComponent x < l} := by
  rw [push_translate_singleTuple]
  refine Submodule.subset_span ⟨⟨singleTuple _ (isC1c_comp_sub hh _), fun f hf => ?_⟩, rfl⟩
  obtain rfl : f = fun x => h (x - timeVec (l / 2)) := List.mem_singleton.1 hf
  intro x hx
  have hc : Continuous fun x : AmbientSpace => x - timeVec (l / 2) := continuous_id.sub continuous_const
  have h₁ := hs (tsupport_comp_subset_preimage h hc hx)
  have h₂ : TorusMetric.euclidNormVec (x - timeVec (l / 2) - timeZeroPoint y) ≤ l / 4 := h₁
  have h₃ := (abs_apply_le_euclidNormVec _ 3).trans h₂
  have h₄ : (x - timeVec (l / 2) - timeZeroPoint y) 3 = x 3 - l / 2 := by
    simp [timeVec, TimeAxis.timeIdx]
  rw [h₄, abs_le] at h₃
  change 0 < x 3 ∧ x 3 < l
  constructor <;> linarith [h₃.1, h₃.2]
private theorem disjoint_timeBelow_slab {l : ℝ} :
    Disjoint (SlabInsertion.timeBelow 0) {x | 0 < TimeAxis.timeComponent x ∧ TimeAxis.timeComponent x < l} := by apply _root_.YangMills.DeltaSharedProofs.p502575 <;> assumption
private theorem disjoint_timeBelow_union_slab_timeAbove {l : ℝ} (hl : 0 < l) :
    Disjoint (SlabInsertion.timeBelow 0 ∪ {x | 0 < TimeAxis.timeComponent x ∧ TimeAxis.timeComponent x < l})
      (SlabInsertion.timeAbove l) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₂ : l < TimeAxis.timeComponent x := h'
    rcases h with h | h
    · have h₁ : TimeAxis.timeComponent x < 0 := h
      linarith
    · linarith [h.2]
private theorem disjoint_timeBelow_upperHalfSpace :
    Disjoint (SlabInsertion.timeBelow 0) TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.disjoint_lowerHalfSpace_upperHalfSpace <;> assumption
private theorem centred_pushSpan_reflectConj (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {ν : Measure D.GaugeField}
    (hconj : ∀ (Ξ : FormalSpan) (U : CutoffLattice.FieldsAt D.L (D.K : ℕ)),
      conj (centred ν Ξ U) = centred ν (conjugation Ξ) U)
    (hinv : ∀ t : InfiniteLattice.halfSpacingTimes D.mesh, ∀ Ξ : FormalSpan,
      (InfiniteLattice.timeReflect t).actOn (centred ν Ξ) =
        centred ν (pushSpan (InfiniteLattice.timeReflect t).toFun Ξ))
    (t : InfiniteLattice.halfSpacingTimes D.mesh) {v : AmbientSpace} (hv : v 3 = t) (W : PositiveSpan) :
    centred ν (pushSpan (translate v) (reflectConj W)) =
      timeConj t (centred ν (pushSpan (translate v) W.1)) := by
  unfold reflectConj
  rw [pushSpan_translate_reflectConj rules v W.1, conjReflect_eq_timeReflect t hv, ← hinv]
  funext U
  exact (hconj _ _).symm
private theorem isLipschitzFor_of_isC1c {f : RealValued} (hf : IsC1c f) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by apply _root_.YangMills.SharedProofs.p37577 <;> assumption
private theorem subset_closedBallR4_quarter_of_insertionRadius {N : BoundConstants} (hN : N.Admissible) {l : ℝ}
    (hl : 0 < l) {S : Set AmbientSpace} {x : AmbientSpace}
    (h : S ⊆ TestFunctions.closedBallR4 x (N.insertionRadiusRatio * l)) :
    S ⊆ TestFunctions.closedBallR4 x (l / 4) := fun z hz => by
  have h₁ : TestFunctions.euclidDistR4 z x ≤ N.insertionRadiusRatio * l := h hz
  have h₂ : N.insertionRadiusRatio * l ≤ l / 4 := by nlinarith [hN.insertionRadiusRatio_mem.2]
  exact h₁.trans h₂
private theorem norm_integral_translated_insertion_le (h₁ : SingleInsertionWithConstants)
    (hCalc : InfiniteLattice.CutoffRepresentative.CentredProductCalculus)
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement)
    {F : StatedSideFamily} {N : BoundConstants} (B : BoundsHoldAt F N) (hDL : D.L = F.L)
    (hdat : F.IsFirstPassage D.K D.β)
    {ρ ν : Measure D.GaugeField} (hρ : ρ ∈ F.stateSet D.L D.K D.β)
    (hν : ν ∈ F.stateSet D.L D.K D.β) (hνp : IsProbabilityMeasure ν)
    (hνt : ∀ u : InfiniteLattice.LatticePoint D.mesh,
      InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift u))
    (hνr : ∀ t : InfiniteLattice.halfSpacingTimes D.mesh,
      InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.timeReflect t))
    {l : ℝ} {e : ℤ} (hl : l = (D.L : ℝ) ^ e) (hl1 : l ≤ 1) (hside : D.mesh ≤ l / (D.L : ℝ) ^ 2)
    {y : Fin 3 → ℝ} {v : AmbientSpace} (hv : v 3 = D.mesh / 2)
    (hoff : ∀ μ, ∃ i : ℤ,
      (timeZeroPoint y + timeVec (l / 2) + v) μ - l / 2 = D.mesh * ((i : ℝ) + 1 / 2))
    {h : RealValued} (hh : IsC1c h)
    (hs : tsupport h ⊆ TestFunctions.closedBallR4 (timeZeroPoint y) (N.insertionRadiusRatio * l))
    {P Q : PositiveSpan} {δ : ℝ} (hδ : D.mesh / 2 < δ)
    (hP : P.1 ∈ spanIn {x : AmbientSpace | δ ≤ x 3})
    (hQ : Q.1 ∈ spanIn {x : AmbientSpace | δ ≤ x 3}) :
    ‖∫ U, centred ν (pushSpan (translate v) (insertionSpan l h hh P Q)) U ∂ρ‖ ≤
      N.insertionConst * l ^ (-N.insertionExponent) * TestFunctions.sharpNormR4 F.M h *
        Real.sqrt (∫ U, centred ν (pushSpan (translate v) (reflectionSquare Q)) U ∂ρ).re *
        Real.sqrt (∫ U, centred ν (pushSpan (translate v) (reflectionSquare P)) U ∂ρ).re := by
  have rules := (hmaps D).2.2.1
  obtain ⟨-, -, ⟨hprod, hconj, -⟩, hinv, hloc⟩ := hCalc D.toStandingParameters ν hνp
  have hlpos : 0 < l := by
    rw [hl]
    exact zpow_pos (zero_lt_one.trans D.one_lt_factor) e
  have hn : D.IsAdmissibleSide ((D.L : ℝ) ^ e) := ⟨⟨e, rfl⟩, hl ▸ hside⟩
  set x : AmbientSpace := timeZeroPoint y + timeVec (l / 2) + v with hx
  let g : ChessboardTori.ReflectionGrid D := D.gridOfSide e hn (fun μ => x μ - l / 2) hoff
  let c : GridCell D := ⟨g, hn, 0⟩
  have hcs : c.side = l := hl.symm
  have hcc : c.centre = x := by
    funext μ
    change (x μ - l / 2) + c.side * ((0 : ℤ) : ℝ) + c.side / 2 = x μ
    rw [hcs]
    simp
  have hct : ((c.baseTime : InfiniteLattice.halfSpacingTimes D.mesh) : ℝ) = D.mesh / 2 := by
    change c.centre InfiniteLattice.timeAxis - c.side / 2 = D.mesh / 2
    rw [hcc, hcs]
    have h0 : timeZeroPoint y 3 = 0 := rfl
    have h1 : timeVec (l / 2) 3 = l / 2 := Pi.single_eq_same _ _
    have : x InfiniteLattice.timeAxis = l / 2 + v 3 := by
      change timeZeroPoint y 3 + timeVec (l / 2) 3 + v 3 = _
      rw [h0, h1]
      ring
    rw [this, hv]
    ring
  set t := c.baseTime with ht
  have hvt : v 3 = t := by rw [hv, hct]
  have hvI : IsEuclidIsometry ⇑(translatePerm v) := isEuclidIsometry_translate v
  set w : AmbientSpace := timeVec (l / 2) with hw
  set E : SepTuple := push (translate w) (singleTuple h hh) with hE
  have hEm := basisVec_insertion_mem_slab hlpos hh
    (subset_closedBallR4_quarter_of_insertionRadius B.admissible_constants hlpos hs)
  have hd1 : FormalMulDefined (reflectConj Q) (basisVec E) :=
    formalMulDefined_of_mem disjoint_timeBelow_slab (reflectConj_mem_timeBelow Q) hEm
  have hd2 : FormalMulDefined (formalMul (reflectConj Q) (basisVec E))
      (pushSpan (translate (timeVec l)) P.1) :=
    formalMulDefined_of_mem (disjoint_timeBelow_union_slab_timeAbove hlpos)
      (formalMul_mem disjoint_timeBelow_slab (reflectConj_mem_timeBelow Q) hEm)
      (pushSpan_timeVec_mem_timeAbove l P)
  obtain ⟨-, hdef2, hmul2, -⟩ := (rules (translatePerm v) (translatePerm v) hvI hvI).2 _ _ hd2
  obtain ⟨-, hdef1, hmul1, -⟩ := (rules (translatePerm v) (translatePerm v) hvI hvI).2 _ _ hd1
  rw [coe_translatePerm] at hdef2 hmul2 hdef1 hmul1
  have hEeq : E = singleTuple _ (isC1c_comp_sub hh w) := push_translate_singleTuple w hh
  set hj : RealValued := fun z => (fun x => h (x - w)) (z - v) with hhj
  have hjm : IsC1c hj := isC1c_comp_sub (isC1c_comp_sub hh w) v
  have hE' : pushSpan (translate v) (basisVec E) = basisVec (singleTuple hj hjm) := by
    rw [hEeq]
    exact (linearExtend_basisVec _ _).trans (by rw [push_translate_singleTuple])
  set A := centred ν (pushSpan (translate v) P.1) with hA
  set Bq := centred ν (pushSpan (translate v) Q.1) with hB
  have hrefl := fun W => centred_pushSpan_reflectConj (D := D) (ν := ν) rules hconj
    (fun t Ξ => hinv _ (hνr t) Ξ) t hvt W
  have hcarried : ∀ W : FormalSpan, W ∈ spanIn {x : AmbientSpace | δ ≤ x 3} →
      pushSpan (translate v) W ∈
        spanIn {x : AmbientSpace | (t : ℝ) + δ ≤ x InfiniteLattice.timeAxis} := by
    intro W hW
    have hc : Continuous fun x : AmbientSpace => x - v := continuous_id.sub continuous_const
    refine SlabInsertion.pushSpan_mem_spanIn (SlabInsertion.invMap_translate v) hc
      (fun z hz => ?_) hW
    have h₂ : δ ≤ (z - v) 3 := hz
    have h₃ : (z - v) 3 = z 3 - v 3 := rfl
    rw [h₃, hvt] at h₂
    change (t : ℝ) + δ ≤ z 3
    linarith
  have hAloc : A ∈ InfiniteLattice.localObsAbove t := hloc t δ hδ _ (hcarried _ hP)
  have hBloc : Bq ∈ InfiniteLattice.localObsAbove t := hloc t δ hδ _ (hcarried _ hQ)
  have hcol : (c.timeShift 1).toFun = SeparatedTuples.translate (timeVec l) := by
    funext z
    have hs1 : ((c.timeStep 1 : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) = timeVec l := by
      change (((1 : ℤ) : ℝ) * c.side) • timeUnitVec = timeVec l
      rw [hcs]
      funext μ
      by_cases hμ : μ = InfiniteLattice.timeAxis
      · subst hμ
        simp [timeUnitVec, ChessboardTori.coordVec, timeVec, TimeAxis.timeIdx,
          InfiniteLattice.timeAxis]
      · have hμ' : μ ≠ TimeAxis.timeIdx := hμ
        simp [timeUnitVec, ChessboardTori.coordVec, timeVec, Pi.single_eq_of_ne hμ,
          Pi.single_eq_of_ne hμ']
    change z + ((c.timeStep 1 : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) = z + timeVec l
    rw [hs1]
  have hshift : centred ν (pushSpan (translate v)
      (pushSpan (translate (timeVec l)) P.1)) =
      (c.timeShift 1).actOn A := by
    rw [pushSpan_translate_comm rules v (timeVec l) P.1]
    have h2 := hinv (c.timeShift 1) (hνt _) (pushSpan (translate v) P.1)
    have h3 : pushSpan (c.timeShift 1).toFun (pushSpan (translate v) P.1) =
        pushSpan (translate (timeVec l)) (pushSpan (translate v) P.1) := by
      rw [hcol]
    exact (h2.trans (congrArg (centred ν) h3)).symm
  have hrepΞ : ∀ U : D.GaugeField,
      centred ν (pushSpan (translate v) (insertionSpan l h hh P Q)) U =
      timeConj t Bq U * centred ν (basisVec (singleTuple hj hjm)) U *
        (c.timeShift 1).actOn A U := by
    intro U
    change centred ν (pushSpan (translate v) (formalMul
      (formalMul (reflectConj Q) (basisVec E))
      (pushSpan (translate (timeVec l)) P.1))) U = _
    rw [hmul2, hprod _ _ hdef2, hmul1, hprod _ _ hdef1, hE', hrefl Q, hshift]
    rfl
  have hsq : ∀ (W : PositiveSpan) (U : D.GaugeField),
      centred ν (pushSpan (translate v) (reflectionSquare W)) U =
        timeConj t (centred ν (pushSpan (translate v) W.1)) U *
          centred ν (pushSpan (translate v) W.1) U := by
    intro W U
    have hd : FormalMulDefined (reflectConj W) W.1 :=
      formalMulDefined_of_mem disjoint_timeBelow_upperHalfSpace (reflectConj_mem_timeBelow W) W.2
    obtain ⟨-, hdef, hmul, -⟩ := (rules (translatePerm v) (translatePerm v) hvI hvI).2 _ _ hd
    rw [coe_translatePerm] at hdef hmul
    unfold reflectionSquare
    rw [hmul, hprod _ _ hdef, hrefl W]
    rfl
  have hroot : ∀ W : PositiveSpan,
      reflectionSeminorm ρ t (centred ν (pushSpan (translate v) W.1)) =
        Real.sqrt (∫ U, centred ν (pushSpan (translate v) (reflectionSquare W)) U ∂ρ).re := by
    intro W
    have h₂ : ∫ U, centred ν (pushSpan (translate v) (reflectionSquare W)) U ∂ρ =
        InfiniteLattice.reflectionForm ρ t (centred ν (pushSpan (translate v) W.1))
          (centred ν (pushSpan (translate v) W.1)) :=
      integral_congr_ae (ae_of_all _ (hsq W))
    rw [h₂]
    rfl
  have hjl : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 hj := isLipschitzFor_of_isC1c hjm
  have hsup : tsupport hj ⊆ TestFunctions.closedBallR4 c.centre (N.insertionRadiusRatio * c.side) := by
    intro z hz
    have hc : Continuous fun x : AmbientSpace => x - v - w :=
      (continuous_id.sub continuous_const).sub continuous_const
    have h₁ := hs (tsupport_comp_subset_preimage h hc hz)
    have h₂ : TorusMetric.euclidNormVec (z - v - w - timeZeroPoint y) ≤ N.insertionRadiusRatio * l := h₁
    rw [hcc, hcs]
    change TorusMetric.euclidNormVec (z - x) ≤ N.insertionRadiusRatio * l
    have h₃ : z - x = z - v - w - timeZeroPoint y := by
      rw [hx]
      abel
    rw [h₃]
    exact h₂
  have hsharp : TestFunctions.sharpNormR4 F.M hj = TestFunctions.sharpNormR4 F.M h := by
    have hu : IsEuclidIsometry ⇑(translatePerm (v + w)) := isEuclidIsometry_translate _
    have h₂ := (((rules _ _ hu hu).1 ℝ h (isLipschitzFor_of_isC1c hh) hh.2).2.2) F.M F.one_le_M
    have h₃ : MirrorGridsAllSides.transportFun (translatePerm (v + w)) h = hj := by
      funext z
      change h (z + -(v + w)) = h (z - v - w)
      congr 1
      abel
    rw [← h₃]
    exact h₂
  obtain ⟨-, hb⟩ := h₁ F N B D hDL hdat c hj hjl hsup (hcs.le.trans hl1)
  have hmain := hb ρ hρ ν hν _ hAloc _ hBloc
  have hval : ∫ V : D.GaugeField, complexSmeared D hj V ∂ν =
      ((∫ V : D.GaugeField, InfiniteLattice.smearedEnergy hj V ∂ν : ℝ) : ℂ) := integral_ofReal
  have hint : ∫ U, centred ν (pushSpan (translate v) (insertionSpan l h hh P Q)) U ∂ρ =
      ∫ U : D.GaugeField, timeConj t Bq U *
        (complexSmeared D hj U - ∫ V : D.GaugeField, complexSmeared D hj V ∂ν) *
        (c.timeShift 1).actOn A U ∂ρ := by
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have h₄ : centred ν (basisVec (singleTuple hj hjm)) U = complexSmeared D hj U -
        ((∫ V : D.GaugeField, InfiniteLattice.smearedEnergy hj V ∂ν : ℝ) : ℂ) := by
      refine (centredProductLinear_basisVec_singleTuple D.L (D.K : ℕ) ν hjm U).trans ?_
      simp only [complexSmeared, Complex.ofReal_sub]
      rfl
    rw [hrepΞ U, hval, h₄]
  rw [hint, ← hroot Q, ← hroot P]
  rw [hcs, hsharp] at hmain
  exact hmain
private theorem exists_pos_spanIn_time_ge (P : PositiveSpan) :
    ∃ δ : ℝ, 0 < δ ∧ P.1 ∈ spanIn {x : AmbientSpace | δ ≤ x 3} := by
  have hF := (R4TupleForms.mem_spanIn_iff TimeAxis.upperHalfSpace P.1).1 P.2
  have hQ : IsCompact (⋃ X ∈ P.1.support, ⋃ f ∈ X.1, tsupport f) :=
    P.1.support.isCompact_biUnion fun X _ =>
      (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  have h : ∀ x ∈ (⋃ X ∈ P.1.support, ⋃ f ∈ X.1, tsupport f), 0 < x TimeAxis.timeIdx := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨X, hX, f, hf, hxf⟩ := hx
    exact hF X hX f hf hxf
  rcases (⋃ X ∈ P.1.support, ⋃ f ∈ X.1, tsupport f).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, (R4TupleForms.mem_spanIn_iff _ P.1).2 fun X hX f hf x hx => ?_⟩
    have : x ∈ (⋃ X ∈ P.1.support, ⋃ f ∈ X.1, tsupport f) := Set.mem_biUnion hX (Set.mem_biUnion hf hx)
    rw [he] at this
    exact this.elim
  · obtain ⟨m, hm, hmin⟩ := hQ.exists_isMinOn hne (continuous_apply TimeAxis.timeIdx).continuousOn
    refine ⟨m TimeAxis.timeIdx, h m hm,
      (R4TupleForms.mem_spanIn_iff _ P.1).2 fun X hX f hf x hx => ?_⟩
    exact hmin (Set.mem_biUnion hX (Set.mem_biUnion hf hx))
private def nearestVec (a : ℝ) (y : Fin 3 → ℝ) : AmbientSpace :=
  ![a * round (y 0 / a) - y 0, a * round (y 1 / a) - y 1, a * round (y 2 / a) - y 2, a / 2]
private theorem abs_mul_round_div_sub_le {a : ℝ} (ha : 0 < a) (b : ℝ) : |a * round (b / a) - b| ≤ a / 2 := by
  have h := abs_sub_round (b / a)
  have h₁ : a * round (b / a) - b = -(a * (b / a - round (b / a))) := by
    field_simp
    ring
  rw [h₁, abs_neg, abs_mul, abs_of_pos ha]
  calc a * |b / a - round (b / a)| ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left h ha.le
    _ = a / 2 := by ring
private theorem abs_nearestVec_le {a : ℝ} (ha : 0 < a) (y : Fin 3 → ℝ) (μ : Fin 4) :
    |nearestVec a y μ| ≤ a / 2 := by
  fin_cases μ
  · exact abs_mul_round_div_sub_le ha _
  · exact abs_mul_round_div_sub_le ha _
  · exact abs_mul_round_div_sub_le ha _
  · change |a / 2| ≤ a / 2
    rw [abs_of_pos (by positivity)]
private theorem exists_odd_mul_mesh (D : ChessboardTori.ChessboardSetup) {e : ℤ}
    (hn : D.IsAdmissibleSide ((D.L : ℝ) ^ e)) :
    ∃ r : ℤ, (D.L : ℝ) ^ e = (2 * (r : ℝ) + 1) * D.mesh := by
  have hL1 : (1 : ℝ) < D.L := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have he : 0 ≤ e + ((D.K : ℕ) : ℤ) := by
    have := D.one_sub_K_le_of_isAdmissibleSide hn
    linarith
  obtain ⟨n, hn'⟩ := Int.eq_ofNat_of_zero_le he
  have hodd : Odd (D.L ^ n) := D.isAdmissible.1.pow
  obtain ⟨r, hr⟩ := hodd
  refine ⟨r, ?_⟩
  have h1 : (D.L : ℝ) ^ e = (D.L : ℝ) ^ (e + ((D.K : ℕ) : ℤ)) * D.mesh := by
    change _ = _ * PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)
    rw [PeriodicLattice.meshSize, ← zpow_add₀ hL0]
    simp
  rw [h1, hn', zpow_natCast]
  have h2 : ((D.L ^ n : ℕ) : ℝ) = 2 * (r : ℝ) + 1 := by
    rw [hr]
    push_cast
    ring
  push_cast at h2
  rw [h2]
  push_cast
  ring
private theorem exists_half_integer_origin (D : ChessboardTori.ChessboardSetup) {e : ℤ} {l : ℝ}
    (hl : l = (D.L : ℝ) ^ e)
    (hn : D.IsAdmissibleSide ((D.L : ℝ) ^ e)) (y : Fin 3 → ℝ) (μ : Fin 4) :
    ∃ i : ℤ, (timeZeroPoint y + timeVec (l / 2) + nearestVec D.mesh y) μ - l / 2 =
      D.mesh * ((i : ℝ) + 1 / 2) := by
  obtain ⟨r, hr⟩ := exists_odd_mul_mesh D hn
  rw [← hl] at hr
  have hsp : ∀ (k : Fin 4), k ≠ 3 → ∀ u : ℤ, ∀ b : ℝ,
      b + 0 + (D.mesh * u - b) - l / 2 = D.mesh * (((u - r - 1 : ℤ) : ℝ) + 1 / 2) := by
    intro k _ u b
    rw [hr]
    push_cast
    ring
  fin_cases μ
  · refine ⟨round (y 0 / D.mesh) - r - 1, ?_⟩
    have h0 : timeVec (l / 2) 0 = 0 := Pi.single_eq_of_ne (by decide) _
    change y 0 + timeVec (l / 2) 0 + (D.mesh * round (y 0 / D.mesh) - y 0) - l / 2 = _
    rw [h0]
    exact hsp 0 (by decide) (round (y 0 / D.mesh)) (y 0)
  · refine ⟨round (y 1 / D.mesh) - r - 1, ?_⟩
    have h0 : timeVec (l / 2) 1 = 0 := Pi.single_eq_of_ne (by decide) _
    change y 1 + timeVec (l / 2) 1 + (D.mesh * round (y 1 / D.mesh) - y 1) - l / 2 = _
    rw [h0]
    exact hsp 1 (by decide) (round (y 1 / D.mesh)) (y 1)
  · refine ⟨round (y 2 / D.mesh) - r - 1, ?_⟩
    have h0 : timeVec (l / 2) 2 = 0 := Pi.single_eq_of_ne (by decide) _
    change y 2 + timeVec (l / 2) 2 + (D.mesh * round (y 2 / D.mesh) - y 2) - l / 2 = _
    rw [h0]
    exact hsp 2 (by decide) (round (y 2 / D.mesh)) (y 2)
  · refine ⟨0, ?_⟩
    have h0 : timeZeroPoint y 3 = 0 := rfl
    have h1 : timeVec (l / 2) 3 = l / 2 := Pi.single_eq_same _ _
    have h2 : nearestVec D.mesh y 3 = D.mesh / 2 := rfl
    change timeZeroPoint y 3 + timeVec (l / 2) 3 + nearestVec D.mesh y 3 - l / 2 = _
    rw [h0, h1, h2]
    push_cast
    ring
variable {s : Conventions.StandingParameters} {K : ℕ → ℕ}
  {ρ ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ)))}
private theorem realSpanLift_eq_integral (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hKpos : ∀ j, 0 < K j) (hρ : ∀ j, IsProbabilityMeasure (ρ j)) (j : ℕ) (Ξ : FormalSpan) :
    Integrable (InfiniteLattice.CutoffRepresentative.centredProductLinear s.L (K j) (ν j) Ξ) (ρ j) ∧
      realSpanLift (StateLimits.pairedValue K ρ ν j) Ξ =
        ∫ U, InfiniteLattice.CutoffRepresentative.centredProductLinear s.L (K j) (ν j) Ξ U ∂ρ j := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.realSpanLift_eq_integral <;> assumption
private theorem tendsto_meshSize (hL : 2 ≤ s.L) (hK : Tendsto K atTop atTop) :
    Tendsto (fun j => PeriodicLattice.meshSize s.L (K j : ℤ)) atTop (𝓝 0) := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.tendsto_meshSize <;> assumption
private theorem periodicGibbs_properties
    (hSym : InfiniteLattice.PeriodicStatesAllScales.AllScalesAllCouplings)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 0 < k) {b : ℝ} (hb : 0 < b)
    {μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (k : ℤ)))}
    (h : μ ∈ periodicGibbsSet L k b) :
    IsProbabilityMeasure μ ∧
      (∀ v : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (k : ℤ)),
        InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.shift v)) ∧
      ∀ t : InfiniteLattice.halfSpacingTimes (PeriodicLattice.meshSize L (k : ℤ)),
        InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.timeReflect t) := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.periodicGibbs_facts <;> assumption
theorem singleCellBoundOfLimit_holds (h₁ : SingleInsertionWithConstants)
    (h₂ : TranslatedTuplesWithConstants)
    (hCalc : InfiniteLattice.CutoffRepresentative.CentredProductCalculus)
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement)
    (hCI : InfiniteLattice.CenteredIdentity.Statement)
    (hSym : InfiniteLattice.PeriodicStatesAllScales.AllScalesAllCouplings) :
    SingleCellBoundOfLimit := by
  intro F N B s K β ρ ν σ hσ hsL hlim hd hρs hνs e l hl hl1 y h hh hs P Q
  have hCl := h₂ F N B s K β ρ ν σ hsL hlim hd hρs hνs
  have hKpos := hlim.cutoff_pos
  have hSeq := hlim.periodicGibbs
  have hβ : ∀ j, 0 < β j := fun j => F.pos_of_isFirstPassage _ _ (hd j (hKpos j))
  have hLs : Conventions.IsAdmissibleBlockingFactor s.L := s.isAdmissible
  have hL2 : 2 ≤ s.L := by
    have := hLs.2
    omega
  have fρ := fun j => periodicGibbs_properties hSym hLs (hKpos j) (hβ j) (hSeq.left_mem j)
  have fν := fun j => periodicGibbs_properties hSym hLs (hKpos j) (hβ j) (hSeq.right_mem j)
  have hρp := fun j => (fρ j).1
  obtain ⟨δ₁, hδ₁, hP₁⟩ := exists_pos_spanIn_time_ge P
  obtain ⟨δ₂, hδ₂, hQ₁⟩ := exists_pos_spanIn_time_ge Q
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have hmono : ∀ (W : FormalSpan) (δ' : ℝ), δ ≤ δ' → W ∈ spanIn {x : AmbientSpace | δ' ≤ x 3} →
      W ∈ spanIn {x : AmbientSpace | δ ≤ x 3} := fun W δ' hle hW =>
    (R4TupleForms.mem_spanIn_iff _ W).2 fun X hX f hf x hx =>
      hle.trans ((R4TupleForms.mem_spanIn_iff _ W).1 hW X hX f hf hx)
  have hP := hmono _ _ (min_le_left _ _) hP₁
  have hQ := hmono _ _ (min_le_right _ _) hQ₁
  have hL1 : (1 : ℝ) < s.L := by exact_mod_cast (by omega : 1 < s.L)
  have hlpos : 0 < l := by
    rw [hl, ← hsL]
    exact zpow_pos (zero_lt_one.trans hL1) e
  have hsp := tendsto_meshSize hL2 hSeq.cutoff_tendsto
  have hapos : ∀ j, 0 < PeriodicLattice.meshSize s.L (K j : ℤ) := fun j =>
    zpow_pos (zero_lt_one.trans hL1) _
  set v : ℕ → AmbientSpace := fun j => nearestVec (PeriodicLattice.meshSize s.L (K j : ℤ)) y with hvdef
  have hv0 : Tendsto v atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun μ => ?_
    have h₃ : Tendsto (fun j => PeriodicLattice.meshSize s.L (K j : ℤ) / 2) atTop (𝓝 0) := by
      simpa using hsp.div_const 2
    refine squeeze_zero_norm (fun j => ?_) h₃
    exact abs_nearestVec_le (hapos j) y μ
  have t1 := hCl.tendsto_shifted (insertionSpan l h hh P Q) v hv0
  have t2 := hCl.tendsto_shifted (reflectionSquare Q) v hv0
  have t3 := hCl.tendsto_shifted (reflectionSquare P) v hv0
  have hroot : Continuous fun z : ℂ => Real.sqrt z.re := Real.continuous_sqrt.comp Complex.continuous_re
  have hlim₂ := (((hroot.tendsto _).comp t2).const_mul
    (N.insertionConst * l ^ (-N.insertionExponent) * TestFunctions.sharpNormR4 F.M h)).mul
      ((hroot.tendsto _).comp t3)
  have hl' : l = (s.L : ℝ) ^ e := by
    rw [hsL]
    exact hl
  have hL2pos : 0 < l / (s.L : ℝ) ^ 2 := div_pos hlpos (by positivity)
  have e1 : ∀ᶠ j in atTop, PeriodicLattice.meshSize s.L (K j : ℤ) < l / (s.L : ℝ) ^ 2 :=
    hsp.eventually (gt_mem_nhds hL2pos)
  have e2 : ∀ᶠ j in atTop, PeriodicLattice.meshSize s.L (K j : ℤ) / 2 < δ := by
    have h₃ : Tendsto (fun j => PeriodicLattice.meshSize s.L (K j : ℤ) / 2) atTop (𝓝 0) := by
      simpa using hsp.div_const 2
    exact h₃.eventually (gt_mem_nhds hδ0)
  refine le_of_tendsto_of_tendsto t1.norm hlim₂ ?_
  filter_upwards [e1, e2] with j hj1 hj2
  let D : ChessboardTori.ChessboardSetup := ⟨{ s with K := ⟨K j, hKpos j⟩ }, β j, hβ j⟩
  have hn : D.IsAdmissibleSide ((D.L : ℝ) ^ e) := ⟨⟨e, rfl⟩, by
    have h₄ : (D.L : ℝ) ^ e = l := hl'.symm
    rw [h₄]
    exact hj1.le⟩
  have hb := norm_integral_translated_insertion_le (D := D) h₁ hCalc hmaps B hsL (hd j (hKpos j))
    (ρ := ρ j) (ν := ν j) (hρs j (hKpos j)) (hνs j (hKpos j)) (fν j).1 (fν j).2.1 (fν j).2.2
    (l := l) (e := e) hl' hl1 hj1.le (y := y) (v := v j) rfl (exists_half_integer_origin D hl' hn y)
    hh hs hj2 hP hQ
  have eI := fun Ξ => (realSpanLift_eq_integral (ν := ν) hCI hKpos hρp j Ξ).2
  change ‖realSpanLift (StateLimits.pairedValue K ρ ν j) _‖ ≤
    N.insertionConst * l ^ (-N.insertionExponent) * TestFunctions.sharpNormR4 F.M h *
      Real.sqrt (realSpanLift (StateLimits.pairedValue K ρ ν j) _).re *
      Real.sqrt (realSpanLift (StateLimits.pairedValue K ρ ν j) _).re
  rw [eI, eI, eI]
  exact hb
end YangMills.Construction.SystemsWithFiveBounds
end
