import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import YangMills.Construction.SystemsWithFiveBounds.FieldOperatorAndFreeSlabAtNumbersProof
import YangMills.Construction.EuclideanFunctionals.InsertionBoundOfAReconstructionFromTheBoundOnTheFreeSlab
import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenationProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SlabInsertionTransfer
theorem mem_sepAll_of_sepTuple (X : SeparatedTuples.SepTuple) : X.1 ∈ sepAll :=
  (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData X.1).1 X.2
theorem isDisjointlySupported_of_mem_sepAll (X : sepAll) :
    SeparatedTuples.IsDisjointlySupported X.1 :=
  (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData X.1).2 X.2
theorem formalSpan_linearMap_ext {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {f g : SeparatedTuples.FormalSpan →ₗ[ℂ] V}
    (h : ∀ X, f (SeparatedTuples.basisVec X) = g (SeparatedTuples.basisVec X)) : f = g :=
  Finsupp.lhom_ext' fun X => LinearMap.ext_ring (h X)
def spanToFree : SeparatedTuples.FormalSpan →ₗ[ℂ] FreeSep :=
  SeparatedTuples.linearExtend fun X => toFree X.1
theorem spanToFree_basisVec (X : SeparatedTuples.SepTuple) :
    spanToFree (SeparatedTuples.basisVec X) = toFree X.1 :=
  SeparatedTuples.linearExtend_basisVec _ _
def freeToSpan : FreeSep →ₗ[ℂ] SeparatedTuples.FormalSpan :=
  liftLin fun X => SeparatedTuples.basisVec ⟨X.1, isDisjointlySupported_of_mem_sepAll X⟩
theorem spanToFree_freeToSpan (F : FreeSep) : spanToFree (freeToSpan F) = F := by
  have h : spanToFree ∘ₗ freeToSpan = LinearMap.id := by
    refine Finsupp.lhom_ext' fun X => LinearMap.ext_ring ?_
    have h₁ : freeToSpan (Finsupp.single X 1) =
        SeparatedTuples.basisVec ⟨X.1, isDisjointlySupported_of_mem_sepAll X⟩ := by
      simp [freeToSpan, liftLin]
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply, h₁,
      spanToFree_basisVec]
    exact toFree_of_mem X.2
  exact LinearMap.congr_fun h F
theorem freeToSpan_mem {O : Set R4} {F : FreeSep} (hF : F ∈ finCombIn O) :
    freeToSpan F ∈ SeparatedTuples.spanIn O := by
  rw [finCombIn_eq_freeSpanIn] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, hX, rfl⟩ := hG
    have h₁ : freeToSpan (toFree X) =
        SeparatedTuples.basisVec ⟨X, isDisjointlySupported_of_mem_sepAll ⟨X, hX.1⟩⟩ :=
      liftLin_toFree _ ⟨X, hX.1⟩
    rw [h₁]
    exact Submodule.subset_span
      ⟨⟨_, (R4TupleForms.mem_supportedIn_iff_mem_separatedWithin defaultMirrorData O _).2 hX⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
theorem spanToFree_mem {O : Set R4} {G : SeparatedTuples.FormalSpan}
    (hG : G ∈ SeparatedTuples.spanIn O) : spanToFree G ∈ finCombIn O := by
  rw [finCombIn_eq_freeSpanIn]
  induction hG using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨X, rfl⟩ := hH
    rw [spanToFree_basisVec]
    exact Submodule.subset_span
      ⟨X.1.1, (R4TupleForms.mem_supportedIn_iff_mem_separatedWithin defaultMirrorData O _).1 X.2, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
theorem spanToFree_conjugation (G : SeparatedTuples.FormalSpan) :
    spanToFree (SeparatedTuples.conjugation G) = freeConj (spanToFree G) := by
  induction G using Finsupp.induction_linear with
  | zero => simp [freeConj]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb]
    simp [freeConj, Finsupp.mapRange_add]
  | single X c =>
    have h₁ : (Finsupp.single X c : SeparatedTuples.FormalSpan) =
        c • SeparatedTuples.basisVec X := by
      simp [SeparatedTuples.basisVec]
    have h₂ : SeparatedTuples.conjugation (Finsupp.single X c) =
        (starRingEnd ℂ c) • SeparatedTuples.basisVec X := by
      rw [h₁, map_smulₛₗ, SeparatedTuples.conjugation_basisVec]
    rw [h₂, h₁, map_smul, map_smul, spanToFree_basisVec, toFree_of_mem (mem_sepAll_of_sepTuple X)]
    simp [freeConj]
theorem contDiff_euclidMotion (R : EuclidMotion) : ContDiff ℝ 1 fun x => R x := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.contDiff_motion <;> assumption
def motionHomeomorph (R : EuclidMotion) : R4 ≃ₜ R4 where
  toEquiv := R.toPerm
  continuous_toFun := (contDiff_euclidMotion R).continuous
  continuous_invFun := (contDiff_euclidMotion R⁻¹).continuous
theorem isDisjointlySupported_actList (R : EuclidMotion) (X : SeparatedTuples.SepTuple) :
    SeparatedTuples.IsDisjointlySupported (R.actList X.1) := by
  have hs : ∀ f : R4 → ℝ, tsupport (R.actFn f) = (fun x => R⁻¹ x) ⁻¹' tsupport f := fun f =>
    tsupport_comp_eq_preimage f (motionHomeomorph R).symm
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    have hc := X.2.1 g hg
    exact ⟨hc.1.comp (contDiff_euclidMotion R⁻¹),
      hc.2.comp_homeomorph (motionHomeomorph R).symm⟩
  · refine List.pairwise_map.2 (X.2.2.imp fun {f g} h => ?_)
    rw [hs, hs]
    exact h.preimage _
theorem spanToFree_pushSpan {r : R4 → R4} (R : EuclidMotion)
    (hr : SeparatedTuples.invMap r = fun x => R⁻¹ x) (G : SeparatedTuples.FormalSpan) :
    spanToFree (SeparatedTuples.pushSpan r G) = R.actFree (spanToFree G) := by
  have h : spanToFree ∘ₗ SeparatedTuples.pushSpan r = R.actFree ∘ₗ spanToFree := by
    refine formalSpan_linearMap_ext fun X => ?_
    have hl : SeparatedTuples.pushList r X.1 = R.actList X.1 := by
      simp only [SeparatedTuples.pushList, hr, EuclidMotion.actList]
      rfl
    have hsep : SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList r X.1) := by
      rw [hl]
      exact isDisjointlySupported_actList R X
    have h₁ : SeparatedTuples.pushSpan r (SeparatedTuples.basisVec X) =
        SeparatedTuples.basisVec (SeparatedTuples.push r X) :=
      SeparatedTuples.linearExtend_basisVec _ _
    have h₂ : (SeparatedTuples.push r X).1 = R.actList X.1 := by
      unfold SeparatedTuples.push
      rw [dif_pos hsep]
      exact hl
    have h₃ : R.actFree (toFree X.1) = toFree (R.actList X.1) :=
      liftLin_toFree _ ⟨X.1, mem_sepAll_of_sepTuple X⟩
    simp only [LinearMap.comp_apply, h₁, spanToFree_basisVec, h₂, h₃]
  exact LinearMap.congr_fun h G
theorem spanToFree_formalMul {O O' : Set R4} (hO : Disjoint O O')
    {G H : SeparatedTuples.FormalSpan} (hG : G ∈ SeparatedTuples.spanIn O)
    (hH : H ∈ SeparatedTuples.spanIn O') :
    spanToFree (SeparatedTuples.formalMul G H) = freeMul (spanToFree G) (spanToFree H) := by
  have hbasis : ∀ (X : SeparatedTuples.supportedIn O) (Y : SeparatedTuples.supportedIn O'),
      spanToFree (SeparatedTuples.formalMul (SeparatedTuples.basisVec X.1)
        (SeparatedTuples.basisVec Y.1)) =
      freeMul (spanToFree (SeparatedTuples.basisVec X.1))
        (spanToFree (SeparatedTuples.basisVec Y.1)) := by
    intro X Y
    have hdef := SeparatedTuples.composable_of_mem_supportedIn hO X.2 Y.2
    have h₁ : freeMul (toFree X.1.1) (toFree Y.1.1) = toFree (listAppend X.1.1 Y.1.1) := by
      have h₂ : freeMul (toFree X.1.1) =
          liftLin fun Y : sepAll => toFree (listAppend X.1.1 Y.1) :=
        liftLin_toFree _ ⟨X.1.1, mem_sepAll_of_sepTuple X.1⟩
      rw [h₂]
      exact liftLin_toFree _ ⟨Y.1.1, mem_sepAll_of_sepTuple Y.1⟩
    rw [SeparatedTuples.formalMul_basisVec, spanToFree_basisVec, spanToFree_basisVec,
      spanToFree_basisVec, h₁, R4TupleForms.juxt_val_eq_append defaultMirrorData hdef]
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    induction hH using Submodule.span_induction with
    | mem G' hG' =>
      obtain ⟨Y, rfl⟩ := hG'
      exact hbasis X Y
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | smul c a _ ha => simp only [map_smul, ha]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul c a _ ha => simp only [map_smul, LinearMap.smul_apply, ha]
theorem centeredFnFree_spanToFree {ς : SeparatedTuples.TupleFunctional} {S : ConnFamily}
    (h : AgreesWithCenteredFn ς S) (G : SeparatedTuples.FormalSpan) :
    centeredFnFree S (spanToFree G) = ς.spanExtension G := by
  have hl : centeredFnFree S ∘ₗ spanToFree = ς.spanExtension := by
    refine formalSpan_linearMap_ext fun X => ?_
    have h₁ : centeredFnFree S (toFree X.1) =
        (centeredFn S ⟨X.1, mem_sepAll_of_sepTuple X⟩ : ℂ) :=
      liftLin_toFree _ ⟨X.1, mem_sepAll_of_sepTuple X⟩
    have h₂ : ς.spanExtension (SeparatedTuples.basisVec X) = (ς X : ℂ) :=
      SeparatedTuples.linearExtend_basisVec _ _
    rw [LinearMap.comp_apply, spanToFree_basisVec, h₁, h₂]
    exact congrArg _ (h X).symm
  exact LinearMap.congr_fun hl G
theorem timeReflection_eq_timeFlip (x : R4) : TimeAxis.timeReflection x = timeFlip x := by
  rw [timeFlip_apply]
  funext i
  fin_cases i <;> simp [TimeAxis.timeReflection, PeriodicLattice.coordVec]
  ring
theorem invMap_timeReflection_eq :
    SeparatedTuples.invMap TimeAxis.timeReflection = fun x => timeFlip⁻¹ x := by
  rw [SlabInsertion.invMap_timeReflection]
  funext x
  have h₁ : timeFlip (TimeAxis.timeReflection x) = x := by
    rw [← timeReflection_eq_timeFlip, SlabInsertion.timeReflection_timeReflection]
  calc TimeAxis.timeReflection x = timeFlip⁻¹ (timeFlip (TimeAxis.timeReflection x)) :=
        (EuclidMotion.inv_apply_apply _ _).symm
    _ = timeFlip⁻¹ x := by rw [h₁]
theorem invMap_translate_eq (v : R4) :
    SeparatedTuples.invMap (SeparatedTuples.translate v) =
      fun x => (EuclidMotion.transl v)⁻¹ x := by
  rw [SlabInsertion.invMap_translate]
  funext x
  have h₁ : EuclidMotion.transl v (x - v) = x := by
    rw [EuclidMotion.transl_apply, sub_add_cancel]
  calc x - v = (EuclidMotion.transl v)⁻¹ (EuclidMotion.transl v (x - v)) :=
        (EuclidMotion.inv_apply_apply _ _).symm
    _ = (EuclidMotion.transl v)⁻¹ x := by rw [h₁]
theorem slabTimeVec_eq (t : ℝ) : SlabInsertion.timeVec t = t • timeVec := by
  change (Pi.single TimeAxis.timeIdx t : R4) = _
  funext i
  fin_cases i <;> simp [TimeAxis.timeIdx, PeriodicLattice.coordVec]
theorem spanToFree_shiftDown {η : ℝ} (hη : 0 < η)
    (G : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4))) :
    spanToFree (SlabInsertion.shiftDown hη G).1 = pullDown (η / 4) (spanToFree G.1) := by
  change spanToFree (SeparatedTuples.pushSpan
    (SeparatedTuples.translate (SlabInsertion.timeVec (-(η / 4)))) G.1) = _
  rw [spanToFree_pushSpan _ (invMap_translate_eq _), pullDown, slabTimeVec_eq]
theorem spanToFree_reflectConj (P : ReflectionPositivity.TupleForm.PositiveSpan) :
    spanToFree (ReflectionPositivity.TupleForm.reflectConj P) =
      timeFlip.actFree (freeConj (spanToFree P.1)) := by
  rw [ReflectionPositivity.TupleForm.reflectConj, spanToFree_pushSpan _ invMap_timeReflection_eq,
    spanToFree_conjugation]
theorem reflectConj_mem_lowerHalf (P : ReflectionPositivity.TupleForm.PositiveSpan) :
    ReflectionPositivity.TupleForm.reflectConj P ∈
      SeparatedTuples.spanIn {x | TimeAxis.timeComponent x < 0} := by apply _root_.YangMills.DeltaSharedProofs.p500614 <;> assumption
theorem spanClassNorm_eq {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
    {ς : SeparatedTuples.TupleFunctional} (h : AgreesWithCenteredFn ς S)
    (P : ReflectionPositivity.TupleForm.PositiveSpan) :
    ReflectionsAndOneInsertion.spanClassNorm ς P = ‖reconClass σ (spanToFree P.1)‖ := by
  have hmem : spanToFree P.1 ∈ finCombIn upperHalf := spanToFree_mem P.2
  have hd : Disjoint {x | TimeAxis.timeComponent x < 0} TimeAxis.upperHalfSpace :=
    Set.disjoint_left.2 fun x h₁ h₂ => by
      have h₃ : TimeAxis.timeComponent x < 0 := h₁
      have h₄ : TimeAxis.timeComponent x > 0 := h₂
      linarith
  have hform : ReflectionPositivity.TupleForm.reflectionForm ς P P =
      osForm S (spanToFree P.1) (spanToFree P.1) := by
    rw [ReflectionPositivity.TupleForm.reflectionForm, ← centeredFnFree_spanToFree h,
      spanToFree_formalMul hd (reflectConj_mem_lowerHalf P) P.2, spanToFree_reflectConj, osForm]
  have hc : reconClass σ (spanToFree P.1) = σ.recon.cls ⟨spanToFree P.1, hmem⟩ := by
    rw [reconClass, readClass, dif_pos hmem]
  rw [ReflectionsAndOneInsertion.spanClassNorm, hform, hc, @norm_eq_sqrt_re_inner ℂ,
    σ.recon.inner_cls]
  rfl
theorem shiftDownNorm_eq {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S)
    {ς : SeparatedTuples.TupleFunctional} (h : AgreesWithCenteredFn ς S)
    {η : ℝ} (hη : 0 < η)
    (G : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4))) :
    SlabInsertion.shiftDownNorm ς hη G = heightNorm σ (η / 4) (spanToFree G.1) := by
  rw [SlabInsertion.shiftDownNorm, spanClassNorm_eq σ h, spanToFree_shiftDown, heightNorm]
theorem singleComponent_ofReal (k : R4 → ℝ) :
    singleComponent (fun y => (k y : ℂ)) = toFree [k] := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.singleComponent_ofRealFn <;> assumption
theorem insertionForm_eq_insertion {ς : SeparatedTuples.TupleFunctional} {S : ConnFamily}
    (h : AgreesWithCenteredFn ς S) {η : ℝ} (hη : 0 < η)
    (G G' : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4)))
    {k : SeparatedTuples.RealValued} (hk : SeparatedTuples.IsC1c k)
    (hs : tsupport k ⊆ SlabInsertion.centralSlab η) :
    SlabInsertion.insertionForm ς G k hk G' =
      insertion S (spanToFree G.1) (fun y => (k y : ℂ)) (spanToFree G'.1) := by
  have hr : spanToFree (SlabInsertion.reflectConj G) =
      timeFlip.actFree (freeConj (spanToFree G.1)) := by
    rw [SlabInsertion.reflectConj, spanToFree_pushSpan _ invMap_timeReflection_eq,
      spanToFree_conjugation]
  rw [SlabInsertion.insertionForm, ← centeredFnFree_spanToFree h,
    spanToFree_formalMul (SlabInsertion.disjoint_union_timeAbove hη)
      (R4TupleForms.formalMul_mem SlabInsertion.disjoint_timeBelow_centralSlab
        (SlabInsertion.reflectConj_mem G) (SlabInsertion.singleTuple_mem hk hs)) G'.2,
    spanToFree_formalMul SlabInsertion.disjoint_timeBelow_centralSlab
      (SlabInsertion.reflectConj_mem G) (SlabInsertion.singleTuple_mem hk hs),
    hr, spanToFree_basisVec, insertion, freeMul3, flipConj, singleComponent_ofReal]
  rfl
theorem abs_time_sub_le_euclidNormVec (z x : R4) :
    |z 3 - x 3| ≤ TorusMetric.euclidNormVec (z - x) := by
  have h : (z - x) 3 ^ 2 ≤ ∑ μ, (z - x) μ ^ 2 :=
    Finset.single_le_sum (f := fun μ => (z - x) μ ^ 2) (fun μ _ => sq_nonneg _) (Finset.mem_univ 3)
  exact Real.abs_le_sqrt h
theorem euclidNormVec_le_two_mul_norm (z : R4) : TorusMetric.euclidNormVec z ≤ 2 * ‖z‖ := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.euclidNormVec_le_two_mul_norm <;> assumption
def nilAbove (η : ℝ) : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4)) :=
  ⟨SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil, Submodule.subset_span
    ⟨⟨_, SeparatedTuples.nil_mem_supportedIn _⟩, rfl⟩⟩
theorem shiftDownNorm_nilAbove (ς : SeparatedTuples.TupleFunctional) {η : ℝ} (hη : 0 < η) :
    SlabInsertion.shiftDownNorm ς hη (nilAbove η) = 1 := by
  have hact : ∀ r, SeparatedTuples.pushSpan r
      (SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil) =
      SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil := fun r => by
    have h : SeparatedTuples.pushSpan r
        (SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil) =
        SeparatedTuples.basisVec (SeparatedTuples.push r SeparatedTuples.SepTuple.nil) :=
      SeparatedTuples.linearExtend_basisVec _ _
    rw [h, SeparatedTuples.push_nil]
  have hP : (SlabInsertion.shiftDown hη (nilAbove η)).1 =
      SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil := hact _
  have hprod : SeparatedTuples.SepTuple.juxt SeparatedTuples.SepTuple.nil
      SeparatedTuples.SepTuple.nil = SeparatedTuples.SepTuple.nil := by
    have hd : SeparatedTuples.SepTuple.Composable SeparatedTuples.SepTuple.nil
        SeparatedTuples.SepTuple.nil := fun f hf => by simp [SeparatedTuples.SepTuple.nil] at hf
    exact Subtype.ext (by
      rw [SeparatedTuples.SepTuple.juxt_val hd]
      simp [SeparatedTuples.SepTuple.nil])
  have hform : ReflectionPositivity.TupleForm.reflectionForm ς (SlabInsertion.shiftDown hη (nilAbove η))
      (SlabInsertion.shiftDown hη (nilAbove η)) = 1 := by
    have h₁ : ς.spanExtension (SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil) =
        (ς SeparatedTuples.SepTuple.nil : ℂ) := SeparatedTuples.linearExtend_basisVec _ _
    rw [ReflectionPositivity.TupleForm.reflectionForm, ReflectionPositivity.TupleForm.reflectConj, hP,
      SeparatedTuples.conjugation_basisVec, hact, SeparatedTuples.formalMul_basisVec,
      hprod, h₁]
    simp [ς.map_nil]
  rw [SlabInsertion.shiftDownNorm, ReflectionsAndOneInsertion.spanClassNorm, hform]
  simp
theorem nonneg_constant_of_freeSlabBound {ς : SeparatedTuples.TupleFunctional} {M p C c : ℝ}
    (hc : 0 < c) (h : FreeSlabBound ς M p C c) : 0 ≤ C := by
  let b : ContDiffBump (0 : R4) := ⟨c / 8, c / 4, by positivity, by linarith⟩
  have hk : SeparatedTuples.IsC1c (b : R4 → ℝ) :=
    ⟨b.contDiff, b.hasCompactSupport⟩
  have hball : tsupport (b : R4 → ℝ) ⊆ TestFunctions.closedBallR4 0 (c * 1) := by
    intro z hz
    rw [b.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hz
    change TorusMetric.euclidNormVec (z - 0) ≤ c * 1
    rw [sub_zero]
    have hz' : ‖z‖ ≤ c / 4 := hz
    have := euclidNormVec_le_two_mul_norm z
    linarith
  have hb := h 1 one_pos le_rfl 0 (by simp [TimeAxis.timeComponent]) b hk hball
    (nilAbove 1) (nilAbove 1)
  rw [shiftDownNorm_nilAbove, Real.one_rpow, mul_one, mul_one, mul_one] at hb
  have hbdd : BddAbove (Set.range fun x => ‖(b : R4 → ℝ) x‖) := ⟨1, by
    rintro _ ⟨x, rfl⟩
    change ‖(b : R4 → ℝ) x‖ ≤ 1
    rw [Real.norm_of_nonneg b.nonneg]
    exact b.le_one⟩
  have hpos : 0 < TestFunctions.sharpNormR4 M (b : R4 → ℝ) := by
    have h₁ : ‖(b : R4 → ℝ) 0‖ ≤ TestFunctions.uniformNorm (b : R4 → ℝ) := le_ciSup hbdd 0
    have h₂ : (b : R4 → ℝ) 0 = 1 := b.one_of_mem_closedBall (by simp; positivity)
    rw [h₂, norm_one] at h₁
    exact lt_of_lt_of_le one_pos (h₁.trans (le_max_left _ _))
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hb) hpos
theorem holds : Holds := by
  intro m S σ ς p C c hp hc hc' hag hb
  refine ⟨hp, nonneg_constant_of_freeSlabBound hc hb, hc, hc', ?_⟩
  intro η hη _ x hx k hk hsupp F hF A hA
  have hsupp' : tsupport k ⊆ {z | TorusMetric.euclidNormVec (z - x) ≤ c * η} := by
    rw [← R4TupleForms.closedSupport_euclidean_eq defaultMirrorData k]
    exact hsupp
  have hk' : SeparatedTuples.IsC1c k := by
    refine ⟨hk.1, ?_⟩
    have h₁ : @IsCompact R4 _
        (ReflectionPositivity.AxisMirror.Ambient.closedSupport defaultMirrorData .euclidean k) :=
      (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).1 hk.2
    rw [R4TupleForms.closedSupport_euclidean_eq defaultMirrorData k] at h₁
    exact h₁
  have hslab : tsupport k ⊆ SlabInsertion.centralSlab η := by
    intro z hz
    have h₁ : |z 3 - x 3| ≤ c * η := (abs_time_sub_le_euclidNormVec z x).trans (hsupp' hz)
    have h₂ : |z 3| ≤ |z 3 - x 3| + |x 3| := by
      simpa using abs_add_le (z 3 - x 3) (x 3)
    have h₄ : c * η < 1 / 8 * η := mul_lt_mul_of_pos_right hc' hη
    change |z 3| < η / 4
    linarith
  let G : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4)) :=
    ⟨freeToSpan F, freeToSpan_mem hF⟩
  let G' : SeparatedTuples.spanIn (SlabInsertion.timeAbove (η / 4)) :=
    ⟨freeToSpan A, freeToSpan_mem hA⟩
  have hbound := hb η hη ‹_› x hx k hk' hsupp' G G'
  rw [insertionForm_eq_insertion hag hη G G' hk' hslab, shiftDownNorm_eq σ hag hη G,
    shiftDownNorm_eq σ hag hη G'] at hbound
  simp only [G, G', spanToFree_freeToSpan] at hbound
  exact hbound
end YangMills.Construction.EuclideanFunctionals.SlabInsertionTransfer
end
