import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.Continuum.WhatACanonicalDecompositionOfAFunctionalDeterminesProof
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import YangMills.Construction.SystemsWithFiveBounds.BoundOnOneInsertedFieldAtNumbers
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
private theorem sepAll_of_single {f : SeparatedTuples.RealValued} (hf : SeparatedTuples.IsC1c f) :
    [f] ∈ EuclideanFunctionals.sepAll :=
  (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll EuclideanFunctionals.defaultMirrorData [f]).1
    (R4TupleForms.singleTuple f hf).2
private theorem freeSpan_single {f : SeparatedTuples.RealValued} (hf : SeparatedTuples.IsC1c f) :
    WightmanReconstruction.freeToFormalSpan (EuclideanFunctionals.toFree [f]) =
      SeparatedTuples.basisVec (R4TupleForms.singleTuple f hf) := by
  rw [WightmanReconstruction.freeToFormalSpan, EuclideanFunctionals.liftLin_toFree _ ⟨[f], sepAll_of_single hf⟩ ]
  exact congrArg SeparatedTuples.basisVec (Subtype.ext rfl)
private theorem complexTuple_eq_single (f : ComplexTestFunctions.ComplexValued)
    (hf : ComplexTestFunctions.IsC1cComplex f) :
    WightmanReconstruction.complexTuple f = ComplexTupleComponents.singleSpan f hf := by
  classical
  unfold ComplexTupleComponents.singleSpan
  split_ifs with hreal
  · have hre : (fun x => ((ComplexTestFunctions.rePart f x : ℝ) : ℂ)) = f := by
      funext x
      have him : (f x).im = 0 := congrFun hreal x
      exact Complex.ext (by simp [ComplexTestFunctions.rePart]) (by simp [him])
    have hm := sepAll_of_single (ComplexTupleComponents.rePart_isC1c hf)
    have e := WightmanReconstruction.complexTuple_ofReal (ComplexTestFunctions.rePart f) hm
    rw [hre] at e
    rw [e]
    exact congrArg SeparatedTuples.basisVec (Subtype.ext rfl)
  · have hI : EuclideanFunctionals.nonrealIdx (fun _ : Fin 1 => f) = {0} := by
      ext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst hk
      simp only [EuclideanFunctionals.nonrealIdx, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, iff_true]
      intro hall
      exact hreal (funext hall)
    have hmem : (0 : Fin 1) ∈ EuclideanFunctionals.nonrealIdx (fun _ : Fin 1 => f) := by
      rw [hI]
      exact Finset.mem_singleton_self 0
    letI : Unique ↥(EuclideanFunctionals.nonrealIdx (fun _ : Fin 1 => f)) :=
      { default := ⟨0, hmem⟩
        uniq := fun a => Subtype.ext (Subsingleton.elim _ _) }
    rw [WightmanReconstruction.complexTuple, EuclideanFunctionals.complexList,
      ← (Equiv.funUnique ↥(EuclideanFunctionals.nonrealIdx (fun _ : Fin 1 => f)) (Fin 2)).symm.sum_comp,
      Fin.sum_univ_two, map_add, map_smul, map_smul]
    have e₀ : List.ofFn (EuclideanFunctionals.realPartComponent (fun _ : Fin 1 => f)
        ((Equiv.funUnique _ (Fin 2)).symm 0)) = [ComplexTestFunctions.rePart f] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      congr 1
      simp [EuclideanFunctionals.realPartComponent, hmem, ComplexTestFunctions.rePart]
      rfl
    have e₁ : List.ofFn (EuclideanFunctionals.realPartComponent (fun _ : Fin 1 => f)
        ((Equiv.funUnique _ (Fin 2)).symm 1)) = [ComplexTestFunctions.imPart f] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      congr 1
      simp [EuclideanFunctionals.realPartComponent, hmem, ComplexTestFunctions.imPart]
      rfl
    have s₀ : EuclideanFunctionals.imagCount (fun _ : Fin 1 => f) ((Equiv.funUnique _ (Fin 2)).symm 0) = 0 := by
      simp [EuclideanFunctionals.imagCount]
    have s₁ : EuclideanFunctionals.imagCount (fun _ : Fin 1 => f) ((Equiv.funUnique _ (Fin 2)).symm 1) = 1 := by
      simp [EuclideanFunctionals.imagCount]
    rw [e₀, e₁, s₀, s₁, freeSpan_single (ComplexTupleComponents.rePart_isC1c hf),
      freeSpan_single (ComplexTupleComponents.imPart_isC1c hf)]
    simp
private theorem pushSpan_basis (r : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (X : SeparatedTuples.SepTuple) :
    SeparatedTuples.pushSpan r (SeparatedTuples.basisVec X) = SeparatedTuples.basisVec (SeparatedTuples.push r X) :=
  SeparatedTuples.linearExtend_basisVec _ X
private theorem pushSpan_mem_upper {r : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (h : ∀ X ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace,
      SeparatedTuples.push r X ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace)
    {C : SeparatedTuples.FormalSpan} (hC : C ∈ SeparatedTuples.spanIn TimeAxis.upperHalfSpace) :
    SeparatedTuples.pushSpan r C ∈ SeparatedTuples.spanIn TimeAxis.upperHalfSpace := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨X, hX⟩, rfl⟩ := hx
    change SeparatedTuples.pushSpan r (SeparatedTuples.basisVec X) ∈ _
    rw [pushSpan_basis]
    exact Submodule.subset_span ⟨⟨_, h X hX⟩, rfl⟩
  | zero => simp
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ih
abbrev _root_.YangMills.SharedProofs.p30829 := @pushSpan_mem_upper
private theorem tupleFunctional_eq {φ ψ : SeparatedTuples.TupleFunctional} (h : ∀ Y, φ Y = ψ Y) : φ = ψ := by apply _root_.YangMills.SharedProofs.p5793 <;> assumption
private theorem reflectionForm_evalOnMap (φ : SeparatedTuples.TupleFunctional) :
    FieldFormConditions.pairing (LimitTheorem.evalOnMap φ) = ReflectionPositivity.TupleForm.reflectionForm φ := by
  have h1 : LimitTheorem.evalOnMap φ TestSpaces.sepTupleNil = 1 := by
    show φ (TupleLists.toList TestSpaces.sepTupleNil) = 1
    rw [TupleLists.toList_sepTupleNil]
    exact φ.map_nil
  rw [FieldFormConditions.pairing_eq_reflectionForm _ h1]
  congr 1
  exact tupleFunctional_eq fun Y => by
    show φ (TupleLists.toList (TupleLists.ofList Y)) = φ Y
    rw [TupleLists.toList_ofList]
abbrev _root_.YangMills.SharedProofs.p594 := @reflectionForm_evalOnMap
theorem existsInsertionBound_of_fieldOperatorBound (hLaws : OrthogonalAction.Laws.Statement)
    (hCompl : FormCompletion.FormCompletionIsHilbertSpace)
    (hWell : HilbertWellDefined.WellDefinedStatement) :
    ExistsInsertionBoundOfFieldOperatorBound := by
  intro L M N ς hN hpos hcl
  have psh := (hWell.1 _ (FieldFormConditions.pairing (LimitTheorem.evalOnMap ς)) hpos).1
  obtain ⟨-, hH, -⟩ := hCompl _ (FieldFormConditions.pairing (LimitTheorem.evalOnMap ς)) psh
  have hin := hH.2.2.2.2.2.2.1
  have hnorm : ∀ G : ReflectionPositivity.TupleForm.PositiveSpan,
      ‖FieldFormConditions.stateOf (LimitTheorem.evalOnMap ς) G‖ =
        ReflectionsAndOneInsertion.spanClassNorm ς G := fun G => by
    rw [@norm_eq_sqrt_re_inner ℂ, ReflectionsAndOneInsertion.spanClassNorm, ← reflectionForm_evalOnMap]
    exact congrArg (fun z : ℂ => Real.sqrt z.re) (hin G G)
  have hp : 0 ≤ fieldExponent N := by
    have := hN.insertionExponent_nonneg
    unfold fieldExponent
    linarith
  refine ⟨fieldExponent N, max 1 (fieldOperatorConst L M N 1), hp, le_max_left _ _, ?_⟩
  intro η hη hη₁ f hf hsupp hdiam F h
  have hf' : ComplexTestFunctions.IsC1cComplex f :=
    ⟨⟨Complex.reCLM.contDiff.comp hf.1, Complex.imCLM.contDiff.comp hf.1⟩, hf.2.1⟩
  obtain ⟨G, hG, hb⟩ := hcl η hη hη₁ 1 one_pos f hf' (fun x hx => hsupp x hx) (fun x hx y hy => hdiam x hx y hy) F
  have ht : (4 * η) • FieldFormConditions.timeUnitVec = SlabInsertion.timeVec (4 * η) := by
    funext μ
    simp [PeriodicLattice.coordVec, SlabInsertion.timeVec, Pi.single_apply]
  have hmem : SeparatedTuples.pushSpan (SeparatedTuples.translate ((4 * η) • FieldFormConditions.timeUnitVec)) F.1 ∈
      SeparatedTuples.spanIn TimeAxis.upperHalfSpace :=
    pushSpan_mem_upper (fun X hX => ((hLaws.2.2.1 1).2.1 X hX).1 (4 * η) (by positivity)) F.2
  have e : (⟨_, h⟩ : ReflectionPositivity.TupleForm.PositiveSpan) = G := by
    refine Subtype.ext ?_
    show SeparatedTuples.formalMul (WightmanReconstruction.complexTuple f)
      (ReflectionPositivity.FormProperties.shiftedSpan _ F).1 = G.1
    rw [hG, complexTuple_eq_single f hf', ReflectionPositivity.FormProperties.shiftedSpan, dif_pos hmem]
    show SeparatedTuples.formalMul _
      (SeparatedTuples.pushSpan (SeparatedTuples.translate ((4 * η) • FieldFormConditions.timeUnitVec)) F.1) = _
    rw [ht]
  rw [e, hnorm, hnorm]
  have hS : 0 ≤ TestFunctions.uniformNorm f + ⨆ x, ReflectionsAndOneInsertion.gradNorm f x := by
    have h₁ : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
    have h₂ : 0 ≤ ⨆ x, ReflectionsAndOneInsertion.gradNorm f x := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
    positivity
  have hC : 0 ≤ ReflectionsAndOneInsertion.spanClassNorm ς F := Real.sqrt_nonneg _
  have hgr : TestFunctions.uniformNorm f + ⨆ x, ReflectionsAndOneInsertion.gradNorm f x =
      WightmanReconstruction.supC1Norm f := by
    unfold WightmanReconstruction.supC1Norm
    congr 2
    funext x
    unfold ReflectionsAndOneInsertion.gradNorm
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hd : DifferentiableAt ℝ f x := (hf.1.differentiable (by norm_num)) x
    have hpart : TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by
      unfold TestFunctions.partialDerivR4
      have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) (Pi.single μ (1 : ℝ)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add x
      have hc := (by simpa using hd.hasFDerivAt :
        HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))).comp_hasDerivAt 0 hl
      exact hc.deriv
    rw [hpart]
  rw [← hgr]
  refine hb.trans ?_
  have hle := le_max_right 1 (fieldOperatorConst L M N 1)
  gcongr
end YangMills.Construction.SystemsWithFiveBounds
end
