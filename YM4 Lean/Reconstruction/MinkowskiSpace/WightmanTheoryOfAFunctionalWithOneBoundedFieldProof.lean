import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctionsProof
import Reconstruction.LimitTheorem.WightmanTheoryOfAComponentOnOneCompletion
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequenceProof
import Reconstruction.MinkowskiSpace.FormRepresentsTheSequenceOfItsFunctional
import Reconstruction.MinkowskiSpace.ReconstructionFromTheAxiomsAndABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoundedFieldWightman
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal)
open FieldForms FormReconstruction WightmanTheory FormsOperators OneLoopNotation ComplexHilbert
  MinkowskiSpace
section Congruence
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : ProjectionMeasures.FourBorelSet → BddOp K} {Ω : K} {A A' : ℝ → BddOp K}
theorem isBoundedFieldForm_of_eqOn_pos {p C : ℝ} (h : ∀ s : ℝ, 0 < s → A s = A' s)
    (hf : IsBoundedFieldForm E Ω A' p C) : IsBoundedFieldForm E Ω A p C where
  exponent_nonneg := hf.exponent_nonneg
  one_le_const := hf.one_le_const
  isPVM := hf.isPVM
  supportedOn := hf.supportedOn
  norm_vacuum := hf.norm_vacuum
  origin_fixes := hf.origin_fixes
  isSelfAdjoint s hs := by
    rw [h s hs]
    exact hf.isSelfAdjoint s hs
  shift_conj s a hs ha := by
    rw [h s hs, h (s + a) (add_pos hs ha)]
    exact hf.shift_conj s a hs ha
  opNorm_le s hs := by
    rw [h s hs]
    exact hf.opNorm_le s hs
theorem halfMinTubeGap_pos {n : ℕ} {ζ : Fin (n + 1) → ComplexVec4}
    (hζ : ∀ k, ζ k ∈ futureTube) : 0 < halfMinTubeGap ζ := by
  unfold halfMinTubeGap
  exact mul_pos (by norm_num) ((Finset.lt_inf'_iff _).2 fun k _ => hζ k)
theorem fieldProduct_congr {n : ℕ} {ζ : Fin (n + 1) → ComplexVec4}
    (h : A (halfMinTubeGap ζ) = A' (halfMinTubeGap ζ)) :
    fieldProduct E A n ζ = fieldProduct E A' n ζ := by
  cases n with
  | zero => rfl
  | succ n => simp only [fieldProduct, h]
theorem imagTimeShift_one_mem_futureTube : imagTimeShift 1 ∈ futureTube := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.imagTimeShift_one_mem_futureTube <;> assumption
theorem orderedSchwinger_congr (h : ∀ s : ℝ, 0 < s → A s = A' s) (m : ℕ)
    {x : TestSpaces.PointTuple (m + 1)} (hx : x ∈ TestSpaces.increasingTimes (m + 1)) :
    orderedSchwinger E Ω A m x = orderedSchwinger E Ω A' m x := by
  have hin : ∀ k, consPoint (imagTimeShift 1)
      (snocPoint (FieldForms.wickDiffs x) (imagTimeShift 1)) k ∈ futureTube := by
    intro k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simpa [consPoint] using imagTimeShift_one_mem_futureTube
    · refine Fin.lastCases ?_ (fun i => ?_) k'
      · simpa [consPoint, snocPoint] using imagTimeShift_one_mem_futureTube
      · simpa [consPoint, snocPoint] using wickDiffs_mem_futureTube hx i
  simp only [orderedSchwinger, vacuumExpectation]
  rw [fieldProduct_congr (h _ (halfMinTubeGap_pos hin))]
theorem orderedIntegral_congr (h : ∀ s : ℝ, 0 < s → A s = A' s) (m : ℕ)
    (φ : TestSpaces.PointTuple (m + 1) → ℂ) :
    orderedIntegral E Ω A m φ = orderedIntegral E Ω A' m φ := by
  unfold orderedIntegral
  congr 1
  funext x
  by_cases hx : x ∈ TestSpaces.increasingTimes (m + 1)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, orderedSchwinger_congr h m hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
end Congruence
section Sequence
variable {sigma : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
theorem mem_flatSchwartzSet_of_mem {m : ℕ} {f : TestSpaces.PointTuple (m + 1) → ℂ}
    (h : f ∈ schwartzFlatOffDiagonal (m + 1)) : f ∈ TestSpaces.flatSchwartzSet (m + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).superset h
theorem flatSequenceAsMaps_succ (S : FlatSequence) (m : ℕ)
    (φ : TestSpaces.flatSchwartzSet (m + 1)) (ψ : schwartzFlatOffDiagonal (m + 1))
    (h : φ.1 = ψ.1) :
    WightmanReconstruction.flatSequenceAsMaps S (m + 1) φ = S.atSucc m ψ := by apply _root_.YangMills.Construction.LimitTheorem.ComponentConditions.flatSequenceAsMaps_succ <;> assumption
theorem isLinearFunctionalSeq_of_isSchwingerFamily
    (h0 : ∀ c : ConfigSpace.flatOffDiagonalAt 0, S 0 c = c.1)
    (hS : TestSpaces.IsSchwingerFamily sigma (WightmanReconstruction.flatSequenceAsMaps S)) :
    ConfigSpace.IsLinearFunctionalSeq S := by
  refine ⟨h0, fun m c c' φ ψ χ h => ?_⟩
  have e := (hS.1 (m + 1) (Nat.succ_pos m)).1 c c' ⟨φ.1, mem_flatSchwartzSet_of_mem φ.2⟩
    ⟨ψ.1, mem_flatSchwartzSet_of_mem ψ.2⟩ ⟨χ.1, mem_flatSchwartzSet_of_mem χ.2⟩ h
  rwa [flatSequenceAsMaps_succ S m _ χ rfl, flatSequenceAsMaps_succ S m _ φ rfl,
    flatSequenceAsMaps_succ S m _ ψ rfl] at e
theorem isContinuousSeq_of_isSchwingerFamily
    (hS : TestSpaces.IsSchwingerFamily sigma (WightmanReconstruction.flatSequenceAsMaps S)) :
    ConfigSpace.IsContinuousSeq S := fun m =>
  (SchwartzAxioms.isContinuousOnFlat_iff _).1
    ⟨(hS.1 (m + 1) (Nat.succ_pos m)).1, (hS.1 (m + 1) (Nat.succ_pos m)).2.1⟩
theorem agreesOnTensors_of_isSchwingerFamily
    (hS : TestSpaces.IsSchwingerFamily sigma (WightmanReconstruction.flatSequenceAsMaps S)) :
    ReflectionPositivityFromValues.AgreesOnTensors sigma S := by apply _root_.YangMills.Construction.AdmissibleClustering.agreesOnTensors_of_schwinger <;> assumption
theorem exists_isBoundedExtensionFamily
    (hS : TestSpaces.IsSchwingerFamily sigma (WightmanReconstruction.flatSequenceAsMaps S)) :
    ∃ (k : ℕ → ℕ) (c : ℕ → ℝ), TestSpaces.IsBoundedExtensionFamily sigma
      (WightmanReconstruction.flatSequenceAsMaps S) k c := by
  have hex : ∀ n : ℕ, ∃ (k : ℕ) (c : ℝ), 1 ≤ n → 0 < k ∧ 0 ≤ c ∧
      ∀ φ : TestSpaces.flatSchwartzSet n,
        ENNReal.ofReal ‖WightmanReconstruction.flatSequenceAsMaps S n φ‖ ≤
          ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1 := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨k, c, h₁, h₂, h₃⟩ := (hS.1 n hn).2.1
      exact ⟨k, c, fun _ => ⟨h₁, h₂, h₃⟩⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose k c h using hex
  exact ⟨k, c, hS.2, fun n hn =>
    ⟨(hS.1 n hn).1, (h n hn).1, (h n hn).2.1, (h n hn).2.2, (hS.1 n hn).2.2⟩⟩
theorem sepTupleInvariant_of_isMotionInvariant {r : Motions.RigidMotion}
    (h : WightmanReconstruction.IsMotionInvariant sigma r) (n : ℕ) :
    TestSpaces.SepTupleInvariant sigma n r := by
  intro X Y _ hY
  have e : (⟨n, Y⟩ : TestSpaces.SepTuple) = UpperHalfTensors.actOnSTuple r ⟨n, X⟩ :=
    TestSpaces.sepTuple_ext _ _ rfl fun k => congrFun hY k
  rw [e]
  exact h _
theorem sepTupleSymmetric_of_isPermutationInvariant
    (h : WightmanReconstruction.IsPermutationInvariant sigma) (n : ℕ) (hn : 1 ≤ n) :
    TestSpaces.SepTupleSymmetric sigma n := by
  intro τ X Y _ hY
  have e : Y = WightmanReconstruction.permuteComponents X τ := Subtype.ext hY
  rw [e]
  exact h n hn X τ
end Sequence
section Theories
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem uniqueVacuum_of_isUnitaryImage {L : UnitaryMap H H'} {T : HermitianScalarTheory H}
    {T' : HermitianScalarTheory H'} (hI : IsUnitaryImage L T T') (hU : T.UniqueVacuum) :
    T'.UniqueVacuum := by
  intro ψ hψ
  obtain ⟨c, hc⟩ := hU (L.symm ψ) fun a => by
    apply L.injective
    rw [← hI.rep_eq]
    simpa using hψ a
  refine ⟨c, ?_⟩
  rw [hI.vacuum_eq, ← map_smul, ← hc]
  simp
theorem uniqueVacuum_of_rep_vacuum_eq {T T₀ : HermitianScalarTheory H}
    (hr : ∀ g, T.rep g = T₀.rep g) (hv : T.vacuum = T₀.vacuum)
    (hU : T₀.UniqueVacuum) : T.UniqueVacuum := by
  intro ψ hψ
  obtain ⟨c, hc⟩ := hU ψ fun a => by rw [← hr]; exact hψ a
  exact ⟨c, by rw [hv]; exact hc⟩
end Theories
theorem wightmanFromBoundedFieldFunctional_holds
    (hexists : InsertedFieldForm.BoundedFieldFormOfInsertionBound)
    (hcarry : TestSpaces.SchwingerPropertiesTransfer)
    (hrp : ReflectionPositivityFromValues.Statement)
    (hrep : RepresentedSequence.Statement)
    (hsch : FieldForms.EuclideanSchwingerProperties)
    (hwight : FieldFormHilbert.WightmanFromEuclideanForm)
    (hos : MinkowskiSpace.ReconstructionFromBoundedForm) :
    WightmanFromBoundedFieldFunctional := by
  intro sigma hsigma hsym hpos E hE hbound A hA S hS0 hS
  obtain ⟨p, C, hp, hC, hbd⟩ := hbound
  obtain ⟨A₀, -, hU, hF₀, -, hRE⟩ := hexists sigma hsigma hsym hpos E hE p C hp hC hbd
  have hAA : ∀ s : ℝ, 0 < s → A s = A₀ s := hU A hA
  have hF := isBoundedFieldForm_of_eqOn_pos hAA hF₀
  have hEuc : IsEuclidean E (FieldFormConditions.vacuumState sigma) A := fun m x hx R τ hy => by
    rw [orderedSchwinger_congr hAA m hy, orderedSchwinger_congr hAA m hx]
    exact hRE.2.1 m x hx R τ hy
  have hRepσ : RepresentsFunctional E (FieldFormConditions.vacuumState sigma) A sigma :=
    ⟨hRE.1.1, fun m X hX => by
      rw [orderedIntegral_congr hAA]
      exact hRE.1.2 m X hX⟩
  have hSeq := isLinearFunctionalSeq_of_isSchwingerFamily hS0 hS
  have hCont := isContinuousSeq_of_isSchwingerFamily hS
  have hVal := agreesOnTensors_of_isSchwingerFamily hS
  obtain ⟨k, c, hb⟩ := exists_isBoundedExtensionFamily hS
  obtain ⟨-, hpt, -⟩ := hcarry sigma _ k c hsigma hb
  have hMotion : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (r : Motions.RigidMotion)
      (h : Motions.actOnFun r φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
      S.atSucc m ⟨_, h⟩ = S.atSucc m φ := by
    intro m φ r h
    obtain ⟨h', e⟩ := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_mem φ.2⟩).1 r
      (sepTupleInvariant_of_isMotionInvariant (hsym.2 r) (m + 1))
    rwa [flatSequenceAsMaps_succ S m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ S m _ φ rfl] at e
  have hE1 : ConfigSpace.IsEuclidInvariant S := by
    intro m φ r h
    obtain ⟨R, hR, v, hv⟩ := r.2
    have hfun : ConfigSpace.motionAct r φ.1 = Motions.actOnFun ⟨R, hR, v⟩ φ.1 := by
      funext x
      simp only [Motions.actOnFun, ConfigSpace.motionAct]
      exact congrArg φ.1 (funext fun i => ConfigSpace.EuclidMotion.invMap_eq r hR hv _)
    have h' : Motions.actOnFun ⟨R, hR, v⟩ φ.1 ∈ schwartzFlatOffDiagonal (m + 1) := hfun ▸ h
    rw [← hMotion m φ ⟨R, hR, v⟩ h']
    exact congrArg _ (Subtype.ext hfun)
  have hE3 : ConfigSpace.IsPermSymmetric S := by
    intro m φ τ h
    obtain ⟨h', e⟩ := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_mem φ.2⟩).2.1
      (sepTupleSymmetric_of_isPermutationInvariant hsym.1 (m + 1) (Nat.succ_pos m)) τ
    rwa [flatSequenceAsMaps_succ S m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ S m _ φ rfl] at e
  have hReal : ConfigSpace.IsReflectionReal S := by
    intro m φ h
    obtain ⟨h', e⟩ :=
      (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_mem φ.2⟩).2.2.2.2
        (sepTupleInvariant_of_isMotionInvariant (hsym.2 _) (m + 1))
    rwa [flatSequenceAsMaps_succ S m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ S m _ φ rfl] at e
  have hE2 : ConfigSpace.IsOSPositive S :=
    hrp sigma S hsigma hSeq hCont hVal fun F => by
      have h := Complex.le_def.1 (hpos.nonneg F)
      exact ⟨h.2.symm, h.1⟩
  have hRep := hrep E (FieldFormConditions.vacuumState sigma) A _ _ hF sigma S hRepσ hSeq hCont hVal
  have hSchw := hsch (FieldFormConditions.StateSpace sigma) E (FieldFormConditions.vacuumState sigma)
    A _ _ hF hEuc
  have WT := hwight E (FieldFormConditions.vacuumState sigma) A _ _ hF hEuc
  have RC := hos S hSeq hCont hE1 hE2 hE3 E (FieldFormConditions.vacuumState sigma) A _ _ hF hRep
  obtain ⟨T', J, T, h₁, h₂, h₃, h₄, h₅, h₆⟩ := RC.exists_subspaceTheory
  obtain ⟨T₀, hT₀⟩ := WT.exists_theory
  have := WT.separable
  exact
    { euclid_invariant := hE1
      os_positive := hE2
      perm_symmetric := hE3
      reflection_real := hReal
      im_eq_zero_of_real := fun m φ hr => by
        have e := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_mem φ.2⟩).2.2.1 hr
        rwa [flatSequenceAsMaps_succ S m _ φ rfl] at e
      represents := hRep
      eq_integralSchwinger := fun m φ hφ h =>
        (hSchw m).2.2.2.1 S hRep (fun φ' R h' => hMotion m φ' _ h')
          (fun φ' τ h' => hE3 m φ' τ h') φ hφ h
      linear_seq := hSeq
      continuous_seq := hCont
      bounded_form := ⟨_, _, hF⟩
      timeShift_spec := ⟨RC.nonexpanding, RC.shiftOp_spec⟩
      separable := J.symm.surjective.denseRange.separableSpace J.symm.continuous
      exists_theory := ⟨T', J, T, h₁, h₂, h₃, h₄, h₅, h₆, fun hfix =>
        uniqueVacuum_of_isUnitaryImage h₆ (uniqueVacuum_of_rep_vacuum_eq
          (fun g => (WT.existsUnique_rep g).unique (h₅.rep_eq g)
            (hT₀.isFormTheory.rep_eq g))
          (Subtype.ext (h₅.vacuum_eq.trans hT₀.isFormTheory.vacuum_eq.symm))
          (hT₀.uniqueVacuum hfix))⟩ }
end YangMills.Construction.BoundedFieldWightman
end
