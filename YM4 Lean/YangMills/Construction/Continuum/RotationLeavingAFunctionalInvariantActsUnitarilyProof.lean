import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.Continuum.ModulusOfStrongContinuityOnOneTupleProof
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.RotationInvariance.UnitaryProof
open ReflectionPositivity.TupleForm ReflectionPositiveForm ReflectionPositiveHilbert
open OrthogonalAction FormCompletion Orthogonal SeparatedTuples
open InfiniteLattice (AmbientSpace)
theorem pushSpan_basisVec (g : AmbientSpace → AmbientSpace) (T : SepTuple) :
    pushSpan g (basisVec T) = basisVec (push g T) :=
  linearExtend_basisVec _ T
theorem spanExtension_pushSpan {τ : TupleFunctional} {g : AmbientSpace → AmbientSpace}
    (hτ : τ.IsInvariant g) (S : FormalSpan) :
    τ.spanExtension (pushSpan g S) = τ.spanExtension S := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanExtension_pushSpan <;> assumption
theorem pushSpan_pushSpan {g g' g'' : AmbientSpace → AmbientSpace}
    (h : ∀ T : SepTuple, push g (push g' T) = push g'' T) (S : FormalSpan) :
    pushSpan g (pushSpan g' S) = pushSpan g'' S := by
  have hlin : pushSpan g ∘ₗ pushSpan g' = pushSpan g'' := by
    refine Finsupp.lhom_ext' fun T => LinearMap.ext_ring ?_
    change pushSpan g (pushSpan g' (basisVec T)) = pushSpan g'' (basisVec T)
    rw [pushSpan_basisVec, pushSpan_basisVec, pushSpan_basisVec, h T]
  exact LinearMap.congr_fun hlin S
theorem preservesReflectionForm_of_invariant (hLaws : Laws.Statement) {τ : TupleFunctional}
    {O : orthogonalGroupThree} (hτ : τ.IsInvariant (matMap (embedOrthogonal O))) :
    PreservesReflectionForm τ O := by
  intro A A' B B' hB hB'
  obtain ⟨-, -, -, -, -, hLast⟩ := hLaws.2.2.1 O
  have hprod := (hLast A.1 A.2 A'.1 A'.2).1
  simp only [reflectionForm, reflectConj]
  rw [hB, hB', hprod, spanExtension_pushSpan hτ]
def rotatedSpan (hLaws : Laws.Statement) (O : orthogonalGroupThree) :
    PositiveSpan →ₗ[ℂ] PositiveSpan :=
  (pushSpan (matMap (embedOrthogonal O))).restrict fun _ hA =>
    (hLaws.2.2.1 O).2.2.1.mapsTo hA
theorem rotatedSpan_surjective (hLaws : Laws.Statement) (O : orthogonalGroupThree) :
    Function.Surjective (rotatedSpan hLaws O) := by
  intro B
  obtain ⟨A, hA, hAB⟩ := (hLaws.2.2.1 O).2.2.1.surjOn B.2
  exact ⟨⟨A, hA⟩, Subtype.ext hAB⟩
theorem isRotationLift_iff (hLaws : Laws.Statement) (τ : TupleFunctional)
    (O : orthogonalGroupThree) (V : StateSpace τ →L[ℂ] StateSpace τ) :
    IsRotationLift τ O V ↔
      ∀ A, V (stateOf τ A) = stateOf τ (rotatedSpan hLaws O A) := by
  constructor
  · exact fun h A => h A _ rfl
  · intro h A A' hA'
    have : A' = rotatedSpan hLaws O A := Subtype.ext hA'
    rw [this, h]
theorem isPosSemidefHermitianForm_reflectionForm (hForm : FormPropertiesStatement)
    {τ : TupleFunctional} (hRP : ForwardCone.IsRPTimeZero τ) :
    IsPosSemidefHermitianForm (reflectionForm τ) := by apply _root_.YangMills.Construction.Continuum.RotationModulus.isPosSemidefHermitianForm_reflectionForm <;> assumption
theorem rotationLift_existsUnique_and_isometric (hLaws : Laws.Statement)
    (hForm : FormPropertiesStatement)
    (hComp : FormCompletionIsHilbertSpace) {τ : TupleFunctional} {O : orthogonalGroupThree}
    (hRP : ForwardCone.IsRPTimeZero τ)
    (hτ : τ.IsInvariant (matMap (embedOrthogonal O))) :
    (∃! V : StateSpace τ →L[ℂ] StateSpace τ, IsRotationLift τ O V) ∧
      ∀ V : StateSpace τ →L[ℂ] StateSpace τ, IsRotationLift τ O V →
        Function.Bijective V ∧ ∀ v, ‖V v‖ = ‖v‖ := by
  obtain ⟨hA, hB, hM⟩ := hComp PositiveSpan (reflectionForm τ)
    (isPosSemidefHermitianForm_reflectionForm hForm hRP)
  obtain ⟨-, -, -, -, hAdd, hSmul, hSharp, -⟩ := hA
  obtain ⟨-, -, -, -, hNorm, hTo, -, -, hDense⟩ := hB
  have hClassNorm : ∀ A, ‖classVec (reflectionForm τ) A‖ = seminormOfForm (reflectionForm τ) A :=
    fun A => by rw [hNorm, hTo, hSharp]
  let Φ : PositiveSpan →ₗ[ℂ] StateSpace τ :=
    { toFun := fun A => classVec (reflectionForm τ) (rotatedSpan hLaws O A)
      map_add' := fun A A' => asMap_injective (by
        rw [asMap_add, hTo, hTo, hTo, map_add, hAdd])
      map_smul' := fun c A => asMap_injective (by
        rw [RingHom.id_apply, asMap_smul, hTo, hTo, map_smul, hSmul]) }
  have hΦ : ∀ A, ‖Φ A‖ = seminormOfForm (reflectionForm τ) A := fun A => by
    change ‖classVec (reflectionForm τ) (rotatedSpan hLaws O A)‖ = _
    rw [hClassNorm, seminormOfForm, seminormOfForm,
      preservesReflectionForm_of_invariant hLaws hτ A A (rotatedSpan hLaws O A)
        (rotatedSpan hLaws O A) rfl rfl]
  obtain ⟨hEx, hAll⟩ := hM (StateSpace τ) 1 Φ zero_le_one fun A => by rw [one_mul, hΦ]
  have hIff : ∀ V : StateSpace τ →L[ℂ] StateSpace τ,
      IsRotationLift τ O V ↔ ∀ A, V (classVec (reflectionForm τ) A) = Φ A :=
    fun V => isRotationLift_iff hLaws τ O V
  have hRange : Set.range Φ = Set.range (classVec (reflectionForm τ)) := by
    ext v
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨B, rfl⟩
      obtain ⟨A, rfl⟩ := rotatedSpan_surjective hLaws O B
      exact ⟨A, rfl⟩
  refine ⟨?_, fun V hV => ?_⟩
  · obtain ⟨W, hWΦ, hWu⟩ := hEx
    exact ⟨W, (hIff W).2 hWΦ, fun V hV => hWu V ((hIff V).1 hV)⟩
  · obtain ⟨-, hIso⟩ := hAll V ((hIff V).1 hV)
    obtain ⟨hKeeps, hImage⟩ := hIso hΦ
    refine ⟨⟨?_, ?_⟩, hKeeps⟩
    · intro v v' h
      have h0 : ‖v - v'‖ = 0 := by
        rw [← hKeeps, map_sub, h, sub_self, norm_zero]
      exact sub_eq_zero.1 (norm_eq_zero.1 h0)
    · rw [← Set.range_eq_univ, hImage, hRange]
      exact hDense.closure_eq
theorem unitSpan_coe :
    (ReflectionPositivity.FormProperties.unitSpan : FormalSpan) = basisVec SepTuple.nil := by
  unfold ReflectionPositivity.FormProperties.unitSpan spanBasisIn
  exact congrArg Subtype.val (Module.Basis.span_apply (linearIndependent_basisVec
    TimeAxis.upperHalfSpace) ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
theorem rotationUnitary_spec {τ : TupleFunctional} {O : orthogonalGroupThree}
    (h : ∃ V : StateSpace τ →L[ℂ] StateSpace τ, IsRotationLift τ O V) :
    IsRotationLift τ O (rotationUnitary τ O) :=
  Classical.epsilon_spec (p := IsRotationLift τ O) h
theorem invariantRotationIsUnitary_holds (hLaws : Laws.Statement)
    (hForm : FormPropertiesStatement)
    (hComp : FormCompletionIsHilbertSpace) : InvariantRotationIsUnitary := by
  intro τ O hRP hτ
  obtain ⟨hEx, hFacts⟩ := rotationLift_existsUnique_and_isometric hLaws hForm hComp hRP hτ
  have hSpec := rotationUnitary_spec hEx.exists
  refine ⟨preservesReflectionForm_of_invariant hLaws hτ, ⟨hEx, ?_, ?_⟩, ?_⟩
  · exact ⟨(hFacts _ hSpec).1, (hFacts _ hSpec).2⟩
  · refine hSpec _ _ ?_
    rw [unitSpan_coe, pushSpan_basisVec, push_nil]
  · intro O' hτ'
    have hPush : ∀ T : SepTuple,
        push (matMap (embedOrthogonal O)) (push (matMap (embedOrthogonal O')) T) =
          push (matMap (embedOrthogonal (O * O'))) T := fun T => by
      rw [(hLaws.2.1 O O').2.2.2.2.1]
      exact (hLaws.1 (embedOrthogonal O) (embedOrthogonal O')).2.2.2.1 T
    have hMul : τ.IsInvariant (matMap (embedOrthogonal (O * O'))) := fun T => by
      rw [← hPush, hτ, hτ']
    refine ⟨hMul, ?_⟩
    obtain ⟨hEx', -⟩ := rotationLift_existsUnique_and_isometric hLaws hForm hComp hRP hτ'
    obtain ⟨hExMul, -⟩ := rotationLift_existsUnique_and_isometric hLaws hForm hComp hRP hMul
    have hSpec' := rotationUnitary_spec hEx'.exists
    refine hExMul.unique (rotationUnitary_spec hExMul.exists) ?_
    refine (isRotationLift_iff hLaws τ (O * O') _).2 fun A => ?_
    have hA : rotatedSpan hLaws (O * O') A = rotatedSpan hLaws O (rotatedSpan hLaws O' A) :=
      Subtype.ext (pushSpan_pushSpan hPush (A : FormalSpan)).symm
    rw [ContinuousLinearMap.comp_apply, (isRotationLift_iff hLaws τ O' _).1 hSpec' A,
      (isRotationLift_iff hLaws τ O _).1 hSpec, hA]
end YangMills.Construction.RotationInvariance.UnitaryProof
end
