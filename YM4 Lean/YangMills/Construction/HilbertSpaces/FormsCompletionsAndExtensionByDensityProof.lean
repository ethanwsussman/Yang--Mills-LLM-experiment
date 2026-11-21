import YangMills.Construction.HilbertSpaces.FormsCompletionsAndExtensionByDensity
import YangMills.Construction.SpectralCalculus.FormCompletionAndExtension
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.FormsOperators
namespace FormsAndCompletionsProof
section Forms
variable {E : Type*} [AddCommGroup E] [Module ℂ E] {s : E → E → ℂ}
theorem sesq_add_smul_self (hs : IsSesquilinear s) (x y : E) (a : ℂ) :
    s (x + a • y) (x + a • y) =
      s x x + a * s x y + conj a * s y x + conj a * a * s y y := by
  rw [hs.add_left, hs.add_right, hs.add_right, hs.smul_right, hs.smul_left, hs.smul_left,
    hs.smul_right]
  ring
theorem sum_quartic_roots_unity (f : ℂ → ℂ) :
    ∑ a ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), f a =
      f 1 + f Complex.I + f (-1) + f (-Complex.I) := by apply _root_.YangMills.Construction.SpectralCalculus.FormCompletionAndExtension.sum_fourthRootsOfUnity <;> assumption
theorem formPolarization_holds : FormPolarization := by
  intro E _ _ s hs x y
  have e₁ : s (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) = s x x + s x y + s y x + s y y := by
    rw [sesq_add_smul_self hs]
    simp only [map_one]
    ring
  have e₂ : s (x + Complex.I • y) (x + Complex.I • y) =
      s x x + Complex.I * s x y - Complex.I * s y x + s y y := by
    rw [sesq_add_smul_self hs, Complex.conj_I]
    linear_combination (-s y y) * Complex.I_sq
  have e₃ : s (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) = s x x - s x y - s y x + s y y := by
    rw [sesq_add_smul_self hs]
    simp only [map_neg, map_one]
    ring
  have e₄ : s (x + (-Complex.I) • y) (x + (-Complex.I) • y) =
      s x x - Complex.I * s x y + Complex.I * s y x + s y y := by
    rw [sesq_add_smul_self hs]
    simp only [map_neg, Complex.conj_I, neg_neg]
    linear_combination (-s y y) * Complex.I_sq
  constructor
  · rw [sum_quartic_roots_unity, e₁, e₂, e₃, e₄]
    simp only [map_neg, map_one, Complex.conj_I, neg_neg]
    linear_combination ((s x y - s y x) / 2) * Complex.I_sq
  · rw [sum_quartic_roots_unity, e₁, e₂, e₃, e₄]
    ring
@[reducible] def preInnerCoreOfPos (hH : IsHermitianForm s) (hP : IsPosSemidefForm s) :
    PreInnerProductSpace.Core ℂ E where
  inner := s
  conj_inner_symm x y := (hH.conj_symm y x).symm
  re_inner_nonneg x := (Complex.le_def.mp (hP.nonneg x)).1
  add_left x y z := hH.add_left x y z
  smul_left x y r := hH.smul_left r x y
theorem norm_le_qNorm_mul_qNorm (hH : IsHermitianForm s) (hP : IsPosSemidefForm s) (x y : E) :
    ‖s x y‖ ≤ qNorm s x * qNorm s y := by
  let c := preInnerCoreOfPos hH hP
  have h : ‖s x y‖ * ‖s y x‖ ≤ (s x x).re * (s y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) x y
  rw [hH.conj_symm x y, Complex.norm_conj] at h
  have ha : 0 ≤ (s x x).re := (Complex.le_def.mp (hP.nonneg x)).1
  rw [qNorm, qNorm, ← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by rw [sq]; exact h)
theorem exists_seminorm_eq_qNorm (hH : IsHermitianForm s) (hP : IsPosSemidefForm s) :
    ∃ p : Seminorm ℂ E, ∀ x, p x = qNorm s x := by
  let c := preInnerCoreOfPos hH hP
  let _ : SeminormedAddCommGroup E := InnerProductSpace.Core.toSeminormedAddCommGroup (c := c)
  let _ : NormedSpace ℂ E := InnerProductSpace.Core.toNormedSpace (c := c)
  exact ⟨normSeminorm ℂ E, fun x => rfl⟩
theorem self_eq_zero_iff_forall (hH : IsHermitianForm s) (hP : IsPosSemidefForm s) (x : E) :
    s x x = 0 ↔ ∀ y, s y x = 0 := by
  constructor
  · intro h y
    have hz : qNorm s x = 0 := by simp [qNorm, h]
    have := norm_le_qNorm_mul_qNorm hH hP y x
    rw [hz, mul_zero] at this
    exact norm_le_zero_iff.mp this
  · intro h
    exact h x
theorem quotOut_sub_mem_radical (hs : IsSesquilinear s) (x : E) :
    Quotient.out (Submodule.Quotient.mk x : E ⧸ formRadical s hs) - x ∈ formRadical s hs := by
  have h : (Submodule.Quotient.mk
      (Quotient.out (Submodule.Quotient.mk x : E ⧸ formRadical s hs)) :
        E ⧸ formRadical s hs) = Submodule.Quotient.mk x :=
    Quotient.out_eq _
  exact (Submodule.Quotient.eq _).mp h
theorem formOnQuotient_mk (hH : IsHermitianForm s) (x y : E) :
    formOnQuotient s hH.toIsSesquilinear (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      s x y := by
  have hn := quotOut_sub_mem_radical hH.toIsSesquilinear x
  have hn' := quotOut_sub_mem_radical hH.toIsSesquilinear y
  unfold formOnQuotient
  generalize Quotient.out (Submodule.Quotient.mk x : E ⧸ formRadical s hH.toIsSesquilinear) = a
    at hn ⊢
  generalize Quotient.out (Submodule.Quotient.mk y : E ⧸ formRadical s hH.toIsSesquilinear) = b
    at hn' ⊢
  have ha : a = x + (a - x) := by abel
  have hb : b = y + (b - y) := by abel
  have h₁ : ∀ z, s z (a - x) = 0 := hn
  have h₂ : ∀ z, s z (b - y) = 0 := hn'
  have h₃ : ∀ z, s (a - x) z = 0 := fun z => by rw [hH.conj_symm z, h₁, map_zero]
  rw [ha, hb, hH.add_left, hH.add_right, hH.add_right, h₂, h₂, h₃]
  simp
theorem posFormQuotient_holds : PosFormQuotient := by
  intro E _ _ s hH hP
  have hset : {x : E | s x x = 0} = {x : E | ∀ y, s y x = 0} :=
    Set.ext fun x => self_eq_zero_iff_forall hH hP x
  refine ⟨norm_le_qNorm_mul_qNorm hH hP, exists_seminorm_eq_qNorm hH hP, hset, hset.symm,
    formOnQuotient_mk hH, ?_⟩
  set N := formRadical s hH.toIsSesquilinear with hN
  have hmk := formOnQuotient_mk hH
  have hform : IsSesquilinear (formOnQuotient s hH.toIsSesquilinear) :=
    { add_left := by
        intro u v w
        obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective N u
        obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective N v
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N w
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, hH.add_left]
      smul_left := by
        intro c u w
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N u
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N w
        rw [← Submodule.Quotient.mk_smul, hmk, hmk, hH.smul_left]
      add_right := by
        intro w u v
        obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective N u
        obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective N v
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N w
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, hH.add_right]
      smul_right := by
        intro c w u
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N u
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N w
        rw [← Submodule.Quotient.mk_smul, hmk, hmk, hH.smul_right] }
  refine
    { hermitian :=
        { hform with
          conj_symm := by
            intro u v
            obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N u
            obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N v
            rw [hmk, hmk, hH.conj_symm] }
      positive :=
        { hform with
          nonneg := by
            intro u
            obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N u
            rw [hmk]
            exact hP.nonneg x }
      definite := ?_ }
  intro u hu
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N u
  rw [hmk] at hu
  exact (Submodule.Quotient.mk_eq_zero N).mpr ((self_eq_zero_iff_forall hH hP x).mp hu)
end Forms
theorem denseExtension_holds : DenseExtension := by
  intro H H' _ _ _ _ _ _ D c T hD hc hb
  have hDd : Dense (D : Set H) := (isDenseSet_iff_dense _).mp hD
  have hInd : IsUniformInducing (D.subtypeL : D →L[ℂ] H) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hDense : DenseRange (D.subtypeL : D →L[ℂ] H) := by
    intro x
    simpa [DenseRange] using hDd x
  let fL : D →L[ℂ] H' := T.mkContinuous c hb
  let G : H →L[ℂ] H' := fL.extend D.subtypeL
  have hG : ∀ v : D, G v = T v := fun v => ContinuousLinearMap.extend_eq fL hDense hInd v
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro v
    refine hDense.induction_on v
      (isClosed_le G.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro y
    change ‖G (y : H)‖ ≤ c * ‖(y : H)‖
    rw [hG]
    exact hb y
  · intro B' hB'
    refine ContinuousLinearMap.ext fun v => congrFun
      (Continuous.ext_on hDd B'.continuous G.continuous ?_) v
    intro y hy
    exact (hB' ⟨y, hy⟩).trans (hG ⟨y, hy⟩).symm
  · intro hn hr
    have hNorm : ∀ v, ‖G v‖ = ‖v‖ := by
      intro v
      refine hDense.induction_on v (isClosed_eq G.continuous.norm continuous_norm) ?_
      intro y
      change ‖G (y : H)‖ = ‖(y : H)‖
      rw [hG]
      exact hn y
    let GI : H →ₗᵢ[ℂ] H' := ⟨G.toLinearMap, hNorm⟩
    have hClosed : IsClosed (range GI) := GI.isometry.isClosedEmbedding.isClosed_range
    have hSub : range T ⊆ range GI := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hG y⟩
    have hAll : closure (range T) ⊆ range GI := hClosed.closure_subset_iff.2 hSub
    have hSurj : Function.Surjective GI := fun y =>
      hAll ((isDenseSet_iff_dense _).mp hr y)
    exact ⟨LinearIsometryEquiv.ofSurjective GI hSurj, fun v => rfl⟩
theorem clmEqOfEqOnDense_holds : CLMEqOfEqOnDense := by
  intro H H' _ _ _ _ _ _ S A A' hS h
  exact ContinuousLinearMap.ext fun v => congrFun
    (Continuous.ext_on ((isDenseSet_iff_dense _).mp hS) A.continuous A'.continuous h) v
theorem unitaryMapInner_holds : UnitaryMapInner := by
  intro H H' _ _ _ _ _ _ U
  exact ⟨fun u v => U.inner_map_map u v, U.symm, fun v => U.symm_apply_apply v,
    fun v => U.apply_symm_apply v⟩
theorem unitaryAdjEqInv_holds : UnitaryAdjEqInv := by
  intro H _ _ _ U
  have hU : IsDenselyDefined (ofCLM (U.toContinuousLinearEquiv : H →L[ℂ] H)) :=
    (isDenseSet_iff_dense _).mpr (by
      change Dense ((⊤ : Submodule ℂ H) : Set H)
      simp)
  have hspec : ∀ (u : H) (w : (ofCLM (U.toContinuousLinearEquiv : H →L[ℂ] H)).domain),
      ⟪u, ofCLM (U.toContinuousLinearEquiv : H →L[ℂ] H) w⟫_ℂ = ⟪U.symm u, (w : H)⟫_ℂ := by
    intro u w
    have h := U.symm.inner_map_eq_flip u (w : H)
    exact h.symm
  have hdom : (adj (ofCLM (U.toContinuousLinearEquiv : H →L[ℂ] H)) hU).domain = ⊤ :=
    eq_top_iff.mpr fun u _ => ⟨U.symm u, hspec u⟩
  refine ⟨hU, hdom, ?_⟩
  refine (unboundedOp_eq_iff _ _).mpr ⟨hdom.trans rfl, fun w => ?_⟩
  exact adjValue_unique hU (φ := (w : H)) (hspec (w : H))
    (adjValue_spec (ofCLM (U.toContinuousLinearEquiv : H →L[ℂ] H)) w)
section Completions
variable {W : Type} [AddCommGroup W] [Module ℂ W] {s : W → W → ℂ}
@[reducible] def innerCoreOfInnerProductForm (hs : IsInnerProductForm s) :
    InnerProductSpace.Core ℂ W :=
  { preInnerCoreOfPos hs.hermitian hs.positive with definite := hs.definite }
theorem exists_hilbertCompletion (hs : IsInnerProductForm s) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (j : W →ₗ[ℂ] H), IsHilbertCompletion s j := by
  let c := innerCoreOfInnerProductForm hs
  let _ : NormedAddCommGroup W := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ W := InnerProductSpace.ofCore c.toCore
  refine ⟨UniformSpace.Completion W, inferInstance, inferInstance, inferInstance,
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := W)).toLinearMap, ?_⟩
  refine ⟨hs, ?_, ?_⟩
  · intro x y
    exact UniformSpace.Completion.inner_coe x y
  · exact (isDenseSet_iff_dense _).mpr UniformSpace.Completion.denseRange_coe
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem hilbertCompletion_injective {j : W →ₗ[ℂ] H} (hj : IsHilbertCompletion s j) :
    Function.Injective j := by
  intro u v huv
  have h0 : j (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h1 : s (u - v) (u - v) = 0 := by rw [← hj.inner_map, h0, inner_zero_left]
  exact sub_eq_zero.mp (hj.isInnerProduct.definite _ h1)
theorem existsUnique_unitaryMap_comp {j : W →ₗ[ℂ] H} {j' : W →ₗ[ℂ] H'}
    (hj : IsHilbertCompletion s j) (hj' : IsHilbertCompletion s j') :
    ∃! U : UnitaryMap H H', ∀ w, U (j w) = j' w := by
  have hnorm : ∀ w, ‖j' w‖ = ‖j w‖ := fun w => by
    rw [norm_eq_sqrt_re_inner_self (j' w), norm_eq_sqrt_re_inner_self (j w), hj.inner_map,
      hj'.inner_map]
  let e : W ≃ₗ[ℂ] LinearMap.range j :=
    LinearEquiv.ofInjective j (hilbertCompletion_injective hj)
  let T : LinearMap.range j →ₗ[ℂ] H' := j' ∘ₗ e.symm.toLinearMap
  have hT : ∀ w, T (e w) = j' w := fun w => by simp [T]
  have hcoe : ∀ w, ((e w : LinearMap.range j) : H) = j w := fun w => rfl
  have hn : ∀ v : LinearMap.range j, ‖T v‖ = ‖(v : H)‖ := by
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [hT, hcoe, hnorm]
  have hD : IsDenseSet ((LinearMap.range j : Submodule ℂ H) : Set H) := by
    rw [LinearMap.coe_range]
    exact hj.dense_range
  have hr : IsDenseSet (range T) := by
    have h : range T = range j' := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        obtain ⟨w, rfl⟩ := e.surjective v
        exact ⟨w, (hT w).symm⟩
      · rintro ⟨w, rfl⟩
        exact ⟨e w, hT w⟩
    rw [h]
    exact hj'.dense_range
  obtain ⟨B, hB, -, -, hU⟩ := denseExtension_holds H H' (LinearMap.range j) 1 T hD zero_le_one
    (fun v => by rw [hn, one_mul])
  obtain ⟨U, hUB⟩ := hU hn hr
  have hUj : ∀ w, U (j w) = j' w := fun w => by
    rw [hUB, ← hcoe, hB, hT]
  refine ⟨U, hUj, ?_⟩
  intro V hV
  have hd : Dense (range j) := (isDenseSet_iff_dense _).mp hj.dense_range
  refine LinearIsometryEquiv.ext fun v => congrFun
    (Continuous.ext_on hd V.continuous U.continuous ?_) v
  rintro _ ⟨w, rfl⟩
  exact (hV w).trans (hUj w).symm
end Completions
theorem hilbertCompletionExistsUnique_holds : HilbertCompletionExistsUnique := by
  intro W _ _ s hs
  refine ⟨exists_hilbertCompletion hs, ?_⟩
  intro H H' _ _ _ _ _ _ j j' hj hj'
  exact existsUnique_unitaryMap_comp hj hj'
end FormsAndCompletionsProof
open FormsAndCompletionsProof in
theorem formsAndCompletions_holds : FormsAndCompletions :=
  ⟨formPolarization_holds, posFormQuotient_holds, denseExtension_holds, clmEqOfEqOnDense_holds,
    unitaryMapInner_holds, unitaryAdjEqInv_holds, hilbertCompletionExistsUnique_holds⟩
end YangMills.Construction.FormsOperators
