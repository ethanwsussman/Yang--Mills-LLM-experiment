import YangMills.Construction.HilbertSpace.SemidefiniteFormHilbertSpace
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.FormCompletion.RieszRepresentation
theorem eq_zero_of_sesquilinear_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : V → V → ℂ)
    (add_left : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (smul_left : ∀ (z : ℂ) x y, b (z • x) y = conj z * b x y)
    (add_right : ∀ x y y', b x (y + y') = b x y + b x y')
    (smul_right : ∀ (z : ℂ) x y, b x (z • y) = z * b x y)
    (diag : ∀ z, b z z = 0) (x y : V) : b x y = 0 := by
  have e1 := diag (x + y)
  have e2 := diag (x + Complex.I • y)
  simp only [add_left, add_right, smul_left, smul_right, diag, Complex.conj_I] at e1 e2
  have e3 : b x y - b y x = 0 :=
    mul_left_cancel₀ Complex.I_ne_zero (by linear_combination e2)
  linear_combination (1 / 2) * e1 + (1 / 2) * e3
section SingleForm
variable {E : Type} [AddCommGroup E] [Module ℂ E] {q : E → E → ℂ}
@[instance_reducible] def preInnerCore (hq : IsPosSemidefHermitianForm q) :
    PreInnerProductSpace.Core ℂ E where
  inner := q
  conj_inner_symm u v := (hq.hermitian v u).symm
  re_inner_nonneg u := hq.nonneg u
  add_left := hq.add_left
  smul_left u v z := hq.smul_left z u v
def SemiInnerSpace (_ : IsPosSemidefHermitianForm q) : Type := E
variable (hq : IsPosSemidefHermitianForm q)
instance : SeminormedAddCommGroup (SemiInnerSpace hq) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ E _ _ _ (preInnerCore hq)
instance : InnerProductSpace ℂ (SemiInnerSpace hq) :=
  @InnerProductSpace.ofCore ℂ E _ _ _ (preInnerCore hq)
abbrev Completed : Type := UniformSpace.Completion (SemiInnerSpace hq)
def toCompleted : E →ₗ[ℂ] Completed hq where
  toFun u := UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := SemiInnerSpace hq) u
  map_add' u v :=
    map_add (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := SemiInnerSpace hq)) u v
  map_smul' z u :=
    map_smul (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := SemiInnerSpace hq)) z u
include hq
theorem inner_toCompleted (u v : E) : ⟪toCompleted hq u, toCompleted hq v⟫_ℂ = q u v :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := SemiInnerSpace hq) u v
theorem norm_toCompleted (u : E) : ‖toCompleted hq u‖ = seminormOfForm q u := by
  rw [@norm_eq_sqrt_re_inner ℂ, inner_toCompleted, RCLike.re_to_complex]
  rfl
theorem denseRange_toCompleted : DenseRange (toCompleted hq) :=
  UniformSpace.Completion.denseRange_coe (α := SemiInnerSpace hq)
def pairing : Completed hq →ₗ[ℂ] (E → ℂ) where
  toFun x u := ⟪toCompleted hq u, x⟫_ℂ
  map_add' x y := by
    funext u
    simp [inner_add_right]
  map_smul' z x := by
    funext u
    simp [inner_smul_right]
theorem pairing_apply (x : Completed hq) (u : E) : pairing hq x u = ⟪toCompleted hq u, x⟫_ℂ := rfl
theorem pairing_toCompleted (v : E) : pairing hq (toCompleted hq v) = formClass q v := by
  funext u
  exact inner_toCompleted hq u v
theorem norm_mem_antilinearBounds (x : Completed hq) :
    ‖x‖ ∈ antilinearBounds q (pairing hq x) :=
  ⟨norm_nonneg _, fun u => by
    rw [← norm_toCompleted hq, mul_comm]
    exact norm_inner_le_norm (𝕜 := ℂ) (toCompleted hq u) x⟩
theorem pairing_mem (x : Completed hq) : pairing hq x ∈ boundedConjLinearMaps q :=
  ⟨⟨fun u v => by simp [pairing_apply, map_add, inner_add_left],
    fun z u => by simp [pairing_apply, map_smul, inner_smul_left]⟩, _,
    norm_mem_antilinearBounds hq x⟩
theorem dualNorm_pairing (x : Completed hq) : dualNorm q (pairing hq x) = ‖x‖ := by
  refine le_antisymm (csInf_le ⟨0, fun C hC => hC.1⟩ (norm_mem_antilinearBounds hq x)) ?_
  refine le_csInf ⟨_, norm_mem_antilinearBounds hq x⟩ fun C hC => ?_
  have bound : ∀ y : Completed hq, ‖⟪y, x⟫_ℂ‖ ≤ C * ‖y‖ := fun y =>
    (denseRange_toCompleted hq).induction_on y
      (isClosed_le (continuous_id.inner continuous_const).norm
        (continuous_const.mul continuous_norm))
      fun u => by
        rw [norm_toCompleted]
        exact hC.2 u
  have hxx : ‖x‖ * ‖x‖ ≤ C * ‖x‖ := by
    have e1 := bound x
    rw [inner_self_eq_norm_sq_to_K] at e1
    simpa [sq] using e1
  rcases (norm_nonneg x).eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact hC.1
  · exact le_of_mul_le_mul_right hxx hpos
theorem pairing_injective : Function.Injective (pairing hq) := by
  refine (injective_iff_map_eq_zero (pairing hq)).2 fun x hx => norm_eq_zero.1 ?_
  rw [← dualNorm_pairing hq x, hx, ← map_zero (pairing hq), dualNorm_pairing, norm_zero]
theorem exists_pairing_eq {φ : E → ℂ} (hφ : φ ∈ boundedConjLinearMaps q) :
    ∃ x, pairing hq x = φ := by
  obtain ⟨ha, C, hC⟩ := hφ
  let f : E →ₗ[ℂ] ℂ :=
    { toFun := fun u => conj (φ u)
      map_add' := fun u v => by simp [ha.map_add]
      map_smul' := fun z u => by simp [ha.map_smul] }
  have hb : ∀ u, ‖f u‖ ≤ C * ‖toCompleted hq u‖ := fun u => by
    rw [norm_toCompleted]
    simpa [f] using hC.2 u
  let g : StrongDual ℂ (Completed hq) := f.extendOfNorm (toCompleted hq)
  refine ⟨(InnerProductSpace.toDual ℂ (Completed hq)).symm g, ?_⟩
  funext u
  have e1 : g (toCompleted hq u) = conj (φ u) :=
    LinearMap.extendOfNorm_eq (denseRange_toCompleted hq) ⟨C, hb⟩ u
  have e2 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := toCompleted hq u) (y := g)
  rw [pairing_apply, ← inner_conj_symm, e2, e1, Complex.conj_conj]
theorem range_pairing :
    (LinearMap.range (pairing hq) : Set (E → ℂ)) = boundedConjLinearMaps q := by
  ext φ
  constructor
  · rintro ⟨x, rfl⟩
    exact pairing_mem hq x
  · exact exists_pairing_eq hq
theorem formCompletion_eq : formCompletion q = boundedConjLinearMaps q := by
  refine Set.Subset.antisymm (fun φ hφ => hφ.1) fun φ hφ => ⟨hφ, ?_⟩
  obtain ⟨x, rfl⟩ := exists_pairing_eq hq hφ
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_toCompleted hq x)
  choose s hs using hu
  refine ⟨s, ?_⟩
  have he : ∀ n, dualNorm q (pairing hq x - formClass q (s n)) = ‖u n - x‖ := fun n => by
    rw [← pairing_toCompleted hq, ← map_sub, dualNorm_pairing, hs, norm_sub_rev]
  simpa only [he] using tendsto_iff_norm_sub_tendsto_zero.1 hlim
theorem exists_pairing_eq_of_mem_formCompletion {φ : E → ℂ} (hφ : φ ∈ formCompletion q) :
    ∃ x, pairing hq x = φ :=
  exists_pairing_eq hq hφ.1
theorem isDualNormOn_bounded : IsDualNormOn q (boundedConjLinearMaps q) where
  nonneg φ hφ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq hq hφ
    rw [dualNorm_pairing]
    exact norm_nonneg _
  eq_zero φ hφ h0 := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq hq hφ
    rw [dualNorm_pairing, norm_eq_zero] at h0
    rw [h0, map_zero]
  add_le φ hφ φ' hφ' := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq hq hφ'
    rw [← map_add, dualNorm_pairing, dualNorm_pairing, dualNorm_pairing]
    exact norm_add_le x y
  smul z φ hφ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq hq hφ
    rw [← map_smul, dualNorm_pairing, dualNorm_pairing, norm_smul]
theorem isDualComplete_bounded : IsDualComplete q (boundedConjLinearMaps q) := by
  intro u hu hc
  choose v hv using fun n => exists_pairing_eq hq (hu n)
  have hcs : CauchySeq v := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨n₀, hn₀⟩ := hc ε hε
    refine ⟨n₀, fun n hn l hl => ?_⟩
    have e1 := hn₀ n hn l hl
    rwa [← hv n, ← hv l, ← map_sub, dualNorm_pairing, ← dist_eq_norm] at e1
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨pairing hq x, pairing_mem hq x, ?_⟩
  have he : ∀ n, dualNorm q (u n - pairing hq x) = ‖v n - x‖ := fun n => by
    rw [← hv n, ← map_sub, dualNorm_pairing]
  simpa only [he] using tendsto_iff_norm_sub_tendsto_zero.1 hx
theorem dualSpaceComplete_holds : DualSpaceComplete q := by
  refine ⟨⟨LinearMap.range (pairing hq), range_pairing hq⟩, isDualNormOn_bounded hq,
    isDualComplete_bounded hq, fun v => ?_, fun u v => ?_, fun z v => ?_, fun v => ?_,
    fun u v => ?_⟩
  · rw [← pairing_toCompleted hq]
    exact pairing_mem hq _
  · funext w
    exact hq.add_right w u v
  · funext w
    exact hq.smul_right z w v
  · rw [← pairing_toCompleted hq, dualNorm_pairing, norm_toCompleted]
  · constructor
    · intro h
      have h0 : toCompleted hq (u - v) = 0 := pairing_injective hq (by
        rw [map_sub, map_sub, map_zero, pairing_toCompleted, pairing_toCompleted, h, sub_self])
      rw [← inner_toCompleted hq, h0, inner_zero_left]
    · intro h
      have h0 : toCompleted hq (u - v) = 0 :=
        inner_self_eq_zero.1 (by rw [inner_toCompleted]; exact h)
      have he : toCompleted hq u = toCompleted hq v := sub_eq_zero.1 (by rw [← map_sub]; exact h0)
      rw [← pairing_toCompleted hq, ← pairing_toCompleted hq, he]
def completedInner (φ ψ : E → ℂ) : ℂ :=
  ⟪Function.invFun (pairing hq) φ, Function.invFun (pairing hq) ψ⟫_ℂ
theorem completedInner_pairing (x y : Completed hq) :
    completedInner hq (pairing hq x) (pairing hq y) = ⟪x, y⟫_ℂ := by
  rw [completedInner, Function.leftInverse_invFun (pairing_injective hq) x,
    Function.leftInverse_invFun (pairing_injective hq) y]
theorem isCompletionInner_completedInner : IsCompletionInner q (completedInner hq) where
  add_left φ hφ φ' hφ' ψ hψ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨x', rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ'
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    rw [← map_add]
    simp only [completedInner_pairing, inner_add_left]
  smul_left z φ hφ ψ hψ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    rw [← map_smul]
    simp only [completedInner_pairing, inner_smul_left]
  add_right φ hφ ψ hψ ψ' hψ' := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    obtain ⟨y', rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ'
    rw [← map_add]
    simp only [completedInner_pairing, inner_add_right]
  smul_right z φ hφ ψ hψ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    rw [← map_smul]
    simp only [completedInner_pairing, inner_smul_right]
  diagonal φ hφ := by
    obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    rw [completedInner_pairing, dualNorm_pairing, inner_self_eq_norm_sq_to_K]
    rfl
theorem pairing_mem_formCompletion (x : Completed hq) : pairing hq x ∈ formCompletion q := by
  rw [formCompletion_eq hq]
  exact pairing_mem hq x
theorem eq_inner_of_isCompletionInner {s : (E → ℂ) → (E → ℂ) → ℂ}
    (hs : IsCompletionInner q s) (x y : Completed hq) :
    s (pairing hq x) (pairing hq y) = ⟪x, y⟫_ℂ := by
  have hm := pairing_mem_formCompletion hq
  have h0 := eq_zero_of_sesquilinear_of_diag_eq_zero
    (fun x y : Completed hq => s (pairing hq x) (pairing hq y) - ⟪x, y⟫_ℂ)
    (fun x x' y => by
      simp only [map_add, hs.add_left _ (hm x) _ (hm x') _ (hm y), inner_add_left]
      ring)
    (fun z x y => by
      simp only [map_smul, hs.smul_left z _ (hm x) _ (hm y), inner_smul_left]
      ring)
    (fun x y y' => by
      simp only [map_add, hs.add_right _ (hm x) _ (hm y) _ (hm y'), inner_add_right]
      ring)
    (fun z x y => by
      simp only [map_smul, hs.smul_right z _ (hm x) _ (hm y), inner_smul_right]
      ring)
    (fun z => by
      simp only [hs.diagonal _ (hm z), dualNorm_pairing, inner_self_eq_norm_sq_to_K]
      exact sub_self _)
    x y
  exact sub_eq_zero.1 h0
theorem hasHilbertStructure_holds : HasHilbertStructure q := by
  have hform : IsCompletionInner q (completionInner q) :=
    Classical.epsilon_spec ⟨completedInner hq, isCompletionInner_completedInner hq⟩
  refine ⟨?_, hform, fun φ hφ ψ hψ => ?_, ?_, ?_⟩
  · rw [formCompletion_eq hq, ← range_pairing hq, Submodule.span_eq]
  · obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    rw [eq_inner_of_isCompletionInner hq hform, eq_inner_of_isCompletionInner hq hform,
      inner_conj_symm]
  · rw [formCompletion_eq hq]
    exact isDualNormOn_bounded hq
  · rw [formCompletion_eq hq]
    exact isDualComplete_bounded hq
def toHilbert : Completed hq →ₗ[ℂ] FormHilbertSpace q where
  toFun x := ⟨pairing hq x,
    (mem_hilbertSubmodule (hasHilbertStructure_holds hq)).2 (pairing_mem_formCompletion hq x)⟩
  map_add' x y := asMap_injective (map_add (pairing hq) x y)
  map_smul' z x := asMap_injective (map_smul (pairing hq) z x)
theorem asMap_toHilbert (x : Completed hq) : asMap (toHilbert hq x) = pairing hq x := rfl
theorem norm_toHilbert (x : Completed hq) : ‖toHilbert hq x‖ = ‖x‖ := by
  rw [norm_eq_dualNorm (hasHilbertStructure_holds hq), asMap_toHilbert, dualNorm_pairing]
theorem toHilbert_surjective : Function.Surjective (toHilbert hq) := fun φ => by
  obtain ⟨x, hx⟩ :=
    exists_pairing_eq_of_mem_formCompletion hq (asMap_mem (hasHilbertStructure_holds hq) φ)
  exact ⟨x, asMap_injective hx⟩
theorem asMap_classVec (u : E) : asMap (classVec q u) = formClass q u := by
  have hu : formClass q u ∈ hilbertSubmodule q := by
    rw [← pairing_toCompleted hq]
    exact (toHilbert hq (toCompleted hq u)).2
  let w : FormHilbertSpace q := ⟨formClass q u, hu⟩
  have e1 : classVec q u = w := dif_pos hu
  rw [e1]
  rfl
def classMap : E →ₗ[ℂ] FormHilbertSpace q := (toHilbert hq).comp (toCompleted hq)
theorem classMap_apply (u : E) : classMap hq u = classVec q u := by
  refine asMap_injective ?_
  rw [asMap_classVec hq, classMap, LinearMap.comp_apply, asMap_toHilbert, pairing_toCompleted]
theorem norm_classVec (u : E) : ‖classVec q u‖ = seminormOfForm q u := by
  rw [← classMap_apply hq, classMap, LinearMap.comp_apply, norm_toHilbert, norm_toCompleted]
theorem denseRange_classMap : DenseRange (classMap hq) := by
  have hc : Continuous (toHilbert hq) :=
    (AddMonoidHomClass.isometry_of_norm (toHilbert hq) (norm_toHilbert hq)).continuous
  exact (toHilbert_surjective hq).denseRange.comp (denseRange_toCompleted hq) hc
theorem formCompletionHilbert_holds : FormCompletionHilbert q := by
  have h := hasHilbertStructure_holds hq
  refine ⟨h, fun s hs φ hφ ψ hψ => ?_, ?_, inner_eq_completionInner h, norm_eq_dualNorm h,
    asMap_classVec hq, fun u v => ?_, ⟨LinearMap.range (classMap hq), ?_⟩, ?_⟩
  · obtain ⟨x, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hφ
    obtain ⟨y, rfl⟩ := exists_pairing_eq_of_mem_formCompletion hq hψ
    rw [eq_inner_of_isCompletionInner hq hs, eq_inner_of_isCompletionInner hq h.form]
  · ext φ
    exact mem_hilbertSubmodule h
  · rw [inner_eq_completionInner h, asMap_classVec hq, asMap_classVec hq,
      ← pairing_toCompleted hq, ← pairing_toCompleted hq,
      eq_inner_of_isCompletionInner hq h.form, inner_toCompleted]
  · rw [LinearMap.coe_range, funext (classMap_apply hq)]
  · rw [← funext (classMap_apply hq)]
    exact denseRange_classMap hq
theorem inducedOperators_holds : InducedOperators q := by
  intro H' _ _ _ C R hC hR
  have hd := denseRange_classMap hq
  have hb : ∀ u, ‖R u‖ ≤ C * ‖classMap hq u‖ := fun u => by
    rw [classMap_apply hq, norm_classVec hq]
    exact hR u
  let B₀ : FormHilbertSpace q →L[ℂ] H' := R.extendOfNorm (classMap hq)
  have hB₀ : ∀ u, B₀ (classVec q u) = R u := fun u => by
    rw [← classMap_apply hq]
    exact LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ u
  have huniq : ∀ B : FormHilbertSpace q →L[ℂ] H', (∀ u, B (classVec q u) = R u) → B = B₀ :=
    fun B hB => DFunLike.coe_injective (hd.equalizer B.continuous B₀.continuous
      (funext fun u => by
        simp only [Function.comp_apply, classMap_apply hq, hB, hB₀]))
  refine ⟨⟨B₀, hB₀, fun B hB => huniq B hB⟩, fun B hB => ?_⟩
  have hle : ‖B‖ ≤ C := by
    rw [huniq B hB]
    exact LinearMap.opNorm_extendOfNorm_le hd hC hb
  refine ⟨hle, fun hiso => ?_⟩
  have hnorm : ∀ φ, ‖B φ‖ = ‖φ‖ := fun φ =>
    hd.induction_on φ (isClosed_eq B.continuous.norm continuous_norm) fun u => by
      rw [classMap_apply hq, hB, hiso, norm_classVec hq]
  refine ⟨hnorm, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨φ, rfl⟩
    exact hd.induction_on (p := fun φ => B φ ∈ closure (Set.range R)) φ
      (isClosed_closure.preimage B.continuous) fun u => by
        rw [classMap_apply hq, hB]
        exact subset_closure ⟨u, rfl⟩
  · have hclosed : IsClosed (Set.range B) :=
      (AddMonoidHomClass.isometry_of_norm B hnorm).isClosedEmbedding.isClosed_range
    exact closure_minimal (by
      rintro _ ⟨u, rfl⟩
      exact ⟨classVec q u, hB u⟩) hclosed
end SingleForm
theorem formCompletionIsHilbertSpace_holds : FormCompletionIsHilbertSpace :=
  fun _ _ _ _ hq =>
    ⟨dualSpaceComplete_holds hq, formCompletionHilbert_holds hq, inducedOperators_holds hq⟩
end YangMills.Construction.FormCompletion.RieszRepresentation
end
