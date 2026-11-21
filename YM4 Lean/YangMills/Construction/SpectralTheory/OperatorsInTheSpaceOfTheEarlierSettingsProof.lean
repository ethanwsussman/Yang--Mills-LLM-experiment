import YangMills.Construction.SpectralTheory.OperatorsInTheSpaceOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.UnboundedOpsComparison
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem eq_zero_of_inner_dense {D : Submodule ℂ H} (hD : Dense (D : Set H)) {u : H}
    (hu : ∀ v : D, ⟪u, (v : H)⟫_ℂ = 0) : u = 0 := by
  have hcont : Continuous fun w : H => ⟪u, w⟫_ℂ := continuous_const.inner continuous_id
  have hzero : (fun w : H => ⟪u, w⟫_ℂ) = fun _ => 0 :=
    Continuous.ext_on hD hcont continuous_const fun w hw => hu ⟨w, hw⟩
  exact inner_self_eq_zero.mp (congrFun hzero u)
theorem isSelfAdjointUnbounded_iff (T : UnboundedOp H) :
    OperatorTransport.IsSelfAdjointUnbounded T ↔ HilbertSpaceBasics.IsSelfAdjointOp T := by
  constructor
  · rintro ⟨hdense, hT⟩
    refine ⟨hdense, fun x => ⟨fun hx => ⟨T ⟨x, hx⟩, (hT x _).mp ⟨hx, rfl⟩⟩, ?_⟩, fun x y => ?_⟩
    · rintro ⟨z, hz⟩
      exact ((hT x z).mpr hz).1
    · exact (hT (x : H) (T x)).mp ⟨x.2, rfl⟩ y
  · rintro ⟨hdense, hmem, hsymm⟩
    refine ⟨hdense, fun x w => ⟨?_, fun hw => ?_⟩⟩
    · rintro ⟨hx, rfl⟩ y
      exact hsymm ⟨x, hx⟩ y
    · have hx : x ∈ T.domain := (hmem x).mpr ⟨w, hw⟩
      refine ⟨hx, ?_⟩
      have hdiff : T ⟨x, hx⟩ - w = 0 := by
        refine eq_zero_of_inner_dense hdense fun y => ?_
        rw [inner_sub_left, ← hsymm ⟨x, hx⟩ y, hw y, sub_self]
      exact sub_eq_zero.mp hdiff
theorem star_apply_apply_of_isUnitaryMap [CompleteSpace H] {u : H →ₗ[ℂ] H}
    (hu : OperatorTransport.IsUnitaryMap u)
    {U : H →L[ℂ] H} (hU : ⇑U = ⇑u) (x : H) : (star U : H →L[ℂ] H) (U x) = x := by
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, hU]
  exact hu.inner_map_map x y
theorem conjOp_eq_conjByUnitary [CompleteSpace H] (T : UnboundedOp H) {u : H →ₗ[ℂ] H}
    (hu : OperatorTransport.IsUnitaryMap u) (U : H →L[ℂ] H) (hU : ⇑U = ⇑u) :
    OperatorTransport.conjOp hu T = HilbertSpaceBasics.conjByUnitary U T := by
  have hinv := star_apply_apply_of_isUnitaryMap hu hU
  have hUu : ∀ x, U x = u x := fun x => congrFun hU x
  have hdom : (OperatorTransport.conjOp hu T).domain =
      (HilbertSpaceBasics.conjByUnitary U T).domain := by
    ext v
    change v ∈ T.domain.map (hu.toLinearEquiv : H →ₗ[ℂ] H) ↔ (star U : H →L[ℂ] H) v ∈ T.domain
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxu : (hu.toLinearEquiv : H →ₗ[ℂ] H) x = U x := (hUu x).symm
      rw [hxu, hinv]
      exact hx
    · intro hv
      obtain ⟨z, rfl⟩ := hu.bijective.2 v
      rw [← hUu, hinv] at hv
      exact ⟨z, hv, rfl⟩
  refine LinearPMap.ext hdom fun x hf hg => ?_
  have hf' : x ∈ T.domain.map (hu.toLinearEquiv : H →ₗ[ℂ] H) := hf
  obtain ⟨w, hw, rfl⟩ := hf'
  have happ := OperatorTransport.conjOp_apply hu T ⟨w, hw⟩
  refine happ.trans ?_
  have hconj : HilbertSpaceBasics.conjByUnitary U T ⟨(hu.toLinearEquiv : H →ₗ[ℂ] H) w, hg⟩ =
      U (T ⟨(star U : H →L[ℂ] H) ((hu.toLinearEquiv : H →ₗ[ℂ] H) w), hg⟩) := rfl
  have hpt : (⟨(star U : H →L[ℂ] H) ((hu.toLinearEquiv : H →ₗ[ℂ] H) w), hg⟩ : T.domain) =
      ⟨w, hw⟩ :=
    Subtype.ext ((congrArg _ (hUu w).symm).trans (hinv w))
  rw [hconj, hpt, hUu]
theorem unboundedOpsAgreeForAllSpaces_holds : SettingsComparison.UnboundedOpsAgreeForAllSpaces :=
  fun H _ _ _ =>
  { isSelfAdjoint_iff := isSelfAdjointUnbounded_iff
    isNonneg_iff := fun T hT =>
      ⟨fun h => ⟨(isSelfAdjointUnbounded_iff T).mp hT, h⟩, fun h => h.2⟩
    conjOp_eq := fun T _ _ hu U hU => conjOp_eq_conjByUnitary T hu U hU
    ext_iff_domain := fun T T' =>
      ⟨fun h => by
        subst h
        exact ⟨rfl, fun v v' e => congrArg T (Subtype.ext e)⟩,
        fun h => LinearPMap.ext h.1 fun x hf hg => h.2 ⟨x, hf⟩ ⟨x, hg⟩ rfl⟩
    eq_iff_le_le := fun T T' =>
      ⟨fun h => h ▸ ⟨le_rfl, le_rfl⟩, fun h => le_antisymm h.1 h.2⟩ }
end YangMills.Construction.UnboundedOpsComparison
