import YangMills.Construction.SpectralTheory.BoundedOperatorsOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.SettingsComparison.BoundedOps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isBoundedAdjoint_iff_eq_star (A A' : H →L[ℂ] H) :
    OperatorTransport.IsBoundedAdjoint A' A ↔ A' = star A := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  exact ⟨fun hA u w => (hA u w).symm, fun hA u w => (hA u w).symm⟩
theorem isSelfAdjointCLM_iff (A : H →L[ℂ] H) :
    OperatorTransport.IsSelfAdjointCLM A ↔ _root_.IsSelfAdjoint A := by
  unfold OperatorTransport.IsSelfAdjointCLM
  rw [isBoundedAdjoint_iff_eq_star, _root_.isSelfAdjoint_iff]
  exact eq_comm
theorem isProjectionCLM_iff (A : H →L[ℂ] H) :
    OperatorTransport.IsProjectionCLM A ↔ HilbertSpaceBasics.IsOrthProjOp A := by
  unfold OperatorTransport.IsProjectionCLM HilbertSpaceBasics.IsOrthProjOp
  rw [isSelfAdjointCLM_iff, _root_.isSelfAdjoint_iff]
  exact ⟨fun hA => ⟨hA.1.symm, hA.2.symm⟩, fun hA => ⟨hA.1.symm, hA.2.symm⟩⟩
theorem isProjFn_iff (P : H → H) :
    IsProjFn P ↔ IsBoundedOrthProjFn P := by
  constructor
  · rintro ⟨A, hA, hP⟩
    exact ⟨A, hA, (isProjectionCLM_iff A).1 hP⟩
  · rintro ⟨A, hA, hP⟩
    exact ⟨A, hA, (isProjectionCLM_iff A).2 hP⟩
theorem isBoundedOrthProjFn_iff (P : H → H) :
    IsBoundedOrthProjFn P ↔ IsLinearOrthProjFn P := by
  constructor
  · rintro ⟨A, rfl, hsa, hid⟩
    refine ⟨A.toLinearMap, rfl, ?_, ?_⟩
    · refine LinearMap.ext fun u => ?_
      exact (congrArg (fun C : H →L[ℂ] H => C u) hid).symm
    · intro u w
      exact (((isBoundedAdjoint_iff_eq_star A A).2 hsa) u w).symm
  · rintro ⟨p, rfl, hid, hsym⟩
    have hcont : Continuous p := LinearMap.IsSymmetric.continuous hsym
    let A : H →L[ℂ] H := ⟨p, hcont⟩
    refine ⟨A, rfl, ?_, ?_⟩
    · exact (isBoundedAdjoint_iff_eq_star A A).1 fun u w => (hsym u w).symm
    · refine ContinuousLinearMap.ext fun u => ?_
      exact (LinearMap.congr_fun hid u).symm
theorem star_apply_apply_of_isUnitaryOp {A : H →L[ℂ] H} (hA : HilbertSpaceBasics.IsUnitaryOp A)
    (u : H) : (star A : H →L[ℂ] H) (A u) = u :=
  congrArg (fun C : H →L[ℂ] H => C u) hA.1
theorem apply_star_apply_of_isUnitaryOp {A : H →L[ℂ] H} (hA : HilbertSpaceBasics.IsUnitaryOp A)
    (u : H) : A ((star A : H →L[ℂ] H) u) = u :=
  congrArg (fun C : H →L[ℂ] H => C u) hA.2
theorem bijective_of_isUnitaryOp {A : H →L[ℂ] H} (hA : HilbertSpaceBasics.IsUnitaryOp A) :
    Function.Bijective A :=
  Function.bijective_iff_has_inverse.2
    ⟨_, star_apply_apply_of_isUnitaryOp hA, apply_star_apply_of_isUnitaryOp hA⟩
theorem inner_map_map_of_isUnitaryOp {A : H →L[ℂ] H} (hA : HilbertSpaceBasics.IsUnitaryOp A)
    (u w : H) : ⟪A u, A w⟫_ℂ = ⟪u, w⟫_ℂ := by
  have hadj := ContinuousLinearMap.adjoint_inner_left A w (A u)
  rw [← ContinuousLinearMap.star_eq_adjoint, star_apply_apply_of_isUnitaryOp hA] at hadj
  exact hadj.symm
theorem exists_clm_isUnitaryOp (f : H →ₗ[ℂ] H) (hbij : Function.Bijective f)
    (hinner : ∀ u w, ⟪f u, f w⟫_ℂ = ⟪u, w⟫_ℂ) :
    ∃ A : H →L[ℂ] H, ⇑A = ⇑f ∧ HilbertSpaceBasics.IsUnitaryOp A := by
  let A : H →L[ℂ] H := (f.isometryOfInner hinner).toContinuousLinearMap
  have hAf : ∀ u, A u = f u := fun _ => rfl
  have hleft : ∀ u, (star A : H →L[ℂ] H) (A u) = u := by
    intro u
    refine ext_inner_right ℂ fun w => ?_
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, hAf, hAf]
    exact hinner u w
  refine ⟨A, rfl, ContinuousLinearMap.ext hleft, ContinuousLinearMap.ext fun w => ?_⟩
  obtain ⟨z, rfl⟩ := hbij.2 w
  change A ((star A : H →L[ℂ] H) (f z)) = f z
  rw [← hAf z, hleft z]
theorem isUnitaryFn_iff (V : H → H) : IsUnitaryFn V ↔ IsBoundedUnitaryFn V := by
  constructor
  · rintro ⟨f, rfl, hf⟩
    obtain ⟨A, hA, hU⟩ := exists_clm_isUnitaryOp f hf.bijective hf.inner_map_map
    exact ⟨A, hA, hU⟩
  · rintro ⟨A, rfl, hU⟩
    exact ⟨A.toLinearMap, rfl, bijective_of_isUnitaryOp hU, inner_map_map_of_isUnitaryOp hU⟩
theorem isBoundedUnitaryFn_iff (V : H → H) :
    IsBoundedUnitaryFn V ↔ IsIsometricUnitaryFn V := by
  constructor
  · rintro ⟨A, rfl, hU⟩
    exact ⟨A.toLinearMap, rfl, bijective_of_isUnitaryOp hU,
      (LinearMap.isometryOfInner A.toLinearMap (inner_map_map_of_isUnitaryOp hU)).norm_map⟩
  · rintro ⟨g, rfl, hg⟩
    let e : H →ₗᵢ[ℂ] H := ⟨g, hg.norm_map⟩
    obtain ⟨A, hA, hU⟩ := exists_clm_isUnitaryOp g hg.bijective e.inner_map_map
    exact ⟨A, hA, hU⟩
theorem isContractionSemigroup_iff_parts (S : ℝ≥0 → H →L[ℂ] H) :
    OperatorTransport.IsContractionSemigroup S ↔
      HilbertSpaceBasics.IsOpSemigroup S ∧ (∀ t, _root_.IsSelfAdjoint (S t)) ∧
        (∀ t, HilbertSpaceBasics.IsContraction (S t)) ∧
          HilbertSpaceBasics.IsStronglyCont S := by
  constructor
  · intro hS
    exact ⟨⟨hS.map_zero, hS.map_add⟩, fun t => (isSelfAdjointCLM_iff _).1 (hS.selfAdjoint t),
      hS.contraction, hS.continuous_apply⟩
  · rintro ⟨⟨hzero, hadd⟩, hsa, hcon, hcont⟩
    exact ⟨fun t => (isSelfAdjointCLM_iff _).2 (hsa t), hcon, hzero, hadd, hcont⟩
theorem isUnitaryGroupFn_iff_cont (U : ℝ → H → H) :
    IsUnitaryGroupFn U ↔ IsContUnitaryGroupFn U := by
  constructor
  · rintro ⟨f, hf, hG⟩
    choose A hA hU using fun s =>
      exists_clm_isUnitaryOp (f s) (hG.unitary s).bijective (hG.unitary s).inner_map_map
    have hAu : ∀ s u, A s u = f s u := fun s u => congrFun (hA s) u
    refine ⟨A, fun s => (hA s).trans (hf s), ⟨hU, ?_, ?_⟩, ?_⟩
    · refine ContinuousLinearMap.ext fun u => ?_
      rw [hAu, hG.map_zero]
      rfl
    · intro a b
      refine ContinuousLinearMap.ext fun u => ?_
      change A a (A b u) = A (a + b) u
      rw [hAu, hAu, hAu, ← hG.map_add]
      rfl
    · intro w
      have hfun : (fun s => A s w) = fun s => f s w := funext fun s => hAu s w
      rw [hfun]
      exact hG.continuous_apply w
  · rintro ⟨A, hA, ⟨hU, hzero, hadd⟩, hcont⟩
    refine ⟨fun s => (A s).toLinearMap, hA, ?_, ?_, ?_, hcont⟩
    · exact fun s => ⟨bijective_of_isUnitaryOp (hU s), inner_map_map_of_isUnitaryOp (hU s)⟩
    · rw [hzero]
      rfl
    · intro s s'
      rw [← hadd]
      rfl
omit [CompleteSpace H] in
theorem inner_isSesquilinear : HilbertSpaceBasics.IsSesquilinear fun u w : H => ⟪u, w⟫_ℂ where
  add_left := fun a b c => inner_add_left a b c
  smul_left := fun z u w => inner_smul_left u w z
  add_right := fun a b c => inner_add_right a b c
  smul_right := fun z u w => inner_smul_right u w z
omit [CompleteSpace H] in
theorem norm_eq_formSeminorm (w : H) :
    ‖w‖ = HilbertSpaceBasics.formSeminorm (fun u v : H => ⟪u, v⟫_ℂ) w :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) w
omit [CompleteSpace H] in
theorem opNorm_eq_sSup (A : H →L[ℂ] H) :
    ‖A‖ = sSup {r : ℝ | ∃ w : H, ‖w‖ ≤ 1 ∧ r = ‖A w‖} := by
  have hbdd : BddAbove {r : ℝ | ∃ w : H, ‖w‖ ≤ 1 ∧ r = ‖A w‖} := by
    refine ⟨‖A‖, ?_⟩
    rintro r ⟨w, hw, rfl⟩
    exact A.unit_le_opNorm w hw
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound A (Real.sSup_nonneg ?_) fun w => ?_
    · rintro r ⟨u, -, rfl⟩
      exact norm_nonneg _
    · rcases eq_or_ne w 0 with rfl | hw
      · simp
      · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
        have hmem : ‖A ((‖w‖⁻¹ : ℂ) • w)‖ ∈ {r : ℝ | ∃ w : H, ‖w‖ ≤ 1 ∧ r = ‖A w‖} :=
          ⟨_, by simp [norm_smul, hpos.ne'], rfl⟩
        have hle := le_csSup hbdd hmem
        rw [map_smul, norm_smul] at hle
        have hnorm : ‖(‖w‖⁻¹ : ℂ)‖ = ‖w‖⁻¹ := by simp
        rw [hnorm, inv_mul_le_iff₀ hpos] at hle
        linarith [mul_comm ‖w‖ (sSup {r : ℝ | ∃ w : H, ‖w‖ ≤ 1 ∧ r = ‖A w‖})]
  · refine csSup_le ⟨‖A 0‖, 0, by simp, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    exact A.unit_le_opNorm w hw
theorem boundedOpsAgreeForAllSpaces_holds : BoundedOpsAgreeForAllSpaces := by
  intro H _ _ _
  exact
    { isBoundedAdjoint_iff := isBoundedAdjoint_iff_eq_star
      isSelfAdjointCLM_iff := isSelfAdjointCLM_iff
      norm_le_one_iff := fun _ => Iff.rfl
      mul_comm_iff := fun _ _ => Iff.rfl
      proj_iff := fun P => ⟨isProjFn_iff P, isBoundedOrthProjFn_iff P⟩
      unitary_iff := fun V => ⟨isUnitaryFn_iff V, isBoundedUnitaryFn_iff V⟩
      inv_isInverse := fun f hf =>
        ⟨fun u => hf.toLinearEquiv.symm_apply_apply u, fun u => hf.toLinearEquiv.apply_symm_apply u⟩
      star_isInverse := fun _ hA =>
        ⟨star_apply_apply_of_isUnitaryOp hA, apply_star_apply_of_isUnitaryOp hA⟩
      euclideanInv_isInverse := fun g hg =>
        ⟨fun u => (LinearEquiv.ofBijective g hg.bijective).symm_apply_apply u,
          fun u => (LinearEquiv.ofBijective g hg.bijective).apply_symm_apply u⟩
      isContractionSemigroup_iff := isContractionSemigroup_iff_parts
      isUnitaryGroupFn_iff := isUnitaryGroupFn_iff_cont
      inner_isSesquilinear := inner_isSesquilinear
      norm_eq_formSeminorm := norm_eq_formSeminorm
      opNorm_eq_sSup := opNorm_eq_sSup }
end YangMills.Construction.SettingsComparison.BoundedOps
