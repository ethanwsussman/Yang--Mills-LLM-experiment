import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletion
import YangMills.Construction.HilbertSpaces.UnitaryOperatorsOnTheCompletion
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.EuclideanBorel (Space)
open YangMills.Construction.FormsOperators (DenseExtension IsHilbertCompletion IsSesquilinear
  IsStronglyContUnitaryRep IsUnitaryRep UnitaryMap formRadical ofCLM formOnQuotient)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.UnitaryOpsOnCompletion
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem unitaryConjugate_ofCLM_eq (U : UnitaryMap H H) (B C : H →L[ℂ] H)
    (h : toCLM U * B = C * toCLM U) :
    FormsOperators.unitaryConjugate U (ofCLM B) = ofCLM C := by
  have hB : (ofCLM B).domain = ⊤ := rfl
  have hC : (ofCLM C).domain = ⊤ := rfl
  have hd : (FormsOperators.unitaryConjugate U (ofCLM B)).domain = (ofCLM C).domain := by
    rw [hC]
    change (ofCLM B).domain.map U.toLinearEquiv.toLinearMap = ⊤
    rw [hB, Submodule.map_top, LinearEquiv.range]
  refine (FormsOperators.unboundedOp_eq_iff _ _).mpr ⟨hd, fun χ => ?_⟩
  obtain ⟨y, hy⟩ := χ
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  have hc := FormsOperators.unitaryConjugate_apply U (ofCLM B) ⟨x, hx⟩
  have he : C (U x) = U (B x) := (DFunLike.congr_fun h x).symm
  exact he.trans hc.symm
theorem continuous_apply_of_tendsto_zero (U : Space 3 → UnitaryMap H H)
    (hmul : ∀ a b, U a * U b = U (a + b))
    (h₀ : ∀ v, Tendsto (fun a => ‖U a v - v‖) (𝓝 0) (𝓝 0)) (v : H) :
    Continuous fun a => U a v := by
  refine continuous_iff_continuousAt.mpr fun a₀ => ?_
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have ht : Tendsto (fun a : Space 3 => a - a₀) (𝓝 a₀) (𝓝 0) := by
    have hc : Continuous fun a : Space 3 => a - a₀ := by fun_prop
    simpa using hc.tendsto a₀
  refine ((h₀ v).comp ht).congr fun a => ?_
  have hs : U a v = U a₀ (U (a - a₀) v) := by
    have hm := DFunLike.congr_fun (hmul a₀ (a - a₀)) v
    rw [add_sub_cancel] at hm
    exact hm.symm
  rw [Function.comp_apply, hs, ← map_sub, (U a₀).norm_map]
end Operators
section Classes
variable {V : Type} [AddCommGroup V] [Module ℂ V]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : PreHilbertData V} {hq : IsSesquilinear S.form}
  {j : (V ⧸ formRadical S.form hq) →ₗ[ℂ] H}
theorem dense_range_embed (hj : IsHilbertCompletion (formOnQuotient S.form hq) j) :
    Dense (range (embed S hq j : V → H)) := by
  have hd : Dense (range j) := (FormsOperators.isDenseSet_iff_dense _).mp hj.dense_range
  have he : range (embed S hq j : V → H) = range j := by
    ext v
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨f, rfl⟩
  rwa [he]
theorem clm_ext_embed (hj : IsHilbertCompletion (formOnQuotient S.form hq) j) {B B' : H →L[ℂ] H}
    (h : ∀ f, B (embed S hq j f) = B' (embed S hq j f)) : B = B' := by
  refine DFunLike.coe_injective
    (Continuous.ext_on (dense_range_embed hj) B.continuous B'.continuous ?_)
  rintro _ ⟨f, rfl⟩
  exact h f
theorem unitaryMap_ext_embed (hj : IsHilbertCompletion (formOnQuotient S.form hq) j)
    {U U' : UnitaryMap H H}
    (h : ∀ f, U (embed S hq j f) = U' (embed S hq j f)) : U = U' := by
  refine LinearIsometryEquiv.ext fun v => ?_
  refine congrFun (Continuous.ext_on (dense_range_embed hj) U.continuous U'.continuous ?_) v
  rintro _ ⟨f, rfl⟩
  exact h f
theorem norm_embed_sq (hin : ∀ f g, ⟪embed S hq j f, embed S hq j g⟫_ℂ = S.form f g)
    (f : V) : ‖embed S hq j f‖ ^ 2 = (S.form f f).re := by
  rw [← hin f f]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _
theorem exists_unitaryExtends (hE : DenseExtension)
    (hj : IsHilbertCompletion (formOnQuotient S.form hq) j)
    (hin : ∀ f g, ⟪embed S hq j f, embed S hq j g⟫_ℂ = S.form f g)
    (R R' : V →ₗ[ℂ] V) (hRR' : R ∘ₗ R' = LinearMap.id)
    (hR : ∀ f g, S.form (R f) (R g) = S.form f g) :
    ∃ U : UnitaryMap H H, UnitaryExtends S hq j R U := by
  have hnull : formRadical S.form hq ≤ (formRadical S.form hq).comap R := by
    intro f hf g
    have hg : R (R' g) = g := LinearMap.congr_fun hRR' g
    rw [← hg, hR]
    exact hf (R' g)
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).mpr fun x hx => ?_
    refine hj.isInnerProduct.definite x ?_
    rw [← hj.inner_map, hx, inner_zero_left]
  let Rq : (V ⧸ formRadical S.form hq) →ₗ[ℂ] (V ⧸ formRadical S.form hq) :=
    Submodule.mapQ _ _ R hnull
  let e := LinearEquiv.ofInjective j hinj
  let B₀ : LinearMap.range j →ₗ[ℂ] H := j ∘ₗ Rq ∘ₗ e.symm.toLinearMap
  have hB₀ : ∀ f, B₀ (e (Submodule.Quotient.mk f)) = embed S hq j (R f) := by
    intro f
    change j (Rq (e.symm (e _))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hnorm : ∀ v : LinearMap.range j, ‖B₀ v‖ = ‖(v : H)‖ := by
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hB₀]
    have h₁ := norm_embed_sq hin (R f)
    rw [hR, ← norm_embed_sq hin f] at h₁
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h₁
  have hdense : FormsOperators.IsDenseSet ((LinearMap.range j : Submodule ℂ H) : Set H) :=
    by rw [LinearMap.coe_range]; exact hj.dense_range
  have hrange : FormsOperators.IsDenseSet (range B₀) := by
    refine (FormsOperators.isDenseSet_iff_dense _).mpr ((dense_range_embed hj).mono ?_)
    rintro _ ⟨f, rfl⟩
    refine ⟨e (Submodule.Quotient.mk (R' f)), ?_⟩
    rw [hB₀]
    exact congrArg _ (LinearMap.congr_fun hRR' f)
  obtain ⟨B, hB, -, -, hU⟩ := hE H H (LinearMap.range j) 1 B₀ hdense zero_le_one
    (fun v => by rw [hnorm, one_mul])
  obtain ⟨U, hU⟩ := hU hnorm hrange
  refine ⟨U, fun f => ?_⟩
  rw [hU]
  have hm := hB (e (Submodule.Quotient.mk f))
  rw [hB₀] at hm
  exact hm
theorem tendsto_norm_apply_sub_self (hj : IsHilbertCompletion (formOnQuotient S.form hq) j)
    (hin : ∀ f g, ⟪embed S hq j f, embed S hq j g⟫_ℂ = S.form f g)
    (U : Space 3 → UnitaryMap H H)
    (hU : ∀ a, UnitaryExtends S hq j (S.translationMap a) (U a))
    (hlim : ∀ f, Tendsto (fun a => S.form f (S.translationMap a f)) (𝓝 0) (𝓝 (S.form f f)))
    (v : H) :
    Tendsto (fun a => ‖U a v - v‖) (𝓝 0) (𝓝 0) := by
  have hclass : ∀ f, Tendsto (fun a => ‖U a (embed S hq j f) - embed S hq j f‖) (𝓝 0) (𝓝 0) := by
    intro f
    have hsq : ∀ a, ‖U a (embed S hq j f) - embed S hq j f‖ =
        Real.sqrt (2 * (S.form f f).re - 2 * (S.form f (S.translationMap a f)).re) := by
      intro a
      have hUa : U a (embed S hq j f) = embed S hq j (S.translationMap a f) := hU a f
      have h₁ := norm_sub_sq (𝕜 := ℂ) (embed S hq j f) (U a (embed S hq j f))
      rw [(U a).norm_map, norm_embed_sq hin f, hUa, hin] at h₁
      simp only [RCLike.re_to_complex] at h₁
      rw [hUa, norm_sub_rev, ← Real.sqrt_sq (norm_nonneg (embed S hq j f - _)), h₁]
      congr 1
      ring
    have hc : Tendsto (fun a => 2 * (S.form f f).re - 2 * (S.form f (S.translationMap a f)).re)
        (𝓝 0) (𝓝 0) := by
      have h₁ := (Complex.continuous_re.tendsto _).comp (hlim f)
      have h₂ := (tendsto_const_nhds (x := 2 * (S.form f f).re)).sub (h₁.const_mul 2)
      simpa only [sub_self, Function.comp_def] using h₂
    have hs := (Real.continuous_sqrt.tendsto 0).comp hc
    rw [Real.sqrt_zero] at hs
    exact hs.congr fun a => (hsq a).symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, hy, ⟨f, rfl⟩⟩ := Metric.dense_iff.mp (dense_range_embed hj) v (ε / 3) (by positivity)
  have hev := Metric.tendsto_nhds.mp (hclass f) (ε / 3) (by positivity)
  filter_upwards [hev] with a ha
  rw [Real.dist_eq, sub_zero, abs_norm] at ha ⊢
  have hy' : ‖embed S hq j f - v‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hy
  have hd : U a v - v = U a (v - embed S hq j f) + (U a (embed S hq j f) - embed S hq j f) +
      (embed S hq j f - v) := by
    rw [map_sub]
    abel
  have hn : ‖U a (v - embed S hq j f)‖ = ‖embed S hq j f - v‖ := by
    rw [(U a).norm_map, norm_sub_rev]
  rw [hd]
  have ht := norm_add₃_le (a := U a (v - embed S hq j f))
    (b := U a (embed S hq j f) - embed S hq j f) (c := embed S hq j f - v)
  linarith
end Classes
theorem unitaryActionSpec_holds (hF : FormsOperators.FormsAndCompletions)
    (hS : SemigroupOnCompletion.TransferSemigroupSpec) : UnitaryActionSpec := by
  intro V _ _ S h H _ _ _ j hj
  have hq : IsSesquilinear S.form := h.hermitian.toIsSesquilinear
  have hE : DenseExtension := hF.2.2.1
  have hQ := hF.2.1 V S.form h.hermitian h.posSemidef
  have hin : ∀ f g, ⟪embed S hq j f, embed S hq j g⟫_ℂ = S.form f g := by
    intro f g
    have hm := hj.inner_map (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)
    rw [hQ.2.2.2.2.1] at hm
    exact hm
  have hT : ∀ t f, transferOp S hq j t (embed S hq j f) = embed S hq j (S.semigroupMap t f) :=
    (hS V S h H j hj).1
  have hU : ∀ a, UnitaryExtends S hq j (S.translationMap a) (translationOp S hq j a) :=
    fun a => Classical.epsilon_spec (p := UnitaryExtends S hq j (S.translationMap a))
      (exists_unitaryExtends hE hj hin _ (S.translationMap (-a))
        (by rw [h.translationMap_comp, add_neg_cancel, h.translationMap_zero])
        (h.form_translationMap a))
  have hW : ∀ w, UnitaryExtends S hq j (S.rotationMap w) (rotationOp S hq j w) :=
    fun w => Classical.epsilon_spec (p := UnitaryExtends S hq j (S.rotationMap w))
      (exists_unitaryExtends hE hj hin _ (S.rotationMap w⁻¹)
        (by rw [h.rotationMap_comp, mul_inv_cancel, h.rotationMap_one]) (h.form_rotationMap w))
  have hmul : ∀ a b, translationOp S hq j a * translationOp S hq j b =
      translationOp S hq j (a + b) := by
    intro a b
    refine unitaryMap_ext_embed hj fun f => ?_
    change translationOp S hq j a (translationOp S hq j b (embed S hq j f)) = _
    rw [hU b f, hU a, hU (a + b) f, ← h.translationMap_comp]
    rfl
  have hrel : ∀ w a, toCLM (rotationOp S hq j w) * toCLM (translationOp S hq j a) =
      toCLM (translationOp S hq j (rotateSpatial w a)) * toCLM (rotationOp S hq j w) := by
    intro w a
    refine clm_ext_embed hj fun f => ?_
    change rotationOp S hq j w (translationOp S hq j a (embed S hq j f)) =
      translationOp S hq j (rotateSpatial w a) (rotationOp S hq j w (embed S hq j f))
    rw [hU a f, hW w, hW w f, hU (rotateSpatial w a)]
    exact congrArg _ (LinearMap.congr_fun (h.rotationMap_translationMap w a) f)
  refine ⟨hU, ⟨?_, hmul, continuous_apply_of_tendsto_zero _ hmul
      (tendsto_norm_apply_sub_self hj hin _ hU h.tendsto_translation)⟩, ?_, ?_, hW, ⟨?_, ?_⟩, ?_,
    ?_, hrel, fun w a => unitaryConjugate_ofCLM_eq _ _ _ (hrel w a)⟩
  · refine unitaryMap_ext_embed hj fun f => ?_
    rw [hU 0 f, h.translationMap_zero]
    rfl
  · intro a
    change translationOp S hq j a (embed S hq j S.unitVec) = embed S hq j S.unitVec
    rw [hU a S.unitVec, h.translationMap_unitVec]
  · intro a t
    refine clm_ext_embed hj fun f => ?_
    change translationOp S hq j a (transferOp S hq j t (embed S hq j f)) =
      transferOp S hq j t (translationOp S hq j a (embed S hq j f))
    rw [hT t f, hU a, hU a f, hT t]
    exact congrArg _ (LinearMap.congr_fun (h.translationMap_comm a t) f)
  · refine unitaryMap_ext_embed hj fun f => ?_
    rw [hW 1 f, h.rotationMap_one]
    rfl
  · intro w w'
    refine unitaryMap_ext_embed hj fun f => ?_
    change _ = rotationOp S hq j w (rotationOp S hq j w' (embed S hq j f))
    rw [hW w' f, hW w, hW (w * w') f, ← h.rotationMap_comp]
    rfl
  · intro w
    change rotationOp S hq j w (embed S hq j S.unitVec) = embed S hq j S.unitVec
    rw [hW w S.unitVec, h.rotationMap_unitVec]
  · intro w t
    refine clm_ext_embed hj fun f => ?_
    change rotationOp S hq j w (transferOp S hq j t (embed S hq j f)) =
      transferOp S hq j t (rotationOp S hq j w (embed S hq j f))
    rw [hT t f, hW w, hW w f, hT t]
    exact congrArg _ (LinearMap.congr_fun (h.rotationMap_comm w t) f)
end YangMills.Construction.PositiveFormReconstruction.UnitaryOpsOnCompletion
