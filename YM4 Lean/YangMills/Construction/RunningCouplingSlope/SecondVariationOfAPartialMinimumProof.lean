import YangMills.Construction.RunningCouplingSlope.SecondVariationOfAPartialMinimum
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.ParametricMinima
theorem hessianSplitsAtPartialMinimum_holds : HessianSplitsAtPartialMinimum := by
  intro A B _ _ _ _ _ _ E s P hE hs0 hsd hP hcrit x y
  set H := fderiv ℝ (fderiv ℝ E) (0, 0) with hH
  have hEdiff : ∀ᶠ p in 𝓝 ((0, 0) : A × B), DifferentiableAt ℝ E p := by
    have := hE.eventually (by simp)
    filter_upwards [this] with p hp
    exact hp.differentiableAt (by norm_num)
  have hD1 : ContDiffAt ℝ 1 (fderiv ℝ E) (0, 0) := hE.fderiv_right (m := 1) (by norm_num)
  have hDd : HasFDerivAt (fderiv ℝ E) H (0, 0) :=
    (hD1.differentiableAt (by norm_num)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ E (0, 0) := hE.isSymmSndFDerivAt (by simp)
  let γ : B → A × B := fun b => (s b, b)
  let Γ : B →L[ℝ] A × B := P.prod (ContinuousLinearMap.id ℝ B)
  have hγ0 : γ 0 = (0, 0) := by simp [γ, hs0]
  have hγ : HasFDerivAt γ Γ 0 := hP.prodMk (hasFDerivAt_id 0)
  have hγcont : Tendsto γ (𝓝 0) (𝓝 (0, 0)) := by
    have := hγ.continuousAt.tendsto
    rwa [hγ0] at this
  let grad : B → (A × B) →L[ℝ] ℝ := fun b => fderiv ℝ E (γ b)
  have hgrad : HasFDerivAt grad (H.comp Γ) 0 := by
    have h1 : HasFDerivAt (fderiv ℝ E) H (γ 0) := by rw [hγ0]; exact hDd
    exact h1.comp 0 hγ
  have hcritH : ∀ (v : B) (w : A), H (Γ v) (w, 0) = 0 := by
    intro v w
    have h1 : HasFDerivAt (fun b => grad b (w, 0)) ((H.comp Γ).flip (w, 0)) 0 := by
      have := hgrad.clm_apply (hasFDerivAt_const ((w, 0) : A × B) (0 : B))
      simpa using this
    have h2 : (fun b => grad b (w, 0)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [hcrit] with b hb
      exact hb w
    have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hasFDerivAt_const (0 : ℝ) (0 : B))
    have := congrArg (fun L : B →L[ℝ] ℝ => L v) h3
    simpa using this
  have hfirst : ∀ᶠ b in 𝓝 (0 : B), ∀ v, fderiv ℝ (fun b => E (s b, b)) b v = grad b (0, v) := by
    filter_upwards [hsd, hcrit, hγcont.eventually hEdiff] with b hb hcr hEb v
    have hγb : HasFDerivAt γ ((fderiv ℝ s b).prod (ContinuousLinearMap.id ℝ B)) b :=
      hb.hasFDerivAt.prodMk (hasFDerivAt_id b)
    have h1 := hEb.hasFDerivAt.comp b hγb
    have h2 : fderiv ℝ (fun b => E (s b, b)) b = _ := h1.fderiv
    rw [h2]
    have h3 : ((fderiv ℝ s b v, v) : A × B) = (fderiv ℝ s b v, 0) + (0, v) := by simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    rw [h3, map_add, hcr, zero_add]
  let restr : ((A × B) →L[ℝ] ℝ) →L[ℝ] (B →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ B (A × B) ℝ).flip (ContinuousLinearMap.inr ℝ A B)
  have hrestr : ∀ b, restr (grad b) = (grad b).comp (ContinuousLinearMap.inr ℝ A B) := fun b => rfl
  have hsecond : fderiv ℝ (fun b => E (s b, b)) =ᶠ[𝓝 0] fun b => restr (grad b) := by
    filter_upwards [hfirst] with b hb
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hb v, hrestr]
    simp
  have hderiv : HasFDerivAt (fderiv ℝ fun b => E (s b, b)) (restr.comp (H.comp Γ)) 0 :=
    (restr.hasFDerivAt.comp 0 hgrad).congr_of_eventuallyEq hsecond
  rw [hderiv.fderiv]
  have hHm : (restr.comp (H.comp Γ)) y y = H (Γ y) (0, y) := by
    simp [restr]
  rw [hHm]
  have hΓy : Γ y = (P y, y) := rfl
  have hsplit : ((x, y) : A × B) = (x - P y, 0) + Γ y := by
    rw [hΓy]; simp
  have hsplit2 : Γ y = (P y, 0) + (0, y) := by
    rw [hΓy]; simp
  have hs : H (x - P y, 0) (Γ y) = H (Γ y) (x - P y, 0) := hsym _ _
  have e1 := hcritH y (x - P y)
  have e2 := hcritH y (P y)
  calc H (x, y) (x, y)
      = H (x - P y, 0) (x - P y, 0) + H (x - P y, 0) (Γ y) + H (Γ y) (x - P y, 0) + H (Γ y) (Γ y) := by
        rw [hsplit]
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
    _ = H (x - P y, 0) (x - P y, 0) + H (Γ y) (Γ y) := by rw [hs, e1]; ring
    _ = H (x - P y, 0) (x - P y, 0) + H (Γ y) (0, y) := by
        have h4 : H (Γ y) (Γ y) = H (Γ y) (P y, 0) + H (Γ y) (0, y) := by
          have := congrArg (H (Γ y)) hsplit2
          rwa [map_add] at this
        rw [h4, e2, zero_add]
    _ = _ := by ring
end YangMills.Construction.ParametricMinima
end
