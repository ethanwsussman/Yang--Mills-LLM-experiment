import YangMills.Construction.Calculus.CriticalBranchHessian
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Calculus
variable {V U : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U]
  [NormedSpace ℝ U]
theorem fderiv_prod_slice_right {F : V × U → ℝ} {x : V} {y : U}
    (hF : DifferentiableAt ℝ F (x, y)) :
    fderiv ℝ (fun y => F (x, y)) y = (fderiv ℝ F (x, y)).comp (ContinuousLinearMap.inr ℝ V U) :=
  (hF.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).fderiv
theorem fderiv_comp_graph {F : V × U → ℝ} {g : V → U} {x : V}
    (hF : DifferentiableAt ℝ F (x, g x)) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun x => F (x, g x)) x =
      (fderiv ℝ F (x, g x)).comp ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ g x)) :=
  (hF.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hg.hasFDerivAt)).fderiv
theorem criticalBranchHessian_holds : CriticalBranchHessian := by
  intro V U _ _ _ _ H b v₀ hH hb hcrit
  have hHd : ∀ᶠ x in 𝓝 (v₀, b v₀), DifferentiableAt ℝ H x :=
    (hH.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hbd : ∀ᶠ v in 𝓝 v₀, DifferentiableAt ℝ b v :=
    (hb.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hb0 : DifferentiableAt ℝ b v₀ := hb.differentiableAt (by norm_num)
  have hcont : ContinuousAt (fun v => (v, b v)) v₀ := continuousAt_id.prodMk hb0.continuousAt
  have hp : ∀ᶠ v in 𝓝 v₀, DifferentiableAt ℝ H (v, b v) := hcont.eventually hHd
  have hF : DifferentiableAt ℝ (fderiv ℝ H) (v₀, b v₀) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd := hF.hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ H (v₀, b v₀) :=
    hH.isSymmSndFDerivAt (by simp)
  set D := fderiv ℝ (fderiv ℝ H) (v₀, b v₀) with hD
  set A : V →L[ℝ] V × U := (ContinuousLinearMap.id ℝ V).prod (fderiv ℝ b v₀) with hA
  have hpd : HasFDerivAt (fun v => (v, b v)) A v₀ := (hasFDerivAt_id v₀).prodMk hb0.hasFDerivAt
  have hFp : HasFDerivAt (fun v => fderiv ℝ H (v, b v)) (D.comp A) v₀ :=
    HasFDerivAt.comp (g := fderiv ℝ H) v₀ hFd hpd
  have hcritH : ∀ᶠ v in 𝓝 v₀, ∀ k : U, fderiv ℝ H (v, b v) (0, k) = 0 := by
    filter_upwards [hcrit, hp] with v hv hd k
    have := hv k
    rw [fderiv_prod_slice_right hd] at this
    simpa using this
  have hzero : ∀ (h : V) (k : U), D (A h) (0, k) = 0 := by
    intro h k
    have h1 : HasFDerivAt (fun v => fderiv ℝ H (v, b v) (0, k))
        ((ContinuousLinearMap.apply ℝ ℝ ((0, k) : V × U)).comp (D.comp A)) v₀ :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, k) : V × U)).hasFDerivAt.comp v₀ hFp
    have h2 : HasFDerivAt (fun v => fderiv ℝ H (v, b v) (0, k)) (0 : V →L[ℝ] ℝ) v₀ :=
      (hasFDerivAt_const (0 : ℝ) v₀).congr_of_eventuallyEq (hcritH.mono fun v hv => hv k)
    have h3 := h1.unique h2
    simpa using congrArg (fun L : V →L[ℝ] ℝ => L h) h3
  have hφ : fderiv ℝ (fun v => H (v, b v)) =ᶠ[𝓝 v₀]
      fun v => (fderiv ℝ H (v, b v)).comp (ContinuousLinearMap.inl ℝ V U) := by
    filter_upwards [hcritH, hp, hbd] with v h1 hd hbv
    rw [fderiv_comp_graph hd hbv]
    ext h
    have hs : ((h, fderiv ℝ b v h) : V × U) = (h, 0) + (0, fderiv ℝ b v h) := by simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply]
    rw [hs, map_add, h1, add_zero]
  have hφ2 : ∀ h h' : V, fderiv ℝ (fderiv ℝ fun v => H (v, b v)) v₀ h h' = D (A h) (h', 0) := by
    intro h h'
    set L : (V × U →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
      (ContinuousLinearMap.compL ℝ V (V × U) ℝ).flip (ContinuousLinearMap.inl ℝ V U) with hL
    have h1 : HasFDerivAt (fun v => (fderiv ℝ H (v, b v)).comp (ContinuousLinearMap.inl ℝ V U))
        (L.comp (D.comp A)) v₀ := L.hasFDerivAt.comp v₀ hFp
    have h2 := (h1.congr_of_eventuallyEq hφ).fderiv
    rw [h2]
    simp [hL]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hd0 : DifferentiableAt ℝ H (v₀, b v₀) := hHd.self_of_nhds
    have hb1 : ∀ k : U, fderiv ℝ H (v₀, b v₀) (0, k) = 0 := hcritH.self_of_nhds
    rw [fderiv_comp_graph hd0 hb0] at h0
    ext x
    · simp only [ContinuousLinearMap.comp_apply, zero_apply,
        ContinuousLinearMap.inl_apply]
      have h1 := congrArg (fun L : V →L[ℝ] ℝ => L x) h0
      have hs : ((x, fderiv ℝ b v₀ x) : V × U) = (x, 0) + (0, fderiv ℝ b v₀ x) := by simp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.id_apply, zero_apply] at h1
      rw [hs, map_add, hb1, add_zero] at h1
      exact h1
    · simpa using hb1 x
  · intro k k'
    have hcu : ContinuousAt (fun u : U => (v₀, u)) (b v₀) :=
      continuousAt_const.prodMk continuousAt_id
    have hd : ∀ᶠ u in 𝓝 (b v₀), DifferentiableAt ℝ H (v₀, u) := hcu.eventually hHd
    have hG : fderiv ℝ (fun u => H (v₀, u)) =ᶠ[𝓝 (b v₀)]
        fun u => (fderiv ℝ H (v₀, u)).comp (ContinuousLinearMap.inr ℝ V U) :=
      hd.mono fun u hu => fderiv_prod_slice_right hu
    set L : (V × U →L[ℝ] ℝ) →L[ℝ] (U →L[ℝ] ℝ) :=
      (ContinuousLinearMap.compL ℝ U (V × U) ℝ).flip (ContinuousLinearMap.inr ℝ V U) with hL
    have hi : HasFDerivAt (fun u : U => (v₀, u)) (ContinuousLinearMap.inr ℝ V U) (b v₀) :=
      hasFDerivAt_prodMk_right v₀ (b v₀)
    have h0 : HasFDerivAt (fun u => fderiv ℝ H (v₀, u))
        (D.comp (ContinuousLinearMap.inr ℝ V U)) (b v₀) :=
      HasFDerivAt.comp (g := fderiv ℝ H) (b v₀) hFd hi
    have h1 : HasFDerivAt (fun u => (fderiv ℝ H (v₀, u)).comp (ContinuousLinearMap.inr ℝ V U))
        (L.comp (D.comp (ContinuousLinearMap.inr ℝ V U))) (b v₀) :=
      L.hasFDerivAt.comp (b v₀) h0
    rw [(h1.congr_of_eventuallyEq hG).fderiv]
    simp [hL]
  · intro h k
    have hdec : ((h, k) : V × U) = A h + (0, k - fderiv ℝ b v₀ h) := by
      simp [hA]
    have hAh : A h = (h, 0) + (0, fderiv ℝ b v₀ h) := by
      simp [hA]
    have hsym : D (0, k - fderiv ℝ b v₀ h) (A h) = D (A h) (0, k - fderiv ℝ b v₀ h) :=
      hsymm _ _
    have hsplit : D (A h) (A h) = D (A h) (h, 0) + D (A h) (0, fderiv ℝ b v₀ h) := by
      rw [← map_add, ← hAh]
    have haa : D (A h) (A h) = fderiv ℝ (fderiv ℝ fun v => H (v, b v)) v₀ h h := by
      rw [hsplit, hzero, add_zero, hφ2]
    have hexp : ∀ c : V × U, D (A h + c) (A h + c) =
        D (A h) (A h) + D c (A h) + (D (A h) c + D c c) := by
      intro c
      simp only [map_add, add_apply]
    rw [hdec, hexp, hsym, hzero, haa]
    simp
end YangMills.Construction.Calculus
end
