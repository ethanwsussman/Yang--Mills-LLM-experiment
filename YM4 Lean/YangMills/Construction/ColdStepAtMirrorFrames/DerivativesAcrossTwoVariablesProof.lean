import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesAcrossTwoVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction.Calculus
namespace IteratedFDerivParamDiffAux
variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
private theorem iteratedFDeriv_succ_eq_fderiv_last {j : ℕ} {g : P → ℝ} {s₀ : P}
    (hg : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g s₀) (v : Fin (j + 1) → P) :
    iteratedFDeriv ℝ (j + 1) g s₀ v =
      iteratedFDeriv ℝ j (fun s => fderiv ℝ g s (v (Fin.last j))) s₀ (Fin.init v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hd : ContDiffAt ℝ (j : WithTop ℕ∞) (fderiv ℝ g) s₀ :=
    hg.fderiv_right (m := (j : WithTop ℕ∞)) (by norm_cast)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.apply ℝ ℝ (v (Fin.last j)) : (P →L[ℝ] ℝ) →L[ℝ] ℝ) hd (i := j) le_rfl
  have h2 : (fun s => fderiv ℝ g s (v (Fin.last j))) =
      (ContinuousLinearMap.apply ℝ ℝ (v (Fin.last j)) : (P →L[ℝ] ℝ) →L[ℝ] ℝ) ∘ fderiv ℝ g := rfl
  rw [h2, h]
  rfl
private theorem hasFDerivAt_prod_left {G : P × Q → ℝ} {s : P} {ζ : Q} (h : DifferentiableAt ℝ G (s, ζ)) :
    HasFDerivAt (fun s' => G (s', ζ)) ((fderiv ℝ G (s, ζ)).comp (ContinuousLinearMap.inl ℝ P Q)) s := by
  have h1 : HasFDerivAt (fun s' : P => (s', ζ)) (ContinuousLinearMap.inl ℝ P Q) s :=
    (hasFDerivAt_id s).prodMk (hasFDerivAt_const ζ s)
  exact HasFDerivAt.comp s h.hasFDerivAt h1
private theorem hasFDerivAt_prod_right {G : P × Q → ℝ} {s : P} {ζ : Q} (h : DifferentiableAt ℝ G (s, ζ)) :
    HasFDerivAt (fun ζ' => G (s, ζ')) ((fderiv ℝ G (s, ζ)).comp (ContinuousLinearMap.inr ℝ P Q)) ζ := by
  have h1 : HasFDerivAt (fun ζ' : Q => (s, ζ')) (ContinuousLinearMap.inr ℝ P Q) ζ :=
    (hasFDerivAt_const s ζ).prodMk (hasFDerivAt_id ζ)
  exact HasFDerivAt.comp ζ h.hasFDerivAt h1
private theorem fderiv_prod_left_apply {G : P × Q → ℝ} {s : P} {ζ : Q} (h : DifferentiableAt ℝ G (s, ζ)) (w : P) :
    fderiv ℝ (fun s' => G (s', ζ)) s w = fderiv ℝ G (s, ζ) (w, 0) := by
  rw [(hasFDerivAt_prod_left h).fderiv]
  simp
private theorem fderiv_prod_right_apply {G : P × Q → ℝ} {s : P} {ζ : Q} (h : DifferentiableAt ℝ G (s, ζ)) (e : Q) :
    fderiv ℝ (fun ζ' => G (s, ζ')) ζ e = fderiv ℝ G (s, ζ) (0, e) := by
  rw [(hasFDerivAt_prod_right h).fderiv]
  simp
private theorem iteratedFDeriv_param_fderiv_comm (j : ℕ) : ∀ (G : P × Q → ℝ) (η : Q) (v : Fin j → P),
    ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) G (0, η) →
    ContDiffAt ℝ 1 (fun ζ => iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v) η ∧
      ∀ e : Q, fderiv ℝ (fun ζ => iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v) η e =
        iteratedFDeriv ℝ j (fun s => fderiv ℝ (fun ζ => G (s, ζ)) η e) 0 v := by
  induction j with
  | zero =>
    intro G η v hG
    have hG1 : ContDiffAt ℝ 1 G (0, η) := by simpa using hG
    have h0 : (fun ζ => iteratedFDeriv ℝ 0 (fun s => G (s, ζ)) 0 v) = fun ζ => G (0, ζ) := by
      funext ζ
      simp
    rw [h0]
    refine ⟨?_, fun e => ?_⟩
    · have hp : ContDiffAt ℝ 1 (fun ζ : Q => ((0 : P), ζ)) η :=
        contDiffAt_const.prodMk contDiffAt_id
      exact ContDiffAt.comp η hG1 hp
    · simp
  | succ j ih =>
    intro G η v hG
    set w := v (Fin.last j) with hw
    set v' := Fin.init v with hv'
    set G' : P × Q → ℝ := fun z => fderiv ℝ G z (w, 0) with hG'
    have hfd : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ G) (0, η) :=
      hG.fderiv_right (m := ((j + 1 : ℕ) : WithTop ℕ∞)) (by norm_cast)
    have hG'c : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) G' (0, η) :=
      hfd.clm_apply contDiffAt_const
    have hev := hG.eventually (by simp)
    obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.mp hev
    have hS : ∀ s ∈ u, ∀ ζ ∈ t, ContDiffAt ℝ ((j + 1 + 1 : ℕ) : WithTop ℕ∞) G (s, ζ) :=
      fun s hs ζ hζ => hut (Set.mk_mem_prod hs hζ)
    have hD : ∀ s ∈ u, ∀ ζ ∈ t, DifferentiableAt ℝ G (s, ζ) := fun s hs ζ hζ =>
      (hS s hs ζ hζ).differentiableAt (by simp)
    have h0u : (0 : P) ∈ u := mem_of_mem_nhds hu
    have hηt : η ∈ t := mem_of_mem_nhds ht
    have hkey : ∀ ζ ∈ t, iteratedFDeriv ℝ (j + 1) (fun s => G (s, ζ)) 0 v =
        iteratedFDeriv ℝ j (fun s => G' (s, ζ)) 0 v' := by
      intro ζ hζ
      have hc : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun s => G (s, ζ)) 0 := by
        have hp : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun s : P => (s, ζ)) 0 :=
          contDiffAt_id.prodMk contDiffAt_const
        exact ContDiffAt.comp (0 : P) ((hS 0 h0u ζ hζ).of_le (by norm_cast; omega)) hp
      rw [iteratedFDeriv_succ_eq_fderiv_last hc]
      have hee : (fun s => fderiv ℝ (fun s' => G (s', ζ)) s w) =ᶠ[𝓝 (0 : P)] fun s => G' (s, ζ) := by
        filter_upwards [hu] with s hs
        exact fderiv_prod_left_apply (hD s hs ζ hζ) w
      rw [(hee.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    have hev2 : (fun ζ => iteratedFDeriv ℝ (j + 1) (fun s => G (s, ζ)) 0 v) =ᶠ[𝓝 η]
        fun ζ => iteratedFDeriv ℝ j (fun s => G' (s, ζ)) 0 v' := by
      filter_upwards [ht] with ζ hζ using hkey ζ hζ
    obtain ⟨i1, i2⟩ := ih G' η v' hG'c
    refine ⟨i1.congr_of_eventuallyEq hev2, fun e => ?_⟩
    rw [hev2.fderiv_eq, i2 e]
    set ge : P → ℝ := fun s => fderiv ℝ (fun ζ => G (s, ζ)) η e with hge
    have hgeq : ge =ᶠ[𝓝 0] fun s => fderiv ℝ G (s, η) (0, e) := by
      filter_upwards [hu] with s hs
      exact fderiv_prod_right_apply (hD s hs η hηt) e
    have hgc : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) ge 0 := by
      refine ContDiffAt.congr_of_eventuallyEq ?_ hgeq
      have hp : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun s : P => (s, η)) 0 :=
        contDiffAt_id.prodMk contDiffAt_const
      exact (ContDiffAt.comp (0 : P) hfd hp).clm_apply contDiffAt_const
    rw [iteratedFDeriv_succ_eq_fderiv_last hgc]
    suffices hee : (fun s => fderiv ℝ (fun ζ => G' (s, ζ)) η e) =ᶠ[𝓝 (0 : P)] fun s => fderiv ℝ ge s w by
      rw [(hee.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    have hgeq' : ∀ᶠ s in 𝓝 (0 : P), ge =ᶠ[𝓝 s] fun s => fderiv ℝ G (s, η) (0, e) := by
      have := eventually_eventually_nhds.mpr hgeq
      exact this
    have hopen : ∀ᶠ s in 𝓝 (0 : P), ContDiffAt ℝ ((j + 1 + 1 : ℕ) : WithTop ℕ∞) G (s, η) := by
      filter_upwards [hu] with s hs using hS s hs η hηt
    filter_upwards [hgeq', hopen, hu] with s hs1 hs2 hs3
    have hC2 : ContDiffAt ℝ 2 G (s, η) := hs2.of_le (by norm_cast; omega)
    have hfdd : DifferentiableAt ℝ (fderiv ℝ G) (s, η) :=
      (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have hsym := hC2.isSymmSndFDerivAt (by simp)
    have e1 : fderiv ℝ (fun ζ => G' (s, ζ)) η e = fderiv ℝ (fderiv ℝ G) (s, η) (0, e) (w, 0) := by
      have hpath : (fun ζ => G' (s, ζ)) = fun ζ => (fderiv ℝ G) (s, ζ) (w, 0) := rfl
      have h1 : HasFDerivAt (fun ζ' : Q => (s, ζ')) (ContinuousLinearMap.inr ℝ P Q) η :=
        (hasFDerivAt_const s η).prodMk (hasFDerivAt_id η)
      have h2 : HasFDerivAt (fun ζ' => (fderiv ℝ G) (s, ζ'))
          ((fderiv ℝ (fderiv ℝ G) (s, η)).comp (ContinuousLinearMap.inr ℝ P Q)) η :=
        HasFDerivAt.comp η hfdd.hasFDerivAt h1
      have h3 := h2.clm_apply (hasFDerivAt_const ((w, 0) : P × Q) η)
      rw [hpath, h3.fderiv]
      simp
    have e2 : fderiv ℝ ge s w = fderiv ℝ (fderiv ℝ G) (s, η) (w, 0) (0, e) := by
      rw [hs1.fderiv_eq]
      have h1 : HasFDerivAt (fun s' : P => (s', η)) (ContinuousLinearMap.inl ℝ P Q) s :=
        (hasFDerivAt_id s).prodMk (hasFDerivAt_const η s)
      have h2 : HasFDerivAt (fun s' => (fderiv ℝ G) (s', η))
          ((fderiv ℝ (fderiv ℝ G) (s, η)).comp (ContinuousLinearMap.inl ℝ P Q)) s :=
        HasFDerivAt.comp s hfdd.hasFDerivAt h1
      have h3 := h2.clm_apply (hasFDerivAt_const ((0, e) : P × Q) s)
      rw [h3.fderiv]
      simp
    rw [e1, e2, hsym]
end IteratedFDerivParamDiffAux
theorem iteratedFDerivParamDiff_holds : IteratedFDerivParamDiff := by
  intro P Q _ _ _ _ j G η v hG
  exact IteratedFDerivParamDiffAux.iteratedFDeriv_param_fderiv_comm j G η v hG
end YangMills.Construction.Calculus
end
