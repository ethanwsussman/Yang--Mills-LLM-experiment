import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChainRuleSteps
variable {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem iteratedFDeriv_one_vecCons (f : V → F) (x a : V) :
    iteratedFDeriv ℝ 1 f x ![a] = fderiv ℝ f x a := by
  simp [iteratedFDeriv_one_apply]
theorem iteratedFDeriv_two_vecCons (f : V → F) (x a b : V) :
    iteratedFDeriv ℝ 2 f x ![a, b] = fderiv ℝ (fderiv ℝ f) x a b := by
  simp [iteratedFDeriv_two_apply]
theorem iteratedFDeriv_three_vecCons (f : V → F) (x a b c : V) :
    iteratedFDeriv ℝ 3 f x ![a, b, c] = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  simp [Fin.init]
theorem fderiv_clmFamily_apply {F₁ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    (T : V → F₁ →L[ℝ] F) (y b : V) (c : F₁) (hT : DifferentiableAt ℝ T y) :
    fderiv ℝ T y b c = fderiv ℝ (fun z => T z c) y b := by
  have := (hT.hasFDerivAt.clm_apply (hasFDerivAt_const c y)).fderiv
  rw [this]
  simp
theorem hasFDerivAt_comp_fderiv (Ψ : W → F) (ψ : V → W) (y : V) (hΨ : DifferentiableAt ℝ Ψ (ψ y))
    (hψ : DifferentiableAt ℝ ψ y) :
    HasFDerivAt (fun z => Ψ (ψ z)) ((fderiv ℝ Ψ (ψ y)).comp (fderiv ℝ ψ y)) y :=
  HasFDerivAt.comp y hΨ.hasFDerivAt hψ.hasFDerivAt
end ChainRuleSteps
open ChainRuleSteps
theorem thirdOrderChainRuleVectorValued_holds : ThirdOrderChainRuleVectorValued := by
  intro V W F _ _ _ _ _ _ f γ x hf hγ
  have hcomp : ContDiffAt ℝ 3 (f ∘ γ) x := hf.comp x hγ
  set D1 : W → W →L[ℝ] F := fderiv ℝ f with hD1
  set D2 : W → W →L[ℝ] W →L[ℝ] F := fderiv ℝ D1 with hD2
  set D3 : W → W →L[ℝ] W →L[ℝ] W →L[ℝ] F := fderiv ℝ D2 with hD3
  set C1 : V → V →L[ℝ] W := fderiv ℝ γ with hC1
  set C2 : V → V →L[ℝ] V →L[ℝ] W := fderiv ℝ C1 with hC2
  set C3 : V → V →L[ℝ] V →L[ℝ] V →L[ℝ] W := fderiv ℝ C2 with hC3
  have hγcont : ContinuousAt γ x := hγ.continuousAt
  have evf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 f (γ y) :=
    hγcont.eventually (hf.eventually (by simp))
  have evγ : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 γ y := hγ.eventually (by simp)
  have diffD1 : ∀ {y : V}, ContDiffAt ℝ 3 f (γ y) → DifferentiableAt ℝ D1 (γ y) := fun h =>
    (h.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have diffD2 : ∀ {y : V}, ContDiffAt ℝ 3 f (γ y) → DifferentiableAt ℝ D2 (γ y) := fun h =>
    (((h.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num))).differentiableAt
      (by norm_num)
  have diffC0 : ∀ {y : V}, ContDiffAt ℝ 3 γ y → DifferentiableAt ℝ γ y := fun h =>
    h.differentiableAt (by norm_num)
  have diffC1 : ∀ {y : V}, ContDiffAt ℝ 3 γ y → DifferentiableAt ℝ C1 y := fun h =>
    (h.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have diffC2 : ∀ {y : V}, ContDiffAt ℝ 3 γ y → DifferentiableAt ℝ C2 y := fun h =>
    (((h.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num))).differentiableAt
      (by norm_num)
  have diffD0 : ∀ {y : V}, ContDiffAt ℝ 3 f (γ y) → DifferentiableAt ℝ f (γ y) := fun h =>
    h.differentiableAt (by norm_num)
  have first : ∀ y, ContDiffAt ℝ 3 f (γ y) → ContDiffAt ℝ 3 γ y →
      fderiv ℝ (f ∘ γ) y = (D1 (γ y)).comp (C1 y) := fun y h1 h2 =>
    fderiv_comp y (diffD0 h1) (diffC0 h2)
  have hasD1 : ∀ (y : V), ContDiffAt ℝ 3 f (γ y) → ContDiffAt ℝ 3 γ y →
      HasFDerivAt (fun z => D1 (γ z)) ((D2 (γ y)).comp (C1 y)) y := fun y h1 h2 =>
    hasFDerivAt_comp_fderiv D1 γ y (diffD1 h1) (diffC0 h2)
  have hasD2 : ∀ (y : V), ContDiffAt ℝ 3 f (γ y) → ContDiffAt ℝ 3 γ y →
      HasFDerivAt (fun z => D2 (γ z)) ((D3 (γ y)).comp (C1 y)) y := fun y h1 h2 =>
    hasFDerivAt_comp_fderiv D2 γ y (diffD2 h1) (diffC0 h2)
  have hasC1 : ∀ (y : V) (c : V), ContDiffAt ℝ 3 γ y →
      HasFDerivAt (fun z => C1 z c) ((C2 y).flip c) y := fun y c h => by
    have := (diffC1 h).hasFDerivAt.clm_apply (hasFDerivAt_const c y)
    simpa [ContinuousLinearMap.flip] using this
  have second : ∀ y, (∀ᶠ z in 𝓝 y, ContDiffAt ℝ 3 f (γ z) ∧ ContDiffAt ℝ 3 γ z) → ∀ b c : V,
      fderiv ℝ (fderiv ℝ (f ∘ γ)) y b c = D2 (γ y) (C1 y b) (C1 y c) + D1 (γ y) (C2 y b c) := by
    intro y hy b c
    have hy0 := hy.self_of_nhds
    have hev : fderiv ℝ (f ∘ γ) =ᶠ[𝓝 y] fun z => (D1 (γ z)).comp (C1 z) :=
      hy.mono fun z hz => first z hz.1 hz.2
    rw [hev.fderiv_eq]
    have hdiff : DifferentiableAt ℝ (fun z => (D1 (γ z)).comp (C1 z)) y :=
      ((hasD1 y hy0.1 hy0.2).differentiableAt).clm_comp (diffC1 hy0.2)
    rw [fderiv_clmFamily_apply _ y b c hdiff]
    have hprod := ((hasD1 y hy0.1 hy0.2).clm_apply (hasC1 y c hy0.2)).fderiv
    have : (fun z => ((D1 (γ z)).comp (C1 z)) c) = fun z => D1 (γ z) (C1 z c) := rfl
    rw [this, hprod]
    simp [add_comm]
  have evboth : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 3 f (γ z) ∧ ContDiffAt ℝ 3 γ z :=
    (evf.and evγ).eventually_nhds
  have hnear : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 3 f (γ z) ∧ ContDiffAt ℝ 3 γ z := evf.and evγ
  obtain ⟨hfx, hγx⟩ := hnear.self_of_nhds
  have hsymm : ∀ p q : W, D2 (γ x) p q = D2 (γ x) q p := fun p q =>
    (hfx.isSymmSndFDerivAt (by simp; norm_num)).eq p q
  refine ⟨hcomp, ?_, ?_, ?_⟩
  · intro a
    simp only [iteratedFDeriv_one_vecCons]
    rw [first x hfx hγx]
    rfl
  · intro a b
    simp only [iteratedFDeriv_one_vecCons, iteratedFDeriv_two_vecCons]
    exact second x hnear a b
  · intro a b c
    simp only [iteratedFDeriv_one_vecCons, iteratedFDeriv_two_vecCons, iteratedFDeriv_three_vecCons]
    have dsecond : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (f ∘ γ))) x :=
      ((hcomp.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    rw [fderiv_clmFamily_apply _ x a b dsecond]
    have dsecondb : DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ (f ∘ γ)) z b) x :=
      dsecond.clm_apply (differentiableAt_const b)
    rw [fderiv_clmFamily_apply _ x a c dsecondb]
    have hev : (fun z => fderiv ℝ (fderiv ℝ (f ∘ γ)) z b c) =ᶠ[𝓝 x]
        fun z => D2 (γ z) (C1 z b) (C1 z c) + D1 (γ z) (C2 z b c) :=
      evboth.mono fun z hz => second z hz b c
    rw [hev.fderiv_eq]
    have hb := hasC1 x b hγx
    have hc := hasC1 x c hγx
    have term1 := ((hasD2 x hfx hγx).clm_apply hb).clm_apply hc
    have hC2bc : HasFDerivAt (fun z => C2 z b c) (((C3 x).flip b).flip c) x := by
      have h1 := (diffC2 hγx).hasFDerivAt.clm_apply (hasFDerivAt_const b x)
      have h2 := h1.clm_apply (hasFDerivAt_const c x)
      simpa [ContinuousLinearMap.flip] using h2
    have term2 := (hasD1 x hfx hγx).clm_apply hC2bc
    have hsum := (term1.add term2).fderiv
    have : (fun z => D2 (γ z) (C1 z b) (C1 z c) + D1 (γ z) (C2 z b c)) =
        ((fun z => D2 (γ z) (C1 z b) (C1 z c)) + fun z => D1 (γ z) (C2 z b c)) := rfl
    rw [this, hsum]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [hsymm (C1 x b) (C2 x a c), hsymm (C1 x a) (C2 x b c)]
    abel
end YangMills.Construction.ColdStepAtMirrorFrames
end
