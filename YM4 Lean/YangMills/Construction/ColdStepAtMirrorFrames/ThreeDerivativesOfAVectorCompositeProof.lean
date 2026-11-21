import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpaceProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAVectorComposite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ThirdOrderChainRule
variable {P D E₀ : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
theorem iteratedFDeriv_one_eq_fderiv (f : P → E₀) (x u : P) : iteratedFDeriv ℝ 1 f x ![u] = fderiv ℝ f x u := by
  simp [iteratedFDeriv_one_apply]
theorem iteratedFDeriv_two_eq_fderiv_fderiv (f : P → E₀) (x u v : P) :
    iteratedFDeriv ℝ 2 f x ![u, v] = fderiv ℝ (fderiv ℝ f) x u v := by
  simp [iteratedFDeriv_two_apply]
theorem iteratedFDeriv_three_eq_fderiv_fderiv_fderiv (f : P → E₀) (x u v w : P) :
    iteratedFDeriv ℝ 3 f x ![u, v, w] = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChainRuleSteps.iteratedFDeriv_three_vecCons <;> assumption
theorem fderiv_clm_apply_eq {E₁ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] (L : P → E₁ →L[ℝ] E₀) (y v : P)
    (w : E₁) (hL : DifferentiableAt ℝ L y) :
    fderiv ℝ L y v w = fderiv ℝ (fun z => L z w) y v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChainRuleSteps.fderiv_clmFamily_apply <;> assumption
theorem hasFDerivAt_comp_of_differentiableAt (Φ : D → E₀) (φ : P → D) (y : P) (hΦ : DifferentiableAt ℝ Φ (φ y))
    (hφ : DifferentiableAt ℝ φ y) :
    HasFDerivAt (fun z => Φ (φ z)) ((fderiv ℝ Φ (φ y)).comp (fderiv ℝ φ y)) y :=
  HasFDerivAt.comp y hΦ.hasFDerivAt hφ.hasFDerivAt
end ThirdOrderChainRule
open ThirdOrderChainRule
theorem thirdOrderChainRuleNormedSpace : ThirdOrderChainRuleNormedSpace := by
  intro P D E _ _ _ _ _ _ g α x hg hα
  have hc : ContDiffAt ℝ 3 (g ∘ α) x := hg.comp x hα
  set G1 : D → D →L[ℝ] E := fderiv ℝ g with hG1
  set G2 : D → D →L[ℝ] D →L[ℝ] E := fderiv ℝ G1 with hG2
  set G3 : D → D →L[ℝ] D →L[ℝ] D →L[ℝ] E := fderiv ℝ G2 with hG3
  set A1 : P → P →L[ℝ] D := fderiv ℝ α with hA1
  set A2 : P → P →L[ℝ] P →L[ℝ] D := fderiv ℝ A1 with hA2
  set A3 : P → P →L[ℝ] P →L[ℝ] P →L[ℝ] D := fderiv ℝ A2 with hA3
  have hαc : ContinuousAt α x := hα.continuousAt
  have eg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 g (α y) :=
    hαc.eventually (hg.eventually (by simp))
  have eα : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 α y := hα.eventually (by simp)
  have dG1 : ∀ {y : P}, ContDiffAt ℝ 3 g (α y) → DifferentiableAt ℝ G1 (α y) := fun h =>
    (h.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have dG2 : ∀ {y : P}, ContDiffAt ℝ 3 g (α y) → DifferentiableAt ℝ G2 (α y) := fun h =>
    (((h.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num))).differentiableAt
      (by norm_num)
  have dA0 : ∀ {y : P}, ContDiffAt ℝ 3 α y → DifferentiableAt ℝ α y := fun h =>
    h.differentiableAt (by norm_num)
  have dA1 : ∀ {y : P}, ContDiffAt ℝ 3 α y → DifferentiableAt ℝ A1 y := fun h =>
    (h.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have dA2 : ∀ {y : P}, ContDiffAt ℝ 3 α y → DifferentiableAt ℝ A2 y := fun h =>
    (((h.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num))).differentiableAt
      (by norm_num)
  have dg0 : ∀ {y : P}, ContDiffAt ℝ 3 g (α y) → DifferentiableAt ℝ g (α y) := fun h =>
    h.differentiableAt (by norm_num)
  have e1 : ∀ y, ContDiffAt ℝ 3 g (α y) → ContDiffAt ℝ 3 α y →
      fderiv ℝ (g ∘ α) y = (G1 (α y)).comp (A1 y) := fun y h1 h2 =>
    fderiv_comp y (dg0 h1) (dA0 h2)
  have cG1 : ∀ (y : P), ContDiffAt ℝ 3 g (α y) → ContDiffAt ℝ 3 α y →
      HasFDerivAt (fun z => G1 (α z)) ((G2 (α y)).comp (A1 y)) y := fun y h1 h2 =>
    hasFDerivAt_comp_of_differentiableAt G1 α y (dG1 h1) (dA0 h2)
  have cG2 : ∀ (y : P), ContDiffAt ℝ 3 g (α y) → ContDiffAt ℝ 3 α y →
      HasFDerivAt (fun z => G2 (α z)) ((G3 (α y)).comp (A1 y)) y := fun y h1 h2 =>
    hasFDerivAt_comp_of_differentiableAt G2 α y (dG2 h1) (dA0 h2)
  have cA1 : ∀ (y : P) (w : P), ContDiffAt ℝ 3 α y →
      HasFDerivAt (fun z => A1 z w) ((A2 y).flip w) y := fun y w h => by
    have := (dA1 h).hasFDerivAt.clm_apply (hasFDerivAt_const w y)
    simpa [ContinuousLinearMap.flip] using this
  have e2 : ∀ y, (∀ᶠ z in 𝓝 y, ContDiffAt ℝ 3 g (α z) ∧ ContDiffAt ℝ 3 α z) → ∀ v w : P,
      fderiv ℝ (fderiv ℝ (g ∘ α)) y v w = G2 (α y) (A1 y v) (A1 y w) + G1 (α y) (A2 y v w) := by
    intro y hy v w
    have hy0 := hy.self_of_nhds
    have hev : fderiv ℝ (g ∘ α) =ᶠ[𝓝 y] fun z => (G1 (α z)).comp (A1 z) :=
      hy.mono fun z hz => e1 z hz.1 hz.2
    rw [hev.fderiv_eq]
    have hR : DifferentiableAt ℝ (fun z => (G1 (α z)).comp (A1 z)) y :=
      ((cG1 y hy0.1 hy0.2).differentiableAt).clm_comp (dA1 hy0.2)
    rw [fderiv_clm_apply_eq _ y v w hR]
    have h3 := ((cG1 y hy0.1 hy0.2).clm_apply (cA1 y w hy0.2)).fderiv
    have : (fun z => ((G1 (α z)).comp (A1 z)) w) = fun z => G1 (α z) (A1 z w) := rfl
    rw [this, h3]
    simp [add_comm]
  have eboth : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 3 g (α z) ∧ ContDiffAt ℝ 3 α z :=
    (eg.and eα).eventually_nhds
  have hx : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 3 g (α z) ∧ ContDiffAt ℝ 3 α z := eg.and eα
  obtain ⟨hgx, hαx⟩ := hx.self_of_nhds
  have symm : ∀ p q : D, G2 (α x) p q = G2 (α x) q p := fun p q =>
    (hgx.isSymmSndFDerivAt (by simp; norm_num)).eq p q
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro u
    simp only [iteratedFDeriv_one_eq_fderiv]
    rw [e1 x hgx hαx]
    rfl
  · intro u v
    simp only [iteratedFDeriv_one_eq_fderiv, iteratedFDeriv_two_eq_fderiv_fderiv]
    exact e2 x hx u v
  · intro u v w
    simp only [iteratedFDeriv_one_eq_fderiv, iteratedFDeriv_two_eq_fderiv_fderiv,
      iteratedFDeriv_three_eq_fderiv_fderiv_fderiv]
    have d2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (g ∘ α))) x :=
      ((hc.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    rw [fderiv_clm_apply_eq _ x u v d2]
    have d2v : DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ (g ∘ α)) z v) x :=
      d2.clm_apply (differentiableAt_const v)
    rw [fderiv_clm_apply_eq _ x u w d2v]
    have hev : (fun z => fderiv ℝ (fderiv ℝ (g ∘ α)) z v w) =ᶠ[𝓝 x]
        fun z => G2 (α z) (A1 z v) (A1 z w) + G1 (α z) (A2 z v w) :=
      eboth.mono fun z hz => e2 z hz v w
    rw [hev.fderiv_eq]
    have cv := cA1 x v hαx
    have cw := cA1 x w hαx
    have t1 := ((cG2 x hgx hαx).clm_apply cv).clm_apply cw
    have c2 : HasFDerivAt (fun z => A2 z v w) (((A3 x).flip v).flip w) x := by
      have h1 := (dA2 hαx).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
      have h2 := h1.clm_apply (hasFDerivAt_const w x)
      simpa [ContinuousLinearMap.flip] using h2
    have t2 := (cG1 x hgx hαx).clm_apply c2
    have tt := (t1.add t2).fderiv
    have : (fun z => G2 (α z) (A1 z v) (A1 z w) + G1 (α z) (A2 z v w)) =
        ((fun z => G2 (α z) (A1 z v) (A1 z w)) + fun z => G1 (α z) (A2 z v w)) := rfl
    rw [this, tt]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [symm (A1 x v) (A2 x u w), symm (A1 x u) (A2 x v w)]
    abel
end YangMills.Construction.ColdStepAtMirrorFrames
end
