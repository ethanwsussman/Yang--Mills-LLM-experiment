import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsFromSlopesProof
import YangMills.Construction.ColdStepAtMirrorFrames.GradientOfANearFunction
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesOfTwoNearFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace BondPartialDiff
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem isOpen_openPolyball (r : ℝ) : IsOpen (openPolyball ι r) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.isOpen_openPolyball <;> assumption
theorem add_smul_bondVariation_mem {r₁ r₂ δ : ℝ} (hr : r₁ + δ ≤ r₂) (hδ : 0 < δ) {ξ : BondField ι}
    (hξ : ξ ∈ openPolyball ι r₁) (k : ι) {e : BondVector} (he : ‖e‖ = 1) {u : ℝ}
    (hu : u ∈ Set.Icc 0 δ) :
    ξ + u • bondVariation k e ∈ openPolyball ι r₂ := fun b => by
  have hb₀ := hξ b
  by_cases hb : b = k
  · subst hb
    have e1 : (ξ + u • bondVariation b e) b = ξ b + u • e := by simp [bondVariation]
    rw [e1]
    have := norm_add_le (ξ b) (u • e)
    have e2 : ‖u • e‖ = u := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hu.1]
    have := hu.2
    linarith
  · have e1 : (ξ + u • bondVariation k e) b = ξ b := by
      simp [bondVariation, Pi.single_eq_of_ne hb]
    rw [e1]
    linarith
theorem hasDerivAt_line_and_fderiv {r : ℝ} {G : BondField ι → ℝ}
    (hG : ContDiffOn ℝ 2 G (openPolyball ι r))
    {ξ a : BondField ι} {u : ℝ} (hm : ξ + u • a ∈ openPolyball ι r) :
    HasDerivAt (fun s : ℝ => G (ξ + s • a)) (fderiv ℝ G (ξ + u • a) a) u ∧
      HasDerivAt (fun s : ℝ => fderiv ℝ G (ξ + s • a) a) (secondDerivAlong G (ξ + u • a) a a) u := by
  have ho := isOpen_openPolyball (ι := ι) r
  have hc : HasDerivAt (fun s : ℝ => ξ + s • a) a u := by
    simpa using ((hasDerivAt_id u).smul_const a).const_add ξ
  have h0 : DifferentiableAt ℝ G (ξ + u • a) :=
    (hG.contDiffAt (ho.mem_nhds hm)).differentiableAt (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ G) (openPolyball ι r) := hG.fderiv_of_isOpen ho (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ G) (ξ + u • a) :=
    (h1.contDiffAt (ho.mem_nhds hm)).differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (fun ζ => fderiv ℝ G ζ a) (ξ + u • a) :=
    h2.clm_apply (differentiableAt_const a)
  refine ⟨h0.hasFDerivAt.comp_hasDerivAt u hc, ?_⟩
  have h4 := h3.hasFDerivAt.comp_hasDerivAt u hc
  exact h4
end BondPartialDiff
theorem bondPartialDiffBound_of_derivDiffBound (hS : Calculus.DerivDiffBoundOfClose) :
    BondPartialDiffBound := by
  intro ι _ _ r₁ r₂ δ M₀ M₂ G₁ G₂ hδ hr₁ hr h₁ h₂ hM h2₁ h2₂ ξ hξ k e he
  have hmem := fun u (hu : u ∈ Set.Icc 0 δ) =>
    BondPartialDiff.add_smul_bondVariation_mem hr hδ hξ k he hu
  have key := hS (fun s => G₁ (ξ + s • bondVariation k e)) (fun s => G₂ (ξ + s • bondVariation k e))
    (fun s => fderiv ℝ G₁ (ξ + s • bondVariation k e) (bondVariation k e))
    (fun s => fderiv ℝ G₂ (ξ + s • bondVariation k e) (bondVariation k e))
    (fun s => secondDerivAlong G₁ (ξ + s • bondVariation k e) (bondVariation k e) (bondVariation k e))
    (fun s => secondDerivAlong G₂ (ξ + s • bondVariation k e) (bondVariation k e) (bondVariation k e))
    δ M₀ M₂ hδ
    (fun u hu => (BondPartialDiff.hasDerivAt_line_and_fderiv h₁ (hmem u hu)).1)
    (fun u hu => (BondPartialDiff.hasDerivAt_line_and_fderiv h₂ (hmem u hu)).1)
    (fun u hu => (BondPartialDiff.hasDerivAt_line_and_fderiv h₁ (hmem u hu)).2)
    (fun u hu => (BondPartialDiff.hasDerivAt_line_and_fderiv h₂ (hmem u hu)).2)
    (fun u hu => h2₁ _ (hmem u hu) k e he) (fun u hu => h2₂ _ (hmem u hu) k e he)
    (hM _ (hmem 0 ⟨le_rfl, hδ.le⟩)) (hM _ (hmem δ ⟨hδ.le, le_rfl⟩))
  simpa [bondPartialDeriv] using key
end YangMills.Construction.ColdStepAtMirrorFrames
end
