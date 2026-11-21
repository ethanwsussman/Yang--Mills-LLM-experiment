import YangMills.Construction.SourcesAndGluing.MeasuresUnderLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesExpectationsAndObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.RescalingKeepsExpectationsAndObservables
def rclikeToComplex (𝕜 : Type) [RCLike 𝕜] : 𝕜 →ₗ[ℝ] ℂ where
  toFun z := ((RCLike.re z : ℝ) : ℂ) + ((RCLike.im z : ℝ) : ℂ) * Complex.I
  map_add' x y := by
    simp only [map_add, Complex.ofReal_add]
    ring
  map_smul' r x := by
    have hre : RCLike.re (r • x) = r * RCLike.re x := RCLike.reLm.map_smul r x
    have him : RCLike.im (r • x) = r * RCLike.im x := RCLike.imLm.map_smul r x
    simp only [hre, him, RingHom.id_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
theorem rclikeToComplex_apply {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) :
    rclikeToComplex 𝕜 z = ((RCLike.re z : ℝ) : ℂ) + ((RCLike.im z : ℝ) : ℂ) * Complex.I := rfl
theorem rclikeToComplex_injective (𝕜 : Type) [RCLike 𝕜] :
    Function.Injective (rclikeToComplex 𝕜) := by
  intro x y h
  rw [rclikeToComplex_apply, rclikeToComplex_apply] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, zero_add] at hre him
  exact RCLike.ext hre him
theorem continuous_rclikeToComplex (𝕜 : Type) [RCLike 𝕜] : Continuous (rclikeToComplex 𝕜) := by
  have h : (rclikeToComplex 𝕜 : 𝕜 → ℂ) =
      fun z => ((RCLike.re z : ℝ) : ℂ) + ((RCLike.im z : ℝ) : ℂ) * Complex.I := rfl
  rw [h]
  exact (Complex.continuous_ofReal.comp RCLike.continuous_re).add
    ((Complex.continuous_ofReal.comp RCLike.continuous_im).mul continuous_const)
theorem norm_rclikeToComplex_le {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) :
    ‖rclikeToComplex 𝕜 z‖ ≤ 2 * ‖z‖ := by
  rw [rclikeToComplex_apply]
  calc ‖((RCLike.re z : ℝ) : ℂ) + ((RCLike.im z : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((RCLike.re z : ℝ) : ℂ)‖ + ‖((RCLike.im z : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |RCLike.re z| + |RCLike.im z| := by simp
    _ ≤ 2 * ‖z‖ := by
      have hre := RCLike.abs_re_le_norm z
      have him := RCLike.abs_im_le_norm z
      linarith
theorem isBoundedBorelCompactlySupported_rclikeToComplex_comp {𝕜 : Type} [RCLike 𝕜]
    {f : InfiniteLattice.AmbientSpace → 𝕜}
    (hf : InfiniteLattice.IsBoundedBorelCompactlySupported f) :
    InfiniteLattice.IsBoundedBorelCompactlySupported (rclikeToComplex 𝕜 ∘ f) := by
  obtain ⟨hmeas, ⟨C, hC⟩, hsupp⟩ := hf
  refine ⟨(continuous_rclikeToComplex 𝕜).measurable.comp hmeas, ⟨2 * C, fun x => ?_⟩,
    hsupp.comp_left (map_zero (rclikeToComplex 𝕜))⟩
  exact (norm_rclikeToComplex_le (f x)).trans (by have := hC x; simpa using by linarith)
theorem rclikeToComplex_finsum {𝕜 ι : Type} [RCLike 𝕜] (c : ι → ℝ) (g : ι → 𝕜) :
    rclikeToComplex 𝕜 (∑ᶠ p, c p • g p) = ∑ᶠ p, c p • (rclikeToComplex 𝕜 ∘ g) p := by
  have h := (rclikeToComplex 𝕜).toAddMonoidHom.map_finsum_of_injective
    (rclikeToComplex_injective 𝕜) (fun p => c p • g p)
  refine h.trans (finsum_congr fun p => ?_)
  exact (rclikeToComplex 𝕜).map_smul (c p) (g p)
theorem statement_holds (hMeas : ScaledMotionMeasuresClaim)
    (hSpace : ScaledMotionObservablesOfSpaceClaim)
    (hTori : ScaledMotionObservablesOfToriClaim) : Statement := by
  intro D Ψ
  refine ⟨fun A hA => ?_, fun 𝕜 _ f V hV => ?_, fun 𝕜 _ f hf => ?_⟩
  · exact ((hMeas D Ψ.scaleExponent Ψ.toMotion A hA D.β D.beta_pos).2).symm
  · apply rclikeToComplex_injective 𝕜
    have h := (hTori D Ψ.scaleExponent Ψ.toMotion).2 (rclikeToComplex 𝕜 ∘ f) V hV
    have hcomm : ∀ (E : GluingSetup) (g : E.Torus → 𝕜)
        (U : E.PeriodicLink → Matrices.ComplexMatrix2),
        rclikeToComplex 𝕜 (E.smeared g U) = E.smeared (rclikeToComplex 𝕜 ∘ g) U :=
      fun E g U => rclikeToComplex_finsum _ _
    change rclikeToComplex 𝕜 (D.smeared f (Ψ.pullTorus V)) =
      rclikeToComplex 𝕜 (Ψ.scaleExponent.target.smeared (f ∘ Ψ.inverseOnTorus) V)
    rw [hcomm, hcomm]
    exact h
  · funext V
    apply rclikeToComplex_injective 𝕜
    have h := (hSpace D Ψ.scaleExponent Ψ.toMotion).2 (rclikeToComplex 𝕜 ∘ f)
      (isBoundedBorelCompactlySupported_rclikeToComplex_comp hf) V
    rw [Ψ.toMotion_onSpace] at h
    have hcomm : ∀ (a : ℝ) (g : InfiniteLattice.AmbientSpace → 𝕜)
        (U : InfiniteLattice.GaugeField a),
        rclikeToComplex 𝕜 (InfiniteLattice.smearedEnergy g U) =
          InfiniteLattice.smearedEnergy (rclikeToComplex 𝕜 ∘ g) U :=
      fun a g U => rclikeToComplex_finsum _ _
    change rclikeToComplex 𝕜 (InfiniteLattice.smearedEnergy f (Ψ.pull V)) =
      rclikeToComplex 𝕜 (InfiniteLattice.smearedEnergy (f ∘ Ψ.inverseOnSpace) V)
    rw [hcomm, hcomm]
    exact h
end YangMills.Construction.SourcesAndGluing.RescalingKeepsExpectationsAndObservables
end
