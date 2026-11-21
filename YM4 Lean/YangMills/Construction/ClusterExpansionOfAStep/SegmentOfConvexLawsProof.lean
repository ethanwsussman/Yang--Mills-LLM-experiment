import YangMills.Construction.ClusterExpansionOfAStep.MixedDifferenceOfALogarithmProof
import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ClusterExpansionOfAStep.SegmentOfConvexLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
namespace ConvexLawSegment
set_option linter.unusedSectionVars false
section Tilt
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A G : Ω → ℝ} {M : ℝ}
def tiltWeight (A G : Ω → ℝ) (v : ℝ) (ω : Ω) : ℝ := Real.exp (-(A ω + v * G ω))
theorem measurable_tiltWeight (hA : Measurable A) (hG : Measurable G) (v : ℝ) :
    Measurable (tiltWeight A G v) := by apply _root_.YangMills.Construction.MixedDifferences.lineWeight_measurable <;> assumption
omit [MeasurableSpace Ω] in
theorem abs_tiltWeight_le {ω : Ω} (hA : |A ω| ≤ M) (hG : |G ω| ≤ M) {v₀ v : ℝ} (hv : |v - v₀| < 1) :
    |tiltWeight A G v ω| ≤ Real.exp ((|v₀| + 2) * M) := by
  unfold tiltWeight
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 : |v| ≤ |v₀| + 1 := by
    have := abs_sub_abs_le_abs_sub v v₀
    linarith
  have h3 : |A ω + v * G ω| ≤ M + (|v₀| + 1) * M := by
    calc |A ω + v * G ω| ≤ |A ω| + |v * G ω| := abs_add_le _ _
      _ = |A ω| + |v| * |G ω| := by rw [abs_mul]
      _ ≤ M + (|v₀| + 1) * M := by gcongr
  have := neg_abs_le (A ω + v * G ω)
  nlinarith
theorem integrable_mul_tiltWeight {H : Ω → ℝ} {K : ℝ} (hH : Measurable H) (hHK : ∀ᵐ ω ∂μ, |H ω| ≤ K)
    (hA : Measurable A) (hG : Measurable G) (hAM : ∀ᵐ ω ∂μ, |A ω| ≤ M) (hGM : ∀ᵐ ω ∂μ, |G ω| ≤ M) (v : ℝ) :
    Integrable (fun ω => H ω * tiltWeight A G v ω) μ := by
  refine Integrable.of_bound ((hH.mul (measurable_tiltWeight hA hG v)).aestronglyMeasurable)
    (K * Real.exp ((|v| + 2) * M)) ?_
  filter_upwards [hHK, hAM, hGM] with ω h1 h2 h3
  rw [Real.norm_eq_abs, abs_mul]
  have h4 := abs_tiltWeight_le h2 h3 (v₀ := v) (v := v) (by simp)
  have hK : 0 ≤ K := (abs_nonneg _).trans h1
  gcongr
theorem hasDerivAt_integral_mul_tiltWeight {H : Ω → ℝ} {K : ℝ} (hH : Measurable H)
    (hHK : ∀ᵐ ω ∂μ, |H ω| ≤ K)
    (hA : Measurable A) (hG : Measurable G) (hAM : ∀ᵐ ω ∂μ, |A ω| ≤ M) (hGM : ∀ᵐ ω ∂μ, |G ω| ≤ M) (v₀ : ℝ) :
    HasDerivAt (fun v => ∫ ω, H ω * tiltWeight A G v ω ∂μ)
      (∫ ω, -(H ω * G ω * tiltWeight A G v₀ ω) ∂μ) v₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun v ω => H ω * tiltWeight A G v ω) (F' := fun v ω => -(H ω * G ω * tiltWeight A G v ω))
    (x₀ := v₀)
    (s := Metric.ball v₀ 1) (bound := fun _ => K * M * Real.exp ((|v₀| + 2) * M))
    (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun v => (hH.mul (measurable_tiltWeight hA hG v)).aestronglyMeasurable)
    (integrable_mul_tiltWeight hH hHK hA hG hAM hGM v₀)
    (((hH.mul hG).mul (measurable_tiltWeight hA hG v₀)).neg.aestronglyMeasurable)
    (by
      filter_upwards [hHK, hAM, hGM] with ω h1 h2 h3 v hv
      have hv' : |v - v₀| < 1 := by simpa [Real.dist_eq] using hv
      have h4 := abs_tiltWeight_le h2 h3 hv'
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
      have hK : 0 ≤ K := (abs_nonneg _).trans h1
      have hM : 0 ≤ M := (abs_nonneg _).trans h2
      gcongr)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω v _ => by
      have h0 : HasDerivAt (fun x => A ω + x * G ω) (1 * G ω) v :=
        ((hasDerivAt_id' v).mul_const (G ω)).const_add (A ω)
      have h1 : HasDerivAt (fun x => -(A ω + x * G ω)) (-(1 * G ω)) v := h0.neg
      have h2 := (h1.exp).const_mul (H ω)
      exact h2.congr_deriv (by simp only [tiltWeight]; ring))
  exact key.2
def tiltedMean (μ : Measure Ω) (A G H : Ω → ℝ) (v : ℝ) : ℝ :=
  (∫ ω, H ω * tiltWeight A G v ω ∂μ) / ∫ ω, tiltWeight A G v ω ∂μ
theorem abs_tiltedMean_sub_le [NeZero μ] {F : Ω → ℝ} {K c : ℝ} (hF : Measurable F)
    (hFK : ∀ᵐ ω ∂μ, |F ω| ≤ K)
    (hA : Measurable A) (hG : Measurable G) (hAM : ∀ᵐ ω ∂μ, |A ω| ≤ M) (hGM : ∀ᵐ ω ∂μ, |G ω| ≤ M)
    (hc : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |tiltedMean μ A G (fun ω => F ω * G ω) v - tiltedMean μ A G F v * tiltedMean μ A G G v| ≤ c) :
    |tiltedMean μ A G F 1 - tiltedMean μ A G F 0| ≤ c := by
  have hone : ∀ᵐ ω ∂μ, |(fun _ : Ω => (1 : ℝ)) ω| ≤ 1 := Filter.Eventually.of_forall fun _ => by simp
  have hZpos : ∀ v, 0 < ∫ ω, tiltWeight A G v ω ∂μ := by
    intro v
    have hi : Integrable (fun ω => Real.exp (-(A ω + v * G ω))) μ := by
      have := integrable_mul_tiltWeight (μ := μ) (H := fun _ => (1 : ℝ)) measurable_const hone hA hG
        hAM hGM v
      simpa [tiltWeight] using this
    exact integral_exp_pos hi
  have hder : ∀ v, HasDerivAt (tiltedMean μ A G F)
      (-(tiltedMean μ A G (fun ω => F ω * G ω) v - tiltedMean μ A G F v * tiltedMean μ A G G v)) v := by
    intro v
    have hN := hasDerivAt_integral_mul_tiltWeight (μ := μ) hF hFK hA hG hAM hGM v
    have hZ := hasDerivAt_integral_mul_tiltWeight (μ := μ) (H := fun _ => (1 : ℝ)) measurable_const
      hone hA hG hAM hGM v
    simp only [one_mul] at hZ
    have hq := hN.div hZ (hZpos v).ne'
    have hZ0 := (hZpos v).ne'
    have hq' : HasDerivAt (tiltedMean μ A G F) _ v := hq
    refine hq'.congr_deriv ?_
    unfold tiltedMean
    rw [integral_neg, integral_neg]
    field_simp
    ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := tiltedMean μ A G F)
    (f' := fun v =>
      -(tiltedMean μ A G (fun ω => F ω * G ω) v - tiltedMean μ A G F v * tiltedMean μ A G G v))
    (s := Set.Icc (0 : ℝ) 1) (C := c) (x := 0) (y := 1)
    (fun v _ => (hder v).hasDerivWithinAt)
    (fun v hv => by rw [norm_neg, Real.norm_eq_abs]; exact hc v hv)
    (convex_Icc 0 1) (by simp) (by simp)
  simpa [Real.norm_eq_abs] using this
end Tilt
section BallLaw
open BallLaws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem tiltedMean_radialLaw_eq_ballExpectation (hp : IsCutoff ρ p) (A G H : BondField ι → ℝ) (v : ℝ) :
    tiltedMean (radialLaw ι ρ p) A G H v = ballExpectation (cutoffFactor ρ p) (fun η => A η + v * G η) H := by
  unfold tiltedMean ballExpectation ballDensity tiltWeight
  rw [integral_radialLaw hp, integral_radialLaw hp]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only
    ring
end BallLaw
open BallLaws in
theorem convexLawSegmentBound_of_covariance (hcov : ConvexMeasures.covarianceLocalMeasurableBound) :
    ConvexLawSegmentBound := by
  intro ι _ _ ρ m κ A O d Ψ₀ Ψ₁ K₀ K₁ p hρ hm hκ hp hd H₀ H₁ hA₀ hA₁ Z F B hF hFZ hFO hB
  set G : BondField ι → ℝ := fun ζ => Ψ₁ ζ - Ψ₀ ζ with hG
  have cG : ContDiff ℝ 3 G := H₁.smooth.sub H₀.smooth
  have c₀ : Continuous Ψ₀ := H₀.smooth.continuous
  obtain ⟨MA, hMA⟩ := exists_abs_le_on_ballProduct hρ c₀
  obtain ⟨MG, hMG⟩ := exists_abs_le_on_ballProduct hρ cG.continuous
  have := isFiniteMeasure_radialLaw (ι := ι) hρ hp
  have := radialLaw_neZero (ι := ι) hρ hp
  set c := 4 * ρ * (1 + A) * O * ∑ b ∈ Z, ∑ b', B b' * Real.exp (-(κ * d b b')) with hc
  have hFb : ∀ᵐ η ∂(radialLaw ι ρ p), |F η| ≤ |F 0| + O := by
    filter_upwards [ae_mem_ballProduct] with η hη
    have := hFO η 0 hη (zero_mem_ballProduct hρ)
    have h2 := abs_sub_abs_le_abs_sub (F η) (F 0)
    linarith
  have key := abs_tiltedMean_sub_le (μ := radialLaw ι ρ p) (A := Ψ₀) (G := G) (F := F) (M := max MA MG)
    (c := c) hF hFb
    c₀.measurable cG.continuous.measurable
    (by
      filter_upwards [ae_mem_ballProduct] with η hη
      exact (hMA η hη).trans (le_max_left _ _))
    (by
      filter_upwards [ae_mem_ballProduct] with η hη
      exact (hMG η hη).trans (le_max_right _ _))
    (by
      intro v hv
      rw [tiltedMean_radialLaw_eq_ballExpectation hp, tiltedMean_radialLaw_eq_ballExpectation hp,
        tiltedMean_radialLaw_eq_ballExpectation hp]
      have hmix := isUniformlyConvexDecaying_convexComb hv.1 hv.2 H₀ H₁
      have hfun : (fun ζ => (1 - v) * Ψ₀ ζ + v * Ψ₁ ζ) = fun η => Ψ₀ η + v * G η := by
        funext ζ
        simp only [hG]
        ring
      rw [hfun] at hmix
      have hrow : ∀ b, ∑ b' ∈ Finset.univ.erase b,
          ((1 - v) * K₀ b b' + v * K₁ b b') * Real.exp (κ * d b b') ≤ A * m := by
        intro b
        have e : ∑ b' ∈ Finset.univ.erase b, ((1 - v) * K₀ b b' + v * K₁ b b') * Real.exp (κ * d b b') =
            (1 - v) * ∑ b' ∈ Finset.univ.erase b, K₀ b b' * Real.exp (κ * d b b') +
              v * ∑ b' ∈ Finset.univ.erase b, K₁ b b' * Real.exp (κ * d b b') := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]
        have hv' : 0 ≤ 1 - v := by linarith [hv.2]
        nlinarith [mul_le_mul_of_nonneg_left (hA₀ b) hv', mul_le_mul_of_nonneg_left (hA₁ b) hv.1]
      have := hcov ι ρ m κ A O d _ _ p hρ hm hκ hp hd hmix hrow Z F G B hF hFZ hFO
        (cG.of_le (by norm_num)) hB
      exact this)
  rw [tiltedMean_radialLaw_eq_ballExpectation hp, tiltedMean_radialLaw_eq_ballExpectation hp] at key
  have e1 : (fun η => Ψ₀ η + (1 : ℝ) * G η) = Ψ₁ := by
    funext η
    simp [hG]
  have e0 : (fun η => Ψ₀ η + (0 : ℝ) * G η) = Ψ₀ := by
    funext η
    simp
  rw [e1, e0] at key
  exact key
end ConvexLawSegment
theorem convexLawSegmentBound_holds (hcov : ConvexMeasures.covarianceLocalMeasurableBound) :
    ConvexLawSegmentBound := ConvexLawSegment.convexLawSegmentBound_of_covariance hcov
end YangMills.Construction.ClusterExpansionOfAStep
end
