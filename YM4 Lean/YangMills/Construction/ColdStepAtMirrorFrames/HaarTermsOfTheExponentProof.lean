import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import YangMills.Construction.ColdStepAtMirrorFrames.HaarTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativesOfSums
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessSum
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem stepCoordinates_chordBond (η : StepVariable (finiteCells F)) (b : ChordBond F) :
    stepCoordinates η b.1.1 b.1.2 = toImaginaryCLM (η b) := by
  classical
  unfold stepCoordinates
  rw [dif_pos b.2]
  rfl
def bondHaarTerm (v : imaginaryQuaternions) (b : ChordBond F) (η : StepVariable (finiteCells F)) : ℝ :=
  haarLogRatio (v + toImaginaryCLM (η b))
abbrev bondProjection (b : ChordBond F) : StepVariable (finiteCells F) →L[ℝ] imaginaryQuaternions :=
  toImaginaryCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) b)
theorem fderiv_comp_bond {f : imaginaryQuaternions → ℝ} {v : imaginaryQuaternions} {b : ChordBond F}
    {ζ : StepVariable (finiteCells F)}
    (hd : DifferentiableAt ℝ f (v + toImaginaryCLM (ζ b))) (u : StepVariable (finiteCells F)) :
    fderiv ℝ (fun η : StepVariable (finiteCells F) => f (v + toImaginaryCLM (η b))) ζ u =
      fderiv ℝ f (v + toImaginaryCLM (ζ b)) (toImaginaryCLM (u b)) := by
  have h1 : HasFDerivAt (fun η : StepVariable (finiteCells F) => v + toImaginaryCLM (η b))
      (bondProjection b) ζ :=
    ((bondProjection b).hasFDerivAt).const_add v
  have h2 := hd.hasFDerivAt.comp ζ h1
  have h3 : HasFDerivAt (fun η : StepVariable (finiteCells F) => f (v + toImaginaryCLM (η b))) _ ζ := h2
  rw [h3.fderiv]
  rfl
theorem haarExcessSumDiagonalBounds (hH : HaarLogRatioNearZero) (hSum : Calculus.FderivFinsetSum) :
    HaarExcessSumDiagonalBounds := by
  classical
  obtain ⟨C, hC, hH⟩ := hH
  refine ⟨C, hC, ?_⟩
  intro F w hw
  have hwb : ∀ b : ChordBond F, ‖w b.1.1 b.1.2‖ ≤ 1 := fun b => hw b.1 b.2
  have hread : haarExcessSum w = fun ζ => ∑ b : ChordBond F, bondHaarTerm (w b.1.1 b.1.2) b ζ := by
    funext ζ
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [stepCoordinates_chordBond]
    rfl
  have hterm : ∀ b : ChordBond F, ContDiffAt ℝ 3 (bondHaarTerm (w b.1.1 b.1.2) b)
      (0 : StepVariable (finiteCells F)) := by
    intro b
    have h1 : ContDiffAt ℝ 3 haarLogRatio
        (w b.1.1 b.1.2 + toImaginaryCLM ((0 : StepVariable (finiteCells F)) b)) := by
      simpa using (hH _ (hwb b)).1
    have h2 : ContDiffAt ℝ 3
        (fun η : StepVariable (finiteCells F) => w b.1.1 b.1.2 + toImaginaryCLM (η b)) 0 :=
      (contDiff_const.add (bondProjection b).contDiff).contDiffAt
    exact ContDiffAt.comp (0 : StepVariable (finiteCells F)) h1 h2
  have hsum := hSum (StepVariable (finiteCells F)) (ChordBond F) Finset.univ
    (fun b => bondHaarTerm (w b.1.1 b.1.2) b) 0 (fun b _ => hterm b)
  rw [hread]
  refine ⟨hsum.1, fun b b' e e' => ?_⟩
  obtain ⟨hf1, hf2⟩ := hsum.2 (bondVariation b e) (bondVariation b' e')
  have hne := norm_nonneg e
  have hne' := norm_nonneg e'
  have hdiff : ∀ d : ChordBond F, DifferentiableAt ℝ haarLogRatio
      (w d.1.1 d.1.2 + toImaginaryCLM ((0 : StepVariable (finiteCells F)) d)) := fun d => by
    simpa using (hH _ (hwb d)).1.differentiableAt (by norm_num)
  have hfirst : ∀ d : ChordBond F, fderiv ℝ (bondHaarTerm (w d.1.1 d.1.2) d) 0 (bondVariation b e) =
      fderiv ℝ haarLogRatio (w d.1.1 d.1.2)
        (toImaginaryCLM ((bondVariation b e : StepVariable (finiteCells F)) d)) := by
    intro d
    have := fderiv_comp_bond (hdiff d) (bondVariation b e)
    simp only [Pi.zero_apply, map_zero, add_zero] at this
    exact this
  have hsecond : ∀ d : ChordBond F,
      fderiv ℝ (fun ζ => fderiv ℝ (bondHaarTerm (w d.1.1 d.1.2) d) ζ (bondVariation b e)) 0
        (bondVariation b' e') = fderiv ℝ (fun z => fderiv ℝ haarLogRatio z
          (toImaginaryCLM ((bondVariation b e : StepVariable (finiteCells F)) d))) (w d.1.1 d.1.2)
            (toImaginaryCLM ((bondVariation b' e' : StepVariable (finiteCells F)) d)) := by
    intro d
    have hc3 : ContDiffAt ℝ 3 haarLogRatio (w d.1.1 d.1.2) := (hH _ (hwb d)).1
    have hcont : ContinuousAt
        (fun ζ : StepVariable (finiteCells F) => w d.1.1 d.1.2 + toImaginaryCLM (ζ d)) 0 :=
      (continuous_const.add ((bondProjection d).continuous)).continuousAt
    have hnear : ∀ᶠ ζ in 𝓝 (0 : StepVariable (finiteCells F)),
        DifferentiableAt ℝ haarLogRatio (w d.1.1 d.1.2 + toImaginaryCLM (ζ d)) := by
      have h0 : ∀ᶠ z in 𝓝 (w d.1.1 d.1.2 + toImaginaryCLM ((0 : StepVariable (finiteCells F)) d)),
          DifferentiableAt ℝ haarLogRatio z := by
        have : ∀ᶠ z in 𝓝 (w d.1.1 d.1.2), ContDiffAt ℝ 3 haarLogRatio z := hc3.eventually (by simp)
        simp only [Pi.zero_apply, map_zero, add_zero]
        filter_upwards [this] with z hz using hz.differentiableAt (by norm_num)
      exact hcont.eventually h0
    have he : (fun ζ => fderiv ℝ (bondHaarTerm (w d.1.1 d.1.2) d) ζ (bondVariation b e)) =ᶠ[𝓝 0]
        fun ζ => fderiv ℝ haarLogRatio (w d.1.1 d.1.2 + toImaginaryCLM (ζ d))
          (toImaginaryCLM ((bondVariation b e : StepVariable (finiteCells F)) d)) := by
      filter_upwards [hnear] with ζ hζ using fderiv_comp_bond hζ _
    rw [he.fderiv_eq]
    have h2c : ContDiffAt ℝ 2 (fderiv ℝ haarLogRatio) (w d.1.1 d.1.2) := hc3.fderiv_right (by norm_num)
    have hdg : DifferentiableAt ℝ (fun z => fderiv ℝ haarLogRatio z
        (toImaginaryCLM ((bondVariation b e : StepVariable (finiteCells F)) d)))
        (w d.1.1 d.1.2 + toImaginaryCLM ((0 : StepVariable (finiteCells F)) d)) := by
      simpa using (h2c.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
    have := fderiv_comp_bond hdg (bondVariation b' e')
    simp only [Pi.zero_apply, map_zero, add_zero] at this
    exact this
  constructor
  · rw [hf1, Finset.sum_eq_single b]
    · rw [hfirst]
      have : (bondVariation b e : StepVariable (finiteCells F)) b = e := by simp [bondVariation]
      rw [this]
      have h1 := (hH _ (hwb b)).2.1 (toImaginaryCLM e)
      rwa [norm_toImaginaryCLM] at h1
    · intro d _ hd
      rw [hfirst]
      have : (bondVariation b e : StepVariable (finiteCells F)) d = 0 := Pi.single_eq_of_ne hd _
      simp [this]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [hf2]
    have hzero : ∀ d : ChordBond F, d ≠ b →
        fderiv ℝ (fun ζ => fderiv ℝ (bondHaarTerm (w d.1.1 d.1.2) d) ζ (bondVariation b e)) 0
          (bondVariation b' e') = 0 := by
      intro d hd
      rw [hsecond]
      have : (bondVariation b e : StepVariable (finiteCells F)) d = 0 := Pi.single_eq_of_ne hd _
      simp [this]
    rw [Finset.sum_eq_single b (fun d _ hd => hzero d hd) (fun hb => absurd (Finset.mem_univ b) hb),
      hsecond]
    have hb0 : (bondVariation b e : StepVariable (finiteCells F)) b = e := by simp [bondVariation]
    rw [hb0]
    by_cases hbb : b = b'
    · subst hbb
      have hb1 : (bondVariation b e' : StepVariable (finiteCells F)) b = e' := by simp [bondVariation]
      rw [hb1, if_pos rfl]
      have h1 := (hH _ (hwb b)).2.2 (toImaginaryCLM e) (toImaginaryCLM e')
      rwa [norm_toImaginaryCLM, norm_toImaginaryCLM] at h1
    · have hb1 : (bondVariation b' e' : StepVariable (finiteCells F)) b = 0 := Pi.single_eq_of_ne hbb _
      rw [hb1, if_neg hbb]
      simp
end YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessSum
end
