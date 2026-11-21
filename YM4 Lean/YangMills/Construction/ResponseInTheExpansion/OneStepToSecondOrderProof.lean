import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import YangMills.Construction.ResponseInTheExpansion.StepNearItsHessian
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames LinearResponse
namespace ResponseInTheExpansion.SecondOrderStep
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem deriv_deriv_smul_add_eq_fderiv_fderiv {E : P → ℝ} (hE : ContDiffAt ℝ 3 E 0) (u v : P) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => E (s • u + s' • v)) 0) 0 =
      fderiv ℝ (fun ζ => fderiv ℝ E ζ v) 0 u := by
  have hline : ∀ τ : ℝ, HasDerivAt (fun s : ℝ => s • u) u τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const u
  have hcont : ContinuousAt (fun s : ℝ => s • u) 0 := (hline 0).continuousAt
  have hzero : (fun s : ℝ => s • u) 0 = 0 := by simp
  have hnear : ∀ᶠ τ in 𝓝 (0 : ℝ), ContDiffAt ℝ 3 E (τ • u) := by
    have hpt : ∀ᶠ ζ in 𝓝 ((fun s : ℝ => s • u) 0), ContDiffAt ℝ 3 E ζ := by
      rw [hzero]
      exact hE.eventually (by simp)
    exact hcont.eventually hpt
  have hinner : (fun s : ℝ => deriv (fun s' : ℝ => E (s • u + s' • v)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ E (s • u) v := by
    filter_upwards [hnear] with s hs
    have hf : HasFDerivAt E (fderiv ℝ E (s • u)) (s • u + (0 : ℝ) • v) := by
      simpa using (hs.differentiableAt (by norm_num)).hasFDerivAt
    have hg : HasDerivAt (fun s' : ℝ => s • u + s' • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (s • u)
    exact (hf.comp_hasDerivAt (0 : ℝ) hg).deriv
  rw [hinner.deriv_eq]
  have hsecond : ContDiffAt ℝ 2 (fderiv ℝ E) 0 := hE.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fun ζ => fderiv ℝ E ζ v) 0 :=
    (hsecond.differentiableAt (by norm_num)).clm_apply (differentiableAt_const v)
  have hdiff' : DifferentiableAt ℝ (fun ζ => fderiv ℝ E ζ v) ((fun s : ℝ => s • u) 0) := by
    rw [hzero]
    exact hdiff
  have hcomp := hdiff'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
  have hderiv := hcomp.deriv
  simpa [Function.comp_def, hzero] using hderiv
end Calculus
variable {F : BlockFrame}
theorem twoCoordinateVariation_eq (p q : ChartCoordinate F) (s s' : ℝ) :
    twoCoordinateVariation p q s s' = s • bondCoordinateVector p + s' • bondCoordinateVector q := by
  classical
  funext b
  ext i
  have hunit : ∀ r : ChartCoordinate F, ((bondCoordinateVector r : StepVariable (finiteCells F)) b) i =
      if (b, i) = r then 1 else 0 := by
    intro r
    unfold bondCoordinateVector ColdStepAtMirrorFrames.bondVariation
    by_cases hb : b = r.1
    · subst hb
      by_cases hi : i = r.2
      · simp [hi]
      · simp [hi, Prod.ext_iff]
    · simp [Prod.ext_iff, hb]
  simp [twoCoordinateVariation, hunit]
theorem frameHessian_apply_eq {a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hE : ContDiffAt ℝ 3 (chartedEnergyAt a (frameCoordField false a ρA m V) V) 0) (p q : ChartCoordinate F) :
    frameHessian a ρA m V p q =
      bondCoordinateHessian (chartedEnergyAt a (frameCoordField false a ρA m V) V) q p := by
  have hmixed := deriv_deriv_smul_add_eq_fderiv_fderiv hE (bondCoordinateVector p) (bondCoordinateVector q)
  have hfun : (fun s : ℝ => deriv (fun s' : ℝ => chartedEnergy a
      (coordsAboveFrame false a ρA m V (twoCoordinateVariation p q s s')) V) 0) =
      fun s : ℝ => deriv (fun s' : ℝ => chartedEnergyAt a (frameCoordField false a ρA m V) V
        (s • bondCoordinateVector p + s' • bondCoordinateVector q)) 0 := by
    funext s
    congr 1
    funext s'
    rw [twoCoordinateVariation_eq]
    rfl
  unfold frameHessian
  rw [hfun, hmixed]
  rfl
theorem gaussianMomentApprox (hT : StepNearHessian) (hLN : GaussianMomentsNearHessian)
    (hJ : EventuallyInParametersCombines) : gaussianMomentApproxStatement := by
  refine hJ.2 _ _ ?_ hT
  rintro T hT' ⟨Dc, W, K₀, Ci, S, hDc, hW, hK₀, hCi, hS, hall⟩
  intro q
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    have := hT'.σ_pos
    positivity
  have hlam : 0 < T.chainParams.lam := hT'.chain_admissible.positivity.2.2.1
  obtain ⟨C, hC0, hC⟩ := hLN T.ballRadius T.p T.chainParams.lam Dc W K₀ Ci S hρ hT'.cutoff hlam hDc hW hK₀ hCi hS q
  refine ⟨C, ?_⟩
  intro t x f F V hx hrow hF hV l
  obtain ⟨hx1, hE, hN⟩ := hall t x f F V hx hrow hF hV
  have hH : frameHessian T.a T.chainParams.ρA (frameRadius x) V =
      bondCoordinateHessian (chartedEnergyAt T.a (frameCoordField false T.a T.chainParams.ρA (frameRadius x) V) V) := by
    ext p r
    rw [frameHessian_apply_eq hE]
    exact hN.isSymm.apply p r
  have hmain := hC _ x T.κ (chordBondDist F) _ _ _ hx1 hT'.κ_pos.le hN l
  rw [hH]
  exact hmain
end ResponseInTheExpansion.SecondOrderStep
end YangMills.Construction
end
