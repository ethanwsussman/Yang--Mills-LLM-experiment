import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.OrbitUnderThePlainAverage
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanOrbit
open Matrices Tower
theorem matExp_inv_eq_matExp_neg (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem hasDerivAt_matExp_I_smul (A : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • A)))
      (Complex.I • A) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
theorem matExp_I_smul_zero (A : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • A)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_line_zero <;> assumption
abbrev expGaugeCurve {ι : Type*} (ξ : ι → ComplexMatrix2) (t : ℝ) : ι → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-ξ x)))
theorem expGaugeCurve_inv {ι : Type*} (ξ : ι → ComplexMatrix2) (t : ℝ) (x : ι) :
    (expGaugeCurve ξ t x)⁻¹ = ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • ξ x)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.gaugeExpCurve_inv <;> assumption
theorem det_expGaugeCurve {ι : Type*} (ξ : ι → ComplexMatrix2)
    (hξ : ∀ x, ComplexMatrix2.fullTrace (ξ x) = 0) (t : ℝ) (x : ι) :
    Matrix.det (expGaugeCurve ξ t x) = 1 := by
  have htr : ComplexMatrix2.fullTrace (Complex.I • ((t : ℂ) • (-ξ x))) = 0 := by
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_neg]
    have hx := hξ x
    simp only [ComplexMatrix2.fullTrace] at hx
    simp [hx]
  exact SpinHarmonics.det_matExp_of_trace_eq_zero htr
section Orbit
variable {L n k j : ℕ}
def orbitVelocity (V : Edge L n k j → ComplexMatrix2) (ξ : Vertex L n k j → ComplexMatrix2)
    (b : Edge L n k j) : ComplexMatrix2 :=
  Complex.I • (V b * ξ b.target) - Complex.I • (ξ b.source * V b)
theorem hasDerivAt_gaugeTransform_expGaugeCurve (V : Edge L n k j → ComplexMatrix2)
    (ξ : Vertex L n k j → ComplexMatrix2) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.gaugeTransform (expGaugeCurve ξ t) V b)
      (orbitVelocity V ξ b) 0 := by
  have h1 := hasDerivAt_matExp_I_smul (-ξ b.source)
  have h2 := hasDerivAt_matExp_I_smul (ξ b.target)
  have h3 := (h1.mul_const (V b)).mul h2
  have hfun : (fun t : ℝ => PeriodicLattice.gaugeTransform (expGaugeCurve ξ t) V b) =
      fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-ξ b.source))) * V b *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • ξ b.target)) := by
    funext t
    simp only [PeriodicLattice.gaugeTransform, expGaugeCurve_inv]
  rw [hfun]
  refine HasDerivAt.congr_deriv h3 ?_
  rw [matExp_I_smul_zero, matExp_I_smul_zero, orbitVelocity]
  simp only [mul_one, one_mul, smul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  abel
theorem inv_mul_self_of_det_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul g (by rw [h]; exact isUnit_one)
theorem mul_inv_self_of_det_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (by rw [h]; exact isUnit_one)
theorem hasDerivAt_expTwist_covDiff (V : Edge L n k j → ComplexMatrix2)
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (ξ : Vertex L n k j → ComplexMatrix2) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • covDiff V ξ) V b)
      (orbitVelocity V ξ b) 0 := by
  have hdet : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hopp : ∀ b, V b.opposite = (V b)⁻¹ := fun b => hV.2 b (Set.mem_univ b)
  by_cases hb : b.IsPositivelyOriented
  · have hfun : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • covDiff V ξ) V b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • covDiff V ξ b)) * V b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [hfun]
    refine HasDerivAt.congr_deriv ((hasDerivAt_matExp_I_smul _).mul_const (V b)) ?_
    have hcov : covDiff V ξ b = ComplexMatrix2.conjugateBy (V b) (ξ b.target) - ξ b.source := by
      simp only [covDiff, extendOddly, if_pos hb]
    rw [hcov, orbitVelocity, ComplexMatrix2.conjugateBy]
    simp only [Matrix.smul_mul, smul_sub, sub_mul]
    have hcancel : V b * ξ b.target * (V b)⁻¹ * V b = V b * ξ b.target := by
      rw [mul_assoc, inv_mul_self_of_det_eq_one (hdet b), mul_one]
    rw [hcancel]
  · have hpos : b.opposite.IsPositivelyOriented := by
      obtain ⟨μ, h | h⟩ := b.isNeighbour
      · exact absurd ⟨μ, h⟩ hb
      · exact ⟨μ, by change b.source - b.target = _; rw [← neg_sub, h, neg_neg]⟩
    have hinvinv : (V b.opposite)⁻¹ = V b := by
      rw [hopp]
      exact Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet b]; exact isUnit_one)
    have hfun : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • covDiff V ξ) V b) =
        fun t : ℝ => V b *
          ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-covDiff V ξ b.opposite))) := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, Matrix.mul_inv_rev, hinvinv,
        matExp_inv_eq_matExp_neg]
      congr 2
      simp
    rw [hfun]
    refine HasDerivAt.congr_deriv ((hasDerivAt_matExp_I_smul _).const_mul (V b)) ?_
    have hcov : covDiff V ξ b.opposite =
        ComplexMatrix2.conjugateBy (V b.opposite) (ξ b.source) - ξ b.target := by
      simp only [covDiff, extendOddly, if_pos hpos]
      rfl
    have hcancel : V b * (V b.opposite * ξ b.source * (V b.opposite)⁻¹) = ξ b.source * V b := by
      rw [hinvinv, hopp, ← mul_assoc, ← mul_assoc, mul_inv_self_of_det_eq_one (hdet b), one_mul]
    rw [hcov, orbitVelocity, ComplexMatrix2.conjugateBy]
    simp only [neg_sub, smul_sub, Matrix.mul_sub, Matrix.mul_smul, hcancel]
theorem contourMeanGaugeOrbit_holds (hN : NormalizedMeanNearOne) (hC : ContourMeanGaugeCovariant)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex) :
    ContourMeanGaugeOrbit := by
  intro L hL
  obtain ⟨ρ, hρ, H⟩ := hN L hL
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj V hV hVρ ξ hξ c hc
  obtain ⟨-, -, -, hu, D, hD⟩ := H n k j hn hj V hV hVρ c hc
  have hu' : Matrix.det (normalizedMean V c) = 1 := hu
  set u := normalizedMean V c with hudef
  set y := c.source.toSublattice (PeriodicLattice.levelDepth k j) with hy
  set y' := c.target.toSublattice (PeriodicLattice.levelDepth k j) with hy'
  have hinv1 : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  have hgauge0 : (fun t : ℝ => PeriodicLattice.gaugeTransform (expGaugeCurve ξ t) V) 0 = V := by
    funext b
    simp only [PeriodicLattice.gaugeTransform, expGaugeCurve, matExp_I_smul_zero, hinv1, one_mul,
      mul_one]
  have htwist0 : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • covDiff V ξ) V) 0 = V := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply, matExp_I_smul_zero, one_mul]
    · have hdet : Matrix.det (V b) = 1 := hV.1 b (Set.mem_univ b)
      have hopp : V b.opposite = (V b)⁻¹ := hV.2 b (Set.mem_univ b)
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, matExp_I_smul_zero, one_mul,
        hopp]
      exact Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
  have hDgauge := hD (orbitVelocity V ξ) _ hgauge0 (_root_.YangMills.Construction.RunningCouplingSlope.MeanOrbit.hasDerivAt_gaugeTransform_expGaugeCurve V ξ)
  have hDtwist := hD (orbitVelocity V ξ) _ htwist0 (hasDerivAt_expTwist_covDiff V hV ξ)
  have hcov : ∀ t : ℝ, normalizedMean (PeriodicLattice.gaugeTransform (expGaugeCurve ξ t) V) c =
      expGaugeCurve ξ t y * u * ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • ξ y')) := by
    intro t
    have hcovt := (hC L hL n k j hn hj V hV (expGaugeCurve ξ t)
      (det_expGaugeCurve ξ hξ t) c hc).2.2
    rw [hcovt, expGaugeCurve_inv]
  have hexp : HasDerivAt (fun t : ℝ => expGaugeCurve ξ t y * u *
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • ξ y')))
      ((Complex.I • (-ξ y)) * u + u * (Complex.I • ξ y')) 0 := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_matExp_I_smul (-ξ y)).mul_const u).mul
      (hasDerivAt_matExp_I_smul (ξ y'))) ?_
    rw [matExp_I_smul_zero, matExp_I_smul_zero]
    simp
  have hDval : D (orbitVelocity V ξ) = (Complex.I • (-ξ y)) * u + u * (Complex.I • ξ y') := by
    have hfun : (fun t : ℝ => normalizedMean (PeriodicLattice.gaugeTransform (expGaugeCurve ξ t) V) c) =
        fun t : ℝ => expGaugeCurve ξ t y * u * ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • ξ y')) := by
      funext t
      exact hcov t
    rw [hfun] at hDgauge
    exact hDgauge.unique hexp
  have hX : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
      ((t : ℂ) • covDiff V ξ) V) c * u⁻¹) (D (orbitVelocity V ξ) * u⁻¹) 0 :=
    hDtwist.mul_const _
  have hX0 : (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
      ((t : ℂ) • covDiff V ξ) V) c * u⁻¹) 0 = 1 := by
    have hat0 : normalizedMean ((fun t : ℝ => PeriodicLattice.expTwist
        ((t : ℂ) • covDiff V ξ) V) 0) c = u := by rw [htwist0]
    simp only at hat0 ⊢
    rw [hat0, mul_inv_self_of_det_eq_one hu']
  have hlog := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.2.1
  have hdiff : leftDifferential normalizedMean V (covDiff V ξ) c = Complex.I⁻¹ •
      deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • covDiff V ξ) V) c * u⁻¹)) 0 := by
    unfold leftDifferential extendOddly
    rw [if_pos hc]
    rfl
  have hcovmean : covDiff (normalizedMean V) (restrictVertexFunction (j + 1) ξ) c =
      ComplexMatrix2.conjugateBy u (ξ y') - ξ y := by
    simp only [covDiff, extendOddly, if_pos hc]
    rfl
  rw [hdiff, hcovmean, hlog.deriv, hDval, ComplexMatrix2.conjugateBy]
  simp only [add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, neg_mul, smul_neg,
    inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  rw [mul_assoc (ξ y), mul_inv_self_of_det_eq_one hu', mul_one]
  abel
end Orbit
end YangMills.Construction.RunningCouplingSlope.MeanOrbit
end
