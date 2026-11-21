import YangMills.Construction.Continuum.FactsOfConfigurationSpaceAndItsTestFunctionsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.ModulusOfARotationInTheSharpNorm
import YangMills.Construction.Continuum.RulesOfTheOrthogonalActionProof
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import Mathlib
set_option autoImplicit false
open Filter Topology Matrix
noncomputable section
namespace YangMills.Construction
open Orthogonal SeparatedTuples
namespace OrthogonalAction
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
namespace SharpNormRotation
theorem euclidNormVec_nonneg (v : AmbientSpace) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_neg (v : AmbientSpace) : euclidNormVec (-v) = euclidNormVec v := by
  simp [euclidNormVec]
theorem euclidNormVec_eq_euclidean_norm (v : AmbientSpace) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_add_le (v w : AmbientSpace) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem sup_norm_le_euclidNormVec (v : AmbientSpace) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_sup_norm (v : AmbientSpace) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem abs_inner_le_euclidNormVec_mul (v w : AmbientSpace) :
    |∑ μ, v μ * w μ| ≤ euclidNormVec v * euclidNormVec w := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.abs_sum_mul_le_euclid <;> assumption
theorem matrixOperatorNorm_nonneg (A : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ matrixOperatorNorm A :=
  norm_nonneg _
theorem euclidNormVec_mulVec_le (A : Matrix (Fin 4) (Fin 4) ℝ) (v : AmbientSpace) :
    euclidNormVec (A *ᵥ v) ≤ matrixOperatorNorm A * euclidNormVec v := by
  have hop := (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) A).le_opNorm (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp] at hop
  rw [euclidNormVec_eq_euclidean_norm, euclidNormVec_eq_euclidean_norm]
  exact hop
theorem mulVec_inv_mulVec (Q : orthogonalGroupFour) (x : AmbientSpace) :
    Q.1 *ᵥ ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x) = x := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.matMap_matMap_inv <;> assumption
theorem euclidNormVec_orthogonal_mulVec (Q : orthogonalGroupFour) (x : AmbientSpace) :
    euclidNormVec (Q.1 *ᵥ x) = euclidNormVec x := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.euclidNormVec_matMap <;> assumption
theorem euclidNormVec_sub_inv_mulVec_le (Q : orthogonalGroupFour) (x : AmbientSpace) :
    euclidNormVec (x - (Q⁻¹ : orthogonalGroupFour).1 *ᵥ x) ≤
      matrixOperatorNorm (Q.1 - 1) * euclidNormVec x := by
  have hx : x - (Q⁻¹ : orthogonalGroupFour).1 *ᵥ x =
      (Q.1 - 1) *ᵥ ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, mulVec_inv_mulVec]
  rw [hx]
  calc _ ≤ matrixOperatorNorm (Q.1 - 1) * euclidNormVec ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x) :=
        euclidNormVec_mulVec_le _ _
    _ = _ := by rw [euclidNormVec_orthogonal_mulVec]
theorem partialDerivR4_eq_fderiv {u : RealValued} (hu : Differentiable ℝ u) (μ : Fin 4)
    (x : AmbientSpace) :
    TestFunctions.partialDerivR4 μ u x = fderiv ℝ u x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.partialDerivR4_eq_fderiv <;> assumption
theorem gradR4_eq_fderiv {u : RealValued} (hu : Differentiable ℝ u) :
    gradR4 u = fun x μ => fderiv ℝ u x (Pi.single μ (1 : ℝ)) := by
  funext x μ
  exact partialDerivR4_eq_fderiv hu μ x
theorem fderiv_apply_eq_sum_gradR4 {u : RealValued} (hu : Differentiable ℝ u) (x v : AmbientSpace) :
    fderiv ℝ u x v = ∑ μ, v μ * gradR4 u x μ := by apply _root_.YangMills.Construction.ConfigurationSpace.Facts.fderiv_apply_eq_sum_partial <;> assumption
theorem abs_sub_le_of_gradR4_le {u : RealValued} (hu : Differentiable ℝ u) {B : ℝ}
    (hB : ∀ z, euclidNormVec (gradR4 u z) ≤ B) (x y : AmbientSpace) :
    |u x - u y| ≤ B * euclidNormVec (x - y) := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
  have hcomp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u (y + t • (x - y)))
      (fderiv ℝ u (y + t • (x - y)) (x - y)) t := fun t => by
    have hp : HasFDerivAt u (fderiv ℝ u (y + t • (x - y)))
        ((fun t : ℝ => y + t • (x - y)) t) := (hu _).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt t hp (hline t)
  have hbd : ∀ t : ℝ, ‖fderiv ℝ u (y + t • (x - y)) (x - y)‖ ≤ B * euclidNormVec (x - y) :=
    fun t => by
      rw [Real.norm_eq_abs, fderiv_apply_eq_sum_gradR4 hu]
      calc _ ≤ euclidNormVec (x - y) * euclidNormVec (gradR4 u (y + t • (x - y))) :=
            abs_inner_le_euclidNormVec_mul _ _
        _ ≤ euclidNormVec (x - y) * B :=
            mul_le_mul_of_nonneg_left (hB _) (euclidNormVec_nonneg _)
        _ = _ := mul_comm _ _
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => u (y + t • (x - y))) (s := Set.univ) (x := 0) (y := 1)
    (fun t _ => (hcomp t).hasDerivWithinAt) (fun t _ => hbd t) convex_univ trivial trivial
  simpa using hmv
theorem continuous_gradR4 {f : RealValued} (hf : ContDiff ℝ 1 f) :
    Continuous (gradR4 f) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.continuous_gradR4 <;> assumption
theorem hasCompactSupport_gradR4 {f : RealValued} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : HasCompactSupport (gradR4 f) := by
  rw [gradR4_eq_fderiv (hf.differentiable (by norm_num))]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left
    (g := fun (L : AmbientSpace →L[ℝ] ℝ) (μ : Fin 4) => L (Pi.single μ (1 : ℝ)))
    (by funext μ; simp)
theorem le_gradSup {f : RealValued} (hf : IsC1c f) (x : AmbientSpace) :
    euclidNormVec (gradR4 f x) ≤ gradSup f := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_gradR4 hf.1 hf.2).exists_bound_of_continuous
    (continuous_gradR4 hf.1)
  refine le_ciSup (f := fun x => euclidNormVec (gradR4 f x)) ⟨2 * C, ?_⟩ x
  rintro _ ⟨z, rfl⟩
  exact (euclidNormVec_le_two_mul_sup_norm _).trans (by linarith [hC z])
theorem le_gradOscillation {f : RealValued} (hf : IsC1c f) {δ : ℝ}
    {x y : AmbientSpace} (hxy : euclidNormVec (x - y) ≤ δ) :
    euclidNormVec (gradR4 f x - gradR4 f y) ≤ gradOscillation f δ := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_gradR4 hf.1 hf.2).exists_bound_of_continuous
    (continuous_gradR4 hf.1)
  refine le_csSup ⟨2 * (C + C), ?_⟩ ⟨x, y, hxy, rfl⟩
  rintro _ ⟨x', y', -, rfl⟩
  refine (euclidNormVec_le_two_mul_sup_norm _).trans ?_
  linarith [norm_sub_le (gradR4 f x') (gradR4 f y'), hC x', hC y']
theorem gradOscillation_nonneg (f : RealValued) (δ : ℝ) : 0 ≤ gradOscillation f δ :=
  Real.sSup_nonneg (by
    rintro _ ⟨x, y, -, rfl⟩
    exact euclidNormVec_nonneg _)
theorem tendsto_gradOscillation {α : Type*} {l : Filter α} {d : α → ℝ}
    (hd : Tendsto d l (𝓝 0)) {f : RealValued} (hf : IsC1c f) :
    Tendsto (fun a => gradOscillation f (d a)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuous_iff.1
    ((hasCompactSupport_gradR4 hf.1 hf.2).uniformContinuous_of_continuous
      (continuous_gradR4 hf.1)) (ε / 4) (by positivity)
  filter_upwards [hd.eventually_lt_const hη] with a ha
  have hle : gradOscillation f (d a) ≤ ε / 2 := by
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨x, y, hxy, rfl⟩
    have hdist : dist x y < η := by
      rw [dist_eq_norm]
      exact (sup_norm_le_euclidNormVec _).trans_lt (hxy.trans_lt ha)
    have hclose := hU hdist
    rw [dist_eq_norm] at hclose
    linarith [euclidNormVec_le_two_mul_sup_norm (gradR4 f x - gradR4 f y)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gradOscillation_nonneg _ _)]
  linarith
theorem sharpNormR4_orthogonalAct_sub_le (hLaws : Laws.Statement) {M : ℝ} (hM : 1 ≤ M)
    {f : RealValued} (hf : IsC1c f) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport f ⊆ TestFunctions.closedBallR4 0 R) (Q : orthogonalGroupFour) :
    TestFunctions.sharpNormR4 M (orthogonalAct Q f - f) ≤
      rotationBound M R f (matrixOperatorNorm (Q.1 - 1)) := by
  have hc1 : ContDiff ℝ 1 f := hf.1
  have hfd : Differentiable ℝ f := hc1.differentiable (by norm_num)
  set s := matrixOperatorNorm (Q.1 - 1) with hs
  set g := orthogonalAct Q f with hg
  set y : AmbientSpace → AmbientSpace := fun x => (Q⁻¹ : orthogonalGroupFour).1 *ᵥ x with hyd
  have hs0 : 0 ≤ s := matrixOperatorNorm_nonneg _
  have hlaw := (hLaws.1 Q Q).1 f hf
  have hgc1 : ContDiff ℝ 1 g := hlaw.1.1
  have hgd : Differentiable ℝ g := hgc1.differentiable (by norm_num)
  have hzero : ∀ x, R < euclidNormVec x → f x = 0 ∧ gradR4 f x = 0 := by
    intro x hx
    have hn : x ∉ tsupport f := fun hmem => by
      have hin : euclidNormVec (x - 0) ≤ R := hsupp hmem
      rw [sub_zero] at hin
      exact absurd hin (not_le.2 hx)
    refine ⟨image_eq_zero_of_notMem_tsupport hn, ?_⟩
    funext μ
    change TestFunctions.partialDerivR4 μ f x = 0
    rw [partialDerivR4_eq_fderiv hfd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
    rfl
  have hy : ∀ x, euclidNormVec (y x) = euclidNormVec x := fun x =>
    euclidNormVec_orthogonal_mulVec Q⁻¹ x
  have hdisp : ∀ x, euclidNormVec x ≤ R → euclidNormVec (y x - x) ≤ s * R := fun x hx => by
    have hflip : y x - x = -(x - y x) := by abel
    rw [hflip, euclidNormVec_neg]
    exact (euclidNormVec_sub_inv_mulVec_le Q x).trans (mul_le_mul_of_nonneg_left hx hs0)
  have hsup : ∀ z, euclidNormVec (gradR4 f z) ≤ gradSup f := le_gradSup hf
  have hG0 : 0 ≤ gradSup f := (euclidNormVec_nonneg _).trans (hsup 0)
  have hw0 : 0 ≤ gradOscillation f (s * R) := gradOscillation_nonneg _ _
  have hgu : ∀ x, gradR4 (g - f) x =
      (Q.1 - 1) *ᵥ gradR4 f (y x) + (gradR4 f (y x) - gradR4 f x) := by
    intro x
    have hdiff : gradR4 (g - f) x = gradR4 g x - gradR4 f x := by
      funext μ
      change TestFunctions.partialDerivR4 μ (g - f) x =
        TestFunctions.partialDerivR4 μ g x - TestFunctions.partialDerivR4 μ f x
      rw [partialDerivR4_eq_fderiv (hgd.sub hfd), partialDerivR4_eq_fderiv hgd,
        partialDerivR4_eq_fderiv hfd, fderiv_sub (hgd x) (hfd x)]
      rfl
    rw [hdiff, hg, hlaw.2.2.2.2.2 x, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hgb : ∀ x, euclidNormVec (gradR4 (g - f) x) ≤
      s * gradSup f + gradOscillation f (s * R) := by
    intro x
    have hnn : 0 ≤ s * gradSup f + gradOscillation f (s * R) :=
      add_nonneg (mul_nonneg hs0 hG0) hw0
    rw [hgu]
    by_cases hx : euclidNormVec x ≤ R
    · calc _ ≤ euclidNormVec ((Q.1 - 1) *ᵥ gradR4 f (y x)) +
            euclidNormVec (gradR4 f (y x) - gradR4 f x) := euclidNormVec_add_le _ _
        _ ≤ s * euclidNormVec (gradR4 f (y x)) + gradOscillation f (s * R) :=
            add_le_add (euclidNormVec_mulVec_le _ _) (le_gradOscillation hf (hdisp x hx))
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left (hsup (y x)) hs0
            linarith
    · have hx' : R < euclidNormVec x := not_le.1 hx
      have hy' : R < euclidNormVec (y x) := by rwa [hy]
      rw [(hzero x hx').2, (hzero _ hy').2]
      simpa [euclidNormVec_zero] using hnn
  have hunif : TestFunctions.uniformNorm (g - f) ≤ gradSup f * s * R := by
    refine ciSup_le fun x => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    change |f (y x) - f x| ≤ _
    by_cases hx : euclidNormVec x ≤ R
    · calc _ ≤ gradSup f * euclidNormVec (y x - x) :=
            abs_sub_le_of_gradR4_le hfd hsup _ _
        _ ≤ gradSup f * (s * R) := mul_le_mul_of_nonneg_left (hdisp x hx) hG0
        _ = _ := by ring
    · have hx' : R < euclidNormVec x := not_le.1 hx
      have hy' : R < euclidNormVec (y x) := by rwa [hy]
      rw [(hzero x hx').1, (hzero _ hy').1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hG0 hs0) hR.le
  have hlip : TestFunctions.lipConstR4 (g - f) ≤
      s * gradSup f + gradOscillation f (s * R) := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    refine csInf_le ⟨0, fun C hC => hC.1⟩ ⟨add_nonneg (mul_nonneg hs0 hG0) hw0, fun x y' => ?_⟩
    exact (Real.norm_eq_abs _).le.trans (abs_sub_le_of_gradR4_le (hgd.sub hfd) hgb x y')
  change max (TestFunctions.uniformNorm (g - f)) (40 * M * TestFunctions.lipConstR4 (g - f)) ≤
    max (gradSup f * s * R)
      (40 * M * (s * gradSup f + gradOscillation f (s * R)))
  exact max_le_max hunif (mul_le_mul_of_nonneg_left hlip (by linarith))
theorem tendsto_rotationBound (M R : ℝ) {f : RealValued} (hf : IsC1c f) :
    Tendsto (fun Q : orthogonalGroupFour => rotationBound M R f (matrixOperatorNorm (Q.1 - 1)))
      (comap (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1)) (𝓝 0)) (𝓝 0) := by
  have hs : Tendsto (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1))
      (comap (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1)) (𝓝 0)) (𝓝 0) :=
    tendsto_comap
  have hsR : Tendsto (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1) * R)
      (comap (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1)) (𝓝 0)) (𝓝 0) := by
    simpa using hs.mul_const R
  have hA := (hs.const_mul (gradSup f)).mul_const R
  have hB := ((hs.mul_const (gradSup f)).add
    (tendsto_gradOscillation hsR hf)).const_mul (40 * M)
  have hmax := hA.max hB
  have hlim : max (gradSup f * 0 * R) (40 * M * (0 * gradSup f + 0)) = 0 := by
    simp
  rw [hlim] at hmax
  exact hmax
end SharpNormRotation
open SharpNormRotation in
theorem sharpNormRotationModulus_of_laws (hLaws : Laws.Statement) : SharpNormRotationModulus :=
  fun _ hM _ hf _ hR hsupp =>
    ⟨sharpNormR4_orthogonalAct_sub_le hLaws hM hf hR hsupp, tendsto_rotationBound _ _ hf⟩
end OrthogonalAction
end YangMills.Construction
