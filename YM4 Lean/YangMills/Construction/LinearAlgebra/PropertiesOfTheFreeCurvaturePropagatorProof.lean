import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagatorIsSymmetricEvenAndContinuous
import YangMills.Construction.LinearAlgebra.PropertiesOfTheFreeCurvaturePropagator
import YangMills.Construction.LinearAlgebra.ReflectionOnTwoVectors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrix TorusMetric PeriodicLattice Filter
open scoped ContDiff Topology
namespace Exterior
namespace PropagatorProperties
def propagatorEntry (P Q : AxisPlane) (y : Fin 4 → ℝ) : ℝ :=
  bivectorMatrixEntry (freeCurvaturePropagator y) P Q
theorem bivectorMatrixEntry_smul (c : ℝ) (T : Bivector →ₗ[ℝ] Bivector) (P Q : AxisPlane) :
    bivectorMatrixEntry (c • T) P Q = c * bivectorMatrixEntry T P Q := by
  simp only [bivectorMatrixEntry, LinearMap.smul_apply, inner_smul_right]
theorem bivectorTrace_smul (c : ℝ) (T : Bivector →ₗ[ℝ] Bivector) :
    bivectorTrace (c • T) = c * bivectorTrace T := by
  simp only [bivectorTrace, bivectorMatrixEntry_smul, Finset.mul_sum]
theorem bivectorTrace_id : bivectorTrace LinearMap.id = 6 := by
  have hdiag : ∀ P : AxisPlane, bivectorMatrixEntry LinearMap.id P P = 1 := by
    intro P
    have hn := axisBivectorBasis.orthonormal.1 P
    rw [axisBivectorBasis_apply] at hn
    simp only [bivectorMatrixEntry, LinearMap.id_apply]
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  simp only [bivectorTrace, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : Fintype.card AxisPlane = 6 := by
    rw [Fintype.card_congr axisPlaneEquivOrderedPairs]
    decide
  rw [hcard]
  norm_num
theorem sum_sq_ne_zero_of_ne_zero {x : Fin 4 → ℝ} (hx : x ≠ 0) : ∑ μ, x μ ^ 2 ≠ 0 := by
  intro hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => sq_nonneg (x μ)).1 hsum
  apply hx
  funext μ
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (hz μ (Finset.mem_univ μ))
theorem euclidNormVec_pos {x : Fin 4 → ℝ} (hx : x ≠ 0) : 0 < euclidNormVec x := by apply _root_.YangMills.Construction.TorusTransport.euclidNormVec_pos <;> assumption
theorem euclidNormVec_nonneg (x : Fin 4 → ℝ) : 0 ≤ euclidNormVec x := Real.sqrt_nonneg _
theorem euclidNormVec_sq (x : Fin 4 → ℝ) : euclidNormVec x ^ 2 = ∑ μ, x μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem euclidNormVec_smul (c : ℝ) (x : Fin 4 → ℝ) :
    euclidNormVec (c • x) = |c| * euclidNormVec x := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_normalize {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    euclidNormVec ((euclidNormVec x)⁻¹ • x) = 1 := by
  have hpos := euclidNormVec_pos hx
  rw [euclidNormVec_smul, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
theorem freeCurvaturePropagator_eq_smul_exteriorSq (x : Fin 4 → ℝ) :
    freeCurvaturePropagator x = (Real.pi ^ 2 * euclidNormVec x ^ 4)⁻¹ •
      exteriorSq (householder ((euclidNormVec x)⁻¹ • x)) := by
  rw [freeCurvaturePropagator, one_div]
theorem propagatorScale_pos {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    0 < Real.pi ^ 2 * euclidNormVec x ^ 4 :=
  mul_pos (pow_pos Real.pi_pos 2) (pow_pos (euclidNormVec_pos hx) 4)
theorem propagatorScale_smul_freeCurvaturePropagator {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    (Real.pi ^ 2 * euclidNormVec x ^ 4) • freeCurvaturePropagator x =
      exteriorSq (householder ((euclidNormVec x)⁻¹ • x)) := by
  rw [freeCurvaturePropagator_eq_smul_exteriorSq, smul_smul,
    mul_inv_cancel₀ (propagatorScale_pos hx).ne', one_smul]
theorem freeCurvaturePropagator_smul_of_pos {x : Fin 4 → ℝ} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    freeCurvaturePropagator (t • x) = (t ^ 4)⁻¹ • freeCurvaturePropagator x := by
  have hpos := (euclidNormVec_pos hx).ne'
  have hnorm : euclidNormVec (t • x) = t * euclidNormVec x := by
    rw [euclidNormVec_smul, abs_of_pos ht]
  have hdir : (euclidNormVec (t • x))⁻¹ • (t • x) = (euclidNormVec x)⁻¹ • x := by
    rw [hnorm, smul_smul]
    congr 1
    field_simp
  rw [freeCurvaturePropagator_eq_smul_exteriorSq, freeCurvaturePropagator_eq_smul_exteriorSq x,
    hdir, hnorm, smul_smul]
  congr 1
  field_simp
theorem householderMatrix_eq_householder (u : Fin 4 → ℝ) :
    householderMatrix u = householder (unitDirection u) := rfl
theorem unitDirection_eq_smul (u : Fin 4 → ℝ) :
    unitDirection u = (euclidNormVec u)⁻¹ • u := by
  funext μ
  simp [unitDirection, div_eq_inv_mul]
theorem continuumCurvatureKernel_eq_entry (hR : HouseholderOnBivectorsFacts) {u : Fin 4 → ℝ}
    (hu : u ≠ 0) (P Q : AxisPlane) :
    continuumCurvatureKernel P Q u = bivectorMatrixEntry (freeCurvaturePropagator u) P Q := by
  have hm := (hR _ (euclidNormVec_normalize hu)).2.2.2.2.2.1 P.lower P.upper Q.lower Q.upper
  have hm' : bivectorMatrixEntry (exteriorSq (householder ((euclidNormVec u)⁻¹ • u))) P Q = _ :=
    hm
  rw [freeCurvaturePropagator_eq_smul_exteriorSq, bivectorMatrixEntry_smul, hm',
    continuumCurvatureKernel, householderMatrix_eq_householder, unitDirection_eq_smul,
    div_eq_inv_mul]
theorem contDiff_sum_sq_coords : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => ∑ μ, x μ ^ 2) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_sumSq <;> assumption
theorem contDiffOn_householderMatrix (a b : Fin 4) :
    ContDiffOn ℝ ∞ (fun x : Fin 4 → ℝ => householderMatrix x a b) {x | x ≠ 0} := by
  simp only [householderMatrix_apply, euclidNormVec_sq]
  refine contDiffOn_const.sub (ContDiffOn.div ?_ contDiff_sum_sq_coords.contDiffOn
    fun _ hx => sum_sq_ne_zero_of_ne_zero hx)
  exact (contDiff_const.mul (contDiff_apply ℝ ℝ a)).mul (contDiff_apply ℝ ℝ b) |>.contDiffOn
theorem contDiffOn_continuumCurvatureKernel (P Q : AxisPlane) :
    ContDiffOn ℝ ∞ (continuumCurvatureKernel P Q) {x | x ≠ 0} := by
  have hfour : ∀ x : Fin 4 → ℝ, euclidNormVec x ^ 4 = (∑ μ, x μ ^ 2) ^ 2 := fun x => by
    rw [← euclidNormVec_sq]
    ring
  unfold continuumCurvatureKernel
  simp only [hfour]
  refine ContDiffOn.div ?_ ?_ fun x hx => ?_
  · exact ((contDiffOn_householderMatrix _ _).mul (contDiffOn_householderMatrix _ _)).sub
      ((contDiffOn_householderMatrix _ _).mul (contDiffOn_householderMatrix _ _))
  · exact (contDiff_const.mul (contDiff_sum_sq_coords.pow 2)).contDiffOn
  · exact mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero)
      (pow_ne_zero 2 (sum_sq_ne_zero_of_ne_zero hx))
theorem contDiffOn_propagatorEntry (hR : HouseholderOnBivectorsFacts) (P Q : AxisPlane) :
    ContDiffOn ℝ ∞ (propagatorEntry P Q) {x | x ≠ 0} :=
  (contDiffOn_continuumCurvatureKernel P Q).congr fun x hx =>
    (continuumCurvatureKernel_eq_entry hR hx P Q).symm
theorem differentiableAt_propagatorEntry (hR : HouseholderOnBivectorsFacts)
    (P Q : AxisPlane) {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (propagatorEntry P Q) x :=
  ((contDiffOn_propagatorEntry hR P Q).contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt
    (by simp)
theorem fderiv_propagatorEntry_homogeneous (hR : HouseholderOnBivectorsFacts)
    (P Q : AxisPlane) {u : Fin 4 → ℝ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t)
    (v : Fin 4 → ℝ) :
    t * fderiv ℝ (propagatorEntry P Q) (t • u) v =
      (t ^ 4)⁻¹ * fderiv ℝ (propagatorEntry P Q) u v := by
  have hne : t • u ≠ 0 := smul_ne_zero ht.ne' hu
  have hd := (differentiableAt_propagatorEntry hR P Q hne).hasFDerivAt
  have hd' := (differentiableAt_propagatorEntry hR P Q hu).hasFDerivAt
  have hlin : HasFDerivAt (fun y : Fin 4 → ℝ => t • y)
      (t • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) u :=
    (hasFDerivAt_id u).const_smul t
  have hcomp := HasFDerivAt.comp (f := fun y : Fin 4 → ℝ => t • y) u hd hlin
  have heq : (propagatorEntry P Q ∘ fun y : Fin 4 → ℝ => t • y) =ᶠ[𝓝 u]
      fun y => (t ^ 4)⁻¹ * propagatorEntry P Q y := by
    filter_upwards [isOpen_ne.mem_nhds hu] with y hy
    simp only [Function.comp, propagatorEntry, freeCurvaturePropagator_smul_of_pos hy ht,
      bivectorMatrixEntry_smul]
  have hscaled := (hd'.const_mul ((t ^ 4)⁻¹)).congr_of_eventuallyEq heq
  have happ := congrArg (fun L => L v) (hcomp.unique hscaled)
  simpa using happ
theorem isCompact_unitSphere4 : IsCompact unitSphere4 := by
  have hsum : ∀ x ∈ unitSphere4, ∑ ν, x ν ^ 2 = 1 := fun x hx => Real.sqrt_eq_one.1 hx
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq continuous_euclidNormVec continuous_const)
  refine (Metric.isBounded_closedBall (x := (0 : Fin 4 → ℝ)) (r := 1)).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro μ
  have hle : x μ ^ 2 ≤ ∑ ν, x ν ^ 2 :=
    Finset.single_le_sum (f := fun ν => x ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  rw [hsum x hx] at hle
  rw [Real.norm_eq_abs]
  exact sq_le_one_iff_abs_le_one _ |>.1 hle
theorem continuousOn_norm_gradientVec (hR : HouseholderOnBivectorsFacts) (P Q : AxisPlane) :
    ContinuousOn (fun u => euclidNormVec (gradientVec (propagatorEntry P Q) u)) {x | x ≠ 0} := by
  have hf := (contDiffOn_propagatorEntry hR P Q).continuousOn_fderiv_of_isOpen isOpen_ne
    (by simp)
  refine continuous_euclidNormVec.comp_continuousOn (continuousOn_pi.2 fun α => ?_)
  exact hf.clm_apply continuousOn_const
theorem curvatureKernelGradientSup_eq (hR : HouseholderOnBivectorsFacts) :
    curvatureKernelGradientSup =
      ⨆ (P : AxisPlane) (Q : AxisPlane) (u : Fin 4 → ℝ) (_ : euclidNormVec u = 1),
        ENNReal.ofReal (euclidNormVec (gradientVec (propagatorEntry P Q) u)) := by
  unfold curvatureKernelGradientSup
  refine iSup_congr fun P => iSup_congr fun Q => iSup_congr fun u => iSup_congr fun hu => ?_
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [euclidNormVec] at hu
  have heq : continuumCurvatureKernel P Q =ᶠ[𝓝 u] propagatorEntry P Q := by
    filter_upwards [isOpen_ne.mem_nhds hu0] with y hy using
      continuumCurvatureKernel_eq_entry hR hy P Q
  have hgrad : gradientVec (continuumCurvatureKernel P Q) u =
      gradientVec (propagatorEntry P Q) u := by
    funext α
    simp only [gradientVec, heq.fderiv_eq]
  rw [hgrad]
theorem curvatureKernelGradientSup_ne_top (hR : HouseholderOnBivectorsFacts) :
    curvatureKernelGradientSup ≠ ⊤ := by
  have hsub : unitSphere4 ⊆ {x : Fin 4 → ℝ | x ≠ 0} := by
    rintro x hx rfl
    simp [unitSphere4, euclidNormVec] at hx
  have hH : ContinuousOn (fun u => ∑ P : AxisPlane, ∑ Q : AxisPlane,
      euclidNormVec (gradientVec (propagatorEntry P Q) u)) unitSphere4 :=
    continuousOn_finsetSum _ fun P _ => continuousOn_finsetSum _ fun Q _ =>
      (continuousOn_norm_gradientVec hR P Q).mono hsub
  obtain ⟨M, hM⟩ := isCompact_unitSphere4.exists_bound_of_continuousOn hH
  rw [curvatureKernelGradientSup_eq hR]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
  refine iSup_le fun P => iSup_le fun Q => iSup_le fun u => iSup_le fun hu => ?_
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ ((le_abs_self _).trans (hM u hu)))
  refine le_trans ?_ (Finset.single_le_sum (f := fun P : AxisPlane =>
    ∑ Q : AxisPlane, euclidNormVec (gradientVec (propagatorEntry P Q) u))
    (fun _ _ => Finset.sum_nonneg fun _ _ => euclidNormVec_nonneg _) (Finset.mem_univ P))
  exact Finset.single_le_sum (f := fun Q : AxisPlane =>
    euclidNormVec (gradientVec (propagatorEntry P Q) u))
    (fun _ _ => euclidNormVec_nonneg _) (Finset.mem_univ Q)
theorem norm_gradientVec_le_on_sphere (hR : HouseholderOnBivectorsFacts) (P Q : AxisPlane)
    {u : Fin 4 → ℝ} (hu : euclidNormVec u = 1) :
    euclidNormVec (gradientVec (propagatorEntry P Q) u) ≤ curvatureKernelGradientSup.toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal (curvatureKernelGradientSup_ne_top hR)).1 ?_
  rw [curvatureKernelGradientSup_eq hR]
  exact le_iSup_of_le P (le_iSup_of_le Q (le_iSup_of_le u (le_iSup_of_le hu le_rfl)))
theorem norm_gradientVec_le (hR : HouseholderOnBivectorsFacts) (P Q : AxisPlane)
    {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    euclidNormVec (gradientVec (propagatorEntry P Q) x) ≤
      curvatureKernelGradientSup.toReal / euclidNormVec x ^ 5 := by
  have ht := euclidNormVec_pos hx
  set t := euclidNormVec x with htdef
  have hunit : euclidNormVec (t⁻¹ • x) = 1 := euclidNormVec_normalize hx
  have hu0 : t⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero ht.ne') hx
  have hback : t • (t⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hg : gradientVec (propagatorEntry P Q) x =
      (t ^ 5)⁻¹ • gradientVec (propagatorEntry P Q) (t⁻¹ • x) := by
    funext α
    have hh := fderiv_propagatorEntry_homogeneous hR P Q hu0 ht (Pi.single α 1)
    rw [hback] at hh
    simp only [gradientVec, Pi.smul_apply, smul_eq_mul]
    field_simp at hh ⊢
    linarith
  rw [hg, euclidNormVec_smul, abs_of_pos (inv_pos.2 (pow_pos ht 5)), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_gradientVec_le_on_sphere hR P Q hunit)
    (inv_pos.2 (pow_pos ht 5)).le
theorem algebraAndBoundsAt_of_ne_zero (hR : HouseholderOnBivectorsFacts)
    (hK : FreeCurvaturePropagatorSymmEvenContinuous) {x : Fin 4 → ℝ}
    (hx : x ≠ 0) : AlgebraAndBoundsAt x := by
  obtain ⟨-, -, ⟨-, -, hstar⟩, ⟨hsym, -, hinv, htr⟩, ⟨-, -, -, -, -, hbound, hdisj⟩⟩ :=
    hR _ (euclidNormVec_normalize hx)
  have ha := propagatorScale_pos hx
  have hscaled := propagatorScale_smul_freeCurvaturePropagator hx
  have hKa := freeCurvaturePropagator_eq_smul_exteriorSq x
  set R := exteriorSq (householder ((euclidNormVec x)⁻¹ • x)) with hRdef
  have hscaled' : ∀ ξ, (Real.pi ^ 2 * euclidNormVec x ^ 4) • freeCurvaturePropagator x ξ = R ξ :=
    fun ξ => by
      rw [← hscaled]
      rfl
  have hsq : freeCurvaturePropagator x ∘ₗ freeCurvaturePropagator x =
      ((Real.pi ^ 4 * euclidNormVec x ^ 8)⁻¹) • LinearMap.id := by
    have hc : (Real.pi ^ 2 * euclidNormVec x ^ 4)⁻¹ * (Real.pi ^ 2 * euclidNormVec x ^ 4)⁻¹ =
        (Real.pi ^ 4 * euclidNormVec x ^ 8)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ring
    rw [hKa, ← hc, ← hinv]
    refine LinearMap.ext fun ξ => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
  unfold AlgebraAndBoundsAt
  refine ⟨hK.2.1 x hx, hK.1 x hx, hsq, ?_, ?_, fun P Q => ?_,
    fun P Q => norm_gradientVec_le hR P Q hx, fun ξ η => ?_, ?_, ?_, fun P Q hPQ => ?_⟩
  · rw [hKa, bivectorTrace_smul, htr, mul_zero]
  · have hconj : hodge ∘ₗ ((Real.pi ^ 2 * euclidNormVec x ^ 4)⁻¹ • R) ∘ₗ hodge =
        (Real.pi ^ 2 * euclidNormVec x ^ 4)⁻¹ • (hodge ∘ₗ R ∘ₗ hodge) := by
      refine LinearMap.ext fun ξ => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [hKa, hconj, hstar, smul_neg]
  · rw [hKa, bivectorMatrixEntry_smul, abs_mul, abs_of_pos (inv_pos.2 ha)]
    exact mul_le_of_le_one_right (inv_pos.2 ha).le (hbound P Q).1
  · rw [hscaled', hscaled', ← hsym ξ (R η)]
    have hRR : R (R η) = η := by
      have happ := congrArg (fun L => L η) hinv
      simpa using happ
    rw [hRR]
  · rw [hscaled, hinv]
  · rw [hsq, bivectorTrace_smul, bivectorTrace_id]
    ring
  · rw [hKa, bivectorMatrixEntry_smul, (hdisj P Q hPQ).1, mul_zero]
end PropagatorProperties
open PropagatorProperties in
theorem freeCurvaturePropagatorProperties_holds (hR : HouseholderOnBivectorsFacts)
    (hK : FreeCurvaturePropagatorSymmEvenContinuous) :
    FreeCurvaturePropagatorProperties :=
  ⟨fun _ hx => algebraAndBoundsAt_of_ne_zero hR hK hx,
    fun P Q => contDiffOn_propagatorEntry hR P Q,
    fun _ _ hx ht => freeCurvaturePropagator_smul_of_pos hx ht,
    fun _ hu => ⟨rfl, fun P Q => continuumCurvatureKernel_eq_entry hR hu P Q⟩,
    curvatureKernelGradientSup_eq hR, curvatureKernelGradientSup_ne_top hR⟩
end Exterior
end YangMills.Construction
end
