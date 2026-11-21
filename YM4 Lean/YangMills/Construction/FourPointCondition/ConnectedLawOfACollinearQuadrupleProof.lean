import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.FourPointCondition.ConnectedLawOfACollinearQuadruple
import YangMills.Construction.ResponseInTheExpansion.BoundsOfTheCollinearConnectedLaw
import YangMills.Construction.Torus.BumpsAndShapeNumbers
import YangMills.Construction.Torus.PointsSupportsAndLiftsOfAQuadruple
import YangMills.Construction.Torus.RescalingLiftsAndFunctionNorms
import YangMills.Construction.Torus.SumOverThePlanesAroundARing
import YangMills.Construction.Torus.TestPairsCentresAndTorusLebesgueMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set Filter Tuples FreeRingKernels PeriodicLattice Exterior TestFunctions TorusMetric ResponseInTheExpansion
  LinearResponse
namespace FourPointCondition
private theorem euclidNormVec_sq_eq_sqNorm (z : Fin 4 → ℝ) : euclidNormVec z ^ 2 = sqNorm z := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
private theorem householder_normalize_apply (z : Fin 4 → ℝ) (i j : Fin 4) :
    householder ((euclidNormVec z)⁻¹ • z) i j = hyperplaneReflection z i j := by
  unfold householder hyperplaneReflection
  rw [← euclidNormVec_sq_eq_sqNorm]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring
private theorem conj_wedge_apply (T : Matrix (Fin 4) (Fin 4) ℝ) (a b μ ν : Fin 4) :
    (T * (Matrix.vecMulVec (Pi.single a (1 : ℝ)) (Pi.single b 1) - Matrix.vecMulVec (Pi.single b (1 : ℝ)) (Pi.single a 1)) *
      T.transpose) μ ν = T μ a * T ν b - T μ b * T ν a := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose, Matrix.vecMul_transpose]
  simp [Matrix.sub_apply, Matrix.vecMulVec_apply]
private abbrev orderedPlaneEquiv : OrderedPlane ≃ AxisPlane := axisPlaneEquivOrderedPairs.symm
private theorem planeKernelMatrix_eq_entry (z : Fin 4 → ℝ) (P' Q' : OrderedPlane) :
    planeKernelMatrix z P' Q' = bivectorMatrixEntry (freeCurvaturePropagator z) (orderedPlaneEquiv P') (orderedPlaneEquiv Q') := by
  set P := orderedPlaneEquiv P' with hP
  set Q := orderedPlaneEquiv Q' with hQ
  unfold bivectorMatrixEntry
  rw [inner_axisBivector]
  have h4 : euclidNormVec z ^ 4 = sqNorm z ^ 2 := by
    rw [← euclidNormVec_sq_eq_sqNorm]
    ring
  have hE : ((freeCurvaturePropagator z) (axisBivector Q)).1 =
      (1 / (Real.pi ^ 2 * euclidNormVec z ^ 4)) •
        (householder ((euclidNormVec z)⁻¹ • z) *
          (Matrix.vecMulVec (Pi.single Q.lower (1 : ℝ)) (Pi.single Q.upper 1) -
            Matrix.vecMulVec (Pi.single Q.upper (1 : ℝ)) (Pi.single Q.lower 1)) *
          (householder ((euclidNormVec z)⁻¹ • z)).transpose) := rfl
  rw [hE, Matrix.smul_apply, conj_wedge_apply, householder_normalize_apply, householder_normalize_apply,
    householder_normalize_apply, householder_normalize_apply, h4]
  unfold planeKernelMatrix LinearResponse.continuumCurvatureKernel
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv, one_div, mul_comm]
  rfl
private theorem planeKernelMatrix_transpose (z : Fin 4 → ℝ) : (planeKernelMatrix z).transpose = planeKernelMatrix z := by
  have hs : ∀ i j, hyperplaneReflection z i j = hyperplaneReflection z j i := by
    intro i j
    unfold hyperplaneReflection
    by_cases h : i = j
    · subst h
      rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  ext P Q
  show planeKernelMatrix z Q P = planeKernelMatrix z P Q
  unfold planeKernelMatrix LinearResponse.continuumCurvatureKernel
  rw [hs Q.1.1 P.1.1, hs Q.1.2 P.1.2, hs Q.1.1 P.1.2, hs Q.1.2 P.1.1]
  ring
private theorem planeKernelMatrix_neg (z : Fin 4 → ℝ) : planeKernelMatrix (-z) = planeKernelMatrix z := by
  have hl : sqNorm (-z) = sqNorm z := by
    unfold sqNorm
    simp
  have hs : ∀ i j, hyperplaneReflection (-z) i j = hyperplaneReflection z i j := by
    intro i j
    unfold hyperplaneReflection
    rw [hl]
    simp
  ext P Q
  unfold planeKernelMatrix LinearResponse.continuumCurvatureKernel
  simp only [hs, hl]
private theorem planeKernelMatrix_sub_comm (a b : Fin 4 → ℝ) : planeKernelMatrix (a - b) = planeKernelMatrix (b - a) := by
  rw [← neg_sub, planeKernelMatrix_neg]
private def fourKernelTrace (ς : Fin 4 → Fin 4) (x : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Matrix.trace (planeKernelMatrix (x (ς 0) - x (ς 1)) * (planeKernelMatrix (x (ς 1) - x (ς 2)) *
    (planeKernelMatrix (x (ς 2) - x (ς 3)) * planeKernelMatrix (x (ς 3) - x (ς 0)))))
private theorem finRotate_four_values :
    finRotate 4 0 = 1 ∧ finRotate 4 1 = 2 ∧ finRotate 4 2 = 3 ∧ finRotate 4 3 = 0 := by
  decide
open Classical in
private theorem planeKernelMatrix_eq_submatrix (z : Fin 4 → ℝ) :
    planeKernelMatrix z = (LinearMap.toMatrix axisBivectorBasis.toBasis axisBivectorBasis.toBasis
      (freeCurvaturePropagator z)).submatrix orderedPlaneEquiv orderedPlaneEquiv := by
  ext P Q
  rw [planeKernelMatrix_eq_entry, bivectorMatrixEntry_eq_toMatrix]
  rfl
private theorem trace_submatrix_orderedPlaneEquiv (M : Matrix AxisPlane AxisPlane ℝ) :
    Matrix.trace (M.submatrix orderedPlaneEquiv orderedPlaneEquiv) = Matrix.trace M := by
  unfold Matrix.trace
  exact Equiv.sum_comp orderedPlaneEquiv fun P => Matrix.diag M P
open Classical in
private theorem bivectorTrace_eq_trace_toMatrix (T : Module.End ℝ Bivector) :
    bivectorTrace T = Matrix.trace (LinearMap.toMatrix axisBivectorBasis.toBasis axisBivectorBasis.toBasis T) := by
  unfold bivectorTrace Matrix.trace
  exact Finset.sum_congr rfl fun P _ => bivectorMatrixEntry_eq_toMatrix T P P
private theorem cyclicTrace_eq_fourKernelTrace (ς : Fin 4 → Fin 4) (x : Fin 4 → Fin 4 → ℝ) :
    cyclicTrace ς x = fourKernelTrace ς x := by
  classical
  obtain ⟨r0, r1, r2, r3⟩ := finRotate_four_values
  have hp : cyclicPropagatorProduct ς x =
      (freeCurvaturePropagator (x (ς 0) - x (ς 1)) : Module.End ℝ Bivector) *
        ((freeCurvaturePropagator (x (ς 1) - x (ς 2)) : Module.End ℝ Bivector) *
          ((freeCurvaturePropagator (x (ς 2) - x (ς 3)) : Module.End ℝ Bivector) *
            (freeCurvaturePropagator (x (ς 3) - x (ς 0)) : Module.End ℝ Bivector))) := by
    unfold cyclicPropagatorProduct
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    simp [r0, r1, r2, r3]
  unfold cyclicTrace fourKernelTrace
  rw [hp, bivectorTrace_eq_trace_toMatrix]
  simp only [planeKernelMatrix_eq_submatrix, Module.End.mul_eq_comp, Matrix.submatrix_mul_equiv,
    trace_submatrix_orderedPlaneEquiv]
  simp only [LinearMap.toMatrix_comp axisBivectorBasis.toBasis axisBivectorBasis.toBasis axisBivectorBasis.toBasis]
private theorem traceAlongCycle_eq_trace {ℓ : ℝ} (u : Fin 4 → Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    traceAlongCycle (q := 3) ℓ u σ = Matrix.trace
      (planeKernelMatrix (periodicDisplacement ℓ (u (σ 1)) (u (σ 0))) *
        (planeKernelMatrix (periodicDisplacement ℓ (u (σ 2)) (u (σ 1))) *
        (planeKernelMatrix (periodicDisplacement ℓ (u (σ 3)) (u (σ 2))) *
          planeKernelMatrix (periodicDisplacement ℓ (u (σ 0)) (u (σ 3)))))) := by
  obtain ⟨r0, r1, r2, r3⟩ := finRotate_four_values
  unfold traceAlongCycle
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simp [r0, r1, r2, r3]
private theorem fourKernelTrace_rotateBy_one (ς : Fin 4 → Fin 4) (x : Fin 4 → Fin 4 → ℝ) :
    fourKernelTrace (rotateBy 1 ς) x = fourKernelTrace ς x := by
  obtain ⟨r0, r1, r2, r3⟩ := finRotate_four_values
  unfold fourKernelTrace
  simp only [rotateBy_one_apply, r0, r1, r2, r3]
  rw [Matrix.trace_mul_comm (planeKernelMatrix (x (ς 0) - x (ς 1)))]
  simp only [Matrix.mul_assoc]
private theorem fourKernelTrace_rotateBy (t : ℤ) (ς : Fin 4 → Fin 4) (x : Fin 4 → Fin 4 → ℝ) :
    fourKernelTrace (rotateBy t ς) x = fourKernelTrace ς x := by
  induction t using Int.induction_on with
  | zero => rw [rotateBy_zero]
  | succ n ih =>
    rw [show ((n : ℤ) + 1) = n + 1 from rfl, ← rotateBy_rotateBy, fourKernelTrace_rotateBy_one, ih]
  | pred n ih =>
    rw [← ih, show (-(n : ℤ)) = (-(n : ℤ) - 1) + 1 by ring, ← rotateBy_rotateBy, fourKernelTrace_rotateBy_one]
    simp
private theorem trace_mul_four_rev_of_symm (a b c d : Matrix OrderedPlane OrderedPlane ℝ) (ha : a.transpose = a)
    (hb : b.transpose = b) (hc : c.transpose = c) (hd : d.transpose = d) :
    Matrix.trace (a * (b * (c * d))) = Matrix.trace (d * (c * (b * a))) := by
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, ha, hb, hc, hd, Matrix.mul_assoc]
private theorem fourKernelTrace_reversed (ς : Fin 4 → Fin 4) (x : Fin 4 → Fin 4 → ℝ) :
    fourKernelTrace (reversed ς) x = fourKernelTrace ς x := by
  have e0 : Fin.rev (0 : Fin 4) = 3 := by decide
  have e1 : Fin.rev (1 : Fin 4) = 2 := by decide
  have e2 : Fin.rev (2 : Fin 4) = 1 := by decide
  have e3 : Fin.rev (3 : Fin 4) = 0 := by decide
  unfold fourKernelTrace
  simp only [reversed, e0, e1, e2, e3]
  rw [trace_mul_four_rev_of_symm _ _ _ _ (planeKernelMatrix_transpose _) (planeKernelMatrix_transpose _)
    (planeKernelMatrix_transpose _) (planeKernelMatrix_transpose _), planeKernelMatrix_sub_comm (x (ς 0)) (x (ς 3)),
    planeKernelMatrix_sub_comm (x (ς 1)) (x (ς 0)), planeKernelMatrix_sub_comm (x (ς 2)) (x (ς 1)),
    planeKernelMatrix_sub_comm (x (ς 3)) (x (ς 2))]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
private theorem fourKernelTrace_of_mem_ringClass {ς ς' : Fin 4 → Fin 4} (h : ς' ∈ ringClass ς) (x : Fin 4 → Fin 4 → ℝ) :
    fourKernelTrace ς' x = fourKernelTrace ς x := by
  rw [ringClass_eq_union] at h
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact fourKernelTrace_rotateBy t ς x
  · simp only
    rw [fourKernelTrace_rotateBy, fourKernelTrace_reversed]
private theorem fourKernelTrace_flip (a b c d : Fin 4) (x : Fin 4 → Fin 4 → ℝ) :
    fourKernelTrace ![a, d, c, b] x = fourKernelTrace ![a, b, c, d] x := by
  have e : fourKernelTrace ![a, d, c, b] x = fourKernelTrace (rotateBy 1 ![a, d, c, b]) x :=
    (fourKernelTrace_rotateBy_one _ x).symm
  rw [e, ← fourKernelTrace_reversed ![a, b, c, d] x]
  congr 1
  funext i
  obtain ⟨r0, r1, r2, r3⟩ := finRotate_four_values
  fin_cases i <;> simp [rotateBy_one_apply, reversed, r0, r1, r2, r3]
private theorem exists_int_sub_of_coe_eq {ℓ a a' : ℝ} (h : (a : AddCircle ℓ) = a') : ∃ k : ℤ, a - a' = k * ℓ := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_iff_sub_mem).1 h)
  exact ⟨k, by simpa using hk.symm⟩
private theorem circleSub_congr {ℓ a b a' b' : ℝ} (hℓ : 0 < ℓ) (ha : (a : AddCircle ℓ) = a')
    (hb : (b : AddCircle ℓ) = b') : circleSub ℓ a b = circleSub ℓ a' b' := by
  obtain ⟨p, hp⟩ := exists_int_sub_of_coe_eq ha
  obtain ⟨q, hq⟩ := exists_int_sub_of_coe_eq hb
  have e0 : a - b = (a' - b') + ((p - q : ℤ) : ℝ) * ℓ := by
    push_cast
    linarith
  have e : (a - b) / ℓ = (a' - b') / ℓ + ((p - q : ℤ) : ℝ) := by
    rw [e0]
    field_simp
  unfold circleSub
  rw [e, round_add_intCast, e0]
  push_cast
  ring
private theorem circleSub_of_abs_lt {ℓ a b : ℝ} (hℓ : 0 < ℓ) (hs : |a - b| < ℓ / 2) :
    circleSub ℓ a b = a - b := by
  have hr : round ((a - b) / ℓ) = 0 := by
    rw [round_eq_zero_iff]
    have h1 := abs_lt.1 hs
    constructor
    · rw [le_div_iff₀ hℓ]
      linarith
    · rw [div_lt_iff₀ hℓ]
      linarith
  unfold circleSub
  rw [hr]
  simp
private theorem traceAlongCycle_congr {ℓ : ℝ} (hℓ : 0 < ℓ) {u v : Fin 4 → Fin 4 → ℝ}
    (h : ∀ i, torusProj ℓ (u i) = torusProj ℓ (v i)) (σ : Equiv.Perm (Fin 4)) :
    traceAlongCycle (q := 3) ℓ u σ = traceAlongCycle (q := 3) ℓ v σ := by
  have hd : ∀ a b, periodicDisplacement ℓ (u a) (u b) = periodicDisplacement ℓ (v a) (v b) := by
    intro a b
    funext j
    exact circleSub_congr hℓ (congrFun (h b) j) (congrFun (h a) j)
  rw [traceAlongCycle_eq_trace, traceAlongCycle_eq_trace]
  simp only [hd]
private theorem measurable_planeKernelMatrix_apply (P P' : OrderedPlane) :
    Measurable fun z : Fin 4 → ℝ => planeKernelMatrix z P P' := by
  unfold planeKernelMatrix LinearResponse.continuumCurvatureKernel hyperplaneReflection sqNorm
  fun_prop
private theorem measurable_round_cast : Measurable fun x : ℝ => ((round x : ℤ) : ℝ) := by
  have e : (fun x : ℝ => ((round x : ℤ) : ℝ)) = fun x => ((⌊x + 1 / 2⌋ : ℤ) : ℝ) := by
    funext x
    rw [round_eq]
  rw [e]
  exact (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp
    (Int.measurable_floor.comp (measurable_id.add_const _))
abbrev _root_.YangMills.SharedProofs.p15817 := @measurable_round_cast
private theorem measurable_periodicDisplacement (ℓ : ℝ) (a b : Fin 4) :
    Measurable fun u : Fin 4 → Fin 4 → ℝ => periodicDisplacement ℓ (u a) (u b) := by
  refine measurable_pi_iff.2 fun j => ?_
  have hw : Measurable fun u : Fin 4 → Fin 4 → ℝ => u b j - u a j := by fun_prop
  unfold periodicDisplacement circleSub
  exact hw.sub (measurable_const.mul (measurable_round_cast.comp (hw.div_const ℓ)))
private theorem measurable_matrix_mul_apply {α : Type*} [MeasurableSpace α]
    {A B : α → Matrix OrderedPlane OrderedPlane ℝ} (hA : ∀ P P', Measurable fun a => A a P P')
    (hB : ∀ P P', Measurable fun a => B a P P') (P P' : OrderedPlane) :
    Measurable fun a => (A a * B a) P P' := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun R _ => (hA P R).mul (hB R P')
private theorem measurable_traceAlongCycle (ℓ : ℝ) (σ : Equiv.Perm (Fin 4)) :
    Measurable fun u : Fin 4 → Fin 4 → ℝ => traceAlongCycle (q := 3) ℓ u σ := by
  have hK : ∀ (a b : Fin 4) (P P' : OrderedPlane), Measurable fun u : Fin 4 → Fin 4 → ℝ =>
      planeKernelMatrix (periodicDisplacement ℓ (u (σ a)) (u (σ b))) P P' := fun a b P P' =>
    (measurable_planeKernelMatrix_apply P P').comp (measurable_periodicDisplacement ℓ _ _)
  simp only [traceAlongCycle_eq_trace]
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun P _ =>
    measurable_matrix_mul_apply (hK 1 0)
      (measurable_matrix_mul_apply (hK 2 1) (measurable_matrix_mul_apply (hK 3 2) (hK 0 3))) P P
abbrev _root_.YangMills.SharedProofs.p77237 := @measurable_traceAlongCycle
private def icoRepresentative (ℓ : ℝ) [Fact (0 < ℓ)] (y : Torus4 ℓ) : Fin 4 → ℝ :=
  fun μ => ((AddCircle.measurableEquivIco ℓ 0 (y μ) : Ico (0 : ℝ) (0 + ℓ)) : ℝ)
private theorem measurable_icoRepresentative (ℓ : ℝ) [Fact (0 < ℓ)] : Measurable (icoRepresentative ℓ) :=
  measurable_pi_lambda _ fun μ =>
    measurable_subtype_coe.comp ((AddCircle.measurableEquivIco ℓ 0).measurable.comp (measurable_pi_apply μ))
private theorem torusProj_icoRepresentative (ℓ : ℝ) [Fact (0 < ℓ)] (y : Torus4 ℓ) :
    torusProj ℓ (icoRepresentative ℓ y) = y := by
  funext μ
  exact (AddCircle.equivIco ℓ 0).symm_apply_apply (y μ)
private theorem map_torusProj_cubes {ℓ : ℝ} [Fact (0 < ℓ)] (C : Fin 4 → ℝ) :
    (volume.restrict (Set.pi univ fun _ : Fin 4 => centredIcoCube ℓ C)).map
        (fun (u : Fin 4 → Fin 4 → ℝ) i => torusProj ℓ (u i)) =
      Measure.pi fun _ : Fin 4 => Measure.pi fun _ : Fin 4 => (volume : Measure (AddCircle ℓ)) := by
  have h1 : (volume.restrict (centredIcoCube ℓ C)).map (torusProj ℓ) =
      Measure.pi fun _ : Fin 4 => (volume : Measure (AddCircle ℓ)) := cubePushforward_eq_pi C
  have : SigmaFinite ((volume.restrict (centredIcoCube ℓ C)).map (torusProj ℓ)) := by
    rw [h1]
    infer_instance
  have hmap := Measure.pi_map_pi
    (μ := fun _ : Fin 4 => (volume : Measure (Fin 4 → ℝ)).restrict (centredIcoCube ℓ C))
    (f := fun _ => torusProj ℓ) (fun _ => (measurable_torusProj ℓ).aemeasurable)
  simp only [h1] at hmap
  rw [volume_pi, Measure.restrict_pi_pi]
  exact hmap
private theorem setIntegral_cubes_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (C C' : Fin 4 → ℝ) {G : (Fin 4 → Fin 4 → ℝ) → ℝ}
    (hG : Measurable G)
    (hper : ∀ u v : Fin 4 → Fin 4 → ℝ, (∀ i, torusProj ℓ (u i) = torusProj ℓ (v i)) → G u = G v) :
    ∫ u in Set.pi univ (fun _ : Fin 4 => centredIcoCube ℓ C), G u =
      ∫ u in Set.pi univ (fun _ : Fin 4 => centredIcoCube ℓ C'), G u := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  set H : (Fin 4 → Torus4 ℓ) → ℝ := fun y => G fun i => icoRepresentative ℓ (y i) with hH
  have hHm : Measurable H :=
    hG.comp (measurable_pi_lambda _ fun i => (measurable_icoRepresentative ℓ).comp (measurable_pi_apply i))
  have hcov : Measurable fun (u : Fin 4 → Fin 4 → ℝ) (i : Fin 4) => torusProj ℓ (u i) :=
    measurable_pi_lambda _ fun i => (measurable_torusProj ℓ).comp (measurable_pi_apply i)
  have key : ∀ D : Fin 4 → ℝ, ∫ u in Set.pi univ (fun _ : Fin 4 => centredIcoCube ℓ D), G u =
      ∫ y, H y ∂(Measure.pi fun _ : Fin 4 => Measure.pi fun _ : Fin 4 => (volume : Measure (AddCircle ℓ))) := by
    intro D
    rw [← map_torusProj_cubes D, integral_map hcov.aemeasurable hHm.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact hper _ _ fun i => (torusProj_icoRepresentative ℓ _).symm
  rw [key C, key C']
private theorem pi_Ico_eq_centredIcoCube (ℓ : ℝ) :
    (Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ) = centredIcoCube ℓ fun _ => ℓ / 2 := by
  unfold centredIcoCube
  simp only [sub_self, add_halves]
private theorem setIntegral_cycle_eq_freeRingKernelAlong {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (h4 : 4 * ρ < ℓ) (c : Fin 4 → ℝ)
    {f : Fin 4 → Torus4 ℓ → ℝ} (hm : ∀ i, Measurable fun x => f i (torusProj ℓ x))
    (hs : ∀ i y, f i y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c ρ) (σ : Equiv.Perm (Fin 4)) :
    ∫ u in Set.pi univ (fun _ : Fin 4 => Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ),
        (∏ i, f i (torusProj ℓ (u i))) * traceAlongCycle (q := 3) ℓ u σ =
      freeRingKernelAlong (⇑σ) (fun i => (closedBallR4 c ρ).indicator (f i ∘ torusProj ℓ)) := by
  set G : (Fin 4 → Fin 4 → ℝ) → ℝ := fun u => (∏ i, f i (torusProj ℓ (u i))) * traceAlongCycle (q := 3) ℓ u σ
    with hG
  have hGm : Measurable G :=
    (Finset.measurable_prod _ fun i _ => (hm i).comp (measurable_pi_apply i)).mul (measurable_traceAlongCycle ℓ σ)
  have hper : ∀ u v : Fin 4 → Fin 4 → ℝ, (∀ i, torusProj ℓ (u i) = torusProj ℓ (v i)) → G u = G v := by
    intro u v h
    show (∏ i, f i (torusProj ℓ (u i))) * _ = (∏ i, f i (torusProj ℓ (v i))) * _
    rw [traceAlongCycle_congr hℓ h σ]
    simp only [h]
  have hcoord : ∀ v ∈ closedBallR4 c ρ, ∀ μ, |v μ - c μ| ≤ ρ := fun v hv μ =>
    (abs_apply_le_euclidNormVec (v - c) μ).trans hv
  have hball : closedBallR4 c ρ ⊆ centredIcoCube ℓ c := by
    intro v hv μ _
    have := abs_le.1 (hcoord v hv μ)
    constructor <;> linarith [this.1, this.2]
  have hin : ∀ x ∈ centredIcoCube ℓ c, ∀ i, f i (torusProj ℓ x) ≠ 0 → x ∈ closedBallR4 c ρ := by
    intro x hx i hne
    obtain ⟨v, hv, hvx⟩ := hs i _ hne
    rwa [← (bijOn_torusProj_centredIcoCube hℓ c).injOn (hball hv) hx hvx]
  have hDm : MeasurableSet (Set.pi univ fun _ : Fin 4 => centredIcoCube ℓ c) :=
    MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [show (Set.pi univ fun _ : Fin 4 => Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ) =
      Set.pi univ fun _ : Fin 4 => centredIcoCube ℓ fun _ => ℓ / 2 by rw [pi_Ico_eq_centredIcoCube],
    setIntegral_cubes_eq hℓ _ c hGm hper]
  unfold freeRingKernelAlong
  have hcompl : ∀ x, x ∉ (Set.pi univ fun _ : Fin 4 => centredIcoCube ℓ c) →
      (∏ j, (closedBallR4 c ρ).indicator (f j ∘ torusProj ℓ) (x j)) * cyclicTrace (⇑σ) x = 0 := by
    intro x hx
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ (univ : Set (Fin 4)) ∧ x i ∉ centredIcoCube ℓ c := by
      simpa [Set.mem_pi] using hx
    have h2 : (∏ j, (closedBallR4 c ρ).indicator (f j ∘ torusProj ℓ) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun h => hi (hball h)) _)
    rw [h2, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
  · refine setIntegral_congr_fun hDm fun x hx => ?_
    have hx' : ∀ i, x i ∈ centredIcoCube ℓ c := fun i => hx i (mem_univ i)
    by_cases hall : ∀ i, x i ∈ closedBallR4 c ρ
    · have hd : ∀ a b, periodicDisplacement ℓ (x a) (x b) = x b - x a := by
        intro a b
        funext j
        refine circleSub_of_abs_lt hℓ ?_
        have h1 := abs_le.1 (hcoord _ (hall a) j)
        have h2 := abs_le.1 (hcoord _ (hall b) j)
        rw [abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have ht : traceAlongCycle (q := 3) ℓ x σ = cyclicTrace (⇑σ) x := by
        rw [cyclicTrace_eq_fourKernelTrace, traceAlongCycle_eq_trace]
        unfold fourKernelTrace
        simp only [hd]
      show (∏ i, f i (torusProj ℓ (x i))) * traceAlongCycle (q := 3) ℓ x σ = _
      rw [ht]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hall i) (f i ∘ torusProj ℓ)).symm
    · obtain ⟨i, hi⟩ := not_forall.1 hall
      have h0 : f i (torusProj ℓ (x i)) = 0 := by
        by_contra hne
        exact hi (hin _ (hx' i) i hne)
      have h1 : (∏ j, f j (torusProj ℓ (x j))) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
      have h2 : (∏ j, (closedBallR4 c ρ).indicator (f j ∘ torusProj ℓ) (x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      show (∏ i, f i (torusProj ℓ (x i))) * _ = _
      rw [h1, h2, zero_mul, zero_mul]
private theorem image_perms_fixing_zero :
    (Finset.univ.filter fun s : Equiv.Perm (Fin 4) => s 0 = 0).image
        (fun s : Equiv.Perm (Fin 4) => (⇑s : Fin 4 → Fin 4)) =
      {![0, 1, 2, 3], ![0, 3, 2, 1], ![0, 1, 3, 2], ![0, 2, 3, 1], ![0, 2, 1, 3], ![0, 3, 1, 2]} := by
  decide +kernel
private theorem sum_perms_fixing_zero_aux (G : (Fin 4 → Fin 4) → ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s : Equiv.Perm (Fin 4) => s 0 = 0), G ⇑s =
      G ![0, 1, 2, 3] + (G ![0, 3, 2, 1] + (G ![0, 1, 3, 2] + (G ![0, 2, 3, 1] +
        (G ![0, 2, 1, 3] + G ![0, 3, 1, 2])))) := by
  rw [← Finset.sum_image (f := G) (g := fun s : Equiv.Perm (Fin 4) => (⇑s : Fin 4 → Fin 4))
    (fun _ _ _ _ h => DFunLike.coe_injective h), image_perms_fixing_zero]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
private theorem sum_perms_fixing_zero (inst : DecidablePred fun s : Equiv.Perm (Fin 4) => s 0 = 0)
    (G : (Fin 4 → Fin 4) → ℝ) :
    ∑ s ∈ @Finset.filter _ (fun s : Equiv.Perm (Fin 4) => s 0 = 0) inst Finset.univ, G ⇑s =
      G ![0, 1, 2, 3] + (G ![0, 3, 2, 1] + (G ![0, 1, 3, 2] + (G ![0, 2, 3, 1] +
        (G ![0, 2, 1, 3] + G ![0, 3, 1, 2])))) := by
  convert sum_perms_fixing_zero_aux G
private theorem sum_freeRingKernelAlong_eq_two_mul (g : Fin 4 → (Fin 4 → ℝ) → ℝ)
    (inst : DecidablePred fun s : Equiv.Perm (Fin 4) => s 0 = 0) :
    ∑ s ∈ @Finset.filter _ (fun s : Equiv.Perm (Fin 4) => s 0 = 0) inst Finset.univ, freeRingKernelAlong (⇑s) g =
      2 * freeBoxKernel g := by
  have hmem : ∀ {ς ς' : Fin 4 → Fin 4}, ς' ∈ ringClass ς →
      freeRingKernelAlong ς' g = freeRingKernelAlong ς g := by
    intro ς ς' h
    unfold freeRingKernelAlong
    simp only [cyclicTrace_eq_fourKernelTrace, fourKernelTrace_of_mem_ringClass h]
  have hflip : ∀ a b c d : Fin 4, freeRingKernelAlong ![a, d, c, b] g = freeRingKernelAlong ![a, b, c, d] g := by
    intro a b c d
    unfold freeRingKernelAlong
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show _ * _ = _ * _
    rw [cyclicTrace_eq_fourKernelTrace, cyclicTrace_eq_fourKernelTrace, fourKernelTrace_flip]
  have hring : ∀ r : Fin 3, freeRingKernel (standardFourRing r) g = freeRingKernelAlong (standardFourTuple r) g := by
    intro r
    have hne : (standardFourRing r).Nonempty := ⟨_, Or.inl (mem_rotationClass_self _)⟩
    unfold freeRingKernel
    rw [dif_pos hne]
    exact hmem hne.some_mem
  have e0 : standardFourTuple 0 = ![0, 1, 2, 3] := rfl
  have e1 : standardFourTuple 1 = ![0, 1, 3, 2] := rfl
  have e2 : standardFourTuple 2 = ![0, 2, 1, 3] := rfl
  rw [sum_perms_fixing_zero inst fun ς => freeRingKernelAlong ς g]
  unfold freeBoxKernel
  simp only [hring, Fin.sum_univ_three, e0, e1, e2]
  rw [hflip 0 1 2 3, hflip 0 1 3 2, hflip 0 2 1 3]
  ring
private theorem metricSupport_eq_tsupport {L m : ℕ} (f : PeriodicLattice.FourTorus L m → ℝ) :
    PeriodicLattice.metricSupport f = tsupport f := by
  have h : PeriodicLattice.metricTopology L m =
      (inferInstance : TopologicalSpace (Torus4 (PeriodicLattice.torusSide L m))) := by
    refine Eq.trans ?_ (TorusAnalysis.euclidTopology_eq_instTopology (PeriodicLattice.torusSide L m))
    refine TopologicalSpace.ext (funext fun U => propext ?_)
    exact Iff.rfl
  unfold PeriodicLattice.metricSupport
  rw [h]
  rfl
private theorem continuous_comp_torusProj_of_lipschitz {ℓ : ℝ} {h : Torus4 ℓ → ℝ}
    (hh : IsLipschitzFor (TestFunctions.euclidDistTorus (ℓ := ℓ)) h) : Continuous fun x => h (torusProj ℓ x) := by
  obtain ⟨C, hC0, hC⟩ := hh
  have hv : Continuous fun p : Fin 4 → ℝ => euclidNormVec p := by
    unfold euclidNormVec
    fun_prop
  rw [continuous_iff_continuousAt]
  intro b
  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun x => C * euclidNormVec (x - b)) (fun _ => norm_nonneg _) (fun x => ?_) ?_
  · refine (hC _ _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have e : torusProj ℓ x - torusProj ℓ b = torusProj ℓ (x - b) := by
      funext μ
      simp [torusProj]
    unfold TestFunctions.euclidDistTorus
    rw [e]
    exact AmbientPoints.torusEuclidNorm_torusProj_le _
  · have ht : Tendsto (fun x => C * euclidNormVec (x - b)) (nhds b) (nhds (C * euclidNormVec (b - b))) :=
      (((hv.comp (continuous_id.sub continuous_const)).const_mul C).tendsto b)
    simpa [euclidNormVec] using ht
abbrev _root_.YangMills.SharedProofs.p11913 := @continuous_comp_torusProj_of_lipschitz
private theorem gaugeGroupDim_eq : gaugeGroupDim = 3 := by
  norm_num [gaugeGroupDim, ParameterChoice.colorNumber]
theorem gaussianFourPointCollinear_holds (hB : collinearCumulantBoundsStatement)
    (hG : QuadrupleGeometry.Statement) (hS : RingPlaneSums.RingPlaneSumStatement) :
    gaussianFourPointCollinear := by
  intro s d ϑ f hf
  obtain ⟨h1, h2⟩ := hB s d ϑ f hf
  refine ⟨?_, h1, h2⟩
  obtain ⟨hQ, g, ⟨-, c, hsupp, -⟩, -⟩ := hf
  have hQ' := hQ
  obtain ⟨hsc, h40, hfL, -⟩ := hQ
  have hd : 0 < d := hsc.1
  obtain ⟨hMem, hPts, -, hLifts⟩ := hG.2 s d ϑ hd hsc.2 h40
  obtain ⟨-, hBall, -, -⟩ := hLifts f hQ'
  obtain ⟨-, -, hSB, -⟩ := hBall c hsupp
  obtain ⟨-, x, hx⟩ := (hMem f hfL).1 hQ'
  obtain ⟨-, -, -, -, hdisj⟩ := hPts f hQ' x hx
  obtain ⟨-, -, -, hker⟩ := hS.2.2.2.1 s f (fun i => (hfL i).1)
    (fun i j hij => by
      beta_reduce
      rw [metricSupport_eq_tsupport, metricSupport_eq_tsupport]
      exact hdisj i j hij)
    (TorusMeasure.proj s c) (9 * d) c hSB rfl
  set ℓ : ℝ := PeriodicLattice.torusSide s.L s.m with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hcycle := fun σ => setIntegral_cycle_eq_freeRingKernelAlong (f := f) (ρ := 9 * d) hℓ0 (by linarith) c
    (fun i => (continuous_comp_torusProj_of_lipschitz (hfL i).1).measurable)
    (fun i y hy => hsupp i (subset_tsupport _ hy)) σ
  have hLaw : gaussianCumulantLimit (q := 3) ℓ f =
      (3 / 2) * ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))).filter (fun σ => σ 0 = 0),
        ∫ u in Set.pi univ (fun _ : Fin 4 => Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ),
          (∏ i, f i (torusProj ℓ (u i))) * traceAlongCycle (q := 3) ℓ u σ := rfl
  rw [hLaw]
  simp only [hcycle]
  rw [sum_freeRingKernelAlong_eq_two_mul, gaugeGroupDim_eq, hker]
  have : (fun i => (closedBallR4 c (9 * d)).indicator (f i ∘ torusProj ℓ)) = fun i => ballIndicatorLift c (9 * d) (f i) := rfl
  rw [this]
  ring
end FourPointCondition
end YangMills.Construction
end
