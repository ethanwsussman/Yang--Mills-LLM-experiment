import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.GaugeImagesOfCurvesInTheFibre
import YangMills.Construction.Towers.HessianOfTheLastPartialSum
import YangMills.Construction.Towers.TheActionOnATower
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.ComplexMatrix2
namespace Tower
namespace GaugeImageCurves
variable {L n k : ℕ}
theorem ofReal_smul_eq_smul (r : ℝ) (X : ComplexMatrix2) : ((r : ℝ) : ℂ) • X = r • X := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_matrix <;> assumption
theorem I_smul_neg_real_smul (l : ComplexMatrix2) (t : ℝ) :
    Complex.I • (((-t : ℝ) : ℂ) • l) = t • (-(Complex.I • l)) := by
  rw [ofReal_smul_eq_smul, neg_smul, smul_neg, smul_neg, smul_comm]
theorem hasDerivAt_matExp_smul (a : ComplexMatrix2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matExp (s • a)) (matExp (t • a) * a) t :=
  hasDerivAt_exp_smul_const a t
theorem hasDerivAt_conj_product (a c : ComplexMatrix2) {f : ℝ → ComplexMatrix2}
    {f' : ComplexMatrix2} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => matExp (s • a) * f s * matExp (s • c))
      ((matExp (t • a) * a * f t + matExp (t • a) * f') * matExp (t • c) +
        matExp (t • a) * f t * (matExp (t • c) * c)) t :=
  ((hasDerivAt_matExp_smul a t).mul hf).mul (hasDerivAt_matExp_smul c t)
theorem differentiableOn_deriv_conj_product (a c : ComplexMatrix2) {f : ℝ → ComplexMatrix2}
    {J : Set ℝ} (hJ : IsOpen J)
    (h1 : DifferentiableOn ℝ f J) (h2 : DifferentiableOn ℝ (deriv f) J) :
    DifferentiableOn ℝ (deriv fun s : ℝ => matExp (s • a) * f s * matExp (s • c)) J := by
  have ea : DifferentiableOn ℝ (fun s : ℝ => matExp (s • a)) J := fun t _ =>
    (hasDerivAt_matExp_smul a t).differentiableAt.differentiableWithinAt
  have ec : DifferentiableOn ℝ (fun s : ℝ => matExp (s • c)) J := fun t _ =>
    (hasDerivAt_matExp_smul c t).differentiableAt.differentiableWithinAt
  have ea' : DifferentiableOn ℝ (fun s : ℝ => matExp (s • a) * a) J :=
    ea.mul (differentiableOn_const a)
  have ec' : DifferentiableOn ℝ (fun s : ℝ => matExp (s • c) * c) J :=
    ec.mul (differentiableOn_const c)
  have hH : DifferentiableOn ℝ (fun t : ℝ => (matExp (t • a) * a * f t +
      matExp (t • a) * deriv f t) * matExp (t • c) +
      matExp (t • a) * f t * (matExp (t • c) * c)) J :=
    (((ea'.mul h1).add (ea.mul h2)).mul ec).add ((ea.mul h1).mul ec')
  refine hH.congr fun t ht => ?_
  exact (hasDerivAt_conj_product a c
    ((h1 t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt).deriv
theorem gaugeTransform_expVertexFn_apply (κ : Vertex L n k 0 → ComplexMatrix2) (t : ℝ)
    (V : Edge L n k 0 → ComplexMatrix2) (b : Edge L n k 0) :
    PeriodicLattice.gaugeTransform (expVertexFn (((-t : ℝ) : ℂ) • κ)) V b =
      matExp (t • (-(Complex.I • κ b.source))) * V b *
        matExp (t • (Complex.I • κ b.target)) := by
  have h : ∀ x, expVertexFn (((-t : ℝ) : ℂ) • κ) x = matExp (t • (-(Complex.I • κ x))) :=
    fun x => by
      show matExp (Complex.I • (((-t : ℝ) : ℂ) • κ x)) = _
      rw [I_smul_neg_real_smul]
  show expVertexFn _ b.source * V b * (expVertexFn _ b.target)⁻¹ = _
  rw [h, h, ← Matrix.exp_neg, smul_neg, smul_neg, neg_neg]
theorem fieldSpace_ext {V W : Edge L n k 0 → ComplexMatrix2} (hV : V ∈ fieldSpace L n k 0)
    (hW : W ∈ fieldSpace L n k 0)
    (h : restrictToPositiveEdges V = restrictToPositiveEdges W) : V = W := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact congrFun h ⟨b, hb⟩
  · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    have e : V b.opposite = W b.opposite := congrFun h ⟨b.opposite, hr⟩
    have e1 : V b = (V b.opposite)⁻¹ := hV.2 b.opposite (mem_univ _)
    have e2 : W b = (W b.opposite)⁻¹ := hW.2 b.opposite (mem_univ _)
    rw [e1, e2, e]
theorem extendOddly_congr {f g : Edge L n k 0 → ComplexMatrix2}
    (h : ∀ b : Edge L n k 0, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb, h b hb]
  · simp only [extendOddly, if_neg hb,
      h _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
theorem extendOddly_add (f g : Edge L n k 0 → ComplexMatrix2) :
    extendOddly (fun b => f b + g b) = extendOddly f + extendOddly g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, Pi.add_apply, if_pos hb]
  · simp only [extendOddly, Pi.add_apply, if_neg hb, neg_add]
theorem leftChart_derivative_at_zero {U v p q : ComplexMatrix2} (hU : U * U⁻¹ = 1) :
    Complex.I⁻¹ • (((matExp ((0 : ℝ) • (-(Complex.I • p))) * (-(Complex.I • p)) * U +
        matExp ((0 : ℝ) • (-(Complex.I • p))) * v) * matExp ((0 : ℝ) • (Complex.I • q)) +
        matExp ((0 : ℝ) • (-(Complex.I • p))) * U *
          (matExp ((0 : ℝ) • (Complex.I • q)) * (Complex.I • q))) * U⁻¹) =
      Complex.I⁻¹ • (v * U⁻¹) + (conjugateBy U q - p) := by
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  have e : ((-(Complex.I • p) * U + v) + U * (Complex.I • q)) * U⁻¹ =
      -(Complex.I • p) + v * U⁻¹ + Complex.I • conjugateBy U q := by
    rw [add_mul, add_mul, mul_assoc (-(Complex.I • p)), hU, mul_one]
    simp [conjugateBy]
  have hI : Complex.I⁻¹ * Complex.I = 1 := inv_mul_cancel₀ Complex.I_ne_zero
  rw [e, smul_add, smul_add, smul_neg, smul_smul, smul_smul, hI, one_smul, one_smul]
  abel
end GaugeImageCurves
open GaugeImageCurves in
theorem gaugeImageCurvesInFibre_holds (hHess : LastPartialHessianFormula)
    (hCov : PeriodicLattice.BlockAverageLocalityAndCovariance)
    (hAct : ActionFacts.Statement)
    (hImg : GaugeAndSymmetryImages.statement)
    (hLog : ComplexMatrix2.UnitaryLogConjugationProperties) :
    GaugeImageCurvesInFibre := by
  intro L n k hL hn hk
  have hN := (hHess L n k hL hn hk).1
  have hCovk := ((hCov L n k hL hn).2.2 k le_rfl).1
  have hA := (hAct L k n hL hn).2.1
  have hC := (hImg L k 0 hL (Nat.zero_le k)).1 n hn
  refine Filter.Eventually.of_forall fun W κ I γ hγ hmaps h0 => ?_
  obtain ⟨⟨hI, hconf, hd⟩, hd2⟩ := hγ
  have hκ : (κ : Vertex L n k 0 → ComplexMatrix2) ∈ vertexFunctionSpace L n k 0 ∧
      restrictVertexFunction k (κ : Vertex L n k 0 → ComplexMatrix2) = 0 := κ.2
  have hκ' : (κ : Vertex L n k 0 → ComplexMatrix2) ∈
      Submodule.pi (univ : Set (Vertex L n k 0)) fun _ => ComplexMatrix2.hermitianTraceless :=
    hκ.1
  have hκx : ∀ x, (κ : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
    fun x => Submodule.mem_pi.1 hκ' x (mem_univ x)
  have h0I : (0 : ℝ) ∈ I := hI.2.2
  have hu : ∀ t : ℝ, expVertexFn (((-t : ℝ) : ℂ) • (κ : Vertex L n k 0 → ComplexMatrix2)) ∈
      gaugeGroupAt L n k 0 := fun t x => by
    show matExp (Complex.I • (((-t : ℝ) : ℂ) • (κ : Vertex L n k 0 → ComplexMatrix2) x)) ∈ _
    rw [ofReal_smul_eq_smul]
    exact (hLog.1 _ (ComplexMatrix2.hermitianTraceless.smul_mem _ (hκx x))).2.2
  set g : ℝ → Edge L n k 0 → ComplexMatrix2 := fun t => PeriodicLattice.gaugeTransform
    (expVertexFn (((-t : ℝ) : ℂ) • (κ : Vertex L n k 0 → ComplexMatrix2))) (γ t) with hgdef
  have hgv : ∀ (t : ℝ) (b : Edge L n k 0), g t b =
      matExp (t • (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source))) * γ t b *
        matExp (t • (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.target)) :=
    fun t b => gaugeTransform_expVertexFn_apply _ t (γ t) b
  have hfun : ∀ b : Edge L n k 0, (fun t => g t b) = fun t =>
      matExp (t • (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source))) * γ t b *
        matExp (t • (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.target)) :=
    fun b => funext fun t => hgv t b
  have hg0 : g 0 = γ 0 := by
    funext b
    rw [hgv]
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  have hderiv : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ∀ t ∈ I,
      HasDerivAt (fun s => g s b)
      ((matExp (t • (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source))) *
            (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source)) * γ t b +
          matExp (t • (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source))) *
            deriv (fun s => γ s b) t) *
          matExp (t • (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.target)) +
        matExp (t • (-(Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.source))) * γ t b *
          (matExp (t • (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.target)) *
            (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.target))) t := by
    intro b hb t ht
    rw [hfun b]
    exact hasDerivAt_conj_product _ _
      ((hd b hb t ht).differentiableAt (hI.1.mem_nhds ht)).hasDerivAt
  have hcont : ContinuousAt (fun t => restrictToPositiveEdges (g t)) 0 :=
    continuousAt_pi.2 fun b => (hderiv b.1 b.2 0 h0I).continuousAt
  obtain ⟨hsub, O, hO, e⟩ := hN.isOpenNhd.1
  have hO0 : restrictToPositiveEdges (g 0) ∈ O := by
    have h1 : restrictToPositiveEdges (γ 0) ∈
        restrictToPositiveEdges '' smoothingFibreNhd L n k := mem_image_of_mem _ (hmaps h0I).1
    rw [e] at h1
    rw [hg0]
    exact h1.1
  have hnh : (fun t => restrictToPositiveEdges (g t)) ⁻¹' O ∩ I ∈ 𝓝 (0 : ℝ) :=
    inter_mem (hcont.preimage_mem_nhds (hO.mem_nhds hO0)) (hI.1.mem_nhds h0I)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnh
  have hJI : Metric.ball (0 : ℝ) ε ⊆ I := fun t ht => (hball ht).2
  have hJ : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
    ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo,
      Metric.mem_ball_self hε⟩
  have hgc : ∀ t ∈ I, g t ∈ fieldSpace L n k 0 := fun t ht =>
    (hC (γ t) _ id
      ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 ((hconf ht).1 b hb)).2, (hconf ht).2⟩
      (fun x => (Matrix.mem_specialUnitaryGroup_iff.1 (hu t x)).2)
      (fun _ _ => rfl) (image_id _)).2.2.1 (hconf ht) (hu t)
  refine ⟨Metric.ball 0 ε, hJI, ⟨⟨hJ, fun t ht => hgc t (hJI ht), fun b hb t ht =>
    (hderiv b hb t (hJI ht)).differentiableAt.differentiableWithinAt⟩, fun b hb => ?_⟩,
    fun t ht => ⟨?_, ?_⟩, ?_, ?_, fun t ht => hA (γ t) (hconf (hJI ht)) _ (hu t)⟩
  · show DifferentiableOn ℝ (deriv fun t => g t b) _
    rw [hfun b]
    exact differentiableOn_deriv_conj_product _ _ Metric.isOpen_ball ((hd b hb).mono hJI)
      ((hd2 b hb).mono hJI)
  · have hp : restrictToPositiveEdges (g t) ∈
        restrictToPositiveEdges '' smoothingFibreNhd L n k := by
      rw [e]
      exact ⟨(hball ht).1, fun b => (hgc t (hJI ht)).1 b.1 (mem_univ _)⟩
    obtain ⟨V, hV, hVe⟩ := hp
    rwa [fieldSpace_ext (hsub hV) (hgc t (hJI ht)) hVe] at hV
  · have hr : PeriodicLattice.restrictGaugeMap k
        (expVertexFn (((-t : ℝ) : ℂ) • (κ : Vertex L n k 0 → ComplexMatrix2))) =
          fun _ => 1 := by
      funext x
      have e0 : (κ : Vertex L n k 0 → ComplexMatrix2)
          (x.toSublattice (PeriodicLattice.levelDepth k 0)) = 0 :=
        congrFun hκ.2 x
      show matExp (Complex.I • (((-t : ℝ) : ℂ) •
        (κ : Vertex L n k 0 → ComplexMatrix2)
          (x.toSublattice (PeriodicLattice.levelDepth k 0)))) = 1
      rw [e0]
      simp
    have h1 : smoothingIter L n k k (g t) = PeriodicLattice.gaugeTransform
        (PeriodicLattice.restrictGaugeMap k
          (expVertexFn (((-t : ℝ) : ℂ) • (κ : Vertex L n k 0 → ComplexMatrix2))))
        (smoothingIter L n k k (γ t)) := hCovk (γ t) (hconf (hJI ht)) _ (hu t)
    rw [h1, hr, (hmaps (hJI ht)).2]
    funext b
    simp [PeriodicLattice.gaugeTransform]
  · rw [← h0]
    exact hg0
  · have hUinv : ∀ b : Edge L n k 0, γ 0 b * (γ 0 b)⁻¹ = 1 := fun b =>
      Matrix.mul_nonsing_inv _ (by
        rw [(Matrix.mem_specialUnitaryGroup_iff.1 ((hconf h0I).1 b (mem_univ b))).2]
        exact isUnit_one)
    have ht : curveTangent g = curveTangent γ +
        covDiff (γ 0) (κ : Vertex L n k 0 → ComplexMatrix2) := by
      unfold curveTangent covDiff
      rw [← extendOddly_add]
      refine extendOddly_congr fun b hb => ?_
      show Complex.I⁻¹ • (deriv (fun t => g t b) 0 * (g 0 b)⁻¹) = _
      rw [(hderiv b hb 0 h0I).deriv, hg0]
      exact leftChart_derivative_at_zero (hUinv b)
    rw [← h0]
    exact ht
end Tower
end YangMills.Construction
end
