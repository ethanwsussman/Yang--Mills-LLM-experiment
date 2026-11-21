import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.DoubleBlockStraightPathCorridorAndPivotBond
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.ExpLogSeriesConvergence
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Conventions
namespace ElementaryStepFacts
theorem halfTrace_smul_one (c : ℂ) :
    ComplexMatrix2.halfTrace (c • (1 : ComplexMatrix2)) = c := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]
  ring
theorem det_algebraMap_sub_of_sq {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    {r : ℂ} (hsq : Y ^ 2 = (r ^ 2) • (1 : ComplexMatrix2)) (z : ℂ) :
    (algebraMap ℂ ComplexMatrix2 z - Y).det = z ^ 2 - r ^ 2 := by
  have htr : Y 0 0 + Y 1 1 = 0 := by
    have := hY.2
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using this
  have hentry : Y 0 0 * Y 0 0 + Y 0 1 * Y 1 0 = r ^ 2 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.det_fin_two]
  simp [Matrix.algebraMap_matrix_apply]
  linear_combination (Y 0 0 - z) * htr - hentry
theorem lieSquareExpFormula_holds (hU : ComplexMatrix2.UnitaryLogarithmProperties) :
    LieSquareExpFormula := by
  intro Y hY
  obtain ⟨hsq, hexp, -, hmem⟩ := hU.1 Y hY
  refine ⟨hsq, ?_, ?_, ?_, hexp, ?_, hmem⟩
  · rw [hsq, halfTrace_smul_one]
  · simp only [halfTracePairing, pow_two]
  · ext z
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, det_algebraMap_sub_of_sq hY hsq z,
      isUnit_iff_ne_zero, not_not, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]
    simp
  · have htr : Matrix.trace Y = 0 := hY.2
    rw [hexp]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.trace_smul,
      htr]
    ring
theorem expInjOnBallPi_holds (hU : ComplexMatrix2.UnitaryLogarithmProperties) :
    ExpInjOnBallPi := by
  intro Y hY Z hZ hYr hZr heq
  have hSU : ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary :=
    (hU.1 Y hY).2.2.2
  have hne : ComplexMatrix2.matExp (Complex.I • Y) ≠ -1 := by
    intro h
    have htr := (lieSquareExpFormula_holds hU Y hY).2.2.2.2.2.1
    rw [h] at htr
    have hneg : ComplexMatrix2.halfTrace (-1 : ComplexMatrix2) = -1 := by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    rw [hneg] at htr
    have hcos : Real.cos (ComplexMatrix2.operatorNorm Y) = -1 := by exact_mod_cast htr.symm
    have hlt : Real.cos Real.pi < Real.cos (ComplexMatrix2.operatorNorm Y) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (norm_nonneg _) le_rfl hYr
    rw [Real.cos_pi] at hlt
    linarith
  have hdom : ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.unitaryLogDomain :=
    ⟨hSU, hne⟩
  have hlY := (hU.2.2.1 _ hdom Y).1 ⟨hY, hYr, rfl⟩
  have hlZ := (hU.2.2.1 _ hdom Z).1 ⟨hZ, hZr, heq.symm⟩
  rw [hlY, hlZ]
theorem analyticOnNhd_logSeries :
    AnalyticOnNhd ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall := by
  have : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
  set c : ℕ → ℂ := fun n => (n : ℂ)⁻¹ with hc
  set p := FormalMultilinearSeries.ofScalars ComplexMatrix2 c with hp
  have hrad : (1 : ENNReal) ≤ p.radius := by
    have := p.le_radius_of_bound 1 (r := 1) (fun n => by
      simp only [NNReal.coe_one, one_pow, mul_one]
      rw [hp, FormalMultilinearSeries.ofScalars_norm]
      rcases n with _ | n
      · simp [hc]
      · simp only [hc, norm_inv, Complex.norm_natCast]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n))
    simpa using this
  have hball := (p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)).analyticOnNhd
  have hsum : ∀ Y : ComplexMatrix2, ∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • Y ^ (n + 1) = p.sum Y := by
    intro Y
    have hps : p.sum Y = ∑' n : ℕ, c n • Y ^ n :=
      congrFun (FormalMultilinearSeries.ofScalarsSum_eq_tsum c) Y
    rw [hps]
    have hshift := (Nat.succ_injective).tsum_eq (f := fun n : ℕ => c n • Y ^ n) (by
      intro n hn
      rcases n with _ | n
      · simp [hc] at hn
      · exact ⟨n, rfl⟩)
    rw [← hshift]
    refine tsum_congr fun n => ?_
    simp [hc]
  have hlog : ComplexMatrix2.logSeries = fun X => -p.sum (1 - X) := by
    funext X
    simp only [ComplexMatrix2.logSeries, hsum]
  intro X hX
  rw [hlog]
  have hmem : (1 - X) ∈ Metric.eball (0 : ComplexMatrix2) p.radius := by
    refine Metric.eball_subset_eball hrad ?_
    have hlt : ‖1 - X‖ < 1 := by
      rw [norm_sub_rev]
      exact hX
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.2 hlt
  exact ((hball _ hmem).fun_comp (analyticAt_const.sub analyticAt_id)).neg
theorem logSeriesNearOne_holds (hS : ComplexMatrix2.ExpLogSeriesConvergence)
    (hE : ComplexMatrix2.ExpLogEstimates) : LogSeriesNearOne := by
  have hone : ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0 := hS.2.2
  refine ⟨analyticOnNhd_logSeries, hone, ?_, ?_⟩
  · refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds (1 : ComplexMatrix2)
      (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hε)] with X hX
    have hd : ‖X - 1‖ < min (1 / 2) ε := by simpa [dist_eq_norm] using hX
    have hhalf : ‖X - 1‖ < 1 / 2 := lt_of_lt_of_le hd (min_le_left _ _)
    have hlt : ‖X - 1‖ < ε := lt_of_lt_of_le hd (min_le_right _ _)
    have hb : ‖ComplexMatrix2.logSeries X - (X - 1)‖ ≤ ‖X - 1‖ ^ 2 / (2 * (1 - ‖X - 1‖)) :=
      (hS.2.1 X _ rfl (by linarith)).2.2.2.2.2.2.1
    have hnn : 0 ≤ ‖X - 1‖ := norm_nonneg _
    have hq : ‖X - 1‖ ^ 2 / (2 * (1 - ‖X - 1‖)) ≤ ‖X - 1‖ ^ 2 := by
      apply div_le_self (by positivity)
      linarith
    simp only [hone, sub_zero, ContinuousLinearMap.id_apply]
    calc ‖ComplexMatrix2.logSeries X - (X - 1)‖ ≤ ‖X - 1‖ ^ 2 := hb.trans hq
      _ ≤ ε * ‖X - 1‖ := by nlinarith
  · intro X hX
    have h := (hE.2.2.2.1 (X - 1) hX).2.2.2.2
    rwa [add_sub_cancel] at h
theorem sinc_mul_self_eq_sin (r : ℝ) : Real.sinc r * r = Real.sin r := by
  by_cases h : r = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]
    field_simp
theorem operatorNorm_matExp_sub_one_lt_one (hU : ComplexMatrix2.UnitaryLogarithmProperties)
    {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (hr : ComplexMatrix2.operatorNorm Y < Real.pi / 3) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • Y) - 1) < 1 := by
  obtain ⟨hsq, hexp, -, -⟩ := hU.1 Y hY
  set r := ComplexMatrix2.operatorNorm Y with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  set s : ℂ := Complex.I * (Real.sinc r : ℂ) with hs
  set a : ℂ := (Real.cos r : ℂ) - 1 with ha
  set M := ComplexMatrix2.matExp (Complex.I • Y) - 1 with hMdef
  have hYs : star Y = Y := hY.1.symm
  have hstars : star s = -s := by
    simp [hs]
  have hstara : star a = a := by
    rw [ha, star_sub, star_one]
    congr 1
    exact Complex.conj_ofReal _
  have hM : M = a • (1 : ComplexMatrix2) + s • Y := by
    rw [hMdef, hexp, ha, sub_smul, one_smul]
    abel
  have hsM : star M = a • (1 : ComplexMatrix2) - s • Y := by
    rw [hM, star_add, star_smul, star_smul, star_one, hYs, hstars, hstara, neg_smul,
      sub_eq_add_neg]
  have hYY : Y * Y = ((r : ℂ) ^ 2) • (1 : ComplexMatrix2) := by rw [← pow_two, hsq]
  have hsinc : (Real.sinc r : ℂ) * (r : ℂ) = (Real.sin r : ℂ) := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (sinc_mul_self_eq_sin r)
  have hpyth : (Real.cos r : ℂ) ^ 2 + (Real.sin r : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (Real.cos_sq_add_sin_sq r)
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hprod : star M * M = ((((2 - 2 * Real.cos r : ℝ)) : ℂ)) • (1 : ComplexMatrix2) := by
    have hexpand : star M * M = (a * a) • (1 : ComplexMatrix2) - (s * s) • (Y * Y) := by
      rw [hsM, hM]
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
        smul_smul]
      rw [mul_comm s a]
      abel
    have hcast : (((2 - 2 * Real.cos r : ℝ)) : ℂ) = 2 - 2 * (Real.cos r : ℂ) := by simp
    rw [hexpand, hYY, smul_smul, ← sub_smul, hcast]
    congr 1
    rw [hs, ha]
    linear_combination hpyth + ((Real.sinc r : ℂ) * (r : ℂ) + (Real.sin r : ℂ)) * hsinc -
      (Real.sinc r : ℂ) ^ 2 * (r : ℂ) ^ 2 * hII
  have hcos : 1 / 2 < Real.cos r := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos]) hr
    rwa [Real.cos_pi_div_three] at h
  have hcos1 : Real.cos r ≤ 1 := Real.cos_le_one r
  have hn : ‖M‖ * ‖M‖ = 2 - 2 * Real.cos r := by
    rw [← CStarRing.norm_star_mul_self, hprod, norm_smul, norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hM0 : 0 ≤ ‖M‖ := norm_nonneg _
  change ‖M‖ < 1
  nlinarith
theorem logSeriesOnSpecialUnitary_holds (hU : ComplexMatrix2.UnitaryLogarithmProperties)
    (hS : ComplexMatrix2.ExpLogSeriesConvergence) (hE : ComplexMatrix2.ExpLogEstimates) :
    LogSeriesOnSpecialUnitary := by
  have first : ∀ u ∈ ComplexMatrix2.specialUnitary, ComplexMatrix2.operatorNorm (u - 1) < 1 →
      Complex.I⁻¹ • ComplexMatrix2.logSeries u ∈ ComplexMatrix2.hermitianTraceless ∧
      ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries u) < Real.pi / 3 ∧
      u ∈ ComplexMatrix2.unitaryLogDomain ∧
      ComplexMatrix2.logSeries u = ComplexMatrix2.unitaryLog u := by
    intro u hu hd
    have hun : u ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.specialUnitaryGroup_le_unitaryGroup hu
    have hdet : u.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hu).2
    obtain ⟨H, -, hlog, hn, -, -, hdet'⟩ := hE.2.2.2.2.2.2.2.1 u hun hd
    obtain ⟨-, hH, -, hlie⟩ := hdet' hdet
    have hY : Complex.I⁻¹ • ComplexMatrix2.logSeries u = H := by
      rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    refine ⟨hY ▸ hH, hY ▸ hn, ⟨hu, fun h => ?_⟩, ?_⟩
    · have h' : u = -1 := h
      rw [h'] at hd
      have htwo : (-1 - 1 : ComplexMatrix2) = (-2 : ℂ) • (1 : ComplexMatrix2) := by
        rw [neg_smul, two_smul]
        abel
      have hnorm : ComplexMatrix2.operatorNorm (-1 - 1 : ComplexMatrix2) = 2 := by
        simp only [ComplexMatrix2.operatorNorm]
        rw [htwo, norm_smul, norm_one]
        simp
      rw [hnorm] at hd
      norm_num at hd
    · rw [hlog, ComplexMatrix2.unitaryLog, ← hlie]
  refine ⟨first, fun Y hY hr => ?_⟩
  have hd := operatorNorm_matExp_sub_one_lt_one hU hY hr
  refine ⟨hd, ?_⟩
  have hSU : ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary :=
    (hU.1 Y hY).2.2.2
  obtain ⟨hm, hn, -, -⟩ := first _ hSU hd
  refine expInjOnBallPi_holds hU _ hm _ hY (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) ?_
  rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  exact (logSeriesNearOne_holds hS hE).2.2.2 _ hd
theorem mul_mul_star_mem_hermitianTraceless {g X : ComplexMatrix2} (hg : star g * g = 1)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    g * X * star g ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← hX.1, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, star_star, mul_assoc]
  · change Matrix.trace (g * X * star g) = 0
    rw [Matrix.trace_mul_comm, ← mul_assoc, hg, one_mul]
    exact hX.2
theorem conjugateBySpecialUnitary_holds (hN : ComplexMatrix2.OperatorNormUnderConjugation) :
    ConjugateBySpecialUnitary := by
  intro g hg
  have hun : g ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.specialUnitaryGroup_le_unitaryGroup hg
  have hdet : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hg).2
  have hunit : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  have hright : g * star g = 1 := Matrix.mem_unitaryGroup_iff.mp hun
  have hleft : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hun
  have hinv : g⁻¹ = star g := Matrix.inv_eq_right_inv hright
  refine ⟨fun X => hN.2.2.2.2.1 g X hunit, fun X => hN.2.1 X g hun, ?_, fun X X' => ?_⟩
  · ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      simp only [ComplexMatrix2.conjugateBy, hinv]
      exact mul_mul_star_mem_hermitianTraceless hleft hX
    · intro hY
      have hs : star (star g) * star g = 1 := by rw [star_star]; exact hright
      refine ⟨star g * Y * star (star g), mul_mul_star_mem_hermitianTraceless hs hY, ?_⟩
      simp only [ComplexMatrix2.conjugateBy, hinv, star_star]
      calc g * (star g * Y * g) * star g = (g * star g) * Y * (g * star g) := by
            simp only [mul_assoc]
        _ = Y := by rw [hright, one_mul, mul_one]
  · have e : ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g X' =
        g * (X * X') * star g := by
      simp only [ComplexMatrix2.conjugateBy, hinv]
      calc g * X * star g * (g * X' * star g) = g * X * (star g * g) * X' * star g := by
            simp only [mul_assoc]
        _ = g * (X * X') * star g := by rw [hleft, mul_one]; simp only [mul_assoc]
    simp only [ComplexMatrix2.fullTrace]
    rw [e, Matrix.trace_mul_comm, ← mul_assoc, hleft, one_mul]
theorem gaugeTransformComp_holds (L m : ℕ) : GaugeTransformComp L m := by
  intro j _ ℬ _ X Y _ _ a b ha hb
  have hdet : ∀ x, IsUnit (a x).det := fun x => by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp (ha x)).2]
    exact isUnit_one
  refine ⟨fun c _ => ?_, fun h c hc => ?_⟩
  · simp only [gaugeTransform, Pi.mul_apply, Matrix.mul_inv_rev, mul_assoc]
  · have e := h c hc
    simp only [gaugeTransform] at e ⊢
    have e1 := Matrix.nonsing_inv_mul (a c.source) (hdet _)
    have e2 := Matrix.nonsing_inv_mul (a c.target) (hdet _)
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hdet _)]
    calc X c = (a c.source)⁻¹ * (a c.source * X c * (a c.target)⁻¹) * a c.target := by
          simp only [mul_assoc, e2, mul_one]
          rw [← mul_assoc, e1, one_mul]
      _ = (a c.source)⁻¹ * b c.source * Y c * ((b c.target)⁻¹ * a c.target) := by
          rw [e]
          simp only [mul_assoc]
theorem secondFDeriv_comp_curve_normed {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (D : Set E) (D' : Set F) (f : E → F) (I : Set ℝ)
    (γ : ℝ → E) (hf : IsC2Between D D' f) (hγ : IsTwiceDiffCurve I γ) (hmaps : MapsTo γ I D) :
    IsTwiceDiffCurve I (f ∘ γ) ∧
      deriv (deriv (f ∘ γ)) 0 =
        secondFDeriv f (γ 0) (deriv γ 0) (deriv γ 0) +
          firstFDeriv f (γ 0) (deriv (deriv γ) 0) := by
  obtain ⟨hD, -, -, hd1, hd2, -⟩ := hf
  obtain ⟨hI, hdγ, hdγ'⟩ := hγ
  obtain ⟨hIo, -, h0⟩ := id hI
  have hγd : ∀ t ∈ I, DifferentiableAt ℝ γ t :=
    fun t ht => (hdγ t ht).differentiableAt (hIo.mem_nhds ht)
  have hfd : ∀ y ∈ D, DifferentiableAt ℝ f y :=
    fun y hy => (hd1 y hy).differentiableAt (hD.mem_nhds hy)
  have hchain : ∀ t ∈ I, HasDerivAt (f ∘ γ) (fderiv ℝ f (γ t) (deriv γ t)) t := fun t ht =>
    (hfd _ (hmaps ht)).hasFDerivAt.comp_hasDerivAt t (hγd t ht).hasDerivAt
  have heq : deriv (f ∘ γ) =ᶠ[𝓝 0] fun t => fderiv ℝ f (γ t) (deriv γ t) := by
    filter_upwards [hIo.mem_nhds h0] with t ht using (hchain t ht).deriv
  have hu : HasDerivAt (fun t => fderiv ℝ f (γ t))
      (fderiv ℝ (fderiv ℝ f) (γ 0) (deriv γ 0)) 0 :=
    ((hd2 _ (hmaps h0)).differentiableAt (hD.mem_nhds (hmaps h0))).hasFDerivAt.comp_hasDerivAt 0
      (hγd 0 h0).hasDerivAt
  have hderiv := (hu.clm_apply hdγ'.hasDerivAt).congr_of_eventuallyEq heq
  exact ⟨⟨hI, fun t ht => (hchain t ht).differentiableAt.differentiableWithinAt,
    hderiv.differentiableAt⟩, hderiv.deriv⟩
section NormOfTopology
variable (E : Type) [AddCommGroup E] [Module ℝ E] [t : TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
def finBasisCoords : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
abbrev coordNormedGroup : NormedAddCommGroup E :=
  NormedAddCommGroup.induced E (Fin (Module.finrank ℝ E) → ℝ) (finBasisCoords E)
    (finBasisCoords E).injective
theorem topology_eq_coordNormedGroup :
    t = (coordNormedGroup E).toMetricSpace.toUniformSpace.toTopologicalSpace :=
  ((finBasisCoords E).toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced)
abbrev topologicalNormedGroup : NormedAddCommGroup E :=
  @NormedAddCommGroup.mk E (coordNormedGroup E).toNorm ‹AddCommGroup E›
    ((coordNormedGroup E).toMetricSpace.replaceTopology (topology_eq_coordNormedGroup E))
    (fun x y => by
      change dist (finBasisCoords E x) (finBasisCoords E y) = ‖finBasisCoords E (-x + y)‖
      rw [dist_comm, dist_eq_norm, map_add, map_neg, neg_add_eq_sub])
abbrev topologicalNormedSpace :
    @NormedSpace ℝ E _ (topologicalNormedGroup E).toSeminormedAddCommGroup :=
  @NormedSpace.mk ℝ E _ (topologicalNormedGroup E).toSeminormedAddCommGroup ‹Module ℝ E›
    (fun a x => by
      change ‖finBasisCoords E (a • x)‖ ≤ ‖a‖ * ‖finBasisCoords E x‖
      rw [map_smul, norm_smul])
end NormOfTopology
theorem secondDerivCompCurve_holds : SecondDerivCompCurve := by
  intro E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ D D' f I γ hf hγ hmaps
  exact @secondFDeriv_comp_curve_normed E F (topologicalNormedGroup E) (topologicalNormedSpace E)
    (topologicalNormedGroup F) (topologicalNormedSpace F) D D' f I γ hf hγ hmaps
def halfTraceReForm : LinearMap.BilinForm ℝ ComplexMatrix2 :=
  LinearMap.mk₂ ℝ (fun X Y => (ComplexMatrix2.halfTrace (X * Y)).re)
    (fun X X' Y => by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, add_mul, Matrix.trace_add, mul_add])
    (fun c X Y => by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]; ring)
    (fun X Y Y' => by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_add, Matrix.trace_add])
    (fun c X Y => by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]; ring)
theorem halfTrace_mul_eq_ofReal_re {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.halfTrace (X * Y) = ((ComplexMatrix2.halfTrace (X * Y)).re : ℂ) := by
  let A : ComplexMatrix2.LieElement := (⟨X, hX⟩ : ↥ComplexMatrix2.hermitianTraceless)
  let B : ComplexMatrix2.LieElement := (⟨Y, hY⟩ : ↥ComplexMatrix2.hermitianTraceless)
  have h : star (ComplexMatrix2.fullTrace (X * Y)) = ComplexMatrix2.fullTrace (X * Y) :=
    ComplexMatrix2.LieElement.star_fullTrace_mul A B
  have h' : (starRingEnd ℂ) (ComplexMatrix2.halfTrace (X * Y)) =
      ComplexMatrix2.halfTrace (X * Y) := by
    have h2 : (starRingEnd ℂ) (ComplexMatrix2.fullTrace (X * Y)) =
        ComplexMatrix2.fullTrace (X * Y) := h
    have h3 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    simp only [ComplexMatrix2.halfTrace, map_mul, h2, h3]
  exact (Complex.conj_eq_iff_re.mp h').symm
theorem isPosDefComplexPairing_of_sum (hU : ComplexMatrix2.UnitaryLogarithmProperties)
    {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] (c : ℝ) (hc : 0 < c)
    (e : ι → V →ₗ[ℝ] ComplexMatrix2) (hsu : ∀ i v, e i v ∈ ComplexMatrix2.hermitianTraceless)
    (hinj : ∀ v, (∀ i, e i v = 0) → v = 0) (p : V → V → ℂ)
    (hp : ∀ v w, p v w = (c : ℂ) * ∑ i, ComplexMatrix2.halfTrace (e i v * e i w)) :
    IsPosDefComplexPairing p := by
  have hB : ∀ v w, (c • ∑ i, halfTraceReForm.compl₁₂ (e i) (e i)) v w =
      c * ∑ i, (ComplexMatrix2.halfTrace (e i v * e i w)).re := by
    intro v w
    simp [LinearMap.sum_apply, halfTraceReForm, smul_eq_mul]
  refine ⟨c • ∑ i, halfTraceReForm.compl₁₂ (e i) (e i), fun v w => ?_, fun v w => ?_,
    fun v hv => ?_⟩
  · rw [hB, hB]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm]
  · rw [hB, hp]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun i _ => halfTrace_mul_eq_ofReal_re (hsu i v) (hsu i w)
  · rw [hB]
    have hsq : ∀ i, (ComplexMatrix2.halfTrace (e i v * e i v)).re =
        ComplexMatrix2.operatorNorm (e i v) ^ 2 := by
      intro i
      have h2 := (hU.1 _ (hsu i v)).1
      rw [← pow_two, h2, halfTrace_smul_one]
      norm_cast
    simp only [hsq]
    have hne : ∃ i, e i v ≠ 0 := by
      by_contra hall
      exact hv (hinj v fun i => by_contra fun h => hall ⟨i, h⟩)
    obtain ⟨i, hi⟩ := hne
    have hpos : 0 < ComplexMatrix2.operatorNorm (e i v) := norm_pos_iff.mpr hi
    exact mul_pos hc (Finset.sum_pos' (fun _ _ => by positivity)
      ⟨i, Finset.mem_univ i, by positivity⟩)
theorem finite_site_of_counts (hC : SiteAndPlaquetteCounts) {L m : ℕ} {j : ℤ} (hL : 0 < L)
    (hj : -(m : ℤ) ≤ j) : Finite (Site L m j) := by
  have h := (hC L m j hL hj).2.2.1
  have h0 : Nat.card (Site L m j) ≠ 0 := by
    rw [h]
    positivity
  exact Nat.finite_of_card_ne_zero h0
theorem finite_bond {L m : ℕ} {j : ℤ} [Finite (Site L m j)] : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
theorem forwardFrom_isPositivelyOriented {L m : ℕ} {j : ℤ} (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
theorem compactBondForm_eq_zero {L m : ℕ} {j : ℤ} (A : compactBondForms L m j)
    (h : ∀ x μ, A.1 (Bond.forwardFrom x μ) = 0) : A = 0 := by
  apply Subtype.ext
  funext b
  obtain ⟨μ, hb | hb⟩ := b.isNeighbour
  · have : b = Bond.forwardFrom b.source μ := Bond.ext rfl (by
      change b.target = b.source + unitStep L m j μ
      rw [← hb]
      abel)
    rw [this]
    exact h _ _
  · have : b.opposite = Bond.forwardFrom b.target μ := Bond.ext rfl (by
      change b.source = b.target + unitStep L m j μ
      have h2 : unitStep L m j μ = b.source - b.target := by
        rw [← neg_sub, hb, neg_neg]
      rw [h2]
      abel)
    have h3 := A.2.2 b
    rw [this, h] at h3
    exact neg_eq_zero.mp h3.symm
theorem stepSpacesPosDefFinDim_holds (hU : ComplexMatrix2.UnitaryLogarithmProperties)
    (hC : SiteAndPlaquetteCounts) {L m K k : ℕ} (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) : StepSpacesPosDefFinDim L m K k := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfs : ∀ n : ℕ, n ≤ K → Finite (SiteAtLevel L m K n) := fun n hn =>
    finite_site_of_counts hC hL0 (by simp only [levelDepth]; omega)
  have s0 := hfs 0 (Nat.zero_le _)
  have s1 := hfs k hk.le
  have s2 := hfs (k + 1) hk
  have b0 : Finite (BondAtLevel L m K 0) := finite_bond
  have b1 : Finite (BondAtLevel L m K k) := finite_bond
  have b2 : Finite (BondAtLevel L m K (k + 1)) := finite_bond
  have hsl : FiniteDimensional ℝ ↥ComplexMatrix2.traceless :=
    Module.Finite.of_injective (ComplexMatrix2.traceless.subtype.restrictScalars ℝ)
      Subtype.val_injective
  let _ : Fintype (SiteAtLevel L m K 0) := Fintype.ofFinite _
  let _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)) := Fintype.ofFinite _
  have hξ : 0 < finestMeshInLevelUnits L k ^ 4 := by
    have : 0 < finestMeshInLevelUnits L k := zpow_pos (by exact_mod_cast hL0) _
    positivity
  refine ⟨?_, ?_, ?_, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · refine isPosDefComplexPairing_of_sum hU (finestMeshInLevelUnits L k ^ 4) hξ
      (fun i : SiteAtLevel L m K 0 × Fin 4 =>
        (LinearMap.proj (Bond.forwardFrom i.1 i.2)).comp (bareBondFormSpace L m K).subtype)
      (fun i v => v.2.1 _ (forwardFrom_isPositivelyOriented _ _))
      (fun v h => compactBondForm_eq_zero v fun x μ => h (x, μ)) _ (fun v w => ?_)
    change ((finestMeshInLevelUnits L k ^ 4 : ℝ) : ℂ) * ∑ᶠ x : SiteAtLevel L m K 0, ∑ μ : Fin 4,
      ComplexMatrix2.halfTrace (bondFormComponent v.1 μ x * bondFormComponent w.1 μ x) = _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    rfl
  · refine isPosDefComplexPairing_of_sum hU (finestMeshInLevelUnits L k ^ 4) hξ
      (fun x : SiteAtLevel L m K 0 =>
        (LinearMap.proj x).comp (bareSiteFieldSpace L m K).subtype)
      (fun x v => v.2 x) (fun v h => Subtype.ext (funext h)) _ (fun v w => ?_)
    change ((finestMeshInLevelUnits L k ^ 4 : ℝ) : ℂ) * ∑ᶠ x : SiteAtLevel L m K 0,
      ComplexMatrix2.halfTrace (v.1 x * w.1 x) = _
    rw [finsum_eq_sum_of_fintype]
    rfl
  · refine isPosDefComplexPairing_of_sum hU 1 one_pos
      (fun c : PositivelyOrientedBond L m (levelDepth K k) =>
        ({ toFun := fun β => ((β.1 c : ↥ComplexMatrix2.traceless) : ComplexMatrix2)
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl } : lieBondSpaceAtLevel L m K k →ₗ[ℝ] ComplexMatrix2))
      (fun c v => v.2 c) (fun v h => Subtype.ext (funext fun c => Subtype.ext (h c))) _
      (fun v w => ?_)
    change ∑ᶠ c : PositivelyOrientedBond L m (levelDepth K k), halfTracePairing (v.1 c) (w.1 c) = _
    rw [finsum_eq_sum_of_fintype, Complex.ofReal_one, one_mul]
    rfl
theorem bondEndpointsInBlocks_split {L m : ℕ} {j j' : ℤ} (hj : j' = j + ((1 : ℕ) : ℤ))
    (h : BondEndpointsInBlocks L m j 1) (b : Bond L m j') :
    (∃ y : Site L m j, (b.source : FourTorus L m) ∈ unitBlock y ∧
        (b.target : FourTorus L m) ∈ unitBlock y) ∨
      ∃ c : Bond L m j, (b.source : FourTorus L m) ∈ unitBlock c.source ∧
        (b.target : FourTorus L m) ∈ unitBlock c.target := by
  subst hj
  rcases h b with hy | ⟨c, hc, -, -⟩
  · exact Or.inl hy
  · exact Or.inr ⟨c, hc⟩
theorem blockPartitionAndPivots_holds (hP : BlockPartition.Properties)
    (hD : DoubleBlockGeometryClaim) (hX : LevelBondOrientationDichotomy) {L m K : ℕ}
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) :
    BlockPartitionAndPivots L m K := by
  refine ⟨by have := hL.2; omega, fun n hn => ?_⟩
  have hj : -(m : ℤ) ≤ levelDepth K (n + 1) := by
    simp only [levelDepth]
    push_cast
    omega
  have hjn : levelDepth K n = levelDepth K (n + 1) + ((1 : ℕ) : ℤ) := by
    simp only [levelDepth]
    push_cast
    ring
  obtain ⟨hdisp, ⟨hself, -, hdisj, hunion⟩, -, -, hends⟩ :=
    hP L m hL hm (levelDepth K (n + 1)) 1 0 hj
  rw [← hjn] at hunion
  obtain ⟨q, hq⟩ := hL.1
  have hh0 : 0 ≤ centreToFaceSteps L := by
    simp only [centreToFaceSteps]
    omega
  have hhL : (centreToFaceSteps L).toNat < L := by
    simp only [centreToFaceSteps]
    omega
  have hstruct : ∀ (c : BondAtLevel L m K (n + 1)) (μ : Fin 4),
      c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
        AxialPathCorridorProperties c μ :=
    ((hD L K m ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hm, rfl⟩).2 n hn).1
  refine ⟨hdisj, hunion, fun y => ?_, fun y => ?_, fun c hc => ?_, fun c c' hc hc' hset => ?_,
    fun b => ?_, fun y => ⟨Bond.forwardFrom y 0, forwardFrom_isPositivelyOriented y 0, rfl⟩⟩
  · have := (hdisp y).2.2
    simpa using this
  · ext x
    constructor
    · rintro ⟨hx, hxl⟩
      by_contra hne
      have hzy : (⟨x, hxl⟩ : SiteAtLevel L m K (n + 1)) ≠ y := fun h => hne (by
        rw [← h]
        rfl)
      exact Set.disjoint_left.mp (hdisj hzy) (hself ⟨x, hxl⟩) hx
    · rintro rfl
      exact ⟨hself y, y.2⟩
  · obtain ⟨μ, hμ⟩ := hc
    have S := hstruct c μ hμ
    refine ⟨fun b => ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨hb, ht, hh⟩
      rw [S.axialPath_eq] at hb
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
      have hsL : s < L := List.mem_range.mp hs
      have hs' := (S.mem_bondCorridor_iff s hsL).1 ⟨ht, hh⟩
      rw [S.pivot_eq, ← hs']
      simp
    · rintro rfl
      have hc' := (S.mem_bondCorridor_iff (centreToFaceSteps L).toNat hhL).2
        (Int.toNat_of_nonneg hh0)
      rw [S.pivot_eq]
      refine ⟨?_, hc'.1, hc'.2⟩
      rw [S.axialPath_eq]
      exact List.mem_map.mpr ⟨_, List.mem_range.mpr hhL, rfl⟩
    · rw [S.pivot_eq]
      exact forwardFrom_isPositivelyOriented _ _
  · rcases Set.pair_eq_pair_iff.mp hset with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Bond.ext h1 h2
    · exfalso
      have hr : c' = c.opposite := Bond.ext h1 h2
      rcases hX L m K hL hm hK (n + 1) (by omega) c with ⟨-, h⟩ | ⟨-, h⟩
      · exact h (hr ▸ hc')
      · exact h hc
  · rcases bondEndpointsInBlocks_split hjn hends b with ⟨y, ht, hh⟩ | ⟨c, ht, hh⟩
    · exact ⟨Bond.forwardFrom y 0, forwardFrom_isPositivelyOriented y 0, Or.inl ht, Or.inl hh⟩
    · obtain ⟨μ, hμ | hμ⟩ := c.isNeighbour
      · exact ⟨c, ⟨μ, hμ⟩, Or.inl ht, Or.inr hh⟩
      · refine ⟨c.opposite, ⟨μ, ?_⟩, Or.inr ht, Or.inl hh⟩
        change c.source - c.target = _
        rw [← neg_sub, hμ, neg_neg]
end ElementaryStepFacts
theorem elementaryStepFacts_holds
    (hU : ComplexMatrix2.UnitaryLogarithmProperties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hS : ComplexMatrix2.ExpLogSeriesConvergence)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hP : BlockPartition.Properties)
    (hD : DoubleBlockGeometryClaim)
    (hX : LevelBondOrientationDichotomy)
    (hC : SiteAndPlaquetteCounts) :
    ElementaryStepFacts := by
  intro L m K k hL hm hk
  exact ⟨⟨ElementaryStepFacts.lieSquareExpFormula_holds hU,
      ElementaryStepFacts.stepSpacesPosDefFinDim_holds hU hC hL hm hk⟩,
    ElementaryStepFacts.expInjOnBallPi_holds hU,
    ElementaryStepFacts.logSeriesNearOne_holds hS hE,
    ElementaryStepFacts.logSeriesOnSpecialUnitary_holds hU hS hE,
    ElementaryStepFacts.conjugateBySpecialUnitary_holds hN,
    ElementaryStepFacts.blockPartitionAndPivots_holds hP hD hX hL hm (by omega),
    ElementaryStepFacts.gaugeTransformComp_holds L m,
    ElementaryStepFacts.secondDerivCompCurve_holds⟩
end YangMills.Construction.PeriodicLattice
