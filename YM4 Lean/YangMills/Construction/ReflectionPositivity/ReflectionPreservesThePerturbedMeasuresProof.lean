import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import YangMills.Construction.ReflectionPositivity.ReflectionPreservesThePerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PerturbedReflInvariance
open PeriodSublattice NormalFamilies
theorem quotientHaar_isProbabilityMeasure (L : PeriodSublattice 1) :
    IsProbabilityMeasure L.quotientHaar := by
  unfold PeriodSublattice.quotientHaar Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem boltzmannWeight_measurable_and_le_one (L : PeriodSublattice 1)
    (hL : L.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β) :
    Measurable (L.boltzmannWeight β) ∧ ∀ U, L.boltzmannWeight β U ≤ 1 := by
  have := hL.finite_quotientPlaquette
  have := Fintype.ofFinite L.QuotientPlaquette
  have hfin : ∀ U, ∑ᶠ q : L.QuotientPlaquette, L.quotientFaceEnergy U q =
      ∑ q : L.QuotientPlaquette, L.quotientFaceEnergy U q := fun U =>
    finsum_eq_sum_of_fintype _
  refine ⟨?_, fun U => ?_⟩
  · have hfun : L.boltzmannWeight β =
        fun U => Real.exp (-β * ∑ q : L.QuotientPlaquette, L.quotientFaceEnergy U q) := by
      funext U
      rw [PeriodSublattice.boltzmannWeight, hfin]
    rw [hfun]
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun q _ => hL.continuous_quotientFaceEnergy q))).measurable
  · have hnn : 0 ≤ ∑ q : L.QuotientPlaquette, L.quotientFaceEnergy U q :=
      Finset.sum_nonneg fun q _ => (hL.quotientFaceEnergy_mem_Icc q U).1
    rw [PeriodSublattice.boltzmannWeight, hfin]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
theorem perturbedReflMeasureInvariant_holds (hQ : PeriodicQuotient.FinitenessClaim)
    (hS : SplitTorusPullbacks) : PerturbedReflMeasureInvariant := by
  intro β hβ L n hn z hs c hc P E hE
  have hL := hQ.1 L
  have hprob := quotientHaar_isProbabilityMeasure L
  obtain ⟨hwm, hw1⟩ := boltzmannWeight_measurable_and_le_one L hL hβ
  have hsym : IsClassIsometry n P.reflectSymmetry.toFun :=
    isClassIsometry_reflectAcross hc
  have hpull := hS β hβ L n hn z hs
  have hinv : Function.Involutive (L.pullbackField P.reflectSymmetry) :=
    (hpull.1 c hc).1
  obtain ⟨hhom, hpres, -, -, -, -, -, -, -, -, hsum, -, -⟩ := hpull.2.1 _ hsym
  set ψ := L.pullbackField P.reflectSymmetry with hψdef
  have hψ : Measurable ψ := hhom.continuous.measurable
  have hEm : Measurable E := Complex.measurable_re.comp hE.1
  obtain ⟨K, hK⟩ := hE.2.1
  have hEK : ∀ U, E U ≤ K := fun U => by
    have h := hK U
    rw [Complex.norm_real] at h
    exact (le_abs_self _).trans h
  set ρ := L.perturbedReflWeight β P E with hρdef
  have hρe : ∀ U, ρ U = Real.exp (E U + E (ψ U)) * L.boltzmannWeight β U := fun _ => rfl
  have hρm : Measurable ρ :=
    (Real.measurable_exp.comp (hEm.add (hEm.comp hψ))).mul hwm
  have hρpos : ∀ U, 0 < ρ U := fun U => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hρle : ∀ U, ρ U ≤ Real.exp (K + K) := fun U => by
    rw [hρe]
    calc Real.exp (E U + E (ψ U)) * L.boltzmannWeight β U
        ≤ Real.exp (E U + E (ψ U)) * 1 :=
          mul_le_mul_of_nonneg_left (hw1 U) (Real.exp_pos _).le
      _ ≤ Real.exp (K + K) := by
          rw [mul_one]
          exact Real.exp_le_exp.mpr (add_le_add (hEK _) (hEK _))
  have hwψ : ∀ U, L.boltzmannWeight β (ψ U) = L.boltzmannWeight β U := fun U => by
    have h := congrFun hsum U
    change L.totalFaceEnergy (ψ U) = L.totalFaceEnergy U at h
    unfold PeriodSublattice.totalFaceEnergy at h
    rw [PeriodSublattice.boltzmannWeight, PeriodSublattice.boltzmannWeight, h]
  have hρψ : ∀ U, ρ (ψ U) = ρ U := fun U => by
    rw [hρe, hρe, hinv U, hwψ, add_comm]
  have hρint : Integrable ρ L.quotientHaar :=
    Integrable.of_bound hρm.aestronglyMeasurable (Real.exp (K + K))
      (ae_of_all _ fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (hρpos U)]
        exact hρle U)
  have hmass : 0 < ∫ U, ρ U ∂L.quotientHaar := by
    rw [integral_pos_iff_support_of_nonneg (fun U => (hρpos U).le) hρint]
    have hsupp : Function.support ρ = Set.univ :=
      Set.eq_univ_of_forall fun U => (hρpos U).ne'
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hν : L.quotientHaar.withDensity (fun U => ENNReal.ofReal (ρ U)) Set.univ =
      ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun U => (hρpos U).le)]
  have hne0 : ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hmass).ne'
  have hnetop : ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hprobρ : IsProbabilityMeasure (L.perturbedReflMeasure β P E) := by
    refine ⟨?_⟩
    change ((ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar))⁻¹ •
      L.quotientHaar.withDensity fun U => ENNReal.ofReal (ρ U)) Set.univ = 1
    rw [Measure.smul_apply, hν, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hne0 hnetop
  refine ⟨hprobρ, hψ, inferInstance, fun F hF ⟨D, hD⟩ => ?_⟩
  have hrepr : ∀ G : L.QuotientField → ℂ, ∫ U, G U ∂(L.perturbedReflMeasure β P E) =
      ((ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar))⁻¹).toReal •
        ∫ U, G U * (ρ U : ℂ) ∂L.quotientHaar := fun G => by
    have hwd := integral_withDensity_eq_integral_toReal_smul (μ := L.quotientHaar)
      (f := fun U => ENNReal.ofReal (ρ U))
      (ENNReal.measurable_ofReal.comp hρm) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) G
    change ∫ U, G U ∂((ENNReal.ofReal (∫ U, ρ U ∂L.quotientHaar))⁻¹ •
      L.quotientHaar.withDensity fun U => ENNReal.ofReal (ρ U)) = _
    rw [integral_smul_measure, hwd]
    refine congrArg _ (integral_congr_ae (ae_of_all _ fun U => ?_))
    change (ENNReal.ofReal (ρ U)).toReal • G U = _
    rw [ENNReal.toReal_ofReal (hρpos U).le, Complex.real_smul, mul_comm]
  rw [hrepr, hrepr]
  refine congrArg _ ?_
  have hFρ : Measurable fun U => F U * (ρ U : ℂ) :=
    hF.mul (Complex.measurable_ofReal.comp hρm)
  have hbd : ∃ B : ℝ, ∀ U, ‖F U * (ρ U : ℂ)‖ ≤ B := ⟨D * Real.exp (K + K), fun U => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos U)]
    exact mul_le_mul (hD U) (hρle U) (hρpos U).le ((norm_nonneg _).trans (hD U))⟩
  have h := hpres.2.2 _ hFρ hbd
  simp only [hρψ] at h
  exact h
end YangMills.Construction.InfiniteLattice.PerturbedReflInvariance
