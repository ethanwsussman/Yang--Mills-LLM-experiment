import YangMills.Construction.ChessboardTori.InvarianceUnderTheGroupsOfGridsProof
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.FormsOfTheWilsonSpecificationOfAWindow
import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitions
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.InfiniteLattice.SumsIntegralsAndImageMeasuresOfTheStatesAreFormed
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.WellDefinedStates
variable {a : ℝ}
theorem partitionFunction_pos (β : ℝ) (Λ : Finset (Link a)) (U : GaugeField a)
    (hprob : IsProbabilityMeasure (wilsonSpecification β Λ U)) :
    0 < partitionFunction β Λ U := by
  by_contra hZ
  have hZ0 : ENNReal.ofReal (partitionFunction β Λ U) = 0 :=
    ENNReal.ofReal_of_nonpos (not_lt.mp hZ)
  have hm := hprob.measure_univ
  rw [wilsonSpecification, hZ0, ENNReal.inv_zero, Measure.smul_apply, smul_eq_mul] at hm
  by_cases hx : ((Matrices.ComplexMatrix2.haarPi Λ).withDensity fun v =>
      ENNReal.ofReal (boltzmannWeight β Λ U v)) univ = 0
  · rw [hx] at hm
    simp at hm
  · rw [ENNReal.top_mul hx] at hm
    simp at hm
theorem measurable_eval (b : Link a) : Measurable fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval <;> assumption
theorem exteriorSigma_le (Λ : Finset (Link a)) :
    exteriorSigma Λ ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  iSup₂_le fun b _ => (measurable_eval b).comap_le
theorem measurable_restrictTo (Λ : Finset (Link a)) : Measurable (restrictTo Λ) :=
  measurable_pi_iff.mpr fun b => measurable_eval b.1
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem isBoundedObservable_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    IsBoundedObservable F := by
  have := compactSpace_gaugeField (a := a)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨hF.measurable, C, fun U => hC U (mem_univ U)⟩
theorem isBoundedObservable_actOn (g : LatticeSymmetry a) (hg : Continuous g.pullbackField)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : IsBoundedObservable (g.actOn F) := by apply _root_.YangMills.Construction.ChessboardTori.GridGroupInvariance.isBoundedObservable_actOn <;> assumption
theorem isBoundedObservable_mul_conjReflect (P : LatticeMirror a)
    (hg : Continuous P.symmetry.pullbackField)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable fun U => F U * P.conjReflect F U := by
  obtain ⟨hm', C', hC'⟩ := isBoundedObservable_actOn P.symmetry hg hF
  obtain ⟨hm, C, hC⟩ := hF
  have hconj : Measurable (P.conjReflect F) := Complex.continuous_conj.measurable.comp hm'
  refine ⟨hm.mul hconj, C * C', fun U => ?_⟩
  rw [norm_mul]
  have h2 : ‖P.conjReflect F U‖ ≤ C' := by
    rw [LatticeMirror.conjReflect, Complex.norm_conj]
    exact hC' U
  exact mul_le_mul (hC U) h2 (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem exists_isHalf (L m : ℕ) (j : ℤ) (hL : 0 < L) (P : PeriodicMirror L m j) :
    ∃ H, P.IsHalf H := by
  have hℓ : 0 < PeriodicLattice.torusSide L m := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    unfold PeriodicLattice.torusSide
    positivity
  set ℓ := PeriodicLattice.torusSide L m with hℓdef
  refine ⟨_, TorusMetric.torusProj ℓ fun _ => P.level + ℓ / 4, ?_, rfl⟩
  rintro ⟨y, hy, hyx⟩
  have h0 : ((y P.axis - (P.level + ℓ / 4) : ℝ) : AddCircle ℓ) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact congrFun hyx P.axis
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff ℓ).mp h0
  rw [zsmul_eq_mul] at hn
  rcases hy with h | h
  · have h' : y P.axis = P.level := h
    have h3 : (4 * (n : ℝ) + 1) * ℓ = 0 := by
      rw [h'] at hn
      linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have : 4 * n + 1 = 0 := by exact_mod_cast h4
      omega
    · exact hℓ.ne' h4
  · have h' : y P.axis = P.level + ℓ / 2 := h
    have h3 : (4 * (n : ℝ) - 1) * ℓ = 0 := by
      rw [h'] at hn
      linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have : 4 * n - 1 = 0 := by exact_mod_cast h4
      omega
    · exact hℓ.ne' h4
theorem holds (h₁ : SmearedEnergyAndSymmetryAction.Main)
    (h₂ : WindowSpecificationForms.Statement)
    (h₃ : FixedSpacing.FixedSpacingDictionary) : Statement := by
  refine ⟨fun a ha => ?_, fun L K m hL hK hm β hβ => ?_, exists_isHalf⟩
  · obtain ⟨⟨hc, hr⟩, hact, -, -⟩ := h₁ a ha
    have hcont : ∀ g : LatticeSymmetry a, Continuous g.pullbackField :=
      fun g => (hact g).2.2.1
    refine ⟨fun β hβ Λ hΛ => ?_, hc, hr, fun F hF => ⟨fun g => ?_, fun P => ?_⟩,
      fun F hF => isBoundedObservable_of_continuous hF⟩
    · refine ⟨WilsonOperator.facesTouching_finite Λ, fun U => ?_, exteriorSigma_le Λ,
        measurable_restrictTo Λ⟩
      have hp : IsProbabilityMeasure (wilsonSpecification β Λ U) :=
        (h₂ a ha β hβ ⟨Λ, hΛ⟩ U).2.1
      exact ⟨partitionFunction_pos β Λ U hp, hp⟩
    · exact isBoundedObservable_actOn g (hcont g) hF
    · exact isBoundedObservable_mul_conjReflect P (hcont _) hF
  · exact (h₃ L K hL hK β hβ).2.1.2.1 m hm |>.2.2.2
end YangMills.Construction.InfiniteLattice.WellDefinedStates
