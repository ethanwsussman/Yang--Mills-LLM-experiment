import YangMills.Construction.InfiniteLattice.ApproximationInTheQuadraticMeanByFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAreReflectionPositiveOnHalfSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (GaugeField IsSymmetricUnder IsRegionMeasurable IsBoundedObservable
  IsLocalObservable IsReflectionPositiveAt LatticeSymmetry LatticeMirror ReflectionClass AmbientSpace)
open ChessboardTori (axialMirror)
open GibbsAtFixedSpacing
namespace HalfSpacePositivity
section QuadraticForm
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
theorem integral_mul_conj_comp_tendsto {s : X → X} (hs : MeasurePreserving s ν ν)
    {F : X → ℂ} {G : ℕ → X → ℂ} (hF : MemLp F 2 ν) (hG : ∀ k, MemLp (G k) 2 ν)
    (hlim : Tendsto (fun k => ∫⁻ x, ‖F x - G k x‖ₑ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, G k x * conj (G k (s x)) ∂ν) atTop
      (𝓝 (∫ x, F x * conj (F (s x)) ∂ν)) := by
  have inner_eq : ∀ {H : X → ℂ} (hH : MemLp H 2 ν),
      inner ℂ (Lp.compMeasurePreserving s hs (hH.toLp H)) (hH.toLp H) =
        ∫ x, H x * conj (H (s x)) ∂ν := by
    intro H hH
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hH.coeFn_toLp, Lp.coeFn_compMeasurePreserving (hH.toLp H) hs,
      hs.quasiMeasurePreserving.ae hH.coeFn_toLp] with x e1 e2 e3
    rw [e1, e2, Function.comp_apply, e3]
    simp [RCLike.inner_apply]
  have hnorm : ∀ k, eLpNorm (G k - F) 2 ν = (∫⁻ x, ‖F x - G k x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Pi.sub_apply]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [enorm_sub_rev]
  have hconv : Tendsto (fun k => (hG k).toLp (G k)) atTop (𝓝 (hF.toLp F)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    simp_rw [hnorm]
    have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    exact hc.comp hlim
  have hT : Continuous (Lp.compMeasurePreserving s hs : Lp ℂ 2 ν → Lp ℂ 2 ν) :=
    (Lp.isometry_compMeasurePreserving hs).continuous
  have hc := ((hT.tendsto _).comp hconv).inner (𝕜 := ℂ) hconv
  simpa only [Function.comp_def, inner_eq] using hc
end QuadraticForm
variable {a : ℝ}
theorem measurePreserving_pullbackField {ν : Measure (GaugeField a)}
    [IsProbabilityMeasure ν] (s : LatticeSymmetry a) (h : IsSymmetricUnder ν s) :
    MeasurePreserving s.pullbackField ν ν := by
  have hval : Continuous fun U : GaugeField a =>
      (U.1 : InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_subtype_val
  have hc : Continuous s.pullbackField :=
    Continuous.subtype_mk (f := fun U : GaugeField a => fun l => U.1 (s.linkMap l))
      (continuous_pi fun l => (continuous_apply _).comp hval) fun U => (s.pullbackField U).2
  have hm : Measurable s.pullbackField := hc.measurable
  refine ⟨hm, Measure.ext fun E hE => ?_⟩
  have hobs : IsBoundedObservable (E.indicator fun _ => (1 : ℂ)) := by
    refine ⟨measurable_const.indicator hE, 1, fun U => ?_⟩
    by_cases hU : U ∈ E <;> simp [hU]
  have h1 := h _ hobs
  have h2 : s.actOn (E.indicator fun _ => (1 : ℂ)) =
      (s.pullbackField ⁻¹' E).indicator fun _ => (1 : ℂ) := by
    funext U
    by_cases hU : s.pullbackField U ∈ E <;>
      simp [LatticeSymmetry.actOn, Set.indicator, hU]
  rw [h2, integral_indicator_const _ (hm hE), integral_indicator_const _ hE] at h1
  have h3 : ν.real (s.pullbackField ⁻¹' E) = ν.real E := by
    simpa using h1
  rw [Measure.map_apply hm hE]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3
theorem integral_conjReflect_mul_self_nonneg
    (hApprox : QuadraticMeanApproximation.Statement)
    (ha : 0 < a) {ν : Measure (GaugeField a)} {P : LatticeMirror a}
    (hR : IsReflectionPositiveAt ν P) (hI : IsSymmetricUnder ν P.symmetry)
    {H : Set AmbientSpace} (hH : P.IsHalfSpace H) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) (hAH : IsRegionMeasurable H A) :
    0 ≤ ∫ U, P.conjReflect A U * A U ∂ν := by
  have : IsProbabilityMeasure ν := hR.1
  have hs := measurePreserving_pullbackField P.symmetry hI
  obtain ⟨Fk, hFk, hconv⟩ := (hApprox a ha ⟨ν, hR.1⟩).2 H A ⟨hAH, hA.2⟩
  have hconv' : Tendsto (fun k => ∫⁻ U, ‖A U - Fk k U‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := hconv.2.2
  have hobs : ∀ k, IsBoundedObservable (Fk (k + 1)) := fun k =>
    ⟨(hFk (k + 1) (by omega)).1.measurable, (hFk (k + 1) (by omega)).2.2.2⟩
  have hmem : ∀ {B : GaugeField a → ℂ}, IsBoundedObservable B → MemLp B 2 ν := by
    rintro B ⟨hm, C, hC⟩
    exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have key := integral_mul_conj_comp_tendsto hs (hmem hA) (fun k => hmem (hobs k))
    ((tendsto_add_atTop_iff_nat 1).2 hconv')
  have hnn : 0 ≤ ∫ U, A U * conj (A (P.symmetry.pullbackField U)) ∂ν := by
    refine ge_of_tendsto' key fun k => ?_
    obtain ⟨-, hloc, hin⟩ := hFk (k + 1) (by omega)
    have hlocal : IsLocalObservable (Fk (k + 1)) := by
      simp only [locallyMeasurableIn, Set.mem_iUnion] at hloc
      obtain ⟨Q, hQ, hF⟩ := hloc
      exact ⟨H ∩ Q, Bornology.IsBounded.subset hQ inter_subset_right, hF.1⟩
    exact hR.2 H hH _ (hobs k) hlocal hin.1
  have heq : (fun U => P.conjReflect A U * A U) =
      fun U => A U * conj (A (P.symmetry.pullbackField U)) :=
    funext fun U => mul_comm _ _
  rw [heq]
  exact hnn
theorem realNormal_axial_dotProduct (α : Fin 4) (x : AmbientSpace) :
    (ReflectionClass.axial α).realNormal ⬝ᵥ x = x α := by
  fin_cases α <;> simp [ReflectionClass.realNormal, ReflectionClass.intNormal, dotProduct,
    Fin.sum_univ_four]
theorem holds
    (hStrong : ChessboardTori.PeriodicStateSymmetries.Statement)
    (hApprox : QuadraticMeanApproximation.Statement) :
    Statement := by
  intro D μ hμ
  let D' : ChessboardTori.ChessboardSetup := ⟨D.toStandingParameters, D.β, D.β_pos⟩
  obtain ⟨h1, h2, -, -⟩ := hStrong D' μ hμ
  refine ⟨h1, fun α c hc => ⟨fun A hA hm => ?_, (h2 α c hc).2⟩, fun α c hc => (h2 α c hc).1⟩
  obtain ⟨hI, hR⟩ := h2 α c hc
  have ha : 0 < D.mesh := by
    have hL : (0 : ℝ) < (D.L : ℝ) := by
      have h := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    exact zpow_pos hL _
  rcases hm with hm | hm
  · refine integral_conjReflect_mul_self_nonneg hApprox ha hR hI
      (H := {x : AmbientSpace | c ≤ x α}) (Or.inl ?_) hA hm
    ext x
    show c ≤ x α ↔ c ≤ (ReflectionClass.axial α).realNormal ⬝ᵥ x
    rw [realNormal_axial_dotProduct]
  · refine integral_conjReflect_mul_self_nonneg hApprox ha hR hI
      (H := {x : AmbientSpace | x α ≤ c}) (Or.inr ?_) hA hm
    ext x
    show x α ≤ c ↔ (ReflectionClass.axial α).realNormal ⬝ᵥ x ≤ c
    rw [realNormal_axial_dotProduct]
end HalfSpacePositivity
end YangMills.Construction.MultipleReflections
end
