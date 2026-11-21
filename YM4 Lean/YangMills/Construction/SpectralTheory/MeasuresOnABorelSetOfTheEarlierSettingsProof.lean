import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.MeasuresOnABorelSetOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.SpectralPushforwardLemmas
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.BorelSetComparison
open YangMills.Construction.BorelSpectral YangMills.Construction.SettingsComparison
open YangMills.Construction.BorelCalculus (BoundedFunctionalCalculus IsBoundedFn)
open YangMills.Construction.SpectralTheorem (IsSpectralIntegralOf spectralIntegralOp)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {d : ℕ} {S : Set (Fin d → ℝ)}
theorem isStarProjection_of_isProjectionCLM {P : H →L[ℂ] H}
    (hP : OperatorTransport.IsProjectionCLM P) : IsStarProjection P := by
  refine ⟨hP.2, ?_⟩
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  exact (hP.1 x y).symm
theorem isProjectionCLM_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    OperatorTransport.IsProjectionCLM P := by
  refine ⟨fun x y => ?_, hP.isIdempotentElem.eq⟩
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint) x y).symm
omit [CompleteSpace H] in
theorem inner_apply_eq_norm_sq {P : H →L[ℂ] H}
    (hP : OperatorTransport.IsProjectionCLM P) (v : H) :
    ⟪v, P v⟫_ℂ = ((‖P v‖ ^ 2 : ℝ) : ℂ) := by
  have hidem : P (P v) = P v := congrArg (fun T : H →L[ℂ] H => T v) hP.2
  have hsw : ⟪v, P v⟫_ℂ = ⟪P v, P v⟫_ℂ := by
    have := hP.1 v (P v)
    rw [hidem] at this
    exact this
  rw [hsw, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem exists_spectralMeasure_of_isProjValued (hd : 1 ≤ d) (hS : MeasurableSet S)
    (Q : BorelSubsets S → H → H) (hQ : IsProjValuedBorelMeasure Q) :
    ∃ M : SpectralMeasure S H, valueFn M = Q := by
  have hex : ∀ U, ∃ P : H →L[ℂ] H, ⇑P = Q U ∧ OperatorTransport.IsProjectionCLM P :=
    hQ.proj
  choose P hPQ hPp using hex
  refine ⟨⟨hd, hS, P, fun U => isStarProjection_of_isProjectionCLM (hPp U), ?_, ?_, ?_⟩,
    funext hPQ⟩
  · ext v
    rw [hPQ, hQ.apply_univ]
    rfl
  · intro U V
    ext v
    rw [hPQ, hQ.apply_inter]
    change _ = P U (P V v)
    rw [hPQ, hPQ]
    rfl
  · intro v U hdisj
    have hnorm : ∀ V : BorelSubsets S, ⟪v, P V v⟫_ℂ = ((‖P V v‖ ^ 2 : ℝ) : ℂ) := fun V =>
      inner_apply_eq_norm_sq (hPp V) v
    have hQnorm : ∀ V : BorelSubsets S, ⟪v, Q V v⟫_ℂ = ((‖P V v‖ ^ 2 : ℝ) : ℂ) := fun V => by
      rw [← hPQ]
      exact hnorm V
    have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, ((‖P (U j) v‖ ^ 2 : ℝ) : ℂ)) atTop
        (𝓝 ((‖P ⟨⋃ k, (U k).1, MeasurableSet.iUnion fun k => (U k).2⟩ v‖ ^ 2 : ℝ) : ℂ)) := by
      have hca := hQ.diag_countablyAdditive v U hdisj
      simp only [hQnorm] at hca
      exact hca
    have hlimRe : Tendsto (fun N => ∑ j ∈ Finset.range N, ‖P (U j) v‖ ^ 2) atTop
        (𝓝 (‖P ⟨⋃ k, (U k).1, MeasurableSet.iUnion fun k => (U k).2⟩ v‖ ^ 2)) := by
      have hre := (Complex.continuous_re.tendsto _).comp hlim
      rw [Complex.ofReal_re] at hre
      refine hre.congr fun N => ?_
      simp only [Function.comp_apply, Complex.re_sum, Complex.ofReal_re]
    have hsumR := (hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity) _).mpr hlimRe
    have hsumC := Complex.hasSum_ofReal.mpr hsumR
    simp only [hnorm]
    exact hsumC
theorem isProjValued_valueFn (M : SpectralMeasure S H) :
    IsProjValuedBorelMeasure (valueFn M) where
  proj U := ⟨M U, rfl, isProjectionCLM_of_isStarProjection (M.isStarProjection U)⟩
  apply_univ := by
    funext v
    simp [valueFn, M.map_univ]
  apply_inter U V := by
    funext v
    simp [valueFn, M.map_inter]
  diag_countablyAdditive v U hU := (M.countablyAdditive v U hU).tendsto_sum_nat
theorem measurable_truncate {f : S → ℂ} (hf : Measurable f) (m : ℕ) :
    Measurable (truncate f m) :=
  hf.indicator (measurableSet_le hf.norm measurable_const)
theorem isBoundedFn_truncate (f : S → ℂ) (m : ℕ) : IsBoundedFn (truncate f m) := by apply _root_.YangMills.Construction.SpectralPushforward.isBoundedFn_truncate <;> assumption
theorem isBoundedIntegralViaCoeffs_iff
    (hcal : SpectralMeasureCalculus.CalculusTheorem)
    (M : SpectralMeasure S H) (f : S → ℂ) (hf : Measurable f)
    (hfb : IsBoundedFn f) (T : H →L[ℂ] H) :
    IsBoundedIntegralViaCoeffs M f T ↔ T = M.integralOp f := by
  have hbd := (hcal H d S M).2.1
  constructor
  · intro hT
    exact (hbd.existsUnique_operator f hf hfb).unique hT (hbd.inner_eq f hf hfb)
  · rintro rfl
    exact hbd.inner_eq f hf hfb
theorem isDiagonalIntegral_iff
    (hbc : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (M : SpectralMeasure S H) (f : S → ℂ) (hf : Measurable f)
    (hfb : IsBoundedFn f) (T : H →L[ℂ] H) :
    M.IsDiagonalIntegral f T ↔ T = M.integralOp f := by
  have huniq := (hbc H d S M).existsUnique_op f hf hfb
  have hspec : M.IsDiagonalIntegral f (M.integralOp f) :=
    Classical.epsilon_spec huniq.exists
  exact ⟨fun hT => huniq.unique hT hspec, fun hT => hT ▸ hspec⟩
theorem borelSetMeasuresAgree_of
    (hcal : SpectralMeasureCalculus.CalculusTheorem)
    (hbc : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℕ)
    (S : Set (Fin d → ℝ)) (hd : 1 ≤ d) (hS : MeasurableSet S) :
    BorelSetMeasuresAgree H S where
  isProjValued_iff Q := ⟨exists_spectralMeasure_of_isProjValued hd hS Q, by
    rintro ⟨M, rfl⟩
    exact isProjValued_valueFn M⟩
  matrixCoeff_self M v U := M.inner_apply_self_eq_diagMeasure v U
  fnIsCarriedBy_iff M C := by
    constructor
    · intro hC
      exact DFunLike.coe_injective hC
    · intro hC
      funext v
      exact congrArg (fun T : H →L[ℂ] H => T v) hC
  boundedViaCoeffs_iff M f hf hfb T :=
    (isBoundedIntegralViaCoeffs_iff hcal M f hf hfb T).trans
      (isDiagonalIntegral_iff hbc M f hf hfb T).symm
  boundedViaCoeffs_iff_eq M f hf hfb T := isBoundedIntegralViaCoeffs_iff hcal M f hf hfb T
  viaCoeffs_iff M f hf D := by
    have hall := (hcal H d S M).2.2.1
    constructor
    · rintro ⟨hdom, T, hT, hlim⟩
      refine ⟨hdom, fun v => ?_⟩
      have hTm : ∀ m, T m = M.integralOp (truncate f m) := fun m =>
        (isBoundedIntegralViaCoeffs_iff hcal M (truncate f m) (measurable_truncate hf m)
          (isBoundedFn_truncate f m) (T m)).mp (hT m)
      have hl := hlim v
      simp only [hTm] at hl
      exact hl.limUnder_eq.symm
    · rintro ⟨hdom, hval⟩
      refine ⟨hdom, fun m => M.integralOp (truncate f m), fun m => ?_, fun v => ?_⟩
      · exact (isBoundedIntegralViaCoeffs_iff hcal M (truncate f m) (measurable_truncate hf m)
          (isBoundedFn_truncate f m) _).mpr rfl
      · rw [hval v]
        exact hall.tendsto_truncation f hf v ((hdom v).mp v.2)
  setIntegralOp_spec M C f hf _ := by
    have hI := (hcal H d S M).2.2.1.isIntegralOf (zeroExtend C.1 f)
      (measurable_zeroExtend C.2 hf)
    exact ⟨hI.1, hI.2⟩
  valueFn_pushforward M _ _ hd' hS' κ hκ U := rfl
  valueFn_extendCarrier M _ hSS hS' U := rfl
  integralOf_matrixCoeff M f x y hf hI := (hcal H d S M).1.integral_eq f x y hf hI
theorem borelSetMeasuresAgreeForAllSpaces_holds
    (hcal : SpectralMeasureCalculus.CalculusTheorem)
    (hbc : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) :
    BorelSetMeasuresAgreeForAllSpaces :=
  fun H _ _ _ d S hd hS _ => borelSetMeasuresAgree_of hcal hbc H d S hd hS
end YangMills.Construction.BorelSetComparison
