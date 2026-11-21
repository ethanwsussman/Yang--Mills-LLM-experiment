import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.InvariantDensitiesOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfOneLatticeAndTheirAction
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ThreePropertiesOfTheWilsonKernel
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace LatticePhases.InvariantDensities
section Observables
variable {a : ℝ}
theorem integrable_of_isBoundedObservable (μ : Measure (GaugeField a)) [IsFiniteMeasure μ]
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) : Integrable A μ := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem isBoundedObservable_mul {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => A U * B U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
theorem isBoundedObservable_of_shiftInvariant {f : GaugeField a → ℂ}
    (hm : Measurable[shiftInvariantSigma a] f) (hb : ∃ C : ℝ, ∀ U, ‖f U‖ ≤ C) :
    IsBoundedObservable f :=
  ⟨hm.mono (fun _ hs => hs.1) le_rfl, hb⟩
theorem norm_le_supNorm {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (U : GaugeField a) : ‖A U‖ ≤ observableSupNorm A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem supNorm_nonneg (A : GaugeField a → ℂ) : 0 ≤ observableSupNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_integral_mul_sub_integral_mul_le (μ : Measure (GaugeField a)) [IsFiniteMeasure μ]
    {f g G : GaugeField a → ℂ} (hf : IsBoundedObservable f) (hg : IsBoundedObservable g)
    (hG : IsBoundedObservable G) :
    ‖(∫ U, f U * G U ∂μ) - ∫ U, g U * G U ∂μ‖ ≤ observableSupNorm G * ∫ U, ‖f U - g U‖ ∂μ := by
  have i₁ := integrable_of_isBoundedObservable μ (isBoundedObservable_mul hf hG)
  have i₂ := integrable_of_isBoundedObservable μ (isBoundedObservable_mul hg hG)
  have i₃ : Integrable (fun U => ‖f U - g U‖) μ :=
    ((integrable_of_isBoundedObservable μ hf).sub (integrable_of_isBoundedObservable μ hg)).norm
  rw [← integral_sub i₁ i₂, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (i₃.const_mul _) (ae_of_all _ fun U => ?_)
  rw [← sub_mul, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_le_supNorm hG U) (norm_nonneg _)
theorem integral_norm_sub_actOn (μ : Measure (GaugeField a)) (s : LatticeSymmetry a)
    (hμ : IsSymmetricUnder μ s) {f g : GaugeField a → ℂ} (hfix : s.actOn f = f)
    (hf : IsBoundedObservable f) (hg : IsBoundedObservable g) :
    ∫ U, ‖f U - s.actOn g U‖ ∂μ = ∫ U, ‖f U - g U‖ ∂μ := by
  have hA : IsBoundedObservable fun U => ((‖f U - g U‖ : ℝ) : ℂ) := by
    obtain ⟨hm, C, hC⟩ := hf
    obtain ⟨hm', C', hC'⟩ := hg
    refine ⟨Complex.measurable_ofReal.comp (hm.sub hm').norm, C + C', fun U => ?_⟩
    rw [Complex.norm_real, norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hC U) (hC' U))
  have key := hμ _ hA
  have e : ∀ U, s.actOn (fun U => ((‖f U - g U‖ : ℝ) : ℂ)) U =
      ((‖f U - s.actOn g U‖ : ℝ) : ℂ) := fun U => by
    have := congrFun hfix U
    simp only [LatticeSymmetry.actOn] at this ⊢
    rw [this]
  simp only [e] at key
  rw [integral_complex_ofReal, integral_complex_ofReal] at key
  exact_mod_cast key
end Observables
theorem exists_continuousLocal_integral_norm_sub_lt (D : Setup) (T : TopologyDensity D)
    (ρ : ProbMeasure (GaugeField D.mesh)) {f : GaugeField D.mesh → ℂ}
    (hf : IsBoundedObservable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ H ∈ continuousLocalFunctions D.mesh, ∫ U, ‖f U - H U‖ ∂ρ.toMeasure < ε := by
  have := T.compact
  have hi := integrable_of_isBoundedObservable ρ.toMeasure hf
  obtain ⟨Z, ⟨G, hG⟩, hZ⟩ :=
    (T.dense_Lp1 ρ).exists_dist_lt (hi.toL1 f : ρ.Lp1) (half_pos hε)
  obtain ⟨H, hH, hGH⟩ := T.dense_local.2 G G.continuous (ε / 2) (half_pos hε)
  have hHc : Continuous H := hH.2.2
  have hcont : Continuous fun U => ‖(⇑G - H) U‖ := (G.continuous.sub hHc).norm
  have hsup : ∀ U, ‖G U - H U‖ ≤ uniformSup (⇑G - H) := fun U =>
    le_ciSup (f := fun U => ‖(⇑G - H) U‖) (isCompact_range hcont).bddAbove U
  have hdist : ∫ U, ‖f U - G U‖ ∂ρ.toMeasure = dist (hi.toL1 f : ρ.Lp1) Z := by
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (hi.toL1 f : ρ.Lp1) Z, hi.coeFn_toL1, hG] with U e₁ e₂ e₃
    rw [e₁, Pi.sub_apply, e₂, e₃]
  have iG : Integrable (fun U => ‖f U - G U‖) ρ.toMeasure :=
    (hi.sub (G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).norm
  have iH : Integrable (fun U => ‖f U - H U‖) ρ.toMeasure :=
    (hi.sub (integrable_of_isBoundedObservable ρ.toMeasure hH.1)).norm
  refine ⟨H, hH, ?_⟩
  calc ∫ U, ‖f U - H U‖ ∂ρ.toMeasure
      ≤ ∫ U, (‖f U - G U‖ + uniformSup (⇑G - H)) ∂ρ.toMeasure := by
        refine integral_mono iH (iG.add (integrable_const _)) fun U => ?_
        calc ‖f U - H U‖ = ‖(f U - G U) + (G U - H U)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖f U - G U‖ + ‖G U - H U‖ := norm_add_le _ _
          _ ≤ ‖f U - G U‖ + uniformSup (⇑G - H) := add_le_add le_rfl (hsup U)
    _ = dist (hi.toL1 f : ρ.Lp1) Z + uniformSup (⇑G - H) := by
        rw [integral_add iG (integrable_const _), hdist]
        simp
    _ < ε := by linarith
theorem exists_shift_avoidsLinkEndpoints (D : Setup) (W : OrientedLinkSet D.mesh)
    {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    ∃ v : LatticePoint D.mesh,
      WilsonKernelProperties.AvoidsLinkEndpoints W ((shift v).setImage S) := by
  set E : Set AmbientSpace :=
    (fun b : Link D.mesh => (b.initial : AmbientSpace)) '' (W.links : Set (Link D.mesh)) ∪
    (fun b : Link D.mesh => (b.terminal : AmbientSpace)) '' (W.links : Set (Link D.mesh)) with hE
  have hEf : E.Finite :=
    ((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _)
  obtain ⟨r, hr⟩ := (hS.union hEf.isBounded).subset_closedBall (0 : AmbientSpace)
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * r / D.mesh)
  have hm' : 2 * r < m * D.mesh := (div_lt_iff₀ D.mesh_pos).mp hm
  have bound : ∀ x ∈ S ∪ E, |x 0| ≤ r := fun x hx => by
    have h₁ := hr hx
    rw [mem_closedBall_zero_iff] at h₁
    exact (norm_le_pi_norm x 0).trans h₁
  have off : ∀ y ∈ E, y ∉ (shift ((m : ℤ) • axisStep D.mesh 0)).setImage S := by
    rintro y hy ⟨x, hx, rfl⟩
    have h₁ := abs_le.mp (bound x (Or.inl hx))
    have h₂ := abs_le.mp (bound _ (Or.inr hy))
    have e : ((shift ((m : ℤ) • axisStep D.mesh 0)).toFun x) 0 = x 0 + m * D.mesh := by
      simp [shift, axisStep]
    rw [e] at h₂
    linarith [h₁.1, h₂.2]
  exact ⟨(m : ℤ) • axisStep D.mesh 0, fun b hb =>
    ⟨off _ (Or.inl ⟨b, hb, rfl⟩), off _ (Or.inr ⟨b, hb, rfl⟩)⟩⟩
theorem integral_mul_shift_actOn_eq {a : ℝ} (μ : Measure (GaugeField a))
    (hinv : IsShiftInvariant μ) {f : GaugeField a → ℂ}
    (hfix : ∀ v : LatticePoint a, (shift v).actOn f = f) (hf : IsBoundedObservable f)
    (v : LatticePoint a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    ∫ U, f U * (shift v).actOn F U ∂μ = ∫ U, f U * F U ∂μ := by
  have key := hinv v _ (isBoundedObservable_mul hf hF)
  have e : ∀ U, (shift v).actOn (fun U => f U * F U) U = f U * (shift v).actOn F U := fun U => by
    have := congrFun (hfix v) U
    simp only [LatticeSymmetry.actOn] at this ⊢
    rw [this]
  simp only [e] at key
  exact key
theorem integral_mul_heatBath_eq (D : Setup) (K : WilsonKernelProperties.Statement)
    (C : LatticeSymmetryAction.ActionPreservesNormContinuityLocality D)
    (M : LatticeSymmetryAction.SymmetriesAreMotions D)
    (T : TopologyDensity D) (ρ : ProbMeasure (GaugeField D.mesh))
    (hinv : IsShiftInvariant ρ.toMeasure)
    (hkeep : GibbsKernelsAndSymmetries.HeatBathInvariant D.β ρ)
    {f : GaugeField D.mesh → ℂ} (hfix : ∀ v : LatticePoint D.mesh, (shift v).actOn f = f)
    (hf : IsBoundedObservable f) (W : OrientedLinkSet D.mesh) {F : GaugeField D.mesh → ℂ}
    (hF : F ∈ continuousLocalFunctions D.mesh) :
    ∫ U, f U * W.heatBath D.β F U ∂ρ.toMeasure = ∫ U, f U * F U ∂ρ.toMeasure := by
  obtain ⟨-, ⟨-, -, hγ⟩, hpass, -⟩ := K D W D.β D.β D.β_pos D.β_pos F hF
  have hFo : IsBoundedObservable F := hF.1
  have hGo : IsBoundedObservable (W.heatBath D.β F) := hγ.1
  have hcpos : 0 < observableSupNorm (W.heatBath D.β F) + observableSupNorm F + 1 :=
    add_pos_of_nonneg_of_pos
      (add_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) one_pos
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  obtain ⟨H, hH, hnear⟩ := exists_continuousLocal_integral_norm_sub_lt D T ρ hf (div_pos hε hcpos)
  obtain ⟨S, hSb, hSm⟩ := hH.2.1
  obtain ⟨v, hv⟩ := exists_shift_avoidsLinkEndpoints D W hSb
  have hmot : (shift v).toFun ∈ latticeMotions D.mesh := by
    rw [← M]
    exact ⟨_, rfl⟩
  obtain ⟨-, -, hloc⟩ := C (shift v) hmot H hH.1
  obtain ⟨hH'c, hH's⟩ := hloc S ⟨hH, hH.1, hSm⟩
  have hd := integral_norm_sub_actOn ρ.toMeasure (shift v) (hinv v) (hfix v) hf hH.1
  have hprod : (fun U => (shift v).actOn H U * F U) ∈ continuousLocalFunctions D.mesh := by
    obtain ⟨A, hA⟩ := T.exists_nonUnitalSubalgebra
    have m₁ : (shift v).actOn H ∈ A := by
      rw [← SetLike.mem_coe, hA]
      exact hH'c
    have m₂ : F ∈ A := by
      rw [← SetLike.mem_coe, hA]
      exact hF
    rw [← hA]
    exact A.mul_mem m₁ m₂
  have hmid : ∫ U, (shift v).actOn H U * W.heatBath D.β F U ∂ρ.toMeasure =
      ∫ U, (shift v).actOn H U * F U ∂ρ.toMeasure := by
    have e := hkeep W _ hprod
    rw [hpass _ _ hH'c hH's hv] at e
    exact e
  have b₁ := norm_integral_mul_sub_integral_mul_le ρ.toMeasure hf hH'c.1 hGo
  have b₂ := norm_integral_mul_sub_integral_mul_le ρ.toMeasure hf hH'c.1 hFo
  rw [hd] at b₁ b₂
  have hnn : 0 ≤ ∫ U, ‖f U - H U‖ ∂ρ.toMeasure := integral_nonneg fun _ => norm_nonneg _
  have hlt : (observableSupNorm (W.heatBath D.β F) + observableSupNorm F + 1) *
      ∫ U, ‖f U - H U‖ ∂ρ.toMeasure ≤ ε := by
    have := (lt_div_iff₀' hcpos).mp hnear
    exact this.le
  calc ‖(∫ U, f U * W.heatBath D.β F U ∂ρ.toMeasure) - ∫ U, f U * F U ∂ρ.toMeasure‖
      = ‖((∫ U, f U * W.heatBath D.β F U ∂ρ.toMeasure) -
            ∫ U, (shift v).actOn H U * W.heatBath D.β F U ∂ρ.toMeasure) -
          ((∫ U, f U * F U ∂ρ.toMeasure) -
            ∫ U, (shift v).actOn H U * F U ∂ρ.toMeasure)‖ := by
        rw [hmid, sub_sub_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
    _ ≤ observableSupNorm (W.heatBath D.β F) * (∫ U, ‖f U - H U‖ ∂ρ.toMeasure) +
          observableSupNorm F * ∫ U, ‖f U - H U‖ ∂ρ.toMeasure := add_le_add b₁ b₂
    _ ≤ (observableSupNorm (W.heatBath D.β F) + observableSupNorm F + 1) *
          ∫ U, ‖f U - H U‖ ∂ρ.toMeasure := by nlinarith
    _ ≤ ε := hlt
theorem densityMeasure_isProb_and_integral {a : ℝ} (μ : Measure (GaugeField a))
    [IsProbabilityMeasure μ] {f : GaugeField a → ℂ} (hf : IsBoundedObservable f)
    (hpos : ∀ U, (f U).im = 0 ∧ 0 ≤ (f U).re) (hone : ∫ U, f U ∂μ = 1) :
    IsProbabilityMeasure (densityMeasure μ f) ∧
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂(densityMeasure μ f) = ∫ U, f U * F U ∂μ := by
  have hreal : ∀ U, f U = (((f U).re : ℝ) : ℂ) := fun U =>
    Complex.ext (by simp) (by simp [(hpos U).1])
  have hm : Measurable fun U => ENNReal.ofReal (f U).re :=
    (Complex.measurable_re.comp hf.1).ennreal_ofReal
  have ire : Integrable (fun U => (f U).re) μ := (integrable_of_isBoundedObservable μ hf).re
  have hint : ∫ U, (f U).re ∂μ = 1 := by
    have e : ∫ U, f U ∂μ = ((∫ U, (f U).re ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ hreal)
    rw [hone] at e
    exact_mod_cast e.symm
  refine ⟨⟨?_⟩, fun F _ => ?_⟩
  · rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ire (ae_of_all _ fun U => (hpos U).2), hint]
    simp
  · rw [densityMeasure,
      integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    show (ENNReal.ofReal (f U).re).toReal • F U = f U * F U
    rw [ENNReal.toReal_ofReal (hpos U).2, Complex.real_smul, ← hreal U]
theorem invariantDensityLaws_holds (hGibbs : GibbsKernelsAndSymmetries.Assertion)
    (hInvariant : InvariantFunctionsAndErgodicity)
    (hSymmetries : LatticeSymmetryAction.SymmetryActionFacts)
    (hKernel : WilsonKernelProperties.Statement)
    (hTopology : TopologyDensityHolds) : InvariantDensityLaws := by
  intro D ν f hm hb
  have hper : IsPeriodicGibbs D.β ν.1 := ν.2
  have hprob : IsProbabilityMeasure ν.1 := hper.1.1
  let ρ : ProbMeasure (GaugeField D.mesh) :=
    (⟨ν.1, hprob⟩ : ProbabilityMeasure (GaugeField D.mesh))
  obtain ⟨hiff, hsym, -, -⟩ := hGibbs D D.β D.β_pos
  have hkeep := (hiff ρ).mp hper.1
  have hinv : IsShiftInvariant ρ.toMeasure := (hsym ρ hper).2.1
  have hfix := fun v => (hInvariant D).1 f hm v
  obtain ⟨⟨hM, -⟩, ⟨hPull, -⟩, -, -, hC⟩ := hSymmetries D
  have hf : IsBoundedObservable f := isBoundedObservable_of_shiftInvariant hm hb
  have first : ∀ (W : OrientedLinkSet D.mesh) (F : GaugeField D.mesh → ℂ),
      F ∈ continuousLocalFunctions D.mesh →
        ∫ U, f U * W.heatBath D.β F U ∂ρ.toMeasure = ∫ U, f U * F U ∂ρ.toMeasure :=
    fun W F hF => integral_mul_heatBath_eq D hKernel hC hM (hTopology D) ρ hinv hkeep hfix hf W hF
  have second : ∀ (v : LatticePoint D.mesh) (F : GaugeField D.mesh → ℂ), IsBoundedObservable F →
      ∫ U, f U * (shift v).actOn F U ∂ρ.toMeasure = ∫ U, f U * F U ∂ρ.toMeasure :=
    fun v F hF => integral_mul_shift_actOn_eq ρ.toMeasure hinv hfix hf v hF
  refine ⟨first, second, fun hpos hone => ?_⟩
  obtain ⟨hp, hval⟩ := densityMeasure_isProb_and_integral ρ.toMeasure hf hpos hone
  refine ⟨hp, hval, ?_⟩
  let ρ' : ProbMeasure (GaugeField D.mesh) :=
    (⟨densityMeasure ρ.toMeasure f, hp⟩ : ProbabilityMeasure (GaugeField D.mesh))
  have hgibbs : IsGibbs D.β ρ'.toMeasure := by
    refine (hiff ρ').mpr fun W F hF => ?_
    obtain ⟨-, ⟨-, -, hγ⟩, -, -⟩ := hKernel D W D.β D.β D.β_pos D.β_pos F hF
    show ∫ U, W.heatBath D.β F U ∂(densityMeasure ρ.toMeasure f) =
      ∫ U, F U ∂(densityMeasure ρ.toMeasure f)
    rw [hval _ hγ.1, hval _ hF.1]
    exact first W F hF
  refine ⟨hgibbs, ⊤, inferInstance, fun v _ A hA => ?_⟩
  show ∫ U, (shift v).actOn A U ∂(densityMeasure ρ.toMeasure f) =
    ∫ U, A U ∂(densityMeasure ρ.toMeasure f)
  have hmot : (shift v).toFun ∈ latticeMotions D.mesh := by
    rw [← hM]
    exact ⟨_, rfl⟩
  have hτ : IsBoundedObservable ((shift v).actOn A) := by
    obtain ⟨hAm, c, hc⟩ := hA
    exact ⟨hAm.comp (hPull _ _ hmot hmot).1.continuous.measurable, c, fun U => hc _⟩
  rw [hval _ hτ, hval _ hA]
  exact second v A hA
end LatticePhases.InvariantDensities
end YangMills.Construction
