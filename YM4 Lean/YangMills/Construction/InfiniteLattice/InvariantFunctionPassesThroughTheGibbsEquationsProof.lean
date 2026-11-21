import YangMills.Construction.InfiniteLattice.InvariantFunctionPassesThroughTheGibbsEquations
import YangMills.Construction.InfiniteLattice.InvariantFunctionsOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LocalObservablesDetermineMeasuresAndIsometriesOnIntegrableFunctions
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservablesProof
import YangMills.Construction.InfiniteLattice.RulesOfTheGibbsKernelOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.StatesWithAGivenMirrorDominateLocalObservablesProof
import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.InvariantWeight
theorem shiftInvariantSigma_le_borel :
    shiftInvariantSigma 1 ≤ (inferInstance : MeasurableSpace (GaugeField (1 : ℝ))) :=
  fun _ hs => hs.1
theorem isBoundedObservable_mul {A B : GaugeField (1 : ℝ) → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable (A * B) := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPositivityExtension.isBoundedObservable_mul <;> assumption
theorem isLocalObservable_mul {A B : GaugeField (1 : ℝ) → ℂ} (hA : IsLocalObservable A)
    (hB : IsLocalObservable B) : IsLocalObservable (A * B) := by
  obtain ⟨S, bS, mS⟩ := hA
  obtain ⟨S', bS', mS'⟩ := hB
  refine ⟨S ∪ S', bS.union bS', ?_⟩
  exact (mS.mono (regionSigma_mono Set.subset_union_left) le_rfl).mul
    (mS'.mono (regionSigma_mono Set.subset_union_right) le_rfl)
theorem integrable_of_isBoundedObservable {A : GaugeField (1 : ℝ) → ℂ}
    (hA : IsBoundedObservable A) (μ : Measure (GaugeField (1 : ℝ))) [IsFiniteMeasure μ] :
    Integrable A μ := by apply _root_.YangMills.Construction.InfiniteLattice.MirrorDomination.integrable_of_isBoundedObservable <;> assumption
theorem norm_integral_mul_le_of_eLpNorm {μ : Measure (GaugeField (1 : ℝ))}
    [IsProbabilityMeasure μ] {f g : GaugeField (1 : ℝ) → ℂ} (hf : IsBoundedObservable f)
    (hg : IsBoundedObservable g) {C ε : ℝ} (hC0 : 0 ≤ C) (hC : ∀ U, ‖g U‖ ≤ C) (hε : 0 ≤ ε)
    (hfε : eLpNorm f 1 μ ≤ ENNReal.ofReal ε) : ‖∫ U, f U * g U ∂μ‖ ≤ C * ε := by
  have hfi := integrable_of_isBoundedObservable hf μ
  have hfgi := integrable_of_isBoundedObservable (isBoundedObservable_mul hf hg) μ
  have hnorm : ∫ U, ‖f U‖ ∂μ ≤ ε := by
    rw [integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.toReal_le_of_le_ofReal hε hfε
  calc ‖∫ U, f U * g U ∂μ‖ ≤ ∫ U, ‖f U * g U‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ U, C * ‖f U‖ ∂μ := by
        refine integral_mono hfgi.norm (hfi.norm.const_mul C) fun U => ?_
        change ‖f U * g U‖ ≤ C * ‖f U‖
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC U) (norm_nonneg _)
    _ = C * ∫ U, ‖f U‖ ∂μ := integral_const_mul _ _
    _ ≤ C * ε := mul_le_mul_of_nonneg_left hnorm hC0
theorem exists_shift_avoiding {Z : AddSubgroup (LatticePoint (1 : ℝ))} (hZ : Z.FiniteIndex)
    {S : Set AmbientSpace} (bS : Bornology.IsBounded S) (W : Finset (Link (1 : ℝ))) :
    ∃ v ∈ Z, ∀ b ∈ W, ¬ b.IsWithin ((shift v).setImage S) := by
  obtain ⟨R, hR⟩ := bS.subset_closedBall (0 : AmbientSpace)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ b ∈ W, (b.initial : AmbientSpace) 0 ≤ T := by
    refine ⟨∑ b ∈ W, |(b.initial : AmbientSpace) 0|, fun b hb => ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum
      (f := fun b : Link (1 : ℝ) => |(b.initial : AmbientSpace) 0|) (fun _ _ => abs_nonneg _) hb)
  obtain ⟨m, hm⟩ := exists_nat_gt (T + R)
  have hq : 1 ≤ Z.index := Nat.pos_of_ne_zero hZ.index_ne_zero
  have hmem : m • (Z.index • axisStep 1 0) ∈ Z := Z.nsmul_mem (AddSubgroup.nsmul_index_mem Z _) m
  refine ⟨_, hmem, fun b hb hin => ?_⟩
  obtain ⟨x, hx, hxe⟩ := hin.1
  have hv0 : ((m • (Z.index • axisStep 1 0) : LatticePoint (1 : ℝ)) : AmbientSpace) 0 =
      (m : ℝ) * Z.index := by
    simp [axisStep]
  have hinit : (b.initial : AmbientSpace) 0 = x 0 + (m : ℝ) * Z.index := by
    rw [← hv0, ← hxe]
    rfl
  have hx0 : -R ≤ x 0 := by
    have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hR hx)
    have h2 : ‖x 0‖ ≤ ‖x‖ := norm_le_pi_norm x 0
    have h3 := neg_abs_le (x 0)
    rw [Real.norm_eq_abs] at h2
    linarith
  have hmq : (m : ℝ) ≤ (m : ℝ) * Z.index := by
    have : (1 : ℝ) ≤ Z.index := by exact_mod_cast hq
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have := hT b hb
  linarith
theorem actOn_shift_eq_of_measurable
    (hInv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    {w : GaugeField (1 : ℝ) → ℂ} (hm : Measurable[shiftInvariantSigma 1] w)
    (v : LatticePoint (1 : ℝ)) :
    (shift v).actOn w = w :=
  (hInv.1 ShiftPair.allShifts w (hm.mono shiftInvariantSigma_le_borel le_rfl)).mp hm v
    (Set.mem_univ v)
theorem integral_mul_actOn_shift
    (hInv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    {μ : Measure (GaugeField (1 : ℝ))} {w : GaugeField (1 : ℝ) → ℂ}
    (hm : Measurable[shiftInvariantSigma 1] w) (hobs : IsBoundedObservable w)
    {v : LatticePoint (1 : ℝ)} (hv : IsSymmetricUnder μ (shift v))
    {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    ∫ U, w U * (shift v).actOn F U ∂μ = ∫ U, w U * F U ∂μ := by
  have e := hv (w * F) (isBoundedObservable_mul hobs hF)
  have hτ := actOn_shift_eq_of_measurable hInv hm v
  have hfun : (shift v).actOn (w * F) = fun U => w U * (shift v).actOn F U := by
    funext U
    have h1 : w ((shift v).pullbackField U) = w U := congrFun hτ U
    change w ((shift v).pullbackField U) * F ((shift v).pullbackField U) =
      w U * F ((shift v).pullbackField U)
    rw [h1]
  rw [hfun] at e
  exact e
theorem integral_mul_gibbsKernelUnit
    (hKer : UnitGibbsKernelRules)
    (hMeas : LocalDeterminationAndIntegrableAction)
    (hAct : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hInv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    {β : ℝ} (hβ : 0 < β) {μ : Measure (GaugeField (1 : ℝ))} (hG : IsGibbs β μ)
    {Z : AddSubgroup (LatticePoint (1 : ℝ))} (hZ : IsPeriodSubgroup μ Z)
    {w : GaugeField (1 : ℝ) → ℂ} (hm : Measurable[shiftInvariantSigma 1] w)
    (hobs : IsBoundedObservable w) (W : Finset (Link (1 : ℝ)))
    (hW : GibbsAtFixedSpacing.HasNoOppositePairs (W : Set (Link (1 : ℝ))))
    {F : GaugeField (1 : ℝ) → ℂ} (hF : F ∈ GibbsAtFixedSpacing.continuousLocal 1) :
    ∫ U, w U * gibbsKernelUnit β W hW F U ∂μ = ∫ U, w U * F U ∂μ := by
  have : IsProbabilityMeasure μ := hG.1
  obtain ⟨hFc, hFo, hFl⟩ := hF
  obtain ⟨hK, hGib⟩ := hKer β hβ
  obtain ⟨⟨hγo, -, -⟩, hγS⟩ := hK W hW F hFo
  obtain ⟨-, C₁, hC₁⟩ := id hγo
  obtain ⟨-, C₂, hC₂⟩ := id hFo
  obtain ⟨-, hImg, -, -, hNorm, hRules, -, -, -, -⟩ := hAct
  set γF := gibbsKernelUnit β W hW F with hγF
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ U, w U * γF U ∂μ) - ∫ U, w U * F U ∂μ‖ ≤ (|C₁| + |C₂|) * ε := by
    intro ε hε
    have hMem : MemLp w 1 μ :=
      memLp_one_iff_integrable.mpr (integrable_of_isBoundedObservable hobs μ)
    obtain ⟨H, hHc, hHo, hHl, hHe⟩ :=
      (hMeas μ (shift 0)).2.1 1 (Or.inl rfl) (hMem.toLp w) ε hε
    have hHe' : eLpNorm (w - H) 1 μ ≤ ENNReal.ofReal ε := by
      have hae : ⇑(hMem.toLp w) - H =ᵐ[μ] w - H :=
        hMem.coeFn_toLp.sub (Filter.EventuallyEq.refl _ _)
      rwa [eLpNorm_congr_ae hae] at hHe
    obtain ⟨S, bS, mS⟩ := id hHl
    obtain ⟨v, hvZ, hfar⟩ := exists_shift_avoiding hZ.1 bS W
    obtain ⟨hGo, -, hGlf⟩ := hNorm (shift v) H hHo
    have hGl := hGlf hHl
    have hGc : Continuous ((shift v).actOn H) :=
      (hRules (shift v) (shift v) H H hHo hHo).2.2.2.2.2.2 hHc
    have hGin : (shift v).actOn H ∈ unitRegionObservables ((shift v).setImage S) := by
      rw [← hImg (shift v) S]
      exact ⟨H, ⟨hHo, mS⟩, rfl⟩
    set G := (shift v).actOn H with hGdef
    have hτ := actOn_shift_eq_of_measurable hInv hm v
    have hwG : eLpNorm (w - G) 1 μ ≤ ENNReal.ofReal ε := by
      have e : w - G = (shift v).actOn (w - H) := by
        funext U
        have h1 : w ((shift v).pullbackField U) = w U := congrFun hτ U
        change w U - H ((shift v).pullbackField U) =
          w ((shift v).pullbackField U) - H ((shift v).pullbackField U)
        rw [h1]
      have hsub : IsBoundedObservable (w - H) := by
        have := hobs.add (hHo.const_smul (-1))
        have e2 : w + (-1 : ℂ) • H = w - H := by
          funext U
          simp [sub_eq_add_neg]
        rwa [e2] at this
      have hnorm := ((hMeas μ (shift v)).2.2.2 (hZ.2 v hvZ)).2.1 (w - H) hsub.1
        (integrable_of_isBoundedObservable hsub μ)
      rw [e, hnorm.2.2]
      exact hHe'
    have hcomm : gibbsKernelUnit β W hW (G * F) = G * γF :=
      hγS _ hfar G hGin
    have hGF : G * F ∈ continuousLocalFunctions 1 :=
      ⟨isBoundedObservable_mul hGo hFo, isLocalObservable_mul hGl hFl, hGc.mul hFc⟩
    have hgibbs : ∫ U, (G * γF) U ∂μ = ∫ U, (G * F) U ∂μ := by
      rw [← hcomm]
      exact (hGib μ inferInstance).mp hG W hW (G * F) hGF
    have hsubo : IsBoundedObservable (w - G) := by
      have := hobs.add (hGo.const_smul (-1))
      have e2 : w + (-1 : ℂ) • G = w - G := by
        funext U
        simp [sub_eq_add_neg]
      rwa [e2] at this
    have split : ∀ K : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable K →
        ∫ U, (w - G) U * K U ∂μ = (∫ U, w U * K U ∂μ) - ∫ U, (G * K) U ∂μ := by
      intro K hKo
      have i1 := integrable_of_isBoundedObservable (isBoundedObservable_mul hobs hKo) μ
      have i2 := integrable_of_isBoundedObservable (isBoundedObservable_mul hGo hKo) μ
      calc ∫ U, (w - G) U * K U ∂μ = ∫ U, (w * K) U - (G * K) U ∂μ :=
            integral_congr_ae (Filter.Eventually.of_forall fun U => by simp [sub_mul])
        _ = (∫ U, w U * K U ∂μ) - ∫ U, (G * K) U ∂μ := integral_sub i1 i2
    have b1 := norm_integral_mul_le_of_eLpNorm hsubo hγo (abs_nonneg C₁)
      (fun U => (hC₁ U).trans (le_abs_self _)) hε.le hwG
    have b2 := norm_integral_mul_le_of_eLpNorm hsubo hFo (abs_nonneg C₂)
      (fun U => (hC₂ U).trans (le_abs_self _)) hε.le hwG
    rw [split γF hγo] at b1
    rw [split F hFo] at b2
    rw [hgibbs] at b1
    have hdiff : (∫ U, w U * γF U ∂μ) - ∫ U, w U * F U ∂μ =
        ((∫ U, w U * γF U ∂μ) - ∫ U, (G * F) U ∂μ) -
          ((∫ U, w U * F U ∂μ) - ∫ U, (G * F) U ∂μ) := by ring
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add b1 b2
  by_contra hne
  set D := (∫ U, w U * γF U ∂μ) - ∫ U, w U * F U ∂μ with hD
  have hd : 0 < ‖D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hK : 0 < |C₁| + |C₂| + 1 := by positivity
  have h1 := key (‖D‖ / (2 * (|C₁| + |C₂| + 1))) (by positivity)
  have h2 : (|C₁| + |C₂|) * (‖D‖ / (2 * (|C₁| + |C₂| + 1))) ≤
      (|C₁| + |C₂| + 1) * (‖D‖ / (2 * (|C₁| + |C₂| + 1))) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h3 : (|C₁| + |C₂| + 1) * (‖D‖ / (2 * (|C₁| + |C₂| + 1))) = ‖D‖ / 2 := by
    field_simp
  linarith
theorem integral_weightedGibbsUnit {μ : Measure (GaugeField (1 : ℝ))}
    {w : GaugeField (1 : ℝ) → ℂ} (hmB : Measurable w) (hpos : ∀ U, 0 ≤ w U)
    (F : GaugeField (1 : ℝ) → ℂ) :
    ∫ U, F U ∂weightedGibbsUnit w μ = ∫ U, w U * F U ∂μ := by
  have hd : Measurable fun y => ENNReal.ofReal (w y).re :=
    (Complex.measurable_re.comp hmB).ennreal_ofReal
  change ∫ U, F U ∂μ.withDensity (fun y => ENNReal.ofReal (w y).re) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hpos U)
  have hU : w U = ((w U).re : ℂ) := Complex.ext (by simp) (by simp [← him])
  change (ENNReal.ofReal (w U).re).toReal • F U = w U * F U
  rw [ENNReal.toReal_ofReal hre, Complex.real_smul, ← hU]
theorem isProbabilityMeasure_weightedGibbsUnit {μ : Measure (GaugeField (1 : ℝ))}
    [IsProbabilityMeasure μ] {w : GaugeField (1 : ℝ) → ℂ} (hobs : IsBoundedObservable w)
    (hpos : ∀ U, 0 ≤ w U) (hone : ∫ U, w U ∂μ = 1) :
    IsProbabilityMeasure (weightedGibbsUnit w μ) := by
  have hint := integrable_of_isBoundedObservable hobs μ
  have hre : ∫ U, (w U).re ∂μ = 1 := by
    have e : (fun U => w U) = fun U => (((w U).re : ℝ) : ℂ) := by
      funext U
      exact Complex.ext (by simp) (by simp [← (Complex.nonneg_iff.mp (hpos U)).2])
    rw [e, integral_complex_ofReal] at hone
    exact_mod_cast hone
  constructor
  unfold weightedGibbsUnit FormHilbert.densityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have e := ofReal_integral_eq_lintegral_ofReal (f := fun U => (w U).re) hint.re
    (Filter.Eventually.of_forall fun U => (Complex.nonneg_iff.mp (hpos U)).1)
  rw [hre, ENNReal.ofReal_one] at e
  exact e.symm
theorem shiftInvariantWeightPassesGibbsEquations_holds
    (hInv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    (hKer : UnitGibbsKernelRules)
    (hMeas : LocalDeterminationAndIntegrableAction)
    (hAct : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections) :
    ShiftInvariantWeightPassesGibbsEquations := by
  intro β hβ μ Z hμ hZ w hm hb
  have hG : IsGibbs β μ := hμ.1
  have : IsProbabilityMeasure μ := hG.1
  have hobs : IsBoundedObservable w := ⟨hm.mono shiftInvariantSigma_le_borel le_rfl, hb⟩
  have hgibbs := fun W hW F (hF : F ∈ GibbsAtFixedSpacing.continuousLocal 1) =>
    integral_mul_gibbsKernelUnit hKer hMeas hAct hInv hβ hG hZ hm hobs W hW hF
  have hshift : ∀ v ∈ Z, ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
      ∫ U, w U * (shift v).actOn F U ∂μ = ∫ U, w U * F U ∂μ :=
    fun v hv F hF => integral_mul_actOn_shift hInv hm hobs (hZ.2 v hv) hF
  refine ⟨hgibbs, hshift, fun hpos hone => ?_⟩
  have hprob := isProbabilityMeasure_weightedGibbsUnit hobs hpos hone
  have hint : ∀ F : GaugeField (1 : ℝ) → ℂ,
      ∫ U, F U ∂weightedGibbsUnit w μ = ∫ U, w U * F U ∂μ :=
    integral_weightedGibbsUnit hobs.1 hpos
  have hperiod : IsPeriodSubgroup (weightedGibbsUnit w μ) Z := by
    refine ⟨hZ.1, fun v hv A hA => ?_⟩
    rw [hint, hint]
    exact hshift v hv A hA
  have hGibbs : IsGibbs β (weightedGibbsUnit w μ) := by
    refine ((hKer β hβ).2 _ hprob).mpr fun W hW F hF => ?_
    rw [hint, hint]
    obtain ⟨hFo, hFl, hFc⟩ := hF
    exact hgibbs W hW F ⟨hFc, hFo, hFl⟩
  exact ⟨hprob, fun F _ => hint F, ⟨hGibbs, Z, hperiod⟩, hperiod⟩
end YangMills.Construction.InfiniteLattice.InvariantWeight
