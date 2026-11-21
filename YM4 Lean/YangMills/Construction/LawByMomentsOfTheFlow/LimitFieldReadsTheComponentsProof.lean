import YangMills.Construction.HullsInEveryVolume.ALimitAlongTheSidesIsALimitPoint
import YangMills.Construction.HullsInEveryVolume.LimitPointsReadBoundedWindows
import YangMills.Construction.HullsInEveryVolume.TheObservableReadsAWindow
import YangMills.Construction.InfiniteLattice.ExtendedMeasureIsTheWilsonMeasureOnConfigurations
import YangMills.Construction.InfiniteLattice.MeansOfCorrelationsOverCubesProof
import YangMills.Construction.InfiniteLattice.SpecificationInTheTorusMeasuresAndTheirLimitPoints
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldReadsTheComponents
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology Quaternion
namespace YangMills.Construction.MomentLaw
section Conditional
variable {X : Type*} {m : MeasurableSpace X} [m0 : MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
private theorem exists_simpleFunc_abs_sub_le {F : X → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : SimpleFunc X ℝ, ∀ x, |F x - f x| ≤ ε := by
  have hg : Measurable fun x => ⌊F x / ε⌋ := (hF.div_const ε).floor
  let g : SimpleFunc X ℤ :=
    { toFun := fun x => ⌊F x / ε⌋
      measurableSet_fiber' := fun k => hg (measurableSet_singleton k)
      finite_range' := (Set.finite_Icc ⌊-C / ε⌋ ⌊C / ε⌋).subset (by
        rintro _ ⟨x, rfl⟩
        have h := abs_le.mp (hC x)
        exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right h.1 hε.le),
          Int.floor_le_floor (div_le_div_of_nonneg_right h.2 hε.le)⟩) }
  refine ⟨g.map fun k : ℤ => ε * k, fun x => ?_⟩
  have hx : (g.map fun k : ℤ => ε * k) x = ε * (⌊F x / ε⌋ : ℤ) := rfl
  rw [hx]
  have h1 := Int.floor_le (F x / ε)
  have h2 := Int.lt_floor_add_one (F x / ε)
  have h3 : F x = ε * (F x / ε) := by field_simp
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith
private theorem integral_simpleFunc_ae_eq_condExp (κ : Kernel X X) [IsMarkovKernel κ]
    (hv : ∀ B : Set X, MeasurableSet B →
      (fun U => (κ U B).toReal) =ᵐ[ν] (ν[B.indicator (fun _ => (1 : ℝ)) | m])) (f : SimpleFunc X ℝ) :
    (fun U => ∫ x, f x ∂(κ U)) =ᵐ[ν] (ν[f | m]) := by
  refine SimpleFunc.induction (motive := fun f : SimpleFunc X ℝ =>
    (fun U => ∫ x, f x ∂(κ U)) =ᵐ[ν] (ν[f | m])) (fun c s hs => ?_) (fun f g _ hf hg => ?_) f
  · have hfun : ((SimpleFunc.piecewise s hs (SimpleFunc.const X c) (SimpleFunc.const X 0) : SimpleFunc X ℝ) : X → ℝ) =
        c • s.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun]
    have h1 := condExp_smul (μ := ν) c (s.indicator (fun _ => (1 : ℝ))) m
    filter_upwards [hv s hs, h1] with U hU h1U
    rw [h1U, Pi.smul_apply, ← hU]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_indicator_const _ hs]
    simp [Measure.real]
  · have hfi : Integrable f ν := SimpleFunc.integrable_of_isFiniteMeasure f
    have hgi : Integrable g ν := SimpleFunc.integrable_of_isFiniteMeasure g
    have h1 := condExp_add hfi hgi m
    rw [SimpleFunc.coe_add]
    filter_upwards [hf, hg, h1] with U hfU hgU h1U
    rw [h1U, Pi.add_apply, ← hfU, ← hgU]
    exact integral_add (SimpleFunc.integrable_of_isFiniteMeasure f)
      (SimpleFunc.integrable_of_isFiniteMeasure g)
private theorem integrable_of_abs_le {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)
private theorem integral_ae_eq_condExp_of_bounded (κ : Kernel X X) [IsMarkovKernel κ]
    (hv : ∀ B : Set X, MeasurableSet B →
      (fun U => (κ U B).toReal) =ᵐ[ν] (ν[B.indicator (fun _ => (1 : ℝ)) | m])) {F : X → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ x, |F x| ≤ C) : (fun U => ∫ x, F x ∂(κ U)) =ᵐ[ν] (ν[F | m]) := by
  have key : ∀ n : ℕ, ∀ᵐ U ∂ν, |(∫ x, F x ∂(κ U)) - (ν[F | m]) U| ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hεdef
    obtain ⟨f, hf⟩ := exists_simpleFunc_abs_sub_le hF hC hε
    have hfi : Integrable f ν := SimpleFunc.integrable_of_isFiniteMeasure f
    have hFi : Integrable F ν := integrable_of_abs_le hF hC
    have h1 := condExp_sub hFi hfi m
    have h2 : ∀ᵐ U ∂ν, |(ν[F - ⇑f | m]) U| ≤ ε :=
      ae_bdd_abs_condExp_of_ae_bdd_abs (μ := ν) (m := m) (R := ε) (f := F - ⇑f)
        (ae_of_all _ fun x => hf x)
    filter_upwards [integral_simpleFunc_ae_eq_condExp κ hv f, h1, h2] with U hU h1U h2U
    have h3 : |(∫ x, F x ∂(κ U)) - ∫ x, f x ∂(κ U)| ≤ ε := by
      rw [← integral_sub (integrable_of_abs_le hF hC) (SimpleFunc.integrable_of_isFiniteMeasure f)]
      have := norm_integral_le_of_norm_le_const (μ := κ U) (f := fun x => F x - f x) (C := ε)
        (ae_of_all _ fun x => by simpa using hf x)
      simpa using this
    rw [h1U] at h2U
    simp only [Pi.sub_apply] at h2U
    rw [hU] at h3
    have e1 := abs_le.mp h3
    have e2 := abs_le.mp h2U
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  filter_upwards [ae_all_iff.2 key] with U hU
  by_contra hne
  have hpos : 0 < |(∫ x, F x ∂(κ U)) - (ν[F | m]) U| / 2 := by
    have := abs_pos.mpr (sub_ne_zero.mpr hne)
    positivity
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  have := hU n
  linarith
private theorem condExp_le_of_setIntegral_le (hm : m ≤ m0) {Φ : X → ℝ} (hΦ : Integrable Φ ν) {b : ℝ}
    (h : ∀ A, MeasurableSet[m] A → ∫ x in A, Φ x ∂ν ≤ b * ν.real A) : ∀ᵐ x ∂ν, (ν[Φ | m]) x ≤ b := by
  have hYm : StronglyMeasurable[m] (ν[Φ | m]) := stronglyMeasurable_condExp
  have hYi : Integrable (ν[Φ | m]) ν := integrable_condExp
  have hZm : MeasurableSet[m] ((ν[Φ | m]) ⁻¹' Set.Ioi b) := hYm.measurable measurableSet_Ioi
  have hZ0 := hm _ hZm
  have e1 : ∫ x in (ν[Φ | m]) ⁻¹' Set.Ioi b, (ν[Φ | m]) x ∂ν = ∫ x in (ν[Φ | m]) ⁻¹' Set.Ioi b, Φ x ∂ν :=
    setIntegral_condExp hm hΦ hZm
  have hint : IntegrableOn (fun x => (ν[Φ | m]) x - b) ((ν[Φ | m]) ⁻¹' Set.Ioi b) ν :=
    hYi.integrableOn.sub (integrable_const b).integrableOn
  have e2 : ∫ x in (ν[Φ | m]) ⁻¹' Set.Ioi b, ((ν[Φ | m]) x - b) ∂ν ≤ 0 := by
    rw [integral_sub hYi.integrableOn (integrable_const b).integrableOn, setIntegral_const, e1, smul_eq_mul]
    linarith [h _ hZm]
  have hnn : 0 ≤ᵐ[ν.restrict ((ν[Φ | m]) ⁻¹' Set.Ioi b)] fun x => (ν[Φ | m]) x - b :=
    (ae_restrict_iff' hZ0).2 (ae_of_all _ fun x hx => sub_nonneg.2 (le_of_lt hx))
  have e3 := le_antisymm e2 (integral_nonneg_of_ae hnn)
  have e4 := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 e3
  filter_upwards [(ae_restrict_iff' hZ0).1 e4] with x hx
  by_contra hlt
  have h5 := hx (not_le.mp hlt)
  have h6 : (ν[Φ | m]) x - b = 0 := h5
  linarith
variable {T : X → X}
omit [IsProbabilityMeasure ν] in
private theorem setIntegral_comp_iterate (hT : MeasurePreserving T ν ν) {Φ : X → ℝ} (hΦ : Measurable Φ) {A : Set X}
    (hA : MeasurableSet A) (hinv : T ⁻¹' A = A) (k : ℕ) : ∫ x in A, Φ (T^[k] x) ∂ν = ∫ x in A, Φ x ∂ν := by
  have hk := hT.iterate k
  have hinvk : T^[k] ⁻¹' A = A := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ, Set.preimage_comp, ih (hT.iterate k), hinv]
  rw [← integral_indicator hA, ← integral_indicator hA]
  have e : (A.indicator fun x => Φ (T^[k] x)) = (A.indicator Φ) ∘ T^[k] := by
    funext x
    have hx : T^[k] x ∈ A ↔ x ∈ A := by
      conv_rhs => rw [← hinvk]
      rfl
    by_cases h : x ∈ A
    · rw [Function.comp_apply, Set.indicator_of_mem h, Set.indicator_of_mem (hx.2 h)]
    · rw [Function.comp_apply, Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (hx.1 h')]
  rw [e]
  have hm := integral_map (μ := ν) hk.measurable.aemeasurable (f := A.indicator Φ)
    (hΦ.indicator hA).aestronglyMeasurable
  rw [hk.map_eq] at hm
  exact hm.symm
private theorem setIntegral_le_of_birkhoff_averages (hT : MeasurePreserving T ν ν) {Φ : X → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ x, |Φ x| ≤ C) {A : Set X} (hA : MeasurableSet A) (hinv : T ⁻¹' A = A) {b : ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (hav : ∀ᶠ M : ℕ in atTop, ∫ x, max ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x) - b) 0 ∂ν ≤ e M) :
    ∫ x in A, Φ x ∂ν ≤ b * ν.real A := by
  have hI : ∀ k, Integrable (fun x => Φ (T^[k] x)) ν := fun k =>
    Integrable.of_bound (hΦ.comp (hT.iterate k).measurable).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa using hC _)
  refine sub_nonpos.mp (ge_of_tendsto he ?_)
  filter_upwards [hav, eventually_ge_atTop 1] with M hM hM1
  have hM0 : (M : ℝ) ≠ 0 := by
    have : 0 < M := hM1
    positivity
  have hsum : Integrable (fun x => ∑ k ∈ Finset.range M, Φ (T^[k] x)) ν := integrable_finsetSum _ fun k _ => hI k
  have havg : Integrable (fun x => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x)) ν := hsum.const_mul _
  have hsub : Integrable (fun x => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x) - b) ν := havg.sub (integrable_const b)
  have hpos : Integrable (fun x => max ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x) - b) 0) ν := hsub.pos_part
  have e1 : ∫ x in A, ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x)) ∂ν = ∫ x in A, Φ x ∂ν := by
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (hI k).integrableOn]
    simp only [setIntegral_comp_iterate hT hΦ hA hinv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have e2 : ∫ x in A, ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Φ (T^[k] x) - b) ∂ν = ∫ x in A, Φ x ∂ν - b * ν.real A := by
    rw [integral_sub havg.integrableOn (integrable_const b).integrableOn, e1, setIntegral_const, smul_eq_mul, mul_comm]
  have e3 := setIntegral_mono (s := A) hsub.integrableOn hpos.integrableOn fun x => le_max_left _ _
  have e4 := setIntegral_le_integral (s := A) hpos (ae_of_all _ fun x => le_max_right _ _)
  rw [e2] at e3
  exact e3.trans (e4.trans hM)
end Conditional
section Windows
private theorem bondOffsetInBox_mono {R R' : ℕ} (h : R ≤ R') {b : (Fin 4 → ℤ) × Fin 4}
    (hb : TorusFields.BondOffsetInBox R b) : TorusFields.BondOffsetInBox R' b :=
  ⟨fun i => (hb.1 i).trans (by exact_mod_cast h), fun i => (hb.2 i).trans (by exact_mod_cast h)⟩
private def restrictWindow {R R' : ℕ} (h : R ≤ R') (v : TorusLimits.WindowValuation R') : TorusLimits.WindowValuation R :=
  fun b => v ⟨b.1, bondOffsetInBox_mono h b.2⟩
private theorem continuous_restrictWindow {R R' : ℕ} (h : R ≤ R') : Continuous (restrictWindow h) :=
  continuous_pi fun _ => continuous_apply _
private theorem borel_measurable_comp {R R' : ℕ} {f : TorusLimits.WindowValuation R' → TorusLimits.WindowValuation R}
    (hf : Continuous f) {G : TorusLimits.WindowValuation R → ℝ}
    (hG : @Measurable _ _ (borel _) _ G) : @Measurable _ _ (borel _) _ (fun v => G (f v)) := by
  letI i₁ : MeasurableSpace (TorusLimits.WindowValuation R) := borel _
  letI i₂ : MeasurableSpace (TorusLimits.WindowValuation R') := borel _
  haveI : BorelSpace (TorusLimits.WindowValuation R) := ⟨rfl⟩
  haveI : BorelSpace (TorusLimits.WindowValuation R') := ⟨rfl⟩
  exact hG.comp hf.measurable
variable {L K : ℕ} {ms : ℕ → ℕ}
private def ReadsOneWindow (Ψ : TorusLimits.FineField L K → ℝ)
    (θ : ∀ i, TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ ms i)) → ℝ) : Prop :=
  Measurable Ψ ∧ ∃ (R : ℕ) (G : TorusLimits.WindowValuation R → ℝ), TorusLimits.IsBoundedWindowObservable G ∧
    (∀ U, Ψ U = TorusLimits.evalOnField G U) ∧ ∀ᶠ i in atTop, ∀ W, θ i W = TorusLimits.evalOnTorus G W
private theorem ReadsOneWindow.comp {ι : Type} [Fintype ι] {Ψ : ι → TorusLimits.FineField L K → ℝ}
    {θ : ι → ∀ i, TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ ms i)) → ℝ}
    (h : ∀ c, ReadsOneWindow (Ψ c) (θ c)) {H : (ι → ℝ) → ℝ}
    (hH : Continuous H) : ReadsOneWindow (fun U => H fun c => Ψ c U) (fun i W => H fun c => θ c i W) := by
  classical
  refine ⟨hH.measurable.comp (measurable_pi_lambda _ fun c => (h c).1), ?_⟩
  choose R G hG hS hT using fun c => (h c).2
  obtain ⟨R', hR'⟩ : ∃ R', ∀ c, R c ≤ R' :=
    ⟨∑ c, R c, fun c => Finset.single_le_sum (f := R) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)⟩
  choose C hC using fun c => (hG c).bounded
  obtain ⟨D, hD⟩ := (isCompact_univ_pi fun c => isCompact_Icc (a := -C c) (b := C c)).exists_bound_of_continuousOn
    hH.continuousOn
  refine ⟨R', fun v => H fun c => G c (restrictWindow (hR' c) v), ⟨?_, D, fun v => ?_⟩, fun U => ?_, ?_⟩
  · letI i₁ : MeasurableSpace (TorusLimits.WindowValuation R') := borel _
    have hm : ∀ c, Measurable fun v => G c (restrictWindow (hR' c) v) := fun c =>
      borel_measurable_comp (continuous_restrictWindow (hR' c)) (hG c).measurable
    exact hH.measurable.comp (measurable_pi_lambda _ hm)
  · have hmem : (fun c => G c (restrictWindow (hR' c) v)) ∈ Set.pi Set.univ fun c => Set.Icc (-C c) (C c) :=
      fun c _ => abs_le.mp (hC c _)
    simpa using hD _ hmem
  · have e : (fun c => Ψ c U) = fun c => TorusLimits.evalOnField (G c) U := funext fun c => hS c U
    simp only [e]
    rfl
  · filter_upwards [eventually_all.2 hT] with i hi W
    have e : (fun c => θ c i W) = fun c => TorusLimits.evalOnTorus (G c) W := funext fun c => hi c W
    simp only [e]
    rfl
private theorem offsetInBox_add {r c : ℕ} {z h : Fin 4 → ℤ} (hz : TorusFields.OffsetInBox r z)
    (hh : TorusFields.OffsetInBox c h) : TorusFields.OffsetInBox (r + c) (z + h) := fun i => by
  have h1 := abs_add_le (z i) (h i)
  have h2 := hz i
  have h3 := hh i
  simp only [Pi.add_apply]
  push_cast
  linarith
private theorem bondOffsetInBox_shift {R c : ℕ} {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox c h)
    (b : TorusLimits.WindowLink R) : TorusFields.BondOffsetInBox (R + c) (b.1.1 + h, b.1.2) := by
  refine ⟨offsetInBox_add b.2.1 hh, ?_⟩
  have e : b.1.1 + h + Pi.single b.1.2 1 = b.1.1 + Pi.single b.1.2 1 + h := by abel
  change TorusFields.OffsetInBox (R + c) (b.1.1 + h + Pi.single b.1.2 1)
  rw [e]
  exact offsetInBox_add b.2.2 hh
private def translateWindow {R c : ℕ} {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox c h)
    (v : TorusLimits.WindowValuation (R + c)) : TorusLimits.WindowValuation R :=
  fun b => v ⟨(b.1.1 + h, b.1.2), bondOffsetInBox_shift hh b⟩
private theorem continuous_translateWindow {R c : ℕ} {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox c h) :
    Continuous (translateWindow (R := R) hh) :=
  continuous_pi fun _ => continuous_apply _
private theorem siteOfInt_add_pointwise {N : ℕ} (z h : Fin 4 → ℤ) :
    (TorusFields.siteOfInt (z + h) : TorusFields.TorusSite N) = TorusFields.siteOfInt z + TorusFields.siteOfInt h := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem latticePointOfInt_add (a : ℝ) (z h : Fin 4 → ℤ) :
    TorusLimits.latticePointOfInt a z + TorusLimits.latticePointOfInt a h =
      TorusLimits.latticePointOfInt a (z + h) := by
  refine Subtype.ext (funext fun μ => ?_)
  change (z μ : ℝ) * a + (h μ : ℝ) * a = ((z μ + h μ : ℤ) : ℝ) * a
  push_cast
  ring
private theorem evalOnTorus_translateWindow {R c N : ℕ} {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox c h)
    (G : TorusLimits.WindowValuation R → ℝ) (W : TorusFields.TorusField N) :
    TorusLimits.evalOnTorus (fun v => G (translateWindow hh v)) W =
      TorusLimits.evalOnTorus G (TorusFields.translate (TorusFields.siteOfInt h) W) := by
  show G _ = G _
  congr 1
  funext b
  simp only [translateWindow, TorusFields.translate, siteOfInt_add_pointwise]
private theorem evalOnField_translateWindow {R c : ℕ} {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox c h)
    (G : TorusLimits.WindowValuation R → ℝ) (U : TorusLimits.FineField L K) :
    TorusLimits.evalOnField (fun v => G (translateWindow hh v)) U =
      TorusLimits.evalOnField G (TorusLimits.fineShift L K h U) := by
  show G _ = G _
  congr 1
  funext b
  have e : (InfiniteLattice.shift (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h)).linkMap
      (InfiniteLattice.Link.forwardFrom (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) b.1.1) b.1.2) =
      InfiniteLattice.Link.forwardFrom
        (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) (b.1.1 + h)) b.1.2 := by
    refine InfiniteLattice.Link.ext ?_ ?_
    · rw [← latticePointOfInt_add]
      rfl
    · rw [← latticePointOfInt_add]
      refine Subtype.ext ?_
      change ((_ : InfiniteLattice.AmbientSpace) + _) + _ = ((_ : InfiniteLattice.AmbientSpace) + _) + _
      abel
  change ((U _ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
    ((U ((InfiniteLattice.shift _).linkMap _) : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)
  rw [e]
private theorem continuous_fineShift (h : Fin 4 → ℤ) : Continuous (TorusLimits.fineShift L K h) := by
  refine Continuous.subtype_mk (continuous_pi fun b => ?_) _
  exact (continuous_apply _).comp continuous_subtype_val
private theorem ReadsOneWindow.shift {Ψ : TorusLimits.FineField L K → ℝ}
    {θ : ∀ i, TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ ms i)) → ℝ}
    (h : ReadsOneWindow Ψ θ) (a : Fin 4 → ℤ) :
    ReadsOneWindow (fun U => Ψ (TorusLimits.fineShift L K a U))
      (fun i W => θ i (TorusFields.translate (TorusFields.siteOfInt a) W)) := by
  refine ⟨h.1.comp (continuous_fineShift a).measurable, ?_⟩
  obtain ⟨R, G, hG, hS, hT⟩ := h.2
  obtain ⟨c, hc⟩ : ∃ c : ℕ, TorusFields.OffsetInBox c a := by
    refine ⟨∑ i, (a i).natAbs, fun i => ?_⟩
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨R + c, fun v => G (translateWindow hc v),
    ⟨borel_measurable_comp (continuous_translateWindow hc) hG.measurable, ?_⟩, fun U => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hG.bounded
    exact ⟨C, fun v => hC _⟩
  · show Ψ (TorusLimits.fineShift L K a U) = _
    rw [hS, evalOnField_translateWindow]
  · filter_upwards [hT] with i hi W
    show θ i (TorusFields.translate (TorusFields.siteOfInt a) W) = _
    rw [hi, evalOnTorus_translateWindow]
private theorem ReadsOneWindow.iterate {Ψ : TorusLimits.FineField L K → ℝ}
    {θ : ∀ i, TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ ms i)) → ℝ}
    (h : ReadsOneWindow Ψ θ) (a : Fin 4 → ℤ) (k : ℕ) :
    ReadsOneWindow (fun U => Ψ ((TorusLimits.fineShift L K a)^[k] U))
      (fun i W => θ i ((TorusFields.translate (TorusFields.siteOfInt a))^[k] W)) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.shift a
end Windows
section Keeps
private theorem measurePreserving_shift_of_shiftInvariant {a : ℝ} {ν : Measure (InfiniteLattice.GaugeField a)}
    [IsProbabilityMeasure ν] (h : InfiniteLattice.IsShiftInvariant ν) (v : InfiniteLattice.LatticePoint a) :
    MeasurePreserving (InfiniteLattice.shift v).pullbackField ν ν := by apply _root_.YangMills.Construction.LatticePhases.CubeErgodic.measurePreserving_shift <;> assumption
private theorem mem_torusLimits_of_mem_torusLimitSet
    (hE : FixedSpacing.LiftedGibbsIsLiftedWilsonMeasure)
    (hT : FixedSpacing.TorusSpecification.Statement)
    (W : FixedSpacing.Setup) {ν : Measure W.Fields}
    (h : ν ∈ InfiniteLattice.torusLimitSet W.L W.level W.β) : ν ∈ W.torusLimits := by
  obtain ⟨hp, n, hpos, hside, hlim⟩ := h
  have hL : (1 : ℝ) < W.L := by
    have h13 := W.admissible.2
    exact_mod_cast (by omega : 1 < W.L)
  have hn : StrictMono n := by
    intro i j hij
    by_contra hle
    have h₁ : PeriodicLattice.torusSide W.L (n j) ≤ PeriodicLattice.torusSide W.L (n i) := by
      unfold PeriodicLattice.torusSide
      have := pow_le_pow_right₀ hL.le (not_lt.1 hle)
      linarith
    exact absurd (hside hij) (not_lt.2 h₁)
  let n' : ℕ → ℕ+ := fun i => ⟨n i, hpos i⟩
  have hs : Tendsto (fun i => (W.withExponent (n' i)).side) atTop atTop := by
    have h2 := (tendsto_pow_atTop_atTop_of_one_lt hL).comp hn.tendsto_atTop
    have h3 := h2.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    refine h3.congr fun i => ?_
    simp [FixedSpacing.Setup.side, FixedSpacing.Setup.withExponent, PeriodicLattice.torusSide, n']
  obtain ⟨-, -, hsub, -⟩ := hT W
  obtain ⟨ψ, ρ, ρ', hψ, hρ, -, -⟩ := hsub n' hs
  refine ⟨fun i => n' (ψ i), ρ, Subtype.mk ν hp, hs.comp hψ.tendsto_atTop, hρ, rfl, ?_⟩
  intro F hF
  have hmeas : ∀ i, (ρ i).1 = InfiniteLattice.liftedWilsonMeasure W.L (n (ψ i)) W.level W.β := fun i =>
    (hρ i).trans (hE (W.withExponent (n' (ψ i))))
  change Tendsto (fun i => ∫ U, F U ∂(ρ i).1) atTop (𝓝 (∫ U, F U ∂ν))
  refine ((hlim F hF).comp hψ.tendsto_atTop).congr fun i => ?_
  simp only [Function.comp_apply, hmeas i]
private theorem measurePreserving_fineShift
    (hE : FixedSpacing.LiftedGibbsIsLiftedWilsonMeasure)
    (hT : FixedSpacing.TorusSpecification.Statement) {L K : ℕ} (hodd : Odd L) (h13 : 13 ≤ L)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (TorusLimits.FineField L K)} (hν : ν ∈ InfiniteLattice.torusLimitSet L K β)
    (a : Fin 4 → ℤ) : MeasurePreserving (TorusLimits.fineShift L K a) ν ν := by
  let W : FixedSpacing.Setup := ⟨L, ⟨hodd, h13⟩, K, 1, β, hβ⟩
  have hmem : ν ∈ W.torusLimits := mem_torusLimits_of_mem_torusLimitSet hE hT W hν
  obtain ⟨-, -, -, hst, -, -⟩ := hT W
  haveI : IsProbabilityMeasure ν := hν.1
  exact measurePreserving_shift_of_shiftInvariant (hst ν hmem).2 _
end Keeps
section Weights
variable {Λ : MomentLaw.MomentParameters}
private theorem circleRep_eq {c d b : ℝ} {t : ℤ} (hc : 0 < c) (hd : d = b + c * t) (hb : 2 * |b| < c) :
    LevelTestFunctions.circleRep c d = b := by apply _root_.YangMills.SharedProofs.p85907 <;> assumption
private theorem abs_le_of_abs_mul_le {b c R : ℝ} (hc : 1 ≤ c) (h : |c * b| ≤ R) : |b| ≤ |R| := by
  rw [abs_mul, abs_of_pos (by linarith : 0 < c)] at h
  have : |b| ≤ c * |b| := le_mul_of_one_le_left (abs_nonneg _) hc
  linarith [le_abs_self R]
private theorem fn_circleRep_sub_eq {φ : TestFunctions.EuclideanFourSpace → ℝ} {R c top : ℝ} (x₀ y : Fin 4 → ℝ)
    (hφ : ∀ v, φ v ≠ 0 → ∀ a, |v a| ≤ R) (hc : 1 ≤ c)
    (htop : 0 < top) (hfar : ∀ a, 2 * (|R| + |x₀ a|) < top) :
    φ (WithLp.toLp 2 fun a => c * LevelTestFunctions.circleRep top (y a - x₀ a)) =
      φ (WithLp.toLp 2 fun a => c * (LevelTestFunctions.circleRep top (y a) - x₀ a)) := by
  have key₁ : ∀ a, |LevelTestFunctions.circleRep top (y a - x₀ a)| ≤ |R| →
      LevelTestFunctions.circleRep top (y a - x₀ a) = LevelTestFunctions.circleRep top (y a) - x₀ a := by
    intro a hb
    have e : LevelTestFunctions.circleRep top (y a) = LevelTestFunctions.circleRep top (y a - x₀ a) + x₀ a := by
      refine circleRep_eq (t := round ((y a - x₀ a) / top)) htop ?_ ?_
      · unfold LevelTestFunctions.circleRep
        ring
      · have := abs_add_le (LevelTestFunctions.circleRep top (y a - x₀ a)) (x₀ a)
        linarith [hfar a]
    rw [e]
    ring
  have key₂ : ∀ a, |LevelTestFunctions.circleRep top (y a) - x₀ a| ≤ |R| →
      LevelTestFunctions.circleRep top (y a - x₀ a) = LevelTestFunctions.circleRep top (y a) - x₀ a := by
    intro a hb
    refine circleRep_eq (t := round (y a / top)) htop ?_ ?_
    · unfold LevelTestFunctions.circleRep
      ring
    · linarith [hfar a, abs_nonneg (x₀ a)]
  by_cases h₁ : φ (WithLp.toLp 2 fun a => c * LevelTestFunctions.circleRep top (y a - x₀ a)) = 0
  · by_cases h₂ : φ (WithLp.toLp 2 fun a => c * (LevelTestFunctions.circleRep top (y a) - x₀ a)) = 0
    · rw [h₁, h₂]
    · have e : (fun a => c * LevelTestFunctions.circleRep top (y a - x₀ a)) =
          fun a => c * (LevelTestFunctions.circleRep top (y a) - x₀ a) :=
        funext fun a => by rw [key₂ a (abs_le_of_abs_mul_le hc (hφ _ h₂ a))]
      rw [e]
  · have e : (fun a => c * LevelTestFunctions.circleRep top (y a - x₀ a)) =
        fun a => c * (LevelTestFunctions.circleRep top (y a) - x₀ a) :=
      funext fun a => by rw [key₁ a (abs_le_of_abs_mul_le hc (hφ _ h₁ a))]
    rw [e]
private theorem displacementToPlaquette_div {L K m : ℕ} (hL : 0 < L)
    (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide L K (2 * L ^ m))) (a : Fin 4) :
    TwoPointLaw.displacementToPlaquette (TorusFields.siteOfInt fun j => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) j) p a /
        (L : ℝ) ^ K =
      LevelTestFunctions.circleRep ((2 * L ^ m : ℕ) : ℝ) (LevelTestFunctions.barycenterCoord p a / (L : ℝ) ^ K) := by
  have hN : ((WeightedResponses.fineSide L K (2 * L ^ m) : ℕ) : ℝ) = ((2 * L ^ m : ℕ) : ℝ) * (L : ℝ) ^ K := by
    rw [WeightedResponses.fineSide_eq]
    push_cast
    ring
  have h0 : (TorusFields.siteOfInt fun j => (L : ℤ) ^ K * (0 : Fin 4 → ℤ) j :
      TorusFields.TorusSite (WeightedResponses.fineSide L K (2 * L ^ m))) a = 0 := by
    simp [TorusFields.siteOfInt]
  unfold TwoPointLaw.displacementToPlaquette LevelTestFunctions.barycenterCoord LevelTestFunctions.circleRep
  simp only [h0, ZMod.val_zero, Nat.cast_zero, sub_zero, hN]
  have e : ∀ d : ℝ, d / (((2 * L ^ m : ℕ) : ℝ) * (L : ℝ) ^ K) = d / (L : ℝ) ^ K / ((2 * L ^ m : ℕ) : ℝ) := by
    intro d
    field_simp
  rw [e]
  field_simp
private theorem testWeight_eq_scaledTestWeight (S : MomentLaw.MomentPoint Λ) (hL : 0 < Λ.stepParams.side) {m : ℕ}
    (hfar : ∀ a, 2 * (|Λ.R| + |S.data.center a|) < (((2 * Λ.stepParams.side ^ m : ℕ)) : ℝ)) (i : Fin Λ.k)
    (p : TorusFields.TorusPlaquette
      (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m))) :
    ({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).testWeight Λ.stepParams.side i
        (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)) p =
      TwoPointLaw.scaledTestWeight Λ.stepParams.side S.data.windowLevel S.data.windowLevel
        (S.rescaledTestFunction i) 0
        (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)) p := by
  have hq : (0 : ℝ) < (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel := by positivity
  have hLr : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast hL
  have hc : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel := by
    rw [le_div_iff₀ hq, one_mul]
    exact pow_le_pow_right₀ hLr S.supAdmissible.scaleLevel_le
  have hφ : ∀ v, S.data.fn i v ≠ 0 → ∀ a, |v a| ≤ Λ.R := fun v hv =>
    S.supAdmissible.isSupTestFamily.abs_coord_le i v (subset_tsupport _ (Function.mem_support.mpr hv))
  have ht : (0 : ℝ) < (((2 * Λ.stepParams.side ^ m : ℕ)) : ℝ) := by positivity
  have h := fn_circleRep_sub_eq (φ := S.data.fn i) S.data.center
    (fun a => LevelTestFunctions.barycenterCoord p a / (Λ.stepParams.side : ℝ) ^ S.data.windowLevel) hφ hc ht hfar
  show S.data.fn i _ = S.data.fn i _
  refine h.trans ?_
  beta_reduce
  simp only [displacementToPlaquette_div hL p]
private theorem hasCompactSupport_rescaledTestFunction (S : MomentLaw.MomentPoint Λ) (hL : 0 < Λ.stepParams.side)
    (i : Fin Λ.k) : HasCompactSupport (S.rescaledTestFunction i) := by
  have hq : (0 : ℝ) < (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel := by positivity
  have hLr : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast hL
  have hc : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel := by
    rw [le_div_iff₀ hq, one_mul]
    exact pow_le_pow_right₀ hLr S.supAdmissible.scaleLevel_le
  refine HasCompactSupport.intro (isCompact_closedBall S.data.center |Λ.R|) fun x hx => ?_
  by_contra hne
  refine hx ((dist_pi_le_iff (abs_nonneg _)).2 fun a => ?_)
  have h := S.supAdmissible.isSupTestFamily.abs_coord_le i _ (subset_tsupport _ (Function.mem_support.mpr hne)) a
  rw [Real.dist_eq]
  exact abs_le_of_abs_mul_le hc h
private theorem readsOneWindow_curvatureObservable (hO : HullsInEveryVolume.observableReadsWindowStatement)
    (S : MomentLaw.MomentPoint Λ) (hodd : Odd Λ.stepParams.side) (hL : 1 < Λ.stepParams.side) (i : Fin Λ.k)
    {ms : ℕ → ℕ} (hms : Tendsto ms atTop atTop) :
    ReadsOneWindow (L := Λ.stepParams.side) (K := S.data.windowLevel) (ms := ms)
      (InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i))
      (fun n W => WeightedResponses.curvatureObservable
        (({ S.data with sideExponent := ms n } : LevelTestFunctions.LevelData Λ.k).testWeight
          Λ.stepParams.side i _) W) := by
  have hL0 : 0 < Λ.stepParams.side := by omega
  obtain ⟨R, G, hG, hGm, hS, hT⟩ :=
    hO Λ.stepParams.side S.data.windowLevel (S.rescaledTestFunction i) hodd hL
      (hasCompactSupport_rescaledTestFunction S hL0 i)
  have he : (InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) :
      TorusLimits.FineField Λ.stepParams.side S.data.windowLevel → ℝ) = fun U => TorusLimits.evalOnField G U :=
    funext fun U => (InfiniteLattice.cutoffSmearedEnergyRe_eq_smearedEnergy _ U).trans (hS U)
  refine ⟨he ▸ hGm, R, G, hG, fun U => congrFun he U, ?_⟩
  have hLr : (1 : ℝ) < (Λ.stepParams.side : ℝ) := by exact_mod_cast hL
  have hbig : ∀ᶠ m : ℕ in atTop, ∀ a, 2 * (|Λ.R| + |S.data.center a|) < (((2 * Λ.stepParams.side ^ m : ℕ)) : ℝ) := by
    rw [eventually_all]
    intro a
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hLr).eventually_gt_atTop (|Λ.R| + |S.data.center a|)] with m hm
    push_cast
    linarith
  filter_upwards [hms.eventually hT, hms.eventually hbig] with n h₁ h₂ W
  rw [← h₁ W]
  congr 1
  exact funext fun p => testWeight_eq_scaledTestWeight S hL0 h₂ i p
end Weights
section Pairs
variable {ℓ : TorusLumps.StepParameters}
private theorem bottomField_chain (rule : ChainNoise.NoiseRule ℓ) (T : WeightedResponses.StageTower ℓ) :
    ∀ (s n : ℕ) [NeZero n] (W : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side s n))
      (U : ChainNoise.ChainNoise ℓ s n), WeightedResponses.bottomField ℓ s n (rule.chain T s n W U) = W
  | 0, _, _, _, _ => rfl
  | s + 1, n, _, W, U => bottomField_chain rule T s (n * ℓ.side) W U.1
private theorem isProbability_chainNoiseLaw (ℓ : TorusLumps.StepParameters) :
    ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (ChainNoise.chainNoiseLaw ℓ s n) :=
  _root_.YangMills.SharedProofs.p2413 ℓ
private theorem pairTranslate_iterate_fst (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ) (k : ℕ)
    (ω : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n) :
    ((ChainNoise.pairTranslate ℓ u n h)^[k] ω).1 =
      (TorusFields.translate (TorusFields.siteOfInt fun i => (ℓ.side : ℤ) ^ u * h i))^[k] ω.1 := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih => exact ih (ChainNoise.pairTranslate ℓ u n h ω)
end Pairs
section Field
private theorem setIntegral_le_of_jointLimitLaw {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {T : X → X} (hT : MeasurePreserving T ν ν) {Φ : X → ℝ} (hΦ : Measurable Φ) {C : ℝ} (hC : ∀ x, |Φ x| ≤ C)
    {J : Type} {P : Measure (MomentMethod.TranslateValues J)} [IsProbabilityMeasure P] {j : J}
    (hjoint : ∀ (M : ℕ) (G : (Fin M → ℝ) → ℝ), Continuous G → (∃ D : ℝ, ∀ w, |G w| ≤ D) →
      ∫ x, G (fun e : Fin M => Φ (T^[e] x)) ∂ν = ∫ v, G (fun e : Fin M => v (j, (e : ℕ))) ∂P)
    (herg : Tendsto (fun M : ℕ => eLpNorm (fun v : MomentMethod.TranslateValues J =>
      (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v) 2 P)
      atTop (𝓝 0))
    {s b : ℝ} (hs : s = 1 ∨ s = -1)
    (hst : ∀ᵐ v ∂P, s * MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v ≤ b) {A : Set X}
    (hA : MeasurableSet A) (hinv : T ⁻¹' A = A) : ∫ x in A, s * Φ x ∂ν ≤ b * ν.real A := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x₀)
  have hs1 : |s| = 1 := by
    rcases hs with rfl | rfl <;> simp
  have hne : ∀ᶠ M : ℕ in atTop, eLpNorm (fun v : MomentMethod.TranslateValues J =>
      (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v)
      2 P ≠ ⊤ := by
    filter_upwards [(tendsto_order.1 herg).2 1 (by norm_num)] with M hM
    exact ne_top_of_lt hM
  refine setIntegral_le_of_birkhoff_averages hT (Φ := fun x => s * Φ x) (hΦ.const_mul s) (C := C) (fun x => ?_) hA hinv
    (e := fun M => (eLpNorm (fun v : MomentMethod.TranslateValues J =>
      (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v)
      2 P).toReal) ?_ ?_
  · rw [abs_mul, hs1, one_mul]
    exact hC x
  · have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herg
    simp only [ENNReal.toReal_zero] at h
    exact h
  filter_upwards [hne] with M hM
  have hCb : 0 ≤ C + |b| := add_nonneg hC0 (abs_nonneg _)
  let G : (Fin M → ℝ) → ℝ := fun w => min (max (s * ((M : ℝ)⁻¹ * ∑ e, w e) - b) 0) (C + |b|)
  have hGc : Continuous G :=
    (((continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun e _ => continuous_apply e))).sub
      continuous_const).max continuous_const).min continuous_const
  have hGnn : ∀ w, 0 ≤ G w := fun w => le_min (le_max_right _ _) hCb
  have hGb : ∃ D : ℝ, ∀ w, |G w| ≤ D :=
    ⟨C + |b|, fun w => by
      rw [abs_of_nonneg (hGnn w)]
      exact min_le_right _ _⟩
  have e1 : ∀ x, max ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, s * Φ (T^[k] x) - b) 0 =
      G fun e : Fin M => Φ (T^[e] x) := by
    intro x
    have h1 : (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, s * Φ (T^[k] x) =
        s * ((M : ℝ)⁻¹ * ∑ e : Fin M, Φ (T^[e] x)) := by
      rw [← Finset.mul_sum, Finset.sum_range]
      ring
    have h2 : |(M : ℝ)⁻¹ * ∑ e : Fin M, Φ (T^[e] x)| ≤ C := by
      by_cases hM0 : M = 0
      · subst hM0
        simpa using hC0
      have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
      have h3 : |∑ e : Fin M, Φ (T^[e] x)| ≤ M * C := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin M)) (fun e => |Φ (T^[(e : ℕ)] x)|) C
          fun e _ => hC _
        simpa using this
      rw [abs_mul, abs_of_pos (inv_pos.mpr hMp), inv_mul_le_iff₀ hMp]
      exact h3
    have h4 : s * ((M : ℝ)⁻¹ * ∑ e : Fin M, Φ (T^[e] x)) - b ≤ C + |b| := by
      have h5 := le_abs_self (s * ((M : ℝ)⁻¹ * ∑ e : Fin M, Φ (T^[e] x)))
      rw [abs_mul, hs1, one_mul] at h5
      have h6 := neg_abs_le b
      linarith
    show _ = min _ _
    rw [h1, min_eq_left (max_le h4 hCb)]
  simp only [e1]
  rw [hjoint M G hGc hGb]
  have hgm : Measurable fun v : MomentMethod.TranslateValues J => G fun e : Fin M => v (j, (e : ℕ)) :=
    hGc.measurable.comp (measurable_pi_lambda _ fun e => measurable_pi_apply _)
  have hY : StronglyMeasurable (MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j)) :=
    (stronglyMeasurable_condExp (m := MomentMethod.shiftInvariantSigma J) (μ := P)
      (f := MomentMethod.evalAtZero j)).mono inf_le_right
  have hfm : AEStronglyMeasurable (fun v : MomentMethod.TranslateValues J =>
      (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v) P := by
    have h1 : Measurable fun v : MomentMethod.TranslateValues J => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) :=
      (Finset.measurable_sum (Finset.range M) (f := fun k (v : MomentMethod.TranslateValues J) => v (j, k))
        fun k _ => measurable_pi_apply (j, k)).const_mul _
    exact h1.aestronglyMeasurable.sub hY.aestronglyMeasurable
  have hle : ∀ᵐ v ∂P, ENNReal.ofReal (G fun e : Fin M => v (j, (e : ℕ))) ≤
      ‖(M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) -
        MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v‖ₑ := by
    filter_upwards [hst] with v hv
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (max_le ?_ (norm_nonneg _)))
    rw [← Finset.sum_range (fun k => v (j, k)), Real.norm_eq_abs]
    have h1 := le_abs_self (s * ((M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) -
      MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v))
    rw [abs_mul, hs1, one_mul] at h1
    linarith
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun v => hGnn _) hgm.aestronglyMeasurable]
  refine ENNReal.toReal_mono hM ?_
  calc ∫⁻ v, ENNReal.ofReal (G fun e : Fin M => v (j, (e : ℕ))) ∂P
      ≤ ∫⁻ v, ‖(M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) -
          MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v‖ₑ ∂P := lintegral_mono_ae hle
    _ = eLpNorm (fun v : MomentMethod.TranslateValues J =>
        (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) -
          MomentMethod.invariantCondExp P (MomentMethod.evalAtZero j) v) 1 P :=
        eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ _ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hfm
variable {Λ : MomentLaw.MomentParameters}
private def fineCentredProduct (S : MomentLaw.MomentPoint Λ) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k))
    (U : TorusLimits.FineField Λ.stepParams.side S.data.windowLevel) : ℝ :=
  ∏ i ∈ B, (InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U - c i)
private def torusCentredProduct (S : MomentLaw.MomentPoint Λ) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (m : ℕ)
    (W : TorusFields.TorusField
      (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m))) : ℝ :=
  ∏ i ∈ B, (WeightedResponses.curvatureObservable
    (({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).testWeight Λ.stepParams.side i _) W - c i)
private def fineTranslationVector (L K p : ℕ) : Fin 4 → ℤ := fun i => (L : ℤ) ^ K * MomentLaw.translationVector L p i
private theorem integral_sampleLaw_eq_wilsonLaw (S : MomentLaw.MomentPoint Λ) (m : ℕ)
    (hp : ({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).SupAdmissible
      Λ.stepParams.side Λ.R Λ.d)
    (hs : Λ.stepParams.side * Λ.stepParams.n₀ ≤
      ({ S.data with sideExponent := m } : LevelTestFunctions.LevelData Λ.k).period Λ.stepParams.side)
    (rule : ChainNoise.NoiseRule Λ.stepParams) (p M : ℕ)
    (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (G : (Fin M → ℝ) → ℝ) {R : ℕ} (H : TorusLimits.WindowValuation R → ℝ)
    (hread : ∀ W : TorusFields.TorusField
        (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)),
      G (fun e : Fin M => torusCentredProduct S c B m
        ((TorusFields.translate (TorusFields.siteOfInt
          (fineTranslationVector Λ.stepParams.side S.data.windowLevel p)))^[e] W)) = TorusLimits.evalOnTorus H W) :
    ∀ S' : MomentLaw.MomentPoint Λ, S' = S.withSideExponent m hp hs →
      ∫ ω, G (fun e : Fin M => MomentLaw.bottomProduct c B S' (S'.sampleOf rule
          ((ChainNoise.pairTranslate Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)
            (MomentLaw.translationVector Λ.stepParams.side p))^[e] ω))) ∂S'.sampleLaw =
        ∫ W, TorusLimits.evalOnTorus H W ∂(WeightedResponses.wilsonLaw S.β
          (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m))) := by
  rintro _ rfl
  haveI := isProbability_chainNoiseLaw Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m)
  haveI : SFinite (WeightedResponses.wilsonLaw S.β
      (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m))) := by
    unfold WeightedResponses.wilsonLaw
    infer_instance
  have e : ∀ ω : TorusFields.TorusField
        (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)) ×
        ChainNoise.ChainNoise Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m),
      G (fun e : Fin M => MomentLaw.bottomProduct c B (S.withSideExponent m hp hs)
        ((S.withSideExponent m hp hs).sampleOf rule
        ((ChainNoise.pairTranslate Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m)
          (MomentLaw.translationVector Λ.stepParams.side p))^[e] ω))) = TorusLimits.evalOnTorus H ω.1 := by
    intro ω
    refine Eq.trans ?_ (hread ω.1)
    congr 1
    funext e
    have h1 := bottomField_chain rule (S.withSideExponent m hp hs).tower S.data.windowLevel
      (2 * Λ.stepParams.side ^ m)
      (((ChainNoise.pairTranslate Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m)
        (MomentLaw.translationVector Λ.stepParams.side p))^[e] ω).1)
      (((ChainNoise.pairTranslate Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m)
        (MomentLaw.translationVector Λ.stepParams.side p))^[e] ω).2)
    have h2 := pairTranslate_iterate_fst (ℓ := Λ.stepParams) S.data.windowLevel (2 * Λ.stepParams.side ^ m)
      (MomentLaw.translationVector Λ.stepParams.side p) e ω
    unfold MomentLaw.bottomProduct torusCentredProduct
    refine Finset.prod_congr rfl fun i _ => ?_
    show WeightedResponses.curvatureObservable _ (WeightedResponses.bottomField Λ.stepParams S.data.windowLevel
      (2 * Λ.stepParams.side ^ m) (rule.chain (S.withSideExponent m hp hs).tower S.data.windowLevel
        (2 * Λ.stepParams.side ^ m) _ _)) - c i = _
    rw [h1, h2]
    rfl
  show ∫ ω : TorusFields.TorusField
        (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)) ×
        ChainNoise.ChainNoise Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m),
      G (fun e : Fin M => MomentLaw.bottomProduct c B (S.withSideExponent m hp hs)
        ((S.withSideExponent m hp hs).sampleOf rule
        ((ChainNoise.pairTranslate Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m)
          (MomentLaw.translationVector Λ.stepParams.side p))^[e] ω)))
      ∂((WeightedResponses.wilsonLaw S.β
          (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m))).prod
        (ChainNoise.chainNoiseLaw Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m))) = _
  simp only [e]
  exact (integral_fun_fst (μ := WeightedResponses.wilsonLaw S.β
      (WeightedResponses.fineSide Λ.stepParams.side S.data.windowLevel (2 * Λ.stepParams.side ^ m)))
    (ν := ChainNoise.chainNoiseLaw Λ.stepParams S.data.windowLevel (2 * Λ.stepParams.side ^ m))
    (fun W => TorusLimits.evalOnTorus H W)).trans (by simp)
private theorem integral_iterate_eq_jointLimitLaw (hW : HullsInEveryVolume.wilsonLawsAgreeStatement)
    (hLim : HullsInEveryVolume.windowIntegralConvergenceStatement)
    (hodd : Odd Λ.stepParams.side) (hL : 1 < Λ.stepParams.side) (S : MomentLaw.MomentPoint Λ) (hβ : 0 < S.β)
    (F : MomentLaw.LimitLawAtPoint S)
    {ν : Measure (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel)}
    (hlim : TorusLimits.IsTorusLimitAlong Λ.stepParams.side S.data.windowLevel S.β ν F.exponents)
    {c : Fin Λ.k → ℝ} {B : Finset (Fin Λ.k)} {j : F.Index} (hg : F.observables j = MomentLaw.bottomProduct c B)
    (hread : ReadsOneWindow (ms := F.exponents) (fineCentredProduct S c B)
      (fun n W => torusCentredProduct S c B (F.exponents n) W)) (M : ℕ)
    (G : (Fin M → ℝ) → ℝ) (hG : Continuous G) (hGb : ∃ D : ℝ, ∀ w, |G w| ≤ D) :
    ∫ U, G (fun e : Fin M => fineCentredProduct S c B
        ((TorusLimits.fineShift Λ.stepParams.side S.data.windowLevel
          (fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period))^[e] U)) ∂ν =
      ∫ v, G (fun e : Fin M => v (j, (e : ℕ))) ∂F.law := by
  have h1 : Tendsto (fun i => ∫ ω, G (fun e : Fin M =>
      MomentMethod.TranslatedLaws.translate
        (MomentLaw.sampleFamily F.rule F.points F.period (MomentLaw.bottomProduct c B)) (e : ℕ) i ω)
        ∂((MomentLaw.translatedTori F.points F.period).μ i)) atTop
      (𝓝 (∫ v, G (fun e : Fin M => v (j, (e : ℕ))) ∂F.law)) := by
    have h := F.isJointLimitLaw.tendsto M (fun e => (j, (e : ℕ))) G hG hGb
    simpa only [hg] using h
  obtain ⟨-, R, H, hH, hS, hT⟩ :=
    ReadsOneWindow.comp (ι := Fin M)
      (fun e => hread.iterate (fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period) (e : ℕ)) hG
  have h2 := hLim Λ.stepParams.side S.data.windowLevel R S.β ν F.exponents H hodd hL hβ hlim hH
  have e1 : ∀ᶠ i in atTop, ∫ ω, G (fun e : Fin M =>
      MomentMethod.TranslatedLaws.translate
        (MomentLaw.sampleFamily F.rule F.points F.period (MomentLaw.bottomProduct c B)) (e : ℕ) i ω)
        ∂((MomentLaw.translatedTori F.points F.period).μ i) =
      ∫ U, TorusLimits.evalOnField H U ∂(InfiniteLattice.liftedWilsonMeasure Λ.stepParams.side (F.exponents i)
        S.data.windowLevel S.β) := by
    filter_upwards [hT] with i hi
    obtain ⟨hp, hs, hsq⟩ := F.points_eq i
    refine (integral_sampleLaw_eq_wilsonLaw S (F.exponents i) hp hs F.rule F.period M c B G H (fun W => hi W)
      (F.points i) hsq).trans ?_
    exact hW Λ.stepParams.side S.data.windowLevel (F.exponents i) R S.β H hodd hL (hlim.1 i) hβ hH
  have e2 := tendsto_nhds_unique (h1.congr' e1) h2
  rw [e2]
  exact integral_congr_ae (ae_of_all _ fun U => hS U)
end Field
section Main
variable {Λ : MomentLaw.MomentParameters}
private theorem condMean_bounds_of_limitLaw (hO : HullsInEveryVolume.observableReadsWindowStatement)
    (hW : HullsInEveryVolume.wilsonLawsAgreeStatement)
    (hLim : HullsInEveryVolume.windowIntegralConvergenceStatement)
    (hLP : TorusLimits.limitAlongSidesMemTorusLimitSetStatement)
    (hE : FixedSpacing.LiftedGibbsIsLiftedWilsonMeasure)
    (hSp : FixedSpacing.TorusSpecification.Statement) (hM : MomentMethod.jointLimitPropertiesStatement)
    (hodd : Odd Λ.stepParams.side) (h13 : 13 ≤ Λ.stepParams.side) (S : MomentLaw.MomentPoint Λ) (hβ : 0 < S.β)
    (F : MomentLaw.LimitLawAtPoint S)
    (hKeep : (MomentLaw.translatedTori F.points F.period).IsPreserving)
    {ν : Measure (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel)}
    {κ : Kernel (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel)
      (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel)} {c : Fin Λ.k → ℝ} {B : Finset (Fin Λ.k)}
    {j : F.Index} {b₁ b₂ : ℝ}
    (hlim : TorusLimits.IsTorusLimitAlong Λ.stepParams.side S.data.windowLevel S.β ν F.exponents)
    (hκ : TorusLimits.IsPeriodicConditionalKernel Λ.stepParams.side S.data.windowLevel ν F.period κ)
    (hg : F.observables j = MomentLaw.bottomProduct c B)
    (hb : ∀ᵐ v ∂F.law, b₁ ≤ F.condMeanAt j v ∧ F.condMeanAt j v ≤ b₂) :
    ∀ᵐ U ∂ν, b₁ ≤ S.centredStateMoment (κ U) c B ∧ S.centredStateMoment (κ U) c B ≤ b₂ := by
  have hL : 1 < Λ.stepParams.side := by omega
  have hν := hLP Λ.stepParams.side S.data.windowLevel S.β ν F.exponents hodd hL hβ hlim
  haveI : IsProbabilityMeasure ν := hν.1
  haveI : IsProbabilityMeasure F.law := F.isJointLimitLaw.isProbability
  haveI := hκ.isMarkovKernel
  have hT := measurePreserving_fineShift hE hSp hodd h13 hβ hν
    (fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period)
  have hread : ReadsOneWindow (ms := F.exponents) (fineCentredProduct S c B)
      (fun n W => torusCentredProduct S c B (F.exponents n) W) :=
    ReadsOneWindow.comp (ι := Fin Λ.k)
      (fun i => readsOneWindow_curvatureObservable hO S hodd hL i F.strictMono_exponents.tendsto_atTop)
      (H := fun x => ∏ i ∈ B, (x i - c i)) (continuous_finsetProd _ fun i _ => (continuous_apply i).sub continuous_const)
  have hΦ := hread.1
  obtain ⟨R, G, hG, hS, -⟩ := hread.2
  obtain ⟨C, hC'⟩ := hG.bounded
  have hC : ∀ U, |fineCentredProduct S c B U| ≤ C := fun U => by
    rw [hS]
    exact hC' _
  haveI := F.countable_index
  obtain ⟨-, -, -, herg, -, -⟩ := hM (MomentLaw.translatedTori F.points F.period) F.Index
    (fun j => MomentLaw.sampleFamily F.rule F.points F.period (F.observables j)) F.law hKeep
    F.hasBoundedMoments F.isJointLimitLaw
  have hjoint := integral_iterate_eq_jointLimitLaw hW hLim hodd hL S hβ F hlim hg hread
  have hside : ∀ {s b : ℝ}, (s = 1 ∨ s = -1) → (∀ᵐ v ∂F.law, s * F.condMeanAt j v ≤ b) →
      ∀ A : Set (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel),
      MeasurableSet A → TorusLimits.fineShift Λ.stepParams.side S.data.windowLevel
        (fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period) ⁻¹' A = A →
      ∫ U in A, s * fineCentredProduct S c B U ∂ν ≤ b * ν.real A := fun hs hst A hA hinv =>
    setIntegral_le_of_jointLimitLaw hT hΦ hC hjoint (herg j) hs hst hA hinv
  have hm : TorusLimits.periodicSigma Λ.stepParams.side S.data.windowLevel F.period ≤
      (inferInstance : MeasurableSpace (TorusLimits.FineField Λ.stepParams.side S.data.windowLevel)) :=
    MeasurableSpace.generateFrom_le fun I hI => hI.1
  have hinv : TorusLimits.periodicSigma Λ.stepParams.side S.data.windowLevel F.period ≤
      MeasurableSpace.invariants (TorusLimits.fineShift Λ.stepParams.side S.data.windowLevel
        (fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period)) := by
    refine MeasurableSpace.generateFrom_le fun I hI => ?_
    have e : fineTranslationVector Λ.stepParams.side S.data.windowLevel F.period = fun i =>
        (F.period : ℤ) * ((Λ.stepParams.side : ℤ) ^ S.data.windowLevel *
          MomentLaw.translationVector Λ.stepParams.side 1 i) := by
      funext i
      unfold fineTranslationVector MomentLaw.translationVector
      by_cases h : i = 0
      · subst h
        simp only [Pi.single_eq_same]
        push_cast
        ring
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact ⟨hI.1, hI.2 _⟩
  have hΦi : Integrable (fineCentredProduct S c B) ν := Integrable.of_bound hΦ.aestronglyMeasurable C (ae_of_all _ hC)
  have c₂ := condExp_le_of_setIntegral_le hm hΦi (b := b₂) fun A hA => by
    have h := hside (s := 1) (b := b₂) (Or.inl rfl) (hb.mono fun v hv => by simpa using hv.2) A (hm _ hA) (hinv _ hA).2
    simpa using h
  have c₁ := condExp_le_of_setIntegral_le hm (hΦi.neg) (b := -b₁) fun A hA => by
    have h := hside (s := -1) (b := -b₁) (Or.inr rfl) (hb.mono fun v hv => by simpa using hv.1) A (hm _ hA)
      (hinv _ hA).2
    simpa using h
  have hn := condExp_neg (fineCentredProduct S c B)
    (TorusLimits.periodicSigma Λ.stepParams.side S.data.windowLevel F.period) (μ := ν)
  have hker := integral_ae_eq_condExp_of_bounded
    (m := TorusLimits.periodicSigma Λ.stepParams.side S.data.windowLevel F.period) (ν := ν) κ hκ.ae_eq_condExp hΦ hC
  filter_upwards [c₁, c₂, hn, hker] with U h₁ h₂ h₃ h₄
  have e : S.centredStateMoment (κ U) c B =
      (ν[fineCentredProduct S c B | TorusLimits.periodicSigma Λ.stepParams.side S.data.windowLevel F.period]) U := h₄
  rw [e]
  rw [h₃] at h₁
  simp only [Pi.neg_apply] at h₁
  exact ⟨by linarith, h₂⟩
end Main
theorem componentsReadLimitLaw (hO : HullsInEveryVolume.observableReadsWindowStatement)
    (hW : HullsInEveryVolume.wilsonLawsAgreeStatement)
    (hLim : HullsInEveryVolume.windowIntegralConvergenceStatement)
    (hLP : TorusLimits.limitAlongSidesMemTorusLimitSetStatement)
    (hE : FixedSpacing.LiftedGibbsIsLiftedWilsonMeasure)
    (hSp : FixedSpacing.TorusSpecification.Statement) (hM : MomentMethod.jointLimitPropertiesStatement)
    (hPL : MomentLaw.largerToriStatement) : MomentLaw.componentsReadLimitLawStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := hPL a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hLL Tb hTa hTL hD hCS hCH hrt' hC => ?_⟩
  obtain ⟨M, G⟩ := h L hLo hLL Tb hTa hTL hD hCS hCH hrt' hC
  refine ⟨M, fun Kr k₁ k₂ k₃ k₄ k₅ => ?_⟩
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨y₀, fun y hy hret hrow g hg hgy k _ hk2 hk8 R d hd => ?_⟩
  have hpl := Y y hy hret hrow g hg hgy k hk2 hk8 R d hd
  intro S F K ν κ c B j b₁ b₂ hK hlim hκ hgj hb
  subst hK
  have hβ : 0 < S.β := by
    have hab : (g ^ 2)⁻¹ + 2 * Tb.B ≤ S.β := S.window_le
    have hp : 0 < (g ^ 2)⁻¹ := by positivity
    linarith [hD.B_ge]
  have hKeep := ((hpl S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period
    F.strictMono_exponents F.points_eq).1
  exact condMean_bounds_of_limitLaw (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) hO hW hLim hLP hE hSp hM hD.L_odd
    (le_trans (by norm_num) hD.L_ge) S hβ F hKeep hlim hκ hgj hb
end YangMills.Construction.MomentLaw
end
