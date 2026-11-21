import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorus
import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.CommonConstantAndCommonRate
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctions
import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.KernelOfTheSymbolOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.RealKernelsOfMatrixFunctions
import YangMills.Construction.PeriodicOperators.SymbolOfTheKernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.TransposesAndCombinationsOnTheTorus
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace SymbolCalculus
open Quotients (conjKernel)
section Entries
variable {J J' J'' : Type}
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by
  classical
  have := Fintype.ofFinite J
  funext c' c
  have e : linearMapEntry (linearMapOfEntries K) c' c = applyKernel K (Pi.single c 1) c' := by
    rw [← linearMapOfEntries_eq_applyKernel]
    simp only [linearMapEntry]
  rw [e]
  simp only [applyKernel, tsum_fintype]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
theorem linearMap_ext_of_entry [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by
  classical
  have := Fintype.ofFinite J
  refine LinearMap.pi_ext fun c x => ?_
  have e : (Pi.single c x : J → ℂ) = x • Pi.single c 1 := by
    funext b
    simp [Pi.single_apply]
  rw [e, map_smul, map_smul]
  congr 1
  funext c'
  have := congrFun (congrFun h c') c
  simp only [linearMapEntry] at this
  convert this
theorem linearMapOfEntries_compKernel [Finite J] [Finite J''] (A : J' → J → ℂ)
    (B : J → J'' → ℂ) :
    linearMapOfEntries (compKernel A B) = (linearMapOfEntries A).comp (linearMapOfEntries B) := by
  classical
  refine linearMap_ext_of_entry ?_
  rw [linearMapEntry_linearMapOfEntries]
  funext c' c''
  have hB : ∀ c, B c c'' = linearMapOfEntries B (Pi.single c'' 1) c := fun c => by
    have := congrFun (congrFun (linearMapEntry_linearMapOfEntries B) c) c''
    simp only [linearMapEntry] at this
    rw [← this]
  have : linearMapEntry ((linearMapOfEntries A).comp (linearMapOfEntries B)) c' c'' =
      applyKernel A (linearMapOfEntries B (Pi.single c'' 1)) c' := by
    rw [← linearMapOfEntries_eq_applyKernel]
    simp only [linearMapEntry, LinearMap.comp_apply]
  rw [this]
  simp only [compKernel, applyKernel]
  exact tsum_congr fun c => by rw [hB c]
end Entries
section Classes
variable {I I' I'' : PeriodicData}
theorem descendMatrix_mkQuot {s : ℕ} {F : I'.Carrier → I.Carrier → ℂ}
    (hF : ∀ ι₁' ι₂' ι₁ ι₂, I'.mkQuot s ι₁' = I'.mkQuot s ι₂' →
      I.mkQuot s ι₁ = I.mkQuot s ι₂ → F ι₁' ι₁ = F ι₂' ι₂) (ι' : I'.Carrier) (ι : I.Carrier) :
    descendMatrix I I' s F (I'.mkQuot s ι') (I.mkQuot s ι) = F ι' ι := by
  have hz : ∃ z, ∀ a b, I'.mkQuot s a = I'.mkQuot s ι' → I.mkQuot s b = I.mkQuot s ι →
      F a b = z := ⟨F ι' ι, fun a b ha hb => hF _ _ _ _ ha hb⟩
  exact (Classical.epsilon_spec hz ι' ι rfl rfl).symm
theorem carrierEntry_symbolHom (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ}
    {κ : Fin 4 → ℂ}
    (hc : FactorsThroughQuot (P := I) (Q := I') (fourierSymbol I I' T κ)) (ι' : I'.Carrier)
    (ι : I.Carrier) : carrierEntry (symbolHom I I' T κ) ι' ι = fourierSymbol I I' T κ ι' ι := by
  have := hI.finite_quot
  simp only [carrierEntry, symbolHom]
  rw [linearMapEntry_linearMapOfEntries]
  exact descendMatrix_mkQuot hc ι' ι
theorem symbolHom_eq_of_carrierEntry (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ}
    {κ : Fin 4 → ℂ} {M : QuotHom I I'}
    (h : ∀ ι' ι, fourierSymbol I I' T κ ι' ι = carrierEntry M ι' ι) :
    symbolHom I I' T κ = M := by
  have := hI.finite_quot
  have hc : FactorsThroughQuot (P := I) (Q := I') (fourierSymbol I I' T κ) := by
    intro ι₁' ι₂' ι₁ ι₂ e' e
    rw [h, h]
    simp only [carrierEntry, e', e]
  refine linearMap_ext_of_entry ?_
  funext c' c
  obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  have := carrierEntry_symbolHom hI hc ι' ι
  rw [h] at this
  exact this
theorem matFunKernel_congr {M M' : (Fin 4 → ℂ) → QuotHom I I'}
    (h : ∀ κ ∈ realDualPoints, M κ = M' κ) :
    matFunKernel I I' M = matFunKernel I I' M' := by
  funext ι' ι
  simp only [matFunKernel]
  congr 1
  funext κ
  simp only [matFunIntegrand]
  rw [h (toComplexVec κ) fun j => by simp [toComplexVec]]
theorem real_mem_imStrip_pos {δ : ℝ} (hδ : 0 < δ) {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    κ ∈ strictImStrip δ := by
  have e : imVec κ = 0 := by
    funext μ
    exact hκ μ
  change TorusMetric.euclidNormVec (imVec κ) < δ
  rw [e]
  simpa [TorusMetric.euclidNormVec] using hδ
theorem realDualPoints_subset_imStrip {υ : ℝ} (hυ : 0 < υ) : realDualPoints ⊆ imStrip υ := by
  intro κ hκ μ
  rw [hκ μ]
  simpa using hυ.le
theorem realDualPoints_subset_openImStrip {υ : ℝ} (hυ : 0 < υ) :
    realDualPoints ⊆ openImStrip υ := by
  intro κ hκ μ
  rw [hκ μ]
  simpa using hυ
theorem isUnit_of_isInvertibleQuotHom {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by
  refine (Module.End.isUnit_iff _).2 ⟨fun f f' e => ?_, fun g' => (h g').exists⟩
  exact (h (M f)).unique rfl e.symm
theorem isInvertibleQuotHom_of_isUnit {M : QuotHom I I}
    (h : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) : IsInvertibleQuotHom M := by
  obtain ⟨hi, hs⟩ := (Module.End.isUnit_iff _).1 h
  intro g
  obtain ⟨f, hf⟩ := hs g
  exact ⟨f, hf, fun f' e => hi (e.trans hf.symm)⟩
theorem quotHomInverse_comp {M : QuotHom I I} (h : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) :
    (quotHomInverse M).comp M = LinearMap.id :=
  Ring.inverse_mul_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) h
theorem comp_quotHomInverse {M : QuotHom I I} (h : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) :
    M.comp (quotHomInverse M) = LinearMap.id :=
  Ring.mul_inverse_cancel (M : Module.End ℂ (I.UnitQuot → ℂ)) h
theorem ringInverse_inverse_mul_mul {R : Type} [Ring R] {a b : R} (ha : IsUnit a)
    (hb : IsUnit b) :
    Ring.inverse (Ring.inverse a * (b * a)) = Ring.inverse a * (Ring.inverse b * a) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  have e : ((↑u⁻¹ * (↑v * ↑u) : R)) = ((u⁻¹ * (v * u) : Rˣ) : R) := by
    simp
  rw [Ring.inverse_unit, Ring.inverse_unit, e, Ring.inverse_unit]
  simp [mul_assoc]
end Classes
section Facts
variable {I I' I'' : PeriodicData}
theorem exists_symbolProperties_idKernel (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ δ, IsDecayRate I I' T δ ∧ SymbolProperties I I' I T (idKernel I) δ := by
  have st := (hId I hI).2.2.2.2.2.1 I' hI' T hT
  obtain ⟨δ, hδ⟩ := st.exists_rate
  have a := st.withRate δ hδ
  exact ⟨δ, hδ, hFacts.1 I I' I hI hI' hI T (idKernel I) δ a.left_kernel a.left_rate
    a.right_kernel a.right_rate⟩
theorem exists_common_decayRate (hCommon : UniformDecay.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) :
    ∃ δ, IsDecayRate I I' T δ ∧ IsDecayRate I'' I S δ := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := hT.2
  obtain ⟨C', δ', hC', hδ', hb'⟩ := hS.2
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  exact ⟨min δ δ',
    ⟨hm, C, hC, hCommon.1 I I' hI hI' T C δ C _ hT hC hδ hb le_rfl hm (min_le_left _ _)⟩,
    ⟨hm, C', hC', hCommon.1 I'' I hI'' hI S C' δ' C' _ hS hC' hδ' hb' le_rfl hm (min_le_right _ _)⟩⟩
theorem exists_symbolProperties (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) :
    ∃ δ, 0 < δ ∧ SymbolProperties I I' I'' T S δ := by
  obtain ⟨δ, h₁, h₂⟩ := exists_common_decayRate hCommon hI hI' hI'' hT hS
  exact ⟨δ, h₁.1, hFacts.1 I I' I'' hI hI' hI'' T S δ hT h₁ hS h₂⟩
theorem symbolHom_compKernel (hI : IsPeriodic I) (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ} {δ : ℝ}
    (F : SymbolProperties I I' I'' T S δ) {κ : Fin 4 → ℂ} (hκ : κ ∈ strictImStrip δ) :
    symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) := by
  have := hI.finite_quot
  have := hI''.finite_quot
  have e := (F.quotSymbol_compKernel κ hκ).2
  simp only [quotSymbol] at e
  simp only [symbolHom]
  rw [e, linearMapOfEntries_compKernel]
theorem linearMapOfEntries_quotOne (hI : IsPeriodic I) :
    linearMapOfEntries (quotOne I) = (LinearMap.id : QuotHom I I) := by
  classical
  have := hI.finite_quot
  refine linearMap_ext_of_entry ?_
  rw [linearMapEntry_linearMapOfEntries]
  funext c' c
  simp only [quotOne, linearMapEntry, LinearMap.id_apply, Pi.single_apply]
theorem symbolHom_idKernel (hId : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (κ : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) κ = LinearMap.id := by
  have e := (hId I hI).2.2.2.2.1 κ
  simp only [quotSymbol] at e
  simp only [symbolHom]
  rw [e, linearMapOfEntries_quotOne hI]
theorem eq_of_symbolHom_eq (hKer : SymbolKernel.KernelOfSymbol)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T T' : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hT' : IsPeriodicKernel I I' T')
    (h : ∀ κ ∈ realDualPoints, symbolHom I I' T κ = symbolHom I I' T' κ) : T = T' := by
  rw [← hKer I I' hI hI' T hT, ← hKer I I' hI hI' T' hT']
  exact matFunKernel_congr h
theorem finiteRangeSymbolEntire (hD : CovariantFiniteRange.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') :
    FiniteRangeSymbolEntire I I' := by
  intro T hT hr
  obtain ⟨ϱ, hϱ⟩ := hr
  have hcov : IsPhaseCovariant I I' 0 T := by
    intro n ι' ι
    simp [bilinDot, hT.1 n ι' ι]
  have e : dephasedKernel I I' 0 T = T := by
    funext ι' ι
    simp [dephasedKernel, bilinDot]
  obtain ⟨h₁, -, h₃, -⟩ := hD.2 I I' hI hI' 0 ϱ T hcov hϱ
  rw [e] at h₁ h₃
  exact ⟨h₁.summable, fun ι' ι => ⟨by norm_num, h₃ ι' ι⟩⟩
theorem compPeriodic (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'') :
    CompPeriodic I I' I'' := by
  intro T S hT hS
  obtain ⟨δ, -, F⟩ := exists_symbolProperties hFacts hCommon hI hI' hI'' hT hS
  exact F.compKernel_isPeriodicKernel
theorem transposePeriodic (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') :
    TransposePeriodic I I' := by
  intro T hT
  obtain ⟨δ, -, F⟩ := exists_symbolProperties_idKernel hFacts hId hI hI' hT
  refine ⟨fun ι ι' => ?_, F.kernelTranspose_isPeriodicKernel⟩
  simp only [kernelTranspose, wTranspose, div_eq_mul_inv]
theorem symbolSummand_neg_star {T : I'.Carrier → I.Carrier → ℂ} (hr : ∀ ι' ι, (T ι' ι).im = 0)
    (κ : Fin 4 → ℂ) (ι' : I'.Carrier) (ι : I.Carrier) (n : Fin 4 → ℤ) :
    symbolSummand I I' T (-star κ) ι' ι n = conj (symbolSummand I I' T κ ι' ι n) := by
  simp only [symbolSummand, map_mul, ← Complex.exp_conj]
  rw [Complex.conj_eq_iff_im.2 (hr _ _)]
  congr 2
  simp [bilinDot, toComplexVec, Finset.mul_sum]
theorem realKernelSymbol (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') :
    RealKernelSymbol I I' := by
  intro T hT hr κ hκ
  obtain ⟨δ, -, F⟩ := exists_symbolProperties_idKernel hFacts hId hI hI' hT
  have hκ' : SymbolSummableAt I I' T (-star κ) := by
    intro ι' ι
    have := hκ ι' ι
    simpa only [symbolSummand_neg_star hr, Complex.norm_conj] using this
  have hc := F.eq_of_mkQuot_eq κ hκ
  have hc' := F.eq_of_mkQuot_eq _ hκ'
  refine ⟨hκ', hc, hc', ?_⟩
  funext c' c
  obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  have e₁ := carrierEntry_symbolHom hI hc ι' ι
  have e₂ := carrierEntry_symbolHom hI hc' ι' ι
  simp only [carrierEntry] at e₁ e₂
  change conj (linearMapEntry (symbolHom I I' T κ) (I'.mkQuot 1 ι') (I.mkQuot 1 ι)) =
    linearMapEntry (symbolHom I I' T (-star κ)) (I'.mkQuot 1 ι') (I.mkQuot 1 ι)
  rw [e₁, e₂]
  simp only [fourierSymbol, symbolSummand_neg_star hr]
  exact Complex.conj_tsum _
end Facts
section Phases
variable {I I' : PeriodicData}
theorem phaseOn_mkQuot {e : Fin 4 → ℤ}
    (h : ∀ ι₁ ι₂, I.mkQuot 1 ι₁ = I.mkQuot 1 ι₂ →
      Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι₁))) =
        Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι₂))))
    (ι : I.Carrier) :
    phaseOn I e (I.mkQuot 1 ι) = Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι))) := by
  have hz : ∃ z, ∀ a, I.mkQuot 1 a = I.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a))) = z :=
    ⟨_, fun a ha => h a ι ha⟩
  exact (Classical.epsilon_spec hz ι rfl).symm
theorem norm_exp_phase (e : Fin 4 → ℤ) (y : InfiniteLattice.AmbientSpace) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec y))‖ = 1 := by
  have : (2 * (Real.pi : ℂ) * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec y)) =
      ((2 * Real.pi * ∑ μ, (e μ : ℝ) * y μ : ℝ) : ℂ) * Complex.I := by
    simp only [bilinDot, toComplexVec, castVec]
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
theorem phase_properties (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (∀ ι₁ ι₂, I.mkQuot 1 ι₁ = I.mkQuot 1 ι₂ →
      Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι₁))) =
        Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι₂)))) ∧
      IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have a := (hId I hI).2.2.2.2.2.2.2 1 one_pos
  have F := hFacts.1 I I I hI hI hI _ _ 1 a.left_kernel a.left_rate a.right_kernel
    a.right_rate
  refine ⟨F.exp_phase_eq_of_mkQuot_eq e, ?_⟩
  exact (F.quotSymbol_addTwoPiInt 0 e ((hId I hI).2.2.1 0 (mem_univ _))).2.1
theorem norm_phaseOn (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) (e : Fin 4 → ℤ)
    (c : I.UnitQuot) : ‖phaseOn I e c‖ = 1 := by
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  have := phaseOn_mkQuot (phase_properties hFacts hId hI e).1 ι
  change ‖phaseOn I e (I.mkQuot 1 ι)‖ = 1
  rw [this, norm_exp_phase]
theorem wNorm_phaseMul (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) (e : Fin 4 → ℤ)
    (f : I.UnitQuot → ℂ) :
    wNorm (I.quotWeight 1) (phaseMul I e f) = wNorm (I.quotWeight 1) f := by
  simp only [wNorm]
  congr 1
  refine tsum_congr fun c => ?_
  change _ * ‖phaseOn I e c * f c‖ ^ 2 = _
  rw [norm_mul, norm_phaseOn hFacts hId hI, one_mul]
theorem phaseMulDiagonalUnitary (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) :
    PhaseMulDiagonalUnitary I := by
  classical
  intro e
  refine ⟨(phase_properties hFacts hId hI e).1, fun c' c h => ?_, fun f g => ?_,
    wNorm_phaseMul hFacts hId hI e⟩
  · change phaseOn I e c' * (Pi.single c (1 : ℂ) : I.UnitQuot → ℂ) c' = 0
    simp [h]
  · simp only [wInner, wPairing]
    refine tsum_congr fun c => ?_
    change _ * (starRingEnd ℂ (phaseOn I e c * f c) * (phaseOn I e c * g c)) =
      _ * (starRingEnd ℂ (f c) * g c)
    have hp : starRingEnd ℂ (phaseOn I e c) * phaseOn I e c = 1 := by
      rw [Complex.conj_mul', norm_phaseOn hFacts hId hI]
      simp
    rw [map_mul]
    calc _ = (I.quotWeight 1 c : ℂ) * ((starRingEnd ℂ (phaseOn I e c) * phaseOn I e c) *
          (starRingEnd ℂ (f c) * g c)) := by ring
      _ = _ := by rw [hp, one_mul]
theorem quotHomNorm_comp_isometry (hI : IsPeriodic I) {A : QuotHom I I'} {E : QuotHom I I}
    {P : QuotHom I' I'}
    (hE : ∀ f, wNorm (I.quotWeight 1) (E f) = wNorm (I.quotWeight 1) f)
    (hs : Function.Surjective E)
    (hP : ∀ g, wNorm (I'.quotWeight 1) (P g) = wNorm (I'.quotWeight 1) g) :
    quotHomNorm (P.comp (A.comp E)) = quotHomNorm A := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  have hf : ∀ f : I.UnitQuot → ℂ, NormSummable (I.quotWeight 1) f := fun f =>
    (hasSum_fintype _).summable
  have hb : ∀ f : I.UnitQuot → ℂ, wNorm (I.quotWeight 1) f ≤ 1 →
      f ∈ wUnitBall (I.quotWeight 1) univ := fun f h => ⟨mem_univ _, hf f, h⟩
  simp only [quotHomNorm, wOpNorm]
  apply le_antisymm
  · refine iSup₂_le fun f hf' => ?_
    have hm : E f ∈ wUnitBall (I.quotWeight 1) univ := hb _ (by rw [hE]; exact hf'.2.2)
    refine le_trans ?_ (le_iSup₂ (f := fun g _ => ENNReal.ofReal
      (wNorm (I'.quotWeight 1) (A g))) (E f) hm)
    simp only [LinearMap.comp_apply, hP]
    exact le_rfl
  · refine iSup₂_le fun g hg => ?_
    obtain ⟨f, rfl⟩ := hs g
    have hm : f ∈ wUnitBall (I.quotWeight 1) univ := hb _ (by rw [← hE]; exact hg.2.2)
    refine le_trans ?_ (le_iSup₂ (f := fun f _ => ENNReal.ofReal
      (wNorm (I'.quotWeight 1) ((P.comp (A.comp E)) f))) f hm)
    simp only [LinearMap.comp_apply, hP]
    exact le_rfl
theorem symbolHom_addTwoPiInt (hI : IsPeriodic I)
    {T : I'.Carrier → I.Carrier → ℂ} {δ : ℝ} (F : SymbolProperties I I' I T (idKernel I) δ)
    {κ : Fin 4 → ℂ} (e : Fin 4 → ℤ) (hκ : SymbolSummableAt I I' T κ) :
    symbolHom I I' T (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I' e)).comp
        ((symbolHom I I' T κ).comp (phaseMul I e)) := by
  have := hI.finite_quot
  refine LinearMap.ext fun f => ?_
  have h := (F.quotSymbol_addTwoPiInt κ e hκ).2.2 f
  simp only [LinearMap.comp_apply, symbolHom]
  rw [linearMapOfEntries_eq_applyKernel, linearMapOfEntries_eq_applyKernel]
  exact h
theorem symbolNormPeriodic (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') :
    SymbolNormPeriodic I I' := by
  intro T hT κ e hκ
  obtain ⟨δ, -, F⟩ := exists_symbolProperties_idKernel hFacts hId hI hI' hT
  refine ⟨(F.quotSymbol_addTwoPiInt κ e hκ).1, ?_⟩
  rw [symbolHom_addTwoPiInt hI F e hκ]
  have hu := (phase_properties hFacts hId hI e).2
  have hu' := (phase_properties hFacts hId hI' e).2
  refine quotHomNorm_comp_isometry hI (wNorm_phaseMul hFacts hId hI e)
    ((Module.End.isUnit_iff _).1 hu).2 fun g => ?_
  have e₁ : phaseMul I' e (quotHomInverse (phaseMul I' e) g) = g :=
    LinearMap.congr_fun (comp_quotHomInverse hu') g
  rw [← wNorm_phaseMul hFacts hId hI' e, e₁]
end Phases
section Torus
variable {I I' : PeriodicData}
theorem torusProperties (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim)
    (hAct : TorusAction.Claim)
    (hTr : TorusPeriodization.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {s : ℕ} (hs : 1 ≤ s)
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) : TorusProperties I I' s T := by
  obtain ⟨δ, -, F⟩ := exists_symbolProperties_idKernel hFacts hId hI hI' hT
  have a := hAct I I' hI hI' s hs T hT
  have t := (hTr I I' hI hI' s hs).1 T hT
  exact
    { summable := F.periodization_summable s hs
      eq_of_mkQuot_eq := F.periodization_eq_of_mkQuot_eq s hs
      apply_summable := fun f hb hv => (a.1 f hb hv).1
      apply_sidePeriodic := fun f hb hv => (a.1 f hb hv).2.1
      periodicMatrix_apply := fun f hb hv => (a.1 f hb hv).2.2
      comp := a.2
      transpose := t.1
      im_eq_zero := t.2.1
      linComb := t.2.2 }
end Torus
section Strip
variable {I I' : PeriodicData}
theorem isHolomorphicNbhd_const (D : Set (Fin 4 → ℂ)) (A : QuotHom I I') :
    IsHolomorphicNbhd D (fun _ => A) :=
  ⟨univ, isOpen_univ, subset_univ _, fun _ _ =>
    ⟨isOpen_univ, continuousOn_const, fun _ _ _ =>
      Filter.Eventually.of_forall fun _ => differentiableAt_const _⟩⟩
theorem quotHomFamilyBoundedOn_const (D : Set (Fin 4 → ℂ)) (A : QuotHom I I') :
    QuotHomFamilyBoundedOn D (fun _ => A) :=
  fun e => ⟨‖quotHomEntries A e‖, fun _ _ => le_rfl⟩
theorem quotHomFamilyContinuousOn_realDualPoints {υ : ℝ} (hυ : 0 < υ)
    {M : (Fin 4 → ℂ) → QuotHom I I'}
    (h : IsHolomorphicNbhd (imStrip υ) M) : QuotHomFamilyContinuousOn (n := 4) realDualPoints M := by
  obtain ⟨O, -, hs, hh⟩ := h
  refine ⟨by norm_num, fun e => ?_⟩
  have := (hh e.1 e.2).2.1
  exact ((continuous_apply (0 : Fin 1)).comp_continuousOn this).mono
    ((realDualPoints_subset_imStrip hυ).trans hs)
theorem matFunKernelProperties (hBound : MatrixFunctionKernel.DecayBound)
    (hSym : MatFunKernelSymbol.Claim)
    (hKer : SymbolKernel.KernelOfSymbol)
    (hReal : RealKernels.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {υ : ℝ} (hυ : 0 < υ)
    {M : (Fin 4 → ℂ) → QuotHom I I'} (hM : IsStripSymbol I I' υ M) :
    MatFunKernelProperties I I' υ M := by
  have hb := hBound I I' hI hI' υ hυ M hM.1 hM.2.1 hM.2.2
  have hs := hSym I I' hI hI' υ hυ M hM.1 hM.2.1 hM.2.2
  have hc := quotHomFamilyContinuousOn_realDualPoints hυ hM.1
  exact
    { realDualPoints_subset := ⟨realDualPoints_subset_imStrip hυ, hc⟩
      isPeriodicKernel := ⟨hb.1, fun κ hκ => (hs κ (realDualPoints_subset_openImStrip hυ hκ)).1,
        fun κ hκ => symbolHom_eq_of_carrierEntry hI
          (hs κ (realDualPoints_subset_openImStrip hυ hκ)).2⟩
      unique := fun T hT h => by
        rw [← hKer I I' hI hI' T hT]
        exact matFunKernel_congr h.2
      norm_le := hb.2
      summable_openImStrip := hs
      im_eq_zero := fun h => hReal I I' hI hI' M hc fun κ hκ =>
        h κ (realDualPoints_subset_imStrip hυ hκ) }
theorem isStripSymbol_zero (υ : ℝ) : IsStripSymbol I I' υ (fun _ => 0) :=
  ⟨isHolomorphicNbhd_const _ _, quotHomFamilyBoundedOn_const _ _, fun e κ _ => by simp⟩
theorem isStripSymbol_one (hFacts : Symbols.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I) (υ : ℝ) :
    IsStripSymbol I I υ (fun _ => linearMapOfEntries (quotOne I)) := by
  refine ⟨isHolomorphicNbhd_const _ _, quotHomFamilyBoundedOn_const _ _, fun e κ _ => ?_⟩
  rw [linearMapOfEntries_quotOne hI, LinearMap.id_comp,
    quotHomInverse_comp (phase_properties hFacts hId hI e).2]
theorem periodicInverseEq (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hId : IdKernelFacts.Claim)
    (hEntries : EntriesDets.Claim)
    (hBound : MatrixFunctionKernel.DecayBound)
    (hSym : MatFunKernelSymbol.Claim)
    (hKer : SymbolKernel.KernelOfSymbol)
    (hReal : RealKernels.Claim)
    (hI : IsPeriodic I) {υ : ℝ} (hυ : 0 < υ)
    {M : (Fin 4 → ℂ) → QuotHom I I} (hM : IsStripSymbol I I υ M)
    {T : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T) :
    PeriodicInverseEq I υ M T := by
  intro hsym hnear hbd
  obtain ⟨O₁, hO₁, hs₁, hinv⟩ := hnear
  obtain ⟨O₂, hO₂, hs₂, hhol⟩ := hM.1
  have hreal := realDualPoints_subset_imStrip (υ := υ) hυ
  have hIn := (hEntries.2.2.1 I hI).2.2.1
  have hNhol : IsHolomorphicNbhd (imStrip υ) (fun κ => quotHomInverse (M κ)) := by
    refine ⟨O₁ ∩ O₂, hO₁.inter hO₂, subset_inter hs₁ hs₂, fun c' c => ?_⟩
    have hM' : QuotHomFamilyHolomorphicOn (n := 4) (O₁ ∩ O₂) M := by
      refine ⟨by norm_num, hO₁.inter hO₂, fun e => ?_⟩
      have h := hhol e.1 e.2
      exact ⟨hO₁.inter hO₂, h.2.1.mono inter_subset_right, fun a ha j => h.2.2 a ha.2 j⟩
    exact ((hIn (O₁ ∩ O₂) M fun z hz => hinv z hz.1).2 (hO₁.inter hO₂) hM').2.2 (c', c)
  have hNq : IsQuasiPeriodic (imStrip υ) (fun κ => quotHomInverse (M κ)) := by
    intro e κ hκ
    have hE := (phase_properties hFacts hId hI e).2
    have hMu := isUnit_of_isInvertibleQuotHom (hinv κ (hs₁ hκ))
    simp only []
    rw [hM.2.2 e κ hκ]
    exact ringInverse_inverse_mul_mul hE hMu
  have KF := matFunKernelProperties hBound hSym hKer hReal hI hI hυ
    (M := fun κ => quotHomInverse (M κ)) ⟨hNhol, hbd, hNq⟩
  have hRK : periodicInverse I T =
      matFunKernel I I (fun κ => quotHomInverse (M κ)) :=
    matFunKernel_congr fun κ hκ => by rw [hsym.2 κ hκ]
  have hK := KF.isPeriodicKernel.1
  have hU : ∀ κ ∈ realDualPoints, IsUnit (M κ : Module.End ℂ (I.UnitQuot → ℂ)) := fun κ hκ =>
    isUnit_of_isInvertibleQuotHom (hinv κ (hs₁ (hreal hκ)))
  have hone := (hId I hI).1
  obtain ⟨δ, hδ, FK⟩ := exists_symbolProperties hFacts hCommon hI hI hI hK hT
  obtain ⟨δ', hδ', FT⟩ := exists_symbolProperties hFacts hCommon hI hI hI hT hK
  have e₁ : compKernel (matFunKernel I I fun κ => quotHomInverse (M κ)) T = idKernel I :=
    eq_of_symbolHom_eq hKer hI hI FK.compKernel_isPeriodicKernel.2 hone fun κ hκ => by
      rw [symbolHom_compKernel hI hI FK (real_mem_imStrip_pos hδ hκ),
        KF.isPeriodicKernel.2.2 κ hκ, hsym.2 κ hκ, symbolHom_idKernel hId hI]
      exact quotHomInverse_comp (hU κ hκ)
  have e₂ : compKernel T (matFunKernel I I fun κ => quotHomInverse (M κ)) = idKernel I :=
    eq_of_symbolHom_eq hKer hI hI FT.compKernel_isPeriodicKernel.2 hone fun κ hκ => by
      rw [symbolHom_compKernel hI hI FT (real_mem_imStrip_pos hδ' hκ),
        KF.isPeriodicKernel.2.2 κ hκ, hsym.2 κ hκ, symbolHom_idKernel hId hI]
      exact comp_quotHomInverse (hU κ hκ)
  rw [hRK]
  exact ⟨fun κ hκ => by
      rw [hsym.2 κ hκ]
      exact hinv κ (hs₁ (hreal hκ)),
    KF.realDualPoints_subset.2, rfl, hK, FK.compKernel_isPeriodicKernel.1,
    FT.compKernel_isPeriodicKernel.1, e₁, e₂⟩
end Strip
section Laws
variable {I I' I'' : PeriodicData}
theorem compKernel_idKernel (T : I'.Carrier → I.Carrier → ℂ) :
    compKernel T (idKernel I) = T := by
  funext ι' ι
  simp only [compKernel]
  rw [tsum_eq_single ι]
  · simp [idKernel]
  · intro b hb
    simp [idKernel, hb]
theorem idKernel_compKernel (T : I'.Carrier → I.Carrier → ℂ) :
    compKernel (idKernel I') T = T := by
  funext ι' ι
  simp only [compKernel]
  rw [tsum_eq_single ι']
  · simp [idKernel]
  · intro b hb
    simp [idKernel, hb.symm]
theorem compIdLaws (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hId : IdKernelFacts.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') : CompIdLaws I I' := by
  intro T hT
  obtain ⟨δ, -, F⟩ := exists_symbolProperties_idKernel hFacts hId hI hI' hT
  obtain ⟨δ', -, F'⟩ := exists_symbolProperties hFacts hCommon hI' hI' hI (hId I' hI').1 hT
  exact ⟨(hId I hI).1, (hId I' hI').1, F.compKernel_isPeriodicKernel.1,
    F'.compKernel_isPeriodicKernel.1, compKernel_idKernel T, idKernel_compKernel T⟩
theorem compLinLaws (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hTr : TorusPeriodization.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'') :
    CompLinLaws I I' I'' := by
  intro T T' S S' c c' hT hT' hS hS'
  have comb₁ := (((hTr I I' hI hI' 1 le_rfl).1 T hT).2.2 T' hT' c c').1
  have comb₂ := (((hTr I'' I hI'' hI 1 le_rfl).1 S hS).2.2 S' hS' c c').1
  have P := compPeriodic hFacts hCommon hI hI' hI''
  have pTS := P T S hT hS
  have pT'S := P T' S hT' hS
  have pTS' := P T S' hT hS'
  have l₁ : ∀ ι' ι'', compKernel (kernelLinComb c c' T T') S ι' ι'' =
      c * compKernel T S ι' ι'' + c' * compKernel T' S ι' ι'' := fun ι' ι'' => by
    simp only [compKernel, kernelLinComb, add_mul, mul_assoc]
    rw [Summable.tsum_add ((pTS.1 ι' ι'').of_norm.mul_left c)
      ((pT'S.1 ι' ι'').of_norm.mul_left c'), tsum_mul_left, tsum_mul_left]
  have l₂ : ∀ ι' ι'', compKernel T (kernelLinComb c c' S S') ι' ι'' =
      c * compKernel T S ι' ι'' + c' * compKernel T S' ι' ι'' := fun ι' ι'' => by
    simp only [compKernel, kernelLinComb, mul_add, mul_left_comm (T ι' _)]
    rw [Summable.tsum_add ((pTS.1 ι' ι'').of_norm.mul_left c)
      ((pTS'.1 ι' ι'').of_norm.mul_left c'), tsum_mul_left, tsum_mul_left]
  refine ⟨comb₁, comb₂, pTS, pT'S, pTS', P _ S comb₁ hS, P T _ hT comb₂, l₁, l₂,
    funext fun ι' => funext fun ι'' => l₁ ι' ι'', funext fun ι' => funext fun ι'' => l₂ ι' ι'',
    ?_, ?_⟩
  · funext ι' ι''
    simp only [compKernel, mul_assoc]
    rw [tsum_mul_left]
  · funext ι' ι''
    simp only [compKernel, mul_left_comm (T ι' _)]
    rw [tsum_mul_left]
end Laws
theorem claim (hFacts : Symbols.Claim)
    (hCommon : UniformDecay.Claim)
    (hId : IdKernelFacts.Claim)
    (hD : CovariantFiniteRange.Claim)
    (hEntries : EntriesDets.Claim)
    (hBound : MatrixFunctionKernel.DecayBound)
    (hSym : MatFunKernelSymbol.Claim)
    (hKer : SymbolKernel.KernelOfSymbol)
    (hReal : RealKernels.Claim)
    (hAct : TorusAction.Claim)
    (hTr : TorusPeriodization.Claim) : Claim := by
  intro I I' hI hI'
  refine ⟨finiteRangeSymbolEntire hD hI hI', transposePeriodic hFacts hId hI hI',
    realKernelSymbol hFacts hId hI hI', phaseMulDiagonalUnitary hFacts hId hI,
    symbolNormPeriodic hFacts hId hI hI', ?_, ?_, compIdLaws hFacts hCommon hId hI hI',
    fun I'' hI'' => ⟨compPeriodic hFacts hCommon hI hI' hI'',
      compLinLaws hFacts hCommon hTr hI hI' hI''⟩⟩
  · intro s hs
    exact ⟨(hTr I I hI hI s hs).2, fun T hT => torusProperties hFacts hId hAct hTr hI hI' hs hT⟩
  · intro υ hυ
    exact ⟨fun e => isInvertibleQuotHom_of_isUnit (phase_properties hFacts hId hI e).2,
      fun M hM => matFunKernelProperties hBound hSym hKer hReal hI hI' hυ hM,
      isStripSymbol_zero υ, isStripSymbol_one hFacts hId hI υ,
      fun M hM T hT =>
        periodicInverseEq hFacts hCommon hId hEntries hBound hSym hKer hReal hI hυ hM hT⟩
end SymbolCalculus
end YangMills.Construction.PeriodicOperators
end
