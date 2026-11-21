import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZeroProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStripProof
import YangMills.Construction.PeriodicOperators.StripsAndFiniteNormsOfJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripJetNorms
open JetQuad (IsJet)
section Phases
variable {I : PeriodicData}
theorem norm_phaseOn (hper : IsPeriodic I) (e : Fin 4 → ℤ) (q : I.UnitQuot) :
    ‖phaseOn I e q‖ = 1 := by apply _root_.YangMills.SharedProofs.p4911 <;> assumption
theorem quotHomInverse_phaseMul_apply (hper : IsPeriodic I) (e : Fin 4 → ℤ)
    (g : I.UnitQuot → ℂ) (q : I.UnitQuot) :
    quotHomInverse (phaseMul I e) g q = (phaseOn I e q)⁻¹ * g q := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.quotHomInverse_phaseMul_apply <;> assumption
end Phases
section Norms
variable {J : Type}
theorem wNorm_unimodular_mul (w : J → ℝ) (a f : J → ℂ) (ha : ∀ q, ‖a q‖ = 1) :
    wNorm w (fun q => a q * f q) = wNorm w f := by
  simp [wNorm, ha]
theorem normSummable_unimodular_mul (w : J → ℝ) (a f : J → ℂ) (ha : ∀ q, ‖a q‖ = 1)
    (hf : NormSummable w f) : NormSummable w (fun q => a q * f q) := by
  simpa [NormSummable, ha] using hf
variable {I I' : PeriodicData}
theorem quotHomNorm_conj_phaseMul_le (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (M : QuotHom I I') (e : Fin 4 → ℤ) :
    quotHomNorm ((quotHomInverse (phaseMul I' e)).comp
      (M.comp (phaseMul I e))) ≤ quotHomNorm M := by
  refine iSup₂_le fun f hf => ?_
  have hE : phaseMul I e f ∈ wUnitBall (I.quotWeight 1) univ := by
    refine ⟨mem_univ _, ?_, ?_⟩
    · exact normSummable_unimodular_mul _ _ f (norm_phaseOn hI e) hf.2.1
    · have := wNorm_unimodular_mul (I.quotWeight 1) (phaseOn I e) f
        (norm_phaseOn hI e)
      exact (this.trans_le hf.2.2)
  have hval : wNorm (I'.quotWeight 1)
      (((quotHomInverse (phaseMul I' e)).comp
        (M.comp (phaseMul I e))) f) =
      wNorm (I'.quotWeight 1) (M (phaseMul I e f)) := by
    have hfun : ((quotHomInverse (phaseMul I' e)).comp
        (M.comp (phaseMul I e))) f =
        fun q => (phaseOn I' e q)⁻¹ * M (phaseMul I e f) q :=
      funext fun q => quotHomInverse_phaseMul_apply hI' e _ q
    rw [hfun]
    exact wNorm_unimodular_mul _ _ _ fun q => by
      rw [norm_inv, norm_phaseOn hI' e q, inv_one]
  show ENNReal.ofReal (wNorm (I'.quotWeight 1) _) ≤ _
  rw [hval]
  exact le_iSup₂ (f := fun (g : I.UnitQuot → ℂ) (_ : g ∈ wUnitBall (I.quotWeight 1) univ) =>
    ENNReal.ofReal (wNorm (I'.quotWeight 1) (M g))) _ hE
theorem quotHomNorm_le_sum_entries [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ q, 0 < I.quotWeight 1 q) (hw' : ∀ q, 0 < I'.quotWeight 1 q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : QuotHom I I',
      quotHomNorm M ≤ ENNReal.ofReal (C * ∑ q', ∑ q, ‖linearMapEntry M q' q‖) := by
  classical
  have hK0 : 0 ≤ 1 + ∑ q, (I.quotWeight 1 q)⁻¹ :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun q _ => (inv_pos.2 (hw q)).le)
  have hW0 : 0 ≤ ∑ q', I'.quotWeight 1 q' := Finset.sum_nonneg fun q _ => (hw' q).le
  refine ⟨Real.sqrt (∑ q', I'.quotWeight 1 q') * (1 + ∑ q, (I.quotWeight 1 q)⁻¹),
    mul_nonneg (Real.sqrt_nonneg _) hK0, fun M => ?_⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  set K : ℝ := 1 + ∑ q, (I.quotWeight 1 q)⁻¹ with hKdef
  set W : ℝ := ∑ q', I'.quotWeight 1 q' with hWdef
  set S : ℝ := ∑ q', ∑ q, ‖linearMapEntry M q' q‖ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsum : ∑ q, I.quotWeight 1 q * ‖f q‖ ^ 2 ≤ 1 := by
    have h1 : Real.sqrt (∑ q, I.quotWeight 1 q * ‖f q‖ ^ 2) ≤ 1 := by
      have := hf.2.2
      simpa [wNorm, tsum_fintype] using this
    simpa using (Real.sqrt_le_iff.mp h1).2
  have hfq : ∀ q, ‖f q‖ ≤ K := fun q => by
    have h1 : I.quotWeight 1 q * ‖f q‖ ^ 2 ≤ 1 :=
      le_trans (Finset.single_le_sum (f := fun q => I.quotWeight 1 q * ‖f q‖ ^ 2)
        (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)) (Finset.mem_univ q)) hsum
    have h2 : ‖f q‖ ^ 2 ≤ (I.quotWeight 1 q)⁻¹ := by
      rw [← one_div, le_div_iff₀ (hw q)]
      linarith
    have h3 : (I.quotWeight 1 q)⁻¹ ≤ ∑ q, (I.quotWeight 1 q)⁻¹ :=
      Finset.single_le_sum (f := fun q => (I.quotWeight 1 q)⁻¹)
        (fun i _ => (inv_pos.2 (hw i)).le) (Finset.mem_univ q)
    nlinarith [sq_nonneg (‖f q‖ - 1), norm_nonneg (f q)]
  have hM : ∀ q', M f q' = ∑ q, linearMapEntry M q' q * f q := fun q' => by
    have hf' : f = ∑ q, f q • (Pi.single q 1 : I.UnitQuot → ℂ) := by
      ext x
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hf']
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hMq : ∀ q', ‖M f q'‖ ≤ S * K := fun q' => by
    rw [hM]
    calc ‖∑ q, linearMapEntry M q' q * f q‖ ≤ ∑ q, ‖linearMapEntry M q' q * f q‖ := norm_sum_le _ _
      _ ≤ ∑ q, ‖linearMapEntry M q' q‖ * K := Finset.sum_le_sum fun q _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hfq q) (norm_nonneg _)
      _ = (∑ q, ‖linearMapEntry M q' q‖) * K := by rw [Finset.sum_mul]
      _ ≤ S * K := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun q' => ∑ q, ‖linearMapEntry M q' q‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ q')) hK0
  have hbound : ∑ q', I'.quotWeight 1 q' * ‖M f q'‖ ^ 2 ≤ W * (S * K) ^ 2 := by
    rw [hWdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun q' _ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hMq q') 2) (hw' q').le
  calc wNorm (I'.quotWeight 1) (M f)
      = Real.sqrt (∑ q', I'.quotWeight 1 q' * ‖M f q'‖ ^ 2) := by
        simp [wNorm, tsum_fintype]
    _ ≤ Real.sqrt (W * (S * K) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt W * K * S := by
        rw [Real.sqrt_mul hW0, Real.sqrt_sq (mul_nonneg hS0 hK0)]
        ring
end Norms
section Sets
theorem im_add_two_pi_mul_int (z : ℂ) (k : ℤ) : (z + 2 * Real.pi * (k : ℂ)).im = z.im := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.im_add_two_pi_mul_int <;> assumption
theorem isClosed_imStrip (r : ℝ) : IsClosed (imStrip r) := by
  have h : imStrip r = ⋂ μ, {z : Fin 4 → ℂ | |(z μ).im| ≤ r} := by
    ext z
    simp [imStrip]
  rw [h]
  exact isClosed_iInter fun μ => isClosed_le
    (continuous_abs.comp (Complex.continuous_im.comp (continuous_apply μ))) continuous_const
theorem isClosed_realDualPoints : IsClosed realDualPoints := by
  have h : realDualPoints = ⋂ μ, {z : Fin 4 → ℂ | (z μ).im = 0} := by
    ext z
    simp [Coordinates.ComplexCoordinates.realLocus]
  rw [h]
  exact isClosed_iInter fun μ => isClosed_eq
    (Complex.continuous_im.comp (continuous_apply μ)) continuous_const
theorem isClosed_stripAddShift (δ : ℝ) (p : Fin 4 → ℂ) : IsClosed (stripAddShift δ p) :=
  (isClosed_imStrip _).inter
    ((isClosed_imStrip _).preimage (continuous_id.add continuous_const))
theorem isClosed_stripSubShift (δ : ℝ) (p : Fin 4 → ℂ) : IsClosed (stripSubShift δ p) :=
  (isClosed_imStrip _).inter
    ((isClosed_imStrip _).preimage (continuous_id.sub continuous_const))
theorem addTwoPiInt_mem_imStrip {r : ℝ} {z : Fin 4 → ℂ} (h : z ∈ imStrip r) (e : Fin 4 → ℤ) :
    addTwoPiInt z e ∈ imStrip r := by apply _root_.YangMills.SharedProofs.p29809 <;> assumption
theorem addTwoPiInt_add_mem_imStrip {r : ℝ} {z q : Fin 4 → ℂ} (h : z + q ∈ imStrip r)
    (e : Fin 4 → ℤ) : addTwoPiInt z e + q ∈ imStrip r := fun μ => by
  have hμ : (addTwoPiInt z e + q) μ = (z μ + q μ) + 2 * Real.pi * (e μ : ℂ) := by
    simp only [addTwoPiInt, Pi.add_apply]
    ring
  rw [hμ, im_add_two_pi_mul_int]
  exact h μ
theorem exists_addTwoPiInt_re_le_pi (z : Fin 4 → ℂ) :
    ∃ e : Fin 4 → ℤ, ∀ μ, |(addTwoPiInt z e μ).re| ≤ Real.pi := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.exists_abs_re_addTwoPiInt_le <;> assumption
theorem isCompact_inter_re_le_pi {D : Set (Fin 4 → ℂ)} (hD : IsClosed D) {b : ℝ}
    (hb : ∀ z ∈ D, ∀ μ, |(z μ).im| ≤ b) :
    IsCompact (D ∩ {z | ∀ μ, |(z μ).re| ≤ Real.pi}) := by
  have hcube : IsClosed {z : Fin 4 → ℂ | ∀ μ, |(z μ).re| ≤ Real.pi} := by
    have h : {z : Fin 4 → ℂ | ∀ μ, |(z μ).re| ≤ Real.pi} =
        ⋂ μ, {z : Fin 4 → ℂ | |(z μ).re| ≤ Real.pi} := by
      ext z
      simp
    rw [h]
    exact isClosed_iInter fun μ => isClosed_le
      (continuous_abs.comp (Complex.continuous_re.comp (continuous_apply μ))) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded (hD.inter hcube) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 4 → ℂ)) (r := Real.pi + |b|)).subset ?_
  rintro z ⟨hzD, hz⟩
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  calc ‖z μ‖ ≤ |(z μ).re| + |(z μ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Real.pi + |b| := add_le_add (hz μ) ((hb z hzD μ).trans (le_abs_self b))
end Sets
section Suprema
variable {I I' : PeriodicData}
theorem iSup_quotHomNorm_lt_top (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hw : ∀ q, 0 < I.quotWeight 1 q) (hw' : ∀ q, 0 < I'.quotWeight 1 q)
    {D : Set (Fin 4 → ℂ)} (hD : IsClosed D) {b : ℝ} (hb : ∀ z ∈ D, ∀ μ, |(z μ).im| ≤ b)
    (hinv : ∀ z ∈ D, ∀ e, addTwoPiInt z e ∈ D) {A : (Fin 4 → ℂ) → QuotHom I I'}
    (hh : IsHolomorphicNbhd D A) (hp : IsQuasiPeriodic D A) :
    (⨆ z ∈ D, quotHomNorm (A z)) < ∞ := by
  have := hI.finite_quot
  have := hI'.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  have := Fintype.ofFinite I'.UnitQuot
  obtain ⟨O, -, hDO, hent⟩ := hh
  obtain ⟨C, hC0, hC⟩ := quotHomNorm_le_sum_entries (I := I) (I' := I') hw hw'
  have hKc := isCompact_inter_re_le_pi hD hb
  have hg : ContinuousOn (fun z => ∑ q', ∑ q, ‖linearMapEntry (A z) q' q‖)
      (D ∩ {z | ∀ μ, |(z μ).re| ≤ Real.pi}) := by
    refine continuousOn_finsetSum _ fun q' _ => continuousOn_finsetSum _ fun q _ => ?_
    have h1 : ContinuousOn (fun z (_ : Fin 1) => linearMapEntry (A z) q' q)
        (D ∩ {z | ∀ μ, |(z μ).re| ≤ Real.pi}) :=
      (hent q' q).2.1.mono (inter_subset_left.trans hDO)
    exact ((continuous_apply (0 : Fin 1)).comp_continuousOn h1).norm
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hg
  refine lt_of_le_of_lt (iSup₂_le fun z hz => ?_) (ENNReal.ofReal_lt_top (r := C * B))
  obtain ⟨e, he⟩ := exists_addTwoPiInt_re_le_pi z
  have hz'D := hinv z hz e
  have hback : addTwoPiInt (addTwoPiInt z e) (-e) = z := by
    ext μ
    simp [addTwoPiInt]
  have hper := hp (-e) _ hz'D
  rw [hback] at hper
  rw [hper]
  refine (quotHomNorm_conj_phaseMul_le hI hI' _ _).trans ((hC _).trans ?_)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC0)
  exact (le_abs_self _).trans (hB _ ⟨hz'D, he⟩)
end Suprema
theorem claim_holds (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro I I' hI hI' δ p hδ hp
  have hweight : ∀ J : PeriodicData, IsPeriodic J → ∀ q, 0 < J.quotWeight 1 q := by
    intro J hJ q
    induction q using Quot.ind with
    | mk i =>
      have h1 := ((hQ J J hJ hJ 1 one_pos).2.1 1 (Or.inl rfl)).1.2 i
      show 0 < J.quotWeight 1 (J.mkQuot 1 i)
      rw [h1]
      exact hJ.weight_pos _
  have hdouble : ∀ {z : Fin 4 → ℂ}, z ∈ imStrip δ → z ∈ imStrip (2 * δ) := fun hz μ => by
    have := hz μ
    linarith
  have hadd : ∀ {z : Fin 4 → ℂ}, z ∈ imStrip δ → z + p ∈ imStrip (2 * δ) := fun {z} hz μ => by
    have h1 := hz μ
    have h2 := hp μ
    have h3 : |(z μ + p μ).im| ≤ |(z μ).im| + |(p μ).im| := by
      rw [Complex.add_im]
      exact abs_add_le _ _
    show |(z μ + p μ).im| ≤ 2 * δ
    linarith
  have hsub : ∀ {z : Fin 4 → ℂ}, z ∈ imStrip δ → z - p ∈ imStrip (2 * δ) := fun {z} hz μ => by
    have h1 := hz μ
    have h2 := hp μ
    have h3 : |(z μ - p μ).im| ≤ |(z μ).im| + |(p μ).im| := by
      rw [Complex.sub_im]
      exact abs_sub _ _
    show |(z μ - p μ).im| ≤ 2 * δ
    linarith
  refine ⟨⟨fun z hz => ⟨hdouble hz, hadd hz⟩, fun z hz => ⟨hdouble hz, hsub hz⟩⟩, fun T hT => ?_⟩
  have hw := hweight I hI
  have hw' := hweight I' hI'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact iSup_quotHomNorm_lt_top hI hI' hw hw' (isClosed_imStrip _) (fun z hz => hz)
      (fun z hz e => addTwoPiInt_mem_imStrip hz e) hT.holo_f00 hT.quasiPeriodic_f00
  · refine iSup_quotHomNorm_lt_top hI hI' hw hw' (isClosed_stripAddShift _ _) (fun z hz => hz.1)
      (fun z hz e => ⟨addTwoPiInt_mem_imStrip hz.1 e, addTwoPiInt_add_mem_imStrip hz.2 e⟩)
      hT.holo_f10 hT.quasiPeriodic_f10
  · refine iSup_quotHomNorm_lt_top hI hI' hw hw' (isClosed_stripSubShift _ _) (fun z hz => hz.1)
      (fun z hz e => ⟨addTwoPiInt_mem_imStrip hz.1 e, ?_⟩) hT.holo_f01 hT.quasiPeriodic_f01
    have h := addTwoPiInt_add_mem_imStrip (q := -p) (z := z) (by simpa [sub_eq_add_neg] using hz.2) e
    simpa [sub_eq_add_neg] using h
  · refine iSup_quotHomNorm_lt_top (b := 0) hI hI' hw hw' isClosed_realDualPoints
      (fun z hz μ => by rw [hz μ, abs_zero]) (fun z hz e μ => ?_)
      hT.holo_f11 hT.quasiPeriodic_f11
    show (z μ + 2 * Real.pi * (e μ : ℂ)).im = 0
    rw [im_add_two_pi_mul_int]
    exact hz μ
end YangMills.Construction.PeriodicOperators.StripJetNorms
end
