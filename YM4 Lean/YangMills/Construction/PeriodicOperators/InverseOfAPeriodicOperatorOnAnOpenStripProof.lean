import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.InverseOfAPeriodicOperatorOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.KernelOfAHolomorphicMatrixFunctionOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpenStripInverse
theorem exists_addTwoPiInt_mem_cell (z : Fin 4 → ℂ) :
    ∃ (w : Fin 4 → ℂ) (n : Fin 4 → ℤ), z = addTwoPiInt w n ∧
      (∀ i, |(w i).re| ≤ Real.pi) ∧ ∀ i, (w i).im = (z i).im := by
  have hpi := Real.pi_pos
  refine ⟨fun i => z i - 2 * Real.pi * ((round ((z i).re / (2 * Real.pi)) : ℤ) : ℂ),
    fun i => round ((z i).re / (2 * Real.pi)), ?_, ?_, ?_⟩
  · funext i
    simp [addTwoPiInt]
  · intro i
    have h := abs_sub_round ((z i).re / (2 * Real.pi))
    have hre : (z i - 2 * Real.pi * ((round ((z i).re / (2 * Real.pi)) : ℤ) : ℂ)).re =
        2 * Real.pi * ((z i).re / (2 * Real.pi) - round ((z i).re / (2 * Real.pi))) := by
      simp
      field_simp
    show |(z i - 2 * Real.pi * ((round ((z i).re / (2 * Real.pi)) : ℤ) : ℂ)).re| ≤ Real.pi
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  · intro i
    simp
theorem isCompact_fundamentalCell (s : ℝ) :
    IsCompact {z : Fin 4 → ℂ | ∀ i, |(z i).re| ≤ Real.pi ∧ |(z i).im| ≤ s} := by
  have h : IsCompact (Icc (-Real.pi) Real.pi ×ℂ Icc (-s) s) := isCompact_Icc.reProdIm isCompact_Icc
  have hp := isCompact_univ_pi (fun _ : Fin 4 => h)
  convert hp using 1
  ext z
  simp [Set.mem_pi, Complex.mem_reProdIm, abs_le]
theorem isUnit_of_isInvertibleQuotHom {P : PeriodicData} {A : QuotHom P P}
    (h : IsInvertibleQuotHom A) :
    IsUnit (A : Module.End ℂ (P.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isUnit_of_isInvertibleQuotHom <;> assumption
theorem quotHomInverse_conj {P : PeriodicData} {A B : QuotHom P P}
    (hA : IsInvertibleQuotHom A) (hB : IsInvertibleQuotHom B) :
    quotHomInverse ((quotHomInverse B).comp (A.comp B)) =
      (quotHomInverse B).comp ((quotHomInverse A).comp B) := by
  obtain ⟨u, hu⟩ := isUnit_of_isInvertibleQuotHom hA
  obtain ⟨v, hv⟩ := isUnit_of_isInvertibleQuotHom hB
  change Ring.inverse (Ring.inverse (B : Module.End ℂ (P.UnitQuot → ℂ)) *
      ((A : Module.End ℂ (P.UnitQuot → ℂ)) * (B : Module.End ℂ (P.UnitQuot → ℂ)))) =
    Ring.inverse (B : Module.End ℂ (P.UnitQuot → ℂ)) *
      (Ring.inverse (A : Module.End ℂ (P.UnitQuot → ℂ)) * (B : Module.End ℂ (P.UnitQuot → ℂ)))
  rw [← hu, ← hv, Ring.inverse_unit, Ring.inverse_unit, ← Units.val_mul, ← Units.val_mul,
    Ring.inverse_unit, ← Units.val_mul, ← Units.val_mul]
  simp [mul_assoc]
theorem quotHomNorm_phaseMul_le_one (hSym : SymbolCalculus.Claim) {P : PeriodicData}
    (hP : IsPeriodic P) (n : Fin 4 → ℤ) :
    quotHomNorm (phaseMul P n : QuotHom P P) ≤ 1 := by
  have hPh := (hSym P P hP hP).2.2.2.1 n
  refine iSup₂_le fun f hf => ?_
  rw [hPh.2.2.2 f]
  exact ENNReal.ofReal_le_one.2 hf.2.2
theorem quotHomNorm_inverse_phaseMul_le_one (hSym : SymbolCalculus.Claim) {P : PeriodicData}
    (hP : IsPeriodic P) (n : Fin 4 → ℤ) (hB : IsInvertibleQuotHom
      (phaseMul P n : QuotHom P P)) :
    quotHomNorm (quotHomInverse (phaseMul P n : QuotHom P P)) ≤ 1 := by
  have hPh := (hSym P P hP hP).2.2.2.1 n
  refine iSup₂_le fun f hf => ?_
  have h := hPh.2.2.2 (quotHomInverse (phaseMul P n : QuotHom P P) f)
  rw [hB.apply_quotHomInverse f] at h
  rw [← h]
  exact ENNReal.ofReal_le_one.2 hf.2.2
theorem boundedOn_of_isQuasiPeriodic (hSym : SymbolCalculus.Claim)
    (hHN : HomNorm.Claim) {P : PeriodicData} (hP : IsPeriodic P)
    {w w' : ℝ} (hw' : 0 < w') (hlt : w' < w) (A : (Fin 4 → ℂ) → QuotHom P P)
    (hc : QuotHomFamilyContinuousOn (n := 4) (openImStrip w) A)
    (hq : IsQuasiPeriodic (openImStrip w) A) : QuotHomFamilyBoundedOn (imStrip w') A := by
  have hN := hHN P P hP hP
  have hInvB := ((hSym P P hP hP).2.2.2.2.2.2.1 w' hw').1
  have hsub : {z : Fin 4 → ℂ | ∀ i, |(z i).re| ≤ Real.pi ∧ |(z i).im| ≤ w'} ⊆
      openImStrip w := fun z hz i => lt_of_le_of_lt (hz i).2 hlt
  have hKb : QuotHomFamilyBoundedOn {z : Fin 4 → ℂ | ∀ i, |(z i).re| ≤ Real.pi ∧ |(z i).im| ≤ w'} A := by
    intro n
    obtain ⟨C, hC⟩ := (isCompact_fundamentalCell w').exists_bound_of_continuousOn ((hc.2 n).mono hsub)
    exact ⟨C, hC⟩
  obtain ⟨C, hC⟩ := (hN.2.2.2.2.1 _ _ A).2 hKb
  refine (hN.2.2.2.2.1 _ (imStrip w') A).1 ⟨C, fun z hz => ?_⟩
  obtain ⟨y, n, rfl, hre, him⟩ := exists_addTwoPiInt_mem_cell z
  have hcell : y ∈ {z : Fin 4 → ℂ | ∀ i, |(z i).re| ≤ Real.pi ∧ |(z i).im| ≤ w'} := by
    intro i
    exact ⟨hre i, by rw [him i]; exact hz i⟩
  have hle : quotHomNorm (A (addTwoPiInt y n)) ≤ quotHomNorm (A y) := by
    rw [hq n y (hsub hcell)]
    have hcomp := hN.2.2.2.2.2.2.1 P hP
    calc quotHomNorm ((quotHomInverse (phaseMul P n)).comp
          ((A y).comp (phaseMul P n)))
        ≤ quotHomNorm (quotHomInverse (phaseMul P n : QuotHom P P)) *
          quotHomNorm ((A y).comp (phaseMul P n)) := hcomp.2 _ _
      _ ≤ 1 * (quotHomNorm (A y) * 1) := by
          refine mul_le_mul' (quotHomNorm_inverse_phaseMul_le_one hSym hP n (hInvB n)) ?_
          exact (hcomp.2 _ _).trans (mul_le_mul' le_rfl (quotHomNorm_phaseMul_le_one hSym hP n))
      _ = quotHomNorm (A y) := by simp
  have hfin : quotHomNorm (A y) ≠ ⊤ := ((hN.1 (A y)).2).ne
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono hfin hle).trans ((le_abs_self _).trans (hC y hcell))
theorem claim_holds (hPt : SymbolPointwise.Properties) (hSym : SymbolCalculus.Claim)
    (hEnt : EntriesDets.Claim)
    (hHN : HomNorm.Claim)
    (hKer : OpenStripHolomorphicKernel.Claim) : Claim := by
  intro P hP w hw T hT hform hhol hinv
  have hOpen : IsOpen (openImStrip w) := hhol.2.1
  have hcontOf : ∀ A : (Fin 4 → ℂ) → QuotHom P P,
      QuotHomFamilyHolomorphicOn (n := 4) (openImStrip w) A →
      QuotHomFamilyContinuousOn (n := 4) (openImStrip w) A := fun A hA =>
    (hEnt.2.2.2.2.2.2.1 4 (openImStrip w) (by norm_num) hOpen).2.1 P P hP hP A hA
  have hInvHol : QuotHomFamilyHolomorphicOn (n := 4) (openImStrip w)
      fun z => quotHomInverse (symbolHom P P T z) :=
    ((hEnt.2.2.1 P hP).2.2.1 _ _ hinv).2 hOpen hhol
  have hStr := (hSym P P hP hP).2.2.2.2.2.2.1 (w / 2) (half_pos hw)
  have hQ : IsQuasiPeriodic (openImStrip w) (symbolHom P P T) := fun n z hz =>
    (hPt P P hP hP T z hT (hform z hz)).2.2.2.1 n
  have hQinv : IsQuasiPeriodic (openImStrip w)
      fun z => quotHomInverse (symbolHom P P T z) := by
    intro n z hz
    show quotHomInverse (symbolHom P P T (addTwoPiInt z n)) = _
    rw [hQ n z hz]
    exact quotHomInverse_conj (hinv z hz) (hStr.1 n)
  have hlt : w / 2 < w := half_lt_self hw
  have hsub : imStrip (w / 2) ⊆ openImStrip w := fun z hz i =>
    lt_of_le_of_lt (hz i) hlt
  have hBd : ∀ A : (Fin 4 → ℂ) → QuotHom P P,
      QuotHomFamilyHolomorphicOn (n := 4) (openImStrip w) A →
      IsQuasiPeriodic (openImStrip w) A → ∀ w' : ℝ, 0 < w' → w' < w →
        QuotHomFamilyBoundedOn (imStrip w') A := fun A hA hq w' h0 h1 =>
    boundedOn_of_isQuasiPeriodic hSym hHN hP h0 h1 A (hcontOf A hA) hq
  obtain ⟨hReal, -, -, -, hFormedInv, hSymbolInv⟩ :=
    hKer P P hP hP w hw _ hInvHol (hBd _ hInvHol hQinv) hQinv
  have hMat : SymbolCalculus.IsStripSymbol P P (w / 2) (symbolHom P P T) :=
    ⟨⟨openImStrip w, hOpen, hsub, fun c' c => hhol.2.2 (c', c)⟩,
      hBd _ hhol hQ _ (half_pos hw) hlt, fun n z hz => hQ n z (hsub hz)⟩
  obtain ⟨h1, -, -, h4, h5, h6, h7, h8⟩ := hStr.2.2.2.2 (symbolHom P P T) hMat T hT
    ⟨fun z hz => hform z (hReal hz), fun _ _ => rfl⟩
    ⟨openImStrip w, hOpen, hsub, hinv⟩
    (hBd _ hInvHol hQinv _ (half_pos hw) hlt)
  exact ⟨h1, h4, h5, h6, h7, h8, hFormedInv, hSymbolInv⟩
end YangMills.Construction.PeriodicOperators.OpenStripInverse
end
