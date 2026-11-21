import YangMills.Construction.PeriodicOperators.SumsOfExponentialsProof
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolOnQuotients
variable {I I' : PeriodicData}
theorem exists_translate_of_mkQuot_eq (hI : IsPeriodic I) {a b : I.Carrier}
    (h : I.mkQuot 1 a = I.mkQuot 1 b) : ∃ n : Fin 4 → ℤ, b = I.translate n a := by apply _root_.YangMills.Construction.PeriodicOperators.ExponentialSums.exists_translate_of_mkQuot_eq <;> assumption
theorem mkQuot_translate (n : Fin 4 → ℤ) (a : I.Carrier) :
    I.mkQuot 1 (I.translate n a) = I.mkQuot 1 a :=
  (Quot.sound ⟨n, by simp⟩ : I.mkQuot 1 a = I.mkQuot 1 (I.translate n a)).symm
theorem bilinDot_sub (κ : Fin 4 → ℂ) (a b : InfiniteLattice.AmbientSpace) :
    bilinDot κ (toComplexVec (a - b)) = bilinDot κ (toComplexVec a) - bilinDot κ (toComplexVec b) := by
  simp [bilinDot, toComplexVec, mul_sub, Finset.sum_sub_distrib]
theorem fourierSymbol_translate_right (hI : IsPeriodic I) (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (ι' : I'.Carrier) (ι : I.Carrier) (m : Fin 4 → ℤ) :
    fourierSymbol I I' T κ ι' (I.translate m ι) = fourierSymbol I I' T κ ι' ι := by
  have term : ∀ n, symbolSummand I I' T κ ι' (I.translate m ι) n =
      symbolSummand I I' T κ ι' ι (m + n) := by
    intro n
    simp only [symbolSummand, hI.translate_add]
  unfold fourierSymbol
  simp only [term]
  exact (Equiv.addLeft m).tsum_eq (symbolSummand I I' T κ ι' ι)
theorem fourierSymbol_translate_left (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : I'.Carrier → I.Carrier → ℂ) (hT : IsShiftInvariant I I' T)
    (κ : Fin 4 → ℂ) (ι' : I'.Carrier) (ι : I.Carrier) (m : Fin 4 → ℤ) :
    fourierSymbol I I' T κ (I'.translate m ι') ι = fourierSymbol I I' T κ ι' ι := by
  have term : ∀ n, symbolSummand I I' T κ (I'.translate m ι') ι n =
      symbolSummand I I' T κ ι' ι (n - m) := by
    intro n
    have hn : I.translate n ι = I.translate m (I.translate (n - m) ι) := by
      rw [← hI.translate_add, sub_add_cancel]
    have hpos : I.pos (I.translate n ι) - I'.pos (I'.translate m ι') =
        I.pos (I.translate (n - m) ι) - I'.pos ι' := by
      rw [hn, hI.pos_translate, hI'.pos_translate]
      abel
    unfold symbolSummand
    rw [hpos, hn, hT]
  unfold fourierSymbol
  simp only [term]
  exact (Equiv.subRight m).tsum_eq (symbolSummand I I' T κ ι' ι)
theorem fourierSymbol_congr (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : I'.Carrier → I.Carrier → ℂ) (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ)
    {ι₁' ι₂' : I'.Carrier} {ι₁ ι₂ : I.Carrier}
    (h' : I'.mkQuot 1 ι₁' = I'.mkQuot 1 ι₂') (h : I.mkQuot 1 ι₁ = I.mkQuot 1 ι₂) :
    fourierSymbol I I' T κ ι₁' ι₁ = fourierSymbol I I' T κ ι₂' ι₂ := by
  obtain ⟨m', rfl⟩ := exists_translate_of_mkQuot_eq hI' h'
  obtain ⟨m, rfl⟩ := exists_translate_of_mkQuot_eq hI h
  rw [fourierSymbol_translate_left hI hI' T hT, fourierSymbol_translate_right hI]
theorem quotSymbol_apply_mkQuot (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : I'.Carrier → I.Carrier → ℂ) (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ)
    (ι' : I'.Carrier) (ι : I.Carrier) :
    quotSymbol I I' T κ (I'.mkQuot 1 ι') (I.mkQuot 1 ι) = fourierSymbol I I' T κ ι' ι := by
  have hex : ∃ z, ∀ a' a, I'.mkQuot 1 a' = I'.mkQuot 1 ι' → I.mkQuot 1 a = I.mkQuot 1 ι →
      fourierSymbol I I' T κ a' a = z :=
    ⟨fourierSymbol I I' T κ ι' ι, fun a' a h' h => fourierSymbol_congr hI hI' T hT κ h' h⟩
  exact (Classical.epsilon_spec hex ι' ι rfl rfl).symm
def ofQuotAndShift (I : PeriodicData) (p : I.UnitQuot × (Fin 4 → ℤ)) : I.Carrier :=
  I.translate p.2 (Quot.out p.1)
theorem mkQuot_out (c : I.UnitQuot) : I.mkQuot 1 (Quot.out c) = c := Quot.out_eq c
theorem ofQuotAndShift_bijective (hI : IsPeriodic I) :
    Function.Bijective (ofQuotAndShift I) := by apply _root_.YangMills.Construction.PeriodicOperators.ExponentialSums.translate_out_bijective <;> assumption
theorem applyKernel_blochWave_eq (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : I'.Carrier → I.Carrier → ℂ) (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ)
    (hκ : SymbolSummableAt I I' T κ) (φ : I.UnitQuot → ℂ) (ι' : I'.Carrier) :
    ApplySummableAt T (blochWave I κ φ) ι' ∧
      applyKernel T (blochWave I κ φ) ι' =
        blochWave I' κ (applyKernel (quotSymbol I I' T κ) φ) ι' := by
  have : Finite I.UnitQuot := hI.finite_quot
  let e : I.UnitQuot × (Fin 4 → ℤ) ≃ I.Carrier := Equiv.ofBijective _ (ofQuotAndShift_bijective hI)
  set E : ℂ := Complex.exp (Complex.I * bilinDot κ (toComplexVec (I'.pos ι'))) with hE
  have term : ∀ p : I.UnitQuot × (Fin 4 → ℤ), T ι' (e p) * blochWave I κ φ (e p) =
      symbolSummand I I' T κ ι' (Quot.out p.1) p.2 * (E * φ p.1) := by
    rintro ⟨c, n⟩
    have hexp : Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos (I.translate n (Quot.out c))))) =
        Complex.exp (Complex.I * bilinDot κ (toComplexVec
          (I.pos (I.translate n (Quot.out c)) - I'.pos ι'))) * E := by
      rw [hE, ← Complex.exp_add, bilinDot_sub]
      congr 1
      ring
    change T ι' (I.translate n (Quot.out c)) * blochWave I κ φ (I.translate n (Quot.out c)) = _
    simp only [blochWave, symbolSummand, mkQuot_translate, mkQuot_out]
    rw [hexp]
    ring
  have hfib : ∀ c : I.UnitQuot, Summable fun n =>
      ‖symbolSummand I I' T κ ι' (Quot.out c) n * (E * φ c)‖ := by
    intro c
    simp only [norm_mul]
    exact (hκ ι' (Quot.out c)).mul_right _
  have hsum : Summable fun p : I.UnitQuot × (Fin 4 → ℤ) =>
      ‖symbolSummand I I' T κ ι' (Quot.out p.1) p.2 * (E * φ p.1)‖ := by
    refine (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr ⟨hfib, ?_⟩
    exact Summable.of_finite
  have hsum' : Summable fun ι => ‖T ι' ι * blochWave I κ φ ι‖ := by
    rw [← e.summable_iff]
    simpa only [Function.comp_def, term] using hsum
  refine ⟨hsum', ?_⟩
  unfold applyKernel
  rw [← e.tsum_eq]
  simp only [term]
  rw [hsum.of_norm.tsum_prod]
  have hc : ∀ c : I.UnitQuot, ∑' n, symbolSummand I I' T κ ι' (Quot.out c) n * (E * φ c) =
      E * (quotSymbol I I' T κ (I'.mkQuot 1 ι') c * φ c) := by
    intro c
    rw [tsum_mul_right]
    have := quotSymbol_apply_mkQuot hI hI' T hT κ ι' (Quot.out c)
    rw [mkQuot_out] at this
    rw [this]
    unfold fourierSymbol
    ring
  simp only [hc]
  rw [tsum_mul_left]
  rfl
theorem claim_holds : Claim := by
  intro I I' hI hI' T hT
  exact
    { fourierSymbol_congr_mkQuot := fun κ _ ι₁' ι₂' ι₁ ι₂ h' h =>
        fourierSymbol_congr hI hI' T hT.1 κ h' h
      quotSymbol_mkQuot := fun κ _ ι' ι => quotSymbol_apply_mkQuot hI hI' T hT.1 κ ι' ι
      applyKernel_blochWave := fun κ hκ φ ι' =>
        applyKernel_blochWave_eq hI hI' T hT.1 κ hκ φ ι' }
end YangMills.Construction.PeriodicOperators.SymbolOnQuotients
end
