import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Periodized
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
variable {P P' : PeriodicData}
theorem norm_symbolSummand_real (K : P'.Carrier → P.Carrier → ℂ) (ξ : AmbientSpace)
    (a' : P'.Carrier) (a : P.Carrier) (n : Fin 4 → ℤ) :
    ‖symbolSummand P P' K (toComplexVec ξ) a' a n‖ = ‖K a' (P.translate n a)‖ := by
  have hdot : ∀ y : AmbientSpace,
      bilinDot (toComplexVec ξ) (toComplexVec y) = ((∑ μ, ξ μ * y μ : ℝ) : ℂ) := by
    intro y
    simp [bilinDot, toComplexVec]
  unfold symbolSummand
  rw [norm_mul, Complex.norm_exp, hdot]
  simp
theorem symbolSummableAt_real (hS : SymbolSeriesClaim) (hP : IsPeriodic P)
    (hP' : IsPeriodic P') (K : P'.Carrier → P.Carrier → ℂ) {r : ℝ} (hr : IsDecayRate P P' K r)
    (ξ : AmbientSpace) : SymbolSummableAt P P' K (toComplexVec ξ) := by
  refine (hS P P' hP hP' K r hr).summableOn_strip _ ?_
  have him : imVec (toComplexVec ξ) = 0 := by
    funext μ
    simp [imVec, toComplexVec]
  change euclidNormVec (imVec (toComplexVec ξ)) < r
  rw [him]
  simpa [euclidNormVec] using hr.1
theorem nsmul_intVec_injective {L : ℕ} (hL : 0 < L) :
    Function.Injective fun n : Fin 4 → ℤ => L • n := by
  intro u v huv
  funext μ
  have hμ := congrFun huv μ
  simp only [Pi.smul_apply, nsmul_eq_mul] at hμ
  exact mul_left_cancel₀ (by exact_mod_cast hL.ne') hμ
theorem periodization_summable (hS : SymbolSeriesClaim) (hP : IsPeriodic P)
    (hP' : IsPeriodic P') (K : P'.Carrier → P.Carrier → ℂ) {r : ℝ} (hr : IsDecayRate P P' K r)
    {L : ℕ} (hL : 0 < L) (a' : P'.Carrier) (a : P.Carrier) :
    PeriodizationSummableAt P P' K L a' a := by
  have h0 := symbolSummableAt_real hS hP hP' K hr 0 a' a
  simp only [norm_symbolSummand_real] at h0
  exact h0.comp_injective (nsmul_intVec_injective hL)
theorem periodization_translate_right (hP : IsPeriodic P) (K : P'.Carrier → P.Carrier → ℂ)
    (L : ℕ) (a' : P'.Carrier) (a : P.Carrier) (m : Fin 4 → ℤ) :
    periodization P P' K L a' (P.translate (L • m) a) = periodization P P' K L a' a := by
  have summand : ∀ n : Fin 4 → ℤ, K a' (P.translate (L • n) (P.translate (L • m) a)) =
      K a' (P.translate (L • (m + n)) a) := by
    intro n
    rw [← hP.translate_add, smul_add]
  unfold periodization
  simp only [summand]
  exact (Equiv.addLeft m).tsum_eq fun n : Fin 4 → ℤ => K a' (P.translate (L • n) a)
theorem periodization_translate_left (hP : IsPeriodic P) (K : P'.Carrier → P.Carrier → ℂ)
    (hK : IsShiftInvariant P P' K) (L : ℕ) (a' : P'.Carrier) (a : P.Carrier) (m : Fin 4 → ℤ) :
    periodization P P' K L (P'.translate (L • m) a') a = periodization P P' K L a' a := by
  have summand : ∀ n : Fin 4 → ℤ, K (P'.translate (L • m) a') (P.translate (L • n) a) =
      K a' (P.translate (L • (n - m)) a) := by
    intro n
    have hn : P.translate (L • n) a = P.translate (L • m) (P.translate (L • (n - m)) a) := by
      rw [← hP.translate_add, ← smul_add, sub_add_cancel]
    rw [hn, hK]
  unfold periodization
  simp only [summand]
  exact (Equiv.subRight m).tsum_eq fun n : Fin 4 → ℤ => K a' (P.translate (L • n) a)
theorem periodization_congr (hO : QuotOrbits.Claim) (hP : IsPeriodic P)
    (hP' : IsPeriodic P') (K : P'.Carrier → P.Carrier → ℂ) (hK : IsShiftInvariant P P' K) (L : ℕ)
    {a₁' a₂' : P'.Carrier} {a₁ a₂ : P.Carrier} (h' : P'.mkQuot L a₁' = P'.mkQuot L a₂')
    (h : P.mkQuot L a₁ = P.mkQuot L a₂) :
    periodization P P' K L a₁' a₁ = periodization P P' K L a₂' a₂ := by
  obtain ⟨m', rfl⟩ := ((hO P' hP').1 L _ _).mp h'
  obtain ⟨m, rfl⟩ := ((hO P hP).1 L _ _).mp h
  rw [periodization_translate_left hP K hK, periodization_translate_right hP]
theorem periodicMatrix_mkQuot (hO : QuotOrbits.Claim) (hP : IsPeriodic P)
    (hP' : IsPeriodic P') (K : P'.Carrier → P.Carrier → ℂ) (hK : IsShiftInvariant P P' K) (L : ℕ)
    (a' : P'.Carrier) (a : P.Carrier) :
    periodicMatrix P P' K L (P'.mkQuot L a') (P.mkQuot L a) = periodization P P' K L a' a := by
  have hex : ∃ z, ∀ b' b, P'.mkQuot L b' = P'.mkQuot L a' → P.mkQuot L b = P.mkQuot L a →
      periodization P P' K L b' b = z :=
    ⟨periodization P P' K L a' a, fun b' b h' h => periodization_congr hO hP hP' K hK L h' h⟩
  exact (Classical.epsilon_spec hex a' a rfl rfl).symm
def quotRep (L : ℕ) (q : P.QuotMod L) : P.Carrier := Quot.out q
theorem mkQuot_quotRep (L : ℕ) (q : P.QuotMod L) :
    P.mkQuot L (quotRep L q) = q := Quot.out_eq q
theorem mkQuot_translate_nsmul (L : ℕ) (n : Fin 4 → ℤ) (a : P.Carrier) :
    P.mkQuot L (P.translate (L • n) a) = P.mkQuot L a :=
  (Quot.sound ⟨n, rfl⟩ : P.mkQuot L a = P.mkQuot L (P.translate (L • n) a)).symm
theorem periodicMatrix_apply_blochWave (hO : QuotOrbits.Claim)
    (hS : SymbolSeriesClaim) (hQ : SymbolOnQuotients.Claim)
    (hP : IsPeriodic P) (hP' : IsPeriodic P') (K : P'.Carrier → P.Carrier → ℂ)
    (hK : IsPeriodicKernel P P' K) {r : ℝ} (hr : IsDecayRate P P' K r) {L : ℕ} (hL : 0 < L)
    (ξ : AmbientSpace) (φ : P.UnitQuot → ℂ) (g : P.QuotMod L → ℂ)
    (hg : ∀ a, g (P.mkQuot L a) = blochWave P (toComplexVec ξ) φ a) (a' : P'.Carrier) :
    applyKernel (periodicMatrix P P' K L) g (P'.mkQuot L a') =
      blochWave P' (toComplexVec ξ)
        (applyKernel (quotSymbol P P' K (toComplexVec ξ)) φ) a' := by
  obtain ⟨hsumm, hact⟩ := (hQ P P' hP hP' K hK).applyKernel_blochWave (toComplexVec ξ)
    (symbolSummableAt_real hS hP hP' K hr ξ) φ a'
  have hbij := (hO P hP).2 L hL (quotRep L) (mkQuot_quotRep L)
  let e : P.QuotMod L × (Fin 4 → ℤ) ≃ P.Carrier := Equiv.ofBijective _ hbij
  have summand : ∀ p : P.QuotMod L × (Fin 4 → ℤ),
      K a' (e p) * blochWave P (toComplexVec ξ) φ (e p) =
        K a' (P.translate (L • p.2) (quotRep L p.1)) * g p.1 := by
    rintro ⟨q, n⟩
    change K a' (P.translate (L • n) (quotRep L q)) *
      blochWave P (toComplexVec ξ) φ (P.translate (L • n) (quotRep L q)) = _
    rw [← hg, mkQuot_translate_nsmul, mkQuot_quotRep]
  have hsum : Summable fun p : P.QuotMod L × (Fin 4 → ℤ) =>
      K a' (P.translate (L • p.2) (quotRep L p.1)) * g p.1 := by
    have h := (e.summable_iff (f := fun a => K a' a * blochWave P (toComplexVec ξ) φ a)).mpr
      hsumm.of_norm
    simpa only [Function.comp_def, summand] using h
  rw [← hact]
  unfold applyKernel
  rw [← e.tsum_eq]
  simp only [summand]
  rw [hsum.tsum_prod]
  refine tsum_congr fun q => ?_
  change _ = ∑' n : Fin 4 → ℤ, K a' (P.translate (L • n) (quotRep L q)) * g q
  rw [tsum_mul_right]
  congr 1
  have := periodicMatrix_mkQuot hO hP hP' K hK.1 L a' (quotRep L q)
  rw [mkQuot_quotRep] at this
  exact this
theorem claim_holds (hO : QuotOrbits.Claim) (hS : SymbolSeriesClaim)
    (hQ : SymbolOnQuotients.Claim) : Claim := by
  intro P P' hP hP' K r hK hr
  exact
    { summable := fun L hL a' a => periodization_summable hS hP hP' K hr hL a' a
      depends_quot := fun L _ a₁' a₂' a₁ a₂ h' h =>
        periodization_congr hO hP hP' K hK.1 L h' h
      matrix_entries := fun L _ a' a => periodicMatrix_mkQuot hO hP hP' K hK.1 L a' a
      acts_by_symbol := fun L hL ξ _ φ g hg a' =>
        periodicMatrix_apply_blochWave hO hS hQ hP hP' K hK hr hL ξ φ g hg a' }
end YangMills.Construction.PeriodicOperators.Periodized
end
