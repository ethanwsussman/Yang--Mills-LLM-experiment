import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.SymbolAtAPoint
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbol
import YangMills.Construction.PeriodicOperators.TransposeOfAPeriodicOperatorProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolPointwise
variable {I I' : PeriodicData}
theorem im_bilinDot_toComplexVec (κ : Fin 4 → ℂ) (y : InfiniteLattice.AmbientSpace) :
    (bilinDot κ (toComplexVec y)).im = ∑ μ, imVec κ μ * y μ := by
  simp [bilinDot, toComplexVec, imVec]
theorem norm_symbolSummand_eq_of_imVec_eq (T : I'.Carrier → I.Carrier → ℂ) {κ κ' : Fin 4 → ℂ}
    (hκ : imVec κ' = imVec κ) (a' : I'.Carrier) (a : I.Carrier) (n : Fin 4 → ℤ) :
    ‖symbolSummand I I' T κ' a' a n‖ = ‖symbolSummand I I' T κ a' a n‖ := by
  have hre : ∀ z : ℂ, (Complex.I * z).re = -z.im := fun z => by simp
  simp only [symbolSummand, norm_mul, Complex.norm_exp, hre, im_bilinDot_toComplexVec, hκ]
theorem fourierSymbol_kernelTranspose (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ) (a : I.Carrier)
    (a' : I'.Carrier) :
    fourierSymbol I' I (kernelTranspose I I' T) κ a a' =
      ((I'.weightOf a' / I.weightOf a : ℝ) : ℂ) * fourierSymbol I I' T (-κ) a' a := by apply _root_.YangMills.Construction.PeriodicOperators.TransposeProof.fourierSymbol_kernelTranspose <;> assumption
theorem symbolSummableAt_kernelTranspose (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I I' T) {κ : Fin 4 → ℂ}
    (hs : SymbolSummableAt I I' T (-κ)) : SymbolSummableAt I' I (kernelTranspose I I' T) κ := by apply _root_.YangMills.Construction.PeriodicOperators.TransposeProof.symbolSummableAt_kernelTranspose <;> assumption
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem norm_phaseOn
    (hdep : ∀ (e : Fin 4 → ℤ) a₁ a₂, I.mkQuot 1 a₁ = I.mkQuot 1 a₂ →
      Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a₁))) =
        Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a₂))))
    (e : Fin 4 → ℤ) (c : I.UnitQuot) : ‖phaseOn I e c‖ = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, I.mkQuot 1 a = c := Quot.exists_rep c
  have hex : ∃ z, ∀ a₁, I.mkQuot 1 a₁ = I.mkQuot 1 a →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a₁))) = z :=
    ⟨_, fun a₁ hc => hdep e a₁ a hc⟩
  have hv : phaseOn I e (I.mkQuot 1 a) = Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a))) :=
    ((Classical.epsilon_spec hex) a rfl).symm
  have hr : bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos a)) =
      ((∑ μ, castVec e μ * I.pos a μ : ℝ) : ℂ) := by
    simp [bilinDot, toComplexVec]
  rw [hv, hr, show (2 * Real.pi * Complex.I *
      ((∑ μ, castVec e μ * I.pos a μ : ℝ) : ℂ)) =
      ((2 * Real.pi * ∑ μ, castVec e μ * I.pos a μ : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _
theorem wNorm_mul_unimodular {J : Type} (w : J → ℝ) {p : J → ℂ} (hp : ∀ c, ‖p c‖ = 1)
    (f : J → ℂ) : wNorm w (fun c => p c * f c) = wNorm w f := by
  simp only [wNorm, norm_mul, hp, one_mul]
theorem normSummable_mul_unimodular {J : Type} (w : J → ℝ) {p : J → ℂ} (hp : ∀ c, ‖p c‖ = 1)
    (f : J → ℂ) : NormSummable w (fun c => p c * f c) ↔ NormSummable w f := by
  simp only [NormSummable, norm_mul, hp, one_mul]
theorem quotHomNorm_comp_comp (M : QuotHom I I') (E : QuotHom I I) (G : QuotHom I' I')
    (hE : ∀ f, wNorm (I.quotWeight 1) (E f) = wNorm (I.quotWeight 1) f)
    (hE' : ∀ f, NormSummable (I.quotWeight 1) (E f) ↔ NormSummable (I.quotWeight 1) f)
    (hsurj : Function.Surjective E)
    (hG : ∀ g, wNorm (I'.quotWeight 1) (G g) = wNorm (I'.quotWeight 1) g) :
    quotHomNorm (G.comp (M.comp E)) = quotHomNorm M := by
  unfold quotHomNorm wOpNorm
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    have hb : E f ∈ wUnitBall (I.quotWeight 1) univ :=
      ⟨mem_univ _, (hE' f).2 hf.2.1, by rw [hE]; exact hf.2.2⟩
    refine le_iSup₂_of_le (E f) hb ?_
    simp only [LinearMap.comp_apply, hG, le_refl]
  · refine iSup₂_le fun g hg => ?_
    obtain ⟨f, rfl⟩ := hsurj g
    have hb : f ∈ wUnitBall (I.quotWeight 1) univ :=
      ⟨mem_univ _, (hE' f).1 hg.2.1, by rw [← hE]; exact hg.2.2⟩
    refine le_iSup₂_of_le f hb ?_
    simp only [LinearMap.comp_apply, hG, le_refl]
theorem holds (hquots : SymbolOnQuotients.Claim)
    (htrans : SymbolTranslation.Claim)
    (htranspose : Transpose.Claim)
    (hquot : Quotients.QuotientTransposeNorm) : Properties := by
  intro I I' h h' T κ hper hs
  have := h.finite_quot
  have := h'.finite_quot
  have hcl := hquots I I' h h' T hper
  have htf := htrans.1 I I' h h' T hper
  obtain ⟨hcov, C, δ, hC, hδ, hb⟩ := id hper
  have hperT := (htranspose I I' h h' T δ hper ⟨hδ, C, hC, hb⟩).periodic
  have hsT : SymbolSummableAt I' I (kernelTranspose I I' T) (-κ) :=
    symbolSummableAt_kernelTranspose h h' hcov (by rwa [neg_neg])
  have happ : ∀ (κ₀ : Fin 4 → ℂ) (f : I.UnitQuot → ℂ),
      symbolHom I I' T κ₀ f = applyKernel (quotSymbol I I' T κ₀) f :=
    fun κ₀ f => linearMapOfEntries_eq_applyKernel _ f
  have htranslation : ∀ e : Fin 4 → ℤ, symbolHom I I' T (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I' e)).comp
        ((symbolHom I I' T κ).comp (phaseMul I e)) := by
    intro e
    refine LinearMap.ext fun f => ?_
    obtain ⟨-, -, hact⟩ := htf.quotSymbol_addTwoPiInt κ e hs
    rw [happ, hact f]
    show _ = quotHomInverse (phaseMul I' e)
      (symbolHom I I' T κ (phaseMul I e f))
    rw [happ]
    rfl
  have hphase := norm_phaseOn (I := I) htf.exp_phase_eq_of_mkQuot_eq
  have hphase' := norm_phaseOn (I := I') (htrans.1 I' I h' h _ hperT).exp_phase_eq_of_mkQuot_eq
  refine ⟨fun κ' hκ a' a => ?_, hcl.fourierSymbol_congr_mkQuot κ hs, fun a' a => ?_, htranslation,
    fun e => ?_, hperT, hsT, ?_⟩
  · simp_rw [norm_symbolSummand_eq_of_imVec_eq T hκ]
    exact hs a' a
  · have e₁ := congrFun (congrFun (linearMapEntry_linearMapOfEntries
      (descendMatrix I I' 1 (fourierSymbol I I' T κ))) (I'.mkQuot 1 a')) (I.mkQuot 1 a)
    exact e₁.trans (hcl.quotSymbol_mkQuot κ hs a' a)
  · obtain ⟨-, hunit, -⟩ := htf.quotSymbol_addTwoPiInt κ e hs
    have hcancel : ∀ g, phaseMul I' e (quotHomInverse (phaseMul I' e) g) = g :=
      fun g => LinearMap.congr_fun (Ring.mul_inverse_cancel _ hunit) g
    rw [htranslation e]
    refine quotHomNorm_comp_comp _ _ _ (fun f => wNorm_mul_unimodular _ (hphase e) f)
      (fun f => normSummable_mul_unimodular _ (hphase e) f) (fun g => ?_) (fun g => ?_)
    · refine ⟨fun c => (phaseOn I e c)⁻¹ * g c, ?_⟩
      funext c
      have hne : phaseOn I e c ≠ 0 := by
        intro e₀
        have := hphase e c
        simp [e₀] at this
      show phaseOn I e c * ((phaseOn I e c)⁻¹ * g c) = g c
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    · conv_rhs => rw [← hcancel g]
      exact (wNorm_mul_unimodular _ (hphase' e) _).symm
  · obtain ⟨-, hw, -⟩ := hquot I I' h h' 1 one_pos
    have hw₁ := (hw 1 (Or.inl rfl)).1.2
    obtain ⟨-, hw', -⟩ := hquot I' I h' h 1 one_pos
    have hw₂ := (hw' 1 (Or.inl rfl)).1.2
    funext c c'
    obtain ⟨a, rfl⟩ := Quot.exists_rep c
    obtain ⟨a', rfl⟩ := Quot.exists_rep c'
    have e₁ := (hquots I' I h' h _ hperT).quotSymbol_mkQuot (-κ) hsT a a'
    have e₂ := hcl.quotSymbol_mkQuot κ hs a' a
    show quotSymbol I' I (kernelTranspose I I' T) (-κ) (I.mkQuot 1 a) (I'.mkQuot 1 a') =
      ((I'.quotWeight 1 (I'.mkQuot 1 a') / I.quotWeight 1 (I.mkQuot 1 a) : ℝ) : ℂ) *
        quotSymbol I I' T κ (I'.mkQuot 1 a') (I.mkQuot 1 a)
    rw [e₁, e₂, hw₁, hw₂, fourierSymbol_kernelTranspose h h' hcov, neg_neg]
end YangMills.Construction.PeriodicOperators.SymbolPointwise
end
