import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRangeProof
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWavesProof
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolTranslation
open InfiniteLattice (AmbientSpace)
variable {I I' : PeriodicData}
def expPhase (I : PeriodicData) (e : Fin 4 → ℤ) (ι : I.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)))
theorem bilinDot_add_right (κ a b : Fin 4 → ℂ) :
    bilinDot κ (a + b) = bilinDot κ a + bilinDot κ b := by
  simp [bilinDot, mul_add, Finset.sum_add_distrib]
theorem bilinDot_sub_right (κ a b : Fin 4 → ℂ) :
    bilinDot κ (a - b) = bilinDot κ a - bilinDot κ b := by
  simp [bilinDot, mul_sub, Finset.sum_sub_distrib]
theorem toComplexVec_add (a b : AmbientSpace) :
    toComplexVec (a + b) = toComplexVec a + toComplexVec b := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem toComplexVec_sub (a b : AmbientSpace) :
    toComplexVec (a - b) = toComplexVec a - toComplexVec b := by
  funext μ
  simp [toComplexVec]
theorem bilinDot_addTwoPiInt (κ v : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    bilinDot (addTwoPiInt κ e) v =
      bilinDot κ v + 2 * Real.pi * bilinDot (toComplexVec (castVec e)) v := by
  simp only [bilinDot, addTwoPiInt, toComplexVec, castVec, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun μ _ => ?_)
  simp only [Complex.ofReal_intCast]
  ring
theorem exp_two_pi_I_bilinDot_int (e n : Fin 4 → ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec n))) = 1 := by
  have h : bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec n)) =
      ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp [bilinDot, toComplexVec, castVec]
  rw [h, Complex.exp_eq_one_iff]
  exact ⟨∑ μ, e μ * n μ, by ring⟩
theorem expPhase_translate (hI : IsPeriodic I) (e n : Fin 4 → ℤ) (ι : I.Carrier) :
    expPhase I e (I.translate n ι) = expPhase I e ι := by
  unfold expPhase
  rw [hI.pos_translate, toComplexVec_add, bilinDot_add_right, mul_add, Complex.exp_add,
    exp_two_pi_I_bilinDot_int, mul_one]
theorem eq_of_mkQuot_eq {α : Type} (I : PeriodicData) (g : I.Carrier → α)
    (h : ∀ n ι, g (I.translate n ι) = g ι) {ι₁ ι₂ : I.Carrier}
    (hc : I.mkQuot 1 ι₁ = I.mkQuot 1 ι₂) : g ι₁ = g ι₂ := by
  let L : I.QuotMod 1 → α := Quot.lift g (by
    rintro a _ ⟨n, rfl⟩
    exact (h _ a).symm)
  exact congrArg L hc
theorem phaseOn_mkQuot (hI : IsPeriodic I) (e : Fin 4 → ℤ) (ι : I.Carrier) :
    phaseOn I e (I.mkQuot 1 ι) = expPhase I e ι := by
  have hex : ∃ z, ∀ ι', I.mkQuot 1 ι' = I.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι'))) = z :=
    ⟨expPhase I e ι, fun ι' h => eq_of_mkQuot_eq I (expPhase I e) (expPhase_translate hI e) h⟩
  exact ((Classical.epsilon_spec hex) ι rfl).symm
theorem phaseOn_ne_zero (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    phaseOn I e c ≠ 0 := by
  obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot 1 ι = c := Quot.exists_rep c
  rw [phaseOn_mkQuot hI]
  exact Complex.exp_ne_zero _
theorem quotSymbol_mkQuot (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ)
    (ι' : I'.Carrier) (ι : I.Carrier) :
    quotSymbol I I' T κ (I'.mkQuot 1 ι') (I.mkQuot 1 ι) = fourierSymbol I I' T κ ι' ι := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolOnQuotients.quotSymbol_apply_mkQuot <;> assumption
theorem exp_bilinDot_addTwoPiInt (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) (a b : AmbientSpace) :
    Complex.exp (Complex.I * bilinDot (addTwoPiInt κ e) (toComplexVec (a - b))) =
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (a - b))) *
        (Complex.exp (2 * Real.pi * Complex.I *
            bilinDot (toComplexVec (castVec e)) (toComplexVec a)) *
          (Complex.exp (2 * Real.pi * Complex.I *
            bilinDot (toComplexVec (castVec e)) (toComplexVec b)))⁻¹) := by
  rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [bilinDot_addTwoPiInt, toComplexVec_sub a b]
  simp only [bilinDot_sub_right]
  ring
theorem symbolSummand_addTwoPiInt (hI : IsPeriodic I) (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) (ι' : I'.Carrier) (ι : I.Carrier) (n : Fin 4 → ℤ) :
    symbolSummand I I' T (addTwoPiInt κ e) ι' ι n =
      ((expPhase I' e ι')⁻¹ * expPhase I e ι) * symbolSummand I I' T κ ι' ι n := by
  have hp := expPhase_translate hI e n ι
  unfold symbolSummand
  rw [exp_bilinDot_addTwoPiInt]
  change _ * (_ * (expPhase I e (I.translate n ι) * (expPhase I' e ι')⁻¹)) = _
  rw [hp]
  ring
theorem fourierSymbol_addTwoPiInt (hI : IsPeriodic I) (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) (ι' : I'.Carrier) (ι : I.Carrier) :
    fourierSymbol I I' T (addTwoPiInt κ e) ι' ι =
      ((expPhase I' e ι')⁻¹ * expPhase I e ι) * fourierSymbol I I' T κ ι' ι := by
  unfold fourierSymbol
  simp_rw [symbolSummand_addTwoPiInt hI T κ e ι' ι]
  exact tsum_mul_left
theorem symbolSummableAt_addTwoPiInt (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ}
    {κ : Fin 4 → ℂ} (e : Fin 4 → ℤ) (h : SymbolSummableAt I I' T κ) :
    SymbolSummableAt I I' T (addTwoPiInt κ e) := by
  intro ι' ι
  simp_rw [symbolSummand_addTwoPiInt hI T κ e ι' ι, norm_mul]
  exact (h ι' ι).mul_left _
theorem quotSymbol_addTwoPiInt_apply (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsShiftInvariant I I' T) (κ : Fin 4 → ℂ)
    (e : Fin 4 → ℤ) (c' : I'.UnitQuot) (c : I.UnitQuot) :
    quotSymbol I I' T (addTwoPiInt κ e) c' c =
      ((phaseOn I' e c')⁻¹ * phaseOn I e c) * quotSymbol I I' T κ c' c := by
  obtain ⟨ι', rfl⟩ : ∃ ι', I'.mkQuot 1 ι' = c' := Quot.exists_rep c'
  obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot 1 ι = c := Quot.exists_rep c
  rw [quotSymbol_mkQuot hI hI' hT, quotSymbol_mkQuot hI hI' hT,
    phaseOn_mkQuot hI, phaseOn_mkQuot hI', fourierSymbol_addTwoPiInt hI]
def invPhaseMul (I : PeriodicData) (e : Fin 4 → ℤ) :
    (I.UnitQuot → ℂ) →ₗ[ℂ] (I.UnitQuot → ℂ) where
  toFun := fun f c => (phaseOn I e c)⁻¹ * f c
  map_add' := fun f g => by
    funext c
    simp [mul_add]
  map_smul' := fun z f => by
    funext c
    simp [mul_left_comm]
def phaseMulUnit (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (Module.End ℂ (I.UnitQuot → ℂ))ˣ where
  val := phaseMul I e
  inv := invPhaseMul I e
  val_inv := by
    refine LinearMap.ext fun f => ?_
    funext c
    simp [Module.End.mul_apply, phaseMul, invPhaseMul, phaseOn_ne_zero hI e c]
  inv_val := by
    refine LinearMap.ext fun f => ?_
    funext c
    simp [Module.End.mul_apply, phaseMul, invPhaseMul, phaseOn_ne_zero hI e c]
theorem ring_inverse_phaseMul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    Ring.inverse (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) = invPhaseMul I e :=
  Ring.inverse_unit (phaseMulUnit hI e)
theorem properties (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) : Properties I I' T where
  exp_phase_eq_of_mkQuot_eq := fun e _ _ h =>
    eq_of_mkQuot_eq I (expPhase I e) (expPhase_translate hI e) h
  quotSymbol_addTwoPiInt := by
    intro κ e hκ
    refine ⟨symbolSummableAt_addTwoPiInt hI e hκ, (phaseMulUnit hI' e).isUnit, fun f => ?_⟩
    rw [ring_inverse_phaseMul hI']
    funext c'
    change ∑' c, quotSymbol I I' T (addTwoPiInt κ e) c' c * f c =
      (phaseOn I' e c')⁻¹ * ∑' c, quotSymbol I I' T κ c' c * (phaseOn I e c * f c)
    rw [← tsum_mul_left]
    refine tsum_congr fun c => ?_
    rw [quotSymbol_addTwoPiInt_apply hI hI' hT.1]
    ring
theorem endoProperties (hI : IsPeriodic I) {T : I.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I T) : EndoProperties I T where
  trace_addTwoPiInt := by
    intro _ κ e _
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.diag_apply, Matrix.of_apply]
    rw [quotSymbol_addTwoPiInt_apply hI hI hT.1, inv_mul_cancel₀ (phaseOn_ne_zero hI e c),
      one_mul]
  det_addTwoPiInt := by
    intro _ _ κ e _
    have hM : Matrix.of (quotSymbol I I T (addTwoPiInt κ e)) =
        Matrix.diagonal (fun c => (phaseOn I e c)⁻¹) * Matrix.of (quotSymbol I I T κ) *
          Matrix.diagonal (fun c => phaseOn I e c) := by
      ext c' c
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.of_apply]
      rw [quotSymbol_addTwoPiInt_apply hI hI hT.1]
      ring
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Finset.prod_inv_distrib]
    have hne : ∏ c, phaseOn I e c ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c _ => phaseOn_ne_zero hI e c
    field_simp
theorem claim_holds : Claim :=
  ⟨fun _ _ hI hI' _ hT => properties hI hI' hT, fun _ hI _ hT => endoProperties hI hT⟩
end YangMills.Construction.PeriodicOperators.SymbolTranslation
end
