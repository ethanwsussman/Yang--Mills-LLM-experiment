import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.JetOfATransposeOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNormProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfATransposeOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TracesOfTheCoefficientsOnPlaneWavesProof
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeJet
open JetQuad (EqAsJet transposeAt)
section BilinDot
theorem bilinDot_add_right (a y z : Fin 4 → ℂ) : bilinDot a (y + z) = bilinDot a y + bilinDot a z := by
  simp [bilinDot, mul_add, Finset.sum_add_distrib]
theorem bilinDot_sub_right (a y z : Fin 4 → ℂ) : bilinDot a (y - z) = bilinDot a y - bilinDot a z := by
  simp [bilinDot, mul_sub, Finset.sum_sub_distrib]
theorem bilinDot_sub_left (a b y : Fin 4 → ℂ) : bilinDot (a - b) y = bilinDot a y - bilinDot b y := by
  simp [bilinDot, sub_mul, Finset.sum_sub_distrib]
theorem bilinDot_neg_left (a y : Fin 4 → ℂ) : bilinDot (-a) y = -bilinDot a y := by
  simp [bilinDot, Finset.sum_neg_distrib]
theorem bilinDot_zero_left (y : Fin 4 → ℂ) : bilinDot 0 y = 0 := by
  simp [bilinDot]
end BilinDot
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem dephasedKernel_zero (I I' : PeriodicData) (Y : I'.Carrier → I.Carrier → ℂ) :
    dephasedKernel I I' 0 Y = Y := by apply _root_.YangMills.Construction.PeriodicOperators.PlaneWaveTraces.dephasedKernel_zero <;> assumption
section Symbols
variable {I I' : PeriodicData}
theorem weightOf_translate (h : IsPeriodic I) (n : Fin 4 → ℤ) (j : I.Carrier) :
    I.weightOf (I.translate n j) = I.weightOf j := by apply _root_.YangMills.Construction.PeriodicOperators.Quotients.weightOf_translate <;> assumption
theorem translate_translate_neg (h : IsPeriodic I) (n : Fin 4 → ℤ) (j : I.Carrier) :
    I.translate n (I.translate (-n) j) = j := by
  rw [← h.translate_add, neg_add_cancel, h.translate_zero]
theorem symbolSummand_dephased_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic I')
    {q : Fin 4 → ℂ} {Y : I'.Carrier → I.Carrier → ℂ} (hY : IsPhaseCovariant I I' q Y)
    (κ : Fin 4 → ℂ) (j : I.Carrier) (j' : I'.Carrier) (n : Fin 4 → ℤ) :
    symbolSummand I' I (dephasedKernel I' I q (kernelTranspose I I' Y)) κ j j' n =
      ((I'.weightOf j' / I.weightOf j : ℝ) : ℂ) *
        symbolSummand I I' (dephasedKernel I I' q Y) (-κ - q) j' j (-n) := by
  have hker : Y (I'.translate n j') j =
      Complex.exp (Complex.I * bilinDot q (toComplexVec (castVec n))) *
        Y j' (I.translate (-n) j) := by
    have e := hY n j' (I.translate (-n) j)
    rwa [translate_translate_neg h] at e
  have e₁ : toComplexVec (I'.pos (I'.translate n j') - I.pos j) =
      toComplexVec (I'.pos j') + toComplexVec (castVec n) -
        toComplexVec (I.pos j) := by
    funext μ
    simp [toComplexVec, h'.pos_translate]
  have e₂ : toComplexVec (I.pos (I.translate (-n) j) - I'.pos j') =
      toComplexVec (I.pos j) - toComplexVec (castVec n) -
        toComplexVec (I'.pos j') := by
    funext μ
    simp [toComplexVec, castVec, h.pos_translate, sub_eq_add_neg]
  have hexp : Complex.exp (-(Complex.I * bilinDot q (toComplexVec (I.pos j)))) *
        Complex.exp (Complex.I * bilinDot q (toComplexVec (castVec n))) *
        Complex.exp (Complex.I * bilinDot κ (toComplexVec (I'.pos (I'.translate n j') -
          I.pos j))) =
      Complex.exp (-(Complex.I * bilinDot q (toComplexVec (I'.pos j')))) *
        Complex.exp (Complex.I * bilinDot (-κ - q) (toComplexVec (I.pos (I.translate (-n) j) -
          I'.pos j'))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, e₁, e₂]
    simp only [bilinDot_add_right, bilinDot_sub_right, bilinDot_sub_left, bilinDot_neg_left]
    congr 1
    ring
  simp only [symbolSummand, dephasedKernel, kernelTranspose, wTranspose]
  rw [weightOf_translate h', hker]
  linear_combination (((I'.weightOf j' / I.weightOf j : ℝ) : ℂ) * Y j' (I.translate (-n) j)) * hexp
theorem fourierSymbol_dephased_kernelTranspose (h : IsPeriodic I) (h' : IsPeriodic I')
    {q : Fin 4 → ℂ} {Y : I'.Carrier → I.Carrier → ℂ} (hY : IsPhaseCovariant I I' q Y)
    (κ : Fin 4 → ℂ) (j : I.Carrier) (j' : I'.Carrier) :
    fourierSymbol I' I (dephasedKernel I' I q (kernelTranspose I I' Y)) κ j j' =
      ((I'.weightOf j' / I.weightOf j : ℝ) : ℂ) *
        fourierSymbol I I' (dephasedKernel I I' q Y) (-κ - q) j' j := by
  simp only [fourierSymbol]
  simp_rw [symbolSummand_dephased_kernelTranspose h h' hY κ j j']
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.neg (Fin 4 → ℤ)).tsum_eq fun n =>
    symbolSummand I I' (dephasedKernel I I' q Y) (-κ - q) j' j n
theorem symbolHom_dephased_kernelTranspose (hS : SymbolOnQuotients.Claim)
    (hQ : Quotients.QuotientTransposeNorm) (h : IsPeriodic I)
    (h' : IsPeriodic I') {q : Fin 4 → ℂ} {Y : I'.Carrier → I.Carrier → ℂ}
    (hY : IsPhaseCovariant I I' q Y)
    (hZ : IsFiniteRangeAllRates I I' (dephasedKernel I I' q Y))
    (hZ' : IsFiniteRangeAllRates I' I
      (dephasedKernel I' I q (kernelTranspose I I' Y))) (κ : Fin 4 → ℂ) :
    symbolHom I' I (dephasedKernel I' I q (kernelTranspose I I' Y)) κ =
      quotHomTranspose (symbolHom I I' (dephasedKernel I I' q Y) (-κ - q)) := by
  have := h.finite_quot
  have hent := (hS I I' h h' _ hZ.periodic).quotSymbol_mkQuot
  have hent' := (hS I' I h' h _ hZ'.periodic).quotSymbol_mkQuot
  obtain ⟨-, hw, -⟩ := hQ I I' h h' 1 one_pos
  obtain ⟨-, hw', -⟩ := hQ I' I h' h 1 one_pos
  have w₁ := (hw 1 (Or.inl rfl)).1.2
  have w₂ := (hw' 1 (Or.inl rfl)).1.2
  simp only [symbolHom, quotHomTranspose]
  rw [linearMapEntry_linearMapOfEntries]
  congr 1
  funext c c'
  obtain ⟨j, rfl⟩ := Quot.exists_rep c
  obtain ⟨j', rfl⟩ := Quot.exists_rep c'
  have e₁ := hent' κ (hZ'.summable κ (Set.mem_univ _)) j j'
  have e₂ := hent (-κ - q) (hZ.summable _ (Set.mem_univ _)) j' j
  show quotSymbol I' I _ κ (I.mkQuot 1 j) (I'.mkQuot 1 j') =
    ((I'.quotWeight 1 (I'.mkQuot 1 j') / I.quotWeight 1 (I.mkQuot 1 j) : ℝ) : ℂ) *
      quotSymbol I I' _ (-κ - q) (I'.mkQuot 1 j') (I.mkQuot 1 j)
  rw [e₁, e₂, w₁, w₂, fourierSymbol_dephased_kernelTranspose h h' hY]
end Symbols
theorem claim_holds (hK : OpFunKernels.Claim)
    (hL : OpFunTransposeLocal.Claim)
    (hTa : TransposeTaylor.Claim)
    (hS : SymbolOnQuotients.Claim)
    (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro δ p _ _ F I₁ I₂ hF h₁ h₂ εPlus εMinus T hT
  have hTt := hL F I₂ I₁ hF h₂ h₁ T hT
  obtain ⟨hk₀, hk⟩ := hK F I₂ I₁ hF h₂ h₁ T hT
  obtain ⟨hk₀', hk'⟩ := hK F I₁ I₂ hF h₁ h₂ (opFunTranspose T) hTt
  obtain ⟨-, ⟨hc₁, ho₁, he₁⟩, ⟨hc₂, ho₂, he₂⟩, ⟨hc₃, ho₃, he₃⟩⟩ := hk p εPlus εMinus
  obtain ⟨-, ⟨-, ho₁', he₁'⟩, ⟨-, ho₂', he₂'⟩, ⟨-, ho₃', he₃'⟩⟩ := hk' p εPlus εMinus
  have t₁ := (hTa F I₂ I₁ hF h₂ h₁ T hT (blochWave F p εPlus) 0).1
  have t₂ := (hTa F I₂ I₁ hF h₂ h₁ T hT (blochWave F (-p) εMinus) 0).1
  have t₃ := (hTa F I₂ I₁ hF h₂ h₁ T hT (blochWave F p εPlus) (blochWave F (-p) εMinus)).2
  rw [t₁] at ho₁' he₁'
  rw [t₂] at ho₂' he₂'
  rw [t₃] at ho₃' he₃'
  have t₀ : coeffZero F I₁ I₂ (opFunTranspose T) =
      kernelTranspose I₂ I₁ (coeffZero F I₂ I₁ T) := rfl
  rw [t₀] at hk₀'
  have hc₀ : IsPhaseCovariant I₂ I₁ 0 (coeffZero F I₂ I₁ T) := by
    intro n j' j
    rw [hk₀.periodic.1 n j' j, bilinDot_zero_left]
    simp
  have ho₀ : IsFiniteRangeAllRates I₂ I₁
      (dephasedKernel I₂ I₁ 0 (coeffZero F I₂ I₁ T)) := by
    rwa [dephasedKernel_zero]
  have ho₀' : IsFiniteRangeAllRates I₁ I₂
      (dephasedKernel I₁ I₂ 0 (kernelTranspose I₂ I₁ (coeffZero F I₂ I₁ T))) := by
    rwa [dephasedKernel_zero]
  refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
  · have key := symbolHom_dephased_kernelTranspose hS hQ h₂ h₁ hc₀ ho₀ ho₀' κ
    rw [dephasedKernel_zero, dephasedKernel_zero, sub_zero] at key
    exact key
  · show (jetAlong F I₁ I₂ (opFunTranspose T) p εPlus εMinus).f10 κ =
      quotHomTranspose ((jetAlong F I₂ I₁ T p εPlus εMinus).f10 (-κ - p))
    rw [he₁', he₁]
    exact symbolHom_dephased_kernelTranspose hS hQ h₂ h₁ hc₁ ho₁ ho₁' κ
  · show (jetAlong F I₁ I₂ (opFunTranspose T) p εPlus εMinus).f01 κ =
      quotHomTranspose ((jetAlong F I₂ I₁ T p εPlus εMinus).f01 (-κ + p))
    rw [he₂', he₂]
    have key := symbolHom_dephased_kernelTranspose hS hQ h₂ h₁ hc₂ ho₂ ho₂' κ
    rwa [sub_neg_eq_add] at key
  · show (jetAlong F I₁ I₂ (opFunTranspose T) p εPlus εMinus).f11 κ =
      quotHomTranspose ((jetAlong F I₂ I₁ T p εPlus εMinus).f11 (-κ))
    rw [he₃', he₃]
    have key := symbolHom_dephased_kernelTranspose hS hQ h₂ h₁ hc₃ ho₃ ho₃' κ
    rwa [sub_zero] at key
end YangMills.Construction.PeriodicOperators.TransposeJet
end
