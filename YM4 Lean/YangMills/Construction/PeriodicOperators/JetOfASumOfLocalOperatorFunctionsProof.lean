import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbolsProof
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.JetOfASumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfASumOfLocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetAdd
open OpFunKernels (IsComponentKernel)
open JetQuad (EqAsJet add)
section Maps
variable {J J' : Type}
theorem linearMap_apply_eq_applyKernel [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (v : J → ℂ)
    (j' : J') : M v j' = applyKernel (linearMapEntry M) v j' := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.linearMap_apply_eq_tsum <;> assumption
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMapOfEntries_add [Finite J] (K K' : J' → J → ℂ) :
    linearMapOfEntries (fun j' j => K j' j + K' j' j) =
      linearMapOfEntries K + linearMapOfEntries K' := by
  classical
  cases nonempty_fintype J
  refine LinearMap.ext fun v => funext fun j' => ?_
  rw [LinearMap.add_apply, Pi.add_apply, linearMap_apply_eq_applyKernel,
    linearMap_apply_eq_applyKernel, linearMap_apply_eq_applyKernel]
  simp only [linearMapEntry_linearMapOfEntries, applyKernel, tsum_fintype, add_mul,
    Finset.sum_add_distrib]
end Maps
section Symbols
variable {I I' : PeriodicData}
theorem fourierSymbol_add {Z Z' : I'.Carrier → I.Carrier → ℂ} {κ : Fin 4 → ℂ}
    (h : SymbolSummableAt I I' Z κ) (h' : SymbolSummableAt I I' Z' κ) (x' : I'.Carrier)
    (x : I.Carrier) :
    fourierSymbol I I' (Z + Z') κ x' x = fourierSymbol I I' Z κ x' x + fourierSymbol I I' Z' κ x' x := by
  simp only [fourierSymbol]
  rw [← (h x' x).of_norm.tsum_add (h' x' x).of_norm]
  refine tsum_congr fun n => ?_
  simp only [symbolSummand, Pi.add_apply, add_mul]
theorem symbolHom_add (H : SymbolOnQuotients.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {Z Z' : I'.Carrier → I.Carrier → ℂ}
    (hZ : IsFiniteRangeAllRates I I' Z)
    (hZ' : IsFiniteRangeAllRates I I' Z')
    (hS : IsFiniteRangeAllRates I I' (Z + Z')) (κ : Fin 4 → ℂ) :
    symbolHom I I' (Z + Z') κ = symbolHom I I' Z κ + symbolHom I I' Z' κ := by
  have := hI.finite_quot
  have f := hZ.summable κ (mem_univ κ)
  have f' := hZ'.summable κ (mem_univ κ)
  have fS := hS.summable κ (mem_univ κ)
  have e : descendMatrix I I' 1 (fourierSymbol I I' (Z + Z') κ) =
      fun q' q => descendMatrix I I' 1 (fourierSymbol I I' Z κ) q' q +
        descendMatrix I I' 1 (fourierSymbol I I' Z' κ) q' q := by
    funext q' q
    obtain ⟨x', rfl⟩ : ∃ x', I'.mkQuot 1 x' = q' := Quot.exists_rep q'
    obtain ⟨x, rfl⟩ : ∃ x, I.mkQuot 1 x = q := Quot.exists_rep q
    have a := (H I I' hI hI' _ hS.periodic).quotSymbol_mkQuot κ fS x' x
    have b := (H I I' hI hI' _ hZ.periodic).quotSymbol_mkQuot κ f x' x
    have b' := (H I I' hI hI' _ hZ'.periodic).quotSymbol_mkQuot κ f' x' x
    simp only [quotSymbol] at a b b'
    rw [a, b, b']
    exact fourierSymbol_add f f' x' x
  simp only [symbolHom]
  rw [e]
  exact linearMapOfEntries_add _ _
theorem summable_mul_blochWave (H : SymbolOnQuotients.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {q : Fin 4 → ℂ}
    {Y : I'.Carrier → I.Carrier → ℂ} {A : (Fin 4 → ℂ) → QuotHom I I'}
    (h : IsComponentKernel I I' q Y A) (κ : Fin 4 → ℂ) (g : I.UnitQuot → ℂ) (x' : I'.Carrier) :
    Summable fun x => Y x' x * blochWave I κ g x := by
  have hs := ((H I I' hI hI' _ h.2.1.periodic).applyKernel_blochWave κ
    (h.2.1.summable κ (mem_univ κ)) g x').1
  have h₁ : Summable fun x => dephasedKernel I I' q Y x' x * blochWave I κ g x :=
    Summable.of_norm hs
  refine (h₁.mul_left (Complex.exp (Complex.I * bilinDot q (toComplexVec (I'.pos x'))))).congr
    fun x => ?_
  simp only [dephasedKernel]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
theorem applyKernel_add {Y Y' : I'.Carrier → I.Carrier → ℂ} {u : I.Carrier → ℂ} {x' : I'.Carrier}
    (h : Summable fun x => Y x' x * u x) (h' : Summable fun x => Y' x' x * u x) :
    applyKernel (Y + Y') u x' = applyKernel Y u x' + applyKernel Y' u x' := by
  simp only [applyKernel, Pi.add_apply, add_mul]
  exact h.tsum_add h'
theorem blochWave_add (κ : Fin 4 → ℂ) (g g' : I.UnitQuot → ℂ) (x : I.Carrier) :
    blochWave I κ (g + g') x = blochWave I κ g x + blochWave I κ g' x := by
  simp [blochWave, mul_add]
end Symbols
theorem holds (hK : OpFunKernels.Claim)
    (hS : OpFunAdd.LocalClosed)
    (hY : SymbolOnQuotients.Claim)
    (hT : CoeffAdditivity.Claim) :
    JetAdd.Claim := by
  intro δ p _ _ F I₁ I₂ hF hI₁ hI₂ ζp ζm T T' hLT hLT'
  have hsum := hS F I₂ I₁ hF hI₂ hI₁ T T' hLT hLT'
  obtain ⟨h0, h1⟩ := hK F I₂ I₁ hF hI₂ hI₁ T hLT
  obtain ⟨h0', h1'⟩ := hK F I₂ I₁ hF hI₂ hI₁ T' hLT'
  obtain ⟨h0s, h1s⟩ := hK F I₂ I₁ hF hI₂ hI₁ (opFunAdd T T') hsum
  obtain ⟨hset, hc10, hc01, hc11⟩ := h1 p ζp ζm
  obtain ⟨hset', hc10', hc01', hc11'⟩ := h1' p ζp ζm
  have hsetS := (h1s p ζp ζm).1
  have hA := Classical.epsilon_spec hset.exists
  have hA' := Classical.epsilon_spec hset'.exists
  have hB : IsActionTriple F I₂ I₁ (opFunAdd T T') p ζp ζm
      ((jetAlong F I₂ I₁ T p ζp ζm).f10 + (jetAlong F I₂ I₁ T' p ζp ζm).f10,
        (jetAlong F I₂ I₁ T p ζp ζm).f01 + (jetAlong F I₂ I₁ T' p ζp ζm).f01,
        (jetAlong F I₂ I₁ T p ζp ζm).f11 + (jetAlong F I₂ I₁ T' p ζp ζm).f11) := by
    intro κ g x'
    obtain ⟨a₁, a₂, a₃⟩ := hA κ g x'
    obtain ⟨b₁, b₂, b₃⟩ := hA' κ g x'
    have t₁ := (hT F I₂ I₁ hF hI₂ hI₁ T T' hLT hLT' (blochWave F p ζp)
      (blochWave F (-p) ζm)).1
    have t₂ := (hT F I₂ I₁ hF hI₂ hI₁ T T' hLT hLT' (blochWave F (-p) ζm)
      (blochWave F (-p) ζm)).1
    have t₃ := (hT F I₂ I₁ hF hI₂ hI₁ T T' hLT hLT' (blochWave F p ζp)
      (blochWave F (-p) ζm)).2
    refine ⟨?_, ?_, ?_⟩
    · rw [t₁, applyKernel_add (summable_mul_blochWave hY hI₂ hI₁ hc10 κ g x')
        (summable_mul_blochWave hY hI₂ hI₁ hc10' κ g x'), a₁, b₁]
      exact (blochWave_add _ _ _ _).symm
    · rw [t₂, applyKernel_add (summable_mul_blochWave hY hI₂ hI₁ hc01 κ g x')
        (summable_mul_blochWave hY hI₂ hI₁ hc01' κ g x'), a₂, b₂]
      exact (blochWave_add _ _ _ _).symm
    · rw [t₃, applyKernel_add (summable_mul_blochWave hY hI₂ hI₁ hc11 κ g x')
        (summable_mul_blochWave hY hI₂ hI₁ hc11' κ g x'), a₃, b₃]
      exact (blochWave_add _ _ _ _).symm
  have hEq := hsetS.unique (Classical.epsilon_spec hsetS.exists) hB
  refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
  · exact symbolHom_add hY hI₂ hI₁ h0 h0' h0s κ
  · exact congrFun (congrArg Prod.fst hEq) κ
  · exact congrFun (congrArg (fun A => A.2.1) hEq) κ
  · exact congrFun (congrArg (fun A => A.2.2) hEq) κ
end YangMills.Construction.PeriodicOperators.JetAdd
end
