import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZeroProof
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantParts
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbol
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ZeroPartJets
open JetQuad (IsJet EqAsJet)
section Maps
variable {J J' : Type} [Fintype J]
open Classical in
theorem linearMap_eq_applyKernel (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) :
    M f = applyKernel (linearMapEntry M) f := by
  funext c'
  rw [← LinearMap.toMatrix'_mulVec M f]
  simp only [Matrix.mulVec, dotProduct, applyKernel, tsum_fintype, linearMapEntry,
    LinearMap.toMatrix'_apply]
open Classical in
theorem linearMapEntry_linearMapOfEntries (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMapOfEntries_apply (K : J' → J → ℂ) (f : J → ℂ) :
    linearMapOfEntries K f = applyKernel K f := by
  rw [linearMap_eq_applyKernel, linearMapEntry_linearMapOfEntries]
end Maps
section Jets
variable {I I' : PeriodicData}
theorem isHolomorphicNbhd_const (D : Set (Fin 4 → ℂ)) (M : QuotHom I I') :
    IsHolomorphicNbhd D fun _ => M := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isHolomorphicNbhd_const <;> assumption
theorem isQuasiPeriodic_zero (D : Set (Fin 4 → ℂ)) :
    IsQuasiPeriodic D (0 : (Fin 4 → ℂ) → QuotHom I I') := by
  intro e κ _
  simp
theorem isJet_of_zeroPart {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    {A : (Fin 4 → ℂ) → QuotHom I I'} (hA : IsHolomorphicNbhd (imStrip (2 * δ)) A)
    (hq : IsQuasiPeriodic (imStrip (2 * δ)) A) : IsJet δ p (⟨A, 0, 0, 0⟩ : JetQuad I I') :=
  { pos_width := hδ
    mem_imStrip := hp
    holo_f00 := hA
    holo_f10 := isHolomorphicNbhd_const _ 0
    holo_f01 := isHolomorphicNbhd_const _ 0
    holo_f11 := isHolomorphicNbhd_const _ 0
    quasiPeriodic_f00 := hq
    quasiPeriodic_f10 := isQuasiPeriodic_zero _
    quasiPeriodic_f01 := isQuasiPeriodic_zero _
    quasiPeriodic_f11 := isQuasiPeriodic_zero _ }
theorem isUnit_phaseMul (h : SymbolTranslation.Claim) (hI : IsPeriodic I)
    (e : Fin 4 → ℤ) : IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have hT : IsPeriodicKernel I I (fun _ _ => 0) :=
    ⟨fun _ _ _ => rfl, 1, 1, one_pos, one_pos, fun _ _ => by
      simpa using (Real.exp_pos _).le⟩
  have hF : SymbolSummableAt I I (fun _ _ => 0) 0 := fun ι' ι => by
    simp [symbolSummand, summable_zero]
  exact ((h.1 I I hI hI _ hT).quotSymbol_addTwoPiInt 0 e hF).2.1
theorem ringInverse_conj {R : Type} [Ring R] {u a : R} (hu : IsUnit u) (ha : IsUnit a) :
    Ring.inverse (Ring.inverse u * (a * u)) = Ring.inverse u * (Ring.inverse a * u) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.ringInverse_inverse_mul_mul <;> assumption
theorem isQuasiPeriodic_symbolHom (h : SymbolTranslation.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {D : Set (Fin 4 → ℂ)} (hD : SymbolSummableOn I I' T D) :
    IsQuasiPeriodic D (symbolHom I I' T) := by
  intro e κ hκ
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  refine LinearMap.ext fun f => ?_
  have ht := ((h.1 I I' hI hI' T hT).quotSymbol_addTwoPiInt κ e (hD κ hκ)).2.2 f
  simp only [symbolHom, LinearMap.comp_apply, quotHomInverse, linearMapOfEntries_apply]
  exact ht
theorem isHolomorphicNbhd_quotHomInverse {A : (Fin 4 → ℂ) → QuotHom I I} [Finite I.UnitQuot]
    {D : Set (Fin 4 → ℂ)} (hA : IsHolomorphicNbhd D A)
    (hu : ∀ κ ∈ D, IsUnit (A κ : Module.End ℂ (I.UnitQuot → ℂ))) :
    IsHolomorphicNbhd D fun κ => quotHomInverse (A κ) := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.isHolomorphicNbhd_quotHomInverse <;> assumption
end Jets
theorem claim_holds (h : SymbolTranslation.Claim) : Claim := by
  intro I I' hI hI' δ p hδ hp
  refine ⟨fun T hT hS => ?_, ?_, fun T hInv => ?_⟩
  · obtain ⟨O, hO, hDO, hF, hE⟩ := hS
    exact isJet_of_zeroPart hδ hp ⟨O, hO, hDO, hE⟩
      fun e κ hκ => isQuasiPeriodic_symbolHom h hI hI' hT (fun κ hκ => hF κ (hDO hκ)) e κ hκ
  · refine isJet_of_zeroPart hδ hp (isHolomorphicNbhd_const _ LinearMap.id) fun e κ _ => ?_
    have hu := Ring.inverse_mul_cancel _ (isUnit_phaseMul h hI e)
    rw [LinearMap.id_comp]
    exact hu.symm
  · have := hI.finite_quot
    have hJ := hInv.isJet
    have hinv : IsJet δ p (JetQuad.zeroPartInv T) := by
      refine isJet_of_zeroPart hδ hp
        (isHolomorphicNbhd_quotHomInverse hJ.holo_f00 hInv.isUnit_f00) fun e κ hκ => ?_
      have hq := hJ.quasiPeriodic_f00 e κ hκ
      rw [hq]
      exact ringInverse_conj (isUnit_phaseMul h hI e) (hInv.isUnit_f00 κ hκ)
    refine ⟨isJet_of_zeroPart hδ hp hJ.holo_f00 hJ.quasiPeriodic_f00, hinv, ?_, ?_⟩
    · refine ⟨fun κ hκ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
      · exact Ring.inverse_mul_cancel _ (hInv.isUnit_f00 κ hκ)
      all_goals simp [JetQuad.mul, JetQuad.zeroPart, JetQuad.zeroPartInv, JetQuad.one]
    · refine ⟨fun κ hκ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
      · exact Ring.mul_inverse_cancel _ (hInv.isUnit_f00 κ hκ)
      all_goals simp [JetQuad.mul, JetQuad.zeroPart, JetQuad.zeroPartInv, JetQuad.one]
end YangMills.Construction.PeriodicOperators.ZeroPartJets
end
