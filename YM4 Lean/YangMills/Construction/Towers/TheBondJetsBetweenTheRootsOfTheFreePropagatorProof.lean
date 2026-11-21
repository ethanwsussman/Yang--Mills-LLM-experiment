import YangMills.Construction.Towers.TheMassiveJetsProof
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJetsProof
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.Towers.BoundOfTheSiteAverageJetProof
import YangMills.Construction.Towers.TheBasicJetsAreBounded
import YangMills.Construction.Towers.TheBondJetsBetweenTheRootsOfTheFreePropagator
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorsInTheirParts
import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertible
import YangMills.Construction.Towers.TheStripOfTheFreeOperatorsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.Tower.FreeStrip
open YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
open YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetDecomposition
open YangMills.Construction.PeriodicOperators.JetNormsAffine (affinePath)
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
section Maps
variable {I I' I'' : PeriodicData}
theorem isUnit_of_isInvertibleQuotHom {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isUnit_of_isInvertibleQuotHom <;> assumption
theorem quotHomTranspose_symbolHom_neg (hSym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {κ : Fin 4 → ℂ} (fT : SymbolSummableAt I I' T (-κ)) :
    quotHomTranspose (symbolHom I I' T (-κ)) = symbolHom I' I (kernelTranspose I I' T) κ := by
  have : Finite I.UnitQuot := hI.finite_quot
  have h := (((hSym.2.1 I I' hI hI').2.1 T (-κ) hT fT).transpose).2.2
  rw [neg_neg] at h
  have e : linearMapEntry (symbolHom I I' T (-κ)) = quotSymbol I I' T (-κ) :=
    linearMapEntry_linearMapOfEntries _
  rw [quotHomTranspose, e]
  show linearMapOfEntries (quotTranspose I I' (quotSymbol I I' T (-κ))) =
    linearMapOfEntries (quotSymbol I' I (kernelTranspose I I' T) κ)
  rw [h]
theorem quotHomNorm_zero (hNorm : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') : quotHomNorm (0 : QuotHom I I') = 0 := by
  have h := ((hNorm I I' hI hI').2.2.2.2.2.1).2.2.2.2 0 (0 : QuotHom I I')
  simpa using h
theorem quotHomTranspose_zero (hNorm : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') : quotHomTranspose (0 : QuotHom I I') = 0 := by
  have h := ((hNorm I' I hI' hI).2.2.2.2.2.2.2.2 0 0 0).2.2.2.1
  have e : wTranspose (I.quotWeight 1) (I'.quotWeight 1) (linearMapEntry (0 : QuotHom I I')) =
      fun c' c => (0 : ℂ) * linearMapEntry (0 : QuotHom I' I) c' c := by
    funext c' c
    simp [wTranspose, linearMapEntry]
  rw [quotHomTranspose, e, ← h]
  simp
theorem symbolHom_compKernel (hSym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  ((hSym.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS
theorem symbolHom_idKernel (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hI : IsPeriodic I) (κ : Fin 4 → ℂ) :
    SymbolSummableAt I I (idKernel I) κ ∧
      symbolHom I I (idKernel I) κ = LinearMap.id := by
  have h := (hSym.2.1 I I hI hI).1.identity κ
  refine ⟨h.1, ?_⟩
  have hu := (hNorm I I hI hI).2.2.2.2.2.2.2.1.1
  have e : symbolHom I I (idKernel I) κ =
      linearMapOfEntries (quotSymbol I I (idKernel I) κ) := rfl
  rw [e, h.2, hu]
theorem interpPlusOne_eq_linComb (I : PeriodicData) (t : ℝ) (A B : I.Carrier → I.Carrier → ℂ) :
    interpPlusOne I t A B =
      StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel (t : ℂ) ((1 - t : ℝ) : ℂ) A B) (idKernel I) := by apply _root_.YangMills.Construction.Tower.FreeStrip.interpPlusOne_eq_linComb <;> assumption
theorem symbolHom_interpPlusOne (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hId : IdKernelFacts.Claim) (hI : IsPeriodic I)
    {X K : I.Carrier → I.Carrier → ℂ} (hX : IsPeriodicKernel I I X) (hK : IsPeriodicKernel I I K)
    {κ : Fin 4 → ℂ} (fX : SymbolSummableAt I I X κ) (fK : SymbolSummableAt I I K κ) (t : ℝ) :
    IsPeriodicKernel I I (interpPlusOne I t X K) ∧
      SymbolSummableAt I I (interpPlusOne I t X K) κ ∧
      symbolHom I I (interpPlusOne I t X K) κ =
        (t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
          scalarQuotHom I 1 := by
  have hi := symbolHom_idKernel hSym hNorm hI κ
  have h₁ := ((hSym.2.1 I I hI hI).2.1 X κ hX fX).linComb K hK fK (t : ℂ) ((1 - t : ℝ) : ℂ)
  have h₂ := ((hSym.2.1 I I hI hI).2.1 _ κ h₁.1 h₁.2.1).linComb (idKernel I)
    (hId I hI).1 hi.1 1 1
  rw [interpPlusOne_eq_linComb]
  refine ⟨h₂.1, h₂.2.1, ?_⟩
  have e := h₂.2.2
  rw [hi.2, h₁.2.2] at e
  simpa [scalarQuotHom] using e
theorem isUnit_triple_symbol (hSym : StripSymbols.Claim) (hI : IsPeriodic I)
    {N B : I.Carrier → I.Carrier → ℂ} {D : Set (Fin 4 → ℂ)} {κ : Fin 4 → ℂ} {C : ℝ} (hκ : κ ∈ D)
    (hN : IsPeriodicKernel I I N) (hB : IsPeriodicKernel I I B)
    (fN : SymbolSummableAt I I N κ) (fB : SymbolSummableAt I I B κ)
    (tri : TripleCompSymbolInvertibleOn I I N B N D C) :
    IsUnit (((symbolHom I I N κ).comp (symbolHom I I B κ)).comp (symbolHom I I N κ) :
        Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse
        (((symbolHom I I N κ).comp (symbolHom I I B κ)).comp (symbolHom I I N κ))) ≤
          ENNReal.ofReal C := by
  have p₁ := symbolHom_compKernel hSym hI hI hI hN hB fN fB
  have p₂ := symbolHom_compKernel hSym hI hI hI p₁.2.1 hN p₁.2.2.1 fN
  have h := tri.2.2.2 κ hκ
  rw [p₂.2.2.2, p₁.2.2.2] at h
  exact ⟨isUnit_of_isInvertibleQuotHom h.1, h.2⟩
theorem linearMapEntry_injective {J J' : Type} [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
theorem quotHomTranspose_quotHomTranspose (hQ : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (M : QuotHom I I') :
    quotHomTranspose (quotHomTranspose M) = M := by
  have := hI.finite_quot
  have := hI'.finite_quot
  have w : ∀ {K : PeriodicData}, IsPeriodic K → ∀ c : K.UnitQuot,
      ((K.quotWeight 1 c : ℝ) : ℂ) ≠ 0 := by
    intro K hK c
    obtain ⟨ι, rfl⟩ : ∃ ι, K.mkQuot 1 ι = c := Quot.exists_rep c
    have h := ((hQ K K hK hK 1 one_pos).2.1 1 (Or.inl rfl)).1.2 ι
    rw [h]
    exact Complex.ofReal_ne_zero.2 (hK.weight_pos _).ne'
  refine linearMapEntry_injective ?_
  rw [quotHomTranspose, linearMapEntry_linearMapOfEntries, quotHomTranspose,
    linearMapEntry_linearMapOfEntries]
  funext c' c
  have h₁ := w hI c
  have h₂ := w hI' c'
  simp only [wTranspose]
  push_cast
  field_simp
end Maps
section Quadruples
variable {I₁ I₂ I₃ : PeriodicData}
theorem jmul_add_left (p : Fin 4 → ℂ) (T T' : JetQuad I₂ I₃) (S : JetQuad I₁ I₂) :
    mul p (add T T') S = add (mul p T S) (mul p T' S) := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [mul, add, Pi.add_apply, LinearMap.add_comp] <;> abel
theorem jmul_add_right (p : Fin 4 → ℂ) (T : JetQuad I₂ I₃) (S S' : JetQuad I₁ I₂) :
    mul p T (add S S') = add (mul p T S) (mul p T S') := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [mul, add, Pi.add_apply, LinearMap.comp_add] <;> abel
theorem jmul_smul_left (p : Fin 4 → ℂ) (z : ℂ) (T : JetQuad I₂ I₃) (S : JetQuad I₁ I₂) :
    mul p (smul z T) S = smul z (mul p T S) := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [mul, smul, Pi.smul_apply, LinearMap.smul_comp, smul_add]
theorem jmul_smul_right (p : Fin 4 → ℂ) (z : ℂ) (T : JetQuad I₂ I₃) (S : JetQuad I₁ I₂) :
    mul p T (smul z S) = smul z (mul p T S) := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [mul, smul, Pi.smul_apply, LinearMap.comp_smul, smul_add]
theorem jmul_one_right (p : Fin 4 → ℂ) (T : JetQuad I₁ I₂) : mul p T (one I₁) = T := by
  apply JetQuad.ext <;> funext κ <;> simp [mul, one]
theorem conjugateBy_add_smul_one (p : Fin 4 → ℂ) (N A W : JetQuad I₁ I₁) (u v : ℂ) :
    conjugateBy p N (add (add A (smul u (one I₁))) (smul v W)) =
      add (add (conjugateBy p N A) (smul u (mul p N N))) (smul v (conjugateBy p N W)) := by
  simp only [conjugateBy, jmul_add_left, jmul_add_right, jmul_smul_left, jmul_smul_right,
    jmul_one_right]
theorem conjugateBy_f00 (p : Fin 4 → ℂ) (N T : JetQuad I₁ I₁) (κ : Fin 4 → ℂ) :
    (conjugateBy p N T).f00 κ = ((N.f00 κ).comp (T.f00 κ)).comp (N.f00 κ) := rfl
theorem addScalarJet_eq (A W : JetQuad I₁ I₁) (τ : ℝ) :
    addScalarJet (A.add W) τ = add (add A (smul (τ : ℂ) (one I₁))) (smul 1 W) := by
  apply JetQuad.ext <;> funext κ <;> simp only [addScalarJet, add, smul, Pi.add_apply, Pi.smul_apply, one_smul] <;> abel
theorem unitShiftedPath_eq (A W : JetQuad I₁ I₁) (t : ℝ) :
    unitShiftedPath A W t = add (add A (smul ((1 : ℝ) : ℂ) (one I₁))) (smul (t : ℂ) W) := rfl
theorem unitShiftedPath_f00 (A W : JetQuad I₁ I₁) (t : ℝ) (κ : Fin 4 → ℂ) :
    (unitShiftedPath A W t).f00 κ =
      (t : ℂ) • (A.add W).f00 κ + ((1 - t : ℝ) : ℂ) • A.f00 κ + scalarQuotHom I₁ 1 := by
  show (A.f00 κ + ((1 : ℝ) : ℂ) • LinearMap.id) + (t : ℂ) • W.f00 κ =
    (t : ℂ) • (A.f00 κ + W.f00 κ) + ((1 - t : ℝ) : ℂ) • A.f00 κ +
      ((1 : ℝ) : ℂ) • LinearMap.id
  push_cast
  module
theorem eqAsJet_refl (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I₁ I₂) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_symm {δ : ℝ} {p : Fin 4 → ℂ} {T S : JetQuad I₁ I₂} (h : EqAsJet δ p T S) :
    EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem eqAsJet_trans {δ : ℝ} {p : Fin 4 → ℂ} {T S R : JetQuad I₁ I₂} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
theorem eqAsJet_add {δ : ℝ} {p : Fin 4 → ℂ} {T T' S S' : JetQuad I₁ I₂} (h : EqAsJet δ p T T')
    (h' : EqAsJet δ p S S') : EqAsJet δ p (add T S) (add T' S') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_add <;> assumption
theorem eqAsJet_smul {δ : ℝ} {p : Fin 4 → ℂ} (z : ℂ) {T T' : JetQuad I₁ I₂} (h : EqAsJet δ p T T') :
    EqAsJet δ p (smul z T) (smul z T') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_smul <;> assumption
theorem conjugateBy_add (p : Fin 4 → ℂ) (N A B : JetQuad I₁ I₁) :
    conjugateBy p N (add A B) = add (conjugateBy p N A) (conjugateBy p N B) := by
  simp only [conjugateBy, jmul_add_left, jmul_add_right]
theorem conjugateBy_smul (p : Fin 4 → ℂ) (N A : JetQuad I₁ I₁) (z : ℂ) :
    conjugateBy p N (smul z A) = smul z (conjugateBy p N A) := by
  simp only [conjugateBy, jmul_smul_left, jmul_smul_right]
theorem transposeAt_transposeAt (hQ : Quotients.QuotientTransposeNorm)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) (p : Fin 4 → ℂ)
    (T : JetQuad I₁ I₂) : transposeAt p (transposeAt p T) = T := by
  apply JetQuad.ext <;> funext κ
  · show quotHomTranspose (quotHomTranspose (T.f00 (- -κ))) = _
    rw [neg_neg, quotHomTranspose_quotHomTranspose hQ h₁ h₂]
  · show quotHomTranspose (quotHomTranspose (T.f10 (-(-κ - p) - p))) = _
    rw [show -(-κ - p) - p = κ by abel, quotHomTranspose_quotHomTranspose hQ h₁ h₂]
  · show quotHomTranspose (quotHomTranspose (T.f01 (-(-κ + p) + p))) = _
    rw [show -(-κ + p) + p = κ by abel, quotHomTranspose_quotHomTranspose hQ h₁ h₂]
  · show quotHomTranspose (quotHomTranspose (T.f11 (- -κ))) = _
    rw [neg_neg, quotHomTranspose_quotHomTranspose hQ h₁ h₂]
end Quadruples
structure JetToolkit (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  pos : 0 < δ
  mem : p ∈ imStrip δ
  opFun : JetDomains.OpFunJetTheory
  jetCalc : JetCalculus.Claim
  args : JetArgumentsAndEqualJets
  homNorm : HomNorm.Claim
namespace JetToolkit
variable {δ : ℝ} {p : Fin 4 → ℂ} {I₁ I₂ I₃ I₄ : PeriodicData}
theorem isJet_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₃} {S : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (mul p T S) :=
  (c.opFun.2.2 I₂ I₃ I₁ h₂ h₃ h₁ δ p c.pos c.mem).mul_isJet T S jT jS
theorem isJet_transpose (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T : JetQuad I₁ I₂} (jT : IsJet δ p T) : IsJet δ p (transposeAt p T) :=
  (c.opFun.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.pos c.mem).transpose_isJet T jT
theorem isJet_add (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T S : JetQuad I₁ I₂} (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (add T S) :=
  (c.opFun.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.pos c.mem).add_isJet T S jT jS
theorem isJet_smul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (z : ℂ) {T : JetQuad I₁ I₂} (jT : IsJet δ p T) : IsJet δ p (smul z T) :=
  (c.opFun.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.pos c.mem).smul_isJet z T jT
theorem isJet_one (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) : IsJet δ p (one I₁) :=
  (c.opFun.2.2 I₁ I₁ I₁ h₁ h₁ h₁ δ p c.pos c.mem).one_isJet
theorem jmul_assoc (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) (h₄ : IsPeriodic I₄) {T : JetQuad I₂ I₁}
    {S : JetQuad I₃ I₂} {R : JetQuad I₄ I₃} (jT : IsJet δ p T) (jS : IsJet δ p S)
    (jR : IsJet δ p R) : EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R)) :=
  ((c.jetCalc δ p c.pos c.mem).1 I₁ I₂ I₃ I₄ h₁ h₂ h₃ h₄ T S R jT jS jR).1
theorem jetNorm_mul_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₁} {S : JetQuad I₃ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) : jetNorm δ p (mul p T S) ≤ jetNorm δ p T * jetNorm δ p S :=
  ((c.jetCalc δ p c.pos c.mem).1 I₁ I₂ I₃ I₃ h₁ h₂ h₃ h₃ T S (one I₃) jT jS (c.isJet_one h₃)).2
theorem transposeAt_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₁} {S : JetQuad I₃ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) :
    EqAsJet δ p (transposeAt p (mul p T S)) (mul p (transposeAt p S) (transposeAt p T)) :=
  ((c.jetCalc δ p c.pos c.mem).2.1 I₁ I₂ I₃ h₁ h₂ h₃ T S jT jS).1
theorem jetNorm_transposeAt (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {T : JetQuad I₂ I₁} (jT : IsJet δ p T) :
    jetNorm δ p (transposeAt p T) = jetNorm δ p T :=
  ((c.jetCalc δ p c.pos c.mem).2.1 I₁ I₂ I₂ h₁ h₂ h₂ T (one I₂) jT (c.isJet_one h₂)).2
theorem jmul_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T T' : JetQuad I₂ I₃} {S S' : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jT' : IsJet δ p T') (jS : IsJet δ p S) (jS' : IsJet δ p S')
    (e : EqAsJet δ p T T') (e' : EqAsJet δ p S S') : EqAsJet δ p (mul p T S) (mul p T' S') :=
  (c.args.2.1 δ p I₂ I₃ h₂ h₃ T T' jT jT' e).2.2.2.2 I₁ h₁ S S' jS jS' e'
theorem jetNorm_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T T' : JetQuad I₁ I₂} (jT : IsJet δ p T) (jT' : IsJet δ p T') (e : EqAsJet δ p T T') :
    jetNorm δ p T = jetNorm δ p T' :=
  (c.args.2.1 δ p I₁ I₂ h₁ h₂ T T' jT jT' e).1
theorem jetNorm_add_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (T S : JetQuad I₁ I₂) : jetNorm δ p (add T S) ≤ jetNorm δ p T + jetNorm δ p S := by
  have hs := ((c.homNorm I₁ I₂ h₁ h₂).2.2.2.2.2.1).2.2.2.1
  have key : ∀ (D : Set (Fin 4 → ℂ)) (f g : (Fin 4 → ℂ) → QuotHom I₁ I₂),
      (⨆ κ ∈ D, quotHomNorm ((f + g) κ)) ≤
        (⨆ κ ∈ D, quotHomNorm (f κ)) + ⨆ κ ∈ D, quotHomNorm (g κ) := fun D f g =>
    iSup₂_le fun κ hκ => (hs (f κ) (g κ)).trans
      (add_le_add (le_iSup₂ (f := fun κ (_ : κ ∈ D) => quotHomNorm (f κ)) κ hκ)
        (le_iSup₂ (f := fun κ (_ : κ ∈ D) => quotHomNorm (g κ)) κ hκ))
  refine (add_le_add (add_le_add (add_le_add (key _ T.f00 S.f00) (key _ T.f10 S.f10))
    (key _ T.f01 S.f01)) (key _ T.f11 S.f11)).trans (le_of_eq ?_)
  simp only [jetNorm]
  ring
theorem jetNorm_smul_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (T : JetQuad I₁ I₂) : jetNorm δ p (smul z T) ≤ jetNorm δ p T := by
  have hs := ((c.homNorm I₁ I₂ h₁ h₂).2.2.2.2.2.1).2.2.2.2
  have key : ∀ M : QuotHom I₁ I₂, quotHomNorm (z • M) ≤ quotHomNorm M := fun M => by
    rw [hs]
    calc quotHomNorm M * ENNReal.ofReal ‖z‖ ≤ quotHomNorm M * 1 := by
          gcongr
          exact ENNReal.ofReal_le_one.2 hz
      _ = quotHomNorm M := mul_one _
  exact add_le_add (add_le_add (add_le_add
    (iSup₂_mono fun κ _ => key _) (iSup₂_mono fun κ _ => key _))
    (iSup₂_mono fun κ _ => key _)) (iSup₂_mono fun κ _ => key _)
theorem jetNorm_le_of_zeroPart (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {T : JetQuad I₁ I₂} {x : ℝ≥0∞} (h10 : ∀ κ, T.f10 κ = 0)
    (h01 : ∀ κ, T.f01 κ = 0) (h11 : ∀ κ, T.f11 κ = 0)
    (h : ∀ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ) ≤ x) : jetNorm δ p T ≤ x := by
  have hz := quotHomNorm_zero c.homNorm h₁ h₂
  simp only [jetNorm, h10, h01, h11, hz]
  simpa using iSup₂_le h
theorem jetNorm_mul_le_ofReal (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₁} {S : JetQuad I₃ I₂} {x y : ℝ}
    (hx : 0 ≤ x) (jT : IsJet δ p T) (jS : IsJet δ p S) (hT : jetNorm δ p T ≤ ENNReal.ofReal x)
    (hS : jetNorm δ p S ≤ ENNReal.ofReal y) :
    jetNorm δ p (mul p T S) ≤ ENNReal.ofReal (x * y) := by
  rw [ENNReal.ofReal_mul hx]
  exact (c.jetNorm_mul_le h₁ h₂ h₃ jT jS).trans (mul_le_mul' hT hS)
theorem conj_transpose_mul_self (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {N : JetQuad I₁ I₁} {S : JetQuad I₁ I₂} (jN : IsJet δ p N)
    (jS : IsJet δ p S) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (conjugateBy p N (mul p (transposeAt p S) S))
      (mul p (transposeAt p (mul p S N)) (mul p S N)) := by
  have jSt := c.isJet_transpose h₁ h₂ jS
  have jNt := c.isJet_transpose h₁ h₁ jN
  have jSN := c.isJet_mul h₁ h₁ h₂ jS jN
  have jNSt := c.isJet_mul h₂ h₁ h₁ jN jSt
  have jStS := c.isJet_mul h₁ h₂ h₁ jSt jS
  have e₁ : EqAsJet δ p (transposeAt p (mul p S N)) (mul p N (transposeAt p S)) :=
    eqAsJet_trans (c.transposeAt_mul h₂ h₁ h₁ jS jN)
      (c.jmul_congr h₂ h₁ h₁ jNt jN (c.isJet_transpose h₁ h₂ jS) jSt hN (eqAsJet_refl _ _ _))
  have e₂ : EqAsJet δ p (mul p (transposeAt p (mul p S N)) (mul p S N))
      (mul p (mul p N (transposeAt p S)) (mul p S N)) :=
    c.jmul_congr h₁ h₂ h₁ (c.isJet_transpose h₁ h₂ jSN) jNSt jSN jSN e₁ (eqAsJet_refl _ _ _)
  have e₃ : EqAsJet δ p (mul p (mul p (mul p N (transposeAt p S)) S) N)
      (mul p (mul p N (transposeAt p S)) (mul p S N)) :=
    c.jmul_assoc h₁ h₂ h₁ h₁ jNSt jS jN
  have e₄ : EqAsJet δ p (mul p (mul p N (transposeAt p S)) S) (mul p N (mul p (transposeAt p S) S)) :=
    c.jmul_assoc h₁ h₁ h₂ h₁ jN jSt jS
  have e₅ : EqAsJet δ p (mul p (mul p (mul p N (transposeAt p S)) S) N)
      (mul p (mul p N (mul p (transposeAt p S) S)) N) :=
    c.jmul_congr h₁ h₁ h₁ (c.isJet_mul h₁ h₂ h₁ jNSt jS) (c.isJet_mul h₁ h₁ h₁ jN jStS) jN jN e₄
      (eqAsJet_refl _ _ _)
  exact eqAsJet_trans (eqAsJet_symm e₅) (eqAsJet_trans e₃ (eqAsJet_symm e₂))
theorem jetNorm_transpose_mul_self_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {S : JetQuad I₁ I₂} {x : ℝ} (hx : 0 ≤ x) (jS : IsJet δ p S)
    (hS : jetNorm δ p S ≤ ENNReal.ofReal x) :
    jetNorm δ p (mul p (transposeAt p S) S) ≤ ENNReal.ofReal (x ^ 2) := by
  rw [sq]
  refine c.jetNorm_mul_le_ofReal h₁ h₂ h₁ hx (c.isJet_transpose h₁ h₂ jS) jS ?_ hS
  rw [c.jetNorm_transposeAt h₂ h₁ jS]
  exact hS
theorem mul_congr_left (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T T' : JetQuad I₂ I₃} {S : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jT' : IsJet δ p T') (jS : IsJet δ p S) (e : EqAsJet δ p T T') :
    EqAsJet δ p (mul p T S) (mul p T' S) :=
  c.jmul_congr h₁ h₂ h₃ jT jT' jS jS e (eqAsJet_refl _ _ _)
theorem mul_congr_right (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₃} {S S' : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) (jS' : IsJet δ p S') (e : EqAsJet δ p S S') :
    EqAsJet δ p (mul p T S) (mul p T S') :=
  c.jmul_congr h₁ h₂ h₃ jT jT jS jS' (eqAsJet_refl _ _ _) e
theorem conjugateBy_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) {N A A' : JetQuad I₁ I₁}
    (jN : IsJet δ p N) (jA : IsJet δ p A) (jA' : IsJet δ p A') (e : EqAsJet δ p A A') :
    EqAsJet δ p (conjugateBy p N A) (conjugateBy p N A') :=
  c.mul_congr_left h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jA) (c.isJet_mul h₁ h₁ h₁ jN jA') jN
    (c.mul_congr_right h₁ h₁ h₁ jN jA jA' e)
theorem transpose_mul_root (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {N : JetQuad I₁ I₁} {S : JetQuad I₁ I₂} (jN : IsJet δ p N)
    (jS : IsJet δ p S) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (transposeAt p (mul p S N)) (mul p N (transposeAt p S)) :=
  eqAsJet_trans (c.transposeAt_mul h₂ h₁ h₁ jS jN)
    (c.mul_congr_left h₂ h₁ h₁ (c.isJet_transpose h₁ h₁ jN) jN (c.isJet_transpose h₁ h₂ jS) hN)
theorem transpose_root_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₃ : IsPeriodic I₃) {N : JetQuad I₁ I₁} {T : JetQuad I₃ I₁} (jN : IsJet δ p N)
    (jT : IsJet δ p T) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (transposeAt p (mul p N T)) (mul p (transposeAt p T) N) :=
  eqAsJet_trans (c.transposeAt_mul h₁ h₁ h₃ jN jT)
    (c.mul_congr_right h₁ h₁ h₃ (c.isJet_transpose h₃ h₁ jT) (c.isJet_transpose h₁ h₁ jN) jN hN)
theorem conj_transpose_mul_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {N : JetQuad I₁ I₁} {S : JetQuad I₁ I₂} {z : JetQuad I₂ I₂}
    (jN : IsJet δ p N) (jS : IsJet δ p S) (jz : IsJet δ p z) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (conjugateBy p N (mul p (transposeAt p S) (mul p z S)))
      (mul p (transposeAt p (mul p S N)) (mul p z (mul p S N))) := by
  have jSt := c.isJet_transpose h₁ h₂ jS
  have jzS := c.isJet_mul h₁ h₂ h₂ jz jS
  have jNSt := c.isJet_mul h₂ h₁ h₁ jN jSt
  have jSN := c.isJet_mul h₁ h₁ h₂ jS jN
  have jX := c.isJet_mul h₁ h₂ h₁ jSt jzS
  have jzSN := c.isJet_mul h₁ h₂ h₂ jz jSN
  have a₁ := c.mul_congr_left h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jX) (c.isJet_mul h₁ h₂ h₁ jNSt jzS) jN
    (eqAsJet_symm (c.jmul_assoc h₁ h₁ h₂ h₁ jN jSt jzS))
  have a₂ := c.jmul_assoc h₁ h₂ h₁ h₁ jNSt jzS jN
  have a₃ := c.mul_congr_right h₁ h₂ h₁ jNSt (c.isJet_mul h₁ h₁ h₂ jzS jN) jzSN
    (c.jmul_assoc h₂ h₂ h₁ h₁ jz jS jN)
  have a₄ := c.mul_congr_left h₁ h₂ h₁ (c.isJet_transpose h₁ h₂ jSN) jNSt jzSN
    (c.transpose_mul_root h₁ h₂ jN jS hN)
  exact eqAsJet_trans a₁ (eqAsJet_trans a₂ (eqAsJet_trans a₃ (eqAsJet_symm a₄)))
theorem conj_mul_transpose (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₃ : IsPeriodic I₃) {N : JetQuad I₁ I₁} {T : JetQuad I₃ I₁} (jN : IsJet δ p N)
    (jT : IsJet δ p T) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (conjugateBy p N (mul p T (transposeAt p T)))
      (mul p (mul p N T) (transposeAt p (mul p N T))) := by
  have jTt := c.isJet_transpose h₃ h₁ jT
  have jNT := c.isJet_mul h₃ h₁ h₁ jN jT
  have jTTt := c.isJet_mul h₁ h₃ h₁ jT jTt
  have a₁ := c.mul_congr_left h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jTTt) (c.isJet_mul h₁ h₃ h₁ jNT jTt) jN
    (eqAsJet_symm (c.jmul_assoc h₁ h₁ h₃ h₁ jN jT jTt))
  have a₂ := c.jmul_assoc h₁ h₃ h₁ h₁ jNT jTt jN
  have a₃ := c.mul_congr_right h₁ h₃ h₁ jNT (c.isJet_transpose h₃ h₁ jNT) (c.isJet_mul h₁ h₁ h₃ jTt jN)
    (c.transpose_root_mul h₁ h₃ jN jT hN)
  exact eqAsJet_trans a₁ (eqAsJet_trans a₂ (eqAsJet_symm a₃))
theorem conj_subtracted (c : JetToolkit δ p) (hQ : Quotients.QuotientTransposeNorm)
    (h₁ : IsPeriodic I₁) (h₃ : IsPeriodic I₃) (h₄ : IsPeriodic I₄)
    {N : JetQuad I₁ I₁} {D : JetQuad I₃ I₁} {R : JetQuad I₃ I₄} (jN : IsJet δ p N)
    (jD : IsJet δ p D) (jR : IsJet δ p R) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p
      (conjugateBy p N (mul p (mul p D (mul p (transposeAt p R) R)) (transposeAt p D)))
      (mul p (mul p (mul p N D) (transposeAt p R))
        (transposeAt p (mul p (mul p N D) (transposeAt p R)))) := by
  have jRt := c.isJet_transpose h₃ h₄ jR
  have jW := c.isJet_mul h₃ h₄ h₃ jRt jR
  have jDt := c.isJet_transpose h₃ h₁ jD
  have jDW := c.isJet_mul h₃ h₃ h₁ jD jW
  have jX := c.isJet_mul h₁ h₃ h₁ jDW jDt
  have jB := c.isJet_mul h₃ h₁ h₁ jN jD
  have jBW := c.isJet_mul h₃ h₃ h₁ jB jW
  have jY := c.isJet_mul h₄ h₃ h₁ jB jRt
  have jDtN := c.isJet_mul h₁ h₁ h₃ jDt jN
  have a₁ := eqAsJet_symm (c.jmul_assoc h₁ h₁ h₃ h₁ jN jDW jDt)
  have a₂ := eqAsJet_symm (c.jmul_assoc h₁ h₁ h₃ h₃ jN jD jW)
  have a₃ := c.mul_congr_left h₁ h₃ h₁ (c.isJet_mul h₃ h₁ h₁ jN jDW) jBW jDt a₂
  have a₅ := c.mul_congr_left h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jX) (c.isJet_mul h₁ h₃ h₁ jBW jDt) jN
    (eqAsJet_trans a₁ a₃)
  have a₆ := c.jmul_assoc h₁ h₃ h₁ h₁ jBW jDt jN
  have a₇ := eqAsJet_symm (c.jmul_assoc h₁ h₃ h₄ h₃ jB jRt jR)
  have a₈ := c.mul_congr_left h₁ h₃ h₁ jBW (c.isJet_mul h₃ h₄ h₁ jY jR) jDtN a₇
  have a₉ := c.jmul_assoc h₁ h₄ h₃ h₁ jY jR jDtN
  have b₁ := c.transposeAt_mul h₁ h₃ h₄ jB jRt
  rw [transposeAt_transposeAt hQ h₃ h₄ p R] at b₁
  have b₂ := c.mul_congr_right h₁ h₃ h₄ jR (c.isJet_transpose h₃ h₁ jB) jDtN
    (c.transpose_root_mul h₁ h₃ jN jD hN)
  have a₁₁ := c.mul_congr_right h₁ h₄ h₁ jY (c.isJet_transpose h₄ h₁ jY) (c.isJet_mul h₁ h₃ h₄ jR jDtN)
    (eqAsJet_trans b₁ b₂)
  exact eqAsJet_trans a₅ (eqAsJet_trans a₆ (eqAsJet_trans a₈ (eqAsJet_trans a₉ (eqAsJet_symm a₁₁))))
theorem conj_correction (c : JetToolkit δ p) (hQ : Quotients.QuotientTransposeNorm)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂) (h₃ : IsPeriodic I₃)
    (h₄ : IsPeriodic I₄) {N : JetQuad I₁ I₁} {B : JetQuad I₁ I₂} {D : JetQuad I₃ I₁}
    {R : JetQuad I₃ I₄} (jN : IsJet δ p N) (jB : IsJet δ p B) (jD : IsJet δ p D)
    (jR : IsJet δ p R) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p
      (conjugateBy p N ((mul p (transposeAt p B) B).add
        (smul (-1) (mul p (mul p D (mul p (transposeAt p R) R)) (transposeAt p D)))))
      ((mul p (transposeAt p (mul p B N)) (mul p B N)).add
        (smul (-1) (mul p (mul p (mul p N D) (transposeAt p R))
          (transposeAt p (mul p (mul p N D) (transposeAt p R)))))) := by
  rw [conjugateBy_add, conjugateBy_smul]
  exact eqAsJet_add (c.conj_transpose_mul_self h₁ h₂ jN jB hN)
    (eqAsJet_smul _ (c.conj_subtracted hQ h₁ h₃ h₄ jN jD jR hN))
theorem jetNorm_conj_operator_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) (h₃ : IsPeriodic I₃) {A N f : JetQuad I₁ I₁}
    {S : JetQuad I₁ I₂} {z : JetQuad I₂ I₂} {T : JetQuad I₃ I₁} {s w x v u : ℝ}
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hx : 0 ≤ x) (hv : 0 ≤ v) (hu : 0 ≤ u) (jA : IsJet δ p A)
    (jN : IsJet δ p N) (jf : IsJet δ p f) (jS : IsJet δ p S) (jz : IsJet δ p z) (jT : IsJet δ p T)
    (hNt : EqAsJet δ p (transposeAt p N) N)
    (hA : EqAsJet δ p A (((mul p (transposeAt p S) (mul p z S)).add f).add (mul p T (transposeAt p T))))
    (hS : jetNorm δ p (mul p S N) ≤ ENNReal.ofReal s) (hz : jetNorm δ p z ≤ ENNReal.ofReal w)
    (hN : jetNorm δ p N ≤ ENNReal.ofReal x) (hf : jetNorm δ p f ≤ ENNReal.ofReal v)
    (hT : jetNorm δ p (mul p N T) ≤ ENNReal.ofReal u) :
    jetNorm δ p (conjugateBy p N A) ≤ ENNReal.ofReal (s * (w * s) + x * v * x + u * u) := by
  have jSt := c.isJet_transpose h₁ h₂ jS
  have jzS := c.isJet_mul h₁ h₂ h₂ jz jS
  have jX := c.isJet_mul h₁ h₂ h₁ jSt jzS
  have jTT := c.isJet_mul h₁ h₃ h₁ jT (c.isJet_transpose h₃ h₁ jT)
  have jSum := c.isJet_add h₁ h₁ (c.isJet_add h₁ h₁ jX jf) jTT
  have jSN := c.isJet_mul h₁ h₁ h₂ jS jN
  have jNT := c.isJet_mul h₃ h₁ h₁ jN jT
  have jzSN := c.isJet_mul h₁ h₂ h₂ jz jSN
  have conj : ∀ {T : JetQuad I₁ I₁}, IsJet δ p T → IsJet δ p (conjugateBy p N T) := fun jT =>
    c.isJet_mul h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jT) jN
  rw [c.jetNorm_congr h₁ h₁ (conj jA) (conj jSum) (c.conjugateBy_congr h₁ jN jA jSum hA),
    conjugateBy_add, conjugateBy_add, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (c.jetNorm_add_le h₁ h₁ _ _).trans
    (add_le_add ((c.jetNorm_add_le h₁ h₁ _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [c.jetNorm_congr h₁ h₁ (conj jX) (c.isJet_mul h₁ h₂ h₁ (c.isJet_transpose h₁ h₂ jSN) jzSN)
      (c.conj_transpose_mul_mul h₁ h₂ jN jS jz hNt)]
    refine c.jetNorm_mul_le_ofReal h₁ h₂ h₁ hs (c.isJet_transpose h₁ h₂ jSN) jzSN ?_
      (c.jetNorm_mul_le_ofReal h₂ h₂ h₁ hw jz jSN hz hS)
    rw [c.jetNorm_transposeAt h₂ h₁ jSN]
    exact hS
  · exact c.jetNorm_mul_le_ofReal h₁ h₁ h₁ (by positivity) (c.isJet_mul h₁ h₁ h₁ jN jf) jN
      (c.jetNorm_mul_le_ofReal h₁ h₁ h₁ hx jN jf hN hf) hN
  · rw [c.jetNorm_congr h₁ h₁ (conj jTT) (c.isJet_mul h₁ h₃ h₁ jNT (c.isJet_transpose h₃ h₁ jNT))
      (c.conj_mul_transpose h₁ h₃ jN jT hNt)]
    refine c.jetNorm_mul_le_ofReal h₁ h₃ h₁ hu jNT (c.isJet_transpose h₃ h₁ jNT) hT ?_
    rw [c.jetNorm_transposeAt h₁ h₃ jNT]
    exact hT
theorem jetNorm_conj_shift_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    {A W N : JetQuad I₁ I₁} {α ω x : ℝ} (hα : 0 ≤ α) (hω : 0 ≤ ω) (hx : 0 ≤ x)
    (jN : IsJet δ p N) (hA : jetNorm δ p (conjugateBy p N A) ≤ ENNReal.ofReal α)
    (hW : jetNorm δ p (conjugateBy p N W) ≤ ENNReal.ofReal ω)
    (hN : jetNorm δ p N ≤ ENNReal.ofReal x) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    jetNorm δ p (conjugateBy p N (add (add A (smul u (one I₁))) (smul v W))) ≤
      ENNReal.ofReal (α + x ^ 2 + ω) := by
  have hNN : jetNorm δ p (mul p N N) ≤ ENNReal.ofReal (x ^ 2) := by
    rw [sq]
    exact c.jetNorm_mul_le_ofReal h₁ h₁ h₁ hx jN jN hN hN
  rw [conjugateBy_add_smul_one, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  exact (c.jetNorm_add_le h₁ h₁ _ _).trans (add_le_add ((c.jetNorm_add_le h₁ h₁ _ _).trans
    (add_le_add hA ((c.jetNorm_smul_le h₁ h₁ hu _).trans hNN)))
    ((c.jetNorm_smul_le h₁ h₁ hv _).trans hW))
theorem jetNorm_gram_sub_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) (h₃ : IsPeriodic I₃) {X : JetQuad I₁ I₂}
    {Y : JetQuad I₃ I₁} {a : ℝ} (ha : 0 ≤ a) (jX : IsJet δ p X) (jY : IsJet δ p Y)
    (hX : jetNorm δ p X ≤ ENNReal.ofReal a) (hY : jetNorm δ p Y ≤ ENNReal.ofReal a) :
    jetNorm δ p ((mul p (transposeAt p X) X).add (smul (-1) (mul p Y (transposeAt p Y)))) ≤
      ENNReal.ofReal (a ^ 2 + a ^ 2) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (c.jetNorm_add_le h₁ h₁ _ _).trans (add_le_add (c.jetNorm_transpose_mul_self_le h₁ h₂ ha jX hX)
    ((c.jetNorm_smul_le h₁ h₁ (by simp) _).trans ?_))
  rw [sq]
  refine c.jetNorm_mul_le_ofReal h₁ h₃ h₁ ha jY (c.isJet_transpose h₃ h₁ jY) hY ?_
  rw [c.jetNorm_transposeAt h₁ h₃ jY]
  exact hY
end JetToolkit
section Data
variable {p : Fin 4 → ℂ} {I J X : PeriodicData}
theorem invertibleWithConjugate_of_bounds (c : JetToolkit stripHalfWidth p) (hI : IsPeriodic I)
    {N T : JetQuad I I} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (jN : IsJet stripHalfWidth p N)
    (hT : IsInvertibleJet stripHalfWidth p T)
    (hU : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      IsUnit ((conjugateBy p N T).f00 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p N T).f00 κ)) ≤ ENNReal.ofReal C)
    (hn : jetNorm stripHalfWidth p (conjugateBy p N T) ≤ ENNReal.ofReal B) :
    InvertibleWithConjugate p N T (C * (1 + C * B) ^ 2) := by
  have jS : IsJet stripHalfWidth p (conjugateBy p N T) :=
    c.isJet_mul hI hI hI (c.isJet_mul hI hI hI jN hT.isJet) jN
  have hS : IsInvertibleJet stripHalfWidth p (conjugateBy p N T) :=
    ⟨jS, fun κ hκ => (hU κ hκ).1,
      lt_of_le_of_lt (iSup₂_le fun κ hκ => (hU κ hκ).2) ENNReal.ofReal_lt_top⟩
  refine ⟨hT, hS, ?_⟩
  have h := (c.jetCalc stripHalfWidth p c.pos c.mem).2.2.2.2.1 I hI _ hS
  have h₀ : jetNorm stripHalfWidth p (zeroPartInv (conjugateBy p N T)) ≤ ENNReal.ofReal C := by
    rw [h.2.2.2.2]
    exact iSup₂_le fun κ hκ => (hU κ hκ).2
  refine h.2.2.2.1.trans ?_
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_mul hC, ENNReal.ofReal_one]
  gcongr
theorem rootInterpolationData_of_bounds (c : JetToolkit stripHalfWidth p) (hI : IsPeriodic I)
    (hJ : IsPeriodic J) (hX : IsPeriodic X) {A W N M : JetQuad I I}
    {Q : JetQuad I J} {y : JetQuad X I} {P : I.Carrier → I.Carrier → ℂ} {α x a g C : ℝ}
    (hα : 0 ≤ α) (hx : 0 ≤ x) (ha : 0 ≤ a) (hC : 0 ≤ C) (jA : IsJet stripHalfWidth p A)
    (jW : IsJet stripHalfWidth p W) (jN : IsJet stripHalfWidth p N) (jM : IsJet stripHalfWidth p M)
    (jQ : IsJet stripHalfWidth p Q) (jy : IsJet stripHalfWidth p y)
    (hMN : EqAsJet stripHalfWidth p (mul p M N) (one I))
    (hNt : EqAsJet stripHalfWidth p (transposeAt p N) N)
    (hsq : EqAsJet stripHalfWidth p (mul p N N) (ofKernel I I P))
    (hP : jetNorm stripHalfWidth p (ofKernel I I P) ≤ ENNReal.ofReal g)
    (hQN : jetNorm stripHalfWidth p (mul p Q N) ≤ ENNReal.ofReal a)
    (hy : jetNorm stripHalfWidth p y ≤ ENNReal.ofReal a)
    (hcorr : EqAsJet stripHalfWidth p (conjugateBy p N W)
      ((mul p (transposeAt p (mul p Q N)) (mul p Q N)).add
        (smul (-1) (mul p y (transposeAt p y)))))
    (hA : jetNorm stripHalfWidth p (conjugateBy p N A) ≤ ENNReal.ofReal α)
    (hN : jetNorm stripHalfWidth p N ≤ ENNReal.ofReal x)
    (fam : ∀ t ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p (unitShiftedPath A W t) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p N (unitShiftedPath A W t)).f00 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p N (unitShiftedPath A W t)).f00 κ)) ≤
          ENNReal.ofReal C)
    (shf : ∀ τ ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p (addScalarJet (A.add W) τ) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p N (addScalarJet (A.add W) τ)).f00 κ :
          Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p N (addScalarJet (A.add W) τ)).f00 κ)) ≤
          ENNReal.ofReal C) :
    RootInterpolationData p A W N M P Q y a
      (C * (1 + C * (α + x ^ 2 + (a ^ 2 + a ^ 2))) ^ 2) g := by
  have jQN := c.isJet_mul hI hI hJ jQ jN
  have hB : 0 ≤ α + x ^ 2 + (a ^ 2 + a ^ 2) := by positivity
  have hω : 0 ≤ a ^ 2 + a ^ 2 := by positivity
  have jSW : IsJet stripHalfWidth p (conjugateBy p N W) :=
    c.isJet_mul hI hI hI (c.isJet_mul hI hI hI jN jW) jN
  have hWs : jetNorm stripHalfWidth p (conjugateBy p N W) ≤ ENNReal.ofReal (a ^ 2 + a ^ 2) := by
    have jR := c.isJet_add hI hI (c.isJet_mul hI hJ hI (c.isJet_transpose hI hJ jQN) jQN)
      (c.isJet_smul hI hI (-1) (c.isJet_mul hI hX hI jy (c.isJet_transpose hX hI jy)))
    rw [c.jetNorm_congr hI hI jSW jR hcorr]
    exact c.jetNorm_gram_sub_le hI hJ hX ha jQN jy hQN hy
  have abs_le_one : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  refine
    { isJet_A := jA
      isJet_W := jW
      isJet_N := jN
      isJet_M := jM
      isJet_Q := jQ
      isJet_y := jy
      left_inv := hMN
      transpose_self := hNt
      mul_self := hsq
      kernel_norm_le := hP
      x_norm_le := hQN
      y_norm_le := hy
      conj_decomp := hcorr
      path := fun t ht =>
        invertibleWithConjugate_of_bounds c hI hB hC jN (fam t ht).1 (fam t ht).2 ?_
      shifted := fun τ hτ =>
        invertibleWithConjugate_of_bounds c hI hB hC jN (shf τ hτ).1 (shf τ hτ).2 ?_ }
  · rw [unitShiftedPath_eq]
    exact c.jetNorm_conj_shift_le hI hα hω hx jN hA hWs hN (by simp) (abs_le_one t ht)
  · rw [addScalarJet_eq]
    exact c.jetNorm_conj_shift_le hI hα hω hx jN hA hWs hN (abs_le_one τ hτ) (by simp)
end Data
section Tower
variable {L k : ℕ}
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = fun _ => 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.gaugeFieldOfForm_zero <;> assumption
theorem covDerivJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (covDerivJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D := by
  simp only [covDerivJet, jetAlongResponse, jetAlong, coeffZero,
    gaugeFieldOfForm_zero, trivialRescaledOperators]
theorem vertexSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R := by apply _root_.YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBoundProof.vertexSmoothingJet_f00 <;> assumption
theorem edgeOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (edgeOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.edgeOperatorJet_f00 <;> assumption
theorem edgeSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (edgeSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q := by
  simp only [edgeSmoothingJet, jetAlongResponse, jetAlong, coeffZero,
    gaugeFieldOfForm_zero, trivialRescaledOperators]
theorem trivial_Xi_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Xi =
      StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).K
          (compKernel (compKernel (trivialRescaledOperators L k).D (trivialRescaledOperators L k).Rt)
            (compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Dt)))
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) := by
  funext ι' ι
  simp [RescaledOperators.Xi, StripSymbols.linCombKernel, sub_eq_add_neg]
end Tower
theorem edgeJetsInterpolate_holds (hNum : ConstantsAdmissible.ConstantsAreAdmissible)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hRoots : ResolventRootsOnStrip.ResolventRootsHold)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hTr : RescaledConditions.Holds)
    (hIter : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hId : IdKernelFacts.Claim)
    (hL : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hBasic : BoundedBasicJets.BasicJetsBounded)
    (hMid : MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hProp : FreeResolventRoots)
    (hParts : OperatorJetDecomposition.DecompositionHolds)
    (hW : ConstantOpFun.Claim)
    (hQuot : Quotients.QuotientTransposeNorm) : EdgeJetsInterpolate := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδI, hC₀, hAdm⟩ := hNum
  have eδ : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  obtain ⟨Cm, hMid'⟩ := hMid
  intro L hLb
  obtain ⟨⟨Cb, hCb0, hCb⟩, -⟩ := hBasic L hLb
  have hC0 : 0 ≤ C₀ := by linarith
  have hs : 0 ≤ C₀ + Cb * C₀ := by positivity
  have hu : 0 ≤ C₀ + C₀ * Cb := by positivity
  have ha : 0 ≤ Cb * C₀ + (C₀ + C₀ * Cb) * Cb := by positivity
  have hα : 0 ≤ (C₀ + Cb * C₀) * (Cb * (C₀ + Cb * C₀)) + C₀ * Cb * C₀ +
      (C₀ + C₀ * Cb) * (C₀ + C₀ * Cb) := by positivity
  refine ⟨Cb * C₀ + (C₀ + C₀ * Cb) * Cb,
    C₀ * (1 + C₀ * (((C₀ + Cb * C₀) * (Cb * (C₀ + Cb * C₀)) + C₀ * Cb * C₀ +
        (C₀ + C₀ * Cb) * (C₀ + C₀ * Cb)) + C₀ ^ 2 +
      ((Cb * C₀ + (C₀ + C₀ * Cb) * Cb) ^ 2 + (Cb * C₀ + (C₀ + C₀ * Cb) * Cb) ^ 2))) ^ 2,
    C₀ ^ 2, ha, by positivity, by positivity, ?_⟩
  intro k hk p hp μPlus μMinus
  have hAss : StripBounds L k stripHalfWidth C₀ := by
    rw [eδ]
    exact hAdm.2.2 L hLb k hk
  have hδ : 0 < stripHalfWidth := by rw [eδ]; exact hδI.1
  have hδle : stripHalfWidth ≤ 1 / 32 := by
    rw [eδ]
    have := hδI.2
    linarith
  have hps : p ∈ imStrip stripHalfWidth := fun μ => (Complex.abs_im_le_norm _).trans (hp μ)
  have hc : JetToolkit stripHalfWidth p := ⟨hδ, hps, hL, hCalc, hArgs, hNorm⟩
  have hOps := (hOp.1 L hLb k hk).1
  obtain ⟨hSi, hBo, hPl, hSiK, hBoK⟩ := hOps.periodic
  obtain ⟨hmaps, hops⟩ := hFree.2 L hLb k hk
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hTr L hLb k hk).2
  have hint := hSym.1 (1 / 8) (by norm_num)
  have hopenI : IsOpen (StripSymbols.openStripInterior (1 / 8)) := by
    rw [hint.1]
    exact hint.2.1
  have hstrip : imStrip (2 * stripHalfWidth) ⊆ StripSymbols.openStripInterior (1 / 8) := by
    rw [hint.1]
    exact hint.2.2.2 (2 * stripHalfWidth) (by linarith) (by linarith)
  have hRootB := (hRoots L hLb k hk).1
  have parts := hParts L hLb k hk p hp μPlus μMinus
  have hDeq : (trivialRescaledOperators L k).D = scaledVertexCoboundaryKernel L k 0 := hOne.D_eq
  have oD : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourEdges L k 0)
      (scaledVertexCoboundaryKernel L k 0) := (hmaps.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have oDb : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0)
      (colourFaces L k 0) (scaledEdgeCoboundaryKernel L k 0) :=
    (hmaps.edgeCoboundary 0 (Nat.zero_le k)).finite_range
  have oDf : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).D := by
    rw [hDeq]
    exact oD
  have eDt : (trivialRescaledOperators L k).Dt =
      kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D := rfl
  have oDt : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Dt := by
    rw [eDt, hDeq]
    exact hops.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have oR : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k k)
      (trivialRescaledOperators L k).R := hmaps.vertexAverage.finite_range
  have oRt : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k k) (colourVertices L k 0)
      (trivialRescaledOperators L k).Rt := hops.vertexAverage_transpose
  have oQ : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q := hmaps.edgeAverage.finite_range
  have oQt : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k k) (colourEdges L k 0)
      (trivialRescaledOperators L k).Qt := hops.edgeAverage_transpose
  have oK : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0)
      (colourEdges L k 0) (trivialRescaledOperators L k).K := hops.K
  have oXi : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).Xi := hops.Xi
  have formed : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        ∀ κ, SymbolSummableAt I I' T κ := fun hI hI' _ h κ =>
    (hSym.2.1 _ _ hI hI').1.finiteRange _ h.1 h.2.1 κ (mem_univ κ)
  have jetOp : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        IsJet stripHalfWidth p (ofKernel I I' T) := fun hI hI' _ h =>
    (hL.2.2 _ _ _ hI hI' hI' stripHalfWidth p hδ hps).ofKernel_isJet _ h.1
      (hW _ _ _ hBo hI hI' _ h.1 h.2.1 stripHalfWidth p hδ hps 0 0).1.2.2.2.2.1
  have fD := formed hSi hBo oD
  have fDb := formed hBo hPl oDb
  have fDf := formed hSi hBo oDf
  have fDt := formed hBo hSi oDt
  have fR := formed hSi hSiK oR
  have fRt := formed hSiK hSi oRt
  have fQ := formed hBo hBoK oQ
  have fQt := formed hBoK hBo oQt
  have fK := formed hBo hBo oK
  have fXi := formed hBo hBo oXi
  obtain ⟨ρ, cρ, hρ⟩ : ∃ ρ c,
      YangMills.Construction.Tower.IteratedSmallFieldMeans.AdmissibleConstants L ρ c :=
    ⟨_, _, hIter.1 L hLb⟩
  have lR : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R := by
    obtain ⟨r, R', hm, -⟩ := hOps.R_local ρ cρ hρ
    exact ⟨r, R', hm⟩
  have lQ : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k k) fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q := by
    obtain ⟨r, R', hm, -⟩ := hOps.Q_local ρ cρ hρ
    exact ⟨r, R', hm⟩
  have jK : IsJet stripHalfWidth p (edgeOperatorJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hBo _ hOps.K_local.1).isJet _ hδ p hps _ _
  have jD : IsJet stripHalfWidth p (covDerivJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hBo _ hOps.D_local.1).isJet _ hδ p hps _ _
  have jR : IsJet stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hSiK _ lR).isJet _ hδ p hps _ _
  have jQ : IsJet stripHalfWidth p (edgeSmoothingJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hBoK _ lQ).isJet _ hδ p hps _ _
  have jE : IsJet stripHalfWidth p (holonomyDefectJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hPl _ hOps.holonomyDefect_local.1).isJet _ hδ p hps _ _
  have jz : IsJet stripHalfWidth p (halfFaceTraceJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hPl hPl _ hOps.halfFaceTrace_local.1).isJet _ hδ p hps _ _
  have jf : IsJet stripHalfWidth p (curvatureJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hBo _ hOps.curvature_local.1).isJet _ hδ p hps _ _
  have jd : IsJet stripHalfWidth p (vertexCoboundaryJet L k) := jetOp hSi hBo oD
  have jdb : IsJet stripHalfWidth p (edgeCoboundaryJet L k) := jetOp hBo hPl oDb
  have je : IsJet stripHalfWidth p (covDerivDefectJet L k p μPlus μMinus) :=
    hc.isJet_add hSi hBo jD (hc.isJet_smul hSi hBo _ jd)
  have jT : IsJet stripHalfWidth p (vertexCoboundaryAddDefect L k p μPlus μMinus) :=
    hc.isJet_add hSi hBo jd je
  have jS : IsJet stripHalfWidth p (edgeCoboundaryAddDefect L k p μPlus μMinus) :=
    hc.isJet_add hBo hPl jdb jE
  have jRt := hc.isJet_transpose hSi hSiK jR
  have jQt := hc.isJet_transpose hBo hBoK jQ
  have jDt := hc.isJet_transpose hSi hBo jD
  have jV : IsJet stripHalfWidth p (edgeCorrectionJet L k p μPlus μMinus) :=
    hc.isJet_add hBo hBo (hc.isJet_mul hBo hBoK hBo jQt jQ) (hc.isJet_smul hBo hBo _
      (hc.isJet_mul hBo hSi hBo (hc.isJet_mul hSi hSi hBo jD (hc.isJet_mul hSi hSiK hSi jRt jR)) jDt))
  have hb := hAss.1
  have fN : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0) (edgeResolventSqrt L k) κ :=
    fun κ hκ => hRootB.sqrt_summable κ (hstrip hκ)
  have jN : IsJet stripHalfWidth p (edgeSqrtJet L k) :=
    (hL.2.2 _ _ _ hBo hBo hBo stripHalfWidth p hδ hps).ofKernel_isJet _ hRootB.sqrt_periodic
      ⟨_, hopenI, hstrip, hRootB.sqrt_summable, fun c' c => hRootB.sqrt_holomorphicOn.2.2 (c', c)⟩
  have jM : IsJet stripHalfWidth p (edgeInvSqrtJet L k) :=
    (hL.2.2 _ _ _ hBo hBo hBo stripHalfWidth p hδ hps).ofKernel_isJet _ hRootB.invSqrt_periodic
      ⟨_, hopenI, hstrip, hRootB.invSqrt_summable,
        fun c' c => hRootB.invSqrt_holomorphicOn.2.2 (c', c)⟩
  have hMN : EqAsJet stripHalfWidth p (mul p (edgeInvSqrtJet L k) (edgeSqrtJet L k))
      (one (colourEdges L k 0)) := by
    refine ⟨fun κ hκ => (hRootB.invSqrt_inverse κ (hstrip hκ)).1, fun κ _ => ?_, fun κ _ => ?_,
      fun κ _ => ?_⟩ <;> simp [mul, edgeInvSqrtJet, edgeSqrtJet, ofKernel, one]
  have hsq : EqAsJet stripHalfWidth p (mul p (edgeSqrtJet L k) (edgeSqrtJet L k))
      (ofKernel (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k)) := by
    refine ⟨fun κ hκ => (hRootB.resolvent_eq_sq κ (hstrip hκ)).2.symm, fun κ _ => ?_, fun κ _ => ?_,
      fun κ _ => ?_⟩ <;> simp [mul, edgeSqrtJet, ofKernel]
  have hNt : EqAsJet stripHalfWidth p (transposeAt p (edgeSqrtJet L k)) (edgeSqrtJet L k) := by
    have own := (hProp L hLb k hk).2.2.2.1.transpose_eq (-(1 / 2)) (by simp [resolventExponents])
    refine ⟨fun κ hκ => ?_, fun κ _ => quotHomTranspose_zero hNorm hBo hBo,
      fun κ _ => quotHomTranspose_zero hNorm hBo hBo,
      fun κ _ => quotHomTranspose_zero hNorm hBo hBo⟩
    show quotHomTranspose (symbolHom _ _ (edgeResolventSqrt L k) (-κ)) =
      symbolHom _ _ (edgeResolventSqrt L k) κ
    have hneg := (hArgs.1 stripHalfWidth p hδ hps).2.2.comp00 κ hκ
    rw [quotHomTranspose_symbolHom_neg hSym hBo hBo hRootB.sqrt_periodic (fN _ hneg)]
    exact congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ) own
  have hcomp := ((hNorm _ _ hBo hBo).2.2.2.2.2.2.1 _ hBo).2
  have hN : jetNorm stripHalfWidth p (edgeSqrtJet L k) ≤ ENNReal.ofReal C₀ :=
    hc.jetNorm_le_of_zeroPart hBo hBo (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hb.edge_sqrt.2
  have hP : jetNorm stripHalfWidth p
      (ofKernel (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k)) ≤
        ENNReal.ofReal (C₀ ^ 2) := by
    refine hc.jetNorm_le_of_zeroPart hBo hBo (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      fun κ hκ => ?_
    show quotHomNorm (symbolHom _ _ (edgeResolvent L k) κ) ≤ _
    rw [(hRootB.resolvent_eq_sq κ (hstrip hκ)).2, sq, ENNReal.ofReal_mul hC0]
    exact (hcomp _ _).trans (mul_le_mul' (hb.edge_sqrt.2 κ hκ) (hb.edge_sqrt.2 κ hκ))
  have hbound := hCb k hk μPlus μMinus p hp
  have hQN : jetNorm stripHalfWidth p (mul p (edgeSmoothingJet L k p μPlus μMinus) (edgeSqrtJet L k)) ≤
      ENNReal.ofReal (Cb * C₀ + (C₀ + C₀ * Cb) * Cb) :=
    (hc.jetNorm_mul_le_ofReal hBoK hBo hBo hCb0 jQ jN hbound.edgeSmoothing hN).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hu hCb0]))
  have hdbN : jetNorm stripHalfWidth p (mul p (edgeCoboundaryJet L k) (edgeSqrtJet L k)) ≤
      ENNReal.ofReal C₀ := by
    refine hc.jetNorm_le_of_zeroPart hBo hPl (fun κ => ?_) (fun κ => ?_) (fun κ => ?_) fun κ hκ => ?_
    · simp [mul, edgeSqrtJet, edgeCoboundaryJet, ofKernel]
    · simp [mul, edgeSqrtJet, edgeCoboundaryJet, ofKernel]
    · simp [mul, edgeSqrtJet, edgeCoboundaryJet, ofKernel]
    have h := hb.diff_edge_sqrt.2.2 κ hκ
    have pr := symbolHom_compKernel hSym hBo hPl hBo (T := FreeStrip.edgeDiff L k) oDb.1
      hRootB.sqrt_periodic (fDb κ) (fN κ hκ)
    rw [pr.2.2.2] at h
    exact h
  have hNd : jetNorm stripHalfWidth p (mul p (edgeSqrtJet L k) (vertexCoboundaryJet L k)) ≤
      ENNReal.ofReal C₀ := by
    refine hc.jetNorm_le_of_zeroPart hSi hBo (fun κ => ?_) (fun κ => ?_) (fun κ => ?_) fun κ hκ => ?_
    · simp [mul, edgeSqrtJet, vertexCoboundaryJet, ofKernel]
    · simp [mul, edgeSqrtJet, vertexCoboundaryJet, ofKernel]
    · simp [mul, edgeSqrtJet, vertexCoboundaryJet, ofKernel]
    have h := hb.edge_sqrt_diff.2.2 κ hκ
    have pr := symbolHom_compKernel hSym hBo hBo hSi (S := FreeStrip.vertexDiff L k)
      hRootB.sqrt_periodic oD.1 (fN κ hκ) (fD κ)
    rw [pr.2.2.2] at h
    exact h
  have hSN : jetNorm stripHalfWidth p
      (mul p (edgeCoboundaryAddDefect L k p μPlus μMinus) (edgeSqrtJet L k)) ≤
        ENNReal.ofReal (C₀ + Cb * C₀) := by
    rw [show edgeCoboundaryAddDefect L k p μPlus μMinus =
        add (edgeCoboundaryJet L k) (holonomyDefectJet L k p μPlus μMinus) from rfl,
      jmul_add_left, ENNReal.ofReal_add hC0 (by positivity)]
    exact (hc.jetNorm_add_le hBo hPl _ _).trans (add_le_add hdbN
      (hc.jetNorm_mul_le_ofReal hPl hBo hBo hCb0 jE jN hbound.holonomyDefect hN))
  have hNT : jetNorm stripHalfWidth p
      (mul p (edgeSqrtJet L k) (vertexCoboundaryAddDefect L k p μPlus μMinus)) ≤
        ENNReal.ofReal (C₀ + C₀ * Cb) := by
    rw [show vertexCoboundaryAddDefect L k p μPlus μMinus =
        add (vertexCoboundaryJet L k) (covDerivDefectJet L k p μPlus μMinus) from rfl,
      jmul_add_right, ENNReal.ofReal_add hC0 (by positivity)]
    exact (hc.jetNorm_add_le hSi hBo _ _).trans (add_le_add hNd
      (hc.jetNorm_mul_le_ofReal hBo hBo hSi hC0 jN je hN hbound.covDerivDefect))
  have hND : jetNorm stripHalfWidth p (mul p (edgeSqrtJet L k) (covDerivJet L k p μPlus μMinus)) ≤
      ENNReal.ofReal (C₀ + C₀ * Cb) := by
    rw [hc.jetNorm_congr hSi hBo (hc.isJet_mul hSi hBo hBo jN jD) (hc.isJet_mul hSi hBo hBo jN jT)
      (hc.mul_congr_right hSi hBo hBo jN jD jT parts.covDeriv)]
    exact hNT
  have hy : jetNorm stripHalfWidth p (vertexToEdgeJet L k p μPlus μMinus) ≤
      ENNReal.ofReal (Cb * C₀ + (C₀ + C₀ * Cb) * Cb) := by
    refine (hc.jetNorm_mul_le_ofReal hBo hSi hSiK hu (hc.isJet_mul hSi hBo hBo jN jD) jRt hND ?_).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hCb0 hC0]))
    rw [hc.jetNorm_transposeAt hSiK hSi jR]
    exact hbound.vertexSmoothing
  have jy : IsJet stripHalfWidth p (vertexToEdgeJet L k p μPlus μMinus) :=
    hc.isJet_mul hSiK hSi hBo (hc.isJet_mul hSi hBo hBo jN jD) jRt
  have hcorr := hc.conj_correction hQuot hBo hBoK hSi hSiK jN jQ jD jR hNt
  have hAs := hc.jetNorm_conj_operator_le hBo hPl hSi hs hCb0 hC0 hCb0 hu jK jN jf jS jz jT
    hNt parts.edge_operator hSN hbound.halfFaceTrace hN hbound.curvature hNT
  have cRt : ∀ κ, (transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ :=
    fun κ => by
    show quotHomTranspose ((vertexSmoothingJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [vertexSmoothingJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hSi hSiK oR.1 (fR _)
  have cQt : ∀ κ, (transposeAt p (edgeSmoothingJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ :=
    fun κ => by
    show quotHomTranspose ((edgeSmoothingJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [edgeSmoothingJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hBo hBoK oQ.1 (fQ _)
  have cDt : ∀ κ, (transposeAt p (covDerivJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Dt κ :=
    fun κ => by
    show quotHomTranspose ((covDerivJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [covDerivJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hSi hBo oDf.1 (fDf _)
  have cXi : ∀ κ, ((edgeOperatorJet L k p μPlus μMinus).add
      (edgeCorrectionJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ :=
    fun κ => by
    have pQ := symbolHom_compKernel hSym hBoK hBo hBo oQt.1 oQ.1 (fQt κ) (fQ κ)
    have pDR := symbolHom_compKernel hSym hSi hBo hSiK oDf.1 oRt.1 (fDf κ) (fRt κ)
    have pRD := symbolHom_compKernel hSym hSi hSiK hBo oR.1 oDt.1 (fR κ) (fDt κ)
    have pA := symbolHom_compKernel hSym hSiK hBo hBo pDR.2.1 pRD.2.1 pDR.2.2.1 pRD.2.2.1
    have c₁ := ((hSym.2.1 _ _ hBo hBo).2.1 _ κ oK.1 (fK κ)).linComb _ pA.2.1 pA.2.2.1 1 (-1)
    have c₂ := ((hSym.2.1 _ _ hBo hBo).2.1 _ κ c₁.1 c₁.2.1).linComb _ pQ.2.1 pQ.2.2.1 1 1
    have c₃ := c₂.2.2
    rw [c₁.2.2, pA.2.2.2, pDR.2.2.2, pRD.2.2.2, pQ.2.2.2] at c₃
    rw [trivial_Xi_eq]
    refine Eq.trans ?_ c₃.symm
    show (edgeOperatorJet L k p μPlus μMinus).f00 κ +
        (((transposeAt p (edgeSmoothingJet L k p μPlus μMinus)).f00 κ).comp
            ((edgeSmoothingJet L k p μPlus μMinus).f00 κ) +
          (-1 : ℂ) • (((covDerivJet L k p μPlus μMinus).f00 κ).comp
              (((transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ).comp
                ((vertexSmoothingJet L k p μPlus μMinus).f00 κ))).comp
            ((transposeAt p (covDerivJet L k p μPlus μMinus)).f00 κ)) = _
    rw [cQt, cRt, cDt, edgeOperatorJet_f00, edgeSmoothingJet_f00, vertexSmoothingJet_f00,
      covDerivJet_f00]
    simp only [one_smul, LinearMap.comp_assoc]
    abel
  have hM := (hMid' L hLb k hk p hp μPlus μMinus).1
  have fam : ∀ t ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p
        (unitShiftedPath (edgeOperatorJet L k p μPlus μMinus)
          (edgeCorrectionJet L k p μPlus μMinus) t) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p (edgeSqrtJet L k) (unitShiftedPath (edgeOperatorJet L k p μPlus μMinus)
          (edgeCorrectionJet L k p μPlus μMinus) t)).f00 κ : Module.End ℂ _) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p (edgeSqrtJet L k)
          (unitShiftedPath (edgeOperatorJet L k p μPlus μMinus)
            (edgeCorrectionJet L k p μPlus μMinus) t)).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    intro t ht
    refine ⟨(hM t ht).1.1, fun κ hκ => ?_⟩
    have si := symbolHom_interpPlusOne hSym hNorm hId hBo oXi.1 oK.1 (fXi κ) (fK κ) t
    have h := isUnit_triple_symbol hSym hBo hκ hRootB.sqrt_periodic si.1 (fN κ hκ) si.2.1
      (hAss.2 t ht t ht).edge_interp
    rw [si.2.2] at h
    have e : (unitShiftedPath (edgeOperatorJet L k p μPlus μMinus)
        (edgeCorrectionJet L k p μPlus μMinus) t).f00 κ =
        (t : ℂ) • symbolHom _ _ (trivialRescaledOperators L k).Xi κ +
          ((1 - t : ℝ) : ℂ) • symbolHom _ _ (trivialRescaledOperators L k).K κ +
            scalarQuotHom (colourEdges L k 0) 1 := by
      rw [unitShiftedPath_f00, cXi κ, edgeOperatorJet_f00]
    rw [conjugateBy_f00, e]
    exact h
  have shf : ∀ τ ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p
        (addScalarJet ((edgeOperatorJet L k p μPlus μMinus).add
          (edgeCorrectionJet L k p μPlus μMinus)) τ) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p (edgeSqrtJet L k)
          (addScalarJet ((edgeOperatorJet L k p μPlus μMinus).add
            (edgeCorrectionJet L k p μPlus μMinus)) τ)).f00 κ : Module.End ℂ _) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p (edgeSqrtJet L k)
          (addScalarJet ((edgeOperatorJet L k p μPlus μMinus).add
            (edgeCorrectionJet L k p μPlus μMinus)) τ)).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    intro τ hτ
    refine ⟨(hM τ hτ).2.2.1.1, fun κ hκ => ?_⟩
    have sum := (hAss.2 τ hτ τ hτ).edge_inverse
    have h := isUnit_triple_symbol hSym hBo hκ hRootB.sqrt_periodic sum.periodic (fN κ hκ)
      (sum.symbol κ hκ).2.1 (hAss.2 τ hτ τ hτ).edge_add
    rw [(sum.symbol κ hκ).2.2] at h
    have e : (addScalarJet ((edgeOperatorJet L k p μPlus μMinus).add
        (edgeCorrectionJet L k p μPlus μMinus)) τ).f00 κ =
        symbolAddScalar (colourEdges L k 0) τ (trivialRescaledOperators L k).Xi κ := by
      show ((edgeOperatorJet L k p μPlus μMinus).add
        (edgeCorrectionJet L k p μPlus μMinus)).f00 κ + (τ : ℂ) • LinearMap.id = _
      rw [cXi κ]
      rfl
    rw [conjugateBy_f00, e]
    exact h
  exact rootInterpolationData_of_bounds hc hBo hBoK hSiK hα hC0 ha hC0 jK jV jN jM jQ jy hMN hNt
    hsq hP hQN hy hcorr hAs hN fam shf
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets
end
