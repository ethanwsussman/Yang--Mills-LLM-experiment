import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertibleProof
import YangMills.Construction.Towers.TheSiteJetsBetweenTheRootsOfTheFreePropagator
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.VertexRootJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.Tower.FreeStrip
open YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
open YangMills.Construction.PeriodicOperators.JetNormsAffine (affinePath)
section Maps
variable {I I' I'' : PeriodicData}
theorem quotHomTranspose_symbolHom_neg (q2 : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {κ : Fin 4 → ℂ} (fT : SymbolSummableAt I I' T (-κ)) :
    quotHomTranspose (symbolHom I I' T (-κ)) = symbolHom I' I (kernelTranspose I I' T) κ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomTranspose_symbolHom_neg <;> assumption
theorem quotHomNorm_zero (pa3 : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') : quotHomNorm (0 : QuotHom I I') = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomNorm_zero <;> assumption
theorem quotHomTranspose_zero (pa3 : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') : quotHomTranspose (0 : QuotHom I I') = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomTranspose_zero <;> assumption
theorem symbolHom_compKernel (q2 : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  ((q2.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS
theorem symbolHom_interpPlusOne (q2 : StripSymbols.Claim) (pa3 : HomNorm.Claim)
    (hid : IdKernelFacts.Claim) (hI : IsPeriodic I)
    {X K : I.Carrier → I.Carrier → ℂ} (hX : IsPeriodicKernel I I X) (hK : IsPeriodicKernel I I K)
    {κ : Fin 4 → ℂ} (fX : SymbolSummableAt I I X κ) (fK : SymbolSummableAt I I K κ) (t : ℝ) :
    IsPeriodicKernel I I (interpPlusOne I t X K) ∧
      SymbolSummableAt I I (interpPlusOne I t X K) κ ∧
      symbolHom I I (interpPlusOne I t X K) κ =
        (t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
          scalarQuotHom I 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.symbolHom_interpPlusOne <;> assumption
theorem isUnit_symbolHom_triple (q2 : StripSymbols.Claim) (hI : IsPeriodic I)
    {N B : I.Carrier → I.Carrier → ℂ} {D : Set (Fin 4 → ℂ)} {κ : Fin 4 → ℂ} {C : ℝ} (hκ : κ ∈ D)
    (hN : IsPeriodicKernel I I N) (hB : IsPeriodicKernel I I B)
    (fN : SymbolSummableAt I I N κ) (fB : SymbolSummableAt I I B κ)
    (tri : TripleCompSymbolInvertibleOn I I N B N D C) :
    IsUnit (((symbolHom I I N κ).comp (symbolHom I I B κ)).comp (symbolHom I I N κ) :
        Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse
        (((symbolHom I I N κ).comp (symbolHom I I B κ)).comp (symbolHom I I N κ))) ≤
          ENNReal.ofReal C := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.isUnit_triple_symbol <;> assumption
end Maps
section Quadruples
variable {I₁ I₂ I₃ : PeriodicData}
theorem jetMul_add_left (p : Fin 4 → ℂ) (T T' : JetQuad I₂ I₃) (S : JetQuad I₁ I₂) :
    mul p (add T T') S = add (mul p T S) (mul p T' S) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.jmul_add_left <;> assumption
theorem conjugateBy_expand (p : Fin 4 → ℂ) (N A W : JetQuad I₁ I₁) (u v : ℂ) :
    conjugateBy p N (add (add A (smul u (one I₁))) (smul v W)) =
      add (add (conjugateBy p N A) (smul u (mul p N N))) (smul v (conjugateBy p N W)) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.conjugateBy_add_smul_one <;> assumption
theorem conjugateBy_f00 (p : Fin 4 → ℂ) (N T : JetQuad I₁ I₁) (κ : Fin 4 → ℂ) :
    (conjugateBy p N T).f00 κ = ((N.f00 κ).comp (T.f00 κ)).comp (N.f00 κ) := rfl
theorem addScalarJet_eq (A W : JetQuad I₁ I₁) (τ : ℝ) :
    addScalarJet (A.add W) τ = add (add A (smul (τ : ℂ) (one I₁))) (smul 1 W) := by
  apply JetQuad.ext <;> funext κ <;> simp only [addScalarJet, add, smul, Pi.add_apply, Pi.smul_apply, one_smul] <;> abel
theorem unitShiftedPath_eq (A W : JetQuad I₁ I₁) (t : ℝ) :
    unitShiftedPath A W t = add (add A (smul ((1 : ℝ) : ℂ) (one I₁))) (smul (t : ℂ) W) := rfl
theorem unitShiftedPath_f00 (A W : JetQuad I₁ I₁) (t : ℝ) (κ : Fin 4 → ℂ) :
    (unitShiftedPath A W t).f00 κ =
      (t : ℂ) • (A.add W).f00 κ + ((1 - t : ℝ) : ℂ) • A.f00 κ + scalarQuotHom I₁ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.unitShiftedPath_f00 <;> assumption
theorem zeroJet_eq_smul (T : JetQuad I₁ I₂) : zeroJet I₁ I₂ = smul 0 T := by
  apply JetQuad.ext <;> funext κ <;> simp [zeroJet, smul]
theorem eq_add_vanishing_term (p : Fin 4 → ℂ) (X : JetQuad I₁ I₁) :
    X = X.add (smul (-1) (mul p (zeroJet I₂ I₁) (transposeAt p (zeroJet I₂ I₁)))) := by
  apply JetQuad.ext <;> funext κ <;> simp [add, smul, mul, zeroJet]
theorem eqAsJet_refl (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I₁ I₂) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_symm {δ : ℝ} {p : Fin 4 → ℂ} {T S : JetQuad I₁ I₂} (h : EqAsJet δ p T S) :
    EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem eqAsJet_trans {δ : ℝ} {p : Fin 4 → ℂ} {T S R : JetQuad I₁ I₂} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
end Quadruples
structure JetToolkit (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  width_pos : 0 < δ
  mem_strip : p ∈ imStrip δ
  jetClosure : JetDomains.OpFunJetTheory
  jetCalculus : JetCalculus.Claim
  equalJets : JetArgumentsAndEqualJets
  homNorm : HomNorm.Claim
namespace JetToolkit
variable {δ : ℝ} {p : Fin 4 → ℂ} {I₁ I₂ I₃ I₄ : PeriodicData}
theorem isJet_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₃} {S : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (mul p T S) :=
  (c.jetClosure.2.2 I₂ I₃ I₁ h₂ h₃ h₁ δ p c.width_pos c.mem_strip).mul_isJet T S jT jS
theorem isJet_transposeAt (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T : JetQuad I₁ I₂} (jT : IsJet δ p T) : IsJet δ p (transposeAt p T) :=
  (c.jetClosure.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.width_pos c.mem_strip).transpose_isJet T jT
theorem isJet_add (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T S : JetQuad I₁ I₂} (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (add T S) :=
  (c.jetClosure.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.width_pos c.mem_strip).add_isJet T S jT jS
theorem isJet_smul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (z : ℂ) {T : JetQuad I₁ I₂} (jT : IsJet δ p T) : IsJet δ p (smul z T) :=
  (c.jetClosure.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.width_pos c.mem_strip).smul_isJet z T jT
theorem isJet_one (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) : IsJet δ p (one I₁) :=
  (c.jetClosure.2.2 I₁ I₁ I₁ h₁ h₁ h₁ δ p c.width_pos c.mem_strip).one_isJet
theorem jetMul_assoc (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) (h₄ : IsPeriodic I₄) {T : JetQuad I₂ I₁}
    {S : JetQuad I₃ I₂} {R : JetQuad I₄ I₃} (jT : IsJet δ p T) (jS : IsJet δ p S)
    (jR : IsJet δ p R) : EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R)) :=
  ((c.jetCalculus δ p c.width_pos c.mem_strip).1 I₁ I₂ I₃ I₄ h₁ h₂ h₃ h₄ T S R jT jS jR).1
theorem jetNorm_mul_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₁} {S : JetQuad I₃ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) : jetNorm δ p (mul p T S) ≤ jetNorm δ p T * jetNorm δ p S :=
  ((c.jetCalculus δ p c.width_pos c.mem_strip).1 I₁ I₂ I₃ I₃ h₁ h₂ h₃ h₃ T S (one I₃) jT jS
    (c.isJet_one h₃)).2
theorem transposeAt_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₁} {S : JetQuad I₃ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) :
    EqAsJet δ p (transposeAt p (mul p T S)) (mul p (transposeAt p S) (transposeAt p T)) :=
  ((c.jetCalculus δ p c.width_pos c.mem_strip).2.1 I₁ I₂ I₃ h₁ h₂ h₃ T S jT jS).1
theorem jetNorm_transposeAt (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {T : JetQuad I₂ I₁} (jT : IsJet δ p T) :
    jetNorm δ p (transposeAt p T) = jetNorm δ p T :=
  ((c.jetCalculus δ p c.width_pos c.mem_strip).2.1 I₁ I₂ I₂ h₁ h₂ h₂ T (one I₂) jT
    (c.isJet_one h₂)).2
theorem mul_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T T' : JetQuad I₂ I₃} {S S' : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jT' : IsJet δ p T') (jS : IsJet δ p S) (jS' : IsJet δ p S')
    (e : EqAsJet δ p T T') (e' : EqAsJet δ p S S') : EqAsJet δ p (mul p T S) (mul p T' S') :=
  (c.equalJets.2.1 δ p I₂ I₃ h₂ h₃ T T' jT jT' e).2.2.2.2 I₁ h₁ S S' jS jS' e'
theorem jetNorm_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T T' : JetQuad I₁ I₂} (jT : IsJet δ p T) (jT' : IsJet δ p T') (e : EqAsJet δ p T T') :
    jetNorm δ p T = jetNorm δ p T' :=
  (c.equalJets.2.1 δ p I₁ I₂ h₁ h₂ T T' jT jT' e).1
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
theorem jetNorm_le_of_f00 (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
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
theorem conjugateBy_gram (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {N : JetQuad I₁ I₁} {S : JetQuad I₁ I₂} (jN : IsJet δ p N)
    (jS : IsJet δ p S) (hN : EqAsJet δ p (transposeAt p N) N) :
    EqAsJet δ p (conjugateBy p N (mul p (transposeAt p S) S))
      (mul p (transposeAt p (mul p S N)) (mul p S N)) := by
  have jSt := c.isJet_transposeAt h₁ h₂ jS
  have jNt := c.isJet_transposeAt h₁ h₁ jN
  have jSN := c.isJet_mul h₁ h₁ h₂ jS jN
  have jNSt := c.isJet_mul h₂ h₁ h₁ jN jSt
  have jStS := c.isJet_mul h₁ h₂ h₁ jSt jS
  have e₁ : EqAsJet δ p (transposeAt p (mul p S N)) (mul p N (transposeAt p S)) :=
    eqAsJet_trans (c.transposeAt_mul h₂ h₁ h₁ jS jN)
      (c.mul_congr h₂ h₁ h₁ jNt jN (c.isJet_transposeAt h₁ h₂ jS) jSt hN (eqAsJet_refl _ _ _))
  have e₂ : EqAsJet δ p (mul p (transposeAt p (mul p S N)) (mul p S N))
      (mul p (mul p N (transposeAt p S)) (mul p S N)) :=
    c.mul_congr h₁ h₂ h₁ (c.isJet_transposeAt h₁ h₂ jSN) jNSt jSN jSN e₁ (eqAsJet_refl _ _ _)
  have e₃ : EqAsJet δ p (mul p (mul p (mul p N (transposeAt p S)) S) N)
      (mul p (mul p N (transposeAt p S)) (mul p S N)) :=
    c.jetMul_assoc h₁ h₂ h₁ h₁ jNSt jS jN
  have e₄ : EqAsJet δ p (mul p (mul p N (transposeAt p S)) S)
      (mul p N (mul p (transposeAt p S) S)) :=
    c.jetMul_assoc h₁ h₁ h₂ h₁ jN jSt jS
  have e₅ : EqAsJet δ p (mul p (mul p (mul p N (transposeAt p S)) S) N)
      (mul p (mul p N (mul p (transposeAt p S) S)) N) :=
    c.mul_congr h₁ h₁ h₁ (c.isJet_mul h₁ h₂ h₁ jNSt jS) (c.isJet_mul h₁ h₁ h₁ jN jStS) jN jN e₄
      (eqAsJet_refl _ _ _)
  exact eqAsJet_trans (eqAsJet_symm e₅) (eqAsJet_trans e₃ (eqAsJet_symm e₂))
theorem jetNorm_gram_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {S : JetQuad I₁ I₂} {x : ℝ} (hx : 0 ≤ x) (jS : IsJet δ p S)
    (hS : jetNorm δ p S ≤ ENNReal.ofReal x) :
    jetNorm δ p (mul p (transposeAt p S) S) ≤ ENNReal.ofReal (x ^ 2) := by
  rw [sq]
  refine c.jetNorm_mul_le_ofReal h₁ h₂ h₁ hx (c.isJet_transposeAt h₁ h₂ jS) jS ?_ hS
  rw [c.jetNorm_transposeAt h₂ h₁ jS]
  exact hS
theorem jetNorm_conjugateBy_le (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) (h₃ : IsPeriodic I₃) {A N : JetQuad I₁ I₁}
    {D : JetQuad I₁ I₂} {R : JetQuad I₁ I₃} {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (jA : IsJet δ p A) (jN : IsJet δ p N) (jD : IsJet δ p D) (jR : IsJet δ p R)
    (hNt : EqAsJet δ p (transposeAt p N) N) (hA : EqAsJet δ p A (mul p (transposeAt p D) D))
    (hN : jetNorm δ p N ≤ ENNReal.ofReal x) (hD : jetNorm δ p (mul p D N) ≤ ENNReal.ofReal y)
    (hR : jetNorm δ p (mul p R N) ≤ ENNReal.ofReal z) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    jetNorm δ p (conjugateBy p N (add (add A (smul u (one I₁)))
      (smul v (mul p (transposeAt p R) R)))) ≤
      ENNReal.ofReal (y ^ 2 + x ^ 2 + z ^ 2) := by
  have jDt := c.isJet_transposeAt h₁ h₂ jD
  have jDD := c.isJet_mul h₁ h₂ h₁ jDt jD
  have jRR := c.isJet_mul h₁ h₃ h₁ (c.isJet_transposeAt h₁ h₃ jR) jR
  have jDN := c.isJet_mul h₁ h₁ h₂ jD jN
  have jRN := c.isJet_mul h₁ h₁ h₃ jR jN
  have conj : ∀ {T : JetQuad I₁ I₁}, IsJet δ p T → IsJet δ p (conjugateBy p N T) := fun jT =>
    c.isJet_mul h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jT) jN
  have hAs : jetNorm δ p (conjugateBy p N A) ≤ ENNReal.ofReal (y ^ 2) := by
    have e₁ : EqAsJet δ p (conjugateBy p N A) (conjugateBy p N (mul p (transposeAt p D) D)) :=
      c.mul_congr h₁ h₁ h₁ (c.isJet_mul h₁ h₁ h₁ jN jA) (c.isJet_mul h₁ h₁ h₁ jN jDD) jN jN
        (c.mul_congr h₁ h₁ h₁ jN jN jA jDD (eqAsJet_refl _ _ _) hA) (eqAsJet_refl _ _ _)
    have e₂ := eqAsJet_trans e₁ (c.conjugateBy_gram h₁ h₂ jN jD hNt)
    rw [c.jetNorm_congr h₁ h₁ (conj jA) (c.isJet_mul h₁ h₂ h₁ (c.isJet_transposeAt h₁ h₂ jDN) jDN) e₂]
    exact c.jetNorm_gram_le h₁ h₂ hy jDN hD
  have hRs : jetNorm δ p (conjugateBy p N (mul p (transposeAt p R) R)) ≤
      ENNReal.ofReal (z ^ 2) := by
    rw [c.jetNorm_congr h₁ h₁ (conj jRR) (c.isJet_mul h₁ h₃ h₁ (c.isJet_transposeAt h₁ h₃ jRN) jRN)
      (c.conjugateBy_gram h₁ h₃ jN jR hNt)]
    exact c.jetNorm_gram_le h₁ h₃ hz jRN hR
  have hNN : jetNorm δ p (mul p N N) ≤ ENNReal.ofReal (x ^ 2) := by
    rw [sq]
    exact c.jetNorm_mul_le_ofReal h₁ h₁ h₁ hx jN jN hN hN
  rw [conjugateBy_expand, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  exact (c.jetNorm_add_le h₁ h₁ _ _).trans (add_le_add ((c.jetNorm_add_le h₁ h₁ _ _).trans
    (add_le_add hAs ((c.jetNorm_smul_le h₁ h₁ hu _).trans hNN)))
    ((c.jetNorm_smul_le h₁ h₁ hv _).trans hRs))
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
  have h := (c.jetCalculus stripHalfWidth p c.width_pos c.mem_strip).2.2.2.2.1 I hI _ hS
  have h₀ : jetNorm stripHalfWidth p (zeroPartInv (conjugateBy p N T)) ≤ ENNReal.ofReal C := by
    rw [h.2.2.2.2]
    exact iSup₂_le fun κ hκ => (hU κ hκ).2
  refine h.2.2.2.1.trans ?_
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_mul hC, ENNReal.ofReal_one]
  gcongr
theorem rootInterpolationData_of_bounds (c : JetToolkit stripHalfWidth p) (hI : IsPeriodic I)
    (hX : IsPeriodic X) (hJ : IsPeriodic J) {A N M : JetQuad I I}
    {D : JetQuad I X} {R : JetQuad I J} {P : I.Carrier → I.Carrier → ℂ} {x y a g C : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hC : 0 ≤ C) (jA : IsJet stripHalfWidth p A)
    (jN : IsJet stripHalfWidth p N) (jM : IsJet stripHalfWidth p M) (jD : IsJet stripHalfWidth p D)
    (jR : IsJet stripHalfWidth p R) (hMN : EqAsJet stripHalfWidth p (mul p M N) (one I))
    (hNt : EqAsJet stripHalfWidth p (transposeAt p N) N)
    (hsq : EqAsJet stripHalfWidth p (mul p N N) (ofKernel I I P))
    (hP : jetNorm stripHalfWidth p (ofKernel I I P) ≤ ENNReal.ofReal g)
    (hA : EqAsJet stripHalfWidth p A (mul p (transposeAt p D) D))
    (hN : jetNorm stripHalfWidth p N ≤ ENNReal.ofReal x)
    (hD : jetNorm stripHalfWidth p (mul p D N) ≤ ENNReal.ofReal y)
    (hR : jetNorm stripHalfWidth p (mul p R N) ≤ ENNReal.ofReal a)
    (fam : ∀ t ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p (unitShiftedPath A (mul p (transposeAt p R) R) t) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p N (unitShiftedPath A (mul p (transposeAt p R) R) t)).f00 κ :
          Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse
          ((conjugateBy p N (unitShiftedPath A (mul p (transposeAt p R) R) t)).f00 κ)) ≤
            ENNReal.ofReal C)
    (shf : ∀ τ ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p (addScalarJet (A.add (mul p (transposeAt p R) R)) τ) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p N (addScalarJet (A.add (mul p (transposeAt p R) R)) τ)).f00 κ :
          Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse
          ((conjugateBy p N (addScalarJet (A.add (mul p (transposeAt p R) R)) τ)).f00 κ)) ≤
            ENNReal.ofReal C) :
    RootInterpolationData p A (mul p (transposeAt p R) R) N M P R (zeroJet J I) a
      (C * (1 + C * (y ^ 2 + x ^ 2 + a ^ 2)) ^ 2) g := by
  have jRt := c.isJet_transposeAt hI hJ jR
  have jW := c.isJet_mul hI hJ hI jRt jR
  have jy : IsJet stripHalfWidth p (zeroJet J I) := by
    rw [zeroJet_eq_smul (transposeAt p R)]
    exact c.isJet_smul hJ hI _ jRt
  have hB : 0 ≤ y ^ 2 + x ^ 2 + a ^ 2 := by positivity
  have abs_le_one : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  refine
    { isJet_A := jA
      isJet_W := jW
      isJet_N := jN
      isJet_M := jM
      isJet_Q := jR
      isJet_y := jy
      left_inv := hMN
      transpose_self := hNt
      mul_self := hsq
      kernel_norm_le := hP
      x_norm_le := hR
      y_norm_le := c.jetNorm_le_of_f00 hJ hI (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        fun κ _ => ?_
      conj_decomp := ?_
      path := fun t ht =>
        invertibleWithConjugate_of_bounds c hI hB hC jN (fam t ht).1 (fam t ht).2 ?_
      shifted := fun τ hτ =>
        invertibleWithConjugate_of_bounds c hI hB hC jN (shf τ hτ).1 (shf τ hτ).2 ?_ }
  · show quotHomNorm (0 : QuotHom J I) ≤ _
    rw [quotHomNorm_zero c.homNorm hJ hI]
    exact zero_le
  · rw [← eq_add_vanishing_term p _]
    exact c.conjugateBy_gram hI hJ jN jR hNt
  · rw [unitShiftedPath_eq]
    exact c.jetNorm_conjugateBy_le hI hX hJ hx hy ha jA jN jD jR hNt hA hN hD hR
      (by simp) (abs_le_one t ht)
  · rw [addScalarJet_eq]
    exact c.jetNorm_conjugateBy_le hI hX hJ hx hy ha jA jN jD jR hNt hA hN hD hR
      (abs_le_one τ hτ) (by simp)
end Data
section Tower
variable {L k : ℕ}
theorem vertexOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible.vertexOperatorJet_f00 <;> assumption
theorem covDerivJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (covDerivJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.covDerivJet_f00 <;> assumption
theorem vertexSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R := by apply _root_.YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBoundProof.vertexSmoothingJet_f00 <;> assumption
theorem trivial_Y_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Y =
      StripSymbols.linCombKernel 1 1 (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible.Y_eq_linComb <;> assumption
theorem covDerivJet_eq_add (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    covDerivJet L k p μPlus μMinus =
      add (covDerivDefectJet L k p μPlus μMinus)
        (ofKernel (colourVertices L k 0) (colourEdges L k 0)
          (scaledVertexCoboundaryKernel L k 0)) := by
  apply JetQuad.ext <;> funext κ <;> simp only [covDerivDefectJet, add, smul, Pi.add_apply, Pi.smul_apply] <;> module
end Tower
theorem vertexJetsInterpolate_holds
    (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hRoots : ResolventRootsOnStrip.ResolventRootsHold)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hTr : RescaledConditions.Holds)
    (hIter : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (q2 : StripSymbols.Claim) (pa3 : HomNorm.Claim)
    (hid : IdKernelFacts.Claim)
    (hL : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hBasic : BoundedBasicJets.BasicJetsBounded)
    (hMid : MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hProp : FreeResolventRoots) : VertexJetsInterpolate := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδI, hC₀, hAdm⟩ := hNum
  have eδ : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  obtain ⟨Cm, hMid'⟩ := hMid
  intro L hLb
  obtain ⟨⟨Cb, hCb0, hCb⟩, -⟩ := hBasic L hLb
  have hC0 : 0 ≤ C₀ := by linarith
  have ha : 0 ≤ Cb * C₀ := by positivity
  have hy : 0 ≤ Cb * C₀ + C₀ := by positivity
  refine ⟨Cb * C₀, C₀ * (1 + C₀ * ((Cb * C₀ + C₀) ^ 2 + C₀ ^ 2 + (Cb * C₀) ^ 2)) ^ 2, C₀ ^ 2,
    ha, by positivity, by positivity, ?_⟩
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
  have hc : JetToolkit stripHalfWidth p := ⟨hδ, hps, hL, hCalc, hArgs, pa3⟩
  have hOps := (hOp.1 L hLb k hk).1
  obtain ⟨hSi, hBo, -, hSiK, -⟩ := hOps.periodic
  obtain ⟨hmaps, hops⟩ := hFree.2 L hLb k hk
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hTr L hLb k hk).2
  have hint := q2.1 (1 / 8) (by norm_num)
  have hopenI : IsOpen (StripSymbols.openStripInterior (1 / 8)) := by
    rw [hint.1]
    exact hint.2.1
  have hstrip : imStrip (2 * stripHalfWidth) ⊆ StripSymbols.openStripInterior (1 / 8) := by
    rw [hint.1]
    exact hint.2.2.2 (2 * stripHalfWidth) (by linarith) (by linarith)
  have hRootS := (hRoots L hLb k hk).2
  have hDeq : (trivialRescaledOperators L k).D = scaledVertexCoboundaryKernel L k 0 := hOne.D_eq
  have oD : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourEdges L k 0)
      (scaledVertexCoboundaryKernel L k 0) :=
    (hmaps.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have oR : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k k)
      (trivialRescaledOperators L k).R := hmaps.vertexAverage.finite_range
  have oRt : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k k) (colourVertices L k 0)
      (trivialRescaledOperators L k).Rt := hops.vertexAverage_transpose
  have oDelta : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0)
      (colourVertices L k 0) (trivialRescaledOperators L k).Delta := hops.Delta
  have oY : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Y := hops.Y
  have formed : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        ∀ κ, SymbolSummableAt I I' T κ := fun hI hI' _ h κ =>
    (q2.2.1 _ _ hI hI').1.finiteRange _ h.1 h.2.1 κ (mem_univ κ)
  have fD := formed hSi hBo oD
  have fR := formed hSi hSiK oR
  have fRt := formed hSiK hSi oRt
  have fDelta := formed hSi hSi oDelta
  have fY := formed hSi hSi oY
  obtain ⟨ρ, cρ, hρ⟩ : ∃ ρ c,
      YangMills.Construction.Tower.IteratedSmallFieldMeans.AdmissibleConstants L ρ c :=
    ⟨_, _, hIter.1 L hLb⟩
  have lR : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R := by
    obtain ⟨r, R', hm, -⟩ := hOps.R_local ρ cρ hρ
    exact ⟨r, R', hm⟩
  have lD := hOps.D_local.1
  have lDt := (hL.1 _ _ _ _ hBo hSi hBo hSi).2.2 _ lD
  have jDelta : IsJet stripHalfWidth p (vertexOperatorJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hSi _ hOps.Delta_local.1).isJet _ hδ p hps _ _
  have jD : IsJet stripHalfWidth p (covDerivJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hBo _ lD).isJet _ hδ p hps _ _
  have jR : IsJet stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hSiK _ lR).isJet _ hδ p hps _ _
  have jDt' := (hL.2.1 _ _ _ hBo hBo hSi _ lDt).isJet _ hδ p hps
    (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)
  have jDt := hc.isJet_transposeAt hSi hBo jD
  have hA : EqAsJet stripHalfWidth p (vertexOperatorJet L k p μPlus μMinus)
      (mul p (transposeAt p (covDerivJet L k p μPlus μMinus))
        (covDerivJet L k p μPlus μMinus)) := by
    have e₁ := ((hCalc stripHalfWidth p hδ hps).2.2.1 _ _ _ _ hBo hSi hBo hSi
      (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).2.1 _ _ lDt lD
    have e₂ := ((hCalc stripHalfWidth p hδ hps).2.2.1 _ _ _ _ hBo hBo hSi hSi
      (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).2.2 _ lD
    exact eqAsJet_trans e₁ (hc.mul_congr hSi hBo hSi jDt' jDt jD jD e₂ (eqAsJet_refl _ _ _))
  have hb := hAss.1
  have fN : ∀ κ ∈ imStrip (2 * stripHalfWidth),
      SymbolSummableAt (colourVertices L k 0) (colourVertices L k 0) (vertexResolventSqrt L k) κ :=
    fun κ hκ => hRootS.sqrt_summable κ (hstrip hκ)
  have jN : IsJet stripHalfWidth p (vertexSqrtJet L k) :=
    (hL.2.2 _ _ _ hSi hSi hSi stripHalfWidth p hδ hps).ofKernel_isJet _ hRootS.sqrt_periodic
      ⟨_, hopenI, hstrip, hRootS.sqrt_summable, fun c' c => hRootS.sqrt_holomorphicOn.2.2 (c', c)⟩
  have jM : IsJet stripHalfWidth p (vertexInvSqrtJet L k) :=
    (hL.2.2 _ _ _ hSi hSi hSi stripHalfWidth p hδ hps).ofKernel_isJet _ hRootS.invSqrt_periodic
      ⟨_, hopenI, hstrip, hRootS.invSqrt_summable,
        fun c' c => hRootS.invSqrt_holomorphicOn.2.2 (c', c)⟩
  have hMN : EqAsJet stripHalfWidth p (mul p (vertexInvSqrtJet L k) (vertexSqrtJet L k))
      (one (colourVertices L k 0)) := by
    refine ⟨fun κ hκ => (hRootS.invSqrt_inverse κ (hstrip hκ)).1, fun κ _ => ?_, fun κ _ => ?_,
      fun κ _ => ?_⟩ <;> simp [mul, vertexInvSqrtJet, vertexSqrtJet, ofKernel, one]
  have hsq : EqAsJet stripHalfWidth p (mul p (vertexSqrtJet L k) (vertexSqrtJet L k))
      (ofKernel (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k)) := by
    refine ⟨fun κ hκ => (hRootS.resolvent_eq_sq κ (hstrip hκ)).2.symm, fun κ _ => ?_,
      fun κ _ => ?_, fun κ _ => ?_⟩ <;> simp [mul, vertexSqrtJet, ofKernel]
  have hNt : EqAsJet stripHalfWidth p (transposeAt p (vertexSqrtJet L k)) (vertexSqrtJet L k) := by
    have own := (hProp L hLb k hk).2.2.2.2.1.transpose_eq (-(1 / 2)) (by simp [resolventExponents])
    refine ⟨fun κ hκ => ?_, fun κ _ => quotHomTranspose_zero pa3 hSi hSi,
      fun κ _ => quotHomTranspose_zero pa3 hSi hSi,
      fun κ _ => quotHomTranspose_zero pa3 hSi hSi⟩
    show quotHomTranspose (symbolHom _ _ (vertexResolventSqrt L k) (-κ)) =
      symbolHom _ _ (vertexResolventSqrt L k) κ
    have hneg := (hArgs.1 stripHalfWidth p hδ hps).2.2.comp00 κ hκ
    rw [quotHomTranspose_symbolHom_neg q2 hSi hSi hRootS.sqrt_periodic (fN _ hneg)]
    exact congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ) own
  have hcomp := ((pa3 _ _ hSi hSi).2.2.2.2.2.2.1 _ hSi).2
  have hN : jetNorm stripHalfWidth p (vertexSqrtJet L k) ≤ ENNReal.ofReal C₀ :=
    hc.jetNorm_le_of_f00 hSi hSi (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hb.vertex_sqrt.2
  have hP : jetNorm stripHalfWidth p
      (ofKernel (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k)) ≤
        ENNReal.ofReal (C₀ ^ 2) := by
    refine hc.jetNorm_le_of_f00 hSi hSi (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      fun κ hκ => ?_
    show quotHomNorm (symbolHom _ _ (vertexResolvent L k) κ) ≤ _
    rw [(hRootS.resolvent_eq_sq κ (hstrip hκ)).2, sq, ENNReal.ofReal_mul hC0]
    exact (hcomp _ _).trans (mul_le_mul' (hb.vertex_sqrt.2 κ hκ) (hb.vertex_sqrt.2 κ hκ))
  have hbound := hCb k hk μPlus μMinus p hp
  have hR : jetNorm stripHalfWidth p (mul p (vertexSmoothingJet L k p μPlus μMinus)
      (vertexSqrtJet L k)) ≤ ENNReal.ofReal (Cb * C₀) :=
    hc.jetNorm_mul_le_ofReal hSiK hSi hSi hCb0 jR jN hbound.vertexSmoothing hN
  have jd : IsJet stripHalfWidth p
      (ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0)) := by
    obtain ⟨O, hO, hsub, hhol⟩ := jD.holo_f00
    rw [covDerivJet_f00, hDeq] at hhol
    exact (hL.2.2 _ _ _ hSi hBo hBo stripHalfWidth p hδ hps).ofKernel_isJet _ oD.1
      ⟨O, hO, hsub, fun κ _ => fD κ, hhol⟩
  have je : IsJet stripHalfWidth p (covDerivDefectJet L k p μPlus μMinus) :=
    hc.isJet_add hSi hBo jD (hc.isJet_smul hSi hBo _ jd)
  have hdN : jetNorm stripHalfWidth p
      (mul p (ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0)) (vertexSqrtJet L k)) ≤ ENNReal.ofReal C₀ := by
    refine hc.jetNorm_le_of_f00 hSi hBo (fun κ => ?_) (fun κ => ?_) (fun κ => ?_)
      fun κ hκ => ?_
    · simp [mul, vertexSqrtJet, ofKernel]
    · simp [mul, vertexSqrtJet, ofKernel]
    · simp [mul, vertexSqrtJet, ofKernel]
    have h := hb.diff_vertex_sqrt.2.2 κ hκ
    have pr := symbolHom_compKernel q2 hSi hBo hSi (T := FreeStrip.vertexDiff L k) oD.1
      hRootS.sqrt_periodic (fD κ) (fN κ hκ)
    rw [pr.2.2.2] at h
    exact h
  have hDN : jetNorm stripHalfWidth p (mul p (covDerivJet L k p μPlus μMinus)
      (vertexSqrtJet L k)) ≤ ENNReal.ofReal (Cb * C₀ + C₀) := by
    rw [covDerivJet_eq_add, jetMul_add_left, ENNReal.ofReal_add ha hC0]
    exact (hc.jetNorm_add_le hSi hBo _ _).trans (add_le_add
      (hc.jetNorm_mul_le_ofReal hBo hSi hSi hCb0 je jN hbound.covDerivDefect hN) hdN)
  have cRt : ∀ κ, (transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourVertices L k k) (colourVertices L k 0)
        (trivialRescaledOperators L k).Rt κ := fun κ => by
    show quotHomTranspose ((vertexSmoothingJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [vertexSmoothingJet_f00]
    exact quotHomTranspose_symbolHom_neg q2 hSi hSiK oR.1 (fR _)
  have cY : ∀ κ, ((vertexOperatorJet L k p μPlus μMinus).add
      (vertexCorrectionJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Y κ := fun κ => by
    have p₁ := symbolHom_compKernel q2 hSiK hSi hSi oRt.1 oR.1 (fRt κ) (fR κ)
    have c₁ := ((q2.2.1 _ _ hSi hSi).2.1 _ κ oDelta.1 (fDelta κ)).linComb _ p₁.2.1 p₁.2.2.1 1 1
    have c₃ := c₁.2.2
    rw [p₁.2.2.2] at c₃
    rw [trivial_Y_eq]
    refine Eq.trans ?_ c₃.symm
    show (vertexOperatorJet L k p μPlus μMinus).f00 κ +
        ((transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ).comp
          ((vertexSmoothingJet L k p μPlus μMinus).f00 κ) = _
    rw [cRt, vertexOperatorJet_f00, vertexSmoothingJet_f00]
    simp only [one_smul]
  have hM := (hMid' L hLb k hk p hp μPlus μMinus).1
  have fam : ∀ t ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p
        (unitShiftedPath (vertexOperatorJet L k p μPlus μMinus)
          (vertexCorrectionJet L k p μPlus μMinus) t) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p (vertexSqrtJet L k)
          (unitShiftedPath (vertexOperatorJet L k p μPlus μMinus)
            (vertexCorrectionJet L k p μPlus μMinus) t)).f00 κ : Module.End ℂ _) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p (vertexSqrtJet L k)
          (unitShiftedPath (vertexOperatorJet L k p μPlus μMinus)
            (vertexCorrectionJet L k p μPlus μMinus) t)).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    intro t ht
    refine ⟨(hM t ht).2.1.1, fun κ hκ => ?_⟩
    have si := symbolHom_interpPlusOne q2 pa3 hid hSi oY.1 oDelta.1 (fY κ) (fDelta κ) t
    have h := isUnit_symbolHom_triple q2 hSi hκ hRootS.sqrt_periodic si.1 (fN κ hκ) si.2.1
      (hAss.2 t ht t ht).vertex_interp
    rw [si.2.2] at h
    have e : (unitShiftedPath (vertexOperatorJet L k p μPlus μMinus)
        (vertexCorrectionJet L k p μPlus μMinus) t).f00 κ =
        (t : ℂ) • symbolHom _ _ (trivialRescaledOperators L k).Y κ +
          ((1 - t : ℝ) : ℂ) • symbolHom _ _ (trivialRescaledOperators L k).Delta κ +
            scalarQuotHom (colourVertices L k 0) 1 := by
      rw [unitShiftedPath_f00, cY κ, vertexOperatorJet_f00]
    rw [conjugateBy_f00, e]
    exact h
  have shf : ∀ τ ∈ Icc (0 : ℝ) 1,
      IsInvertibleJet stripHalfWidth p
        (addScalarJet ((vertexOperatorJet L k p μPlus μMinus).add
          (vertexCorrectionJet L k p μPlus μMinus)) τ) ∧
      ∀ κ ∈ imStrip (2 * stripHalfWidth),
        IsUnit ((conjugateBy p (vertexSqrtJet L k)
          (addScalarJet ((vertexOperatorJet L k p μPlus μMinus).add
            (vertexCorrectionJet L k p μPlus μMinus)) τ)).f00 κ : Module.End ℂ _) ∧
        quotHomNorm (quotHomInverse ((conjugateBy p (vertexSqrtJet L k)
          (addScalarJet ((vertexOperatorJet L k p μPlus μMinus).add
            (vertexCorrectionJet L k p μPlus μMinus)) τ)).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    intro τ hτ
    refine ⟨(hM τ hτ).2.2.2.1, fun κ hκ => ?_⟩
    have sum := (hAss.2 τ hτ τ hτ).vertex_inverse
    have h := isUnit_symbolHom_triple q2 hSi hκ hRootS.sqrt_periodic sum.periodic (fN κ hκ)
      (sum.symbol κ hκ).2.1 (hAss.2 τ hτ τ hτ).vertex_add
    rw [(sum.symbol κ hκ).2.2] at h
    have e : (addScalarJet ((vertexOperatorJet L k p μPlus μMinus).add
        (vertexCorrectionJet L k p μPlus μMinus)) τ).f00 κ =
        symbolAddScalar (colourVertices L k 0) τ (trivialRescaledOperators L k).Y κ := by
      show ((vertexOperatorJet L k p μPlus μMinus).add
        (vertexCorrectionJet L k p μPlus μMinus)).f00 κ + (τ : ℂ) • LinearMap.id = _
      rw [cY κ]
      rfl
    rw [conjugateBy_f00, e]
    exact h
  exact rootInterpolationData_of_bounds hc hSi hBo hSiK hC0 hy ha hC0 jDelta jN jM jD jR hMN hNt
    hsq hP hA hN hDN hR fam shf
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.VertexRootJets
end
