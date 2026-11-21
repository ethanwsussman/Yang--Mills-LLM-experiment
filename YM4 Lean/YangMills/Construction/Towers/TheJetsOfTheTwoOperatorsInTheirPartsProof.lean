import YangMills.Construction.Towers.TheBondJetsBetweenTheRootsOfTheFreePropagatorProof
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocalProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetDecomposition
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.PeriodicOperators.ConstantOpFun (constAssign)
section Maps
variable {I I' I'' : PeriodicData}
theorem quotHomTranspose_symbolHom_neg (hsym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {κ : Fin 4 → ℂ} (fT : SymbolSummableAt I I' T (-κ)) :
    quotHomTranspose (symbolHom I I' T (-κ)) = symbolHom I' I (kernelTranspose I I' T) κ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomTranspose_symbolHom_neg <;> assumption
theorem quotHomTranspose_zero (hnorm : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') : quotHomTranspose (0 : QuotHom I I') = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomTranspose_zero <;> assumption
theorem symbolHom_compKernel (hsym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    (∀ i' i'', CompSummableAt T S i' i'') ∧ IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  ((hsym.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS
theorem transposeAt_ofKernel (hsym : StripSymbols.Claim)
    (hnorm : HomNorm.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (fT : ∀ κ, SymbolSummableAt I I' T κ) (p : Fin 4 → ℂ) :
    transposeAt p (ofKernel I I' T) = ofKernel I' I (kernelTranspose I I' T) := by
  apply JetQuad.ext
  · funext κ
    exact quotHomTranspose_symbolHom_neg hsym hI hI' hT (fT _)
  · funext κ
    exact quotHomTranspose_zero hnorm hI hI'
  · funext κ
    exact quotHomTranspose_zero hnorm hI hI'
  · funext κ
    exact quotHomTranspose_zero hnorm hI hI'
theorem ofKernel_compKernel (hsym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S)
    (fT : ∀ κ, SymbolSummableAt I I' T κ) (fS : ∀ κ, SymbolSummableAt I'' I S κ)
    (δ : ℝ) (p : Fin 4 → ℂ) :
    EqAsJet δ p (ofKernel I'' I' (compKernel T S))
      (mul p (ofKernel I I' T) (ofKernel I'' I S)) := by
  refine ⟨fun κ _ => (symbolHom_compKernel hsym hI hI' hI'' hT hS (fT κ) (fS κ)).2.2.2, fun κ _ => ?_,
    fun κ _ => ?_, fun κ _ => ?_⟩ <;> simp [mul, ofKernel]
theorem ofKernel_linCombKernel (hsym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {A C : I'.Carrier → I.Carrier → ℂ}
    (hA : IsPeriodicKernel I I' A) (hC : IsPeriodicKernel I I' C)
    (fA : ∀ κ, SymbolSummableAt I I' A κ) (fC : ∀ κ, SymbolSummableAt I I' C κ)
    {δ : ℝ} {p : Fin 4 → ℂ} {X Y : JetQuad I I'} (hX : EqAsJet δ p (ofKernel I I' A) X)
    (hY : EqAsJet δ p (ofKernel I I' C) Y) :
    EqAsJet δ p (ofKernel I I' (StripSymbols.linCombKernel 1 1 A C)) (add X Y) := by
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · have e := (((hsym.2.1 I I' hI hI').2.1 A κ hA (fA κ)).linComb C hC (fC κ) 1 1).2.2
    show symbolHom I I' _ κ = X.f00 κ + Y.f00 κ
    rw [e, one_smul, one_smul, ← hX.1 hκ, ← hY.1 hκ]
    rfl
  · show (0 : QuotHom I I') = X.f10 κ + Y.f10 κ
    rw [← hX.2.1 hκ, ← hY.2.1 hκ]
    simp [ofKernel]
  · show (0 : QuotHom I I') = X.f01 κ + Y.f01 κ
    rw [← hX.2.2.1 hκ, ← hY.2.2.1 hκ]
    simp [ofKernel]
  · show (0 : QuotHom I I') = X.f11 κ + Y.f11 κ
    rw [← hX.2.2.2 hκ, ← hY.2.2.2 hκ]
    simp [ofKernel]
end Maps
section Quadruples
variable {I₁ I₂ I₃ : PeriodicData}
theorem eqAsJet_refl (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I₁ I₂) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_trans {δ : ℝ} {p : Fin 4 → ℂ} {T S R : JetQuad I₁ I₂} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
end Quadruples
structure JetToolkit (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  pos : 0 < δ
  mem_strip : p ∈ imStrip δ
  opFun : JetDomains.OpFunJetTheory
  calculus : JetCalculus.Claim
  arguments : JetArgumentsAndEqualJets
namespace JetToolkit
variable {δ : ℝ} {p : Fin 4 → ℂ} {I₁ I₂ I₃ : PeriodicData}
theorem isJet_mul (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T : JetQuad I₂ I₃} {S : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (mul p T S) :=
  (c.opFun.2.2 I₂ I₃ I₁ h₂ h₃ h₁ δ p c.pos c.mem_strip).mul_isJet T S jT jS
theorem isJet_transposeAt (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T : JetQuad I₁ I₂} (jT : IsJet δ p T) : IsJet δ p (transposeAt p T) :=
  (c.opFun.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.pos c.mem_strip).transpose_isJet T jT
theorem isJet_add (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T S : JetQuad I₁ I₂} (jT : IsJet δ p T) (jS : IsJet δ p S) : IsJet δ p (add T S) :=
  (c.opFun.2.2 I₁ I₂ I₂ h₁ h₂ h₂ δ p c.pos c.mem_strip).add_isJet T S jT jS
theorem mul_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    (h₃ : IsPeriodic I₃) {T T' : JetQuad I₂ I₃} {S S' : JetQuad I₁ I₂}
    (jT : IsJet δ p T) (jT' : IsJet δ p T') (jS : IsJet δ p S) (jS' : IsJet δ p S')
    (e : EqAsJet δ p T T') (e' : EqAsJet δ p S S') : EqAsJet δ p (mul p T S) (mul p T' S') :=
  (c.arguments.2.1 δ p I₂ I₃ h₂ h₃ T T' jT jT' e).2.2.2.2 I₁ h₁ S S' jS jS' e'
theorem add_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {T T' S S' : JetQuad I₁ I₂} (jT : IsJet δ p T) (jT' : IsJet δ p T') (jS : IsJet δ p S)
    (jS' : IsJet δ p S') (e : EqAsJet δ p T T') (e' : EqAsJet δ p S S') :
    EqAsJet δ p (add T S) (add T' S') :=
  (c.arguments.2.1 δ p I₁ I₂ h₁ h₂ T T' jT jT' e).2.2.2.1 S S' jS jS' e'
theorem transposeAt_congr (c : JetToolkit δ p) (h₁ : IsPeriodic I₁)
    (h₂ : IsPeriodic I₂) {T T' : JetQuad I₁ I₂} (jT : IsJet δ p T) (jT' : IsJet δ p T')
    (e : EqAsJet δ p T T') : EqAsJet δ p (transposeAt p T) (transposeAt p T') :=
  (c.arguments.2.1 δ p I₁ I₂ h₁ h₂ T T' jT jT' e).2.2.1
end JetToolkit
section Formula
variable {δ : ℝ} {p : Fin 4 → ℂ} {F V E Q : PeriodicData}
theorem isJet_jetAlong (c : JetToolkit δ p) {I I' : PeriodicData} (hF : IsPeriodic F)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (lT : IsLocalOpFun F I I' T)
    (εPlus εMinus : F.UnitQuot → ℂ) : IsJet δ p (jetAlong F I I' T p εPlus εMinus) :=
  (c.opFun.2.1 F I I' hF hI hI' T lT).isJet δ c.pos p c.mem_strip εPlus εMinus
theorem eqAsJet_hessianFormula (c : JetToolkit δ p) (hF : IsPeriodic F)
    (hV : IsPeriodic V) (hE : IsPeriodic E) (hQ : IsPeriodic Q)
    (εPlus εMinus : F.UnitQuot → ℂ)
    {S : (F.Carrier → ℂ) → Q.Carrier → E.Carrier → ℂ} {Z : (F.Carrier → ℂ) → Q.Carrier → Q.Carrier → ℂ}
    {C : (F.Carrier → ℂ) → E.Carrier → E.Carrier → ℂ} {D : (F.Carrier → ℂ) → E.Carrier → V.Carrier → ℂ}
    (lS : IsLocalOpFun F E Q S) (lZ : IsLocalOpFun F Q Q Z)
    (lC : IsLocalOpFun F E E C) (lD : IsLocalOpFun F V E D) :
    EqAsJet δ p
      (jetAlong F E E (opFunAdd (opFunAdd (opFunComp (opFunTranspose S) (opFunComp Z S)) C)
        (opFunComp D (opFunTranspose D))) p εPlus εMinus)
      (add (add (mul p (transposeAt p (jetAlong F E Q S p εPlus εMinus))
          (mul p (jetAlong F Q Q Z p εPlus εMinus) (jetAlong F E Q S p εPlus εMinus)))
          (jetAlong F E E C p εPlus εMinus))
        (mul p (jetAlong F V E D p εPlus εMinus) (transposeAt p (jetAlong F V E D p εPlus εMinus)))) := by
  have hJ := (c.calculus δ p c.pos c.mem_strip).2.2.1
  have lSt := (c.opFun.1 F E Q Q hF hE hQ hQ).2.2 S lS
  have lZS := (c.opFun.1 F Q Q E hF hQ hQ hE).2.1 Z S lZ lS
  have lA := (c.opFun.1 F Q E E hF hQ hE hE).2.1 _ _ lSt lZS
  have lH := (c.opFun.1 F E E E hF hE hE hE).1 _ C lA lC
  have lDt := (c.opFun.1 F V E E hF hV hE hE).2.2 D lD
  have lG := (c.opFun.1 F V E E hF hV hE hE).2.1 D _ lD lDt
  have jS := isJet_jetAlong c hF hE hQ lS εPlus εMinus
  have jZ := isJet_jetAlong c hF hQ hQ lZ εPlus εMinus
  have jC := isJet_jetAlong c hF hE hE lC εPlus εMinus
  have jD := isJet_jetAlong c hF hV hE lD εPlus εMinus
  have jSt := isJet_jetAlong c hF hQ hE lSt εPlus εMinus
  have jZS := isJet_jetAlong c hF hE hQ lZS εPlus εMinus
  have jA := isJet_jetAlong c hF hE hE lA εPlus εMinus
  have jH := isJet_jetAlong c hF hE hE lH εPlus εMinus
  have jDt := isJet_jetAlong c hF hE hV lDt εPlus εMinus
  have jG := isJet_jetAlong c hF hE hE lG εPlus εMinus
  have jSt' := c.isJet_transposeAt hE hQ jS
  have jZS' := c.isJet_mul hE hQ hQ jZ jS
  have jA' := c.isJet_mul hE hQ hE jSt' jZS'
  have jDt' := c.isJet_transposeAt hV hE jD
  have e₁ := (hJ F E E E hF hE hE hE εPlus εMinus).1 _ _ lH lG
  have e₂ := (hJ F E E E hF hE hE hE εPlus εMinus).1 _ _ lA lC
  have e₃ := (hJ F E Q E hF hE hQ hE εPlus εMinus).2.1 _ _ lSt lZS
  have e₄ := (hJ F Q E E hF hQ hE hE εPlus εMinus).2.2 S lS
  have e₅ := (hJ F Q Q E hF hQ hQ hE εPlus εMinus).2.1 Z S lZ lS
  have e₆ := (hJ F E V E hF hE hV hE εPlus εMinus).2.1 D _ lD lDt
  have e₇ := (hJ F E V V hF hE hV hV εPlus εMinus).2.2 D lD
  have a₁ := eqAsJet_trans e₃ (c.mul_congr hE hQ hE jSt jSt' jZS jZS' e₄ e₅)
  have a₂ := eqAsJet_trans e₂ (c.add_congr hE hE jA jA' jC jC a₁ (eqAsJet_refl _ _ _))
  have a₃ := eqAsJet_trans e₆ (c.mul_congr hE hV hE jD jD jDt jDt' (eqAsJet_refl _ _ _) e₇)
  exact eqAsJet_trans e₁ (c.add_congr hE hE jH (c.isJet_add hE hE jA' jC) jG
    (c.isJet_mul hE hV hE jD jDt') a₂ a₃)
end Formula
theorem exists_form_gaugeField {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    ∃ a ∈ complexEdgeForms (meshAt L k 0), remainderGaugeField a = gaugeFieldOfForm L k ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.exists_complexForm <;> assumption
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
theorem vertexCoboundaryAddDefect_eq (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    vertexCoboundaryAddDefect L k p μPlus μMinus = covDerivJet L k p μPlus μMinus := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [vertexCoboundaryAddDefect, vertexCoboundaryJet, covDerivDefectJet, add, smul,
      Pi.add_apply, Pi.smul_apply] <;> module
abbrev covDerivFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D
abbrev halfFaceTraceFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourFaces L k 0).Carrier → (colourFaces L k 0).Carrier → ℂ :=
  fun ζ => halfFaceTraceKernel L k (gaugeFieldOfForm L k ζ)
abbrev curvatureFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun ζ => curvatureKernel (gaugeFieldOfForm L k ζ)
abbrev edgeCoboundaryAddDefectFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourFaces L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  opFunAdd (F := remainderIndex L k) (I := colourEdges L k 0) (I' := colourFaces L k 0)
    (constAssign (remainderIndex L k) (I := colourEdges L k 0)
      (I' := colourFaces L k 0) (scaledEdgeCoboundaryKernel L k 0))
    fun ζ => holonomyDefectKernel L k (gaugeFieldOfForm L k ζ)
theorem decompositionHolds_of (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hTr : RescaledConditions.Holds)
    (hHess : WilsonHessian.DecompositionHolds)
    (hsym : StripSymbols.Claim) (hnorm : HomNorm.Claim)
    (hL : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hW : ConstantOpFun.Claim) : DecompositionHolds := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδI, -, -⟩ := hNum
  have eδ : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  intro L hLb k hk p hp μPlus μMinus
  have hδ : 0 < stripHalfWidth := by rw [eδ]; exact hδI.1
  have hps : p ∈ imStrip stripHalfWidth := fun μ => (Complex.abs_im_le_norm _).trans (hp μ)
  have c : JetToolkit stripHalfWidth p := ⟨hδ, hps, hL, hCalc, hArgs⟩
  have hOps := (hOp.1 L hLb k hk).1
  obtain ⟨hV, hE, hQ, -, -⟩ := hOps.periodic
  obtain ⟨hmaps, hops⟩ := hFree.2 L hLb k hk
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hTr L hLb k hk).2
  have oD := (hmaps.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have oB := (hmaps.edgeCoboundary 0 (Nat.zero_le k)).finite_range
  have oDt := hops.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have oBt := hops.edgeCoboundary_transpose 0 (Nat.zero_le k)
  have formed : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        ∀ κ, SymbolSummableAt I I' T κ := fun hI hI' _ h κ =>
    (hsym.2.1 _ _ hI hI').1.finiteRange _ h.1 h.2.1 κ (mem_univ κ)
  have fD := formed hV hE oD
  have fB := formed hE hQ oB
  have fDt := formed hE hV oDt
  have fBt := formed hQ hE oBt
  have lD := hOps.D_local.1
  have lE := hOps.holonomyDefect_local.1
  have lZ := hOps.halfFaceTrace_local.1
  have lC := hOps.curvature_local.1
  have lDt := (hL.1 _ _ _ _ hE hV hE hE).2.2 _ lD
  have jD : IsJet stripHalfWidth p (covDerivJet L k p μPlus μMinus) :=
    isJet_jetAlong c hE hV hE lD _ _
  have jE : IsJet stripHalfWidth p (holonomyDefectJet L k p μPlus μMinus) :=
    isJet_jetAlong c hE hE hQ lE _ _
  have jZ : IsJet stripHalfWidth p (halfFaceTraceJet L k p μPlus μMinus) :=
    isJet_jetAlong c hE hQ hQ lZ _ _
  have jC : IsJet stripHalfWidth p (curvatureJet L k p μPlus μMinus) :=
    isJet_jetAlong c hE hE hE lC _ _
  have jDt := c.isJet_transposeAt hV hE jD
  have wB := (hW _ _ _ hE hE hQ _ oB.1 oB.2.1 stripHalfWidth p hδ hps
    (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).1
  have lB := wB.1
  have jB : IsJet stripHalfWidth p (edgeCoboundaryJet L k) :=
    (hL.2.2 _ _ _ hE hQ hQ stripHalfWidth p hδ hps).ofKernel_isJet _ oB.1 wB.2.2.2.2.1
  have jAssign := isJet_jetAlong c hE hE hQ lB (scaledResponseField L k p μPlus)
    (scaledResponseField L k (-p) μMinus)
  have lS := (hL.1 _ _ _ _ hE hE hQ hQ).1 _ _ lB lE
  have jS := isJet_jetAlong c hE hE hQ lS (scaledResponseField L k p μPlus)
    (scaledResponseField L k (-p) μMinus)
  have jS' : IsJet stripHalfWidth p (edgeCoboundaryAddDefect L k p μPlus μMinus) :=
    c.isJet_add hE hQ jB jE
  have eS := eqAsJet_trans (((hCalc stripHalfWidth p hδ hps).2.2.1 _ _ _ _ hE hQ hE hE
    (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).1 _ _ lB lE)
    (c.add_congr hE hQ jAssign jB jE jE wB.2.2.2.2.2 (eqAsJet_refl _ _ _))
  have eK : (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).K) =
      opFunAdd (opFunAdd (opFunComp (opFunTranspose (edgeCoboundaryAddDefectFun L k))
        (opFunComp (halfFaceTraceFun L k) (edgeCoboundaryAddDefectFun L k))) (curvatureFun L k))
      (opFunComp (covDerivFun L k) (opFunTranspose (covDerivFun L k))) := by
    funext ζ
    obtain ⟨a, ha, hc⟩ := exists_form_gaugeField hLb ζ
    have h2 := (hHess L hLb k hk).2 a ha
    rw [hc] at h2
    exact congrArg (· + compKernel (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D
      (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Dt) h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vertexCoboundaryAddDefect_eq]
    exact eqAsJet_refl _ _ _
  · rw [vertexCoboundaryAddDefect_eq]
    show EqAsJet _ _ (jetAlong (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
      (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).K) p _ _) _
    rw [eK]
    refine eqAsJet_trans (eqAsJet_hessianFormula c hE hV hE hQ _ _ lS lZ lC lD) ?_
    have jSt := c.isJet_transposeAt hE hQ jS
    have jSt' := c.isJet_transposeAt hE hQ jS'
    have jP := c.isJet_mul hE hQ hE jSt (c.isJet_mul hE hQ hQ jZ jS)
    have jP' := c.isJet_mul hE hQ hE jSt' (c.isJet_mul hE hQ hQ jZ jS')
    have jG := c.isJet_mul hE hV hE jD jDt
    exact c.add_congr hE hE (c.isJet_add hE hE jP jC) (c.isJet_add hE hE jP' jC) jG jG
      (c.add_congr hE hE jP jP' jC jC
        (c.mul_congr hE hQ hE jSt jSt' (c.isJet_mul hE hQ hQ jZ jS) (c.isJet_mul hE hQ hQ jZ jS')
          (c.transposeAt_congr hE hQ jS jS' eS)
          (c.mul_congr hE hQ hQ jZ jZ jS jS' (eqAsJet_refl _ _ _) eS))
        (eqAsJet_refl _ _ _))
      (eqAsJet_refl _ _ _)
  · rw [vertexCoboundaryAddDefect_eq]
    have jDt' := isJet_jetAlong c hE hE hV lDt (scaledResponseField L k p μPlus)
      (scaledResponseField L k (-p) μMinus)
    have e₁ := ((hCalc stripHalfWidth p hδ hps).2.2.1 _ _ _ _ hE hV hE hV
      (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).2.1 _ _ lDt lD
    have e₂ := ((hCalc stripHalfWidth p hδ hps).2.2.1 _ _ _ _ hE hE hV hV
      (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).2.2 _ lD
    exact eqAsJet_trans e₁ (c.mul_congr hV hE hV jDt' jDt jD jD e₂ (eqAsJet_refl _ _ _))
  · have e₂ : (trivialRescaledOperators L k).K = StripSymbols.linCombKernel 1 1
        (compKernel
          (kernelTranspose (colourEdges L k 0) (colourFaces L k 0)
            (scaledEdgeCoboundaryKernel L k 0))
          (scaledEdgeCoboundaryKernel L k 0))
        (compKernel (scaledVertexCoboundaryKernel L k 0)
          (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
            (scaledVertexCoboundaryKernel L k 0))) := by
      funext i' i
      refine (congrFun (congrFun hOne.K_eq i') i).trans ?_
      show (_ : ℂ) + _ = 1 * _ + 1 * _
      rw [one_mul, one_mul]
      rfl
    have t₁ := transposeAt_ofKernel hsym hnorm hE hQ oB.1 fB p
    have t₂ := transposeAt_ofKernel hsym hnorm hV hE oD.1 fD p
    show EqAsJet _ _ _ (add (mul p (transposeAt p (ofKernel (colourEdges L k 0)
        (colourFaces L k 0) (scaledEdgeCoboundaryKernel L k 0)))
        (ofKernel (colourEdges L k 0) (colourFaces L k 0)
          (scaledEdgeCoboundaryKernel L k 0)))
      (mul p (ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0))
        (transposeAt p (ofKernel (colourVertices L k 0) (colourEdges L k 0)
          (scaledVertexCoboundaryKernel L k 0)))))
    rw [t₁, t₂, e₂]
    exact ofKernel_linCombKernel hsym hE hE
      (symbolHom_compKernel hsym hQ hE hE oBt.1 oB.1 (fBt 0) (fB 0)).2.1
      (symbolHom_compKernel hsym hV hE hE oD.1 oDt.1 (fD 0) (fDt 0)).2.1
      (fun κ => (symbolHom_compKernel hsym hQ hE hE oBt.1 oB.1 (fBt κ) (fB κ)).2.2.1)
      (fun κ => (symbolHom_compKernel hsym hV hE hE oD.1 oDt.1 (fD κ) (fDt κ)).2.2.1)
      (ofKernel_compKernel hsym hQ hE hE oBt.1 oB.1 fBt fB _ p)
      (ofKernel_compKernel hsym hV hE hE oD.1 oDt.1 fD fDt _ p)
  · have e₂ : (trivialRescaledOperators L k).Delta = compKernel
        (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
          (scaledVertexCoboundaryKernel L k 0))
        (scaledVertexCoboundaryKernel L k 0) := hOne.Delta_eq
    have t := transposeAt_ofKernel hsym hnorm hV hE oD.1 fD p
    show EqAsJet _ _ _ (mul p (transposeAt p (ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0)))
      (ofKernel (colourVertices L k 0) (colourEdges L k 0)
        (scaledVertexCoboundaryKernel L k 0)))
    rw [t, e₂]
    exact ofKernel_compKernel hsym hE hV hV oDt.1 oD.1 fDt fD _ p
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetDecomposition
end
