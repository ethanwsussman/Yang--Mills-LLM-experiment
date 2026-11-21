import YangMills.Construction.Towers.TheMassiveJetsProof
import YangMills.Construction.Towers.TheBondJetsBetweenTheRootsOfTheFreePropagatorProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.Tower.FreeStrip
open YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.PeriodicOperators.JetNormsAffine (affinePath)
section Maps
variable {I I' : PeriodicData}
theorem isUnit_of_isInvertibleQuotHom {M : QuotHom I I} (h : IsInvertibleQuotHom M) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isUnit_of_isInvertibleQuotHom <;> assumption
theorem isUnit_and_norm_inverse_of_conj (hNorm : HomNorm.Claim)
    (hI : IsPeriodic I) {N Ni A : QuotHom I I} {C : ℝ} (hC : 0 ≤ C)
    (h₁ : Ni.comp N = LinearMap.id) (h₂ : N.comp Ni = LinearMap.id)
    (hN : quotHomNorm N ≤ ENNReal.ofReal C) (hB : IsInvertibleQuotHom ((N.comp A).comp N))
    (hBn : quotHomNorm (quotHomInverse ((N.comp A).comp N)) ≤ ENNReal.ofReal C) :
    IsUnit (A : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse A) ≤ ENNReal.ofReal (C ^ 3) := by
  have hcomp := ((hNorm I I hI hI).2.2.2.2.2.2.1 I hI).2
  let uN : (Module.End ℂ (I.UnitQuot → ℂ))ˣ := ⟨N, Ni, h₂, h₁⟩
  obtain ⟨uB, hB'⟩ := isUnit_of_isInvertibleQuotHom hB
  have cB : quotHomInverse ((N.comp A).comp N) =
      ((uB⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ (I.UnitQuot → ℂ)) := by
    show Ring.inverse (((N.comp A).comp N : QuotHom I I) : Module.End ℂ (I.UnitQuot → ℂ)) = _
    rw [← hB']
    exact Ring.inverse_unit uB
  have eA : (A : Module.End ℂ (I.UnitQuot → ℂ)) =
      ((uN⁻¹ * uB * uN⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ (I.UnitQuot → ℂ)) := by
    have eB : (uB : Module.End ℂ (I.UnitQuot → ℂ)) =
        (uN : Module.End ℂ (I.UnitQuot → ℂ)) * A * (uN : Module.End ℂ (I.UnitQuot → ℂ)) := hB'
    rw [Units.val_mul, Units.val_mul, eB]
    simp [mul_assoc]
  have cA : quotHomInverse A = (N.comp (quotHomInverse ((N.comp A).comp N))).comp N := by
    rw [cB]
    show Ring.inverse (A : Module.End ℂ (I.UnitQuot → ℂ)) = _
    rw [eA, Ring.inverse_unit]
    have e : (uN⁻¹ * uB * uN⁻¹)⁻¹ = uN * uB⁻¹ * uN := by group
    rw [e]
    rfl
  refine ⟨?_, ?_⟩
  · rw [eA]
    exact Units.isUnit _
  rw [cA]
  calc quotHomNorm ((N.comp (quotHomInverse ((N.comp A).comp N))).comp N)
      ≤ quotHomNorm (N.comp (quotHomInverse ((N.comp A).comp N))) * quotHomNorm N := hcomp _ _
    _ ≤ quotHomNorm N * quotHomNorm (quotHomInverse ((N.comp A).comp N)) * quotHomNorm N := by
        gcongr
        exact hcomp _ _
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal C * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (C ^ 3) := by
        rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
theorem quotHomTranspose_symbolHom_neg (hSym : StripSymbols.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    {κ : Fin 4 → ℂ} (fT : SymbolSummableAt I I' T (-κ)) :
    quotHomTranspose (symbolHom I I' T (-κ)) = symbolHom I' I (kernelTranspose I I' T) κ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.quotHomTranspose_symbolHom_neg <;> assumption
end Maps
theorem symbolHom_compKernel (hSym : StripSymbols.Claim) {I I' I'' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  ((hSym.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS
theorem symbolHom_interpPlusOne (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hid : IdKernelFacts.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {X K : I.Carrier → I.Carrier → ℂ} (hX : IsPeriodicKernel I I X) (hK : IsPeriodicKernel I I K)
    {κ : Fin 4 → ℂ} (fX : SymbolSummableAt I I X κ) (fK : SymbolSummableAt I I K κ) (t : ℝ) :
    IsPeriodicKernel I I (interpPlusOne I t X K) ∧
      SymbolSummableAt I I (interpPlusOne I t X K) κ ∧
      symbolHom I I (interpPlusOne I t X K) κ =
        (t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
          scalarQuotHom I 1 := by apply _root_.YangMills.Construction.Tower.FreeStrip.symbolHom_interpPlusOne_at <;> assumption
theorem isUnit_symbolHom_of_triple (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    {I : PeriodicData} (hI : IsPeriodic I) {N B : I.Carrier → I.Carrier → ℂ}
    {Ni : QuotHom I I} {D : Set (Fin 4 → ℂ)} {κ : Fin 4 → ℂ} {C : ℝ} (hC : 0 ≤ C) (hκ : κ ∈ D)
    (hN : IsPeriodicKernel I I N) (hB : IsPeriodicKernel I I B)
    (fN : SymbolSummableAt I I N κ) (fB : SymbolSummableAt I I B κ)
    (h₁ : Ni.comp (symbolHom I I N κ) = LinearMap.id)
    (h₂ : (symbolHom I I N κ).comp Ni = LinearMap.id)
    (hNn : quotHomNorm (symbolHom I I N κ) ≤ ENNReal.ofReal C)
    (tri : TripleCompSymbolInvertibleOn I I N B N D C) :
    IsUnit (symbolHom I I B κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse (symbolHom I I B κ)) ≤ ENNReal.ofReal (C ^ 3) := by
  have p₁ := symbolHom_compKernel hSym hI hI hI hN hB fN fB
  have p₂ := symbolHom_compKernel hSym hI hI hI p₁.2.1 hN p₁.2.2.1 fN
  have h := tri.2.2.2 κ hκ
  rw [p₂.2.2.2, p₁.2.2.2] at h
  exact isUnit_and_norm_inverse_of_conj hNorm hI hC h₁ h₂ hNn h.1 h.2
section Jets
variable {I : PeriodicData}
theorem invertibleOnStrip_of_f00 {C : ℝ} {p : Fin 4 → ℂ} {T : JetQuad I I}
    (hj : IsJet stripHalfWidth p T)
    (hU : ∀ κ ∈ imStrip (2 * stripHalfWidth), IsUnit (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      quotHomNorm (quotHomInverse (T.f00 κ)) ≤ ENNReal.ofReal C) :
    InvertibleOnStrip C p T :=
  ⟨⟨hj, fun κ hκ => (hU κ hκ).1,
    lt_of_le_of_lt (iSup₂_le fun κ hκ => (hU κ hκ).2) ENNReal.ofReal_lt_top⟩,
    fun κ hκ => (hU κ hκ).2⟩
theorem invJet_f00 (p : Fin 4 → ℂ) (T : JetQuad I I) (κ : Fin 4 → ℂ)
    (h : IsUnit (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ))) :
    (invJet p T).f00 κ = quotHomInverse (T.f00 κ) := by
  have e : (quotHomInverse (T.f00 κ)).comp (T.f00 κ) = LinearMap.id :=
    Ring.inverse_mul_cancel _ h
  have hN : (normalize p T).f00 κ = 0 := by
    show (quotHomInverse (T.f00 κ)).comp (T.f00 κ) + (-1 : ℂ) • LinearMap.id = 0
    rw [e]
    refine LinearMap.ext fun f => ?_
    show f + (-1 : ℂ) • f = 0
    rw [neg_smul, one_smul, add_neg_cancel]
  show ((LinearMap.id + (-1 : ℂ) • (normalize p T).f00 κ) +
      ((normalize p T).f00 κ).comp ((normalize p T).f00 κ)).comp
        (quotHomInverse (T.f00 κ)) = _
  rw [hN]
  simp
theorem unitShiftedPath_f00 (A W : JetQuad I I) (t : ℝ) (κ : Fin 4 → ℂ) :
    (unitShiftedPath A W t).f00 κ =
      (t : ℂ) • (A.add W).f00 κ + ((1 - t : ℝ) : ℂ) • A.f00 κ + scalarQuotHom I 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.unitShiftedPath_f00 <;> assumption
theorem invertibleOnStrip_of_sandwich (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hid : IdKernelFacts.Claim)
    (hL : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim)
    {J : PeriodicData} (hI : IsPeriodic I) (hJ : IsPeriodic J)
    {N X K : I.Carrier → I.Carrier → ℂ} {Ni : (Fin 4 → ℂ) → QuotHom I I}
    {Av : J.Carrier → I.Carrier → ℂ} {Avt : I.Carrier → J.Carrier → ℂ} {p : Fin 4 → ℂ}
    {A W : JetQuad I I} {R : JetQuad I J} {C : ℝ}
    (hδ : 0 < stripHalfWidth) (hp : p ∈ imStrip stripHalfWidth) (hC : 1 ≤ C)
    (hN : IsPeriodicKernel I I N) (hX : IsPeriodicKernel I I X) (hK : IsPeriodicKernel I I K)
    (hAv : IsPeriodicKernel I J Av) (hAvt : IsPeriodicKernel J I Avt)
    (fN : SymbolSummableOn I I N (imStrip (2 * stripHalfWidth)))
    (fX : SymbolSummableOn I I X (imStrip (2 * stripHalfWidth)))
    (fK : SymbolSummableOn I I K (imStrip (2 * stripHalfWidth)))
    (fAv : SymbolSummableOn I J Av (imStrip (2 * stripHalfWidth)))
    (fAvt : SymbolSummableOn J I Avt (imStrip (2 * stripHalfWidth)))
    (hNi : ∀ κ ∈ imStrip (2 * stripHalfWidth), (Ni κ).comp (symbolHom I I N κ) = LinearMap.id ∧
      (symbolHom I I N κ).comp (Ni κ) = LinearMap.id)
    (hNn : ∀ κ ∈ imStrip (2 * stripHalfWidth), quotHomNorm (symbolHom I I N κ) ≤ ENNReal.ofReal C)
    (jA : IsJet stripHalfWidth p A) (jW : IsJet stripHalfWidth p W) (jR : IsJet stripHalfWidth p R)
    (cA : ∀ κ, A.f00 κ = symbolHom I I K κ) (cX : ∀ κ, (A.add W).f00 κ = symbolHom I I X κ)
    (cR : ∀ κ, R.f00 κ = symbolHom I J Av κ)
    (cRt : ∀ κ, (transposeAt p R).f00 κ = symbolHom J I Avt κ)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1,
      TripleCompSymbolInvertibleOn I I N (interpPlusOne I t X K) N
          (imStrip (2 * stripHalfWidth)) C ∧
        TripleCompSymbolInvertibleOn I I N (addScalar I t X) N (imStrip (2 * stripHalfWidth)) C ∧
        TripleCompSymbolInvertibleOn J I Av (periodicInverse I (addScalar I t X)) Avt
          (imStrip (2 * stripHalfWidth)) C ∧
        AddScalarInvertibleOn I X t (imStrip (2 * stripHalfWidth))) :
    (∀ t ∈ Icc (0 : ℝ) 1, InvertibleOnStrip (C ^ 3) p (unitShiftedPath A W t) ∧
      InvertibleOnStrip (C ^ 3) p (addScalarJet (A.add W) t)) ∧
      InvertibleOnStrip (C ^ 3) p (A.add W) ∧
      InvertibleOnStrip (C ^ 3) p (mul p (mul p R (invJet p (A.add W))) (transposeAt p R)) := by
  have hC0 : 0 ≤ C := by linarith
  have hF := hL.2.2 I I I hI hI hI _ p hδ hp
  have jX : IsJet stripHalfWidth p (A.add W) := hF.add_isJet _ _ jA jW
  have plus : ∀ (T : JetQuad I I) (z : ℝ), IsJet stripHalfWidth p T →
      IsJet stripHalfWidth p (addScalarJet T z) := fun T z hT =>
    hF.add_isJet _ _ hT (hF.smul_isJet _ _ hF.one_isJet)
  have sum_unit : ∀ t ∈ Icc (0 : ℝ) 1, ∀ κ ∈ imStrip (2 * stripHalfWidth),
      IsUnit ((symbolAddScalar I t X κ : QuotHom I I) : Module.End ℂ (I.UnitQuot → ℂ)) ∧
        quotHomNorm (quotHomInverse (symbolAddScalar I t X κ)) ≤ ENNReal.ofReal (C ^ 3) := by
    intro t ht κ hκ
    obtain ⟨-, tri, -, sum⟩ := hs t ht
    have h := isUnit_symbolHom_of_triple hSym hNorm hI hC0 hκ hN sum.periodic (fN κ hκ)
      (sum.symbol κ hκ).2.1 (hNi κ hκ).1 (hNi κ hκ).2 (hNn κ hκ) tri
    rwa [(sum.symbol κ hκ).2.2] at h
  have zero_eq : ∀ κ, symbolAddScalar I 0 X κ = symbolHom I I X κ := fun κ => by
    simp [symbolAddScalar]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hXinv : InvertibleOnStrip (C ^ 3) p (A.add W) := by
    refine invertibleOnStrip_of_f00 jX fun κ hκ => ?_
    rw [cX κ, ← zero_eq κ]
    exact sum_unit 0 h0 κ hκ
  refine ⟨fun t ht => ⟨?_, ?_⟩, hXinv, ?_⟩
  · refine invertibleOnStrip_of_f00 (hF.add_isJet _ _ (plus A 1 jA) (hF.smul_isJet _ _ jW))
      fun κ hκ => ?_
    obtain ⟨tri, -, -, -⟩ := hs t ht
    have si := symbolHom_interpPlusOne hSym hNorm hid hI hX hK (fX κ hκ) (fK κ hκ) t
    have h := isUnit_symbolHom_of_triple hSym hNorm hI hC0 hκ hN si.1 (fN κ hκ) si.2.1 (hNi κ hκ).1
      (hNi κ hκ).2 (hNn κ hκ) tri
    rw [si.2.2] at h
    rw [unitShiftedPath_f00, cA κ, cX κ]
    exact h
  · refine invertibleOnStrip_of_f00 (plus _ t jX) fun κ hκ => ?_
    have e : (addScalarJet (A.add W) t).f00 κ = symbolAddScalar I t X κ := by
      show (A.add W).f00 κ + (t : ℂ) • LinearMap.id = _
      rw [cX κ]
      rfl
    rw [e]
    exact sum_unit t ht κ hκ
  · have hInv := (hCalc _ p hδ hp).2.2.2.2.1 I hI _ hXinv.1
    have hFJ := hL.2.2 I J I hI hJ hI _ p hδ hp
    have hFJ' := hL.2.2 I J J hI hJ hJ _ p hδ hp
    refine invertibleOnStrip_of_f00 (hFJ'.mul_isJet _ _ (hFJ.mul_isJet _ _ jR hInv.1)
      (hFJ'.transpose_isJet _ jR)) fun κ hκ => ?_
    obtain ⟨-, -, tri, sum⟩ := hs 0 h0
    have p₁ := symbolHom_compKernel hSym hI hJ hI hAv sum.inverse_periodic (fAv κ hκ)
      (sum.inverse_summable κ hκ)
    have p₂ := symbolHom_compKernel hSym hI hJ hJ p₁.2.1 hAvt p₁.2.2.1 (fAvt κ hκ)
    have h := tri.2.2.2 κ hκ
    rw [p₂.2.2.2, p₁.2.2.2, sum.inverse_symbol κ hκ, zero_eq κ] at h
    have e : (mul p (mul p R (invJet p (A.add W))) (transposeAt p R)).f00 κ =
        ((symbolHom I J Av κ).comp (quotHomInverse (symbolHom I I X κ))).comp
          (symbolHom J I Avt κ) := by
      show ((R.f00 κ).comp ((invJet p (A.add W)).f00 κ)).comp ((transposeAt p R).f00 κ) = _
      rw [invJet_f00 p _ κ (hXinv.1.isUnit_f00 κ hκ), cX κ, cR κ, cRt κ]
    rw [e]
    refine ⟨isUnit_of_isInvertibleQuotHom h.1, h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 3 := pow_le_pow_right₀ hC (by norm_num)
end Jets
section Tower
variable {L k : ℕ}
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = fun _ => 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.gaugeFieldOfForm_zero <;> assumption
theorem edgeOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (edgeOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.edgeOperatorJet_f00 <;> assumption
theorem vertexOperatorJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexOperatorJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.vertexOperatorJet_f00 <;> assumption
theorem covDerivJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (covDerivJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.covDerivJet_f00 <;> assumption
theorem edgeSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (edgeSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.edgeSmoothingJet_f00 <;> assumption
theorem vertexSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R := by apply _root_.YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBoundProof.vertexSmoothingJet_f00 <;> assumption
theorem Xi_eq_linComb (L k : ℕ) :
    (trivialRescaledOperators L k).Xi =
      StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).K
          (compKernel (compKernel (trivialRescaledOperators L k).D (trivialRescaledOperators L k).Rt)
            (compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Dt)))
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets.trivial_Xi_eq <;> assumption
theorem Y_eq_linComb (L k : ℕ) :
    (trivialRescaledOperators L k).Y =
      StripSymbols.linCombKernel 1 1 (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) := by
  funext ι' ι
  simp [RescaledOperators.Y, StripSymbols.linCombKernel]
end Tower
theorem middleJetsInvertibleClaim_holds (hNum : ConstantsAdmissible.ConstantsAreAdmissible)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hRoots : ResolventRootsOnStrip.ResolventRootsHold)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hTr : RescaledConditions.Holds)
    (hIter : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hSym : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    (hid : IdKernelFacts.Claim)
    (hL : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim) :
    MiddleJetsInvertibleClaim := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδI, hC₀, hAdm⟩ := hNum
  have eδ : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  refine ⟨C₀ ^ 3, ?_⟩
  intro L hLb k hk p hp μPlus μMinus
  have hAss : StripBounds L k stripHalfWidth C₀ := by
    rw [eδ]
    exact hAdm.2.2 L hLb k hk
  have hδ : 0 < stripHalfWidth := by rw [eδ]; exact hδI.1
  have hδle : stripHalfWidth ≤ 1 / 32 := by
    rw [eδ]
    have := hδI.2
    linarith
  have hps : p ∈ imStrip stripHalfWidth := fun μ => (Complex.abs_im_le_norm _).trans (hp μ)
  have hOps := (hOp.1 L hLb k hk).1
  obtain ⟨hSi, hBo, -, hSiK, hBoK⟩ := hOps.periodic
  obtain ⟨hmaps, hops⟩ := hFree.2 L hLb k hk
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hTr L hLb k hk).2
  have hstrip : imStrip (2 * stripHalfWidth) ⊆ StripSymbols.openStripInterior (1 / 8) := by
    have e := hSym.1 (1 / 8) (by norm_num)
    rw [e.1]
    exact e.2.2.2 (2 * stripHalfWidth) (by linarith) (by linarith)
  obtain ⟨hRootB, hRootS⟩ := hRoots L hLb k hk
  have z := Nat.zero_le k
  have hDeq : (trivialRescaledOperators L k).D = scaledVertexCoboundaryKernel L k 0 := hOne.D_eq
  have oD : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).D := by
    rw [hDeq]
    exact (hmaps.vertexCoboundary 0 z).finite_range
  have oDt : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Dt := by
    show FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourVertices L k 0)
      (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D)
    rw [hDeq]
    exact hops.vertexCoboundary_transpose 0 z
  have oQ : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q := hmaps.edgeAverage.finite_range
  have oR : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k k)
      (trivialRescaledOperators L k).R := hmaps.vertexAverage.finite_range
  have oQt : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k k) (colourEdges L k 0)
      (trivialRescaledOperators L k).Qt := hops.edgeAverage_transpose
  have oRt : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k k) (colourVertices L k 0)
      (trivialRescaledOperators L k).Rt := hops.vertexAverage_transpose
  have oK : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).K := hops.K
  have oDelta : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0)
      (colourVertices L k 0) (trivialRescaledOperators L k).Delta := hops.Delta
  have oXi : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).Xi := hops.Xi
  have oY : FreeOperators.HasFiniteRangeEveryRate (colourVertices L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Y := hops.Y
  have formed : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        ∀ κ, SymbolSummableAt I I' T κ := fun hI hI' _ h κ =>
    (hSym.2.1 _ _ hI hI').1.finiteRange _ h.1 h.2.1 κ (mem_univ κ)
  have fD := formed hSi hBo oD
  have fDt := formed hBo hSi oDt
  have fQ := formed hBo hBoK oQ
  have fR := formed hSi hSiK oR
  have fQt := formed hBoK hBo oQt
  have fRt := formed hSiK hSi oRt
  have fK := formed hBo hBo oK
  have fDelta := formed hSi hSi oDelta
  have fXi := formed hBo hBo oXi
  have fY := formed hSi hSi oY
  obtain ⟨ρ, cρ, hρ⟩ : ∃ ρ c,
      YangMills.Construction.Tower.IteratedSmallFieldMeans.AdmissibleConstants L ρ c :=
    ⟨_, _, hIter.1 L hLb⟩
  have lQ : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k k) fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q := by
    obtain ⟨r, R', hm, -⟩ := hOps.Q_local ρ cρ hρ
    exact ⟨r, R', hm⟩
  have lR : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R := by
    obtain ⟨r, R', hm, -⟩ := hOps.R_local ρ cρ hρ
    exact ⟨r, R', hm⟩
  have jK : IsJet stripHalfWidth p (edgeOperatorJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hBo _ hOps.K_local.1).isJet _ hδ p hps _ _
  have jDelta : IsJet stripHalfWidth p (vertexOperatorJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hSi _ hOps.Delta_local.1).isJet _ hδ p hps _ _
  have jD : IsJet stripHalfWidth p (covDerivJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hBo _ hOps.D_local.1).isJet _ hδ p hps _ _
  have jQ : IsJet stripHalfWidth p (edgeSmoothingJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hBo hBoK _ lQ).isJet _ hδ p hps _ _
  have jR : IsJet stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus) :=
    (hL.2.1 _ _ _ hBo hSi hSiK _ lR).isJet _ hδ p hps _ _
  have jQt := (hL.2.2 _ _ _ hBo hBoK hBoK _ p hδ hps).transpose_isJet _ jQ
  have jRt := (hL.2.2 _ _ _ hSi hSiK hSiK _ p hδ hps).transpose_isJet _ jR
  have jDt := (hL.2.2 _ _ _ hSi hBo hBo _ p hδ hps).transpose_isJet _ jD
  have jRtR : IsJet stripHalfWidth p (vertexCorrectionJet L k p μPlus μMinus) :=
    (hL.2.2 _ _ _ hSiK hSi hSi _ p hδ hps).mul_isJet _ _ jRt jR
  have jQtQ := (hL.2.2 _ _ _ hBoK hBo hBo _ p hδ hps).mul_isJet _ _ jQt jQ
  have jDRR := (hL.2.2 _ _ _ hSi hBo hSi _ p hδ hps).mul_isJet _ _ jD jRtR
  have jDRRD := (hL.2.2 _ _ _ hSi hBo hBo _ p hδ hps).mul_isJet _ _ jDRR jDt
  have jV : IsJet stripHalfWidth p (edgeCorrectionJet L k p μPlus μMinus) :=
    (hL.2.2 _ _ _ hBo hBo hBo _ p hδ hps).add_isJet _ _ jQtQ
      ((hL.2.2 _ _ _ hBo hBo hBo _ p hδ hps).smul_isJet _ _ jDRRD)
  have cQt : ∀ κ, (transposeAt p (edgeSmoothingJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ :=
    fun κ => by
    show quotHomTranspose ((edgeSmoothingJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [edgeSmoothingJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hBo hBoK oQ.1 (fQ _)
  have cRt : ∀ κ, (transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ :=
    fun κ => by
    show quotHomTranspose ((vertexSmoothingJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [vertexSmoothingJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hSi hSiK oR.1 (fR _)
  have cDt : ∀ κ, (transposeAt p (covDerivJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Dt κ :=
    fun κ => by
    show quotHomTranspose ((covDerivJet L k p μPlus μMinus).f00 (-κ)) = _
    rw [covDerivJet_f00]
    exact quotHomTranspose_symbolHom_neg hSym hSi hBo oD.1 (fD _)
  have cXi : ∀ κ, ((edgeOperatorJet L k p μPlus μMinus).add
      (edgeCorrectionJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ :=
    fun κ => by
    have p₁ := symbolHom_compKernel hSym hSi hBo hSiK oD.1 oRt.1 (fD κ) (fRt κ)
    have p₂ := symbolHom_compKernel hSym hSi hSiK hBo oR.1 oDt.1 (fR κ) (fDt κ)
    have p₃ := symbolHom_compKernel hSym hSiK hBo hBo p₁.2.1 p₂.2.1 p₁.2.2.1 p₂.2.2.1
    have p₄ := symbolHom_compKernel hSym hBoK hBo hBo oQt.1 oQ.1 (fQt κ) (fQ κ)
    have c₁ := ((hSym.2.1 _ _ hBo hBo).2.1 _ κ oK.1 (fK κ)).linComb _ p₃.2.1 p₃.2.2.1 1 (-1)
    have c₂ := ((hSym.2.1 _ _ hBo hBo).2.1 _ κ c₁.1 c₁.2.1).linComb _ p₄.2.1 p₄.2.2.1 1 1
    have c₃ := c₂.2.2
    rw [c₁.2.2, p₃.2.2.2, p₁.2.2.2, p₂.2.2.2, p₄.2.2.2] at c₃
    rw [Xi_eq_linComb]
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
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, one_smul]
    abel
  have cY : ∀ κ, ((vertexOperatorJet L k p μPlus μMinus).add
      (vertexCorrectionJet L k p μPlus μMinus)).f00 κ =
      symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Y κ :=
    fun κ => by
    have p₁ := symbolHom_compKernel hSym hSiK hSi hSi oRt.1 oR.1 (fRt κ) (fR κ)
    have c₁ := ((hSym.2.1 _ _ hSi hSi).2.1 _ κ oDelta.1 (fDelta κ)).linComb _ p₁.2.1 p₁.2.2.1 1 1
    have c₃ := c₁.2.2
    rw [p₁.2.2.2] at c₃
    rw [Y_eq_linComb]
    refine Eq.trans ?_ c₃.symm
    show (vertexOperatorJet L k p μPlus μMinus).f00 κ +
        ((transposeAt p (vertexSmoothingJet L k p μPlus μMinus)).f00 κ).comp
          ((vertexSmoothingJet L k p μPlus μMinus).f00 κ) = _
    rw [cRt, vertexOperatorJet_f00, vertexSmoothingJet_f00]
    simp only [one_smul]
  have hb := hAss.1
  have B := invertibleOnStrip_of_sandwich (I := colourEdges L k 0) (J := colourEdges L k k)
    (N := edgeResolventSqrt L k) (X := (trivialRescaledOperators L k).Xi)
    (K := (trivialRescaledOperators L k).K)
    (Ni := symbolHom _ _ (edgeResolventInvSqrt L k)) (Av := (trivialRescaledOperators L k).Q)
    (Avt := (trivialRescaledOperators L k).Qt)
    hSym hNorm hid hL hCalc hBo hBoK hδ hps hC₀ hRootB.sqrt_periodic oXi.1 oK.1 oQ.1 oQt.1
    hb.edge_sqrt.1 (fun κ _ => fXi κ) (fun κ _ => fK κ) (fun κ _ => fQ κ) (fun κ _ => fQt κ)
    (fun κ hκ => hRootB.invSqrt_inverse κ (hstrip hκ)) hb.edge_sqrt.2 jK jV jQ
    (fun κ => congrFun (edgeOperatorJet_f00 p μPlus μMinus) κ) cXi
    (fun κ => congrFun (edgeSmoothingJet_f00 p μPlus μMinus) κ) cQt
    (fun t ht => ⟨(hAss.2 t ht t ht).edge_interp, (hAss.2 t ht t ht).edge_add,
      (hAss.2 t ht t ht).edge_avg, (hAss.2 t ht t ht).edge_inverse⟩)
  have S := invertibleOnStrip_of_sandwich (I := colourVertices L k 0) (J := colourVertices L k k)
    (N := vertexResolventSqrt L k) (X := (trivialRescaledOperators L k).Y)
    (K := (trivialRescaledOperators L k).Delta)
    (Ni := symbolHom _ _ (vertexResolventInvSqrt L k)) (Av := (trivialRescaledOperators L k).R)
    (Avt := (trivialRescaledOperators L k).Rt)
    hSym hNorm hid hL hCalc hSi hSiK hδ hps hC₀ hRootS.sqrt_periodic oY.1 oDelta.1 oR.1 oRt.1
    hb.vertex_sqrt.1 (fun κ _ => fY κ) (fun κ _ => fDelta κ) (fun κ _ => fR κ) (fun κ _ => fRt κ)
    (fun κ hκ => hRootS.invSqrt_inverse κ (hstrip hκ)) hb.vertex_sqrt.2 jDelta jRtR jR
    (fun κ => congrFun (vertexOperatorJet_f00 p μPlus μMinus) κ) cY
    (fun κ => congrFun (vertexSmoothingJet_f00 p μPlus μMinus) κ) cRt
    (fun t ht => ⟨(hAss.2 t ht t ht).vertex_interp, (hAss.2 t ht t ht).vertex_add,
      (hAss.2 t ht t ht).vertex_avg, (hAss.2 t ht t ht).vertex_inverse⟩)
  exact ⟨fun t ht => ⟨(B.1 t ht).1, (S.1 t ht).1, (B.1 t ht).2, (S.1 t ht).2⟩, B.2.1, S.2.1, B.2.2,
    S.2.2⟩
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible
end
