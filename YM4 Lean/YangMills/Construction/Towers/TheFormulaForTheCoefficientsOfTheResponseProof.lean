import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheFormulaForTheCoefficientsOfTheResponse
import YangMills.Construction.Towers.TheMassiveJetsProof
import YangMills.Construction.Towers.TheRelationsOfTheResponse
import YangMills.Construction.Towers.TheResponseOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseCoefficientFormula
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.PlaneWaveCalculus (edgeCoboundaryT vertexCoboundaryT)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect)
open YangMills.Construction.Tower.PlaneWaves (VertexClass fourierCoeff edgeFourierCoeff
  edgeFieldOfClasses edgeAt)
open YangMills.Construction.Tower.ResponseProperties (ResponseModeEquations oneMinusSmoothingSquare
  coboundaryLaplacian responseDivergenceKernel smoothedDivergence responseSymbolForm defectSymbol)
variable {L k : ℕ}
theorem finite_vertexClass (hS : IsPeriodic (colourVertices L k 0)) :
    Finite (VertexClass L k) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finite_vertexClass <;> assumption
theorem edgeFourierCoeff_add (hf : Finite (VertexClass L k))
    (b b' : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k (b + b') μ m =
      edgeFourierCoeff L k b μ m + edgeFourierCoeff L k b' μ m := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.edgeFourierCoeff_add <;> assumption
theorem symbolHom_idKernel {I : PeriodicData}
    (hI : IsPeriodic I) (hS : StripSymbols.Claim) (κ : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) κ = LinearMap.id := by
  have hform := ((hS.2.1 I I hI hI).1.identity κ).2
  have := hI.finite_quot
  let _ := Fintype.ofFinite I.UnitQuot
  have unitId : linearMapOfEntries (quotOne I) = LinearMap.id := by
    refine LinearMap.ext fun f => ?_
    rw [linearMapOfEntries_eq_applyKernel]
    funext c
    classical
    simp [applyKernel, tsum_fintype, quotOne]
  change linearMapOfEntries (quotSymbol I I _ κ) = _
  rw [hform, unitId]
theorem symbolHom_zero (hS : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) {κ : Fin 4 → ℂ} (hf : SymbolSummableAt I I' T κ) :
    symbolHom I I' (0 : I'.Carrier → I.Carrier → ℂ) κ = 0 := by
  have e := (((hS.2.1 I I' hI hI').2.1 T κ hT hf).linComb T hT hf 0 0).2.2
  have z : StripSymbols.linCombKernel 0 0 T T = (0 : I'.Carrier → I.Carrier → ℂ) := by
    funext ι' ι
    simp [StripSymbols.linCombKernel]
  rw [z] at e
  simpa using e
theorem claim_holds (hT : TowerIndexSets.Claim) (hId : IdKernelFacts.Claim)
    (hS : StripSymbols.Claim) (hF : FreeOperators.FreeOperatorsArePeriodic)
    (hC : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hOne : FullSpace.RescaledTrivialRelations)
    (hRel : ResponseRelationsAtAllHeights.ResponseRelationsHold) (hR : ResponseOperators.Claim) :
    Claim := by
  intro δ₀ hδ L hL k hk p hp ε
  obtain ⟨δ₁, hδ₁, hAt⟩ := hR
  obtain rfl : δ₁ = δ₀ := Part.mem_unique hδ₁ hδ
  have hA := hAt L hL k hk
  obtain ⟨O, -, hO, hN⟩ := hA.near
  have hpO : p ∈ O := hO hp.1
  have fh : SymbolSummableAt (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) p :=
    hN.resp_summable p hpO
  have fν : SymbolSummableAt (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) p := hN.defect_summable p hpO
  have qh : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) :=
    hA.resp_periodic
  have qν : IsPeriodicKernel (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) := hA.defect_periodic
  obtain ⟨sS, sB, sP⟩ := hT L hL k 0 (Nat.zero_le k)
  obtain ⟨tS, tB, -⟩ := hT L hL k k le_rfl
  obtain ⟨hM, hOp⟩ := hF.2 L hL k hk
  obtain ⟨-, -, -, -, -, hAct, hAvg, -⟩ := hC L hL k hk
  have rel := hRel L hL k hk
  have hKeq := (hOne L hL k hk).K_eq
  have pDt := hOp.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have pPt := hOp.edgeCoboundary_transpose 0 (Nat.zero_le k)
  have pD := (hM.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have pP := (hM.edgeCoboundary 0 (Nat.zero_le k)).finite_range
  have pQt := hOp.edgeAverage_transpose
  have pRt := hOp.vertexAverage_transpose
  have pR := hM.vertexAverage.finite_range
  have fDt := (hS.2.1 _ _ sB sS).1.finiteRange _ pDt.1 pDt.2.1 p (mem_univ _)
  have fPt := (hS.2.1 _ _ sP sB).1.finiteRange _ pPt.1 pPt.2.1 p (mem_univ _)
  have fD := (hS.2.1 _ _ sS sB).1.finiteRange _ pD.1 pD.2.1 p (mem_univ _)
  have fP := (hS.2.1 _ _ sB sP).1.finiteRange _ pP.1 pP.2.1 p (mem_univ _)
  have fQt := (hS.2.1 _ _ tB sB).1.finiteRange _ pQt.1 pQt.2.1 p (mem_univ _)
  have fRt := (hS.2.1 _ _ tS sS).1.finiteRange _ pRt.1 pRt.2.1 p (mem_univ _)
  have fR := (hS.2.1 _ _ sS tS).1.finiteRange _ pR.1 pR.2.1 p (mem_univ _)
  obtain ⟨-, qA, fA, eA⟩ := ((hS.2.1 _ _ sP sB).2.1 _ p pPt.1 fPt).comp _ sB _ pP.1 fP
  obtain ⟨-, -, -, eAh⟩ := ((hS.2.1 _ _ sB sB).2.1 _ p qA fA).comp _ tB _ qh fh
  obtain ⟨-, -, -, eQν⟩ := ((hS.2.1 _ _ tB sB).2.1 _ p pQt.1 fQt).comp _ tB _ qν fν
  have eLap : symbolHom (colourEdges L k 0) (colourEdges L k 0) (coboundaryLaplacian L k) p
        (responseSymbolForm L k p ε) =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p
        (defectSymbol L k p ε) := by
    have e := congrArg (fun T => symbolHom (colourEdges L k k) (colourEdges L k 0) T p ε)
      rel.laplacian_comp
    exact (LinearMap.congr_fun eAh ε).symm.trans (e.trans (LinearMap.congr_fun eQν ε))
  obtain ⟨-, qW, fW, eW⟩ := ((hS.2.1 _ _ sB sS).2.1 _ p pDt.1 fDt).comp _ tB _ qh fh
  obtain ⟨-, qRR, fRR, eRR⟩ := ((hS.2.1 _ _ tS sS).2.1 _ p pRt.1 fRt).comp _ sS _ pR.1 fR
  have idS := hId _ sS
  have fI := idS.2.2.1 p (mem_univ _)
  have cmb := ((hS.2.1 _ _ sS sS).2.1 _ p idS.1 fI).linComb _ qRR fRR 1 (-1)
  have eC : StripSymbols.linCombKernel 1 (-1) (idKernel (colourVertices L k 0))
      (compKernel (FullSpace.rescaledOperators L k fun _ => 1).Rt
        (FullSpace.rescaledOperators L k fun _ => 1).R) = oneMinusSmoothingSquare L k := by
    funext ι' ι
    simp only [StripSymbols.linCombKernel, one_mul, neg_mul, ← sub_eq_add_neg]
    rfl
  obtain ⟨qC₀, fC₀, sC₀⟩ := cmb
  have qC : IsPeriodicKernel (colourVertices L k 0) (colourVertices L k 0)
      (oneMinusSmoothingSquare L k) := Eq.mp (congrArg (IsPeriodicKernel _ _) eC) qC₀
  have fC : SymbolSummableAt (colourVertices L k 0) (colourVertices L k 0)
      (oneMinusSmoothingSquare L k) p :=
    Eq.mp (congrArg (fun T => SymbolSummableAt (colourVertices L k 0) (colourVertices L k 0) T p) eC) fC₀
  have sC := (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T p) eC).symm.trans
    sC₀
  obtain ⟨-, -, -, eCW⟩ := ((hS.2.1 _ _ sS sS).2.1 _ p qC fC).comp _ tB _ qW fW
  have eGauge : symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (vertexCoboundaryT L k 0) p (responseSymbolForm L k p ε) =
      symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt p
        (smoothedDivergence L k p ε) := by
    have e0 : symbolHom (colourEdges L k k) (colourVertices L k 0)
        (compKernel (oneMinusSmoothingSquare L k) (responseDivergenceKernel L k)) p = 0 := by
      rw [rel.gauge_comp]
      exact symbolHom_zero hS tB sS qW fW
    have e1 := LinearMap.congr_fun (eCW.symm.trans e0) ε
    rw [LinearMap.comp_apply, sC, eRR, symbolHom_idKernel sS hS] at e1
    have e2 : symbolHom (colourEdges L k k) (colourVertices L k 0)
        (compKernel (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
          (FullSpace.scaledVertexCoboundaryKernel L k 0)) (responseKernel L k)) p ε =
        symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (vertexCoboundaryT L k 0) p (responseSymbolForm L k p ε) := LinearMap.congr_fun eW ε
    rw [e2] at e1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply, one_smul, neg_smul] at e1
    exact eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans e1)
  obtain ⟨-, qB, fB, eB⟩ := ((hS.2.1 _ _ sS sB).2.1 _ p pD.1 fD).comp _ sB _ pDt.1 fDt
  have eK := ((hS.2.1 _ _ sB sB).2.1 _ p qA fA).linComb _ qB fB 1 1
  have e₂ : (PlaneWaveCalculus.freeOps L k).K = StripSymbols.linCombKernel 1 1
      (compKernel (edgeCoboundaryT L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0))
      (compKernel (FullSpace.scaledVertexCoboundaryKernel L k 0)
        (vertexCoboundaryT L k 0)) := by
    funext ι' ι
    refine (congrFun (congrFun hKeq ι') ι).trans ?_
    show (_ : ℂ) + _ = 1 * _ + 1 * _
    rw [one_mul, one_mul]
    rfl
  have eKb : symbolHom (colourEdges L k 0) (colourEdges L k 0)
        (PlaneWaveCalculus.freeOps L k).K p (responseSymbolForm L k p ε) =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p
          (defectSymbol L k p ε) +
        symbolHom (colourVertices L k 0) (colourEdges L k 0)
          (FullSpace.scaledVertexCoboundaryKernel L k 0) p
          (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt p
            (smoothedDivergence L k p ε)) := by
    have t₁ := LinearMap.congr_fun eK.2.2 (responseSymbolForm L k p ε)
    have t₂ := LinearMap.congr_fun eB (responseSymbolForm L k p ε)
    rw [← eLap, ← eGauge]
    refine (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T p
      (responseSymbolForm L k p ε)) e₂).trans (t₁.trans ?_)
    simp only [LinearMap.add_apply, one_smul]
    exact congrArg₂ (· + ·) rfl t₂
  intro m hm μ
  have hf := finite_vertexClass sS
  have h1 := hAct.K p (responseSymbolForm L k p ε) μ m hm
  have c₁ : edgeFourierCoeff L k
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p
        (defectSymbol L k p ε)) μ m = _ := hAvg.Qt p _ μ m hm
  have c₂ : PlaneWaves.vertexFourierCoeff L k
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt p
        (smoothedDivergence L k p ε)) m = _ := hAvg.Rt p _ m hm
  rw [← h1, eKb, edgeFourierCoeff_add hf, c₁, hAct.vertexCoboundary p _ μ m hm, c₂, smul_smul]
end YangMills.Construction.Tower.ResponseCoefficientFormula
end
