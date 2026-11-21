import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.FreeOperatorsAtTheRealPoints
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.RealPoints
open PeriodicOperators
open PeriodicOperators.Quotients (conjKernel conjFun)
open FreeResolvents
open InfiniteLattice (AmbientSpace)
theorem applyKernel_linearMapEntry {J J' : Type} [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) :
    applyKernel (linearMapEntry M) f = M f := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.applyKernel_linearMapEntry <;> assumption
theorem wInner_self {J : Type} (w : J → ℝ) (h : J → ℂ) :
    wInner w h h = ((∑' i, w i * ‖h i‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.wInner_self_eq_tsum <;> assumption
theorem quotWeight_pos (hTransposeNorm : Quotients.QuotientTransposeNorm) {I : PeriodicData}
    (hI : IsPeriodic I) (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.quotWeight_one_pos <;> assumption
theorem isSelfAdjoint_of_transpose (hTransposeNorm : Quotients.QuotientTransposeNorm) {I : PeriodicData}
    (hI : IsPeriodic I) {M N : QuotHom I I} (htr : quotHomTranspose N = M)
    (hconj : conjKernel (linearMapEntry M) = linearMapEntry N) : IsSelfAdjointQuotHom M := by
  intro f g
  have := hI.finite_quot
  have hadj := ((hTransposeNorm I I hI hI 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)).2.2.1
    (linearMapEntry M) g f
  rw [hconj, applyKernel_linearMapEntry] at hadj
  have e : applyKernel (wTranspose (I.quotWeight 1) (I.quotWeight 1) (linearMapEntry N)) f = M f := by
    rw [← htr, quotHomTranspose, linearMapOfEntries_eq_applyKernel]
  rw [e] at hadj
  exact hadj
theorem isSelfAdjoint_scalar_zero (I : PeriodicData) : IsSelfAdjointQuotHom (scalarQuotHom I 0) := by
  intro f g
  simp [scalarQuotHom, wInner, PeriodicOperators.wPairing]
theorem loewner_nonneg_of_sq {I : PeriodicData} {A B : QuotHom I I}
    (hw : ∀ c, 0 ≤ I.quotWeight 1 c) (hB : IsSelfAdjointQuotHom B) (hA : A = B.comp B) :
    LoewnerLE (scalarQuotHom I 0) A := by
  subst hA
  have key : ∀ f : I.UnitQuot → ℂ,
      wInner (I.quotWeight 1) f ((B.comp B - scalarQuotHom I 0) f) =
        ((∑' c, I.quotWeight 1 c * ‖B f c‖ ^ 2 : ℝ) : ℂ) := by
    intro f
    have e : (B.comp B - scalarQuotHom I 0) f = B (B f) := by
      simp [scalarQuotHom]
    rw [e, ← hB f (B f), wInner_self]
  refine ⟨isSelfAdjoint_scalar_zero I, ?_, ?_, ?_⟩
  · intro f g
    change wInner _ (B (B f)) g = wInner _ f (B (B g))
    rw [hB (B f) g, hB f (B g)]
  · intro f
    rw [key, Complex.ofReal_im]
  · intro f
    rw [key, Complex.ofReal_re]
    exact tsum_nonneg fun c => mul_nonneg (hw c) (by positivity)
theorem mem_openImStrip_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    κ ∈ openImStrip 1 := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.mem_openImStrip_of_real <;> assumption
theorem conjVec_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    PlaneWaveCalculus.conjVec κ = κ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.conjVec_of_real <;> assumption
theorem toComplexVec_re_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    toComplexVec (fun μ => (κ μ).re) = κ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.toComplexVec_re <;> assumption
theorem mem_imStrip_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) {δ : ℝ} (hδ : 0 < δ) :
    κ ∈ strictImStrip δ := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.mem_imStrip_of_real <;> assumption
def symbolRoot (L k : ℕ) (q : Fin 4 → ℂ) : ℂ :=
  ((Real.sqrt (PlaneWaves.symbolSquare L k q).re : ℝ) : ℂ)
theorem symbolRoot_mul_self {L k : ℕ} (hf : PlaneWaveCalculus.SymbolFormulas L k)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) :
    symbolRoot L k (PlaneWaves.shiftedFreq κ m) * symbolRoot L k (PlaneWaves.shiftedFreq κ m) =
      PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) := by
  have hq : PlaneWaves.shiftedFreq κ m =
      toComplexVec (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) := by
    funext μ
    have e := congrFun (toComplexVec_re_of_real hκ) μ
    simp only [toComplexVec] at e
    simp only [PlaneWaves.shiftedFreq, toComplexVec]
    push_cast
    rw [e]
  rw [hq]
  have h := hf.symbolSquare_ofReal (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ))
  have h' : PlaneWaves.symbolSquare L k
      (toComplexVec fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) =
      ((∑ ν, ‖PlaneWaves.forwardSymbol L k
        (toComplexVec fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) ν‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]
    push_cast
    rfl
  simp only [symbolRoot]
  rw [h', Complex.ofReal_re, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
theorem loewner_nonneg_of_matrixFacts (hTransposeNorm : Quotients.QuotientTransposeNorm) {L k : ℕ}
    (hf : PlaneWaveCalculus.SymbolFormulas L k) {I : PeriodicData}
    (hI : IsPeriodic I) {MultR MultD : (Fin 4 → ℂ) → QuotHom I I → Prop}
    {MR MD : (Fin 4 → ℂ) → QuotHom I I}
    (FR : PlaneWaveCalculus.MultiplierMatrixFacts I MultR MR 1 (symbolRoot L k))
    (FD : PlaneWaveCalculus.MultiplierMatrixFacts I MultD MD 1 (PlaneWaves.symbolSquare L k))
    {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints)
    (hcomp : MultD κ ((MR κ).comp (MR κ))) {A : QuotHom I I} (hA : MultD κ A) :
    LoewnerLE (scalarQuotHom I 0) A := by
  have hs := mem_openImStrip_of_real hκ
  have hEven : ∀ q ∈ openImStrip 1, symbolRoot L k (-q) = symbolRoot L k q := by
    intro q _
    simp only [symbolRoot, hf.symbolSquare_neg]
  have hConj : ∀ q ∈ openImStrip 1,
      conj (symbolRoot L k q) =
        symbolRoot L k (PlaneWaveCalculus.conjVec q) := by
    intro q _
    simp only [symbolRoot, ← hf.conj_symbolSquare, Complex.conj_ofReal, Complex.conj_re]
  have hB : IsSelfAdjointQuotHom (MR κ) := by
    refine isSelfAdjoint_of_transpose hTransposeNorm hI (N := MR (-κ)) (FR.transpose_neg hEven κ hs) ?_
    have h := FR.conj_entries hEven hConj κ hs
    rwa [conjVec_of_real hκ] at h
  have e₁ := (FD.scales_unique κ hs).2 A hA
  have e₂ := (FD.scales_unique κ hs).2 _ hcomp
  exact loewner_nonneg_of_sq (fun c => (quotWeight_pos hTransposeNorm hI c).le) hB (e₁.trans e₂.symm)
theorem isAdjoint_symbolHom_kernelTranspose {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (facts : SymbolProperties I I' I'' T S 1) (hreal : ∀ ι' ι, (T ι' ι).im = 0)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    IsAdjointQuotHom (symbolHom I I' T κ) (symbolHom I' I (kernelTranspose I I' T) κ) := by
  intro f g
  have := hI.finite_quot
  have := hI'.finite_quot
  have e₁ : symbolHom I I' T κ f = applyKernel (quotSymbol I I' T κ) f :=
    linearMapOfEntries_eq_applyKernel _ _
  have e₂ : symbolHom I' I (kernelTranspose I I' T) κ g =
      applyKernel (quotSymbol I' I (kernelTranspose I I' T) κ) g :=
    linearMapOfEntries_eq_applyKernel _ _
  rw [e₁, e₂, (facts.quotSymbol_kernelTranspose κ (mem_imStrip_of_real hκ one_pos)).2]
  have h := facts.wInner_quotTranspose hreal (fun μ => (κ μ).re) f g
  rw [toComplexVec_re_of_real hκ] at h
  exact h.symm
theorem quotHomAdjoint_eq (hTransposeNorm : Quotients.QuotientTransposeNorm) {I I' : PeriodicData}
    (hI : IsPeriodic I) {M : QuotHom I I'} {A : QuotHom I' I}
    (h : IsAdjointQuotHom M A) : quotHomAdjoint M = A := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.quotHomAdjoint_eq <;> assumption
theorem edge_Qt_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Qt =
      kernelTranspose (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q := rfl
theorem vertex_Rt_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Rt =
      kernelTranspose (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R := rfl
theorem freeSymbolsAtRealPoints_holds (hplane : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hfree : FreeOperators.FreeOperatorsArePeriodic)
    (hidx : TowerIndexSets.Claim) (hsym : Symbols.Claim)
    (hTransposeNorm : Quotients.QuotientTransposeNorm) : FreeSymbolsAtRealPoints := by
  intro L hL k hk κ hκ
  obtain ⟨-, -, -, -, hf, hact, -, -, hreal, hM⟩ := hplane L hL k hk
  obtain ⟨hmaps, hops⟩ := hfree.2 L hL k hk
  have hS₀ := (hidx L hL k 0 (Nat.zero_le k)).1
  have hB₀ := (hidx L hL k 0 (Nat.zero_le k)).2.1
  have hSk := (hidx L hL k k le_rfl).1
  have hBk := (hidx L hL k k le_rfl).2.1
  have hs := mem_openImStrip_of_real hκ
  have hRootPer : ∀ q ∈ openImStrip 1, ∀ e : Fin 4 → ℤ,
      symbolRoot L k (PlaneWaveCalculus.periodShift L k q e) = symbolRoot L k q := by
    intro q _ e
    simp only [symbolRoot, hf.symbolSquare_periodic]
  have hSqPer : ∀ q ∈ openImStrip 1, ∀ e : Fin 4 → ℤ,
      PlaneWaves.symbolSquare L k (PlaneWaveCalculus.periodShift L k q e) =
        PlaneWaves.symbolSquare L k q := fun q _ e => hf.symbolSquare_periodic q e
  obtain ⟨FRs, FRb, -⟩ := hM 1 one_pos _ hRootPer
  obtain ⟨FDs, FDb, -⟩ := hM 1 one_pos _ hSqPer
  have hK : LoewnerLE (scalarQuotHom (colourEdges L k 0) 0)
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ) := by
    refine loewner_nonneg_of_matrixFacts hTransposeNorm hf hB₀ FRb FDb hκ ?_ (hact.K κ)
    intro b μ m hm
    have h := (FRb.scales_unique κ hs).1
    rw [LinearMap.comp_apply, h _ μ m hm, h b μ m hm, smul_smul, symbolRoot_mul_self hf hκ m]
  have hD : LoewnerLE (scalarQuotHom (colourVertices L k 0) 0)
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta κ) := by
    refine loewner_nonneg_of_matrixFacts hTransposeNorm hf hS₀ FRs FDs hκ ?_ (hact.Delta κ)
    intro l m hm
    have h := (FRs.scales_unique κ hs).1
    rw [LinearMap.comp_apply, h _ m hm, h l m hm, smul_smul, symbolRoot_mul_self hf hκ m]
  have hQ := hmaps.edgeAverage.finite_range
  have hR := hmaps.vertexAverage.finite_range
  have hQt := hops.edgeAverage_transpose
  have hRt := hops.vertexAverage_transpose
  have adjQ : IsAdjointQuotHom
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ)
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ) := by
    rw [edge_Qt_eq]
    exact isAdjoint_symbolHom_kernelTranspose hB₀ hBk
      (hsym.1 _ _ _ hB₀ hBk hBk _ _ 1 hQ.1 (hQ.2.2 1 one_pos) hQt.1 (hQt.2.2 1 one_pos))
      hreal.Q.2.1 hκ
  have adjR : IsAdjointQuotHom
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ)
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ) := by
    rw [vertex_Rt_eq]
    exact isAdjoint_symbolHom_kernelTranspose hS₀ hSk
      (hsym.1 _ _ _ hS₀ hSk hSk _ _ 1 hR.1 (hR.2.2 1 one_pos) hRt.1 (hRt.2.2 1 one_pos))
      hreal.R.2.1 hκ
  exact ⟨hK, hD, adjQ, adjR, quotHomAdjoint_eq hTransposeNorm hB₀ adjQ, quotHomAdjoint_eq hTransposeNorm hS₀ adjR⟩
end YangMills.Construction.Tower.RealPoints
end
