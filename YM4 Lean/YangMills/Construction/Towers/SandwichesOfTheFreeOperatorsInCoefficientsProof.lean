import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.FreeSandwiches
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open FreeResolvents
open Coercivity
open RealFrequencyFamily
open PlaneWaveCalculus (SymbolFormulas WeightRelations posEdgeAt topEdgeComponent topVertexElement)
open InfiniteLattice (AmbientSpace)
open Matrices
variable {L k : ℕ}
theorem wInner_self_eq {J : Type} (w : J → ℝ) (h : J → ℂ) :
    wInner w h h = ((∑' i, w i * ‖h i‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.wInner_self_eq_tsum <;> assumption
theorem conj_wInner {J : Type} (w : J → ℝ) (f g : J → ℂ) :
    conj (wInner w f g) = wInner w g f := by
  simp only [wInner, wPairing]
  rw [Complex.conj_tsum]
  refine tsum_congr fun i => ?_
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring
theorem wInner_sandwich_symm {J J' : Type} (w : J → ℝ) (w' : J' → ℝ) {A : (J → ℂ) → J' → ℂ}
    {B : (J' → ℂ) → J → ℂ} {G : (J → ℂ) → J → ℂ}
    (adj : ∀ f g, wInner w' g (A f) = wInner w (B g) f)
    (hG : ∀ f g, wInner w (G f) g = wInner w f (G g)) (z z' : J' → ℂ) :
    wInner w' (A (G (B z))) z' = wInner w' z (A (G (B z'))) := by
  rw [← conj_wInner w' z', adj, conj_wInner, hG, ← adj]
theorem toComplexVec_re {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    toComplexVec (fun μ => (κ μ).re) = κ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.toComplexVec_re <;> assumption
theorem mem_imStrip_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) {δ : ℝ} (hδ : 0 < δ) :
    κ ∈ strictImStrip δ := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.mem_imStrip_of_real <;> assumption
theorem shiftedFreq_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) :
    PlaneWaves.shiftedFreq κ m =
      toComplexVec (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.shiftedFreq_of_real <;> assumption
theorem symbolHom_kernelTranspose_adjoint {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (facts : SymbolProperties I I' I'' T S 1) (hreal : ∀ ι' ι, (T ι' ι).im = 0)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ) :
    wInner (I'.quotWeight 1) g (symbolHom I I' T κ f) =
      wInner (I.quotWeight 1) (symbolHom I' I (kernelTranspose I I' T) κ g) f := by
  have := hI.finite_quot
  have := hI'.finite_quot
  have e₁ : symbolHom I I' T κ f = applyKernel (quotSymbol I I' T κ) f :=
    linearMapOfEntries_eq_applyKernel _ _
  have e₂ : symbolHom I' I (kernelTranspose I I' T) κ g =
      applyKernel (quotSymbol I' I (kernelTranspose I I' T) κ) g :=
    linearMapOfEntries_eq_applyKernel _ _
  rw [e₁, e₂, (facts.quotSymbol_kernelTranspose κ (mem_imStrip_of_real hκ one_pos)).2]
  have h := facts.wInner_quotTranspose hreal (fun μ => (κ μ).re) f g
  rw [toComplexVec_re hκ] at h
  exact h.symm
theorem symbolHom_selfAdjoint_of_transpose_eq (hSym : Symbols.Claim) {I : PeriodicData}
    (hI : IsPeriodic I) {T : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T)
    (hreal : ∀ ι' ι, (T ι' ι).im = 0) (hown : kernelTranspose I I T = T) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) (f g : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) (symbolHom I I T κ f) g =
      wInner (I.quotWeight 1) f (symbolHom I I T κ g) := by
  have : Finite I.UnitQuot := hI.finite_quot
  obtain ⟨C, δ, hC, hδ, hb⟩ := hT.2
  have rate : IsDecayRate I I T δ := ⟨hδ, C, hC, hb⟩
  have F := hSym.1 I I I hI hI hI T T δ hT rate hT rate
  have e := (F.quotSymbol_kernelTranspose κ (mem_imStrip_of_real hκ hδ)).2
  rw [hown] at e
  have a := F.wInner_quotTranspose hreal (fun μ => (κ μ).re) g f
  rw [toComplexVec_re hκ, ← e] at a
  have ap : ∀ h, symbolHom I I T κ h = applyKernel (quotSymbol I I T κ) h :=
    fun h => linearMapOfEntries_eq_applyKernel _ h
  rw [ap, ap]
  exact a
theorem exists_selfAdjoint_sqrt_resolvent (hS : StripSymbols.Claim)
    (hSym : Symbols.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {Mult : ℝ → (Fin 4 → ℂ) → QuotHom I I → Prop} {M : ℝ → (Fin 4 → ℂ) → QuotHom I I}
    {P : I.Carrier → I.Carrier → ℂ} (hF : PowerMatrixFacts I Mult M P) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) :
    ∃ N : QuotHom I I, Mult (-(1 / 2)) κ N ∧
      (∀ f g, wInner (I.quotWeight 1) (N f) g =
        wInner (I.quotWeight 1) f (N g)) ∧
      symbolHom I I (periodicInverse I P) κ = N.comp N := by
  have : Finite I.UnitQuot := hI.finite_quot
  obtain ⟨hi1, -, hi3, hi4⟩ := hS.1 (1 / 8) (by norm_num)
  obtain ⟨-, hfacts, hker, -⟩ := hS.2.1 I I hI hI
  have hsub : openStripInterior (1 / 8) ⊆ imStrip (1 / 8) := by
    rw [hi1]
    exact hi3
  have KT := fun σ (hσ : σ ∈ resolventExponents) => hker (1 / 8) (by norm_num) (M σ)
    (hF.holomorphicOn σ hσ)
    (fun υ' h0 h1 e =>
      let ⟨B, hB⟩ := hF.boundedOn σ hσ e
      ⟨B, fun κ hκ => hB κ (by rw [hi1]; exact hi4 υ' h0 h1 hκ)⟩)
    (fun e κ hκ => hF.quasiPeriodic σ hσ e κ (hsub hκ))
  have mem1 : (-(1 / 2) : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  obtain ⟨hinc, -, -, pN, fN, sN⟩ := KT _ mem1
  have hκ' := hinc hκ
  refine ⟨M (-(1 / 2)) κ, (hF.scales_unique _ mem1 κ (hsub hκ')).1, fun f g => ?_, ?_⟩
  · rw [← sN κ hκ']
    exact symbolHom_selfAdjoint_of_transpose_eq hSym hI pN (hF.im_eq_zero _ mem1)
      (hF.transpose_eq _ mem1) hκ f g
  · rw [hF.inverse_eq, ← hF.invSqrt_comp_invSqrt.2, ← sN κ hκ']
    exact ((hfacts _ κ pN (fN κ hκ')).comp I hI _ pN (fN κ hκ')).2.2.2
theorem symbolSquare_shiftedFreq_real (hf : SymbolFormulas L k) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) :
    PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) =
        ((symbolSquares L k κ m : ℝ) : ℂ) ∧
      0 ≤ symbolSquares L k κ m := by
  have h := hf.symbolSquare_ofReal (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ))
  rw [← shiftedFreq_of_real hκ m] at h
  have h' : PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) =
      ((∑ ν, ‖PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) ν‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]
    push_cast
    rfl
  have e : symbolSquares L k κ m =
      ∑ ν, ‖PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) ν‖ ^ 2 := by
    simp only [symbolSquares]
    rw [h', Complex.ofReal_re]
  refine ⟨by rw [e, h'], ?_⟩
  rw [e]
  exact Finset.sum_nonneg fun _ _ => by positivity
theorem norm_shiftedSymbolPow_sq (hf : SymbolFormulas L k) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) :
    ‖shiftedSymbolPow L k (-(1 / 2)) (PlaneWaves.shiftedFreq κ m)‖ ^ 2 =
      (symbolSquares L k κ m + 1)⁻¹ := by
  obtain ⟨e, h0⟩ := symbolSquare_shiftedFreq_real hf hκ m
  have hz : PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m) + 1 =
      ((symbolSquares L k κ m + 1 : ℝ) : ℂ) := by
    rw [e]
    push_cast
    rfl
  have hpos : 0 < symbolSquares L k κ m + 1 := by linarith
  have hn : ‖((symbolSquares L k κ m + 1 : ℝ) : ℂ)‖ = symbolSquares L k κ m + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hexp : ∀ φ : ℝ, ‖Complex.exp (Complex.I * ((-(1 / 2) : ℝ) : ℂ) * (φ : ℂ))‖ = 1 :=
    fun φ => by
      have : Complex.I * ((-(1 / 2) : ℝ) : ℂ) * (φ : ℂ) =
          (((-(1 / 2) : ℝ) * φ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
  simp only [shiftedSymbolPow, principalRpow]
  rw [hz, norm_mul, hexp, mul_one, Complex.norm_real, hn, Real.norm_eq_abs, sq_abs,
    ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num
  exact Real.rpow_neg_one _
theorem norm_exp_halfPhase (η t : ℝ) :
    ‖Complex.exp (Complex.I * (1 - (η : ℂ)) * (t : ℂ) / 2)‖ = 1 := by
  have : Complex.I * (1 - (η : ℂ)) * (t : ℂ) / 2 = (((1 - η) * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
theorem neg_toComplexVec_apply (x : AmbientSpace) (μ : Fin 4) :
    (-toComplexVec x) μ = ((-(x μ) : ℝ) : ℂ) := by
  simp [toComplexVec]
theorem norm_vertexWeight_neg (hr : WeightRelations L k) (x : AmbientSpace) :
    ‖PlaneWaves.vertexWeight L k (-toComplexVec x)‖ =
      ‖PlaneWaves.vertexWeight L k (toComplexVec x)‖ := by
  rw [hr.vertexWeight_neg]
theorem norm_edgeWeight_neg (hf : SymbolFormulas L k) (hr : WeightRelations L k)
    (x : AmbientSpace) (μ : Fin 4) :
    ‖PlaneWaves.edgeWeight L k (-toComplexVec x) μ‖ =
      ‖PlaneWaves.edgeWeight L k (toComplexVec x) μ‖ := by
  simp only [PlaneWaves.edgeWeight, norm_mul]
  rw [norm_vertexWeight_neg hr, neg_toComplexVec_apply, norm_exp_halfPhase]
  have e : (toComplexVec x) μ = ((x μ : ℝ) : ℂ) := rfl
  rw [e, norm_exp_halfPhase]
  have e' : (((-(x μ) : ℝ) : ℂ)) = -((x μ : ℝ) : ℂ) := by push_cast; rfl
  rw [e', hf.dirichletSum_neg]
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul (c : ℂ) (X : ComplexMatrix2) (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by
  by_cases hX : X ∈ ComplexMatrix2.traceless
  · have hc : c • X ∈ ComplexMatrix2.traceless := ComplexMatrix2.traceless.smul_mem c hX
    unfold pauliCoeff
    rw [dif_pos hc, dif_pos hX]
    have e : (⟨c • X, hc⟩ : ComplexMatrix2.traceless) = c • ⟨X, hX⟩ := rfl
    rw [e, map_smul]
    rfl
  · by_cases h0 : c = 0
    · subst h0
      have e := pauliCoeff_sum_smul 0 a
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e
      rw [zero_smul, e, zero_mul]
    · have hc : c • X ∉ ComplexMatrix2.traceless :=
        fun h => hX ((Submodule.smul_mem_iff _ h0).1 h)
      simp only [pauliCoeff, dif_neg hX, dif_neg hc, mul_zero]
theorem meshAt_self : meshAt L k k = 1 := by simp [meshAt]
theorem quotWeight_eq_of_const {I : PeriodicData} {w : ℝ} (hw : ∀ ι, I.weightOf ι = w)
    (c : I.UnitQuot) : I.quotWeight 1 c = w := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.quotWeight_of_const <;> assumption
theorem eq_of_mkQuot_eq (I : PeriodicData) {β : Type*} (φ : I.Carrier → β)
    (h : ∀ n ι, φ (I.translate n ι) = φ ι) {ι ι' : I.Carrier}
    (e : I.mkQuot 1 ι = I.mkQuot 1 ι') : φ ι = φ ι' :=
  congrArg (Quot.lift φ (by
    rintro a b ⟨n, rfl⟩
    exact (h _ a).symm)) e
theorem mkQuot_translate (I : PeriodicData) (n : Fin 4 → ℤ) (ι : I.Carrier) :
    I.mkQuot 1 (I.translate n ι) = I.mkQuot 1 ι :=
  (Quot.sound ⟨n, by simp⟩).symm
theorem exists_eq_posEdgeAt {j : ℕ} (b : PosEdge L k j) :
    ∃ μ, b = posEdgeAt L k j b.1.initial μ := by
  obtain ⟨μ, h⟩ := b.2
  refine ⟨μ, Subtype.ext (InfiniteLattice.Link.ext rfl ?_)⟩
  show b.1.terminal = b.1.initial + _
  rw [← h]
  abel
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ μ' : Fin 4}
    (e : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a μ') : μ = μ' := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
section TopLevel
variable (ht : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hk : 1 ≤ k)
include ht hL hk
theorem topVertexInner_self (g : (colourVertices L k k).UnitQuot → ℂ) :
    topVertexInner L k g g = ((∑ a, ‖topVertexCoeff L k g a‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.top_vertex_wInner_self <;> assumption
theorem topEdgeInner_self (z : (colourEdges L k k).UnitQuot → ℂ) :
    topEdgeInner L k z z = ((∑ a, ∑ μ, ‖topEdgeCoeff L k z a μ‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.top_edge_wInner_self <;> assumption
end TopLevel
theorem trivial_Qt_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Qt =
      kernelTranspose (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q :=
  rfl
theorem trivial_Rt_eq (L k : ℕ) :
    (trivialRescaledOperators L k).Rt =
      kernelTranspose (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R :=
  rfl
theorem sandwichFacts_holds (hforms : FreeSymbolCoefficients.FreeSymbolForms)
    (hplane : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hG : FreeResolventRoots)
    (hfree : FreeOperators.FreeOperatorsArePeriodic) (hidx : TowerIndexSets.Claim)
    (hsym : Symbols.Claim) (hS : StripSymbols.Claim)
    (ht : TowerTranslations.Claim) : SandwichFacts := by
  intro L hL k hk κ hκ
  obtain ⟨-, -, -, -, hf, -, hav, hrel, hreal, -⟩ := hplane L hL k hk
  have forms := hforms L hL k hk κ hκ
  obtain ⟨-, -, -, fB, fS, -, -⟩ := hG L hL k hk
  obtain ⟨hmaps, hops⟩ := hfree.2 L hL k hk
  have hS₀ := (hidx L hL k 0 (Nat.zero_le k)).1
  have hB₀ := (hidx L hL k 0 (Nat.zero_le k)).2.1
  have hSk := (hidx L hL k k le_rfl).1
  have hBk := (hidx L hL k k le_rfl).2.1
  obtain ⟨NB, mNB, hNB, eNB⟩ := exists_selfAdjoint_sqrt_resolvent hS hsym hB₀ fB hκ
  obtain ⟨NS, mNS, hNS, eNS⟩ := exists_selfAdjoint_sqrt_resolvent hS hsym hS₀ fS hκ
  have hQ := hmaps.edgeAverage.finite_range
  have hR := hmaps.vertexAverage.finite_range
  have hQt := hops.edgeAverage_transpose
  have hRt := hops.vertexAverage_transpose
  have adjQ : ∀ f g, topEdgeInner L k g
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ f) =
    FreeSymbolCoefficients.edgeInner L k
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ g)
        f := by
    intro f g
    rw [trivial_Qt_eq]
    exact symbolHom_kernelTranspose_adjoint hB₀ hBk
      (hsym.1 _ _ _ hB₀ hBk hBk _ _ 1 hQ.1 (hQ.2.2 1 one_pos) hQt.1 (hQt.2.2 1 one_pos))
      hreal.Q.2.1 hκ f g
  have adjR : ∀ f g, topVertexInner L k g
      (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R
        κ f) =
    FreeSymbolCoefficients.vertexInner L k
      (symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt
        κ g) f := by
    intro f g
    rw [trivial_Rt_eq]
    exact symbolHom_kernelTranspose_adjoint hS₀ hSk
      (hsym.1 _ _ _ hS₀ hSk hSk _ _ 1 hR.1 (hR.2.2 1 one_pos) hRt.1 (hRt.2.2 1 one_pos))
      hreal.R.2.1 hκ f g
  have hermG : ∀ f g, FreeSymbolCoefficients.edgeInner L k
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) κ f) g =
    FreeSymbolCoefficients.edgeInner L k f
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) κ g) := by
    intro f g
    have e : ∀ h, symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) κ h =
        NB (NB h) := fun h => by
      rw [edgeResolvent, eNB]
      rfl
    rw [e, e]
    exact (hNB _ _).trans (hNB _ _)
  have hermg : ∀ f g, FreeSymbolCoefficients.vertexInner L k
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) κ f) g =
    FreeSymbolCoefficients.vertexInner L k f
      (symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) κ g) := by
    intro f g
    have e : ∀ h,
        symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) κ h =
          NS (NS h) := fun h => by
      rw [vertexResolvent, eNS]
      rfl
    rw [e, e]
    exact (hNS _ _).trans (hNS _ _)
  refine
    { edge_adjoint := adjQ
      vertex_adjoint := adjR
      edge_hermitian := wInner_sandwich_symm _ _ adjQ hermG
      vertex_hermitian := wInner_sandwich_symm _ _ adjR hermg
      edge_norm := topEdgeInner_self ht hL hk
      vertex_norm := topVertexInner_self ht hL hk
      edge_form := fun z => ?_
      vertex_form := fun g => ?_ }
  · set b := symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt
      κ z with hb
    have e : topEdgeInner L k z (edgeSandwich L k κ z) =
        FreeSymbolCoefficients.edgeInner L k (NB b) (NB b) := by
      have e₁ : symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) κ b =
          NB (NB b) := by
        rw [edgeResolvent, eNB]
        rfl
      have e₂ : edgeSandwich L k κ z =
          symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ
            (NB (NB b)) := by
        rw [← e₁]
        rfl
      rw [e₂, adjQ, ← hb]
      exact (hNB _ _).symm
    have term : ∀ a, ∀ m ∈ PlaneWaves.freqBox L k, ∀ μ,
        ‖FreeSymbolCoefficients.edgeColourCoeffs L k (NB b) a m μ‖ ^ 2 =
          ‖edgeWeights L k κ m μ‖ ^ 2 * (symbolSquares L k κ m + 1)⁻¹ *
            ‖topEdgeCoeff L k z a μ‖ ^ 2 := by
      intro a m hm μ
      have c₁ : PlaneWaves.edgeFourierCoeff L k (NB b) μ m =
          shiftedSymbolPow L k (-(1 / 2)) (PlaneWaves.shiftedFreq κ m) •
            PlaneWaves.edgeFourierCoeff L k b μ m := mNB b μ m hm
      have c₂ : PlaneWaves.edgeFourierCoeff L k b μ m =
          PlaneWaves.edgeWeight L k (-PlaneWaves.shiftedFreq κ m) μ • topEdgeComponent L k z μ :=
        hav.Qt κ z μ m hm
      have c₃ : ‖PlaneWaves.edgeWeight L k (-PlaneWaves.shiftedFreq κ m) μ‖ =
          ‖edgeWeights L k κ m μ‖ := by
        simp only [edgeWeights]
        rw [shiftedFreq_of_real hκ m]
        exact norm_edgeWeight_neg hf hrel _ μ
      simp only [FreeSymbolCoefficients.edgeColourCoeffs, topEdgeCoeff]
      rw [c₁, c₂, pauliCoeff_smul, pauliCoeff_smul, norm_mul, norm_mul, mul_pow, mul_pow, c₃,
        norm_shiftedSymbolPow_sq hf hκ m]
      ring
    rw [e, forms.edge_norm_sq]
    refine congrArg (fun x : ℝ => (x : ℂ)) (Finset.sum_congr rfl fun a _ => ?_)
    simp only [bondResolventWeight, bondNormSq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun m hm => term a m hm μ
  · set l := symbolHom (colourVertices L k k) (colourVertices L k 0)
      (trivialRescaledOperators L k).Rt κ g with hl
    have e : topVertexInner L k g (vertexSandwich L k κ g) =
        FreeSymbolCoefficients.vertexInner L k (NS l) (NS l) := by
      have e₁ : symbolHom (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) κ l =
          NS (NS l) := by
        rw [vertexResolvent, eNS]
        rfl
      have e₂ : vertexSandwich L k κ g =
          symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R
            κ (NS (NS l)) := by
        rw [← e₁]
        rfl
      rw [e₂, adjR, ← hl]
      exact (hNS _ _).symm
    have term : ∀ a, ∀ m ∈ PlaneWaves.freqBox L k,
        ‖FreeSymbolCoefficients.vertexColourCoeffs L k (NS l) a m‖ ^ 2 =
          vertexWeights L k κ m ^ 2 * (symbolSquares L k κ m + 1)⁻¹ *
            ‖topVertexCoeff L k g a‖ ^ 2 := by
      intro a m hm
      have c₁ : PlaneWaves.vertexFourierCoeff L k (NS l) m =
          shiftedSymbolPow L k (-(1 / 2)) (PlaneWaves.shiftedFreq κ m) •
            PlaneWaves.vertexFourierCoeff L k l m := mNS l m hm
      have c₂ : PlaneWaves.vertexFourierCoeff L k l m =
          PlaneWaves.vertexWeight L k (-PlaneWaves.shiftedFreq κ m) • topVertexElement L k g :=
        hav.Rt κ g m hm
      have c₃ : ‖PlaneWaves.vertexWeight L k (-PlaneWaves.shiftedFreq κ m)‖ ^ 2 =
          vertexWeights L k κ m ^ 2 := by
        simp only [vertexWeights]
        rw [shiftedFreq_of_real hκ m, norm_vertexWeight_neg hrel]
        generalize hx : (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) = x
        have him := hrel.vertexWeight_im x
        have hz : PlaneWaves.vertexWeight L k (toComplexVec x) =
            (((PlaneWaves.vertexWeight L k (toComplexVec x)).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simpa using him)
        rw [hz, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, sq_abs]
      simp only [FreeSymbolCoefficients.vertexColourCoeffs, topVertexCoeff]
      rw [c₁, c₂, pauliCoeff_smul, pauliCoeff_smul, norm_mul, norm_mul, mul_pow, mul_pow, c₃,
        norm_shiftedSymbolPow_sq hf hκ m]
      ring
    rw [e, forms.vertex_norm_sq]
    refine congrArg (fun x : ℝ => (x : ℂ)) (Finset.sum_congr rfl fun a _ => ?_)
    simp only [siteResolventWeight, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => term a m hm
end YangMills.Construction.Tower.FreeSandwiches
end
