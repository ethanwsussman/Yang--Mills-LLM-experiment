import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorusProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.FreeInversesOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.FreePictureReadsOnASide
import YangMills.Construction.RunningCouplingSlope.RateOfASymbolOnAStrip
import YangMills.Construction.RunningCouplingSlope.RootsReadOnASide
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FreeInversesLocalProof
open Tower PeriodicOperators
open Tower.FreeStrip
open PeriodicOperators.StripSymbols (openStripInterior)
open LocalKernels.Periodisation (periodSide)
section Inverses
variable {I : PeriodicData} {J : Type}
private theorem periodicInverse_facts (hSS : StripSymbols.Claim) (hRt : DecayFromStripSymbol)
    (hI : IsPeriodic I) {T : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T) {υ : ℝ}
    (hυ : 0 < υ) (hf : SymbolSummableOn I I T (imStrip υ))
    (hinv : ∀ κ ∈ imStrip υ, IsInvertibleQuotHom (symbolHom I I T κ)) :
    IsPeriodicKernel I I (periodicInverse I T) ∧
      compKernel (periodicInverse I T) T = idKernel I ∧
      SymbolSummableOn I I (periodicInverse I T) (openStripInterior υ) ∧
      ∀ κ ∈ openStripInterior υ, symbolHom I I (periodicInverse I T) κ =
        quotHomInverse (symbolHom I I T κ) := by
  obtain ⟨C, -, hb⟩ := hRt I I hI hI T υ hυ hT.1 hf
  have hint := hSS.1 υ hυ
  have hsub : openStripInterior υ ⊆ imStrip υ := by
    rw [hint.1]
    exact hint.2.2.1
  have hdec := ((hSS.2.1 I I hI hI).1).decay υ hυ C T hT hb
  obtain ⟨-, h2, -, -, h5, -, h7, h8⟩ :=
    hSS.2.2.2 I hI υ hυ T hT hdec.1 hdec.2 fun κ hκ => hinv κ (hsub hκ)
  exact ⟨h2, h5, h7, h8⟩
private theorem readsKernel_inv (hRK : KernelMatricesOnSide) [Fintype J]
    [DecidableEq J] (hI : IsPeriodic I) {q : I.Carrier → J} {s : ℕ} (hs : 0 < s)
    (hq : IsPeriodicQuotient I q s) {T T' : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T)
    (hT' : IsPeriodicKernel I I T') (h : compKernel T' T = idKernel I) {M : Matrix J J ℂ}
    (hM : ReadsKernel q q s T M) : IsUnit M.det ∧ ReadsKernel q q s T' (M⁻¹ : Matrix J J ℂ) := by
  obtain ⟨hmul, hex, hid⟩ := hRK I I I hI hI hI q q q s hs hq hq hq
  obtain ⟨N, hN⟩ := hex T' hT'
  have h1 := hmul T' T N M hT' hT hN hM
  rw [h] at h1
  have h2 : (Matrix.of N : Matrix J J ℂ) * M = 1 := by
    ext a a'
    obtain ⟨i, rfl⟩ := hq.surjective a
    obtain ⟨i', rfl⟩ := hq.surjective a'
    have e1 := h1 i i'
    have e2 := hid i i'
    rw [← e2] at e1
    unfold compKernel at e1
    rw [tsum_fintype] at e1
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact e1
  have h3 : M⁻¹ = Matrix.of N := Matrix.inv_eq_left_inv h2
  refine ⟨Matrix.isUnit_det_of_left_inverse h2, fun i' i => ?_⟩
  show (M⁻¹ : Matrix J J ℂ) (q i') (q i) = _
  rw [h3]
  exact hN i' i
private theorem isLocalOnCells_inv (hSS : StripSymbols.Claim)
    (hRt : DecayFromStripSymbol) (hRK : KernelMatricesOnSide)
    {δ C K θ : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hLoc : ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
      ∀ w w' : ℝ, 0 < w → 0 < w' → (∀ i, I.weightOf i = w) → (∀ i, I'.weightOf i = w') →
      ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
        (q : I.Carrier → ι) (q' : I'.Carrier → ι') (c : ι → Vertex L n k k) (c' : ι' → Vertex L n k k),
        IsCellQuotient L n k I q c → IsCellQuotient L n k I' q' c' →
        ∀ (T : I'.Carrier → I.Carrier → ℂ) (C : ℝ), 0 < C → IsPeriodicKernel I I' T →
          SymbolBoundedOn I I' T (imStrip δ) C →
        ∀ M : Matrix ι' ι ℂ,
          (∀ i' i, M (q' i') (q i) = periodization I I' T (periodSide L n) i' i) →
          IsLocalOnCells c c' M (K * C * Real.sqrt (w / w')) θ fun _ => 1)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hs : 0 < periodSide L n)
    (hI : IsPeriodic I) {w : ℝ} (hw : 0 < w) (hwt : ∀ i, I.weightOf i = w)
    [Fintype J] [DecidableEq J] {q : I.Carrier → J} {c : J → Vertex L n k k}
    (hc : IsCellQuotient L n k I q c) {T : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T)
    (h : SymbolInvertibleOn I T (imStrip (2 * δ)) C) {M : Matrix J J ℂ}
    (hM : ReadsKernel q q (periodSide L n) T M) :
    IsUnit M.det ∧ IsLocalOnCells c c M⁻¹ (K * C) θ fun _ => 1 := by
  have h2δ : 0 < 2 * δ := by positivity
  obtain ⟨hper, hleft, hform, hsym⟩ :=
    periodicInverse_facts hSS hRt hI hT h2δ h.1 fun κ hκ => (h.2 κ hκ).1
  have hq : IsPeriodicQuotient I q (periodSide L n) := ⟨hc.surjective, hc.image_eq_iff⟩
  obtain ⟨hu, hr⟩ := readsKernel_inv hRK hI hs hq hT hper hleft hM
  refine ⟨hu, ?_⟩
  have hint := hSS.1 (2 * δ) h2δ
  have hsub : imStrip δ ⊆ openStripInterior (2 * δ) := by
    rw [hint.1]
    exact hint.2.2.2 δ hδ (by linarith)
  have hbound : SymbolBoundedOn I I (periodicInverse I T) (imStrip δ) C :=
    ⟨fun κ hκ => hform κ (hsub hκ), fun κ hκ => by
      rw [hsym κ (hsub hκ)]
      exact (h.2 κ ((hint.2.2.1) (hint.1 ▸ hsub hκ))).2⟩
  have h1 := hLoc L n k hL hn I I hI hI w w hw hw hwt hwt q q c c hc hc
    (periodicInverse I T) C hC hper hbound M⁻¹ hr
  have h2 : Real.sqrt (w / w) = 1 := by rw [div_self hw.ne', Real.sqrt_one]
  rwa [h2, mul_one] at h1
end Inverses
private theorem compKernel_eq_mul {A B D : Type} [Fintype B] (M : Matrix A B ℂ)
    (N : Matrix B D ℂ) : compKernel M N = M * N := by
  funext a d
  show ∑' b, M a b * N b d = _
  rw [tsum_fintype, Matrix.mul_apply]
section Flat
variable {L n k j : ℕ}
private theorem twoSourceBackground_zero : twoSourceBackground L n k 0 0 0 = trivialField L n k 0 := by
  funext b
  unfold twoSourceBackground PeriodicLattice.expTwist
  simp [Matrices.ComplexMatrix2.matExp]
private theorem normalizedMean_one (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) : normalizedMean (fun _ : Edge L n k j => (1 : Matrices.ComplexMatrix2)) c = 1 :=
  (hD L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
private theorem meanIterate_one (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : ∀ j, j ≤ k →
    meanIterate (trivialField L n k 0) j = fun _ => (1 : Matrices.ComplexMatrix2)
  | 0, _ => rfl
  | j + 1, hj => by
    have hjk : j < k := hj
    have ih := meanIterate_one hD hL hn j hjk.le
    have e : meanIterate (trivialField L n k 0) (j + 1) = fieldOfPositiveValues
        fun c => (1 : Matrices.ComplexMatrix2) * normalizedMean (meanIterate (trivialField L n k 0) j) c.1 := by
      show levelField _ (j + 1) = _
      rw [levelField, dif_pos hjk]
      rfl
    rw [e, ih]
    funext b
    unfold fieldOfPositiveValues
    split_ifs with h1 h2
    · simp [normalizedMean_one hD hL hn hjk h1]
    · simp [normalizedMean_one hD hL hn hjk h2]
    · rfl
private theorem complexBlockFieldAtLevel_trivial (hS : RescaledTrivialSteps)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) : ∀ j, j ≤ k →
    PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) = trivialField L n k j
  | 0, _ => rfl
  | j + 1, hj => by
    show PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.complexBlockFieldAtLevel j _) = _
    rw [complexBlockFieldAtLevel_trivial hS hL hn hk j (by omega)]
    exact ((hS L hL k hk n hn).2 j (by omega)).1
private theorem composedCubeAverage_trivial (hD : NormalizedMeanAtOne)
    (hS : RescaledTrivialSteps)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (l : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    ∀ j, j ≤ k → composedCubeAverage (quietPoint (trivialField L n k 0)) j l =
      iterAdjointCubeAverage L n k (trivialField L n k 0) j l
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := composedCubeAverage_trivial hD hS hL hn hk l j (by omega)
    show adjointCubeAverage (levelField _ j) (composedCubeAverage _ j l) =
      adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j _) (iterAdjointCubeAverage L n k _ j l)
    rw [ih, complexBlockFieldAtLevel_trivial hS hL hn hk j (by omega)]
    have := meanIterate_one hD hL hn (k := k) j (by omega)
    rw [show levelField (quietPoint (trivialField L n k 0)) j = _ from this]
private theorem meanKernelR_trivial (hD : NormalizedMeanAtOne)
    (hS : RescaledTrivialSteps)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    meanKernelR L n k (trivialField L n k 0) =
      (rescaledOperators L n k (trivialField L n k 0)).R := by
  unfold meanKernelR
  rw [show composedCubeAverage (quietPoint (trivialField L n k 0)) k =
    iterAdjointCubeAverage L n k (trivialField L n k 0) k from
      funext fun l => composedCubeAverage_trivial hD hS hL hn hk l k le_rfl]
  rfl
end Flat
section Products
variable {I I' I'' : PeriodicData}
private theorem exists_isDecayRate {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ δ, IsDecayRate I I' T δ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.exists_decayRate <;> assumption
private theorem isDecayRate_mono {T : I'.Carrier → I.Carrier → ℂ} {δ δ' : ℝ} (h : IsDecayRate I I' T δ)
    (h0 : 0 < δ') (hle : δ' ≤ δ) : IsDecayRate I I' T δ' := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.decayRate_of_le <;> assumption
private theorem isPeriodicKernel_comp (hP : CompClaim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) :
    IsPeriodicKernel I'' I' (compKernel T S) := by
  obtain ⟨δ, hδ⟩ := exists_isDecayRate hT
  obtain ⟨δ', hδ'⟩ := exists_isDecayRate hS
  have h0 : 0 < min δ δ' := lt_min hδ.1 hδ'.1
  exact (hP I I' I'' hI hI' hI'' T S (min δ δ') hT (isDecayRate_mono hδ h0 (min_le_left _ _)) hS
    (isDecayRate_mono hδ' h0 (min_le_right _ _))).comp_periodic.2
abbrev _root_.YangMills.SharedProofs.p12760 := @isPeriodicKernel_comp
end Products
open Tower.FreeResolvents in
theorem freeInversesLocal (hLM : BoundedSymbolLocalMatrix) (hRt : DecayFromStripSymbol)
    (hCR : CellQuotientsOfTower) (hRoots : ResolventRootsPeriodize)
    (hRK : KernelMatricesOnSide) (hFP : FreeOperatorsPeriodizeOnTorus)
    (hStrip : FreeStripEstimate) (hSS : StripSymbols.Claim)
    (hIS : TowerIndexSets.Claim) (hFG : FreeResolventRoots)
    (hFO : FreeOperators.FreeOperatorsArePeriodic) (hPr : CompClaim)
    (hSt : RescaledTrivialSteps)
    (hDer : NormalizedMeanAtOne) :
    FreeInversesLocal := by
  obtain ⟨δ, hδ, C, hC1, hA⟩ := hStrip
  have hδ0 : 0 < δ := hδ.1
  have hC : 0 < C := by linarith
  obtain ⟨K, θ, hK, hθ, hLoc⟩ := hLM δ hδ0
  intro L hL
  refine ⟨K * C, θ, by positivity, hθ, fun k hk => ⟨0, fun n _ hn => ?_⟩⟩
  intro _ _ _ _ _ _ _ _
  have hs : 0 < periodSide L n := by
    have : 0 < L := by have := hL.2; omega
    unfold LocalKernels.Periodisation.periodSide
    positivity
  obtain ⟨cS, cB, -, cTS, cTB⟩ := hCR L n k hL hn
  have rS : IsPeriodicQuotient (colourVertices L k 0) (colouredVertexProj L n k 0) (periodSide L n) :=
    ⟨cS.surjective, cS.image_eq_iff⟩
  have rB : IsPeriodicQuotient (colourEdges L k 0) (colouredEdgeProj L n k 0) (periodSide L n) :=
    ⟨cB.surjective, cB.image_eq_iff⟩
  have rTS : IsPeriodicQuotient (colourVertices L k k) (colouredVertexProj L n k k) (periodSide L n) :=
    ⟨cTS.surjective, cTS.image_eq_iff⟩
  have rTB : IsPeriodicQuotient (colourEdges L k k) (colouredEdgeProj L n k k) (periodSide L n) :=
    ⟨cTB.surjective, cTB.image_eq_iff⟩
  obtain ⟨pS, pB, -⟩ := hIS L hL k 0 (Nat.zero_le k)
  obtain ⟨pTS, pTB, -⟩ := hIS L hL k k le_rfl
  have FP := hFP L n k hL hn hk
  obtain ⟨hRb, hRs⟩ := hRoots L n k hL hn hk
  have hAs := hA L hL k hk
  have hI := hAs.2 0 (Set.left_mem_Icc.2 zero_le_one) 0 (Set.left_mem_Icc.2 zero_le_one)
  obtain ⟨-, -, -, hGb, hGs, -, -⟩ := hFG L hL k hk
  have hexp : (-(1 / 2) : ℝ) ∈ resolventExponents := by simp [resolventExponents]
  have perB : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0)
      (edgeResolventSqrt L k) := hGb.periodic _ hexp
  have perG : IsPeriodicKernel (colourVertices L k 0) (colourVertices L k 0)
      (vertexResolventSqrt L k) := hGs.periodic _ hexp
  have hw0 : ∀ j, 0 < meshAt L k j ^ 4 := fun j => by
    have : 0 < L := by have := hL.2; omega
    have : 0 < meshAt L k j := zpow_pos (by exact_mod_cast this) _
    positivity
  have eX : addScalar (edges L k) 0 (edgeOpXi L k) = (trivialRescaledOperators L k).Xi := by
    funext ι' ι
    simp [addScalar, edgeOpXi]
  have eY : addScalar (vertices L k) 0 (vertexOpY L k) = (trivialRescaledOperators L k).Y := by
    funext ι' ι
    simp [addScalar, vertexOpY]
  have hXr : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k 0)
      (colouredEdgeProj L n k 0) (colouredEdgeProj L n k 0) (periodSide L n)
      (addScalar (edges L k) 0 (edgeOpXi L k))
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi) := by
    rw [eX]
    exact FP.Xi
  have hYr : ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k 0)
      (colouredVertexProj L n k 0) (colouredVertexProj L n k 0) (periodSide L n)
      (addScalar (vertices L k) 0 (vertexOpY L k))
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Y) := by
    rw [eY]
    exact FP.Y
  have perX := hI.edge_inverse.periodic
  have perY := hI.vertex_inverse.periodic
  have h2δ : 0 < 2 * δ := by positivity
  have mBB := (hRK _ _ _ pB pB pB _ _ _ _ hs rB rB rB).1
  have mSS := (hRK _ _ _ pS pS pS _ _ _ _ hs rS rS rS).1
  have perBX := isPeriodicKernel_comp hPr pB pB pB perB perX
  have perBXB := isPeriodicKernel_comp hPr pB pB pB perBX perB
  have rXi : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k 0)
      (colouredEdgeProj L n k 0) (colouredEdgeProj L n k 0) (periodSide L n)
      (compKernel (compKernel (edgeResolventSqrt L k)
        (addScalar (edges L k) 0 (edgeOpXi L k))) (edgeResolventSqrt L k))
      (xiConjugated L n k 0 0 0) := by
    have e : xiConjugated L n k 0 0 0 = compKernel (compKernel (periodicEdgeResolventSqrt L n k)
        (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi))
        (periodicEdgeResolventSqrt L n k) := by
      unfold xiConjugated
      rw [twoSourceBackground_zero, compKernel_eq_mul, compKernel_eq_mul]
    rw [e]
    exact mBB _ _ _ _ perBX perB (mBB _ _ _ _ perB perX hRb hXr) hRb
  obtain ⟨u1, l1⟩ := isLocalOnCells_inv hSS hRt hRK hδ0 hC hLoc hL hn hs pB (hw0 0) (fun _ => rfl) cB
    perBXB hI.edge_add.2.2 rXi
  have perGY := isPeriodicKernel_comp hPr pS pS pS perG perY
  have perGYG := isPeriodicKernel_comp hPr pS pS pS perGY perG
  have rY : ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k 0)
      (colouredVertexProj L n k 0) (colouredVertexProj L n k 0) (periodSide L n)
      (compKernel (compKernel (vertexResolventSqrt L k)
        (addScalar (vertices L k) 0 (vertexOpY L k))) (vertexResolventSqrt L k))
      (yConjugated L n k 0 0 0) := by
    have e : yConjugated L n k 0 0 0 = compKernel (compKernel (periodicVertexResolventSqrt L n k)
        (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Y))
        (periodicVertexResolventSqrt L n k) := by
      unfold yConjugated
      rw [twoSourceBackground_zero, compKernel_eq_mul, compKernel_eq_mul]
    rw [e]
    exact mSS _ _ _ _ perGY perG (mSS _ _ _ _ perG perY hRs hYr) hRs
  obtain ⟨u2, l2⟩ := isLocalOnCells_inv hSS hRt hRK hδ0 hC hLoc hL hn hs pS (hw0 0) (fun _ => rfl) cS
    perGYG hI.vertex_add.2.2 rY
  obtain ⟨perXi, leftXi, -, -⟩ := periodicInverse_facts hSS hRt pB perX h2δ
    (fun κ hκ => (hI.edge_inverse.symbol κ hκ).2.1) fun κ hκ => by
      rw [(hI.edge_inverse.symbol κ hκ).2.2]
      exact hI.edge_inverse.matrix_invertible κ hκ
  obtain ⟨perYi, leftYi, -, -⟩ := periodicInverse_facts hSS hRt pS perY h2δ
    (fun κ hκ => (hI.vertex_inverse.symbol κ hκ).2.1) fun κ hκ => by
      rw [(hI.vertex_inverse.symbol κ hκ).2.2]
      exact hI.vertex_inverse.matrix_invertible κ hκ
  obtain ⟨-, rXinv⟩ := readsKernel_inv hRK pB hs rB perX perXi leftXi hXr
  obtain ⟨-, rYinv⟩ := readsKernel_inv hRK pS hs rS perY perYi leftYi hYr
  have perQ : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q :=
    ((hFO.2 L hL k hk).1.edgeAverage).finite_range.1
  have perR : IsPeriodicKernel (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R :=
    ((hFO.2 L hL k hk).1.vertexAverage).finite_range.1
  have perQt : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt :=
    ((hFO.2 L hL k hk).2.edgeAverage_transpose).1
  have perRt : IsPeriodicKernel (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt :=
    ((hFO.2 L hL k hk).2.vertexAverage_transpose).1
  have perQX := isPeriodicKernel_comp hPr pB pTB pB perQ perXi
  have perQXQ := isPeriodicKernel_comp hPr pB pTB pTB perQX perQt
  have perRY := isPeriodicKernel_comp hPr pS pTS pS perR perYi
  have perRYR := isPeriodicKernel_comp hPr pS pTS pTS perRY perRt
  have rC : ReadsKernel (I := colourEdges L k k) (I' := colourEdges L k k)
      (colouredEdgeProj L n k k) (colouredEdgeProj L n k k) (periodSide L n)
      (compKernel (compKernel (trivialRescaledOperators L k).Q
        (periodicInverse (edges L k) (addScalar (edges L k) 0 (edgeOpXi L k))))
        (trivialRescaledOperators L k).Qt)
      (topCovariance (trivialField L n k 0)) := by
    have e : topCovariance (trivialField L n k 0) = compKernel (compKernel
        (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Q)
        (xiInv (trivialField L n k 0)))
        (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Qt) := by
      unfold topCovariance
      rw [compKernel_eq_mul, compKernel_eq_mul]
    rw [e]
    exact (hRK _ _ _ pB pTB pTB _ _ _ _ hs rB rTB rTB).1 _ _ _ _ perQX perQt
      ((hRK _ _ _ pB pTB pB _ _ _ _ hs rB rTB rB).1 _ _ _ _ perQ perXi FP.Q rXinv) FP.Qt
  obtain ⟨u3, l3⟩ := isLocalOnCells_inv hSS hRt hRK hδ0 hC hLoc hL hn hs pTB (hw0 k) (fun _ => rfl) cTB
    perQXQ hI.edge_avg.2.2 rC
  have rD : ReadsKernel (I := colourVertices L k k) (I' := colourVertices L k k)
      (colouredVertexProj L n k k) (colouredVertexProj L n k k) (periodSide L n)
      (compKernel (compKernel (trivialRescaledOperators L k).R
        (periodicInverse (vertices L k) (addScalar (vertices L k) 0 (vertexOpY L k))))
        (trivialRescaledOperators L k).Rt)
      (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).R *
        yInv (trivialField L n k 0) *
        Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Rt) := by
    rw [← compKernel_eq_mul, ← compKernel_eq_mul]
    exact (hRK _ _ _ pS pTS pTS _ _ _ _ hs rS rTS rTS).1 _ _ _ _ perRY perRt
      ((hRK _ _ _ pS pTS pS _ _ _ _ hs rS rTS rS).1 _ _ _ _ perR perYi FP.R rYinv) FP.Rt
  obtain ⟨u4, l4⟩ := isLocalOnCells_inv hSS hRt hRK hδ0 hC hLoc hL hn hs pTS (hw0 k) (fun _ => rfl) cTS
    perRYR hI.vertex_avg.2.2 rD
  rw [meanKernelR_trivial hDer hSt hL hn hk]
  exact ⟨u1, l1, u2, l2, u3, l3, u4, l4, u4, l4⟩
end YangMills.Construction.RunningCouplingSlope.FreeInversesLocalProof
end
