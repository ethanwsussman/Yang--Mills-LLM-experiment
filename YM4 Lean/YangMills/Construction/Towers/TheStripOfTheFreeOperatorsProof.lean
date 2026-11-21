import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.SandwichesOfARootedPair
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbols
import YangMills.Construction.Towers.BoundsOfTheSandwichesOfTheFreeOperators
import YangMills.Construction.Towers.BoundsOfTheSymbolsOfTheAverages
import YangMills.Construction.Towers.FreeOperatorsAtTheRealPoints
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import YangMills.Construction.Towers.TheStripOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FreeStrip
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.PeriodicOperators.RootedSandwiches
open YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.Tower.SandwichBounds (sandwichConstant)
theorem symbolHom_comp_at (q2 : StripSymbols.Claim) {I I' I'' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  ((q2.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS
theorem symbolHom_id_at (q2 : StripSymbols.Claim) (hn : HomNorm.Claim)
    {I : PeriodicData} (hI : IsPeriodic I) (κ : Fin 4 → ℂ) :
    SymbolSummableAt I I (idKernel I) κ ∧
      symbolHom I I (idKernel I) κ = LinearMap.id := by
  have h := (q2.2.1 I I hI hI).1.identity κ
  refine ⟨h.1, ?_⟩
  have hu := (hn I I hI hI).2.2.2.2.2.2.2.1.1
  have e : symbolHom I I (idKernel I) κ =
      linearMapOfEntries (quotSymbol I I (idKernel I) κ) := rfl
  rw [e, h.2, hu]
theorem addScalar_eq_rootedAddScalar (I : PeriodicData) (τ : ℝ) (A : I.Carrier → I.Carrier → ℂ) :
    FreeStrip.addScalar I τ A = RootedSandwiches.addScalar I A τ := by
  funext ι' ι
  simp [FreeStrip.addScalar, RootedSandwiches.addScalar, StripSymbols.linCombKernel]
theorem interpPlusOne_eq_linComb (I : PeriodicData) (t : ℝ) (A B : I.Carrier → I.Carrier → ℂ) :
    interpPlusOne I t A B =
      StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel (t : ℂ) ((1 - t : ℝ) : ℂ) A B) (idKernel I) := by
  funext ι' ι
  simp [interpPlusOne, StripSymbols.linCombKernel]
theorem symbolHom_addScalar_at (q2 : StripSymbols.Claim) (hn : HomNorm.Claim)
    (hid : IdKernelFacts.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {X : I.Carrier → I.Carrier → ℂ} (hX : IsPeriodicKernel I I X) {κ : Fin 4 → ℂ}
    (fX : SymbolSummableAt I I X κ) (τ : ℝ) :
    IsPeriodicKernel I I (RootedSandwiches.addScalar I X τ) ∧
      SymbolSummableAt I I (RootedSandwiches.addScalar I X τ) κ ∧
      symbolHom I I (RootedSandwiches.addScalar I X τ) κ = symbolHom I I X κ + scalarQuotHom I τ := by
  have hi := symbolHom_id_at q2 hn hI κ
  have h := ((q2.2.1 I I hI hI).2.1 X κ hX fX).linComb (idKernel I) (hid I hI).1 hi.1 1 τ
  refine ⟨h.1, h.2.1, ?_⟩
  have e := h.2.2
  rw [hi.2] at e
  change symbolHom I I (StripSymbols.linCombKernel 1 (τ : ℂ) X (idKernel I)) κ = _
  simpa [scalarQuotHom] using e
theorem symbolHom_interpPlusOne_at (q2 : StripSymbols.Claim) (hn : HomNorm.Claim)
    (hid : IdKernelFacts.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {X K : I.Carrier → I.Carrier → ℂ} (hX : IsPeriodicKernel I I X) (hK : IsPeriodicKernel I I K)
    {κ : Fin 4 → ℂ} (fX : SymbolSummableAt I I X κ) (fK : SymbolSummableAt I I K κ) (t : ℝ) :
    IsPeriodicKernel I I (interpPlusOne I t X K) ∧
      SymbolSummableAt I I (interpPlusOne I t X K) κ ∧
      symbolHom I I (interpPlusOne I t X K) κ =
        (t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
          scalarQuotHom I 1 := by
  have hi := symbolHom_id_at q2 hn hI κ
  have h₁ := ((q2.2.1 I I hI hI).2.1 X κ hX fX).linComb K hK fK (t : ℂ) ((1 - t : ℝ) : ℂ)
  have h₂ := ((q2.2.1 I I hI hI).2.1 _ κ h₁.1 h₁.2.1).linComb (idKernel I)
    (hid I hI).1 hi.1 1 1
  rw [interpPlusOne_eq_linComb]
  refine ⟨h₂.1, h₂.2.1, ?_⟩
  have e := h₂.2.2
  rw [hi.2, h₁.2.2] at e
  simpa [scalarQuotHom] using e
theorem tripleCompSymbolInvertibleOn_of_symbols (q2 : StripSymbols.Claim) {I J : PeriodicData}
    (hI : IsPeriodic I) (hJ : IsPeriodic J) {T : I.Carrier → J.Carrier → ℂ}
    {A : J.Carrier → J.Carrier → ℂ} {S : J.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel J I T)
    (hA : IsPeriodicKernel J J A) (hS : IsPeriodicKernel I J S) {D : Set (Fin 4 → ℂ)}
    (h0 : (0 : Fin 4 → ℂ) ∈ D) (fT : SymbolSummableOn J I T D) (fA : SymbolSummableOn J J A D)
    (fS : SymbolSummableOn I J S D) {C : ℝ}
    (hm : ∀ κ ∈ D,
      IsInvertibleQuotHom ((symbolHom J I T κ).comp ((symbolHom J J A κ).comp (symbolHom I J S κ))) ∧
      quotHomNorm (quotHomInverse
        ((symbolHom J I T κ).comp ((symbolHom J J A κ).comp (symbolHom I J S κ)))) ≤
        ENNReal.ofReal C) :
    TripleCompSymbolInvertibleOn I J T A S D C := by
  have p₁ : ∀ κ ∈ D, _ := fun κ hκ => symbolHom_comp_at q2 hJ hI hJ hT hA (fT κ hκ) (fA κ hκ)
  have hTA := (p₁ 0 h0).2.1
  have p₂ : ∀ κ ∈ D, _ := fun κ hκ =>
    symbolHom_comp_at q2 hJ hI hI hTA hS (p₁ κ hκ).2.2.1 (fS κ hκ)
  refine ⟨(p₁ 0 h0).1, (p₂ 0 h0).1, fun κ hκ => (p₂ κ hκ).2.2.1, fun κ hκ => ?_⟩
  rw [(p₂ κ hκ).2.2.2, (p₁ κ hκ).2.2.2]
  exact hm κ hκ
theorem compSymbolBoundedOn_of_symbols (q2 : StripSymbols.Claim) {I I' I'' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {D : Set (Fin 4 → ℂ)}
    (h0 : (0 : Fin 4 → ℂ) ∈ D) (fT : SymbolSummableOn I I' T D) (fS : SymbolSummableOn I'' I S D)
    {C : ℝ}
    (hb : ∀ κ ∈ D, quotHomNorm ((symbolHom I I' T κ).comp (symbolHom I'' I S κ)) ≤
      ENNReal.ofReal C) :
    CompSymbolBoundedOn I I' I'' T S D C := by
  have p : ∀ κ ∈ D, _ := fun κ hκ => symbolHom_comp_at q2 hI hI' hI'' hT hS (fT κ hκ) (fS κ hκ)
  refine ⟨(p 0 h0).1, fun κ hκ => (p κ hκ).2.2.1, fun κ hκ => ?_⟩
  rw [(p κ hκ).2.2.2]
  exact hb κ hκ
theorem strip_properties_of_sandwichInvertibility (q2 : StripSymbols.Claim)
    (hn : HomNorm.Claim) (hid : IdKernelFacts.Claim)
    {I J : PeriodicData} (hI : IsPeriodic I) (hJ : IsPeriodic J)
    {N K X : I.Carrier → I.Carrier → ℂ} {A : J.Carrier → I.Carrier → ℂ} {At : I.Carrier → J.Carrier → ℂ}
    (hN : IsPeriodicKernel I I N) (hK : IsPeriodicKernel I I K) (hX : IsPeriodicKernel I I X)
    (hA : IsPeriodicKernel I J A) (hAt : IsPeriodicKernel J I At) {D D' : Set (Fin 4 → ℂ)}
    (h0 : (0 : Fin 4 → ℂ) ∈ D) (hD : D ⊆ D') (fN : SymbolSummableOn I I N D)
    (fK : SymbolSummableOn I I K D) (fX : SymbolSummableOn I I X D)
    (fA : SymbolSummableOn I J A D) (fAt : SymbolSummableOn J I At D) {C C' t τ : ℝ}
    (hC : C' ≤ C) (h : SandwichInvertibility I J N K X A At D' C' t τ) :
    TripleCompSymbolInvertibleOn I I N (interpPlusOne I t X K) N D C ∧
      TripleCompSymbolInvertibleOn I I N (FreeStrip.addScalar I τ X) N D C ∧
      TripleCompSymbolInvertibleOn J I A (periodicInverse I (FreeStrip.addScalar I τ X)) At D C ∧
      AddScalarInvertibleOn I X τ D := by
  have hle : ENNReal.ofReal C' ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC
  have e := addScalar_eq_rootedAddScalar I τ X
  have si : ∀ κ ∈ D, _ := fun κ hκ =>
    symbolHom_interpPlusOne_at q2 hn hid hI hX hK (fX κ hκ) (fK κ hκ) t
  have ss : ∀ κ ∈ D, _ := fun κ hκ => symbolHom_addScalar_at q2 hn hid hI hX (fX κ hκ) τ
  have first : TripleCompSymbolInvertibleOn I I N (interpPlusOne I t X K) N D C := by
    refine tripleCompSymbolInvertibleOn_of_symbols q2 hI hI hN (si 0 h0).1 hN h0 fN
      (fun κ hκ => (si κ hκ).2.1) fN ?_
    intro κ hκ
    rw [(si κ hκ).2.2]
    exact ⟨(h.interp_invertible κ (hD hκ)).1, (h.interp_invertible κ (hD hκ)).2.trans hle⟩
  have second : TripleCompSymbolInvertibleOn I I N (FreeStrip.addScalar I τ X) N D C := by
    rw [e]
    refine tripleCompSymbolInvertibleOn_of_symbols q2 hI hI hN (ss 0 h0).1 hN h0 fN
      (fun κ hκ => (ss κ hκ).2.1) fN ?_
    intro κ hκ
    rw [(ss κ hκ).2.2]
    exact ⟨(h.shift_invertible κ (hD hκ)).1, (h.shift_invertible κ (hD hκ)).2.trans hle⟩
  have third : TripleCompSymbolInvertibleOn J I A (periodicInverse I (FreeStrip.addScalar I τ X)) At
      D C := by
    rw [e]
    refine tripleCompSymbolInvertibleOn_of_symbols q2 hJ hI hA h.inverse_isPeriodic hAt h0 fA
      (fun κ hκ => h.inverse_summable κ (hD hκ)) fAt ?_
    intro κ hκ
    rw [h.inverse_symbol_eq κ (hD hκ)]
    exact ⟨(h.avg_invertible κ (hD hκ)).1, (h.avg_invertible κ (hD hκ)).2.trans hle⟩
  refine ⟨first, second, third, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact (ss 0 h0).1
  · intro κ hκ
    rw [e]
    exact ⟨fX κ hκ, (ss κ hκ).2.1, (ss κ hκ).2.2⟩
  · rw [e]; exact h.symbol_invertible_real
  · rw [e]; exact h.inverse_isPeriodic
  · intro κ hκ; exact h.shifted_invertible κ (hD hκ)
  · rw [e]; exact fun κ hκ => h.inverse_summable κ (hD hκ)
  · intro κ hκ
    rw [e]
    exact h.inverse_symbol_eq κ (hD hκ)
theorem mem_openStripInterior_of_real (q2 : StripSymbols.Claim) {κ : Fin 4 → ℂ}
    (h : κ ∈ realDualPoints) : κ ∈ openStripInterior (1 / 8) := by
  rw [(q2.1 (1 / 8) (by norm_num)).1]
  show ∀ μ, |(κ μ).im| < 1 / 8
  intro μ
  have e : (κ μ).im = 0 := h μ
  rw [e]
  norm_num
theorem imStrip_subset_openStripInterior (q2 : StripSymbols.Claim) {δ : ℝ} (h0 : 0 < δ)
    (h : δ ≤ 1 / 32) : imStrip (2 * δ) ⊆ openStripInterior (1 / 8) := by
  have e := q2.1 (1 / 8) (by norm_num)
  rw [e.1]
  exact e.2.2.2 (2 * δ) (by linarith) (by linarith)
theorem zero_mem_imStrip {δ : ℝ} (h : 0 < δ) : (0 : Fin 4 → ℂ) ∈ imStrip (2 * δ) := by
  show ∀ μ, |((0 : Fin 4 → ℂ) μ).im| ≤ 2 * δ
  intro μ
  simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
  linarith
theorem imStrip_mono {a b : ℝ} (h : a ≤ b) : imStrip a ⊆ imStrip b :=
  fun _ hκ μ => (hκ μ).trans h
section RootedPairs
open YangMills.Construction.Tower.FreeCoercivity
variable (roots : ResolventRootsOnStrip.ResolventRootsHold)
  (diag : DiagonalSymbolBounds.DiagonalSymbolBoundsHold)
  (avg : SymbolBounds.FreeSymbolNormBounds)
  (sand : SandwichBounds.FreeSandwichBounds)
  (real : FreeSymbolsAtRealPoints)
  (hsym : StripSymbols.Claim)
  (htow : TowerIndexSets.Claim)
include roots diag avg sand real hsym htow
theorem edge_rootedPair {L j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j)
    {cXi cY cC : ℝ} (ops : FiniteRangeOperators L j)
    (rel : ∀ κ ∈ realDualPoints, SymbolMatricesAt L j κ ∧ CoercivityAt L j cXi cY cC κ) :
    RootedPair (colourEdges L j 0) (colourEdges L j j) (edgeResolventSqrt L j)
      (edgeResolventInvSqrt L j) (trivialRescaledOperators L j).K (trivialRescaledOperators L j).Xi
      (trivialRescaledOperators L j).Q (trivialRescaledOperators L j).Qt 10 (Real.exp 1)
      sandwichConstant cXi cC := by
  have r := (roots L hL j hj).1
  refine
    { source_periodic := (htow L hL j 0 (Nat.zero_le j)).2.1
      target_periodic := (htow L hL j j le_rfl).2.1
      K_finiteRange := ⟨ops.K.1, ops.K.2.1⟩
      X_finiteRange := ⟨ops.Xi.1, ops.Xi.2.1⟩
      A_finiteRange := ⟨ops.Q.1, ops.Q.2.1⟩
      At_finiteRange := ⟨ops.Qt.1, ops.Qt.2.1⟩
      N_periodic := r.sqrt_periodic
      Ni_periodic := r.invSqrt_periodic
      N_summable := r.sqrt_summable
      Ni_summable := r.invSqrt_summable
      N_holomorphic := r.sqrt_holomorphicOn
      Ni_holomorphic := r.invSqrt_holomorphicOn
      inverse_pair := r.invSqrt_inverse
      N_norm_le := fun κ hκ => (diag L hL j hj κ hκ).edgeSqrt_le
      A_norm_le := fun κ hκ => ⟨(avg L hL j hj κ hκ).1, (avg L hL j hj κ hκ).2.2.1⟩
      sandwich_norm_le := fun κ hκ => (sand L hL j hj κ hκ).1
      N_selfAdjoint := r.sqrt_selfAdjoint
      K_nonneg := fun κ h => (real L hL j hj κ h).1
      X_lower_bound := fun κ h => (rel κ h).2.Xi_lower
      X_upper_bound := fun κ h => (rel κ h).2.Xi_upper
      N_sandwich_eq_one := fun κ h => r.sqrt_conj_add_one κ (mem_openStripInterior_of_real hsym h)
      At_adjoint := fun κ h => (real L hL j hj κ h).2.2.1
      A_sandwich_lower := fun κ h => ?_ }
  have l := (rel κ h).2.edge_lower
  have e₁ := (r.resolvent_eq_sq κ (mem_openStripInterior_of_real hsym h)).2
  have e₂ := (real L hL j hj κ h).2.2.2.2.1
  simp only [edgeResolventConjugate] at l
  rw [e₁, e₂] at l
  exact l
theorem vertex_rootedPair {L j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j)
    {cXi cY cC : ℝ} (ops : FiniteRangeOperators L j)
    (rel : ∀ κ ∈ realDualPoints, SymbolMatricesAt L j κ ∧ CoercivityAt L j cXi cY cC κ) :
    RootedPair (colourVertices L j 0) (colourVertices L j j) (vertexResolventSqrt L j)
      (vertexResolventInvSqrt L j) (trivialRescaledOperators L j).Delta
      (trivialRescaledOperators L j).Y (trivialRescaledOperators L j).R
      (trivialRescaledOperators L j).Rt 10 (Real.exp 1) sandwichConstant cY cC := by
  have r := (roots L hL j hj).2
  refine
    { source_periodic := (htow L hL j 0 (Nat.zero_le j)).1
      target_periodic := (htow L hL j j le_rfl).1
      K_finiteRange := ⟨ops.Delta.1, ops.Delta.2.1⟩
      X_finiteRange := ⟨ops.Y.1, ops.Y.2.1⟩
      A_finiteRange := ⟨ops.R.1, ops.R.2.1⟩
      At_finiteRange := ⟨ops.Rt.1, ops.Rt.2.1⟩
      N_periodic := r.sqrt_periodic
      Ni_periodic := r.invSqrt_periodic
      N_summable := r.sqrt_summable
      Ni_summable := r.invSqrt_summable
      N_holomorphic := r.sqrt_holomorphicOn
      Ni_holomorphic := r.invSqrt_holomorphicOn
      inverse_pair := r.invSqrt_inverse
      N_norm_le := fun κ hκ => (diag L hL j hj κ hκ).vertexSqrt_le
      A_norm_le := fun κ hκ => ⟨(avg L hL j hj κ hκ).2.1, (avg L hL j hj κ hκ).2.2.2⟩
      sandwich_norm_le := fun κ hκ => (sand L hL j hj κ hκ).2
      N_selfAdjoint := r.sqrt_selfAdjoint
      K_nonneg := fun κ h => (real L hL j hj κ h).2.1
      X_lower_bound := fun κ h => (rel κ h).2.Y_lower
      X_upper_bound := fun κ h => (rel κ h).2.Y_upper
      N_sandwich_eq_one := fun κ h => r.sqrt_conj_add_one κ (mem_openStripInterior_of_real hsym h)
      At_adjoint := fun κ h => (real L hL j hj κ h).2.2.2.1
      A_sandwich_lower := fun κ h => ?_ }
  have l := (rel κ h).2.vertex_lower
  have e₁ := (r.resolvent_eq_sq κ (mem_openStripInterior_of_real hsym h)).2
  have e₂ := (real L hL j hj κ h).2.2.2.2.2
  simp only [vertexResolventConjugate] at l
  rw [e₁, e₂] at l
  exact l
end RootedPairs
theorem freeStripEstimate_holds (hS : RootedSandwiches.SandwichBounds)
    (roots : ResolventRootsOnStrip.ResolventRootsHold)
    (diag : DiagonalSymbolBounds.DiagonalSymbolBoundsHold)
    (avg : SymbolBounds.FreeSymbolNormBounds)
    (sand : SandwichBounds.FreeSandwichBounds)
    (real : FreeSymbolsAtRealPoints)
    (hco : FreeCoercivity.FreeOperatorsCoercive)
    (hsym : StripSymbols.Claim) (hn : HomNorm.Claim)
    (hid : IdKernelFacts.Claim) (htow : TowerIndexSets.Claim)
    (hfree : FreeOperators.FreeOperatorsArePeriodic) : FreeStripEstimate := by
  obtain ⟨cXi, hcXi, cY, hcY, cC, hcC, hco⟩ := hco
  have hB : 0 ≤ sandwichConstant := by
    unfold sandwichConstant
    positivity
  obtain ⟨δ₁, hδ₁, C₁, hC₁, hb₁⟩ := hS 10 (Real.exp 1) sandwichConstant cXi cC (by norm_num)
    (Real.exp_pos 1).le hB hcXi.1 hcXi.2 hcC.1
  obtain ⟨δ₂, hδ₂, C₂, hC₂, hb₂⟩ := hS 10 (Real.exp 1) sandwichConstant cY cC (by norm_num)
    (Real.exp_pos 1).le hB hcY.1 hcY.2 hcC.1
  have hδ0 : 0 < min δ₁ δ₂ := lt_min hδ₁.1 hδ₂.1
  have hδ : min δ₁ δ₂ ≤ 1 / 32 := (min_le_left _ _).trans hδ₁.2
  refine ⟨min δ₁ δ₂, ⟨hδ0, hδ⟩, max (max C₁ C₂) (max 10 (Real.exp 1)),
    le_max_of_le_left (le_max_of_le_left hC₁), fun L hL j hj => ?_⟩
  set δ := min δ₁ δ₂ with hδdef
  set C := max (max C₁ C₂) (max 10 (Real.exp 1)) with hCdef
  have hC1 : C₁ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hC2 : C₂ ≤ C := le_max_of_le_left (le_max_right _ _)
  have h10 : ENNReal.ofReal 10 ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_right (le_max_left _ _))
  have he : ENNReal.ofReal (Real.exp 1) ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (le_max_of_le_right (le_max_right _ _))
  obtain ⟨ops, -, -, rel⟩ := hco L hL j hj
  have pe := edge_rootedPair roots diag avg sand real hsym htow hL hj ops rel
  have pv := vertex_rootedPair roots diag avg sand real hsym htow hL hj ops rel
  have hint := imStrip_subset_openStripInterior hsym hδ0 hδ
  have h0 := zero_mem_imStrip hδ0
  have hEd := pe.source_periodic
  have hTE := pe.target_periodic
  have hVe := pv.source_periodic
  have hTV := pv.target_periodic
  have hFa := (htow L hL j 0 (Nat.zero_le j)).2.2
  have re := (roots L hL j hj).1
  have rv := (roots L hL j hj).2
  have hmaps := (hfree.2 L hL j hj).1
  have hops := (hfree.2 L hL j hj).2
  have dV := (hmaps.vertexCoboundary 0 (Nat.zero_le j)).finite_range
  have dE := (hmaps.edgeCoboundary 0 (Nat.zero_le j)).finite_range
  have dVt := hops.vertexCoboundary_transpose 0 (Nat.zero_le j)
  have dEt := hops.edgeCoboundary_transpose 0 (Nat.zero_le j)
  have fin : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : I'.Carrier → I.Carrier → ℂ}, FreeOperators.HasFiniteRangeEveryRate I I' T →
        SymbolSummableOn I I' T (imStrip (2 * δ)) := by
    intro I I' hI hI' T hT κ _
    exact (hsym.2.1 _ _ hI hI').1.finiteRange T hT.1 hT.2.1 κ (mem_univ κ)
  have fop : ∀ {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ},
      FreeCoercivity.IsFiniteRangeEntire I I' T →
        SymbolSummableOn I I' T (imStrip (2 * δ)) := by
    intro I I' T hT κ _
    exact hT.2.2 κ (mem_univ κ)
  have fNe : SymbolSummableOn _ _ (edgeResolventSqrt L j) (imStrip (2 * δ)) :=
    fun κ hκ => re.sqrt_summable κ (hint hκ)
  have fNv : SymbolSummableOn _ _ (vertexResolventSqrt L j) (imStrip (2 * δ)) :=
    fun κ hκ => rv.sqrt_summable κ (hint hκ)
  have bd := fun κ (hκ : κ ∈ imStrip (2 * δ)) => diag L hL j hj κ (hint hκ)
  have ba := fun κ (hκ : κ ∈ imStrip (2 * δ)) => avg L hL j hj κ (hint hκ)
  refine ⟨?_, fun t ht τ hτ => ?_⟩
  · exact
      { edge_sqrt := ⟨fNe, fun κ hκ => (bd κ hκ).edgeSqrt_le.trans h10⟩
        edge_sqrt_eq := fun κ hκ => re.sqrt_symbol κ (hint hκ)
        vertex_sqrt := ⟨fNv, fun κ hκ => (bd κ hκ).vertexSqrt_le.trans h10⟩
        vertex_sqrt_eq := fun κ hκ => rv.sqrt_symbol κ (hint hκ)
        diff_edge_sqrt := compSymbolBoundedOn_of_symbols hsym hEd hFa hEd dE.1 re.sqrt_periodic h0
          (fin hEd hFa dE) fNe fun κ hκ => (bd κ hκ).coboundary_comp_edgeSqrt_le.trans h10
        diffT_edge_sqrt := compSymbolBoundedOn_of_symbols hsym hEd hVe hEd dVt.1 re.sqrt_periodic h0
          (fin hEd hVe dVt) fNe fun κ hκ => (bd κ hκ).coboundaryTranspose_comp_edgeSqrt_le.trans h10
        edge_sqrt_diff := compSymbolBoundedOn_of_symbols hsym hEd hEd hVe re.sqrt_periodic dV.1 h0 fNe
          (fin hVe hEd dV) fun κ hκ => (bd κ hκ).edgeSqrt_comp_coboundary_le.trans h10
        edge_sqrt_diffT := compSymbolBoundedOn_of_symbols hsym hEd hEd hFa re.sqrt_periodic dEt.1 h0
          fNe (fin hFa hEd dEt) fun κ hκ =>
            (bd κ hκ).edgeSqrt_comp_coboundaryTranspose_le.trans h10
        diff_vertex_sqrt := compSymbolBoundedOn_of_symbols hsym hVe hEd hVe dV.1 rv.sqrt_periodic h0
          (fin hVe hEd dV) fNv fun κ hκ => (bd κ hκ).coboundary_comp_vertexSqrt_le.trans h10
        vertex_sqrt_diffT := compSymbolBoundedOn_of_symbols hsym hVe hVe hEd rv.sqrt_periodic dVt.1 h0
          fNv (fin hEd hVe dVt) fun κ hκ =>
            (bd κ hκ).vertexSqrt_comp_coboundaryTranspose_le.trans h10
        edge_avg := ⟨fop ops.Q, fun κ hκ => (ba κ hκ).1.trans he⟩
        vertex_avg := ⟨fop ops.R, fun κ hκ => (ba κ hκ).2.1.trans he⟩
        edge_avgT := ⟨fop ops.Qt, fun κ hκ => (ba κ hκ).2.2.1.trans he⟩
        vertex_avgT := ⟨fop ops.Rt, fun κ hκ => (ba κ hκ).2.2.2.trans he⟩ }
  · have hd₁ : 2 * δ ≤ 2 * δ₁ := by
      have : δ ≤ δ₁ := min_le_left _ _
      linarith
    have hd₂ : 2 * δ ≤ 2 * δ₂ := by
      have : δ ≤ δ₂ := min_le_right _ _
      linarith
    have ce := strip_properties_of_sandwichInvertibility hsym hn hid hEd hTE re.sqrt_periodic ops.K.1
      ops.Xi.1 ops.Q.1 ops.Qt.1 h0 (imStrip_mono hd₁) fNe (fop ops.K) (fop ops.Xi) (fop ops.Q)
      (fop ops.Qt) hC1 (hb₁ _ _ _ _ _ _ _ _ pe t ht τ hτ)
    have cv := strip_properties_of_sandwichInvertibility hsym hn hid hVe hTV rv.sqrt_periodic
      ops.Delta.1 ops.Y.1 ops.R.1 ops.Rt.1 h0 (imStrip_mono hd₂) fNv (fop ops.Delta) (fop ops.Y)
      (fop ops.R) (fop ops.Rt) hC2 (hb₂ _ _ _ _ _ _ _ _ pv t ht τ hτ)
    exact ⟨ce.1, ce.2.1, cv.1, cv.2.1, ce.2.2.1, cv.2.2.1, ce.2.2.2, cv.2.2.2⟩
end YangMills.Construction.Tower.FreeStrip
end
