import YangMills.Construction.Matrices.ExpSurjectivityAndComplexification
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurations
import YangMills.Construction.Matrices.RestrictionsSumsAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Matrices.TopologiesAndChartsThroughTheInterchange
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.EvaluationOfARealAnalyticMapAtAPoint
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.LogChartsAroundFamily YangMills.Construction.Matrices.ConfigurationLogCharts YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AnalyticRepresentation
theorem exists_basis_traceless : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.traceless_basis_nonempty <;> assumption
def coordinateEntryEquiv {ι : Type} {k : ℕ} (ν : ι ≃ Fin k) :
    Fin (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix) ≃
      ι × Fin 4 :=
  (finSigmaFinEquiv (m := k) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin k) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
theorem matrixPiEquiv_apply_eq {ι : Type} {k : ℕ} (ν : ι ≃ Fin k) (M : ι → ComplexMatrix2)
    (j : Fin (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν M j =
      Coordinates.ComplexCoordinates.matrixEquiv (M (coordinateEntryEquiv ν j).1)
        (coordinateEntryEquiv ν j).2 :=
  rfl
theorem exists_index_eq_entry {ι : Type} {k : ℕ} (ν : ι ≃ Fin k) (i : ι) (r s : Fin 2) :
    ∃ j, ∀ M : ι → ComplexMatrix2, matrixPiEquiv ν M j = M i r s := by
  refine ⟨(coordinateEntryEquiv ν).symm (i, Coordinates.ComplexCoordinates.entryIndex (r, s)),
    fun M => ?_⟩
  rw [matrixPiEquiv_apply_eq, Equiv.apply_symm_apply]
  simp [Coordinates.ComplexCoordinates.matrixEquiv]
theorem differentiableAt_of_forall_entry {γ : ℝ → ComplexMatrix2} {x : ℝ}
    (h : ∀ r s, DifferentiableAt ℝ (fun t => γ t r s) x) : DifferentiableAt ℝ γ x := by
  have hγ : γ = fun t => ∑ r, ∑ s, γ t r s • (Matrix.single r s (1 : ℂ)) := by
    funext t
    ext i j
    simp [Matrix.sum_apply, Matrix.single_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [hγ]
  exact DifferentiableAt.fun_sum fun r _ => DifferentiableAt.fun_sum fun s _ =>
    (h r s).smul_const _
section Products
variable {A B : Type}
def evalOnProduct (w₀ : A → ComplexMatrix2) (W₀ : B → ComplexMatrix2)
    (f : (A ⊕ Empty → ComplexMatrix2) → B ⊕ Empty → ComplexMatrix2)
    (M : A → ComplexMatrix2) : B → ComplexMatrix2 :=
  chartLog W₀ (groupComponent (f (expOnProduct w₀ (tracelessPoint M))))
theorem tracelessPoint_algebraComponent (q : Empty ⊕ A → ComplexMatrix2) :
    tracelessPoint (algebraComponent q) = q := by
  funext i
  rcases i with e | b
  · exact e.elim
  · rfl
theorem expOnProduct_tracelessPoint_zero (w₀ : A → ComplexMatrix2) :
    expOnProduct w₀ (tracelessPoint 0) = asGroupFactors w₀ := by
  funext i
  rcases i with b | e
  · change ComplexMatrix2.expTimesUnitary (0 : ComplexMatrix2) (w₀ b) = w₀ b
    simp [ComplexMatrix2.expTimesUnitary]
  · exact e.elim
theorem hermitianTracelessFunctions_empty : hermitianTracelessFunctions Empty = ⊥ :=
  Submodule.eq_bot_of_subsingleton
variable [Fintype A] [Fintype B]
theorem expOnProduct_analytic (hE : ComplexMatrix2.ExpSurjectivityAndComplexification)
    {w₀ : A → ComplexMatrix2} (hw₀ : w₀ ∈ compactPi A)
    (hExp : ExpHolomorphic w₀) :
    IsSubspaceAnalyticToProduct (R := Empty) (S := A) (R' := A) (S' := Empty)
      (hermitianTracelessFunctions A) ⊥
      (subspaceTimesGroup (hermitianTracelessFunctions A) Empty) (expOnProduct w₀) := by
  refine ⟨⟨le_rfl, univ, isOpen_univ, (univ_inter _).symm⟩, bot_le, ?_, ?_⟩
  · intro q hq
    refine ⟨(Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _), fun b => ?_⟩
    exact Submonoid.mul_mem _ (hE.1 _ (hq.1 b (mem_univ b))) (hw₀ b)
  · intro p hp
    refine ⟨GroupLieProduct Empty A, ?_, ⟨univ, isOpen_univ, (univ_inter _).symm⟩,
      inter_subset_right, expOnProduct w₀, hExp.2, fun _ _ => rfl⟩
    rintro (e | b)
    · exact e.elim
    · exact (hp.1 b (mem_univ b)).2
theorem logOnProduct_analytic (hF : Subspaces.Swap.SwapTheory)
    {W₀ : B → ComplexMatrix2} {ρ : ℝ} (hρ : 0 < ρ) (hB : NeighbourhoodsBasis W₀ ρ)
    (hH : LogHolomorphic W₀ ρ) (hI : LeftInverseOfExp W₀ ρ) :
    IsOpenInSubspaceTimesGroup (R := B) (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
        {q | groupComponent q ∈ chartNeighbourhood ρ W₀ ∩ compactPi B} ∧
      IsSubspaceAnalyticToProduct (R := B) (S := Empty) (R' := Empty) (S' := B) ⊥
        (hermitianTracelessFunctions B)
        {q | groupComponent q ∈ chartNeighbourhood ρ W₀ ∩ compactPi B} (logOnProduct W₀) := by
  have hop : IsOpenInSubspaceTimesGroup (R := B) (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      {q | groupComponent q ∈ chartNeighbourhood ρ W₀ ∩ compactPi B} := by
    have h := (((hF Empty B).1 _ inter_subset_right).2).1 ((hB.2.1 ρ hρ le_rfl).1)
    rwa [hermitianTracelessFunctions_empty] at h
  refine ⟨hop, hop, le_rfl, ?_, ?_⟩
  · intro q hq
    exact ⟨hI.2 _ hq, fun e => e.elim⟩
  · intro p hp
    have hpt : ∀ q : B ⊕ Empty → ComplexMatrix2, asGroupFactors (groupComponent q) = q := by
      intro q
      funext i
      rcases i with b | e
      · rfl
      · exact e.elim
    obtain ⟨b₀⟩ := exists_basis_traceless
    refine ⟨asGroupFactors '' chartNeighbourhood ρ W₀, ⟨_, hp.1, hpt p⟩, (hH.2 b₀).1, ?_,
      logOnProduct W₀, hH.2, fun _ _ => rfl⟩
    rintro q ⟨⟨W, hW, rfl⟩, hq⟩
    exact ⟨hW, hq.2⟩
theorem exists_analytic_chart_domain
    (hC : ConfigurationLogCharts.Statement)
    (hK : AnalyticCalculusStatement)
    (hP : Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (hF : Subspaces.Swap.SwapTheory)
    (hE : ComplexMatrix2.ExpSurjectivityAndComplexification)
    {w₀ : A → ComplexMatrix2} (hw₀ : w₀ ∈ compactPi A) {𝒲 : Set (A ⊕ Empty → ComplexMatrix2)}
    {f : (A ⊕ Empty → ComplexMatrix2) → B ⊕ Empty → ComplexMatrix2}
    (hf : IsSubspaceAnalyticToProduct (R := A) (S := Empty) (R' := B) (S' := Empty) ⊥ ⊥ 𝒲 f)
    (hw : asGroupFactors w₀ ∈ 𝒲) {W₀ : B → ComplexMatrix2}
    (hW₀ : W₀ = groupComponent (f (asGroupFactors w₀)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set (A → ComplexMatrix2), (0 : A → ComplexMatrix2) ∈ O ∧
      (∀ M ∈ O, (∀ c, ComplexMatrix2.operatorNorm (M c) < ε) ∧
        expOnProduct w₀ (tracelessPoint M) ∈ 𝒲 ∧
        groupComponent (f (expOnProduct w₀ (tracelessPoint M))) ∈
          chartNeighbourhood (9 / 10) W₀) ∧
      IsAnalyticOnSubspace (hermitianTracelessFunctions A) (hermitianTracelessFunctions B) O
        (evalOnProduct w₀ W₀ f) ∧
      ∀ M ∈ hermitianTracelessFunctions A, ∀ c,
        DifferentiableAt ℝ (fun t : ℝ => evalOnProduct w₀ W₀ f (t • M) c) 0 := by
  have hWreal : W₀ ∈ compactPi B := by
    rw [hW₀]
    exact (hf.2.2.1 hw).2
  have cA : IsChartCentre w₀ (9 / 10) := ⟨hw₀, by norm_num, by
    simp [ComplexMatrix2.logChartRadius]⟩
  have cB : IsChartCentre W₀ (9 / 10) := ⟨hWreal, by norm_num, by
    simp [ComplexMatrix2.logChartRadius]⟩
  obtain ⟨-, -, -, -, hExp⟩ := hC A w₀ (9 / 10) cA
  obtain ⟨hBasis, hChart, hInv, -, -⟩ := hC B W₀ (9 / 10) cB
  have h1 := expOnProduct_analytic hE hw₀ hExp
  obtain ⟨hop'', h3⟩ := logOnProduct_analytic hF (by norm_num) hBasis hChart hInv
  have hopen₀ : IsOpenInSubspaceTimesGroup (R := Empty) (hermitianTracelessFunctions A)
      (subspaceTimesGroup (hermitianTracelessFunctions A) Empty) := h1.1
  obtain ⟨-, h1'⟩ := (((hK A Empty Empty A).2.2.2 (hermitianTracelessFunctions A) ⊥ le_rfl
    bot_le).2.2.1 _ hopen₀).2.2.1 _ h1
  obtain ⟨hopen1, -, hcomp1⟩ := h1' 𝒲 hf.1
  have h12 := hcomp1 Empty B ⊥ f hf
  obtain ⟨-, h2'⟩ := (((hK A Empty Empty B).2.2.2 (hermitianTracelessFunctions A) ⊥ le_rfl
    bot_le).2.2.1 _ ⟨le_rfl, hopen1⟩).2.2.1 _ h12
  obtain ⟨hopen2, -, hcomp2⟩ := h2' _ hop''
  have h123 := hcomp2 B Empty (hermitianTracelessFunctions B) (logOnProduct W₀) h3
  have hBl : IsOpen {q : Empty ⊕ A → ComplexMatrix2 |
      ∀ c, ComplexMatrix2.operatorNorm (q (.inr c)) < ε} := by
    have hset : {q : Empty ⊕ A → ComplexMatrix2 |
        ∀ c, ComplexMatrix2.operatorNorm (q (.inr c)) < ε} =
        ⋂ c, {q : Empty ⊕ A → ComplexMatrix2 | ComplexMatrix2.operatorNorm (q (.inr c)) < ε} := by
      ext q
      simp
    rw [hset]
    exact isOpen_iInter_of_finite fun c =>
      isOpen_lt (continuous_norm.comp (continuous_apply _)) continuous_const
  obtain ⟨U₂, hU₂, hU₂e⟩ := hopen2
  set D : Set (Empty ⊕ A → ComplexMatrix2) :=
      subspaceTimesGroup (hermitianTracelessFunctions A) Empty ∩
      expOnProduct w₀ ⁻¹' 𝒲 ∩ (f ∘ expOnProduct w₀) ⁻¹'
        {q | groupComponent q ∈ chartNeighbourhood (9 / 10) W₀ ∩ compactPi B} with hD
  have hDopen : ComplexMatrix2.IsRelativelyOpen
      (subspaceTimesGroup (hermitianTracelessFunctions A) Empty) D := ⟨U₂, hU₂, hU₂e⟩
  set D₂ : Set (Empty ⊕ A → ComplexMatrix2) :=
    D ∩ {q : Empty ⊕ A → ComplexMatrix2 | ∀ c, ComplexMatrix2.operatorNorm (q (.inr c)) < ε}
    with hD₂
  have hD₂open : ComplexMatrix2.IsRelativelyOpen
      (subspaceTimesGroup (hermitianTracelessFunctions A) Empty) D₂ := by
    refine ⟨U₂ ∩ {q : Empty ⊕ A → ComplexMatrix2 |
      ∀ c, ComplexMatrix2.operatorNorm (q (.inr c)) < ε}, hU₂.inter hBl, ?_⟩
    rw [hD₂, hU₂e]
    ext q
    simp only [mem_inter_iff]
    tauto
  have h4 := ((hP A Empty B Empty (hermitianTracelessFunctions A) (hermitianTracelessFunctions B)
    le_rfl le_rfl D ⟨le_rfl, hDopen⟩).1 D₂ inter_subset_left hD₂open).2 _ h123
  set O : Set (A → ComplexMatrix2) := {M | tracelessPoint M ∈ D₂} with hO
  have hOset : {q : Empty ⊕ A → ComplexMatrix2 | algebraComponent q ∈ O} = D₂ := by
    ext q
    change tracelessPoint (algebraComponent q) ∈ D₂ ↔ _
    rw [tracelessPoint_algebraComponent]
  have hmap : (fun q : Empty ⊕ A → ComplexMatrix2 =>
      ofParts Empty.elim (evalOnProduct w₀ W₀ f (algebraComponent q))) =
      logOnProduct W₀ ∘ (f ∘ expOnProduct w₀) := by
    funext q
    simp only [evalOnProduct, tracelessPoint_algebraComponent]
    rfl
  have han : IsAnalyticOnSubspace (hermitianTracelessFunctions A) (hermitianTracelessFunctions B)
      O (evalOnProduct w₀ W₀ f) := by
    unfold IsAnalyticOnSubspace
    rw [hOset, hmap]
    exact h4
  have h0 : (0 : A → ComplexMatrix2) ∈ O := by
    have hz : expOnProduct w₀ (tracelessPoint 0) = asGroupFactors w₀ :=
      expOnProduct_tracelessPoint_zero w₀
    refine ⟨⟨⟨⟨Submodule.zero_mem _, fun e => e.elim⟩, ?_⟩, ?_⟩, ?_⟩
    · change expOnProduct w₀ (tracelessPoint 0) ∈ 𝒲
      rw [hz]
      exact hw
    · change groupComponent (f (expOnProduct w₀ (tracelessPoint 0))) ∈
        chartNeighbourhood (9 / 10) W₀ ∩ compactPi B
      rw [hz, ← hW₀]
      exact (hBasis.2.1 _ (by norm_num) le_rfl).2
    · intro c
      change ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) < ε
      simpa using hε
  refine ⟨O, h0, ?_, han, ?_⟩
  · intro M hM
    exact ⟨hM.2, hM.1.1.2, hM.1.2.1⟩
  · intro M hMr c
    have : FiniteDimensional ℝ (hermitianTracelessFunctions A) := (hK A Empty Empty Empty).1 _ le_rfl
    let e := Module.finBasis ℝ (hermitianTracelessFunctions A)
    let ν : IndexEnum Empty := Fintype.equivFinOfCardEq (by simp)
    have hOpen : IsOpenInSubspaceTimesGroup (R := Empty) (hermitianTracelessFunctions A)
        {q : Empty ⊕ A → ComplexMatrix2 | algebraComponent q ∈ O} := han.1
    have hz₀ : (0 : Empty ⊕ A → ComplexMatrix2) ∈
        subspaceTimesGroup (hermitianTracelessFunctions A) Empty :=
      ⟨Submodule.zero_mem _, fun e => e.elim⟩
    have hz₁ : (0 : Empty ⊕ A → ComplexMatrix2) ∈
        {q : Empty ⊕ A → ComplexMatrix2 | algebraComponent q ∈ O} := h0
    have pack := hP A Empty B Empty (hermitianTracelessFunctions A)
      (hermitianTracelessFunctions B) le_rfl le_rfl _ hOpen
    have hν := (pack.2.2.2 ν).1 _ e 0 hz₀
    obtain ⟨T, hT, h0T, hTsub⟩ := (hν.1.2.2.2.2 hz₁).2
    have hread := ((hν.2 hz₁ T hT h0T hTsub).2.2.2 _ han).2 _ (Fintype.equivFin (Empty ⊕ B))
    have hsm := hread.2.1
    obtain ⟨Uo, hUo, hTe⟩ := hT
    have hptc : Continuous (ofRealVector
        (N := Module.finrank ℝ (hermitianTracelessFunctions A) + 3 * Fintype.card Empty)) :=
      continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
    have hnh : ofRealVector ⁻¹' T ∈ 𝓝
        (0 : Fin (Module.finrank ℝ (hermitianTracelessFunctions A) + 3 * Fintype.card Empty) → ℝ) := by
      have h0U : ofRealVector
          (0 : Fin (Module.finrank ℝ (hermitianTracelessFunctions A) + 3 * Fintype.card Empty) → ℝ)
            ∈ Uo := by
        have hz : ofRealVector
            (0 : Fin (Module.finrank ℝ (hermitianTracelessFunctions A) + 3 * Fintype.card Empty)
              → ℝ) = 0 := by
          funext j
          simp [ofRealVector]
        rw [hz]
        rw [hTe] at h0T
        exact h0T.1
      refine Filter.mem_of_superset ((hUo.preimage hptc).mem_nhds h0U) fun u hu => ?_
      change ofRealVector u ∈ T
      rw [hTe]
      exact ⟨hu, fun j => by simp [ofRealVector], fun ρ => ρ.elim⟩
    let U₀ : Fin (Module.finrank ℝ (hermitianTracelessFunctions A) + 3 * Fintype.card Empty) → ℝ :=
      Fin.addCases (fun i => e.repr ⟨M, hMr⟩ i) (fun _ => 0)
    have hsumM : ∑ i, (e.repr ⟨M, hMr⟩ i) • ((e i : hermitianTracelessFunctions A) :
        A → ComplexMatrix2) = M := by
      have h : ((∑ i, e.repr ⟨M, hMr⟩ i • e i : hermitianTracelessFunctions A) :
          A → ComplexMatrix2) = M := by
        rw [e.sum_repr]
      rw [AddSubmonoidClass.coe_finsetSum] at h
      exact h
    have hline : ∀ t : ℝ,
        algebraComponent (basisExpChart e ν 0 (ofRealVector (t • U₀))) = t • M := by
      intro t
      have hlin : ∀ i, linearPart (ofRealVector (t • U₀)) i =
          ((t * e.repr ⟨M, hMr⟩ i : ℝ) : ℂ) := by
        intro i
        simp [linearPart, ofRealVector, U₀]
      change algebraComponent (0 : Empty ⊕ A → ComplexMatrix2) +
        ∑ i, linearPart (ofRealVector (t • U₀)) i •
          ((e i : hermitianTracelessFunctions A) : A → ComplexMatrix2) = t • M
      simp only [hlin]
      conv_rhs => rw [← hsumM]
      rw [Finset.smul_sum]
      have hz : algebraComponent (0 : Empty ⊕ A → ComplexMatrix2) = 0 := rfl
      rw [hz, zero_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext a
      ext r s
      simp [mul_assoc]
    have hdiff := DifferentiableAt.comp (0 : ℝ)
      (g := (matrixPiEquiv (Fintype.equivFin (Empty ⊕ B)) ∘
        (fun q : Empty ⊕ A → ComplexMatrix2 =>
          ofParts Empty.elim (evalOnProduct w₀ W₀ f (algebraComponent q))) ∘
            basisExpChart e ν 0) ∘ ofRealVector)
      (f := fun t : ℝ => t • U₀)
      (by
        rw [zero_smul]
        exact (hsm.contDiffAt hnh).differentiableAt (by simp))
      (differentiableAt_id.smul_const U₀)
    refine differentiableAt_of_forall_entry fun r s => ?_
    obtain ⟨j, hj⟩ := exists_index_eq_entry (Fintype.equivFin (Empty ⊕ B)) (.inr c) r s
    refine (differentiableAt_pi.1 hdiff j).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    change _ = matrixPiEquiv (Fintype.equivFin (Empty ⊕ B))
      (ofParts Empty.elim (evalOnProduct w₀ W₀ f
        (algebraComponent (basisExpChart e ν 0 (ofRealVector (t • U₀)))))) j
    rw [hj, hline]
    rfl
end Products
section Lattice
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (c : Edge L n k j) :
    c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem edgeFormOfPositiveValues_smul (t : ℝ) (M : PositiveEdge L n k j → ComplexMatrix2) :
    edgeFormOfPositiveValues (t • M) = (t : ℂ) • edgeFormOfPositiveValues M := by
  funext c
  unfold edgeFormOfPositiveValues
  by_cases hc : c.IsPositivelyOriented
  · ext r s
    simp [hc]
  · by_cases hr : c.opposite.IsPositivelyOriented
    · ext r s
      simp [hc, hr]
    · simp [hc, hr]
theorem fieldOfPositiveValues_expOnProduct (V : Edge L n k j → ComplexMatrix2)
    (M : PositiveEdge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues
        (groupComponent (expOnProduct (restrictToPositiveEdges V) (tracelessPoint M))) =
      PeriodicLattice.expTwist (edgeFormOfPositiveValues M) V := by
  funext c
  by_cases hc : c.IsPositivelyOriented
  · simp only [fieldOfPositiveValues, dif_pos hc, PeriodicLattice.expTwist, if_pos hc,
      edgeFormOfPositiveValues]
    rfl
  · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
    simp only [fieldOfPositiveValues, dif_neg hc, dif_pos hr, PeriodicLattice.expTwist,
      if_neg hc, edgeFormOfPositiveValues]
    rfl
end Lattice
theorem analyticMapObservable (hC : ConfigurationLogCharts.Statement)
    (hK : AnalyticCalculusStatement)
    (hP : Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (hF : Subspaces.Swap.SwapTheory)
    (hE : ComplexMatrix2.ExpSurjectivityAndComplexification) : AnalyticMapRepresentationStatement := by
  intro L n k a b hL hn ha hb iA iB 𝒰 m hm V hV ε hε
  obtain ⟨hU, hmaps, f₁, f₂, hra⟩ := hm
  obtain rfl : f₁ = iA := Subsingleton.elim _ _
  obtain rfl : f₂ = iB := Subsingleton.elim _ _
  have hVc : V ∈ fieldSpace L n k a := hU.1 hV
  have hmV : m V ∈ fieldSpace L n k b := hmaps hV
  have hw₀ : restrictToPositiveEdges V ∈ compactPi (PositiveEdge L n k a) :=
    fun c => hVc.1 c (mem_univ _)
  have hw : asGroupFactors (restrictToPositiveEdges V) ∈
      {q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 |
        fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
    change fieldOfPositiveValues (restrictToPositiveEdges V) ∈ 𝒰
    rw [fieldOfPositiveValues_restrict hVc]
    exact hV
  have hW₀ : restrictToPositiveEdges (m V) = groupComponent
      ((fun q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 =>
        ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q))))
          Empty.elim) (asGroupFactors (restrictToPositiveEdges V))) := by
    change restrictToPositiveEdges (m V) =
      restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges V)))
    rw [fieldOfPositiveValues_restrict hVc]
  obtain ⟨O, h0, hO, han, hdf⟩ := exists_analytic_chart_domain hC hK hP hF hE hw₀ hra hw hW₀ hε
  have hval : ∀ M : PositiveEdge L n k a → ComplexMatrix2,
      groupComponent ((fun q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 =>
        ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q))))
          Empty.elim) (expOnProduct (restrictToPositiveEdges V) (tracelessPoint M))) =
        restrictToPositiveEdges (m (PeriodicLattice.expTwist (edgeFormOfPositiveValues M) V)) := by
    intro M
    change restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent
      (expOnProduct (restrictToPositiveEdges V) (tracelessPoint M))))) = _
    rw [fieldOfPositiveValues_expOnProduct]
  have hread : evalOnProduct (restrictToPositiveEdges V) (restrictToPositiveEdges (m V))
      (fun q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 =>
        ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q))))
          Empty.elim) =
      logChartCoordinates m V := by
    funext M
    unfold evalOnProduct
    rw [hval]
    rfl
  rw [hread] at han hdf
  have hlog : ∀ c : PositiveEdge L n k b, ComplexMatrix2.logSeries (m V c * (m V c)⁻¹) = 0 := by
    intro c
    have hd : (m V c).det = 1 :=
      (Matrix.mem_specialUnitaryGroup_iff.1 (hmV.1 c.1 (mem_univ _))).2
    rw [Matrix.mul_nonsing_inv _ (by rw [hd]; exact isUnit_one)]
    simp [ComplexMatrix2.logSeries]
  have hWreal : restrictToPositiveEdges (m V) ∈ compactPi (PositiveEdge L n k b) :=
    fun c => hmV.1 c (mem_univ _)
  obtain ⟨-, -, hInv, -, -⟩ := hC _ (restrictToPositiveEdges (m V)) (9 / 10)
    ⟨hWreal, by norm_num, by simp [ComplexMatrix2.logChartRadius]⟩
  refine ⟨O, h0, ?_, ?_, han, ?_⟩
  · have hV0 : PeriodicLattice.expTwist (edgeFormOfPositiveValues 0) V = V := by
      rw [← fieldOfPositiveValues_expOnProduct, expOnProduct_tracelessPoint_zero]
      exact fieldOfPositiveValues_restrict hVc
    funext c
    simp only [logChartCoordinates, hV0, hlog]
    simp
  · intro M hM
    obtain ⟨hb', hmem, hnb⟩ := hO M hM
    have hmem' : PeriodicLattice.expTwist (edgeFormOfPositiveValues M) V ∈ 𝒰 := by
      have h := hmem
      change fieldOfPositiveValues _ ∈ 𝒰 at h
      rwa [fieldOfPositiveValues_expOnProduct] at h
    refine ⟨hb', hmem', ?_, ?_⟩
    · intro h0'
      rw [hval] at hnb
      have hinv := (hInv.1 _ hnb).1
      have hcm : chartLog (restrictToPositiveEdges (m V))
          (restrictToPositiveEdges
            (m (PeriodicLattice.expTwist (edgeFormOfPositiveValues M) V))) = 0 := h0'
      rw [hcm] at hinv
      have hon : restrictToPositiveEdges (m V) =
          restrictToPositiveEdges (m (PeriodicLattice.expTwist (edgeFormOfPositiveValues M) V)) := by
        rw [← hinv]
        funext c
        simp [expTimesUnitaryFamily, ComplexMatrix2.expTimesUnitary]
      rw [← fieldOfPositiveValues_restrict (hmaps hmem'), ← hon,
        fieldOfPositiveValues_restrict hmV]
    · intro he
      funext c
      simp only [logChartCoordinates, he, hlog]
      simp
  · intro M hM
    have hd : ∀ c, DifferentiableAt ℝ (fun t : ℝ => logChartCoordinates m V (t • M) c) 0 :=
      hdf M hM
    rw [deriv_pi hd]
    funext c
    have hg : (fun t : ℝ => logChartCoordinates m V (t • M) c) = fun t : ℝ => Complex.I⁻¹ •
        ComplexMatrix2.logSeries
          (m (PeriodicLattice.expTwist ((t : ℂ) • edgeFormOfPositiveValues M) V) c *
            (m V c)⁻¹) := by
      funext t
      simp only [logChartCoordinates, edgeFormOfPositiveValues_smul]
    have hgd : DifferentiableAt ℝ (fun t : ℝ =>
        ComplexMatrix2.logSeries
          (m (PeriodicLattice.expTwist ((t : ℂ) • edgeFormOfPositiveValues M) V) c *
            (m V c)⁻¹)) 0 := by
      refine ((hd c).const_smul Complex.I).congr_of_eventuallyEq
        (Eventually.of_forall fun t => ?_)
      change _ = Complex.I • logChartCoordinates m V (t • M) c
      simp only [logChartCoordinates, edgeFormOfPositiveValues_smul, smul_smul,
        mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    rw [hg, deriv_fun_const_smul _ hgd]
    change _ = leftDifferential m V (edgeFormOfPositiveValues M) c.1
    simp only [leftDifferential, extendOddly, if_pos c.2, logDirectionalDeriv]
    rfl
end YangMills.Construction.Tower.AnalyticRepresentation
end
