import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOneProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.AnalyticFieldFunctions
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
open YangMills.Construction.Tower
section Functions
variable {L n k j j' : ℕ}
theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k j)]
    {U : Set (Edge L n k j → ComplexMatrix2)}
    (h : IsOpenFieldSet YangMills.Construction.PeriodicLattice.compactGaugeGroup U) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k j) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ U} := by apply _root_.YangMills.SharedProofs.p979 <;> assumption
theorem analytic_congr {U : Set (Edge L n k j → ComplexMatrix2)}
    {F G : (Edge L n k j → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction U F) (e : EqOn F G U) :
    IsAnalyticFieldFunction U G := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_congr <;> assumption
theorem analytic_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {U U' : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction U F)
    (h' : IsOpenFieldSet YangMills.Construction.PeriodicLattice.compactGaugeGroup U')
    (hsub : U' ⊆ U) : IsAnalyticFieldFunction U' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem analytic_add (H : LocalAnalyticity.LocalAnalyticityStatement)
    {U : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction U F₁) (h₂ : IsAnalyticFieldFunction U F₂) :
    IsAnalyticFieldFunction U fun V => F₁ V + F₂ V := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_add <;> assumption
theorem analytic_const (H : AnalyticCalculus.AnalyticCalculusStatement)
    (hfin : Finite (PositiveEdge L n k j)) {U : Set (Edge L n k j → ComplexMatrix2)}
    (hop : IsOpenFieldSet YangMills.Construction.PeriodicLattice.compactGaugeGroup U) (c : ℝ) :
    IsAnalyticFieldFunction U fun _ => c := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_const <;> assumption
theorem analytic_mul (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    {U : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction U F₁) (h₂ : IsAnalyticFieldFunction U F₂) :
    IsAnalyticFieldFunction U fun V => F₁ V * F₂ V := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mul <;> assumption
theorem finite_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (PositiveEdge L n k j) := by
  have : Finite (Edge L n k j) := Set.finite_univ_iff.1 ((hE L hL k j hj).1 n hn).2.1
  exact Subtype.finite
theorem analytic_comp_map (H : AnalyticCalculus.AnalyticCalculusStatement)
    {U : Set (Edge L n k j → ComplexMatrix2)} {U' : Set (Edge L n k j' → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {F : (Edge L n k j' → ComplexMatrix2) → ℝ}
    (hm : IsAnalyticFieldMap U m) (hF : IsAnalyticFieldFunction U' F) :
    IsAnalyticFieldFunction (U ∩ m ⁻¹' U') (F ∘ m) := by
  obtain ⟨hop, hto, i, i', am⟩ := hm
  obtain ⟨hop', i'', aF⟩ := hF
  obtain rfl : i'' = i' := Subsingleton.elim _ _
  have hW := isOpenInSubspaceTimesGroup_of_isOpenFieldSet hop
  have hW' := isOpenInSubspaceTimesGroup_of_isOpenFieldSet hop'
  have hcomp := ((((H Empty (PositiveEdge L n k j) Empty (PositiveEdge L n k j')).2.2.2
    ⊥ ⊥ bot_le bot_le).2.2.1 _ hW).2.2.1 _ am).2 _ hW'
  have hback : ∀ V ∈ U, fieldOfPositiveValues (groupComponent (ofParts (R := PositiveEdge L n k j')
      (S := Empty) (restrictToPositiveEdges (m V)) Empty.elim)) = m V :=
    fun V hV => fieldOfPositiveValues_restrict (hto hV)
  have hset : {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
        fieldOfPositiveValues (groupComponent q) ∈ U} ∩
      (fun q => ofParts (S := Empty) (restrictToPositiveEdges
        (m (fieldOfPositiveValues (groupComponent q)))) Empty.elim) ⁻¹'
      {q : PositiveEdge L n k j' ⊕ Empty → ComplexMatrix2 |
        fieldOfPositiveValues (groupComponent q) ∈ U'} =
      {q | fieldOfPositiveValues (groupComponent q) ∈ U ∩ m ⁻¹' U'} := by
    ext q
    constructor
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      have h := hq'
      simp only [mem_preimage, mem_ofPred_eq] at h
      rwa [hback _ hq] at h
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      simp only [mem_preimage, mem_ofPred_eq]
      rwa [hback _ hq]
  have hana := hcomp.2.1 1 _ aF
  have hopen := hcomp.1
  rw [hset] at hana hopen
  obtain ⟨O₂, hO₂, he⟩ := hopen
  have hg : Continuous fun w : PositiveEdge L n k j → ComplexMatrix2 =>
      (ofParts (S := Empty) w Empty.elim : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) := by
    refine continuous_pi fun r => ?_
    cases r with
    | inl r => exact continuous_apply r
    | inr r => exact r.elim
  refine ⟨⟨fun V hV => hop.1 hV.1, (fun w : PositiveEdge L n k j → ComplexMatrix2 =>
    (ofParts (S := Empty) w Empty.elim : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2)) ⁻¹' O₂,
    hO₂.preimage hg, ?_⟩, i, ?_⟩
  · ext w
    constructor
    · rintro ⟨V, hV, rfl⟩
      have hmem : (ofParts (S := Empty) (restrictToPositiveEdges V) Empty.elim :
          PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) ∈
          {q | fieldOfPositiveValues (groupComponent q) ∈ U ∩ m ⁻¹' U'} := by
        change fieldOfPositiveValues (restrictToPositiveEdges V) ∈ U ∩ m ⁻¹' U'
        rw [fieldOfPositiveValues_restrict (hop.1 hV.1)]
        exact hV
      rw [he] at hmem
      exact ⟨hmem.1, hmem.2.2⟩
    · rintro ⟨h₁, h₂⟩
      have hmem : (ofParts (S := Empty) w Empty.elim :
          PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) ∈
          O₂ ∩ subspaceTimesGroup ⊥ (PositiveEdge L n k j) := ⟨h₁, Subsingleton.elim _ _, h₂⟩
      rw [← he] at hmem
      exact ⟨fieldOfPositiveValues w, hmem, restrict_fieldOfPositiveValues w⟩
  · refine ⟨?_, fun p hp => ?_⟩
    · exact hana.1
    · obtain ⟨X, h1, h2, h3, Φ, hΦ, e⟩ := hana.2 p hp
      refine ⟨X, h1, h2, h3, Φ, hΦ, fun q hq => (e hq).trans ?_⟩
      have hqU : fieldOfPositiveValues (groupComponent q) ∈ U := (h3 hq).1
      funext x
      simp only [Function.comp_apply]
      rw [hback _ hqU]
end Functions
theorem analyticFieldFunctionsClosed (h₁ : LocalAnalyticity.LocalAnalyticityStatement)
    (h₂ : AnalyticCalculus.AnalyticCalculusStatement)
    (h₃ : ExpChartHolomorphy.ExpChartTheory)
    (h₄ : BondSetFields.ProductStructureHolds) :
    AnalyticFieldFunctionsClosed := by
  intro L n k j j' hL hn hj _
  exact ⟨fun U c hop => analytic_const h₂ (finite_positiveEdge h₄ hL hn hj) hop c,
    fun U F G hF hG => ⟨analytic_add h₁ hF hG, analytic_mul h₃ h₁ hF hG⟩,
    fun U U' F hF hop hsub => analytic_mono h₁ hF hop hsub,
    fun U F G hF e => analytic_congr hF e,
    fun U U' m F hm hF => analytic_comp_map h₂ hm hF⟩
end YangMills.Construction.Tower.AnalyticFieldFunctions
end
