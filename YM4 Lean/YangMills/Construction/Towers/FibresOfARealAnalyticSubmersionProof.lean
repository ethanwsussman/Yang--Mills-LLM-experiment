import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealForm
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.EvaluationOfARealAnalyticMapAtAPoint
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersion
import YangMills.Construction.Towers.GraphsInTheLeftChartAreSubmanifolds
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiable
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.SubmersionFibres
variable {L n k j : ℕ}
private theorem edge_or_opposite_positive (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem opposite_not_positive (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) (e : Edge L n k j) (he : e.IsPositivelyOriented) :
    ¬ e.opposite.IsPositivelyOriented :=
  PeriodicLattice.Bond.opposite_not_isPositivelyOriented (by have := hL.2; omega)
    (by simp only [PeriodicLattice.levelDepth]; omega) he
abbrev _root_.YangMills.SharedProofs.p24505 := @opposite_not_positive
private theorem edgeForm_apply_positive (w : PositiveEdge L n k j → Matrices.ComplexMatrix2)
    {e : Edge L n k j} (he : e.IsPositivelyOriented) :
    edgeFormOfPositiveValues w e = w ⟨e, he⟩ := by
  simp [edgeFormOfPositiveValues, he]
private theorem edgeForm_apply_negative (w : PositiveEdge L n k j → Matrices.ComplexMatrix2)
    {e : Edge L n k j} (he : ¬ e.IsPositivelyOriented) :
    edgeFormOfPositiveValues w e =
      -w ⟨e.opposite, (edge_or_opposite_positive e).resolve_left he⟩ := by
  simp [edgeFormOfPositiveValues, he, (edge_or_opposite_positive e).resolve_left he]
private def edgeFormLinear (L n k j : ℕ) :
    (PositiveEdge L n k j → Matrices.ComplexMatrix2) →ₗ[ℝ]
      (Edge L n k j → Matrices.ComplexMatrix2) where
  toFun := edgeFormOfPositiveValues
  map_add' w w' := by
    funext e
    by_cases he : e.IsPositivelyOriented
    · simp [edgeForm_apply_positive _ he]
    · simp only [edgeForm_apply_negative _ he, Pi.add_apply]
      abel
  map_smul' s w := by
    funext e
    by_cases he : e.IsPositivelyOriented
    · simp [edgeForm_apply_positive _ he]
    · simp [edgeForm_apply_negative _ he]
private theorem restrict_edgeForm (w : PositiveEdge L n k j → Matrices.ComplexMatrix2) :
    restrictToPositiveEdges (edgeFormOfPositiveValues w) = w := by
  funext p
  exact edgeForm_apply_positive w p.2
private theorem edgeForm_restrict {F : Edge L n k j → Matrices.ComplexMatrix2}
    (hodd : ∀ e : Edge L n k j, ¬ e.IsPositivelyOriented → F e = -F e.opposite) :
    edgeFormOfPositiveValues (restrictToPositiveEdges F) = F := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · rw [edgeForm_apply_positive _ he]
    rfl
  · rw [edgeForm_apply_negative _ he, hodd e he]
    rfl
private theorem edgeForm_mem_space
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → Matrices.ComplexMatrix2}
    (hw : w ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j)) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · rw [edgeForm_apply_positive w he]
    exact hw _ (mem_univ _)
  · by_cases he : e.IsPositivelyOriented
    · rw [edgeForm_apply_negative w (hopp e he), edgeForm_apply_positive w he]
      rfl
    · rw [edgeForm_apply_positive w ((edge_or_opposite_positive e).resolve_left he),
        edgeForm_apply_negative w he, neg_neg]
private theorem extendOddly_apply_negative (F : Edge L n k j → Matrices.ComplexMatrix2)
    (e : Edge L n k j) (he : ¬ e.IsPositivelyOriented) :
    extendOddly F e = -extendOddly F e.opposite := by
  have he' := (edge_or_opposite_positive e).resolve_left he
  simp [extendOddly, he, he']
private theorem extendOddly_eq_zero {F : Edge L n k j → Matrices.ComplexMatrix2}
    (hF : restrictToPositiveEdges (extendOddly F) = 0) : extendOddly F = 0 := by
  rw [← edgeForm_restrict (extendOddly_apply_negative F), hF]
  exact (edgeFormLinear L n k j).map_zero
theorem submersionFibres_areSubmanifolds
    (hGraph : LeftChartGraphsAreSubmanifolds)
    (hImplicit : Matrices.GroupLieProduct.Subspaces.RealForm.ImplicitFunctionStatement)
    (hPullback : AnalyticMapRepresentationStatement)
    (hDiff : AnalyticMapDifferentiableStatement)
    (hCurve : FiniteLevelCurveDifferentials.Statement)
    (hFields : LeftChartFields.Claim) :
    SubmersionFibresAreSubmanifolds := by
  intro L n k a b hL hn ha hb 𝒰 m hm honto W
  obtain ⟨ia, ib, -⟩ := hm.2.2
  have hoppa : ∀ e : Edge L n k a, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented :=
    opposite_not_positive hL hn ha
  have hoppb : ∀ e : Edge L n k b, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented :=
    opposite_not_positive hL hn hb
  obtain ⟨N, hN⟩ : ∃ N : Set (Edge L n k a → Matrices.ComplexMatrix2),
      N = {U | U ∈ 𝒰 ∧ m U = W} := ⟨_, rfl⟩
  rw [← hN]
  have hmemN : ∀ U, U ∈ N ↔ U ∈ 𝒰 ∧ m U = W := fun U => by rw [hN]; rfl
  have hsub : N ⊆ fieldSpace L n k a := fun U hU => hm.1.1 ((hmemN U).1 hU).1
  have hlocal : ∀ U, U ∈ 𝒰 → m U = W →
      ∃ (E E' : Submodule ℝ (PositiveEdge L n k a → Matrices.ComplexMatrix2))
        (O₁ O₂ : Set (PositiveEdge L n k a → Matrices.ComplexMatrix2))
        (g : (PositiveEdge L n k a → Matrices.ComplexMatrix2) →
          PositiveEdge L n k a → Matrices.ComplexMatrix2),
        IsLeftChartGraphAt N U E E' O₁ O₂ g ∧
        ∀ X, X ∈ E ↔ X ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions
            (PositiveEdge L n k a) ∧
          restrictToPositiveEdges (leftDifferential m U (edgeFormOfPositiveValues X)) = 0 := by
    intro U hU hUW
    obtain ⟨O, hO0, hΦ0, hOprop, hanalytic, hderiv⟩ :=
      hPullback L n k a b hL hn ha hb 𝒰 m hm U hU (1 / 2) (by norm_num)
    have honto' : ∀ Y ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k b),
        ∃ X ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a),
          deriv (fun s : ℝ => logChartCoordinates m U (s • X)) 0 = Y := by
      intro Y hY
      obtain ⟨F, hF, hFY⟩ := honto U hU (edgeFormOfPositiveValues Y) (edgeForm_mem_space hoppb hY)
      have hF1 : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra F := hF
      have hFfix : edgeFormOfPositiveValues (restrictToPositiveEdges F) = F :=
        edgeForm_restrict fun e _ => by rw [hF1.2 e, neg_neg]
      have hFreal : restrictToPositiveEdges F ∈
          Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a) :=
        fun p _ => hF1.1 p.1 p.2
      refine ⟨restrictToPositiveEdges F, hFreal, ?_⟩
      rw [hderiv _ hFreal, hFfix, hFY, restrict_edgeForm]
    obtain ⟨E, E', O₁, O₂, g, hsup, hinf, hmemE, hO₁, hO₂, hz₁, hz₂, hgraph, hmaps, hg0, hganalytic,
      hgsmall, hgderiv⟩ := hImplicit (PositiveEdge L n k a) (PositiveEdge L n k b) O
        (logChartCoordinates m U) hO0 hanalytic hΦ0 honto'
    refine ⟨E, E', O₁, O₂, g, ⟨hsup, hinf, hO₁, hO₂, hz₁, hz₂, ?_, hmaps, hg0, hganalytic, hgsmall,
      hgderiv, ?_⟩, ?_⟩
    · intro X hX X' hX' e
      exact (hOprop _ (hgraph X hX X' hX').1).1 e
    · intro X hX X' hX'
      obtain ⟨hin, hiff⟩ := hgraph X hX X' hX'
      obtain ⟨-, h𝒰, hzero⟩ := hOprop _ hin
      rw [← hiff, hzero, hmemN, hUW]
      exact ⟨fun h => h.2, fun h => ⟨h𝒰, h⟩⟩
    · intro X
      rw [hmemE X]
      constructor
      · rintro ⟨hX, h⟩
        exact ⟨hX, by rw [← hderiv X hX]; exact h⟩
      · rintro ⟨hX, h⟩
        exact ⟨hX, by rw [hderiv X hX]; exact h⟩
  refine ⟨(hGraph L n k a hL hn ha N hsub).1 fun U hU => ?_,
    fun U hU hUW F => ⟨fun hF => ?_, fun hF => ?_⟩⟩
  · obtain ⟨E, E', O₁, O₂, g, hg, -⟩ := hlocal U ((hmemN U).1 hU).1 ((hmemN U).1 hU).2
    exact ⟨E, E', O₁, O₂, g, hg⟩
  · obtain ⟨E, E', O₁, O₂, g, -, hE⟩ := hlocal U hU hUW
    have hle : (fieldCurveData L n k a).tangentSpan N U ≤ E.map (edgeFormLinear L n k a) := by
      refine Submodule.span_le.2 ?_
      rintro v ⟨I, γ, hγ, hγmap, hγ0, rfl⟩
      have hγ' : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ := hγ
      have hI0 : I ∈ 𝓝 (0 : ℝ) := hγ'.1.1.mem_nhds hγ'.1.2.2
      have hcurve := (hCurve L k a b hL ha hb n hn).1 𝒰 m (hDiff L n k a b hL hn ha hb 𝒰 m hm) U hU
        I γ hγ' hγ0
      have hzero : curveTangent (fun s => m (γ s)) = 0 := by
        have hconst : ∀ e, deriv (fun s => m (γ s) e) 0 = 0 := by
          intro e
          have hev : (fun s => m (γ s) e) =ᶠ[𝓝 0] fun _ => W e := by
            filter_upwards [hI0] with s hs
            rw [((hmemN _).1 (hγmap hs)).2]
          rw [hev.deriv_eq]
          simp
        funext e
        simp [curveTangent, extendOddly, hconst]
      have hfix : edgeFormOfPositiveValues (restrictToPositiveEdges (curveTangent γ)) =
          curveTangent γ :=
        edgeForm_restrict (extendOddly_apply_negative _)
      have hreal : restrictToPositiveEdges (curveTangent γ) ∈
          Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a) := by
        intro p _
        have h := ((hFields.1 I hγ'.1).1 (fun s => γ s p.1)
          (fun s hs => (hγ'.2.1 hs).1 p.1 (mem_univ _))
          ((hγ'.2.2 p.1 p.2 0 hγ'.1.2.2).differentiableAt hI0)).2.2.2
        simpa [curveTangent, extendOddly, p.2, restrictToPositiveEdges] using h
      have hXE := (hE _).2 ⟨hreal, by rw [hfix, ← hcurve.2, hzero]; rfl⟩
      exact SetLike.mem_coe.2 (Submodule.mem_map.2 ⟨_, hXE, hfix⟩)
    obtain ⟨X, hX, rfl⟩ := Submodule.mem_map.1 (hle hF)
    obtain ⟨hXreal, hX0⟩ := (hE X).1 hX
    exact ⟨edgeForm_mem_space hoppa hXreal, extendOddly_eq_zero hX0⟩
  · obtain ⟨E, E', O₁, O₂, g, hg, hE⟩ := hlocal U hU hUW
    have hF1 : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra F := hF.1
    have hfix : edgeFormOfPositiveValues (restrictToPositiveEdges F) = F :=
      edgeForm_restrict fun e _ => by rw [hF1.2 e, neg_neg]
    have hreal : restrictToPositiveEdges F ∈
        Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a) :=
      fun p _ => hF1.1 p.1 p.2
    have hXE := (hE _).2 ⟨hreal, by rw [hfix, hF.2]; rfl⟩
    have hT := (hGraph L n k a hL hn ha N hsub).2 U ((hmemN U).2 ⟨hU, hUW⟩) E E' O₁ O₂ g hg _ hXE
    rwa [hfix] at hT
end YangMills.Construction.Tower.SubmersionFibres
end
