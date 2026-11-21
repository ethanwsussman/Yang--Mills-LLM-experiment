import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiable
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
noncomputable section
namespace YangMills.Construction.Tower.AnalyticMapDifferentiable
variable {L n k j : ℕ}
private theorem positive_or_opposite_positive (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ Matrices.ComplexMatrix2.traceless = 3 := by
  have hk : Matrices.ComplexMatrix2.traceless = LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    ext A
    rfl
  have hs : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    intro z
    refine ⟨Matrix.diagonal ![z, 0], ?_⟩
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, ← hk] at h
  simp [Module.finrank_matrix] at h
  exact Nat.add_left_cancel (h.trans (by norm_num : 4 = 1 + 3))
abbrev _root_.YangMills.SharedProofs.p8292 := @finrank_traceless
private theorem nonempty_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by
  obtain ⟨-, ⟨e, -⟩, -⟩ := ((hE L hL k j hj).1 n hn).2
  rcases positive_or_opposite_positive e with h | h
  · exact ⟨⟨e, h⟩⟩
  · exact ⟨⟨e.opposite, h⟩⟩
abbrev _root_.YangMills.SharedProofs.p12312 := @nonempty_positiveEdge
theorem statement_of_charts (hC : Matrices.PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) : AnalyticMapDifferentiableStatement := by
  intro L n k a b hL hn ha hb 𝒰 m hm
  obtain ⟨hopen, hmaps, f₁, f₂, hra⟩ := hm
  let := f₁
  let := f₂
  have := nonempty_positiveEdge hE hL hn ha
  have := nonempty_positiveEdge hE hL hn hb
  let β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ Matrices.ComplexMatrix2.traceless finrank_traceless
  have hread := ((hC (PositiveEdge L n k a) (PositiveEdge L n k b)).2.2.2.2.2.2.2 β).1
  have hfield : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  have hinto : MapsTo (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w)))
      (restrictToPositiveEdges '' 𝒰) (Matrices.specialUnitaryPower (PositiveEdge L n k b)) := by
    rintro _ ⟨U, hU, rfl⟩
    show restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈ _
    rw [hfield hU]
    exact fun c => (hmaps hU).1 c (mem_univ _)
  have hrest : Matrices.PowerExpCharts.IsLocallyHolomorphicRestriction
      (IsHolomorphicToProduct β) asGroupFactors (restrictToPositiveEdges '' 𝒰)
      (fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))) := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k a ⊕ Empty → Matrices.ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hfield hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ β, ?_⟩
    rintro _ ⟨V, hV, rfl⟩ hx
    refine heq ⟨hx, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV).1 c (mem_univ _)
  exact ⟨hopen, hmaps, f₁, f₂, ((hread _ hopen.2).2.2.2 _ hinto hrest).2⟩
end YangMills.Construction.Tower.AnalyticMapDifferentiable
end
