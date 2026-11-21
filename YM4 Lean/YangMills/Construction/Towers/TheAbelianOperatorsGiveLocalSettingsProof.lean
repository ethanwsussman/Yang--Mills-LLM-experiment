import YangMills.Construction.Towers.TheAbelianOperatorsAreShiftedPositiveProof
import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.TheAbelianOperatorsAreLocalFamilies
import YangMills.Construction.Towers.TheAbelianOperatorsGiveLocalSettings
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.Tower.AbelianFieldFacts
open YangMills.Construction.Tower.AbelianFieldDensity
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies.AbelianLocalExpansion
theorem isBoundedBelowBy_addScalar {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : BddOp H} {c z c' : ℝ} (hT : IsBoundedBelowBy T c) (hle : c' ≤ c + z) :
    IsBoundedBelowBy (addScalar T z) c' := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.ShiftedPositiveProof.isBoundedBelowBy_addScalar <;> assumption
variable {L : ℕ}
theorem abs_faceAngle_le {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ} {r : ℝ}
    (hθ : ∀ e, |θ e| ≤ r) (p : FullSpace.Face L 0 0) :
    |FullSpace.faceAngle θ p| ≤ 4 * r := by
  unfold FullSpace.faceAngle FullSpace.edgeDifference
  have h₁ := abs_le.1 (hθ (FullSpace.forwardEdge p.corner p.lowAxis))
  have h₂ := abs_le.1 (hθ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis))
  have h₃ := abs_le.1 (hθ (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis))
  have h₄ := abs_le.1 (hθ (FullSpace.forwardEdge p.corner p.highAxis))
  rw [abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2]
theorem massiveOp_add_boundedBelow
    (hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ)
    {z : ℝ} (hz : 0 < z) :
    ∃ r : ℝ, 0 < r ∧ ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, (∀ e, |θ e| ≤ r) →
      IsBoundedBelowBy (addScalar (AbelianFieldDensity.massiveOp θ) z) (z / 2) := by
  refine ⟨min (Real.pi / 8) (z / 192), lt_min (by positivity) (by positivity), fun θ hθ => ?_⟩
  have hr₁ : min (Real.pi / 8) (z / 192) ≤ Real.pi / 8 := min_le_left _ _
  have hr₂ : min (Real.pi / 8) (z / 192) ≤ z / 192 := min_le_right _ _
  have hang := abs_faceAngle_le (L := L) hθ
  have hK := (hlow θ).1 fun p => (hang p).trans (by linarith)
  have hsup : ⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)| ≤
      4 * min (Real.pi / 8) (z / 192) :=
    Real.iSup_le (fun p => Real.abs_sin_le_abs.trans (hang p)) (by positivity)
  exact isBoundedBelowBy_addScalar hK (by linarith)
theorem laplacianOp_add_boundedBelow
    (hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ)
    {z : ℝ} (hz : 0 < z) :
    ∃ r : ℝ, 0 < r ∧ ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, (∀ e, |θ e| ≤ r) →
      IsBoundedBelowBy (addScalar (laplacianOp θ) z) (z / 2) :=
  ⟨1, one_pos, fun θ _ => isBoundedBelowBy_addScalar (hlow θ).2 (by linarith)⟩
theorem holds (hFam : AbelianOperatorsLocallySmooth)
    (hSp : UnitLatticeIndexedSpaces)
    (hFacts : AbelianFieldFacts.AllFacts) : AbelianOperatorsLocalExpansion := by
  intro z hz
  obtain ⟨C, hC, hfam⟩ := hFam
  refine ⟨C, hC, fun L hL => ?_⟩
  obtain ⟨hvert, hedge⟩ := hfam L hL
  obtain ⟨isV, isE, tails⟩ := hSp L hL z C hz hC
  have hlow : ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ := fun θ =>
    ((hFacts.2.2 L hL z hz).2.2.2 θ).2.2.2.2.2.1
  exact ⟨⟨isV, tails, hvert, laplacianOp_add_boundedBelow hlow hz⟩,
    ⟨isE, tails, hedge, massiveOp_add_boundedBelow hlow hz⟩⟩
end YangMills.Construction.Tower.LocalFamilies.AbelianLocalExpansion
end
