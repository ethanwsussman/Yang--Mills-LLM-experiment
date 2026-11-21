import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopAtTheExpansion
import YangMills.Construction.TwoPoints.ShapeConstantInTheUnitInterval
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open YangMills.Construction.TestFunctions
open YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.LimitTheorem YangMills.Construction.SeparatedTuples
private theorem isShapedBump_of_shape_le {d ϑ' ϑ : ℝ} (hd : 0 < d) (hϑ : 0 < ϑ') (hle : ϑ' ≤ ϑ)
    {x : Fin 4 → ℝ} {f : (Fin 4 → ℝ) → ℝ}
    (hf : IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d ϑ x f) :
    IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d ϑ' x f := by
  obtain ⟨hLip, hnonneg, hne, hsupp, hmass, hconst⟩ := hf
  have hN : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  refine ⟨hLip, hnonneg, hne, hsupp, le_trans ?_ hmass, le_trans hconst ?_⟩
  · have hd4 : 0 ≤ d ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hN) hd4
  · exact div_le_div_of_nonneg_left hN (mul_pos hϑ hd) (mul_le_mul_of_nonneg_right hle hd.le)
private theorem separatedPairsR4_antitone_shape {d ϑ' ϑ : ℝ} (hd : 0 < d) (hϑ : 0 < ϑ') (hle : ϑ' ≤ ϑ) :
    separatedPairsR4 d ϑ ⊆ separatedPairsR4 d ϑ' := by
  rintro p ⟨x₁, x₂, h₁, h₂, hlow, hhigh⟩
  exact ⟨x₁, x₂, isShapedBump_of_shape_le hd hϑ hle h₁, isShapedBump_of_shape_le hd hϑ hle h₂, hlow, hhigh⟩
private theorem twoPointLawHolds_of_shape_le {ϑ' ϑ d₀ : ℝ} {ηBar : ℝ → ℝ} {σ : TupleFunctional}
    (hϑ : 0 < ϑ') (hle : ϑ' ≤ ϑ)
    (h : TwoPointLawHolds ϑ' d₀ ηBar σ) : TwoPointLawHolds ϑ d₀ ηBar σ :=
  fun d hd f k hp h₁ h₂ => h d hd f k (separatedPairsR4_antitone_shape hd.1 hϑ hle hp) h₁ h₂
private theorem conclusion_of_shape_le {M ϑ' ϑ d₀ : ℝ} {ηBar : ℝ → ℝ} {K : LimitConstants} {L : ℕ}
    {IsPair : ℕ+ → ℝ → Prop} {Q : PairSequence L IsPair} {S : CumulantFamily} (hϑ : 0 < ϑ') (hle : ϑ' ≤ ϑ)
    (h : ErgodicDecompositionConclusion M ϑ' d₀ ηBar K Q S) :
    ErgodicDecompositionConclusion M ϑ d₀ ηBar K Q S where
  limit :=
    { h.limit with
      conditions :=
        { h.limit.conditions with
          twoPointLaw := twoPointLawHolds_of_shape_le hϑ hle h.limit.conditions.twoPointLaw
          twoPoint_pos := fun d hd X hX =>
            h.limit.conditions.twoPoint_pos d hd X (separatedPairsR4_antitone_shape hd.1 hϑ hle hX) } }
  decomposition := h.decomposition
  onePoint := h.onePoint
  components := fun A hA ξ =>
    { h.components A hA ξ with
      twoPointLaw := twoPointLawHolds_of_shape_le hϑ hle (h.components A hA ξ).twoPointLaw }
theorem topAtAdmissibleParams_holds (hS : SystemFromTotalDensities)
    (hT : SystemsWithFiveBounds.MainTheorem.Statement)
    (hC : TwoPoints.Shapes.ShapeConstMemIoc.Statement) : topAtAdmissibleParamsStatement := by
  refine HoldsAtAdmissibleParameters.mono hS fun T y _ h => ?_
  obtain ⟨h4, h5, h6, h7⟩ := h
  refine ⟨h4, h5, h6, fun Bs hBs => ?_⟩
  obtain ⟨c₅, lam, top, hc, hl, ht, hg, hY⟩ := h7 Bs hBs
  refine ⟨c₅, lam, top, hc, hl, ht, hg, fun m ϑ hϑ => ?_⟩
  have h0 : 0 < TwoPoints.Shapes.shapeConst := hC.2.2.2.2.2.2.1
  have hpos : 0 < min ϑ TwoPoints.Shapes.shapeConst := lt_min hϑ.1 h0
  obtain ⟨Y, hYs, hF⟩ := hY m (min ϑ TwoPoints.Shapes.shapeConst)
    ⟨hpos, le_trans (min_le_left _ _) hϑ.2⟩ (min_le_right _ _)
  refine ⟨Y, hYs, hF, ?_⟩
  obtain ⟨K, hK⟩ := hT Y
  refine ⟨K, fun g hg' => ?_⟩
  obtain ⟨k₁, k₂, k₃, k₄⟩ := hK g hg'
  refine ⟨k₁, k₂, k₃, fun Q S hQ => ?_⟩
  have := k₄ Q S hQ
  rw [hYs.shape_eq] at this
  exact conclusion_of_shape_le hpos (min_le_left _ _) this
end YangMills.Construction.TotalDensities
end
