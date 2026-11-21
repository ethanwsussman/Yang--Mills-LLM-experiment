import YangMills.Construction.LawByMomentsOfTheFlow.NumberOfTheFlowNearOne
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.ResponseInTheExpansion.NumbersOfTheChainAreOne
import YangMills.Construction.ResponseInTheExpansion.TheLevelsOfAFlowAreTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
theorem responseCoeffNearOne (hT : TrajectoryData.responseCoeffNearOneStatement)
    (hL : ResponseInTheExpansion.flowStagesAreChainStatement) (hO : ResponseInTheExpansion.chainResponseCoeffsUnique)
    (hR : LevelTestFunctions.CouplingFlowAboveWindow) : responseCoeffNearOneStatement := by
  unfold ResponseInTheExpansion.flowStagesAreChainStatement ResponseInTheExpansion.HoldsOnParameterFamilies at hL
  unfold ResponseInTheExpansion.chainResponseCoeffsUnique ResponseInTheExpansion.HoldsOnParameterFamilies at hO
  unfold responseCoeffNearOneStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, g₁⟩ := hT a ha
  obtain ⟨L₂, r₂, C₂, p₂, g₂⟩ := hL a ha
  obtain ⟨L₃, r₃, C₃, p₃, g₃⟩ := hO a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)), ?_⟩
  intro L hodd hLL T hTa hTL hD hCS hOn hrt hC Kr hFit
  obtain ⟨Kt, hKt, y₁, f₁⟩ := g₁ L hodd ((le_max_left _ _).trans hLL) T hTa hTL hD hCS hOn (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y₂, f₂⟩ := g₂ L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hLL) T hTa hTL hD hCS hOn
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  obtain ⟨y₃, f₃⟩ := g₃ L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hLL) T hTa hTL hD hCS hOn
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) (((le_max_right _ _).trans (le_max_right _ _)).trans hC)
  refine ⟨max (max y₁ y₂) (max y₃ T.floorMin), fun y hy hRt hWy gg hg hgy k _ _ _ R d _ => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₄ : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  refine ⟨fun _ => 6 * Kt.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side), 1, y, one_pos, le_rfl, fun S t ht => ?_⟩
  have hAdm : LevelTestFunctions.AdmissibleStep (T.stepParameters y) := ⟨hD.fits y hy₄, hRt, hWy⟩
  obtain ⟨hxK, -⟩ := hR (T.stepParameters y) hAdm gg hg hgy S.β S.data.windowLevel S.window_le S.passage
  have hflow : ∀ j ≤ t, y ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) S.β j := fun j hj => hxK j (hj.trans ht)
  obtain ⟨al, hal, hb, -⟩ := f₁ y hy₁ hRt hWy S.β t hflow
  have hch := f₂ y hy₂ hRt hWy Kr (hFit y) S.β S.labelFacts S.initial S.data.windowLevel S.isInitial S.onFlow
  have hch' : ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr S.β t
      fun j => (ResponseInTheExpansion.flowStages T y S.β S.labelFacts S.initial j).2.coeff :=
    ⟨hch.zero_eq, fun j hj => hch.bounds j (hj.trans ht)⟩
  have e₁ := f₃ y hy₃ hRt hWy Kr Kt (hFit y) (hKt y) S.β t _ al hflow hch' hal t le_rfl
  have e₂ : (S.resp t).coeff = (ResponseInTheExpansion.flowStages T y S.β S.labelFacts S.initial t).2.coeff :=
    congrArg (fun z => z.2.coeff) (S.stage_eq t ht)
  show |(S.resp t).coeff - 1| ≤ 6 * Kt.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) * S.coupling t ^ (-(1 / 2) : ℝ)
  rw [e₂, e₁]
  exact hb
end YangMills.Construction.MomentLaw
end
