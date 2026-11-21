import YangMills.Construction.LawInAState.TheNumbersOfTheChainAreNearOne
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstantProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChainResponses
private theorem isCurvatureFamily_of_coldBounds {ℓ : TorusLumps.StepParameters} {E E₃ : ℝ} {f : TorusLumps.LocalDensity}
    (hE : E ≤ E₃) (h : WeightedResponses.ColdDensityBounds ℓ E E₃ f) : TorusLumps.IsCurvatureFamily ℓ E₃ f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness.isCurvatureFamily_of_coldDensityBounds <;> assumption
private theorem hasNoLimitFormTerm_of_coldBounds {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible)
    (hSO : TorusLumps.SecondOrderAtAbelianFields) {E E₃ : ℝ} {f : TorusLumps.LocalDensity}
    (hE : E ≤ E₃) (h : WeightedResponses.ColdDensityBounds ℓ E E₃ f) : CouplingUniqueness.HasNoLimitFormTerm f := by
  intro A A' hA hA'
  have hs := (hSO ℓ hfit E₃ f (isCurvatureFamily_of_coldBounds hE h)).2.2.2.2.1 A A' hA hA'
  have h0 := h.no_curvature_term A A' hA hA'
  have h1 := hs.hasSum
  rw [h0] at h1
  exact h1
private theorem coeff_unique (hOC : CouplingUniqueness.CouplingIsUnique) (hSO : TorusLumps.SecondOrderAtAbelianFields)
    (T : RenormalizationStepParameters.ParameterAssignment) (hT : T.Admissible) (y : ℝ) (hy : T.floorMin ≤ y)
    (K K' : WeightedResponses.ResponseParameters) (t : ℕ) (x c c' : ℝ)
    (P : WeightedResponses.ColdResponse (T.stepParameters y).side (t + 1)) (Ra Rb Ra' Rb' : TorusLumps.LocalDensity)
    (hη : 0 < K.η₃) (hη1 : K.η₃ ≤ 1) (hKb : 0 ≤ K.Kb) (hη' : 0 < K'.η₃) (hη1' : K'.η₃ ≤ 1) (hKb' : 0 ≤ K'.Kb)
    (hx : 0 < x) (h₁ : WeightedResponses.ColdResponseBounds (T.stepParameters y) K (t + 1) x c P Ra Rb)
    (h₂ : WeightedResponses.ColdResponseBounds (T.stepParameters y) K' (t + 1) x c' P Ra' Rb') : c = c' := by
  have hfit := hT.fits y hy
  have hle : ∀ {Q : WeightedResponses.ResponseParameters}, 0 < Q.η₃ → Q.η₃ ≤ 1 → 0 ≤ Q.Kb →
      Q.Kb * x⁻¹ ≤ Q.Kb * x⁻¹ / Q.η₃ := by
    intro Q e1 e2 e3
    have e4 : 0 ≤ Q.Kb * x⁻¹ := mul_nonneg e3 (inv_nonneg.mpr hx.le)
    rw [le_div_iff₀ e1]
    nlinarith
  let D : TorusLumps.TorusFunctional := fun n W =>
    if hn : n = 0 then 1 else
      haveI : NeZero n := ⟨hn⟩
      Real.exp (∑ y, WeightedResponses.centeredResponse P n y W (WeightedResponses.constOneWeight _))
  have hflat0 : ∀ (n : ℕ) [NeZero n], ∑ y, WeightedResponses.centeredResponse P n y (TorusFields.trivialField n)
      (WeightedResponses.constOneWeight _) = 0 := by
    intro n _
    simp [WeightedResponses.centeredResponse]
  have hD : ∀ (c₀ : ℝ) (R : TorusLumps.LocalDensity), (∀ n [NeZero n], (T.stepParameters y).n₀ ≤ n →
      ∀ W : TorusFields.TorusField n, TorusFields.IsCold (T.stepParameters y).threshold W →
        ∑ y, WeightedResponses.centeredResponse P n y W (WeightedResponses.constOneWeight _) =
          c₀ * TorusFields.actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ W +
            ∑ y, TorusLumps.centered R n y W) →
      CouplingUniqueness.HasColdForm (T.stepParameters y) (t + 1) (-c₀) D R := by
    intro c₀ R hR n _ hn W hW
    have hne : n ≠ 0 := NeZero.ne n
    have e₁ : D n W = Real.exp (∑ y, WeightedResponses.centeredResponse P n y W (WeightedResponses.constOneWeight _)) :=
      dif_neg hne
    have e₂ : D n (TorusFields.trivialField n) = Real.exp (∑ y, WeightedResponses.centeredResponse P n y
        (TorusFields.trivialField n) (WeightedResponses.constOneWeight _)) := dif_neg hne
    rw [e₁, e₂, Real.log_exp, Real.log_exp, hflat0 n, hR n hn W hW]
    ring
  have e₁ := hle hη hη1 hKb
  have e₂ := hle hη' hη1' hKb'
  have := hOC T hT y hy t (-c) (-c') _ _ D Rb Rb' (isCurvatureFamily_of_coldBounds e₁ h₁.total_family)
    (isCurvatureFamily_of_coldBounds e₂ h₂.total_family) (hasNoLimitFormTerm_of_coldBounds hfit hSO e₁ h₁.total_family)
    (hasNoLimitFormTerm_of_coldBounds hfit hSO e₂ h₂.total_family) (hD c Rb h₁.share_total) (hD c' Rb' h₂.share_total)
  exact neg_injective this
private theorem coldResponseChain_congr (ℓ : TorusLumps.StepParameters) (β : ℝ) (x c c' : ℕ → ℝ) :
    ∀ t : ℕ, (∀ i < t, c i = c' i) →
      ResponseInTheExpansion.coldResponseChain ℓ β x c t = ResponseInTheExpansion.coldResponseChain ℓ β x c' t
  | 0, _ => rfl
  | t + 1, h => by
    have e := coldResponseChain_congr ℓ β x c c' t fun i hi => h i (by omega)
    show ResponseInTheExpansion.stepColdResponse ℓ (x t) (c t) t (WeightedResponses.chainFunctional ℓ β x t)
        (ResponseInTheExpansion.coldResponseChain ℓ β x c t) =
      ResponseInTheExpansion.stepColdResponse ℓ (x t) (c' t) t (WeightedResponses.chainFunctional ℓ β x t)
        (ResponseInTheExpansion.coldResponseChain ℓ β x c' t)
    rw [e, h t (by omega)]
theorem chainResponseCoeffNearOne (hNear : TrajectoryData.responseCoeffNearOneStatement)
    (hOC : CouplingUniqueness.CouplingIsUnique) (hSO : TorusLumps.SecondOrderAtAbelianFields) :
    chainResponseCoeffNearOneStatement := by
  intro a ha
  obtain ⟨L₀, r₀, c₀, p₀, g⟩ := hNear a ha
  refine ⟨L₀, r₀, c₀, p₀, fun L hodd hL T hTa hTL hD hC hH hr hc => ?_⟩
  obtain ⟨Kr₀, hKr₀, y₀, k₀⟩ := g L hodd hL T hTa hTL hD hC hH hr hc
  refine ⟨max y₀ T.floorMin, fun y hy hR hW Kr hKr β k c hrun hcoeff => ?_⟩
  have hy₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hyT : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hfit := hD.fits y hyT
  obtain ⟨d, hcoeff₀, h1, h2⟩ := k₀ y hy₀ hR hW β k hrun
  have hK₀ := hKr₀ y
  have hy1 : (1 : ℝ) ≤ y := hfit.y₁_ge
  have heq : ∀ j ≤ k, c j = d j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      cases j with
      | zero => rw [hcoeff.zero_eq, hcoeff₀.zero_eq]
      | succ t =>
        obtain ⟨Ra, Rb, c₁⟩ := hcoeff.bounds (t + 1) hj
        obtain ⟨Ra', Rb', c₂⟩ := hcoeff₀.bounds (t + 1) hj
        have e := coldResponseChain_congr (T.stepParameters y) β (ResponseInTheExpansion.flowCouplings (T.stepParameters y) β) c d
          (t + 1) fun i hi => ih i hi (by omega)
        rw [e] at c₁
        exact coeff_unique hOC hSO T hD y hyT Kr Kr₀ t _ _ _ _ _ _ _ _ hKr.η₃_pos hKr.η₃_le hKr.Kb_nonneg
          hK₀.η₃_pos hK₀.η₃_le hK₀.Kb_nonneg (lt_of_lt_of_le (by linarith) (hrun (t + 1) hj)) c₁ c₂
  rw [heq k le_rfl]
  exact h1.trans h2
end YangMills.Construction.ChainResponses
end
