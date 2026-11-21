import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstantProof
import YangMills.Construction.ResponseInTheExpansion.ColdHalfOfTheResponseProof
import YangMills.Construction.ResponseInTheExpansion.NumbersOfTheChainAreOne
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponsesAreCarriedByAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
namespace ChainCoeffUniqueness
open TorusLumps TorusFields WeightedResponses CouplingUniqueness ShareFamilies RenormalizationStepParameters BlockAverages
section
variable {ℓ : StepParameters}
private theorem isCurvatureFamily_of_coldBounds {E E₃ : ℝ} {f : LocalDensity} (hE : E ≤ E₃)
    (h : ColdDensityBounds ℓ E E₃ f) : IsCurvatureFamily ℓ E₃ f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness.isCurvatureFamily_of_coldDensityBounds <;> assumption
private theorem sum_centeredResponse_invariant {t : ℕ} {P : ColdResponse ℓ.side t} (hσ : 0 < ℓ.threshold)
    (hP : UnitResponseInvariant ℓ P) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (g : TorusIsometry)
    (W W' : TorusField n) (hW : IsCold ℓ.threshold W) (hc : g.Transports W W') :
    ∑ y, centeredResponse P n y W' (constOneWeight _) = ∑ y, centeredResponse P n y W (constOneWeight _) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness.sum_centeredResponse_invariant <;> assumption
private theorem remainder_noLimitFormTerm (hfit : ℓ.Admissible) (hON : InvariantFamilyCurvatureForm) {t : ℕ}
    {P : ColdResponse ℓ.side (t + 1)} {Ca : ℝ} (hS : LevelShareBounds ℓ t Ca)
    (hSc : SumInvariantUnderIsometries ℓ (levelShareFamily ℓ.coupling ℓ.side (t + 1)))
    (hP : UnitResponseInvariant ℓ P) {E E₃ c₀ : ℝ} {R : LocalDensity} (hE : E ≤ E₃) (hR : ColdDensityBounds ℓ E E₃ R)
    (hT : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
      ∑ y, centeredResponse P n y W (constOneWeight _) =
        c₀ * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ W + ∑ y, centered R n y W) :
    IsCurvatureFamily ℓ E₃ R ∧ HasNoLimitFormTerm R := by
  have hσ := hfit.σ_pos
  have hc := isCurvatureFamily_of_coldBounds hE hR
  have hinv : SumInvariantUnderIsometries ℓ R := by
    intro n _ hn g W W' hW hW' hg
    have e₁ := hT n hn W hW
    have e₂ := hT n hn W' hW'
    have e₃ := sum_centeredResponse_invariant hσ hP hn g W W' hW hg
    have e₄ := hSc n hn g W W' hW hW' hg
    rw [hS.sum_centered_eq n hn W' hW', hS.sum_centered_eq n hn W hW] at e₄
    rw [e₁, e₂, e₄] at e₃
    linarith
  obtain ⟨-, b₀, hb₀⟩ := hON ℓ hfit E₃ R hc hinv
  refine ⟨hc, fun A A' hA hA' => ?_⟩
  have h1 := hb₀ A A' hA hA'
  have h2 := hR.no_curvature_term A A' hA hA'
  rw [h1.tsum_eq] at h2
  rw [h2] at h1
  exact h1
private theorem coeff_eq_of_bounds (hfit : ℓ.Admissible)
    (hOC : ∀ (t : ℕ) (x' x'' C C' : ℝ) (D : TorusFunctional) (f' f'' : LocalDensity),
      IsCurvatureFamily ℓ C f' → IsCurvatureFamily ℓ C' f'' → HasNoLimitFormTerm f' → HasNoLimitFormTerm f'' →
      HasColdForm ℓ (t + 1) x' D f' → HasColdForm ℓ (t + 1) x'' D f'' → x' = x'')
    (hON : InvariantFamilyCurvatureForm) (K K' : ResponseParameters) (hK : K.Admissible ℓ)
    (hK' : K'.Admissible ℓ) (t : ℕ) (x c c' Ca : ℝ) (P : ColdResponse ℓ.side (t + 1))
    (Ra Rb Ra' Rb' : LocalDensity) (hx : 0 < x)
    (hS : LevelShareBounds ℓ t Ca) (hSc : SumInvariantUnderIsometries ℓ (levelShareFamily ℓ.coupling ℓ.side (t + 1)))
    (hP : UnitResponseInvariant ℓ P) (h₁ : ColdResponseBounds ℓ K (t + 1) x c P Ra Rb)
    (h₂ : ColdResponseBounds ℓ K' (t + 1) x c' P Ra' Rb') : c = c' := by
  have hbound : ∀ K₀ : ResponseParameters, K₀.Admissible ℓ → K₀.Kb * x⁻¹ ≤ K₀.Kb * x⁻¹ / K₀.η₃ := by
    intro K₀ h₀
    have hE0 : 0 ≤ K₀.Kb * x⁻¹ := mul_nonneg h₀.Kb_nonneg (inv_nonneg.mpr hx.le)
    rw [le_div_iff₀ h₀.η₃_pos]
    nlinarith [h₀.η₃_le]
  let D : TorusFunctional := fun n W =>
    if hn : n = 0 then 1 else
      haveI : NeZero n := ⟨hn⟩
      Real.exp (∑ y, centeredResponse P n y W (constOneWeight _))
  have htriv0 : ∀ (n : ℕ) [NeZero n], ∑ y, centeredResponse P n y (trivialField n) (constOneWeight _) = 0 := by
    intro n _
    simp [centeredResponse]
  have hD : ∀ (c₀ : ℝ) (R : LocalDensity), (∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
      ∑ y, centeredResponse P n y W (constOneWeight _) =
        c₀ * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ W + ∑ y, centered R n y W) →
      HasColdForm ℓ (t + 1) (-c₀) D R := by
    intro c₀ R hR n _ hn W hW
    have hne : n ≠ 0 := NeZero.ne n
    have e₁ : D n W = Real.exp (∑ y, centeredResponse P n y W (constOneWeight _)) := dif_neg hne
    have e₂ : D n (trivialField n) =
        Real.exp (∑ y, centeredResponse P n y (trivialField n) (constOneWeight _)) := dif_neg hne
    rw [e₁, e₂, Real.log_exp, Real.log_exp, htriv0 n, hR n hn W hW]
    ring
  obtain ⟨c₁, n₁⟩ := remainder_noLimitFormTerm hfit hON hS hSc hP (hbound K hK) h₁.total_family h₁.share_total
  obtain ⟨c₂, n₂⟩ := remainder_noLimitFormTerm hfit hON hS hSc hP (hbound K' hK') h₂.total_family h₂.share_total
  have := hOC t (-c) (-c') _ _ D Rb Rb' c₁ c₂ n₁ n₂ (hD c Rb h₁.share_total) (hD c' Rb' h₂.share_total)
  exact neg_injective this
end
private theorem coldResponseChain_congr (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ) {c c' : ℕ → ℝ} :
    ∀ t : ℕ, (∀ i < t, c i = c' i) → coldResponseChain ℓ β x c t = coldResponseChain ℓ β x c' t
  | 0, _ => rfl
  | t + 1, h => by
    show stepColdResponse ℓ (x t) (c t) t (chainFunctional ℓ β x t) (coldResponseChain ℓ β x c t) =
      stepColdResponse ℓ (x t) (c' t) t (chainFunctional ℓ β x t) (coldResponseChain ℓ β x c' t)
    rw [h t (Nat.lt_succ_self t), coldResponseChain_congr ℓ β x t fun i hi => h i (Nat.lt_succ_of_lt hi)]
private theorem levelShareBounds_of_admissible {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ}
    (hy : T.floorMin ≤ y) (t : ℕ) (hSh : LevelSharesFormCurvatureFamily)
    (hForm : HasCurvatureForm (levelShareFamily T.coupling T.side (t + 1)) 1) (hFlat : flatTopVanishingStatement) :
    LevelShareBounds (T.stepParameters y) t (weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ColdResponseCoefficient.levelShareBounds_of_admissible <;> assumption
end ChainCoeffUniqueness
open TorusLumps TorusFields WeightedResponses CouplingUniqueness ShareFamilies RenormalizationStepParameters BlockAverages
  ChainCoeffUniqueness
theorem chainResponseCoeffsUnique_holds (hOC : CouplingIsUnique) (hON : InvariantFamilyCurvatureForm)
    (hSh : LevelSharesFormCurvatureFamily) (hFm : LevelSharesHaveUnitCurvatureForm)
    (hFlat : flatTopVanishingStatement)
    (hCar : SmallTorusCopies.responseIsometryInvariantStatement) : chainResponseCoeffsUnique := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ T _ _ hT _ _ _ _ => ?_⟩
  refine ⟨max T.floorMin 1, fun y hy _ _ K K' hK hK' β k c c' hrun h h' j => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy₁ : 1 ≤ y := (le_max_right _ _).trans hy
  have hfit := hT.fits y hy₀
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    cases j with
    | zero => rw [h.zero_eq, h'.zero_eq]
    | succ j =>
      have hsame := coldResponseChain_congr (T.stepParameters y) β (flowCouplings (T.stepParameters y) β)
        (c := c) (c' := c') (j + 1) fun i hi => ih i hi (by omega)
      obtain ⟨Ra, Rb, e⟩ := h.bounds (j + 1) hj
      obtain ⟨Ra', Rb', e'⟩ := h'.bounds (j + 1) hj
      rw [← hsame] at e'
      have hx : 0 < flowCouplings (T.stepParameters y) β (j + 1) := by
        have := hrun (j + 1) hj
        linarith
      exact coeff_eq_of_bounds hfit (hOC T hT y hy₀) hON K K' hK hK' j _ _ _ _ _ Ra Rb Ra' Rb' hx
        (levelShareBounds_of_admissible hT hy₀ j hSh (hFm T hT j) hFlat) (hSh T hT y hy₀ j).2.1
        (fun n _ hn g y' W W' _ hc => hCar (T.stepParameters y) hfit β _ c (j + 1) n hn g W W' _ _ y' hc
          fun _ _ _ => rfl) e e'
end YangMills.Construction.ResponseInTheExpansion
end
