import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParameters
import YangMills.Construction.ClusterExpansionOfAStep.OneNumberOfACarriedFamily
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness
open BlockAverages TorusFields TorusLumps ShareFamilies CouplingUniqueness RenormalizationStepParameters WeightedResponses
section
variable {ℓ : StepParameters}
theorem stepWeight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
theorem trivialField_transports (g : TorusIsometry) (n : ℕ) : g.Transports (trivialField n) (trivialField n) := by
  intro x k
  split_ifs <;> simp [trivialField]
theorem isCurvatureFamily_of_coldDensityBounds {E E₃ : ℝ} {f : LocalDensity} (hE : E ≤ E₃)
    (h : ColdDensityBounds ℓ E E₃ f) : IsCurvatureFamily ℓ E₃ f := by
  refine ⟨h.smooth, h.gauge, h.translation, fun n _ hn y W hW k c X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu => ?_⟩
  · refine (h.decay n hn y W hW k c X hk1 hk3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (stepWeight_pos ℓ _).le
    split_ifs
    · exact le_rfl
    · exact hE
  · refine (h.local_density n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans ?_
    exact div_le_div_of_nonneg_right hE (stepWeight_pos ℓ _).le
theorem sum_centeredResponse_invariant {t : ℕ} {P : ColdResponse ℓ.side t} (hσ : 0 < ℓ.threshold)
    (hP : UnitResponseInvariant ℓ P) {n : ℕ}
    [NeZero n] (hn : ℓ.n₀ ≤ n) (g : TorusIsometry) (W W' : TorusField n) (hW : IsCold ℓ.threshold W)
    (hc : g.Transports W W') :
    ∑ y, centeredResponse P n y W' (constOneWeight _) = ∑ y, centeredResponse P n y W (constOneWeight _) := by
  have hb : Function.Bijective (g.mapSite (n := n)) :=
    (Finite.injective_iff_bijective).mp (mapSite_injective (g := g))
  rw [← hb.sum_comp fun y => centeredResponse P n y W' (constOneWeight _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [centeredResponse]
  rw [hP n hn g y W W' hW hc, hP n hn g y (trivialField n) (trivialField n) (trivialField_isCold hσ n)
    (trivialField_transports g n)]
end
theorem coldResponseCoeff_unique (ℓ : StepParameters) (hfit : ℓ.Admissible)
    (hOC : ∀ (t : ℕ) (x' x'' C C' : ℝ) (D : TorusFunctional) (f' f'' : LocalDensity),
      IsCurvatureFamily ℓ C f' → IsCurvatureFamily ℓ C' f'' → HasNoLimitFormTerm f' → HasNoLimitFormTerm f'' →
      HasColdForm ℓ (t + 1) x' D f' → HasColdForm ℓ (t + 1) x'' D f'' → x' = x'')
    (hON : InvariantFamilyCurvatureForm) (K : ResponseParameters) (t : ℕ) (x al al' Ca : ℝ)
    (P : ColdResponse ℓ.side (t + 1)) (Ra Rb Ra' Rb' : LocalDensity)
    (hη : 0 < K.η₃) (hη1 : K.η₃ ≤ 1) (hKb : 0 ≤ K.Kb) (hx : 0 < x) (hS : LevelShareBounds ℓ t Ca)
    (hSc : SumInvariantUnderIsometries ℓ (levelShareFamily ℓ.coupling ℓ.side (t + 1)))
    (hP : UnitResponseInvariant ℓ P)
    (h₁ : ColdResponseBounds ℓ K (t + 1) x al P Ra Rb) (h₂ : ColdResponseBounds ℓ K (t + 1) x al' P Ra' Rb') :
    al = al' := by
  have hσ := hfit.σ_pos
  set E : ℝ := K.Kb * x⁻¹ with hE
  have hE0 : 0 ≤ E := mul_nonneg hKb (inv_nonneg.mpr hx.le)
  have hEη : E ≤ E / K.η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  let D : TorusFunctional := fun n W =>
    if hn : n = 0 then 1 else
      haveI : NeZero n := ⟨hn⟩
      Real.exp (∑ y, centeredResponse P n y W (constOneWeight _))
  have hflat0 : ∀ (n : ℕ) [NeZero n], ∑ y, centeredResponse P n y (trivialField n) (constOneWeight _) = 0 := by
    intro n _
    simp [centeredResponse]
  have hD : ∀ (al₀ : ℝ) (R : LocalDensity), (∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n,
      IsCold ℓ.threshold W →
      ∑ y, centeredResponse P n y W (constOneWeight _) =
        al₀ * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ W + ∑ y, centered R n y W) →
      HasColdForm ℓ (t + 1) (-al₀) D R := by
    intro al₀ R hR n _ hn W hW
    have hne : n ≠ 0 := NeZero.ne n
    have e₁ : D n W = Real.exp (∑ y, centeredResponse P n y W (constOneWeight _)) := dif_neg hne
    have e₂ : D n (trivialField n) =
        Real.exp (∑ y, centeredResponse P n y (trivialField n) (constOneWeight _)) := dif_neg hne
    rw [e₁, e₂, Real.log_exp, Real.log_exp, hflat0 n, hR n hn W hW]
    ring
  have key : ∀ (al₀ : ℝ) (R : LocalDensity), ColdDensityBounds ℓ E (E / K.η₃) R →
      (∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
        ∑ y, centeredResponse P n y W (constOneWeight _) =
          al₀ * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ W + ∑ y, centered R n y W) →
      IsCurvatureFamily ℓ (E / K.η₃) R ∧ HasNoLimitFormTerm R := by
    intro al₀ R hR hT
    have hc := isCurvatureFamily_of_coldDensityBounds hEη hR
    have hcar : SumInvariantUnderIsometries ℓ R := by
      intro n _ hn g W W' hW hW' hg
      have e₁ := hT n hn W hW
      have e₂ := hT n hn W' hW'
      have e₃ := sum_centeredResponse_invariant hσ hP hn g W W' hW hg
      have e₄ := hSc n hn g W W' hW hW' hg
      rw [hS.sum_centered_eq n hn W' hW', hS.sum_centered_eq n hn W hW] at e₄
      rw [e₁, e₂, e₄] at e₃
      linarith
    obtain ⟨-, b₀, hb₀⟩ := hON ℓ hfit (E / K.η₃) R hc hcar
    refine ⟨hc, fun A A' hA hA' => ?_⟩
    have h1 := hb₀ A A' hA hA'
    have h2 := hR.no_curvature_term A A' hA hA'
    rw [h1.tsum_eq] at h2
    rw [h2] at h1
    exact h1
  obtain ⟨c₁, n₁⟩ := key al Rb h₁.total_family h₁.share_total
  obtain ⟨c₂, n₂⟩ := key al' Rb' h₂.total_family h₂.share_total
  have := hOC t (-al) (-al') (E / K.η₃) (E / K.η₃) D Rb Rb' c₁ c₂ n₁ n₂
    (hD al Rb h₁.share_total) (hD al' Rb' h₂.share_total)
  exact neg_injective this
theorem coldResponseCoeffUnique (hOC : CouplingIsUnique)
    (hON : InvariantFamilyCurvatureForm) : ColdResponseCoeffUniqueStatement := by
  intro T hT y hy K t x al al' Ca P Ra Rb Ra' Rb' hη hη1 hKb hx hS hSc hP h₁ h₂
  exact coldResponseCoeff_unique (T.stepParameters y) (hT.fits y hy) (hOC T hT y hy) hON K t x al al' Ca P
    Ra Rb Ra' Rb' hη hη1 hKb hx hS hSc hP h₁ h₂
end YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness
end
