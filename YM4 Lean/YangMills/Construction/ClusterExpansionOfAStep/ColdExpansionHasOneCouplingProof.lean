import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionHasOneCoupling
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParameters
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingUniqueness
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
theorem stepWeight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem isCurvatureFamily_of_coldExpansion {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity} (h : ColdExpansion ℓ t x D f) : IsCurvatureFamily ℓ (max ℓ.E ℓ.E₃) f where
  smooth := h.smooth
  gauge := h.gauge
  translation := h.translation
  decay := fun n _ hn y W hc k c X hk1 hk3 hu => by
    refine (h.decay n hn y W hc k c X hk1 hk3 hu).trans ?_
    refine div_le_div_of_nonneg_right ?_ (stepWeight_pos ℓ _).le
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  local_density := fun n n' _ _ hn hn' y y' W W' m h2 h2' hc hc' ag k b X hk hb hu => by
    refine (h.local_density n n' hn hn' y y' W W' m h2 h2' hc hc' ag k b X hk hb hu).trans ?_
    exact div_le_div_of_nonneg_right (le_max_left _ _) (stepWeight_pos ℓ _).le
theorem coldExpansionCouplingUnique_of_couplingIsUnique (h : CouplingIsUnique) :
    ColdExpansionCouplingUnique :=
  fun T hT y hy t x' x'' D f' f'' r' r'' =>
    h T hT y hy t x' x'' _ _ D f' f'' (isCurvatureFamily_of_coldExpansion r')
      (isCurvatureFamily_of_coldExpansion r'')
      r'.no_curvature_term r''.no_curvature_term r'.form r''.form
end YangMills.Construction.CouplingUniqueness
end
