import YangMills.Construction.LawByMomentsOfTheFlow.PagesJoin
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
private theorem forAll_parameterFacts : ForAllParameters ParameterFacts := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hL _ T hTa hTL hD hS hH _ _ K hK => ?_⟩
  refine ⟨T.floorMin, fun y hy hR _ g _ _ k _ h2 _ R d _ => ?_⟩
  exact ⟨hD, hS, hH, hy, hR, hK, h2⟩
private theorem forAll_and (P Q : MomentParameters → Prop) (hP : ForAllParameters P)
    (hQ : ForAllParameters Q) : ForAllParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
theorem parameterStatementsCombine_holds : parameterStatementsCombine := by
  refine ⟨forAll_and, ?_, ?_, forAll_parameterFacts⟩
  · intro P Q hPQ hP a ha
    obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := forAll_and _ _ hP forAll_parameterFacts a ha
    refine ⟨L₁, r₁, C₁, hr₁, fun L hL hLL T hTa hTL hD hS hH hrt hCd K hK => ?_⟩
    obtain ⟨y₁, g₁⟩ := h₁ L hL hLL T hTa hTL hD hS hH hrt hCd K hK
    refine ⟨y₁, fun y hy hR hW g hg hgy k _ h2 h8 R d hd => ?_⟩
    obtain ⟨q₁, q₂⟩ := g₁ y hy hR hW g hg hgy k h2 h8 R d hd
    exact hPQ _ q₂ q₁
  · intro P hP a ha
    obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hP a ha
    refine ⟨L₁, r₁, C₁, hr₁, fun L hL hLL T hTa hTL hD hS hH hrt hCd K hK => ?_⟩
    obtain ⟨y₁, g₁⟩ := h₁ L hL hLL T hTa hTL hD hS hH hrt hCd
    refine ⟨y₁, fun y hy hR hW g hg hgy k _ h2 h8 R d hd => ?_⟩
    exact g₁ y hy hR hW
end YangMills.Construction.MomentLaw
end
