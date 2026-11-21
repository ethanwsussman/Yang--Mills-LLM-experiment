import YangMills.Construction.InfiniteLattice.DataOfTheComparisonOfABoxWithATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace TermsInBoxes
def Statement : Prop :=
  ∀ d : BoxTorusComparisonData,
    (∀ v : d.translationGroup, (BoxTorusComparisonData.Term.shifted v : d.Term).links =
      shiftLinks (observableSupport d.obs) (v : LatticePoint 1)) ∧
    (∀ T : d.Term, ∀ b ∈ T.links,
      b.initial ∈ T.siteBox ∧ b.terminal ∈ T.siteBox ∧
        ∃ x ∈ T.siteBox, ∃ μ : Fin 4, b = Link.forwardFrom x μ) ∧
    ∀ x : LatticePoint 1,
      Set.InjOn d.periodSublattice.quotientMap (siteCube x (d.boxWidth + 1))
end TermsInBoxes
end InfiniteLattice
end YangMills.Construction
end
