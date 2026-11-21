import YangMills.Construction.InfiniteLattice.BondsAndPlaquettesOfATorusAreFaithful
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithful
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem torusQuotientIsFaithful_of_quotientTorusFaithful (h : QuotientTorusFaithful.Statement) :
    TorusQuotientIsFaithful.Statement := fun Γ =>
  have hΓ : Γ.IsFaithfulQuotient := h 1 one_pos Γ
  ⟨hΓ.injOn_tripleCube, hΓ.ncard_linkEndpoints,
    fun p => ⟨hΓ.ncard_plaquetteVertices p, hΓ.ncard_plaquetteLinks p⟩⟩
end YangMills.Construction.InfiniteLattice
