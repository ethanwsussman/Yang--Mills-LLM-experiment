import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TorusQuotientIsFaithful.Statement : Prop :=
  ∀ Γ : PeriodSublattice 1,
    (∀ x : LatticePoint 1, Set.InjOn Γ.quotientMap (tripleCube x)) ∧
    (∀ c : Γ.QuotientLink, (Γ.linkEndpoints c).ncard = 2) ∧
    ∀ p : Γ.QuotientPlaquette, (Γ.plaquetteVertices p).ncard = 4 ∧ (Γ.plaquetteLinks p).ncard = 4
end YangMills.Construction.InfiniteLattice
