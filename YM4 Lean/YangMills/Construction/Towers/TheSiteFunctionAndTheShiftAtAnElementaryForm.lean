import YangMills.Construction.Towers.EntriesOfTheIteratedMaps
import YangMills.Construction.Towers.TermsOfTheUnsymmetrisedBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BasisFormLocality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
open YangMills.Construction.Tower.FullSpace.IteratedKernelEntries
open YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms
def ElementaryFormLocality : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ j : ℕ, 1 ≤ j →
    ∃ r : ℝ, 0 < r ∧ ∀ (c : Fin 3) (e : PositiveEdge (meshAt L j 0)),
      CoeffsHolomorphicOn (fieldPeriodicData L j hL) r
        (backgroundCoords L j hL (edgesNear L j e.1.initial (7 / 2)))
        (verticesWithin L j e.1.initial (1 / 2))
        (fun f => gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
          (basisForm c e)) ∧
      CoeffsHolomorphicOn (fieldPeriodicData L j hL) r
        (backgroundCoords L j hL (edgesNear L j e.1.initial (7 / 2)))
        (positiveEdgesWithin L j e.1.initial (3 / 2))
        (fun f => restrictToPositiveEdges
          (shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c e))) ∧
      ∀ f, IsSupBelow (fieldPeriodicData L j hL) f r →
        shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c e) ∈
          complexEdgeForms (meshAt L j 0)
end YangMills.Construction.Tower.FullSpace.BasisFormLocality
end
