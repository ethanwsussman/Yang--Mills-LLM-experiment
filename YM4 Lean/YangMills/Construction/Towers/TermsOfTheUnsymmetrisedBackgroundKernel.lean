import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms
open PeriodicOperators FieldValueFunctions
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
def indicesWithin (L k : ℕ) (hL : 0 < L) (x : InfiniteLattice.AmbientSpace) (ρ : ℝ) :
    Set (fieldPeriodicData L k hL).Carrier :=
  {i | ∀ j, |(fieldPeriodicData L k hL).pos i j - x j| < ρ}
def verticesWithin (L k : ℕ) (x : InfiniteLattice.AmbientSpace) (ρ : ℝ) : Set (Vertex L k 0) :=
  {y | ∀ j, |(y : InfiniteLattice.AmbientSpace) j - x j| < ρ}
def positiveEdgesWithin (L k : ℕ) (x : InfiniteLattice.AmbientSpace) (ρ : ℝ) :
    Set (PositiveEdge (meshAt L k 0)) :=
  {e | ∀ j, |(e.1.initial : InfiniteLattice.AmbientSpace) j - x j| < ρ ∧
    |(e.1.terminal : InfiniteLattice.AmbientSpace) j - x j| < ρ}
structure CoeffsHolomorphicOn {P : Type} (D : PeriodicData) (ρ : ℝ) (T : Set D.Carrier) (S : Set P)
    (Φ : (D.Carrier → ℂ) → P → Matrices.ComplexMatrix2) : Prop where
  finite : S.Finite
  eq_zero_of_not_mem : ∀ ζ, IsSupBelow D ζ ρ → ∀ p, p ∉ S → Φ ζ p = 0
  mem_traceless : ∀ ζ, IsSupBelow D ζ ρ → ∀ p, Φ ζ p ∈ Matrices.ComplexMatrix2.traceless
  holomorphic_coeff : ∀ p ∈ S, ∀ c : Fin 3,
    HolomorphicInValuesBelow D ρ T fun ζ => pauliCoeff c (Φ ζ p)
variable (L k : ℕ) (hL : 0 < L) (c' : Fin 3) (e' : PositiveEdge (meshAt L k 0)) (c : Fin 3)
  (e : PositiveEdge (meshAt L k 0))
def gaugeFixingPairing (f : (fieldPeriodicData L k hL).Carrier → ℂ) : ℂ :=
  traceFinsumPairing
    (gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c' e'))
    (gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c e))
def sourceBracketTerm (f : (fieldPeriodicData L k hL).Carrier → ℂ) : ℂ :=
  2 * finiteEdgePairing (sourceOfCoeffs hL f)
    (levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
      (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c' e'))
      (basisForm c e))
def sourceBracketCovTerm (f : (fieldPeriodicData L k hL).Carrier → ℂ) : ℂ :=
  finiteEdgePairing (sourceOfCoeffs hL f)
    (levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
      (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c' e'))
      (covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
        (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c e))))
def quadraticCoarseTerm (f : (fieldPeriodicData L k hL).Carrier → ℂ) : ℂ :=
  traceFinsumPairing (restrictToPositiveEdges (coarseOfCoeffs hL f))
    (complexQuadraticTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
      (shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c' e'))
      (shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm c e)))
variable {L k hL e' e}
structure IsLocalTerm (L k : ℕ) (hL : 0 < L) (ρ : ℝ) (e' e : PositiveEdge (meshAt L k 0))
    (g : ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ) : Prop where
  eq_zero_of_far : (∃ j, 6 ≤ |(e.1.initial : InfiniteLattice.AmbientSpace) j -
      (e'.1.initial : InfiniteLattice.AmbientSpace) j|) →
    ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → g ζ = 0
  holomorphic_of_near : (∀ j, |(e.1.initial : InfiniteLattice.AmbientSpace) j -
      (e'.1.initial : InfiniteLattice.AmbientSpace) j| < 6) →
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (indicesWithin L k hL e'.1.initial (9 / 2) ∪ indicesWithin L k hL e.1.initial (7 / 2)) g
end YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms
end
