import YangMills.Construction.Lattice.CovariantSiteOperators
import YangMills.Construction.Lattice.LieValuedBondFunctions
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice
namespace TransposeFormulas
variable {L m : ℕ} {j : ℤ}
def covDerivAdjointSum (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) : ComplexMatrix2 :=
  ∑ ν ∈ Finset.univ.erase μ, covDerivAdjointComponent ξ U ν (F ν μ) x
def transportedDifferenceSum (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) : ComplexMatrix2 :=
  ((ξ⁻¹ : ℝ) : ℂ) • ∑ ν ∈ Finset.univ.erase μ,
    (F μ ν x - ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
      (F μ ν (x - unitStep L m j ν)))
def conjugateAtOrigin (u : Site L m j → ComplexMatrix2) (X : Plaquette L m j → ComplexMatrix2) :
    Plaquette L m j → ComplexMatrix2 :=
  fun p => ComplexMatrix2.conjugateBy (u p.origin) (X p)
def AdjointFormulaOnLieForms (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  ∀ F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2, IsPlaquetteForm complexLieAlgebra F → ∀ μ x,
    bondFormComponent (covExteriorDerivAdjoint ξ U F) μ x = covDerivAdjointSum ξ U F μ x ∧
      covDerivAdjointSum ξ U F μ x = transportedDifferenceSum ξ U F μ x
def GradientAdjointIdentity (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  ∀ A : Bond L m j → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    ∀ f : Site L m j → ComplexMatrix2, IsSiteField complexLieAlgebra f →
      bondFormInner ξ A (covGradient univ ξ U f) =
        siteInner ξ (bondFormDivergenceSum ξ U A) f
def AdjointFormulaOnMatrixForms (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  ∀ X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2, IsPlaquetteForm univ X →
    IsBondForm univ (matrixCovExteriorDerivTranspose ξ U X) ∧
    (∀ A : Bond L m j → ComplexMatrix2, IsBondForm univ A →
      bondFormInner ξ (matrixCovExteriorDerivTranspose ξ U X) A =
        plaquetteFormInner ξ X (covExteriorDeriv ξ U A)) ∧
    ∀ μ x, bondFormComponent (matrixCovExteriorDerivTranspose ξ U X) μ x =
        covDerivAdjointSum ξ U X μ x ∧
      covDerivAdjointSum ξ U X μ x = transportedDifferenceSum ξ U X μ x
def GaugeCovariant (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (u : Site L m j → ComplexMatrix2) :
    Prop :=
  ∀ b : Bond L m j, b.IsPositivelyOriented →
    (∀ X : Plaquette L m j → ComplexMatrix2,
      matrixCovExteriorDerivTranspose ξ (gaugeTransform u U)
          (plaquetteFormOf (conjugateAtOrigin u X)) b =
        ComplexMatrix2.conjugateBy (u b.source)
          (matrixCovExteriorDerivTranspose ξ U (plaquetteFormOf X) b)) ∧
    yangMillsCurrent ξ (gaugeTransform u U) b =
      ComplexMatrix2.conjugateBy (u b.source) (yangMillsCurrent ξ U b) ∧
    matrixCovExteriorDerivTranspose ξ (gaugeTransform u U)
        (plaquetteFormOf (plaquetteHolonomy (gaugeTransform u U))) b =
      ComplexMatrix2.conjugateBy (u b.source)
        (matrixCovExteriorDerivTranspose ξ U (plaquetteFormOf (plaquetteHolonomy U)) b)
def CovDerivSupBounds (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  ∀ A : Bond L m j → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    supOfOperatorNorms (bondFormDivergenceSum ξ U A) ≤ 4 * ⨆ x, covDerivNorm ξ U A x ∧
      ξ * ⨆ x, covDerivNorm ξ U A x ≤ 2 * supOfOperatorNorms A
def FinestOperatorIdentities (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  (∀ F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2, IsPlaquetteForm complexLieAlgebra F →
    ∀ μ x, plaquetteFormDivergenceSum ξ U F μ x =
      bondFormComponent (covExteriorDerivAdjoint ξ U F) μ x) ∧
  ∀ A : Bond L m j → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    bondFormDivergenceSum ξ U A = covDivergence univ ξ U A
def ExplicitAdjointFormulas : Prop :=
  (∀ L m K k : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K → k ≤ K → ∀ j : ℤ, -(m : ℤ) < j →
    ∀ ξ : ℝ, ξ = toLevelUnits L K k (meshSize L j) →
      (∀ U : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
        AdjointFormulaOnLieForms ξ U ∧ GradientAdjointIdentity ξ U ∧
          AdjointFormulaOnMatrixForms ξ U) ∧
      ∀ U : Bond L m j → ComplexMatrix2, IsGaugeField compactGaugeGroup univ U →
        (∀ u : Site L m j → ComplexMatrix2, IsGaugeMap compactGaugeGroup u →
          GaugeCovariant ξ U u) ∧
        CovDerivSupBounds ξ U) ∧
  ∀ L m K k : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K → k ≤ K →
    ∀ U₀ : BondAtLevel L m K 0 → ComplexMatrix2, IsGaugeField complexGaugeGroup univ U₀ →
      FinestOperatorIdentities (finestMeshInLevelUnits L k) U₀
end TransposeFormulas
end PeriodicLattice
end YangMills.Construction
