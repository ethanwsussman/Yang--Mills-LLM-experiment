import YangMills.Construction.Lattice.ComponentFamiliesOfForms
import YangMills.Construction.Lattice.CovariantAdjointFormulas
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CovariantAdjoints
variable {L m : ℕ} {j : ℤ}
def transposeDivergence (ξ : ℝ) (U A : Bond L m j → Matrices.ComplexMatrix2) (x : Site L m j) :
    Matrices.ComplexMatrix2 :=
  ∑ μ : Fin 4, covDerivTranspose ξ U μ (bondFormComponent A μ) x
def transposedCurlComponent (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) : Matrices.ComplexMatrix2 :=
  ∑ ν ∈ Finset.univ.erase μ, covDerivTranspose ξ U ν (F ν μ) x
def FamiliesAreFormComponents (L m : ℕ) (j : ℤ) (V : Set Matrices.ComplexMatrix2) : Prop :=
  (∀ f : AxisSiteFamily L m j, (∀ μ x, f μ x ∈ V) →
    ∃! A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm V A ∧ bondFormComponent A = f) ∧
  ∀ f : PlaquetteFamily L m j, (∀ p, f p ∈ V) →
    ∃! F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2,
      IsPlaquetteForm V F ∧ plaquetteFamilyOfComponents F = f
def InnerProductsNondegenerate (L m : ℕ) (j : ℤ) (ξ : ℝ) (V : Set Matrices.ComplexMatrix2) :
    Prop :=
  (∀ f : Site L m j → Matrices.ComplexMatrix2, IsSiteField V f →
    (∀ g, IsSiteField V g → siteInner ξ f g = 0) → f = 0) ∧
  (∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm V A →
    (∀ B, IsBondForm V B → bondFormInner ξ A B = 0) → A = 0) ∧
  ∀ F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2, IsPlaquetteForm V F →
    (∀ H, IsPlaquetteForm V H → plaquetteFormInner ξ F H = 0) → F = 0
def BondPlaquetteFormFacts (L m : ℕ) (j : ℤ) (ξ : ℝ) : Prop :=
  2 * L ≤ gridSideLength L m j ∧ 26 ≤ 2 * L ∧
  (∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) ∧
  Function.Injective (Plaquette.face : Plaquette L m j → Set (FourTorus L m)) ∧
  ∀ V : Set Matrices.ComplexMatrix2, V = complexLieAlgebra ∨ V = univ →
    FamiliesAreFormComponents L m j V ∧ InnerProductsNondegenerate L m j ξ V
def IsExteriorDerivAdjoint (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (V : Set Matrices.ComplexMatrix2)
    (T : (Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2) →
      Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  (∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm V A →
    IsPlaquetteForm V (covExteriorDeriv ξ U A)) ∧
  (∀ F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2, IsPlaquetteForm V F →
    (∃! B : Bond L m j → Matrices.ComplexMatrix2, IsBondForm V B ∧ ∀ A, IsBondForm V A →
      bondFormInner ξ B A = plaquetteFormInner ξ F (covExteriorDeriv ξ U A)) ∧
    IsBondForm V (T F) ∧
    (∀ A, IsBondForm V A →
      bondFormInner ξ (T F) A = plaquetteFormInner ξ F (covExteriorDeriv ξ U A)) ∧
    ∀ μ x, bondFormComponent (T F) μ x = transposedCurlComponent ξ U F μ x ∧
      transposedCurlComponent ξ U F μ x =
        TransposeFormulas.transportedDifferenceSum ξ U F μ x) ∧
  (∀ F G : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2,
    IsPlaquetteForm V F → IsPlaquetteForm V G → T (F + G) = T F + T G) ∧
  ∀ (c : ℂ) (F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2),
    IsPlaquetteForm V F → T (c • F) = c • T F
def GradientAdjointFacts (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (V : Set Matrices.ComplexMatrix2) : Prop :=
  (∀ g : Site L m j → Matrices.ComplexMatrix2, IsSiteField V g →
    IsBondForm V (covGradient univ ξ U g) ∧
      bondFormComponent (covGradient univ ξ U g) = axisFamilyGradient ξ U g) ∧
  ∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm V A →
    IsSiteField V (transposeDivergence ξ U A) ∧
    (∀ g, IsSiteField V g →
      bondFormInner ξ A (covGradient univ ξ U g) =
        siteInner ξ (transposeDivergence ξ U A) g) ∧
    ∀ τ, IsSiteField V τ →
      (∀ g, IsSiteField V g →
        siteInner ξ τ g = bondFormInner ξ A (covGradient univ ξ U g)) →
      τ = transposeDivergence ξ U A
def DerivativeAdjoints (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  IsExteriorDerivAdjoint ξ U complexLieAlgebra (covExteriorDerivAdjoint ξ U) ∧
  GradientAdjointFacts ξ U complexLieAlgebra ∧
  IsExteriorDerivAdjoint ξ U univ (matrixCovExteriorDerivTranspose ξ U) ∧
  GradientAdjointFacts ξ U univ ∧
  ∀ F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2,
    IsPlaquetteForm complexLieAlgebra F →
    matrixCovExteriorDerivTranspose ξ U F = covExteriorDerivAdjoint ξ U F
def AdjointIdentityAndBounds (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  ∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm univ A →
    (∀ μ x, covDerivTranspose ξ U μ (bondFormComponent A μ) x =
      -Matrices.ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j μ) μ))⁻¹
        (covDeriv ξ U μ (bondFormComponent A μ) (x - unitStep L m j μ))) ∧
    (IsGaugeField compactGaugeGroup univ U →
      (∀ x, Matrices.ComplexMatrix2.operatorNorm (transposeDivergence ξ U A x) ≤
        ∑ μ : Fin 4, Matrices.ComplexMatrix2.operatorNorm
          (covDeriv ξ U μ (bondFormComponent A μ) (x - unitStep L m j μ))) ∧
      supOfOperatorNorms (transposeDivergence ξ U A) ≤ 4 * (⨆ x, covDerivNorm ξ U A x) ∧
      ξ * (⨆ x, covDerivNorm ξ U A x) ≤
        2 * supOfOperatorNorms fun b : PositivelyOrientedBond L m j => A b.1)
def boundaryBonds (p : Plaquette L m j) : Set (Bond L m j) :=
  {Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis,
    Bond.forwardFrom p.origin p.secondAxis}
def plaquetteSpanned (y : Site L m j) {μ ν : Fin 4} (h : μ ≠ ν) : Plaquette L m j :=
  ⟨y, min μ ν, max μ ν, min_lt_max.mpr h⟩
def forwardPlaquette (x : Site L m j) (μ : Fin 4) (ν : {ν : Fin 4 // ν ≠ μ}) :
    Plaquette L m j :=
  plaquetteSpanned x ν.2.symm
def backwardPlaquette (x : Site L m j) (μ : Fin 4) (ν : {ν : Fin 4 // ν ≠ μ}) :
    Plaquette L m j :=
  plaquetteSpanned (x - unitStep L m j ν) ν.2.symm
def cofacePlaquettes (x : Site L m j) (μ : Fin 4) : Set (Plaquette L m j) :=
  range (forwardPlaquette x μ) ∪ range (backwardPlaquette x μ)
def axisOrderSign (μ ν : Fin 4) : ℂ := if μ < ν then 1 else -1
def extendByOne (S : Set (Bond L m j)) (W : Bond L m j → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if b ∈ S then W b else 1
def AdjointValueAtBond (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  ∀ (μ : Fin 4) (x : Site L m j),
    Function.Injective (Sum.elim (forwardPlaquette x μ) (backwardPlaquette x μ)) ∧
    (∀ p : Plaquette L m j, Bond.forwardFrom x μ ∈ boundaryBonds p ↔ p ∈ cofacePlaquettes x μ) ∧
    (∀ p : Plaquette L m j, (Bond.forwardFrom x μ).opposite ∉ boundaryBonds p) ∧
    (∀ ν : {ν : Fin 4 // ν ≠ μ},
      Bond.forwardFrom (x - unitStep L m j ν) ν ∈ boundaryBonds (backwardPlaquette x μ ν)) ∧
    (∀ X : MatrixPlaquetteForm L m j,
      matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent X) (Bond.forwardFrom x μ) =
        ∑ ν : {ν : Fin 4 // ν ≠ μ}, axisOrderSign μ ν • ((ξ⁻¹ : ℝ) : ℂ) •
          (X (forwardPlaquette x μ ν) -
            Matrices.ComplexMatrix2.conjugateBy
              (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
              (X (backwardPlaquette x μ ν)))) ∧
    ∀ W : Bond L m j → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ W →
      (∀ p ∈ cofacePlaquettes x μ, ∀ b ∈ boundaryBonds p, W b = U b) →
      (∀ X Y : MatrixPlaquetteForm L m j, (∀ p ∈ cofacePlaquettes x μ, Y p = X p) →
        matrixCovExteriorDerivTranspose ξ W (plaquetteFamilyComponent Y) (Bond.forwardFrom x μ) =
          matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent X)
            (Bond.forwardFrom x μ)) ∧
      yangMillsCurrent ξ W (Bond.forwardFrom x μ) = yangMillsCurrent ξ U (Bond.forwardFrom x μ) ∧
      matrixCovExteriorDerivTranspose ξ W (plaquetteFamilyComponent (plaquetteHolonomy W))
          (Bond.forwardFrom x μ) =
        matrixCovExteriorDerivTranspose ξ U (plaquetteFamilyComponent (plaquetteHolonomy U))
          (Bond.forwardFrom x μ)
def GaugeFieldsExtendByOne (L m : ℕ) (j : ℤ) : Prop :=
  ∀ (S : Set (Bond L m j)) (W : Bond L m j → Matrices.ComplexMatrix2), IsReversalClosed S →
    IsGaugeField complexGaugeGroup S W →
    IsGaugeField complexGaugeGroup univ (extendByOne S W) ∧
    (∀ b ∈ S, extendByOne S W b = W b) ∧
    (IsGaugeField compactGaugeGroup S W →
      IsGaugeField compactGaugeGroup univ (extendByOne S W))
def IsRealInnerProductOnSet {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E)
    (P : E → E → ℂ) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, (P a b).im = 0) ∧
  (∀ a ∈ S, ∀ b ∈ S, P a b = P b a) ∧
  (∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ S, ∀ c d : ℝ,
    P (c • a + d • a') b = (c : ℂ) * P a b + (d : ℂ) * P a' b) ∧
  (∀ a ∈ S, ∀ b ∈ S, ∀ b' ∈ S, ∀ c d : ℝ,
    P a (c • b + d • b') = (c : ℂ) * P a b + (d : ℂ) * P a b') ∧
  ∀ a ∈ S, a ≠ 0 → 0 < (P a a).re
def CompactRealForms (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  (∀ g : Site L m j → Matrices.ComplexMatrix2, IsSiteField compactLieAlgebra g →
    IsBondForm compactLieAlgebra (covGradient univ ξ U g)) ∧
  (∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm compactLieAlgebra A →
    IsPlaquetteForm compactLieAlgebra (covExteriorDeriv ξ U A) ∧
      IsSiteField compactLieAlgebra (transposeDivergence ξ U A)) ∧
  (∀ F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2,
    IsPlaquetteForm compactLieAlgebra F →
    IsBondForm compactLieAlgebra (covExteriorDerivAdjoint ξ U F)) ∧
  IsRealInnerProductOnSet {f : Site L m j → Matrices.ComplexMatrix2 |
    IsSiteField compactLieAlgebra f} (siteInner ξ) ∧
  IsRealInnerProductOnSet {A : Bond L m j → Matrices.ComplexMatrix2 |
    IsBondForm compactLieAlgebra A} (bondFormInner ξ) ∧
  IsRealInnerProductOnSet {F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2 |
    IsPlaquetteForm compactLieAlgebra F} (plaquetteFormInner ξ) ∧
  (∀ F A, IsPlaquetteForm compactLieAlgebra F → IsBondForm compactLieAlgebra A →
    bondFormInner ξ (covExteriorDerivAdjoint ξ U F) A =
      plaquetteFormInner ξ F (covExteriorDeriv ξ U A)) ∧
  ∀ A g, IsBondForm compactLieAlgebra A → IsSiteField compactLieAlgebra g →
    siteInner ξ (transposeDivergence ξ U A) g = bondFormInner ξ A (covGradient univ ξ U g)
def FinestLatticeOperators (η : ℝ) (U₀ : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  (∀ ν f x, covDerivTranspose η U₀ ν f x = covDerivAdjointComponent η U₀ ν f x) ∧
  (∀ X : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2,
    IsPlaquetteForm complexLieAlgebra X → ∀ μ x,
    plaquetteFormDivergenceSum η U₀ X μ x =
      bondFormComponent (covExteriorDerivAdjoint η U₀ X) μ x) ∧
  (∀ X : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2, IsPlaquetteForm univ X → ∀ μ x,
    plaquetteFormDivergenceSum η U₀ X μ x =
      bondFormComponent (matrixCovExteriorDerivTranspose η U₀ X) μ x) ∧
  ∀ A : Bond L m j → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
    covDivergence univ η U₀ A = bondFormDivergenceSum η U₀ A ∧
    ∀ τ : Site L m j → Matrices.ComplexMatrix2,
      (IsSiteField complexLieAlgebra τ ∧ ∀ g, IsSiteField complexLieAlgebra g →
        siteInner η τ g = bondFormInner η A (covGradient univ η U₀ g)) ↔
      τ = bondFormDivergenceSum η U₀ A
def CovariantAdjointsStatement : Prop :=
  ∀ L m K k : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K → k ≤ K →
    (∀ j : ℤ, -(m : ℤ) < j → ∀ ξ : ℝ, ξ = toLevelUnits L K k (meshSize L j) →
      BondPlaquetteFormFacts L m j ξ ∧
      GaugeFieldsExtendByOne L m j ∧
      ∀ U : Bond L m j → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
        DerivativeAdjoints ξ U ∧
        (∀ u : Site L m j → Matrices.ComplexMatrix2, IsGaugeMap complexGaugeGroup u →
          TransposeFormulas.GaugeCovariant ξ U u ∧
          (IsGaugeField compactGaugeGroup univ U → IsGaugeMap compactGaugeGroup u →
            IsGaugeField compactGaugeGroup univ (gaugeTransform u U))) ∧
        AdjointIdentityAndBounds ξ U ∧
        AdjointValueAtBond ξ U ∧
        (IsGaugeField compactGaugeGroup univ U → CompactRealForms ξ U)) ∧
    -(m : ℤ) < levelDepth K 0 ∧
    toLevelUnits L K k (meshSize L (levelDepth K 0)) = finestMeshInLevelUnits L k ∧
    IsPartitionRegion (L := L) (m := m) (levelDepth K 0) univ ∧
    ∀ U₀ : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ U₀ →
      FinestLatticeOperators (finestMeshInLevelUnits L k) U₀
end CovariantAdjoints
end PeriodicLattice
end YangMills.Construction
