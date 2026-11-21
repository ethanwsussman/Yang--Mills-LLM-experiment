import YangMills.Construction.Conventions.BoundNumber
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondFormEnergy
import YangMills.Construction.Lattice.CurrentOnPart
import YangMills.Construction.Matrices.CommutatorAndCurveDerivative
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices Conventions
variable {L m K : ℕ} {j : ℤ}
abbrev BareBondForm (L m K : ℕ) : Type := BondAtLevel L m K 0 → ComplexMatrix2
abbrev BareBondFormMap (L m K : ℕ) : Type := BareBondForm L m K → BareBondForm L m K
open Classical in
def bondFormFromPositiveBonds (a : PositivelyOrientedBond L m j → ComplexMatrix2)
    (b : Bond L m j) : ComplexMatrix2 :=
  if hb : b.IsPositivelyOriented then a ⟨b, hb⟩
  else if hb' : b.opposite.IsPositivelyOriented then -a ⟨b.opposite, hb'⟩
  else 0
def IsHolomorphicOnBondForms
    (V : (Bond L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2) : Prop :=
  ∃ _ : Fintype (PositivelyOrientedBond L m j),
    ∀ (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
      (ν : PositivelyOrientedBond L m j ≃ Fin (Fintype.card (PositivelyOrientedBond L m j))),
      GroupLieProduct.IsHolomorphicOnTraceless e (GroupLieProduct.matrixPiEquiv ν)
        (GroupLieProduct.tracelessPi (PositivelyOrientedBond L m j))
        (fun a β => V (bondFormFromPositiveBonds a) (β : Bond L m j))
def Plaquette.bondSet (p : Plaquette L m j) : Set (Bond L m j) := {b | p.HasBond b}
def bondsNear (b : Bond L m j) : Set (Bond L m j) :=
  {b' | ∃ p ∈ plaquettesThrough b, b' ∈ p.bondSet}
def bareCovDerivSup (k : ℕ) (U A : BareBondForm L m K) : ℝ :=
  ⨆ x : SiteAtLevel L m K 0, covDerivNorm (finestMeshInLevelUnits L k) U A x
def supOperatorNormOn (S : Set (Bond L m j)) (A : Bond L m j → ComplexMatrix2) : ℝ :=
  supOfOperatorNorms fun b : ↥S => A b
def covDerivSupOn (k : ℕ) (S : Set (BondAtLevel L m K 0)) (U A : BareBondForm L m K) : ℝ :=
  ⨆ q : {q : SiteAtLevel L m K 0 × Fin 4 × Fin 4 //
      Bond.forwardFrom q.1 q.2.2 ∈ S ∧
        Bond.forwardFrom (q.1 + unitStep L m (levelDepth K 0) q.2.1) q.2.2 ∈ S},
    ComplexMatrix2.operatorNorm
      (covDeriv (finestMeshInLevelUnits L k) U q.1.2.1 (bondFormComponent A q.1.2.2) q.1.1)
def bondFormC1NormOn (k : ℕ) (S : Set (BondAtLevel L m K 0)) (U A : BareBondForm L m K) : ℝ :=
  max (supOperatorNormOn S A) (covDerivSupOn k S U A)
def HasHolonomyNearOne (k : ℕ) (U : BareBondForm L m K) (α : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧ ∀ p : PlaquetteAtLevel L m K 0,
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ α * finestMeshInLevelUnits L k ^ 2
structure IsGradientExpansion (ρ C α : ℝ) (k : ℕ) (U : BareBondForm L m K)
    (Δ V : BareBondFormMap L m K) : Prop where
  gradient_eq : ∀ A, IsBondForm complexLieAlgebra A →
    bareFormEnergyGradient k U A = yangMillsCurrent (finestMeshInLevelUnits L k) U +
      bareCovExteriorDerivAdjoint k U (bareCovExteriorDeriv k U A) + Δ A + V A
  linear_isBondForm : ∀ A, IsBondForm complexLieAlgebra A →
    IsBondForm complexLieAlgebra (Δ A)
  linear_add : ∀ A B, IsBondForm complexLieAlgebra A → IsBondForm complexLieAlgebra B →
    Δ (A + B) = Δ A + Δ B
  linear_smul : ∀ (c : ℂ) A, IsBondForm complexLieAlgebra A → Δ (c • A) = c • Δ A
  linear_symm : ∀ A B, IsBondForm complexLieAlgebra A → IsBondForm complexLieAlgebra B →
    bondFormInner (finestMeshInLevelUnits L k) (Δ A) B =
      bondFormInner (finestMeshInLevelUnits L k) A (Δ B)
  linear_local : ∀ A B, IsBondForm complexLieAlgebra A → IsBondForm complexLieAlgebra B →
    ∀ b : BondAtLevel L m K 0, (∀ b' ∈ bondsNear b, A b' = B b') → Δ A b = Δ B b
  linear_eq_zero : ∀ A, IsBondForm complexLieAlgebra A → ∀ b : BondAtLevel L m K 0,
    (∀ p ∈ plaquettesThrough b, plaquetteHolonomy U p = 1) → Δ A b = 0
  linear_le : ∀ A, IsBondForm complexLieAlgebra A → ∀ b : BondAtLevel L m K 0,
    ComplexMatrix2.operatorNorm (Δ A b) ≤ C * α * supOfOperatorNorms A
  rest_isBondForm : ∀ A, IsBondForm complexLieAlgebra A → IsBondForm complexLieAlgebra (V A)
  rest_holomorphic : IsHolomorphicOnBondForms V
  rest_zero : V 0 = 0
  rest_hasDerivAt_zero : ∀ A, IsBondForm complexLieAlgebra A → ∀ b : BondAtLevel L m K 0,
    HasDerivAt (fun t : ℂ => V (t • A) b) 0 0
  rest_le : ∀ A, IsBondForm complexLieAlgebra A → supOfOperatorNorms A ≤ ρ →
    supOfOperatorNorms (V A) ≤ C * supOfOperatorNorms A * bondFormC1Norm k U A
  hessian_eq : ∀ A, IsBondForm complexLieAlgebra A →
    bondFormInner (finestMeshInLevelUnits L k) A
        (bareCovExteriorDerivAdjoint k U (bareCovExteriorDeriv k U A) + Δ A) =
      iteratedDeriv 2 (fun t : ℝ => bareFormEnergy k U ((t : ℂ) • A)) 0
  gradient_eq_of_real : ∀ A, IsBondForm compactLieAlgebra A → ∀ b : BondAtLevel L m K 0,
    b.IsPositivelyOriented →
    bareFormEnergyGradient k U A b =
      ComplexMatrix2.expDivisorSeries
        ((-(Complex.I * ((finestMeshInLevelUnits L k : ℝ) : ℂ))) • ComplexMatrix2.commutatorMap (A b))
        (yangMillsCurrent (finestMeshInLevelUnits L k) (bareTwist k A U) b)
  current_le_gradient : ∀ A, IsBondForm compactLieAlgebra A →
    finestMeshInLevelUnits L k * supOfOperatorNorms A ≤ 1 / 8 →
    ∀ b : BondAtLevel L m K 0, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (yangMillsCurrent (finestMeshInLevelUnits L k) (bareTwist k A U) b) ≤
        (1 + 4 * finestMeshInLevelUnits L k * ComplexMatrix2.operatorNorm (A b)) *
          ComplexMatrix2.operatorNorm (bareFormEnergyGradient k U A b)
  gradient_le_current : ∀ A, IsBondForm compactLieAlgebra A →
    finestMeshInLevelUnits L k * supOfOperatorNorms A ≤ 1 / 8 →
    ∀ b : BondAtLevel L m K 0, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (bareFormEnergyGradient k U A b) ≤
        (1 + 2 * finestMeshInLevelUnits L k * ComplexMatrix2.operatorNorm (A b)) *
          ComplexMatrix2.operatorNorm (yangMillsCurrent (finestMeshInLevelUnits L k) (bareTwist k A U) b)
  holonomy_le : ∀ A, IsBondForm compactLieAlgebra A → supOfOperatorNorms A ≤ ρ →
    ∀ p : PlaquetteAtLevel L m K 0,
      ComplexMatrix2.operatorNorm (plaquetteHolonomy (bareTwist k A U) p - 1) ≤
        ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) +
          (2 * bareCovDerivSup k U A + C * supOfOperatorNorms A ^ 2) * finestMeshInLevelUnits L k ^ 2
  rest_lipschitz : ∀ (r : ℝ) (A₁ A₂ : BareBondForm L m K), IsBondForm complexLieAlgebra A₁ →
    IsBondForm complexLieAlgebra A₂ → bondFormC1Norm k U A₁ ≤ r →
    bondFormC1Norm k U A₂ ≤ r → r ≤ ρ / 4 →
    supOfOperatorNorms (V A₁ - V A₂) ≤ 4 * C * r * bondFormC1Norm k U (A₁ - A₂)
  linear_le_local : ∀ A, IsBondForm complexLieAlgebra A → ∀ b : BondAtLevel L m K 0,
    ComplexMatrix2.operatorNorm (Δ A b) ≤ C * α * supOperatorNormOn (bondsNear b) A
  rest_le_local : ∀ A, IsBondForm complexLieAlgebra A → supOfOperatorNorms A ≤ ρ →
    ∀ b : BondAtLevel L m K 0,
      ComplexMatrix2.operatorNorm (V A b) ≤
        C * supOperatorNormOn (bondsNear b) A * bondFormC1NormOn k (bondsNear b) U A
  holonomy_le_local : ∀ A, IsBondForm compactLieAlgebra A → supOfOperatorNorms A ≤ ρ →
    ∀ p : PlaquetteAtLevel L m K 0,
      ComplexMatrix2.operatorNorm (plaquetteHolonomy (bareTwist k A U) p - 1) ≤
        ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) +
          (2 * covDerivSupOn k p.bondSet U A + C * supOperatorNormOn p.bondSet A ^ 2) *
            finestMeshInLevelUnits L k ^ 2
def IsGradientExpansionConstants (ρ C : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 / 128 ∧ 1 ≤ C ∧
    ∀ (L m K k : ℕ), IsAdmissibleBlockingFactor L → 0 < m →
      ∀ U : BareBondForm L m K, IsBareFormEnergyData K k U →
        ∃ Δ V : BareBondFormMap L m K, ∀ α : ℝ, HasHolonomyNearOne k U α →
          IsGradientExpansion ρ C α k U Δ V
def gradientExpansionConstants : ℝ × ℝ :=
  boundNumber fun p => IsGradientExpansionConstants p.1 p.2
def gradientExpansionRadius : ℝ := gradientExpansionConstants.1
def gradientExpansionBound : ℝ := gradientExpansionConstants.2
def gradientExpansionMaps (k : ℕ) (U : BareBondForm L m K) :
    BareBondFormMap L m K × BareBondFormMap L m K :=
  boundNumber fun p => ∀ α : ℝ, HasHolonomyNearOne k U α →
    IsGradientExpansion gradientExpansionRadius gradientExpansionBound α k U p.1 p.2
def gradientExpansionLinear (k : ℕ) (U : BareBondForm L m K) : BareBondFormMap L m K :=
  (gradientExpansionMaps k U).1
end YangMills.Construction.PeriodicLattice
