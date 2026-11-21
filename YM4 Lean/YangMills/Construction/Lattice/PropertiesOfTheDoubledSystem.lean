import YangMills.Construction.Lattice.DoubledSystemOfATriple
import YangMills.Construction.Lattice.SymmetricMapsTransposesAndTheOperatorsOfATripleAreLinear
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set Matrices PeriodicLattice SeparatedSequences SeparatedRegions
open scoped ENNReal
noncomputable section
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def weightedTopSiteAdjoint (W : FineBond L m S → ComplexMatrix2)
    (μ : FourTorus L m → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  layerValueAdjoint S Ω W (weightSmul S Ω (topWeight S Ω) fun y => μ y)
def endpointTops (q : LeveledBond L m S) : Set (FourTorus L m) :=
  layerPoints S Ω ∩ (siteBlock S q.2.source ∪ siteBlock S q.2.target)
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
structure IsTopGradient (W : FineBond L m S → ComplexMatrix2)
    (T : (FourTorus L m → ComplexMatrix2) → LeveledBond L m S → ComplexMatrix2) : Prop where
  isLinear : IsLinearOnSets (pointFunctionSpace S Ω) (leveledFunctionSpace S Ω) T
  expansionValues_grad : ∀ l ∈ regionSiteSpace S (Ω 0),
    expansionValuesOfForm S Ω W (covGradAt S Ω W l) = T (topSiteValues S Ω W l)
  local_support : ∀ μ ∈ pointFunctionSpace S Ω, ∀ μ' ∈ pointFunctionSpace S Ω,
    ∀ q ∈ leveledIndexSet S Ω, (∀ y ∈ endpointTops S Ω q, μ y = μ' y) → T μ q = T μ' q
  norm_le : ∀ μ ∈ pointFunctionSpace S Ω, ∀ q ∈ leveledIndexSet S Ω,
    ENNReal.ofReal (ComplexMatrix2.operatorNorm (T μ q)) ≤
      ENNReal.ofReal (4 * (bondSpacing S q)⁻¹) *
        ⨆ y ∈ endpointTops S Ω q, ENNReal.ofReal (ComplexMatrix2.operatorNorm (μ y))
def topGradient (W : FineBond L m S → ComplexMatrix2) :
    (FourTorus L m → ComplexMatrix2) → LeveledBond L m S → ComplexMatrix2 :=
  Classical.epsilon (IsTopGradient S Ω W)
def weightedRowAdjoint (W : FineBond L m S → ComplexMatrix2)
    (ω : LeveledBond L m S → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  expansionValuesAdjoint S Ω W (spacingWeightSMul S ω)
def secondCopyResidual (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) (v f₂ : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (f₄ : FourTorus L m → ComplexMatrix2) : ReducedTuple L m S :=
  let W := firstMemberRestriction S Ω U
  reducedInjOne S (compressedHessian S Ω 𝔸 U (covGradAt S Ω W v) -
        currentTerm S Ω W J v + weightedRowAdjoint S Ω W (topGradient S Ω W f₄) -
        covGradAt S Ω W (dirichletCorrection S Ω v) -
        covGradAt S Ω W (weightedTopSiteAdjoint S Ω W f₄ - f₂)) +
      reducedInjTwo S (weightedTopSiteAdjoint S Ω W f₄ + dirichletCorrection S Ω v) +
      reducedInjFour S f₄ -
    reducedInjFive S (siteSourceTerm S Ω W J j (covGradAt S Ω W v) v)
end Operators
end SequenceTriples
end
end YangMills.Construction
