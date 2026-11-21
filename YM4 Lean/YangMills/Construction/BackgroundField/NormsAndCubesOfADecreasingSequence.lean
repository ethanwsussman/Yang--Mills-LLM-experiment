import YangMills.Construction.BackgroundField.GaugeFixedOperators
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
open Set
open scoped ENNReal ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences Matrices
namespace BackgroundField
def halfTraceNorm (X : ComplexMatrix2) : ℝ := Real.sqrt (halfTraceNormSq X)
section SupremumNorms
variable {L m K : ℕ}
def siteSupNorm (f : FineSite L m K → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (halfTraceNorm (f x))
def bondSupNorm (A : FineBond L m K → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ μ : Fin 4, siteSupNorm (bondFormComponent A μ)
def complexSupNorm (K : ℕ) (ζ : FourTorus L m → ℂ) : ℝ≥0∞ :=
  ⨆ x : FineSite L m K, ENNReal.ofReal ‖ζ x‖
end SupremumNorms
section HolderNorms
variable {L m : ℕ} (S : ScaleData)
def holderTerm (lam β : ℝ) (U : FineBond L m S.levels → ComplexMatrix2)
    (Γ : List (FineBond L m S.levels))
    (x x' : FineSite L m S.levels) (v v' : ComplexMatrix2) : ℝ≥0∞ :=
  ENNReal.ofReal ((lam / unitL1Dist S (x : FourTorus L m) x') ^ β *
    halfTraceNorm (ComplexMatrix2.conjugateBy (pathHolonomy U Γ) v' - v))
def siteHolderNorm (lam β : ℝ) (U : FineBond L m S.levels → ComplexMatrix2)
    (path : FineSite L m S.levels → FineSite L m S.levels → List (FineBond L m S.levels))
    (f : FineSite L m S.levels → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ x : FineSite L m S.levels, ⨆ x' : FineSite L m S.levels,
    ⨆ _ : 0 < unitL1Dist S (x : FourTorus L m) x' ∧ unitL1Dist S (x : FourTorus L m) x' ≤ lam,
      holderTerm S lam β U (path x x') x x' (f x) (f x')
def bondHolderNorm (lam β : ℝ) (U : FineBond L m S.levels → ComplexMatrix2)
    (path : FineSite L m S.levels → FineSite L m S.levels → List (FineBond L m S.levels))
    (A : FineBond L m S.levels → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ μ : Fin 4, siteHolderNorm S lam β U path (bondFormComponent A μ)
def complexHolderNorm (lam β : ℝ) (ζ : FourTorus L m → ℂ) : ℝ≥0∞ :=
  ⨆ x : FineSite L m S.levels, ⨆ x' : FineSite L m S.levels,
    ⨆ _ : 0 < unitL1Dist S (x : FourTorus L m) x' ∧ unitL1Dist S (x : FourTorus L m) x' ≤ lam,
      ENNReal.ofReal ((lam / unitL1Dist S (x : FourTorus L m) x') ^ β *
        ‖ζ (x' : FourTorus L m) - ζ (x : FourTorus L m)‖)
end HolderNorms
namespace NestedRegions
variable {L m t : ℕ} (𝔰 : NestedRegions L m t)
def siteWeightedNorm {K : ℕ} (α : ℝ) (f : FineSite L m K → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ j ∈ Iic t, ⨆ x ∈ 𝔰.fineSitesOf K j \ 𝔰.fineSitesOf K (j + 1),
    ENNReal.ofReal (meshAtLevel L t j ^ (-α) * halfTraceNorm (f x))
def bondWeightedNorm {K : ℕ} (α : ℝ) (A : FineBond L m K → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ j ∈ Iic t, ⨆ b ∈ bondsTouching (𝔰.fineSitesOf K j) \ bondsTouching (𝔰.fineSitesOf K (j + 1)),
    ENNReal.ofReal (meshAtLevel L t j ^ (-α) * halfTraceNorm (A b))
def shellMesh {K : ℕ} (y : 𝔰.ShellSite K) : ℝ := meshAtLevel L t y.1.1
def shellCube {K : ℕ} (y : 𝔰.ShellSite K) : Set (FineSite L m K) := fineBlock y.1.2
def doubledCube {K : ℕ} (y : 𝔰.ShellSite K) : Set (FourTorus L m) :=
  closedSupCube (centeredPoint y.1.2) (2 * meshSize L (levelDepth K y.1.1))
def IsSmoothSupportedInDoubledCube {K : ℕ} (y : 𝔰.ShellSite K) (ζ : FourTorus L m → ℂ) : Prop :=
  ContDiff ℝ ∞ (ζ ∘ TorusMetric.torusProj (torusSide L m)) ∧ tsupport ζ ⊆ 𝔰.doubledCube y
end NestedRegions
end BackgroundField
end YangMills.Construction
