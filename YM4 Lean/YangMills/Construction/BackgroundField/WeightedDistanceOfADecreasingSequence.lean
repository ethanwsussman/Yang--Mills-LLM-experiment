import YangMills.Construction.BackgroundField.GaugeFixedOperators
import Mathlib
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.BackgroundField.NestedRegions
variable {L m t : ℕ} (N : NestedRegions L m t)
open Classical in
def weightingSites (K j : ℕ) : Set (FineSite L m K) :=
  if j = 0 then (N.fineSitesOf K 1)ᶜ else fineBlockUnion (N.shellSites K j)
open Classical in
def pathLengthIn {K : ℕ} (X : Set (FineSite L m K)) (Γ : List (FineBond L m K)) : ℝ :=
  finestMeshInLevelUnits L t * ((Γ.filter fun b => decide (b ∈ bondsTouching X)).length : ℝ)
def LiesOnLevelBond {K : ℕ} (j : ℕ) (b : FineBond L m K) : Prop :=
  ∃ c : BondAtLevel L m K j, b.edgeSet ⊆ (fun p => p - diagonalShift L m K j) '' c.edgeSet
def IsAdmissiblePath {K : ℕ} (Γ : List (FineBond L m K)) : Prop :=
  ∀ j ≤ t, ∀ b ∈ Γ, b ∈ bondsTouching (fineBlockUnion (N.shellSites K j)) → LiesOnLevelBond j b
def weightedPathLength {K : ℕ} (Γ : List (FineBond L m K)) : ℝ :=
  ∑ j ∈ Finset.range (t + 1),
    (meshAtLevel L t j)⁻¹ * pathLengthIn (t := t) (N.weightingSites K j) Γ
def shellSiteToFine {K : ℕ} (y : N.ShellSite K) : FineSite L m K :=
  siteOfCenteredPoint 0 (centeredPoint y.1.2)
def scaleWeightedDistance {K : ℕ} (y y' : N.ShellSite K) : ℝ :=
  sInf {w | ∃ Γ : List (FineBond L m K), IsBondPathFromTo Γ (N.shellSiteToFine y) (N.shellSiteToFine y') ∧
    N.IsAdmissiblePath Γ ∧ w = N.weightedPathLength Γ}
end YangMills.Construction.BackgroundField.NestedRegions
