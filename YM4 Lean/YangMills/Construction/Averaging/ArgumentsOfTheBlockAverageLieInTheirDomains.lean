import YangMills.Construction.Averaging.RadiiBelowTheExplicitBound
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Averaging.BlockArguments
def IsFamilyLogMean {ι : Type*} [Fintype ι] (V : ι → ComplexMatrix2) : Prop :=
  (∀ i, V i ∈ complexGaugeGroup) ∧ ComplexMatrix2.IsLogMean complexGaugeGroup V (complexLogMean V) ∧
    (∃ i, ComplexMatrix2.operatorNorm (V i * (complexLogMean V)⁻¹ - 1) ≤ complexMeanTolerance) ∧
    ∀ W, ComplexMatrix2.IsLogMean complexGaugeGroup V W →
      (∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance) →
      W = complexLogMean V
structure WellDefinedAtBond {L m K : ℕ} (ω₁ : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop where
  finite_blocks : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    (sitesInBlock (levelDepth K k) y).Finite
  shift_mem_block : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
    shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target
  axisOrdering_nonempty : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x : SiteAtLevel L m K k, Nonempty (AxisOrdering y x)
  logMean_on_complexDomain :
    ∀ U ∈ (complexAveragingDomain c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, IsFamilyLogMean (contourHolonomies U y x)
  smallFields_subset : ∀ ω ∈ Ioc (0 : ℝ) ω₁,
    (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) ⊆
      complexAveragingDomain c
  regular : ∀ ω ∈ Ioc (0 : ℝ) ω₁, c.IsPositivelyOriented →
    YangMills.Construction.Averaging.ExplicitRadii.RegularCaseOnSmallSet ω k c
  complexDomain_of_small : ∀ ω ∈ Ioc (0 : ℝ) ω₁, c.IsPositivelyOriented →
    YangMills.Construction.Averaging.ExplicitRadii.SmallSetInComplexDomain ω k c
def Holds : Prop :=
  ∀ s : YangMills.Construction.Conventions.StandingParameters, ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1),
    WellDefinedAtBond (averagingRadiusCap s.L) k c
end YangMills.Construction.Averaging.BlockArguments
end
