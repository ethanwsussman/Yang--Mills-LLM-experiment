import YangMills.Construction.Lattice.GaugeSizeAnglesAndBlockMean
import YangMills.Construction.Lattice.OneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K n : ℕ}
abbrev centredStepGauge (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  stepGauge AveragingScheme.centred c a W₀ y
def sitesOfDoubleBlock (c : BondAtLevel L m K (n + 1)) : Set (SiteAtLevel L m K n) :=
  sitesInBlock (levelDepth K n) c.source ∪ sitesInBlock (levelDepth K n) c.target
abbrev IsGaugeFieldOnDoubleBlock (c : BondAtLevel L m K (n + 1))
    (W₀ : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  IsGaugeField compactGaugeGroup (doubleBlockSymmetricSet c).bonds W₀
def IsGaugeTransformOnDoubleBlock (c : BondAtLevel L m K (n + 1))
    (r : SiteAtLevel L m K n → ComplexMatrix2) : Prop :=
  ∀ x ∈ sitesOfDoubleBlock c, r x ∈ compactGaugeGroup
def gaugeDeviation (c : BondAtLevel L m K (n + 1)) (r : SiteAtLevel L m K n → ComplexMatrix2) : ℝ :=
  ⨆ x : ↥(sitesOfDoubleBlock c), ComplexMatrix2.operatorNorm (r x - 1)
def maxGaugeBondAngle (c : BondAtLevel L m K (n + 1)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (r : SiteAtLevel L m K n → ComplexMatrix2) : ℝ :=
  ⨆ v : ↥(doubleBlockSymmetricSet c).bonds, ComplexMatrix2.rotationAngle (gaugeBondTwist W₀ r v)
end YangMills.Construction.PeriodicLattice
