import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.GaugeFixingFactor
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
open ParameterChoice Matrices
variable (c : ChoiceUpToDegreeConstants) {m K k : ℕ} (D : StepData c.L m K k)
def fixedGaugeSites : Set (SiteAtLevel c.L m K (k + 1)) := sitesIn D.region
def positiveRegionBonds : Set (BondAtLevel c.L m K (k + 1)) :=
  {e | e ∈ bondsMeeting D.region ∧ e.IsPositivelyOriented}
def averagingFiber : Set (BondAtLevel c.L m K k → ComplexMatrix2) :=
  {V | V ∈ gaugeFieldsAtLevel c.L m K k ∧ (∀ b ∉ touchingBonds c D, V b = D.current b) ∧
    ∀ e ∈ (bondsMeeting D.region : Set (BondAtLevel c.L m K (k + 1))),
      blockAverageStep (Averaging.smoothingRadius c.L) k V e = D.next e}
def StepActionDefinedAt (V : BondAtLevel c.L m K k → ComplexMatrix2) : Prop :=
  HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K k D.domains
      (activeBondSet K k D.domains) (fieldDatum c D V) ∧
    HasOffCenterContours K k (fixedGaugeSites c D) V
def stepAction (V : BondAtLevel c.L m K k → ComplexMatrix2) : ℝ :=
  wilsonAction (backgroundOf c D V) + axialGaugeFunction K k (fixedGaugeSites c D) V
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
