import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.MinimalOrbitsOfTheConstantSequenceAtARadius
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
open YangMills.Construction.ParameterChoice
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K k : ℕ)
structure IsSmallFieldStepData (V : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : Prop where
  radius_setting : IsConstantRadiusSetting c.L m K k c.εv
  lt_cutoff : k < K
  current_mem : V ∈ gaugeFieldsAtLevel c.L m K k
  next_mem : W ∈ gaugeFieldsAtLevel c.L m K (k + 1)
variable {K k}
def smallFieldStepData {L m : ℕ} (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (W : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) : StepData L m K k where
  domains := constantWholeTorus
  region := univ
  lowerFields := fun _ _ => 1
  current := V
  next := W
variable (K k)
def smallFieldRegularCritical (V : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    Set (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) :=
  regularCriticalFields (Averaging.smoothingRadius c.L) c.εv K k constantWholeTorus
    (datumOnLevel K k V)
def SmallFieldCriticalOrbitExists (V : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : Prop :=
  CriticalFieldsFormOneOrbit (Averaging.smoothingRadius c.L) c.εv K k constantWholeTorus
    (datumOnLevel K k V)
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
end
