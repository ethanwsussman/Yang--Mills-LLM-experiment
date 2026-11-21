import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ConstantSequence
import YangMills.Construction.Lattice.RegularAtRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
structure IsConstantRadiusSetting (L m K n : ℕ) (ε : ℝ) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  cutoff_pos : 0 < K
  exponent_pos : 0 < m
  scale_le_cutoff : n ≤ K
  radius_pos : 0 < ε
def IsConstantRegular (ε : ℝ) (K n : ℕ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    Prop :=
  U ∈ gaugeFieldsAtLevel L m K 0 ∧ IsRegularWithRadius ε K n constantWholeTorus U
def constantConstrainedFields (K n : ℕ) (V : BondAtLevel L m K n → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  constrainedFields (Averaging.smoothingRadius L) K n constantWholeTorus (datumOnLevel K n V)
def constantRegularCriticalFields (ε : ℝ) (K n : ℕ)
    (V : BondAtLevel L m K n → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ constantConstrainedFields K n V ∧
    IsConstantCritical (Averaging.smoothingRadius L) K n (datumOnLevel K n V) U ∧
    IsConstantRegular ε K n U}
def HasConstantMinimalOrbit (ε : ℝ) (K n : ℕ)
    (V : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  V ∈ gaugeFieldsAtLevel L m K n ∧
    ∃ U ∈ constantRegularCriticalFields ε K n V,
      constantRegularCriticalFields ε K n V = residualGaugeOrbit K n constantWholeTorus U
def HoldsOnConstantMinimalOrbit (ε : ℝ) (K n : ℕ)
    (V : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (P : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → Prop) : Prop :=
  HasConstantMinimalOrbit ε K n V ∧
    ∀ U ∈ constantRegularCriticalFields ε K n V, P U
end YangMills.Construction.PeriodicLattice
