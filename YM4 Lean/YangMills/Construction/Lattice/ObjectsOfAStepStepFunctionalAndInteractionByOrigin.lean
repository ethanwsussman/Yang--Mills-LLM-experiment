import YangMills.Construction.Lattice.LinearisingChartAtAForm
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices PeriodicLattice
namespace PeriodicLattice
variable {L m K k : ℕ}
def chartJacobian (V : BondAtLevel L m K k → ComplexMatrix2) (Γ : Set (BondAtLevel L m K (k + 1)))
    (B : SupportBond (levelDepth K k) Γ → ComplexMatrix2) :
    Module.End ℂ (supportForms (levelDepth K k) Γ) :=
  restrictEndomorphism (supportForms (levelDepth K k) Γ) fun X =>
    X - pivotCorrectionLift V Γ (continuationCorrectionDeriv V Γ B X)
def traceLogChartJacobian (V : BondAtLevel L m K k → ComplexMatrix2)
    (Γ : Set (BondAtLevel L m K (k + 1)))
    (B : SupportBond (levelDepth K k) Γ → ComplexMatrix2) : ℂ :=
  -∑' n : ℕ, ((n + 1 : ℂ)⁻¹) *
    LinearMap.trace ℂ (supportForms (levelDepth K k) Γ)
      ((1 - chartJacobian V Γ B) ^ (n + 1))
end PeriodicLattice
end YangMills.Construction
end
