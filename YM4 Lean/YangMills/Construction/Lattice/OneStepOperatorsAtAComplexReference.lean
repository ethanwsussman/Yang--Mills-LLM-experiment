import YangMills.Construction.Lattice.ObjectsOfTheLinearPartOfOneStep
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K n : ℕ}
def twistedStepMap (W : BondAtLevel L m K n → ComplexMatrix2) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) : ↥ComplexMatrix2.traceless :=
  toTraceless (stepVariable .centred c a W)
def twistedStepDerivative (W : BondAtLevel L m K n → ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) [Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))] :
    LieBondField (doubleBlockSymmetricSet c) →ₗ[ℂ] ↥ComplexMatrix2.traceless :=
  (fderiv ℂ (twistedStepMap W c) 0).toLinearMap
def TwistedStepDerivativeDefined (W : BondAtLevel L m K n → ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) [Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))] :
    Prop :=
  (∀ᶠ a in 𝓝 (0 : LieBondField (doubleBlockSymmetricSet c)), StepVariableDefined .centred c a W) ∧
    DifferentiableAt ℂ (twistedStepMap W c) 0
def twistedBlockAverage (W : BondAtLevel L m K n → ComplexMatrix2) (y : SiteAtLevel L m K (n + 1))
    (ρ : LieSiteField (sitesInBlock (levelDepth K n) y)) : ↥ComplexMatrix2.traceless :=
  inverseFourthPowerWeight L • ∑ᶠ x : ↥(sitesInBlock (levelDepth K n) y),
    (⟨ComplexMatrix2.conjugateBy (contourHolonomy .centred W y x.1) (ρ x : ComplexMatrix2),
      conjugateBy_mem_traceless_of_any _ (ρ x).2⟩ : ↥ComplexMatrix2.traceless)
end YangMills.Construction.PeriodicLattice
