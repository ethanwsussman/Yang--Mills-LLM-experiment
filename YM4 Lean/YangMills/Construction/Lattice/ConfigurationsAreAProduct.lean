import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open Matrices Conventions
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def restrictToPositiveBonds (U : CompactGaugeField L m j) : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary :=
  fun b => U.linkValue b.1
def IsProductHaarImage (L m : ℕ) (j : ℤ) (μ : Measure (CompactGaugeField L m j)) : Prop :=
  μ.map restrictToPositiveBonds = ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)
def gaugeFieldMeasure (L m : ℕ) (j : ℤ) : Measure (CompactGaugeField L m j) :=
  Classical.epsilon (IsProductHaarImage L m j)
def reindexFactors {S S' : Type} (u : S ≃ S') (g : S → ComplexMatrix2.specialUnitary) :
    S' → ComplexMatrix2.specialUnitary :=
  fun σ' => g (u.symm σ')
end PeriodicLattice
namespace GaugeFieldProduct
open PeriodicLattice
def MeshAndOrientation (L m : ℕ) (j : ℤ) : Prop :=
  torusSide L m / meshSize L j = 2 * (L : ℝ) ^ ((m : ℤ) + j) ∧ 2 < 2 * (L : ℝ) ^ ((m : ℤ) + j) ∧
    0 < meshSize L j ∧ meshSize L j < 2 * meshSize L j ∧ 2 * meshSize L j < torusSide L m ∧
    ∀ b : Bond L m j, Xor (Bond.IsPositivelyOriented b) (Bond.IsPositivelyOriented b.opposite)
def FiniteAndNonempty (L m : ℕ) (j : ℤ) : Prop :=
  (Finite (Site L m j) ∧ Nonempty (Site L m j)) ∧
    (Finite (PositivelyOrientedBond L m j) ∧ Nonempty (PositivelyOrientedBond L m j)) ∧
      (Finite (Plaquette L m j) ∧ Nonempty (Plaquette L m j))
def ProductStructure (L m : ℕ) (j : ℤ) : Prop :=
  Function.Bijective (restrictToPositiveBonds : CompactGaugeField L m j → _) ∧
    (∃ e : CompactGaugeField L m j ≃ₜ (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary),
      ⇑e = restrictToPositiveBonds) ∧
    CompactSpace (CompactGaugeField L m j) ∧
    TopologicalSpace.MetrizableSpace (CompactGaugeField L m j) ∧
    (∃! μ : Measure (CompactGaugeField L m j), IsProductHaarImage L m j μ) ∧
    IsProductHaarImage L m j (gaugeFieldMeasure L m j) ∧
    IsProbabilityMeasure (gaugeFieldMeasure L m j)
def PlaquetteEnergyContinuousBounded (L m : ℕ) (j : ℤ) : Prop :=
  ∀ p : Plaquette L m j,
    Continuous (fun U : CompactGaugeField L m j => plaquetteEnergy U.1 p) ∧
      ∀ U : CompactGaugeField L m j,
        plaquetteEnergy U.1 p ∈ (fun t : ℝ => (t : ℂ)) '' Icc (0 : ℝ) 2
def ReindexingFactors : Prop :=
  ∀ (S S' : Type) [Finite S] [Finite S'] (u : S ≃ S'),
    (∃ e : (S → ComplexMatrix2.specialUnitary) ≃ₜ (S' → ComplexMatrix2.specialUnitary),
      ⇑e = reindexFactors u) ∧
      (ComplexMatrix2.haarPi S).map (reindexFactors u) = ComplexMatrix2.haarPi S'
def Statement : Prop :=
  (∀ (L m : ℕ) (j : ℤ), IsAdmissibleBlockingFactor L → 0 < m → 0 ≤ j →
    MeshAndOrientation L m j ∧ FiniteAndNonempty L m j ∧ ProductStructure L m j ∧
      PlaquetteEnergyContinuousBounded L m j) ∧
    ReindexingFactors
end GaugeFieldProduct
end YangMills.Construction
