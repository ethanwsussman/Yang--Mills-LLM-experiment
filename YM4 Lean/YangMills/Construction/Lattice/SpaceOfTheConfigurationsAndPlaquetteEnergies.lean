import YangMills.Construction.Lattice.DataOfOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CutoffData.ConfigSpace
variable (d : CutoffData)
def linkValue (b : d.Bond) (U : d.GaugeField) : Matrices.ComplexMatrix2.specialUnitary :=
  ⟨U.1 b, U.2.1 b (mem_univ b)⟩
def FiniteBondsAndCoordinates : Prop :=
  Finite d.PosBond ∧ Nonempty d.PosBond ∧
  Finite d.Plaquette ∧ Nonempty d.Plaquette ∧
  (∀ b : d.Bond, Xor b.IsPositivelyOriented (∃! b' : d.PosBond, b'.1.opposite = b)) ∧
  Function.Bijective d.restrictPositive
def TopologyAndHaar : Prop :=
  SeparableSpace d.GaugeField ∧ MetrizableSpace d.GaugeField ∧
  IsProbabilityMeasure d.haarOnGaugeFields ∧
  IsProbabilityMeasure d.haar ∧
  ∀ b : d.Bond, Continuous (linkValue d b)
def WeightedEnergyBounds (E : (d.Bond → Matrices.ComplexMatrix2) → ℂ) (w : d.Plaquette → ℂ) : Prop :=
  Continuous (fun U : d.GaugeField => E U.1) ∧
  ((∀ p, (w p).im = 0) → ∀ U : d.GaugeField, (E U.1).im = 0) ∧
  (∀ U : d.GaugeField, ‖E U.1‖ ≤ 2 * ∑ᶠ p : d.Plaquette, ‖w p‖) ∧
  (∀ U : d.GaugeField,
    ‖Complex.exp (-E U.1)‖ ≤ Real.exp (2 * ∑ᶠ p : d.Plaquette, ‖w p‖)) ∧
  Continuous (fun U : d.GaugeField => Complex.exp (-E U.1)) ∧
  (∃ C : ℝ, ∀ U : d.GaugeField, ‖Complex.exp (-E U.1)‖ ≤ C) ∧
  Integrable (fun U : d.GaugeField => Complex.exp (-E U.1)) d.haarOnGaugeFields ∧
  Integrable (fun U : d.Bond → Matrices.ComplexMatrix2 => Complex.exp (-E U)) d.haar
def PlaquetteTermBounds : Prop :=
  (∀ p : d.Plaquette, Continuous (fun U : d.GaugeField => d.plaquetteTerm U.1 p) ∧
    ∀ U : d.GaugeField, ∃ r ∈ Icc (0 : ℝ) 2, d.plaquetteTerm U.1 p = (r : ℂ)) ∧
  (∀ c : d.Plaquette → ℂ, WeightedEnergyBounds d (d.weightedByPlaquettes c) c) ∧
  ∀ c : d.Torus → ℂ,
    WeightedEnergyBounds d (d.weightedByTorus c) fun p => c p.barycenter
def BasicStructure : Prop :=
  ∀ d : CutoffData, FiniteBondsAndCoordinates d ∧ TopologyAndHaar d ∧ PlaquetteTermBounds d
end YangMills.Construction.PeriodicLattice.CutoffData.ConfigSpace
