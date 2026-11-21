import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.SoftAverages.ModelsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Quaternion Topology
namespace YangMills.Construction
namespace TorusLimits
abbrev FineField (L K : ℕ) : Type :=
  InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))
abbrev WindowLink (R : ℕ) : Type := {b : (Fin 4 → ℤ) × Fin 4 // TorusFields.BondOffsetInBox R b}
abbrev WindowValuation (R : ℕ) : Type := WindowLink R → Matrices.ComplexMatrix2
structure IsBoundedWindowObservable {R : ℕ} (G : WindowValuation R → ℝ) : Prop where
  measurable : @Measurable _ _ (borel _) _ G
  bounded : ∃ C : ℝ, ∀ v, |G v| ≤ C
def latticePointOfInt (a : ℝ) (h : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨fun μ => (h μ : ℝ) * a, h, fun _ => rfl⟩
def evalOnTorus {R N : ℕ} (G : WindowValuation R → ℝ) (W : TorusFields.TorusField N) : ℝ :=
  G fun b => SoftAverages.quaternionToMatrix
    ((W (TorusFields.siteOfInt b.1.1) b.1.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ])
def evalOnField {R : ℕ} {a : ℝ} (G : WindowValuation R → ℝ) (U : InfiniteLattice.GaugeField a) : ℝ :=
  G fun b => ((U (InfiniteLattice.Link.forwardFrom (latticePointOfInt a b.1.1) b.1.2) :
    Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)
def IsTorusLimitAlong (L K : ℕ) (β : ℝ) (ν : Measure (FineField L K)) (ms : ℕ → ℕ) : Prop :=
  (∀ i, 0 < ms i) ∧ StrictMono ms ∧
    ∀ A : FineField L K → ℂ, Continuous A →
      Tendsto (fun i => ∫ U, A U ∂InfiniteLattice.liftedWilsonMeasure L (ms i) K β) atTop
        (𝓝 (∫ U, A U ∂ν))
def fineShift (L K : ℕ) (h : Fin 4 → ℤ) : FineField L K → FineField L K :=
  (InfiniteLattice.shift (latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h)).pullbackField
@[reducible] def periodicSigma (L K p : ℕ) : MeasurableSpace (FineField L K) :=
  MeasurableSpace.generateFrom
    {I | MeasurableSet I ∧ ∀ h : Fin 4 → ℤ, fineShift L K (fun i => (p : ℤ) * h i) ⁻¹' I = I}
structure IsPeriodicConditionalKernel (L K : ℕ) (ν : Measure (FineField L K)) (p : ℕ)
    (κ : ProbabilityTheory.Kernel (FineField L K) (FineField L K)) : Prop where
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel κ
  ae_eq_condExp : ∀ B : Set (FineField L K), MeasurableSet B →
    (fun U => (κ U B).toReal) =ᵐ[ν] (ν[B.indicator (fun _ => (1 : ℝ)) | periodicSigma L K p])
end TorusLimits
end YangMills.Construction
end
