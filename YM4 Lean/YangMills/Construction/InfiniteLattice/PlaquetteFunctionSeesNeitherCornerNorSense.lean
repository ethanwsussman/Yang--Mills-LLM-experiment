import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction
namespace GibbsAtFixedSpacing
def RealTraceConjInvInvariant : Prop :=
  ∀ g V : Matrices.ComplexMatrix2.specialUnitary,
    (Matrices.ComplexMatrix2.fullTrace
        ((g * V * g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
      (Matrices.ComplexMatrix2.fullTrace (V : Matrices.ComplexMatrix2)).re ∧
    (Matrices.ComplexMatrix2.fullTrace
        ((V⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
      (Matrices.ComplexMatrix2.fullTrace (V : Matrices.ComplexMatrix2)).re
def FaceEnergyDeterminedByCorners {a : ℝ} (p : ElementaryPlaquette a) (U : GaugeField a) :
    Prop :=
  (∀ c c' : BoundaryCycle p,
    (Matrices.ComplexMatrix2.fullTrace (c.holonomy U : Matrices.ComplexMatrix2)).re =
      (Matrices.ComplexMatrix2.fullTrace (c'.holonomy U : Matrices.ComplexMatrix2)).re) ∧
  Nat.card (BoundaryCycle p) = 8 ∧
  (∃ c : BoundaryCycle p, c.holonomy U = faceHolonomy U p) ∧
  ∀ q : ElementaryPlaquette a, q.cornerSet = p.cornerSet → faceEnergy U q = faceEnergy U p
def FaceEnergyIsLocalInEdges {a : ℝ} (p : ElementaryPlaquette a) : Prop :=
  (edgesOf p).ncard = 4 ∧
  (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)) ∈ continuousLocal a ∧
  DependsOnlyOnLinks (edgesOf p) (fun U : GaugeField a => faceEnergy U p) ∧
  ∀ U : GaugeField a, 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2
def FaceEnergyIndependentOfBasepointAndOrientation : Prop :=
  RealTraceConjInvInvariant ∧
  ∀ (a : ℝ), 0 < a →
    (∀ (p : ElementaryPlaquette a) (U : GaugeField a), FaceEnergyDeterminedByCorners p U) ∧
    (∀ p : ElementaryPlaquette a, FaceEnergyIsLocalInEdges p) ∧
    (∀ p q : ElementaryPlaquette a, p.cornerSet = q.cornerSet → p = q) ∧
    ∀ e ∈ positiveLinkSet a, {p : ElementaryPlaquette a | e ∈ edgesOf p}.ncard = 6
end GibbsAtFixedSpacing
end YangMills.Construction
