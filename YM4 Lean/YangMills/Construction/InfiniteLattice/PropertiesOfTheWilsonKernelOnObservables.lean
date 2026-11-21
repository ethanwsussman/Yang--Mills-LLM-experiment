import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace WilsonOperator
variable {a : ℝ}
def IgnoresLinksOf {E : Type*} (S : Set (Link a)) (F : GaugeField a → E) : Prop :=
  DependsOnlyOnLinks {l | l ∉ S ∧ l.opposite ∉ S} F
structure WeightAndKernelBounds (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) : Prop where
  localWeight_mem : (fun U => (localWeight β Λ U : ℂ)) ∈ continuousCylinderFunctions a
  localWeight_dependsOnlyOn : DependsOnlyOnLinks (thickenedLinks Λ) (localWeight β Λ)
  integrable_kernel : ∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ U : GaugeField a,
    Integrable (fun V => F (splice ha hΛ V U) * (localWeight β Λ (splice ha hΛ V U) : ℂ))
      (Matrices.ComplexMatrix2.haarPi Λ)
  integrable_localPartition : ∀ U : GaugeField a,
    Integrable (fun V => localWeight β Λ (splice ha hΛ V U)) (Matrices.ComplexMatrix2.haarPi Λ)
  localWeight_bounds : ∀ U : GaugeField a,
    Real.exp (-2 * β * touchingFaceCount Λ) ≤ localWeight β Λ U ∧ localWeight β Λ U ≤ 1
  localPartition_bounds : ∀ U : GaugeField a,
    Real.exp (-2 * β * touchingFaceCount Λ) ≤ localPartition ha β hΛ U ∧
      localPartition ha β hΛ U ≤ 1
  kernel_isBoundedObservable : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    IsBoundedObservable (kernelOperator ha β hΛ F)
  kernel_ignoresLinksOf : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    IgnoresLinksOf (Λ : Set (Link a)) (kernelOperator ha β hΛ F)
  supNorm_kernel_le : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    observableSupNorm (kernelOperator ha β hΛ F) ≤ observableSupNorm F
  kernel_add : ∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    kernelOperator ha β hΛ (F + G) = kernelOperator ha β hΛ F + kernelOperator ha β hΛ G
  kernel_smul : ∀ (c : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    kernelOperator ha β hΛ (c • F) = c • kernelOperator ha β hΛ F
  kernel_const_one : kernelOperator ha β hΛ (fun _ => 1) = fun _ => 1
  kernel_nonneg : ∀ F : GaugeField a → ℂ, IsBoundedObservable F → (∀ U, 0 ≤ F U) →
    ∀ U, 0 ≤ kernelOperator ha β hΛ F U
  kernel_tendsto : ∀ (G : ℕ → GaugeField a → ℂ) (F : GaugeField a → ℂ),
    (∀ k, IsBoundedObservable (G k)) → (∃ C : ℝ, ∀ k, observableSupNorm (G k) ≤ C) →
      (∀ U, Tendsto (fun k => G k U) atTop (𝓝 (F U))) →
        ∀ U, Tendsto (fun k => kernelOperator ha β hΛ (G k) U) atTop
          (𝓝 (kernelOperator ha β hΛ F U))
structure DependenceIsMeasurability (a : ℝ) : Prop where
  dependsOnlyOnLinks_iff_measurable : ∀ S : Set (Link a), S ⊆ positiveLinkSet a →
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      (DependsOnlyOnLinks S F ↔ Measurable[linkSigmaAlgebra S] F)
  regionMeasurable_iff : ∀ (S : Set AmbientSpace) (F : GaugeField a → ℂ),
    (IsBoundedObservable F ∧ IsRegionMeasurable S F) ↔
      (IsBoundedObservable F ∧ DependsOnlyOnLinks (linksWithin S : Set (Link a)) F)
structure KernelOnIgnoringObservables (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) : Prop where
  ignoresLinksOf_iff_measurable : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (IgnoresLinksOf (Λ : Set (Link a)) F ↔
      Measurable[linkSigmaAlgebra (positiveLinkSet a \ (Λ : Set (Link a)))] F)
  kernel_mul_left : ∀ H : GaugeField a → ℂ, IsBoundedObservable H →
    IgnoresLinksOf (Λ : Set (Link a)) H → ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      kernelOperator ha β hΛ (H * F) = H * kernelOperator ha β hΛ F
  kernel_of_ignores : ∀ H : GaugeField a → ℂ, IsBoundedObservable H →
    IgnoresLinksOf (Λ : Set (Link a)) H → kernelOperator ha β hΛ H = H
structure KernelDependence (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) : Prop where
  kernel_dependsOnlyOn_diff : ∀ S : Set (Link a), thickenedLinks Λ ⊆ S → S ⊆ positiveLinkSet a →
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F → DependsOnlyOnLinks S F →
      DependsOnlyOnLinks (S \ (Λ : Set (Link a))) (kernelOperator ha β hΛ F)
  kernel_mem_continuousCylinderFunctions : ∀ F ∈ continuousCylinderFunctions a,
    kernelOperator ha β hΛ F ∈ continuousCylinderFunctions a
def GibbsPropertyEquivalences (ha : 0 < a) (β : ℝ) (ν : GaugeFieldProbability a) : Prop :=
  List.TFAE
    [IsGibbs β ν.1,
      ∀ (Λ : Finset (Link a)) (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a)
        (F : GaugeField a → ℂ), IsBoundedObservable F →
          ν.expect (kernelOperator ha β hΛ F) = ν.expect F,
      ∀ (Λ : Finset (Link a)) (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a),
        ∀ F ∈ continuousCylinderFunctions a, ν.expect (kernelOperator ha β hΛ F) = ν.expect F]
end WilsonOperator
open WilsonOperator in
def WilsonOperatorProperties : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K →
    ∀ (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) (β : ℝ), 0 < β →
      (∀ (Λ : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
        (hΛ : (Λ : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆ cutoffLinks L K),
          WeightAndKernelBounds ha β hΛ ∧ KernelOnIgnoringObservables ha β hΛ ∧
            KernelDependence ha β hΛ) ∧
        DependenceIsMeasurability (PeriodicLattice.meshSize L (K : ℤ)) ∧
          ∀ ν : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)),
            GibbsPropertyEquivalences ha β ν
end YangMills.Construction.InfiniteLattice
