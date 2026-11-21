import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem Link.orientedRepresentative_isPositivelyOriented (ℓ : Link a) :
    ℓ.orientedRepresentative.IsPositivelyOriented := by
  by_cases hpos : ℓ.IsPositivelyOriented
  · simp [Link.orientedRepresentative, hpos]
  · simp only [Link.orientedRepresentative, hpos, if_false]
    obtain ⟨μ, e | e⟩ := ℓ.isAdjacent
    · exact (hpos ⟨μ, e⟩).elim
    · refine ⟨μ, ?_⟩
      change ℓ.initial - ℓ.terminal = axisStep a μ
      rw [← neg_sub, e, neg_neg]
open Classical in
def LinkWindow.image (W : LinkWindow a) (r : LatticeSymmetry a) : LinkWindow a where
  links := W.links.image fun ℓ => (r.linkMap ℓ).orientedRepresentative
  isPositive ℓ hℓ := by
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hℓ
    exact Link.orientedRepresentative_isPositivelyOriented _
def supportEndpoints (F : GaugeField a → ℂ) : Set (LatticePoint a) :=
  {x | ∃ ℓ ∈ observableSupport F, x = ℓ.initial ∨ x = ℓ.terminal}
def GaugeTransform.ofFinsetValues (Y : Finset (LatticePoint a))
    (g : Y → Matrices.ComplexMatrix2.specialUnitary) : GaugeTransform a where
  toFun x := open Classical in if hx : x ∈ Y then g ⟨x, hx⟩ else 1
  finite_ne_one := Y.finite_toSet.subset fun x hx => by
    by_contra hY
    exact hx (dif_neg hY)
def gaugeAverage (Y : Finset (LatticePoint a)) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  ∫ g, F ((GaugeTransform.ofFinsetValues Y g).act U) ∂Matrices.ComplexMatrix2.haarPi Y
def IsConvexWeaklyCompact (𝒞 : Set (Measure (GaugeField a))) : Prop :=
  Convex ℝ≥0 𝒞 ∧
    @IsCompact (ProbabilityMeasure (GaugeField a)) (probabilityMeasuresWeakTopology a)
      {ν | (ν : Measure (GaugeField a)) ∈ 𝒞}
def KernelIsConditionalExpectation (ha : 0 < a) (β : ℝ) (W : LinkWindow a) : Prop :=
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    Measurable[W.exteriorSigma] (W.conditionalExpectation ha β F) ∧
    ∀ ν ∈ gibbsClass ha β,
      (∀ H : GaugeField a → ℂ, Measurable[W.exteriorSigma] H → (∃ C : ℝ, ∀ U, ‖H U‖ ≤ C) →
        ∫ U, H U * W.conditionalExpectation ha β F U ∂ν = ∫ U, H U * F U ∂ν) ∧
      W.conditionalExpectation ha β F =ᵐ[ν] ν[F | W.exteriorSigma] ∧
      ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν
def GibbsClassIsGaugeInvariant (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ ν ∈ gibbsClass ha β, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    ∀ g : GaugeTransform a, ∫ U, g.pullback F U ∂ν = ∫ U, F U ∂ν) ∧
  (∀ F ∈ continuousLocalFunctions a, ∃ Y : Finset (LatticePoint a),
    (Y : Set (LatticePoint a)) = supportEndpoints F ∧
    gaugeAverage Y F ∈ continuousLocalFunctions a ∧
    IsGaugeInvariantFunction (gaugeAverage Y F) ∧
    observableSupport (gaugeAverage Y F) ⊆ observableSupport F ∧
    observableSupNorm (gaugeAverage Y F) ≤ observableSupNorm F ∧
    ∀ ν ∈ gibbsClass ha β, ∫ U, gaugeAverage Y F U ∂ν = ∫ U, F U ∂ν) ∧
  ∀ ν₁ ∈ gibbsClass ha β, ∀ ν₂ ∈ gibbsClass ha β,
    (∀ F ∈ continuousLocalFunctions a, IsGaugeInvariantFunction F →
      ∫ U, F U ∂ν₁ = ∫ U, F U ∂ν₂) → ν₁ = ν₂
def KernelIsCovariant (ha : 0 < a) (β : ℝ) (W : LinkWindow a) : Prop :=
  ∀ r : LatticeSymmetry a,
    ((W.image r).links : Set (Link a)) =
      {ℓ | ℓ.IsPositivelyOriented ∧ ∃ m ∈ W.links, ℓ = r.linkMap m ∨ ℓ.opposite = r.linkMap m} ∧
    facesMeeting ((W.image r).links : Set (Link a)) =
      r.plaquetteMap '' facesMeeting (W.links : Set (Link a)) ∧
    (∀ (p : ElementaryPlaquette a) (U : GaugeField a),
      faceEnergy U (r.plaquetteMap p) = faceEnergy (r.pullbackField U) p) ∧
    (∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p)) ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      (W.image r).conditionalExpectation ha β (r.actOn F) =
        r.actOn (W.conditionalExpectation ha β F)) ∧
    ∀ ν ∈ gibbsClass ha β,
      (∀ F ∈ continuousLocalFunctions a,
        ∫ U, r.actOn (W.conditionalExpectation ha β F) U ∂ν =
            ∫ U, (W.image r).conditionalExpectation ha β (r.actOn F) U ∂ν ∧
          ∫ U, (W.image r).conditionalExpectation ha β (r.actOn F) U ∂ν =
            ∫ U, r.actOn F U ∂ν) ∧
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂(ν.map r.pullbackField) = ∫ U, r.actOn F U ∂ν) ∧
      ν.map r.pullbackField ∈ gibbsClass ha β
def GibbsClassStructure : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β →
    (∀ W : LinkWindow a, KernelIsConditionalExpectation ha β W) ∧
    GibbsClassIsGaugeInvariant ha β ∧
    IsConvexWeaklyCompact (gibbsClass ha β) ∧
    (∀ Q : AddSubgroup (LatticePoint a), IsConvexWeaklyCompact (subgroupInvariantGibbsClass ha β Q)) ∧
    ∀ W : LinkWindow a, KernelIsCovariant ha β W
end YangMills.Construction.InfiniteLattice
