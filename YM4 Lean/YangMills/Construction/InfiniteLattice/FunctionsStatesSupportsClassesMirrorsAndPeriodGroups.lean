import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import YangMills.Construction.InfiniteLattice.ReflectionInALatticeMirrorGivenWithANormal
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory GibbsAtFixedSpacing NormalFamilies LatticeConventions
open scoped ComplexConjugate Matrix
namespace InfiniteLattice
namespace BasicStructure
def CompactAndLocalDense (a : ℝ) : Prop :=
  CompactSpace (GaugeField a) ∧
  TopologicalSpace.MetrizableSpace (GaugeField a) ∧
  borel (GaugeField a) = linkSigma (Set.univ : Set (Link a)) ∧
  InfiniteLattice.continuousLocalFunctions a ⊆ continuousFns a ∧
  (∀ F ∈ InfiniteLattice.continuousLocalFunctions a, ∀ G ∈ InfiniteLattice.continuousLocalFunctions a,
    F + G ∈ InfiniteLattice.continuousLocalFunctions a ∧ F * G ∈ InfiniteLattice.continuousLocalFunctions a) ∧
  (∀ (z : ℂ), ∀ F ∈ InfiniteLattice.continuousLocalFunctions a, z • F ∈ InfiniteLattice.continuousLocalFunctions a) ∧
  (∀ z : ℂ, (fun _ => z) ∈ InfiniteLattice.continuousLocalFunctions a) ∧
  (∀ F ∈ InfiniteLattice.continuousLocalFunctions a, (fun U => conj (F U)) ∈ InfiniteLattice.continuousLocalFunctions a) ∧
  (∃ D : Set (GaugeField a → ℂ), D.Countable ∧ D ⊆ InfiniteLattice.continuousLocalFunctions a ∧
    IsSupNormDenseIn D (continuousFns a)) ∧
  IsSupNormDenseIn (InfiniteLattice.continuousLocalFunctions a) (continuousFns a) ∧
  IsSupNormDenseIn (InfiniteLattice.continuousLocalFunctions a ∩ realContinuous a)
    (realContinuous a)
def SymmetryActionFacts (a : ℝ) : Prop :=
  ∀ r s : LatticeSymmetry a,
    IsHomeomorph r.pullbackField ∧
    (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
      r.actOn (F * G) = r.actOn F * r.actOn G ∧
      r.actOn (fun U => conj (F U)) = (fun U => conj (r.actOn F U)) ∧
      r.actOn (fun U => ‖F U‖) = (fun U => ‖r.actOn F U‖) ∧
      (r.comp s).actOn F = r.actOn (s.actOn F)) ∧
    (∀ (S : Set AmbientSpace) (F : GaugeField a → ℂ), F ∈ regionObservables a S →
      r.actOn F ∈ regionObservables a (r.imageSet S)) ∧
    (∀ F ∈ continuousFns a, r.actOn F ∈ continuousFns a) ∧
    (∀ F ∈ InfiniteLattice.continuousLocalFunctions a, r.actOn F ∈ InfiniteLattice.continuousLocalFunctions a)
def StateFacts (a : ℝ) : Prop :=
  (∀ μ μ' : Measure (GaugeField a), IsLatticeState μ → IsLatticeState μ' →
    (∀ F ∈ InfiniteLattice.continuousLocalFunctions a, stateEval μ F = stateEval μ' F) → μ = μ') ∧
  (∀ (μ : Measure (GaugeField a)) (N : Set (Measure (GaugeField a))), IsLatticeState μ →
    IsWeakBasicNhd μ N → IsWeakOpen N ∧ μ ∈ N) ∧
  (∀ (μ : ProbabilityMeasure (GaugeField a)) (N : Set (ProbabilityMeasure (GaugeField a))),
    N ∈ @nhds _ (probabilityMeasuresWeakTopology a) μ →
      ∃ B : Set (Measure (GaugeField a)),
        IsWeakBasicNhd (μ : Measure (GaugeField a)) B ∧ asProbabilityMeasures B ⊆ N) ∧
  (∀ (μ : ℕ → Measure (GaugeField a)) (μ₀ : Measure (GaugeField a)),
    (∀ i, 1 ≤ i → IsLatticeState (μ i)) → IsLatticeState μ₀ →
      (IsWeakClusterPoint μ μ₀ ↔
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ StatesTendstoWeakly (μ ∘ φ) μ₀)) ∧
  (∀ μ : ℕ → Measure (GaugeField a), (∀ i, 1 ≤ i → IsLatticeState (μ i)) →
    ∃ μ₀, IsLatticeState μ₀ ∧ IsWeakClusterPoint μ μ₀) ∧
  IsWeakCompact {ρ : Measure (GaugeField a) | IsLatticeState ρ} ∧
  (∀ (μ : Measure (GaugeField a)) (r : LatticeSymmetry a), IsLatticeState μ →
    (IsSymmetricUnder μ r ↔
      ∀ F ∈ continuousFns a, stateEval μ (r.actOn F) = stateEval μ F)) ∧
  (∀ μ : Measure (GaugeField a), IsLatticeState μ →
    ∃ G : Subgroup (Equiv.Perm AmbientSpace), ∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = f ∧ IsSymmetricUnder μ r) ↔ ∃ g ∈ G, ⇑g = f)
def SigmaAlgebraFacts (a : ℝ) : Prop :=
  (∀ M M' : Set (Link a), IsLinkSet M → IsLinkSet M' →
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      (Measurable[linkSigma M] F ↔ DependsOnlyOn M F) ∧
      (DependsOnlyOn M F → DependsOnlyOn M' F →
        DependsOnlyOn (M ∩ M') F)) ∧
  (∀ S : Set AmbientSpace, regionObservables a S =
    {F | IsBoundedObservable F ∧ Measurable[linkSigma (positiveLinksWithin a S)] F}) ∧
  (∀ (S S' : Set AmbientSpace) (F : GaugeField a → ℂ), IsBoundedObservable F →
    IsRegionMeasurable S F → IsRegionMeasurable S' F → IsRegionMeasurable (S ∩ S') F)
def SupportFacts (a : ℝ) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsLocalObservable F →
    (observableSupport F).Finite ∧
    DependsOnlyOn (observableSupport F) F ∧
    ∀ M : Set (Link a), IsLinkSet M → DependsOnlyOn M F →
      observableSupport F ⊆ M) ∧
  ∀ F ∈ InfiniteLattice.continuousLocalFunctions a, ∀ v : LatticePoint a,
    (shift v).actOn F ∈ InfiniteLattice.continuousLocalFunctions a ∧
    observableSupport ((shift v).actOn F) =
      shiftLinks (observableSupport F) v
def gibbsClass_antitone_period {a : ℝ} (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ Q' Q : AddSubgroup (LatticePoint a), Q' ≤ Q →
    subgroupInvariantGibbsClass ha β Q ⊆ subgroupInvariantGibbsClass ha β Q'
def KernelAndClassFacts {a : ℝ} (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ (W : LinkWindow a) (F : GaugeField a → ℂ), IsBoundedObservable F →
    IsBoundedObservable (W.conditionalExpectation ha β F) ∧
    observableSupNorm (W.conditionalExpectation ha β F) ≤ observableSupNorm F ∧
    (∀ H : GaugeField a → ℂ, IsBoundedObservable H → Measurable[W.exteriorSigma] H →
      W.conditionalExpectation ha β (H * F) = H * W.conditionalExpectation ha β F) ∧
    (F ∈ InfiniteLattice.continuousLocalFunctions a →
      W.conditionalExpectation ha β F ∈ InfiniteLattice.continuousLocalFunctions a)) ∧
  InfiniteLattice.gibbsClass ha β = {μ | IsGibbs β μ} ∧
  periodicGibbsClass ha β = {μ | IsPeriodicGibbs β μ} ∧
  subgroupInvariantGibbsClass ha β ⊤ = {μ | IsGibbs β μ ∧ IsShiftInvariant μ}
def MirrorDescriptionsAgree (a : ℝ) : Prop :=
  (∀ P : NormalLevelPair a,
    (∃ r : LatticeSymmetry a, r.toFun = reflectAcross P.normal P.level) ∧
    reflectAcross P.normal P.level ∘ reflectAcross P.normal P.level = id) ∧
  (∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a),
    ∃ (P : NormalLevelPair a) (ς : ℤˣ),
      ((Q.normal ∈ normalSet ∧ P.normal = Q.normal ∧ P.level = Q.level ∧ ς = 1) ∨
        (Q.normal ∉ normalSet ∧ P.normal = -Q.normal ∧ P.level = -Q.level ∧ ς = -1)) ∧
      Q.carrier = {x | P.normal ⬝ᵥ x = P.level} ∧
      Q.reflect = reflectAcross P.normal P.level ∧
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        (fun U => conj ((NormalHyperplane.reflectSymmetry hQ).actOn F U)) =
          P.conjReflectObservable F) ∧
      regionObservables a Q.upperHalfSpace = halfSpaceObservables a P.normal P.level ς ∧
      regionObservables a Q.lowerHalfSpace = halfSpaceObservables a P.normal P.level (-ς)) ∧
  ∀ P : NormalLevelPair a,
    ∃ Q : NormalHyperplane, Q.normal = P.normal ∧ Q.level = P.level ∧
      Q.IsLatticeMirror a
def PeriodLatticeFacts : Prop :=
  ∀ n ∈ normalSet, ∀ h : ℤ, Even h → 2 ≤ h →
    n ⬝ᵥ firstNonzeroBasisVec n = 1 ∧
    (∀ x ∈ latticeSubgroup 1, ∃ k : ℤ, n ⬝ᵥ x = (k : ℝ)) ∧
    normalPeriodLattice n h ≤ axialPeriodLattice n h ∧
    axialPeriodLattice n h ≤ evenLattice ∧
    (normalPeriodLattice n h).relIndex (axialPeriodLattice n h) = 2 ∧
    latticeSubgroup (2 * (h : ℝ)) ≤ normalPeriodLattice n h ∧
    (normalPeriodLattice n h ≤ latticeSubgroup 1 ∧ (normalPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0) ∧
    (axialPeriodLattice n h ≤ latticeSubgroup 1 ∧ (axialPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0)
def Statement : Prop :=
  (∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β →
    CompactAndLocalDense a ∧ SymmetryActionFacts a ∧
    StateFacts a ∧ SigmaAlgebraFacts a ∧ SupportFacts a ∧
    gibbsClass_antitone_period ha β ∧ KernelAndClassFacts ha β ∧
    MirrorDescriptionsAgree a) ∧
  PeriodLatticeFacts
end BasicStructure
end InfiniteLattice
end YangMills.Construction
end
