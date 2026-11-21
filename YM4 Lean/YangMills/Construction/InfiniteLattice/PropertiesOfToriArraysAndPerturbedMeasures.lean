import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def tripleCube (x : LatticePoint a) : Set (LatticePoint a) :=
  {y | ∃ w : Fin 4 → ℤ, (∀ μ, 0 ≤ w μ ∧ w μ ≤ 2) ∧
    ∀ μ, (y : AmbientSpace) μ = (x : AmbientSpace) μ + (w μ : ℝ) * a}
def PositiveLink.forwardAt (x : LatticePoint a) (μ : Fin 4) : PositiveLink a :=
  ⟨Link.forwardFrom x μ, μ, add_sub_cancel_left x (axisStep a μ)⟩
def cubicSublattice (a c : ℝ) : AddSubgroup (LatticePoint a) :=
  (latticeSubgroup c).addSubgroupOf (latticeSubgroup a)
namespace PeriodSublattice
variable (Γ : PeriodSublattice a)
def invariantFields : Set (GaugeField a) :=
  {U | ∀ γ ∈ Γ.periods, (shift γ).pullbackField U = U}
structure IsFaithfulQuotient : Prop where
  periods_finiteIndex : Γ.periods.FiniteIndex
  finite_quotientTorus : Finite Γ.QuotientTorus
  finite_quotientLink : Finite Γ.QuotientLink
  finite_quotientPlaquette : Finite Γ.QuotientPlaquette
  link_equiv : ∃ e : Γ.QuotientLink ≃ Γ.QuotientTorus × Fin 4, ∀ (x : LatticePoint a) (μ : Fin 4),
    e (Γ.linkClass (PositiveLink.forwardAt x μ)) = (Γ.quotientMap x, μ)
  plaquette_equiv : ∃ e : Γ.QuotientPlaquette ≃ {t : Γ.QuotientTorus × Fin 4 × Fin 4 // t.2.1 < t.2.2},
    ∀ p : ElementaryPlaquette a,
      e (Γ.faceClass p) =
        ⟨(Γ.quotientMap p.corner, p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩
  injOn_tripleCube : ∀ x : LatticePoint a, InjOn Γ.quotientMap (tripleCube x)
  linkEndpoints_linkClass : ∀ b : PositiveLink a,
    Γ.linkEndpoints (Γ.linkClass b) = {Γ.quotientMap b.1.initial, Γ.quotientMap b.1.terminal}
  plaquetteVertices_faceClass : ∀ p : ElementaryPlaquette a,
    Γ.plaquetteVertices (Γ.faceClass p) = Γ.quotientMap '' p.cornerSet
  plaquetteLinks_faceClass : ∀ p : ElementaryPlaquette a,
    Γ.plaquetteLinks (Γ.faceClass p) =
      {c | ∃ b : PositiveLink a, b.1 ∈ p.linkSet ∧ c = Γ.linkClass b}
  ncard_linkEndpoints : ∀ c : Γ.QuotientLink, (Γ.linkEndpoints c).ncard = 2
  ncard_plaquetteVertices : ∀ p : Γ.QuotientPlaquette, (Γ.plaquetteVertices p).ncard = 4
  ncard_plaquetteLinks : ∀ p : Γ.QuotientPlaquette, (Γ.plaquetteLinks p).ncard = 4
  link_eq_of_shared_endpoint : ∀ b b' : PositiveLink a, b' ∈ Γ.linkOrbit b →
    (({b.1.initial, b.1.terminal} ∩ {b'.1.initial, b'.1.terminal} : Set (LatticePoint a))).Nonempty →
      b' = b
  plaquette_eq_of_shared_corner : ∀ p p' : ElementaryPlaquette a, p' ∈ Γ.plaquetteOrbit p →
    (p.cornerSet ∩ p'.cornerSet).Nonempty → p' = p
structure LiftIsFaithful : Prop where
  isEmbedding_lift : Topology.IsEmbedding Γ.lift
  range_lift : range Γ.lift = Γ.invariantFields
  continuous_periodize : ∀ F ∈ continuousLocalFunctions a, Continuous (Γ.periodize F)
  periodize_actOn_shift : ∀ F ∈ continuousLocalFunctions a, ∀ γ ∈ Γ.periods,
    Γ.periodize ((shift γ).actOn F) = Γ.periodize F
  faceEnergy_lift : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette) (q : ElementaryPlaquette a),
    q ∈ (p : Set (ElementaryPlaquette a)) →
      faceEnergy (Γ.lift U) q = Γ.quotientFaceEnergy U p
  continuous_quotientFaceEnergy :
    ∀ p : Γ.QuotientPlaquette, Continuous fun U => Γ.quotientFaceEnergy U p
  quotientFaceEnergy_mem_Icc : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
    Γ.quotientFaceEnergy U p ∈ Icc (0 : ℝ) 2
structure GibbsMeasuresAreProbability (β : ℝ) : Prop where
  exp_le_partitionFunction :
    Real.exp (-2 * β * (Nat.card Γ.QuotientPlaquette : ℝ)) ≤ Γ.partitionFunction β
  partitionFunction_le_one : Γ.partitionFunction β ≤ 1
  isProbabilityMeasure_gibbs : IsProbabilityMeasure (Γ.gibbsMeasure β)
  isProbabilityMeasure_lifted : IsProbabilityMeasure (Γ.liftedGibbsMeasure β)
  integral_lifted : ∀ F ∈ continuousLocalFunctions a,
    ∫ U, F U ∂Γ.liftedGibbsMeasure β = ∫ U, Γ.periodize F U ∂Γ.gibbsMeasure β
end PeriodSublattice
namespace LocalObservableArray
variable (A : LocalObservableArray)
structure SupportsLocallyFinite : Prop where
  observableSupport_translate : ∀ i : A.Label, observableSupport (A.translate i) =
    shiftLinks (observableSupport (A.gen i.2)) (i.1 : LatticePoint 1)
  finite_labels_at_link : ∀ b ∈ positiveLinks 1,
    {i : A.Label | b ∈ observableSupport (A.translate i)}.Finite
  finite_labelsTouching : ∀ W : LinkWindow 1, (A.labelsTouching W).Finite
structure TiltedKernelWellDefined (β t : ℝ) : Prop where
  windowEnergy_mem : ∀ W : LinkWindow 1,
    (fun U => (A.windowEnergy β t W U : ℂ)) ∈ continuousLocalFunctions 1
  windowPartition_pos : ∀ (W : LinkWindow 1) (U : GaugeField 1), 0 < A.windowPartition β t W U
  integrable_weighted : ∀ (W : LinkWindow 1) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
    ∀ U : GaugeField 1, Integrable (fun V => F (W.glue one_pos V U) *
      (Real.exp (-A.windowEnergy β t W (W.glue one_pos V U)) : ℂ)) W.haarProd
  isBoundedObservable_tiltedKernel : ∀ (W : LinkWindow 1) (F : GaugeField 1 → ℂ),
    IsBoundedObservable F → IsBoundedObservable (A.tiltedKernel β t W F)
  supNorm_tiltedKernel_le : ∀ (W : LinkWindow 1) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
    observableSupNorm (A.tiltedKernel β t W F) ≤ observableSupNorm F
  tiltedKernel_zero : ∀ (W : LinkWindow 1) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
    A.tiltedKernel β 0 W F = W.conditionalExpectation one_pos β F
  tiltedGibbsClass_zero : A.tiltedGibbsClass β 0 = gibbsClass one_pos β
variable (Γ : PeriodSublattice 1)
structure PeriodicDescentWellDefined (β t : ℝ) : Prop where
  finite_cosets : Finite (A.Cosets Γ)
  periodize_translate : ∀ (v v' : A.sublattice) (ι : Fin A.size),
    (QuotientAddGroup.mk v : A.Cosets Γ) = QuotientAddGroup.mk v' →
      Γ.periodize (A.translate (v, ι)) = Γ.periodize (A.translate (v', ι))
  continuous_periodicSum : Continuous (A.periodicSum Γ)
  bounded_periodicSum : ∃ C : ℝ, ∀ U, |A.periodicSum Γ U| ≤ C
  tiltedPartition_pos : 0 < A.tiltedPartition Γ β t
  isProbabilityMeasure_tilted : IsProbabilityMeasure (A.tiltedMeasure Γ β t)
  isProbabilityMeasure_tiltedLift : IsProbabilityMeasure (A.tiltedLiftMeasure Γ β t)
  tiltedPartition_zero : A.tiltedPartition Γ β 0 = Γ.partitionFunction β
  tiltedMeasure_zero : A.tiltedMeasure Γ β 0 = Γ.gibbsMeasure β
end LocalObservableArray
def CubicSublatticesInsideSubgroups : Prop :=
  ∀ Q : AddSubgroup (LatticePoint 1), Q.FiniteIndex → ∀ s : ℕ, 3 ≤ s → Q.index ∣ s →
    latticeSubgroup (s : ℝ) ≤ latticeSubgroup 1 ∧
      ∃ Γ : PeriodSublattice 1, Γ.periods = cubicSublattice 1 s ∧ Γ.periods ≤ Q
def CubicTorusLiftsPeriodically (d : Conventions.StandingParameters) (β : ℝ) : Prop :=
  latticeSubgroup d.side ≤ latticeSubgroup (PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ)) ∧
    ∃ Γ : PeriodSublattice (PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ)),
      Γ.periods = cubicSublattice _ d.side ∧
      Function.Injective
        (liftCompactField : PeriodicLattice.CompactGaugeField d.L d.m ((d.K : ℕ) : ℤ) → _) ∧
      range (liftCompactField : PeriodicLattice.CompactGaugeField d.L d.m ((d.K : ℕ) : ℤ) → _) =
        periodicFields d.L d.m ((d.K : ℕ) : ℤ) ∧
      liftedWilsonMeasure d.L d.m d.K β = Γ.liftedGibbsMeasure β
end InfiniteLattice
end YangMills.Construction
