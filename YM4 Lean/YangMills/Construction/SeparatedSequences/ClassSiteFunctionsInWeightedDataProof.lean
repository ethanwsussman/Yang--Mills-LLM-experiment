import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ClassGeometryInWeightedData
import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedDataProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import YangMills.Construction.SeparatedSequences.WeightsOfAClassSequenceAtOne
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.WeightedScalarDataProof
open SingleSequence SingleSequence.SequenceData
section Comparison
variable {X X' Y Y' : Type}
theorem pairsUniquely_of_equiv (e : X ≃ X') {R : X → X' → Prop} (h : ∀ x x', R x x' ↔ e x = x') :
    PairsUniquely R := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.pairsUniquely_of_equiv <;> assumption
end Comparison
variable (s : SequenceData) {D : Weighted.TorusData} {B : Weighted.SeparatedChain D}
theorem torusData_side_ne_zero (D : Weighted.TorusData) : D.side ≠ 0 := by
  obtain ⟨k, hk, h⟩ := D.side_multiple
  have hL : 0 < D.L := by
    have := D.blocking.three_le_factor
    omega
  have hM : 0 < D.blockNumber := lt_of_lt_of_le hL D.le_blockNumber
  have := D.bareSpacing_pos
  rw [h]
  positivity
def torusAddEquiv (D : Weighted.TorusData) : s.data.Point ≃+ D.Space :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ D.side s.torusSide_ne_zero (torusData_side_ne_zero D)
theorem torusAddEquiv_apply (D : Weighted.TorusData) (x : s.data.Point) :
    torusAddEquiv s D x = s.toTorus D.side x := by
  unfold SequenceData.toTorus
  rw [dif_pos (torusData_side_ne_zero D)]
  rfl
variable {s}
def bareSiteEquiv (G : s.WeightedGeometry B) : s.data.BareSite ≃ D.BareSite :=
  Equiv.subtypeEquiv (torusAddEquiv s D).toEquiv fun a => by
    have h := G.sublattices 0 (Nat.zero_le _)
    beta_reduce at h
    show a ∈ _ ↔ torusAddEquiv s D a ∈ D.latticeAt (D.scale 0)
    rw [← h, torusAddEquiv_apply]
    constructor
    · exact fun ha => ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hab⟩
      have : b = a := (torusAddEquiv s D).injective (by rw [torusAddEquiv_apply, torusAddEquiv_apply, hab])
      exact this ▸ hb
theorem bareSiteEquiv_coe (G : s.WeightedGeometry B) (x : s.data.BareSite) :
    ((bareSiteEquiv G x : D.BareSite) : D.Space) = s.toTorus D.side (x : s.data.Point) := by
  rw [← torusAddEquiv_apply]
  rfl
def apexEquiv (G : s.WeightedGeometry B) :
    ↥(s.params.allLayerPoints s.Ω) ≃ ↥B.allSites :=
  Equiv.subtypeEquiv (torusAddEquiv s D).toEquiv fun a => by
    have h := G.allLayerSites
    show a ∈ _ ↔ torusAddEquiv s D a ∈ B.allSites
    rw [← h, torusAddEquiv_apply]
    constructor
    · exact fun ha => ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hab⟩
      have : b = a := (torusAddEquiv s D).injective (by rw [torusAddEquiv_apply, torusAddEquiv_apply, hab])
      exact this ▸ hb
theorem apexEquiv_coe (G : s.WeightedGeometry B) (y : ↥(s.params.allLayerPoints s.Ω)) :
    ((apexEquiv G y : ↥B.allSites) : D.Space) = s.toTorus D.side (y : s.data.Point) := by
  rw [← torusAddEquiv_apply]
  rfl
theorem siteRel_iff (G : s.WeightedGeometry B) (x : s.data.BareSite) (x' : D.BareSite) :
    s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side) x x' ↔ bareSiteEquiv G x = x' := by
  show s.toTorus D.side (x : s.data.Point) = (x' : D.Space) ↔ _
  rw [← bareSiteEquiv_coe G, Subtype.val_inj]
theorem coarseRel_iff (G : s.WeightedGeometry B) (y : ↥(s.params.allLayerPoints s.Ω))
    (y' : ↥B.allSites) :
    s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side) y y' ↔ apexEquiv G y = y' := by
  show s.toTorus D.side (y : s.data.Point) = (y' : D.Space) ↔ _
  rw [← apexEquiv_coe G, Subtype.val_inj]
def apexOf (y : ↥(s.params.allLayerPoints s.Ω)) : s.data.Apex s.Ω :=
  ⟨s.params.levelSite s.Ω y, (s.params.exists_levelSite s.Ω y).choose_spec.1,
    (s.params.exists_levelSite s.Ω y).choose_spec.2.1⟩
theorem apexOf_point (y : ↥(s.params.allLayerPoints s.Ω)) : (apexOf y).point = y :=
  (s.params.exists_levelSite s.Ω y).choose_spec.2.2
theorem one_lt_blockFactor : (1 : ℝ) < s.data.L := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.one_lt_blockFactor <;> assumption
theorem mem_fineBlock_iff (T : s.data.Apex s.Ω) (x : s.data.BareSite) :
    (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) T.site ↔
      (x : s.data.Point) ∈ T.block :=
  ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
theorem mem_zeroFormsOn {Ω₀ : Set s.data.Point} (g : s.data.SiteFn)
    (hg : ∀ x, x ∉ sitesOfRegion s.data.cutoff Ω₀ → g x = 0) : g ∈ zeroFormsOn s.data.cutoff Ω₀ :=
  ⟨g, funext fun x => by
    by_cases hx : x ∈ sitesOfRegion s.data.cutoff Ω₀
    · exact Set.indicator_of_mem hx _
    · exact (Set.indicator_of_notMem hx _).trans (hg x hx).symm⟩
theorem scale_zero_eq (hw : s.IsWeightedTorus D B) :
    D.scale 0 = finestMeshInLevelUnits s.data.L s.data.t := by
  show (D.L : ℝ) ^ 0 * D.bareSpacing = _
  rw [pow_zero, one_mul, hw.bareSpacing_eq]
  rfl
theorem extendByZero_of_mem {X Y : Type} {E : Submodule ℝ (X → ℝ)} {T : ↥E → Y → ℝ} {f : X → ℝ}
    (h : f ∈ E) : _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero E T f = T ⟨f, h⟩ := dif_pos h
end SeparatedClasses.WeightedScalarDataProof
end YangMills.Construction
