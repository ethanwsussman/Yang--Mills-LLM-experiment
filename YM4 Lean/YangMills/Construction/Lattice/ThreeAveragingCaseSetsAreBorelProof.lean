import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.ThreeAveragingCaseSetsAreBorel
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CaseSetsMeasurable
variable {L m : ℕ} {j j' : ℤ}
private theorem continuousOn_contourCrossingDefect (c : Bond L m j) (x : Site L m j')
    (σ : AxisOrdering c.source x) (σ' : AxisOrdering c.target (shiftAcross c x)) :
    ContinuousOn (fun U : Bond L m j' → Matrices.ComplexMatrix2 => contourCrossingDefect U c x σ σ')
      (compactGaugeFields L m j') := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuousOn_contourCrossingDefect <;> assumption
private theorem isOpen_of_isOpen_levelTopology {K k : ℕ} {A : Set (gaugeFieldsAtLevel L m K k)}
    (h : IsOpen[gaugeFieldsAtLevelTopology L m K k] A) : IsOpen A := by
  obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1
    (show IsOpen[TopologicalSpace.induced gaugeFieldAtLevelValues inferInstance] A from h)
  refine ht.preimage (continuous_pi fun b => ?_)
  exact Continuous.subtype_mk ((continuous_apply b.1).comp continuous_subtype_val) _
private theorem isOpen_noCrossingDefectIsNegOne {K k : ℕ} [Finite (Site L m (levelDepth K k))]
    (c : BondAtLevel L m K (k + 1)) :
    IsOpen {U : gaugeFieldsAtLevel L m K k | NoCrossingDefectIsNegOne U.1 c} := by
  have hfin : (sitesInBlock (levelDepth K k) c.source).Finite := Set.toFinite _
  have e : {U : gaugeFieldsAtLevel L m K k | NoCrossingDefectIsNegOne U.1 c} =
      ⋂ x ∈ sitesInBlock (levelDepth K k) c.source, ⋂ σ, ⋂ σ',
        {U : gaugeFieldsAtLevel L m K k | contourCrossingDefect U.1 c x σ σ' ≠ -1} := by
    ext U
    simp [NoCrossingDefectIsNegOne]
  rw [e]
  refine hfin.isOpen_biInter fun x _ => isOpen_iInter_of_finite fun σ =>
    isOpen_iInter_of_finite fun σ' => ?_
  have hcont : Continuous fun U : gaugeFieldsAtLevel L m K k => contourCrossingDefect U.1 c x σ σ' :=
    (continuousOn_contourCrossingDefect c x σ σ').comp_continuous continuous_subtype_val
      fun U => U.2
  exact isOpen_compl_singleton.preimage hcont
theorem caseSetsMeasurable_of_everySmallRadiusSuffices
    (hR : Averaging.SmallRadius.EverySmallRadiusSuffices) : CaseSetsMeasurableStatement := by
  intro s k hk c hc κ
  have hLpos : 0 < s.L := by have := s.isAdmissible.2; omega
  have : Finite (Site s.L s.m (levelDepth s.K k)) :=
    SeparatedSequences.BaseParameters.site_finite hLpos _ _
  have hω : Averaging.smoothingRadius s.L ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L) :=
    Averaging.isSmoothingRadius_smoothingRadius s.isAdmissible.1 s.isAdmissible.2
  have hC := hR s _ hω k hk c
  have hL1 : (1 : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast hLpos
  have hω1 : Averaging.smoothingRadius s.L ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨hω.1, hω.2.trans ?_⟩
    unfold averagingRadiusCap
    rw [div_le_one (by positivity)]
    nlinarith
  let S : Set (gaugeFieldsAtLevel s.L s.m s.K k) := Subtype.val ⁻¹'
    (smallPlaquetteFields (Averaging.smoothingRadius s.L) c :
      Set (BondAtLevel s.L s.m s.K k → Matrices.ComplexMatrix2))
  let N : Set (gaugeFieldsAtLevel s.L s.m s.K k) := {U | NoCrossingDefectIsNegOne U.1 c}
  have hS : IsOpen S := isOpen_of_isOpen_levelTopology (hC.isOpen_smallPlaquetteFields _ hω1)
  have hN : IsOpen N := isOpen_noCrossingDefectIsNegOne c
  have hA : ∀ U : gaugeFieldsAtLevel s.L s.m s.K k,
      IsRegularAveragingCase (Averaging.smoothingRadius s.L) U.1 c ↔ U ∈ S := fun U =>
    ⟨fun h => ⟨U.2, h.1⟩, fun h => ⟨h.2,
      fun x hx => (hC.contourMean_spec U.1 h c.source (Or.inl rfl) x hx).1,
      fun x hx => (hC.contourMean_spec U.1 h c.target (Or.inr rfl) x hx).1,
      fun x hx => (hC.crossingDefect_near hc U.1 h x hx).2.trans (by norm_num)⟩⟩
  refine ⟨fun U hU => hU.1, ?_⟩
  let _ : MeasurableSpace (gaugeFieldsAtLevel s.L s.m s.K k) := borel _
  have _ : BorelSpace (gaugeFieldsAtLevel s.L s.m s.K k) := ⟨rfl⟩
  have hcase : ∀ U : gaugeFieldsAtLevel s.L s.m s.K k,
      blockAverageCase (Averaging.smoothingRadius s.L) U.1 c = κ ↔
        match κ with
        | .logarithmOfMeans => U ∈ S
        | .intrinsicLogarithmOfDefects => U ∉ S ∧ U ∈ N
        | .alongBond => U ∉ S ∧ U ∉ N := by
    intro U
    have hU := hA U
    unfold blockAverageCase
    by_cases h₁ : U ∈ S <;> by_cases h₂ : U ∈ N <;> cases κ <;>
      simp [hU, h₁, show NoCrossingDefectIsNegOne U.1 c ↔ U ∈ N from Iff.rfl, h₂]
  have hpre : ((↑) ⁻¹' caseSet (Averaging.smoothingRadius s.L) k c κ :
      Set (gaugeFieldsAtLevel s.L s.m s.K k)) =
      {U | blockAverageCase (Averaging.smoothingRadius s.L) U.1 c = κ} := by
    ext U
    exact ⟨And.right, fun h => ⟨U.2, h⟩⟩
  rw [hpre]
  cases κ with
  | logarithmOfMeans =>
    have e : {U : gaugeFieldsAtLevel s.L s.m s.K k |
        blockAverageCase (Averaging.smoothingRadius s.L) U.1 c = .logarithmOfMeans} = S := by
      ext U
      exact hcase U
    rw [e]
    exact hS.measurableSet
  | intrinsicLogarithmOfDefects =>
    have e : {U : gaugeFieldsAtLevel s.L s.m s.K k |
        blockAverageCase (Averaging.smoothingRadius s.L) U.1 c = .intrinsicLogarithmOfDefects} =
          Sᶜ ∩ N := by
      ext U
      exact hcase U
    rw [e]
    exact hS.measurableSet.compl.inter hN.measurableSet
  | alongBond =>
    have e : {U : gaugeFieldsAtLevel s.L s.m s.K k |
        blockAverageCase (Averaging.smoothingRadius s.L) U.1 c = .alongBond} = Sᶜ ∩ Nᶜ := by
      ext U
      exact hcase U
    rw [e]
    exact hS.measurableSet.compl.inter hN.measurableSet.compl
end YangMills.Construction.PeriodicLattice.CaseSetsMeasurable
end
