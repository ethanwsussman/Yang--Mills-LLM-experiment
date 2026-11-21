import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace Link GaugeField LinkVariables)
namespace MeasurableObservables
variable {a : ℝ}
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem borel_linkVariables (ι : Type) [Countable ι] :
    borel (LinkVariables ι) = MeasurableSpace.pi := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact (Pi.borelSpace (ι := ι) (X := fun _ => Matrices.ComplexMatrix2.specialUnitary)).measurable_eq.symm
theorem eq_of_eqOn_links {L : Set (Link a)} {A : GaugeField a → ℂ}
    (hA : Measurable[InfiniteLattice.linkSigma L] A) {U V : GaugeField a}
    (hUV : ∀ l ∈ L, U l = V l) : A U = A V := by
  let m' : MeasurableSpace (GaugeField a) :=
    { MeasurableSet' := fun E => U ∈ E ↔ V ∈ E
      measurableSet_empty := by simp
      measurableSet_compl := fun E hE => by simpa using not_congr hE
      measurableSet_iUnion := fun f hf => by
        simp only [mem_iUnion]
        exact exists_congr hf }
  have hle : InfiniteLattice.linkSigma L ≤ m' := by
    refine iSup₂_le fun l hl => ?_
    rintro E ⟨E', -, rfl⟩
    change U ∈ _ ↔ V ∈ _
    simp [hUV l hl]
  have hE : MeasurableSet[InfiniteLattice.linkSigma L] (A ⁻¹' {A U}) :=
    hA (measurableSet_singleton _)
  have hU : U ∈ A ⁻¹' {A U} ↔ V ∈ A ⁻¹' {A U} := hle _ hE
  exact (hU.mp rfl).symm
theorem eq_on_linksWithin {S : Set AmbientSpace} {U V : GaugeField a}
    (hUV : ∀ l ∈ InfiniteLattice.positiveLinksWithin a S, U l = V l) :
    ∀ l ∈ (InfiniteLattice.linksWithin S : Set (Link a)), U l = V l := by
  intro l hl
  rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem l with h₁ | h₁
  · exact hUV l ⟨h₁, hl⟩
  · have hr := hUV l.opposite ⟨h₁, hl.2, hl.1⟩
    have hU := U.2 l.opposite
    have hV := V.2 l.opposite
    rw [InfiniteLattice.Link.opposite_opposite] at hU hV
    rw [hU, hV, hr]
theorem measurable_link_eval_of_mem {L : Set (Link a)} {l : Link a} (hl : l ∈ L) :
    Measurable[InfiniteLattice.linkSigma L] (fun U : GaugeField a => U l) := by
  have hle : MeasurableSpace.comap (fun U : GaugeField a => U l) inferInstance ≤
      InfiniteLattice.linkSigma L :=
    le_iSup₂_of_le l hl le_rfl
  exact (comap_measurable _).mono hle le_rfl
theorem continuous_link_eval (l : Link a) : Continuous (fun U : GaugeField a => U l) := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem measurable_link_eval (l : Link a) : Measurable (fun U : GaugeField a => U l) := by
  exact (continuous_link_eval l).measurable
theorem measurable_pi_of_coords {Ω ι : Type} {m : MeasurableSpace Ω}
    {p : Ω → ι → Matrices.ComplexMatrix2.specialUnitary}
    (hp : ∀ i, Measurable[m] fun ω => p ω i) : Measurable[m] p :=
  measurable_pi_lambda p hp
theorem continuous_gluedField_trivial (ha : 0 < a) {P : Set (Link a)}
    (hP : P ⊆ InfiniteLattice.positiveLinkSet a) :
    Continuous fun V : LinkVariables P =>
      InfiniteLattice.gluedField ha hP V (InfiniteLattice.trivialField a) := by
  classical
  refine Continuous.subtype_mk (f := fun V l => (InfiniteLattice.gluedField ha hP V
    (InfiniteLattice.trivialField a)) l) (continuous_pi fun l => ?_) _
  by_cases hl : l ∈ P
  · have e : (fun V : LinkVariables P => (InfiniteLattice.gluedField ha hP V
        (InfiniteLattice.trivialField a)) l) = fun V => V ⟨l, hl⟩ :=
      funext fun V => InfiniteLattice.gluedField_apply_of_mem ha hP V _ ⟨l, hl⟩
    rw [e]
    exact continuous_apply _
  · by_cases hl' : l.opposite ∈ P
    · have e : (fun V : LinkVariables P => (InfiniteLattice.gluedField ha hP V
          (InfiniteLattice.trivialField a)) l) = fun V => (V ⟨l.opposite, hl'⟩)⁻¹ := by
        funext V
        change (if h : l ∈ P then V ⟨l, h⟩ else
          if h' : l.opposite ∈ P then (V ⟨l.opposite, h'⟩)⁻¹ else _) = _
        rw [dif_neg hl, dif_pos hl']
      rw [e]
      exact (continuous_apply _).inv
    · have e : (fun V : LinkVariables P => (InfiniteLattice.gluedField ha hP V
          (InfiniteLattice.trivialField a)) l) =
          fun _ => (InfiniteLattice.trivialField a) l := by
        funext V
        change (if h : l ∈ P then V ⟨l, h⟩ else
          if h' : l.opposite ∈ P then (V ⟨l.opposite, h'⟩)⁻¹ else _) = _
        rw [dif_neg hl, dif_neg hl']
      rw [e]
      exact continuous_const
theorem isRegionMeasurable_iff (ha : 0 < a) (S : Set AmbientSpace) {A : GaugeField a → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) :
    InfiniteLattice.IsRegionMeasurable S A ↔
      ∃ f : LinkVariables (InfiniteLattice.positiveLinksWithin a S) → ℂ,
        Measurable[borel (LinkVariables (InfiniteLattice.positiveLinksWithin a S))] f ∧
          (∃ C : ℝ, ∀ V, ‖f V‖ ≤ C) ∧
          ∀ U : GaugeField a,
            A U = f (InfiniteLattice.restrictField U
              (InfiniteLattice.positiveLinksWithin a S)) := by
  have := countable_link a
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hP : InfiniteLattice.positiveLinksWithin a S ⊆
      InfiniteLattice.positiveLinkSet a := inter_subset_left
  constructor
  · intro hS
    refine ⟨fun V => A (InfiniteLattice.gluedField ha hP V
      (InfiniteLattice.trivialField a)), ?_, ?_, fun U => ?_⟩
    · rw [borel_linkVariables]
      exact hA.1.comp (continuous_gluedField_trivial ha hP).measurable
    · obtain ⟨C, hC⟩ := hA.2
      exact ⟨C, fun V => hC _⟩
    · exact eq_of_eqOn_links hS (eq_on_linksWithin fun l hl =>
        (InfiniteLattice.gluedField_apply_of_mem ha hP (InfiniteLattice.restrictField U _)
          (InfiniteLattice.trivialField a) ⟨l, hl⟩).symm)
  · rintro ⟨f, hf, -, hrep⟩
    rw [borel_linkVariables] at hf
    have hp : Measurable[InfiniteLattice.regionSigma S] fun U : GaugeField a =>
        InfiniteLattice.restrictField U (InfiniteLattice.positiveLinksWithin a S) :=
      measurable_pi_of_coords fun l => measurable_link_eval_of_mem l.2.2
    have e : A = f ∘ fun U : GaugeField a =>
        InfiniteLattice.restrictField U (InfiniteLattice.positiveLinksWithin a S) :=
      funext hrep
    rw [InfiniteLattice.IsRegionMeasurable, e]
    exact hf.comp hp
theorem cellObservables_eq (D : ChessboardSetup) (S : Set AmbientSpace) :
    ReflectionGrid.cellObservables (D := D) S =
      {A | InfiniteLattice.IsBoundedObservable A ∧
        InfiniteLattice.IsRegionMeasurable (interior S) A} := by
  have := countable_link D.mesh
  ext F
  constructor
  · rintro ⟨f, hf, ⟨C, hC⟩, rfl⟩
    have hs : Measurable[InfiniteLattice.regionSigma (interior S)]
        (ReflectionGrid.restrictField (D := D) S) :=
      measurable_pi_of_coords fun l => measurable_link_eval_of_mem l.2
    have hb : Measurable (ReflectionGrid.restrictField (D := D) S) :=
      measurable_pi_of_coords fun l => measurable_link_eval l.1
    exact ⟨⟨hf.comp hb, C, fun U => hC _⟩, hf.comp hs⟩
  · rintro ⟨hobs, hmeas⟩
    obtain ⟨g, hg, ⟨C, hC⟩, hrep⟩ :=
      (isRegionMeasurable_iff D.mesh_pos (interior S) hobs).mp hmeas
    rw [borel_linkVariables] at hg
    have hq : Measurable fun (V : ReflectionGrid.interiorLinks (D := D) S →
        Conventions.StandingParameters.gaugeGroup)
        (l : InfiniteLattice.positiveLinksWithin D.mesh (interior S)) => V ⟨l.1, l.2.2⟩ :=
      measurable_pi_of_coords fun l => measurable_pi_apply _
    exact ⟨_, hg.comp hq, ⟨C, fun V => hC _⟩, funext hrep⟩
theorem regionSigma_mono {S S' : Set AmbientSpace} (hSS' : S ⊆ S') :
    (InfiniteLattice.regionSigma S : MeasurableSpace (GaugeField a)) ≤
      InfiniteLattice.regionSigma S' := by apply _root_.YangMills.Construction.InfiniteLattice.regionSigma_mono <;> assumption
end MeasurableObservables
open MeasurableObservables in
theorem MeasurableObservablesAndLifts.statement_holds :
    MeasurableObservablesAndLifts.Statement := by
  intro D
  refine ⟨fun S A _ hS U V hUV => eq_of_eqOn_links hS (eq_on_linksWithin hUV),
    fun S A hA => isRegionMeasurable_iff D.mesh_pos S hA,
    fun g _ C _ => cellObservables_eq D C, ?_, ?_⟩
  · intro g g' _ _ C _ C' _ hCC' F hF
    rw [cellObservables_eq] at hF ⊢
    exact ⟨hF.1, hF.2.mono (regionSigma_mono hCC') le_rfl⟩
  · intro A A' hA hA'
    refine ⟨⟨?_, ?_⟩, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · have hc : Continuous (InfiniteLattice.liftCompactField :
          PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ) → _) :=
        InfiniteLattice.continuous_liftCompactField
      exact hA.1.comp hc.measurable
    · obtain ⟨C, hC⟩ := hA.2
      exact ⟨C, fun W => hC _⟩
    · exact (InfiniteLattice.integral_liftedWilsonMeasure D.L D.m D.K D.β hA).symm
end ChessboardTori
end YangMills.Construction
end
