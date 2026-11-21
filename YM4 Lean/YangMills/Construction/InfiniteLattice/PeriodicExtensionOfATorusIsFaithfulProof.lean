import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriodsProof
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLatticeProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithful
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicLift
variable {a : ℝ}
theorem faceEnergy_mem_Icc (W : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (p : ElementaryPlaquette a) :
    faceEnergy W p ∈ Icc (0 : ℝ) 2 := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicLift.faceEnergy_mem_zero_two <;> assumption
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun W : GaugeField a => faceEnergy W p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
theorem eval_linkMap_of_invariant {W : GaugeField a} {γ : LatticePoint a}
    (h : (shift γ).pullbackField W = W) (b : Link a) :
    W ((shift γ).linkMap b) = W b :=
  congrFun (congrArg Subtype.val h) b
def translatePlaquette (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem plaquetteMap_shift_eq_translate (ha : 0 < a) (p : ElementaryPlaquette a)
    (γ : LatticePoint a) :
    (shift γ).plaquetteMap p = translatePlaquette p γ := by apply _root_.YangMills.Construction.UnitSpacing.plaquetteMap_shift <;> assumption
theorem faceHolonomy_translatePlaquette {W : GaugeField a} {γ : LatticePoint a}
    (h : (shift γ).pullbackField W = W) (p : ElementaryPlaquette a) :
    faceHolonomy W (translatePlaquette p γ) = faceHolonomy W p := by
  have hb : ∀ (x : LatticePoint a) (μ : Fin 4),
      W (Link.forwardFrom (x + γ) μ) = W (Link.forwardFrom x μ) := by
    intro x μ
    have he : Link.forwardFrom (x + γ) μ = (shift γ).linkMap (Link.forwardFrom x μ) :=
      Link.ext rfl (by
        change x + γ + axisStep a μ = x + axisStep a μ + γ
        abel)
    rw [he, eval_linkMap_of_invariant h]
  have h₁ : p.corner + γ + axisStep a p.lowAxis = p.corner + axisStep a p.lowAxis + γ := by abel
  have h₂ : p.corner + γ + axisStep a p.highAxis = p.corner + axisStep a p.highAxis + γ := by abel
  simp only [faceHolonomy, translatePlaquette]
  rw [h₁, h₂, hb, hb, hb, hb]
variable (Γ : PeriodSublattice a)
theorem liftValue_of_positive (U : Γ.QuotientField) (b : PositiveLink a) :
    Γ.liftValue U b.1 = U (Γ.linkClass b) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.lift_apply_positive <;> assumption
theorem linkMap_shift_positive (b : PositiveLink a) (γ : LatticePoint a) :
    (shift γ).linkMap b.1 = (b.translate γ).1 := rfl
theorem lift_invariant (U : Γ.QuotientField) {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    (shift γ).pullbackField (Γ.lift U) = Γ.lift U := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicLift.lift_shift_invariant <;> assumption
theorem continuous_lift : Continuous Γ.lift := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts.continuous_lift <;> assumption
theorem lift_injective : Function.Injective Γ.lift := by
  intro U V h
  funext c
  obtain ⟨_, b, rfl⟩ := c
  have hb := congrFun (congrArg Subtype.val h) b.1
  change Γ.liftValue U b.1 = Γ.liftValue V b.1 at hb
  rw [liftValue_of_positive, liftValue_of_positive] at hb
  exact hb
theorem mem_range_lift_of_invariant {W : GaugeField a} (hW : W ∈ Γ.invariantFields) :
    W ∈ range Γ.lift := by
  refine ⟨fun c => W (Γ.linkRep c).1, ?_⟩
  have hpos : ∀ b : PositiveLink a,
      Γ.liftValue (fun c => W (Γ.linkRep c).1) b.1 = W b.1 := by
    intro b
    rw [liftValue_of_positive]
    obtain ⟨γ, hγ, he⟩ : Γ.linkRep (Γ.linkClass b) ∈ Γ.linkOrbit b :=
      (Γ.quotientLink_nonempty (Γ.linkClass b)).some_mem
    rw [he, ← linkMap_shift_positive]
    exact eval_linkMap_of_invariant (hW γ hγ) b.1
  refine Subtype.ext (funext fun b => ?_)
  change Γ.liftValue (fun c => W (Γ.linkRep c).1) b = W b
  by_cases h : b.IsPositivelyOriented
  · exact hpos ⟨b, h⟩
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not h
    have hb : b = b.opposite.opposite := rfl
    rw [hb, Γ.liftValue_opposite, hpos ⟨b.opposite, hr⟩]
    exact (W.2 b.opposite).symm
theorem faceEnergy_lift_of_mem_orbit (ha : 0 < a) (U : Γ.QuotientField)
    (r q : ElementaryPlaquette a) (hq : q ∈ Γ.plaquetteOrbit r) :
    faceEnergy (Γ.lift U) q = faceEnergy (Γ.lift U) r := by
  obtain ⟨γ, hγ, rfl⟩ := hq
  rw [plaquetteMap_shift_eq_translate ha]
  unfold faceEnergy
  rw [faceHolonomy_translatePlaquette (lift_invariant Γ U hγ)]
theorem faceEnergy_lift_eq_quotient (ha : 0 < a) (U : Γ.QuotientField)
    (p : Γ.QuotientPlaquette) (q : ElementaryPlaquette a)
    (hq : q ∈ (p : Set (ElementaryPlaquette a))) :
    faceEnergy (Γ.lift U) q = Γ.quotientFaceEnergy U p := by
  obtain ⟨_, r, rfl⟩ := p
  have hs := (Γ.quotientPlaquette_nonempty ⟨Γ.plaquetteOrbit r, r, rfl⟩).some_mem
  unfold PeriodSublattice.quotientFaceEnergy
  rw [faceEnergy_lift_of_mem_orbit Γ ha U r q hq, faceEnergy_lift_of_mem_orbit Γ ha U r _ hs]
end PeriodicLift
theorem periodicLift_isFaithful : PeriodicLiftIsFaithful := by
  intro a ha Γ
  have : T2Space (GaugeField a) :=
    inferInstanceAs (T2Space {U : Link a → Matrices.ComplexMatrix2.specialUnitary //
      ∀ b, U b.opposite = (U b)⁻¹})
  refine
    { isEmbedding_lift := ((PeriodicLift.continuous_lift Γ).isClosedEmbedding
        (PeriodicLift.lift_injective Γ)).isEmbedding
      range_lift := ?_
      continuous_periodize := fun F hF =>
        hF.2.2.comp (PeriodicLift.continuous_lift Γ)
      periodize_actOn_shift := ?_
      faceEnergy_lift := PeriodicLift.faceEnergy_lift_eq_quotient Γ ha
      continuous_quotientFaceEnergy := fun p =>
        (PeriodicLift.continuous_faceEnergy _).comp (PeriodicLift.continuous_lift Γ)
      quotientFaceEnergy_mem_Icc := fun U p => PeriodicLift.faceEnergy_mem_Icc _ _ }
  · refine Subset.antisymm ?_ fun W hW => PeriodicLift.mem_range_lift_of_invariant Γ hW
    rintro _ ⟨U, rfl⟩ γ hγ
    exact PeriodicLift.lift_invariant Γ U hγ
  · intro F _ γ hγ
    funext U
    change F ((shift γ).pullbackField (Γ.lift U)) = F (Γ.lift U)
    rw [PeriodicLift.lift_invariant Γ U hγ]
end YangMills.Construction.InfiniteLattice
