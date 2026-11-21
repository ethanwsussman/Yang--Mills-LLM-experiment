import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtensionProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicLift
variable {a : ℝ}
theorem positiveLink_translate_translate (b : PositiveLink a) (γ δ : LatticePoint a) :
    (b.translate γ).translate δ = b.translate (γ + δ) :=
  Subtype.ext (Link.ext (add_assoc _ _ _) (add_assoc _ _ _))
theorem linkOrbit_translate (Γ : PeriodSublattice a) (b : PositiveLink a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) : Γ.linkOrbit (b.translate γ) = Γ.linkOrbit b := by
  ext c
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, positiveLink_translate_translate b γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ - γ, sub_mem hδ hγ, ?_⟩
    rw [positiveLink_translate_translate, add_sub_cancel]
theorem liftValue_linkMap_of_isPositivelyOriented (Γ : PeriodSublattice a) (U : Γ.QuotientField)
    {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) {b : Link a} (h : b.IsPositivelyOriented) :
    Γ.liftValue U ((shift γ).linkMap b) = Γ.liftValue U b := by
  have e : (shift γ).linkMap b = (PositiveLink.translate ⟨b, h⟩ γ).1 := Link.ext rfl rfl
  rw [e]
  unfold PeriodSublattice.liftValue
  rw [dif_pos (PositiveLink.translate ⟨b, h⟩ γ).2, dif_pos h]
  exact congrArg U (Subtype.ext (linkOrbit_translate Γ ⟨b, h⟩ hγ))
theorem lift_shift_invariant (Γ : PeriodSublattice a) (U : Γ.QuotientField)
    {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    (shift γ).pullbackField (Γ.lift U) = Γ.lift U := by
  refine Subtype.ext (funext fun b => ?_)
  change Γ.liftValue U ((shift γ).linkMap b) = Γ.liftValue U b
  by_cases h : b.IsPositivelyOriented
  · exact liftValue_linkMap_of_isPositivelyOriented Γ U hγ h
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not h
    have e : (shift γ).linkMap b = ((shift γ).linkMap b.opposite).opposite :=
      Link.ext rfl rfl
    have e' : Γ.liftValue U b = (Γ.liftValue U b.opposite)⁻¹ := by
      rw [Γ.liftValue_opposite, inv_inv]
    rw [e, Γ.liftValue_opposite, liftValue_linkMap_of_isPositivelyOriented Γ U hγ hr, e']
theorem continuous_quotientLift (Γ : PeriodSublattice a) : Continuous Γ.lift := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts.continuous_lift <;> assumption
theorem continuous_faceEnergy_field (q : ElementaryPlaquette a) :
    Continuous fun V : GaugeField a => faceEnergy V q := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
theorem faceEnergy_mem_zero_two (V : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (q : ElementaryPlaquette a) :
    faceEnergy V q ∈ Icc (0 : ℝ) 2 := by
  have hu : (faceHolonomy V q : Matrices.ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup (faceHolonomy V q).2
  have h0 := Complex.abs_re_le_norm ((faceHolonomy V q : Matrices.ComplexMatrix2) 0 0)
  have h1 := Complex.abs_re_le_norm ((faceHolonomy V q : Matrices.ComplexMatrix2) 1 1)
  have b0 := entry_norm_bound_of_unitary hu 0 0
  have b1 := entry_norm_bound_of_unitary hu 1 1
  have hre : (Matrices.ComplexMatrix2.fullTrace (faceHolonomy V q : Matrices.ComplexMatrix2)).re =
      ((faceHolonomy V q : Matrices.ComplexMatrix2) 0 0).re +
        ((faceHolonomy V q : Matrices.ComplexMatrix2) 1 1).re := by
    simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  have c0 := abs_le.1 (h0.trans b0)
  have c1 := abs_le.1 (h1.trans b1)
  unfold faceEnergy
  rw [hre]
  constructor <;> linarith [c0.1, c0.2, c1.1, c1.2]
theorem plaquetteMap_shift (ha : 0 < a) (γ : LatticePoint a) (p : ElementaryPlaquette a) :
    (shift γ).plaquetteMap p =
      ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩ := by
  have hc : (⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩ :
      ElementaryPlaquette a).cornerSet = (shift γ).pointMap '' p.cornerSet := by
    have hm : ∀ x : LatticePoint a, (shift γ).pointMap x = x + γ := fun _ => rfl
    simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, hm]
    have e₁ : p.corner + γ + axisStep a p.lowAxis = p.corner + axisStep a p.lowAxis + γ := by abel
    have e₂ : p.corner + axisStep a p.lowAxis + γ + axisStep a p.highAxis =
        p.corner + axisStep a p.lowAxis + axisStep a p.highAxis + γ := by abel
    have e₃ : p.corner + γ + axisStep a p.highAxis = p.corner + axisStep a p.highAxis + γ := by abel
    rw [e₁, e₂, e₃]
  have hex : ∃ p' : ElementaryPlaquette a, p'.cornerSet = (shift γ).pointMap '' p.cornerSet :=
    ⟨_, hc⟩
  unfold LatticeSymmetry.plaquetteMap
  rw [dif_pos hex]
  exact ElementaryPlaquette.cornerSet_injective ha (hex.choose_spec.trans hc.symm)
theorem faceEnergy_plaquetteMap_shift (ha : 0 < a) (γ : LatticePoint a) (V : GaugeField a)
    (p : ElementaryPlaquette a) :
    faceEnergy V ((shift γ).plaquetteMap p) =
      faceEnergy ((shift γ).pullbackField V) p := by
  rw [plaquetteMap_shift ha]
  have e₁ : (shift γ).linkMap (Link.forwardFrom p.corner p.lowAxis) =
      Link.forwardFrom (p.corner + γ) p.lowAxis :=
    Link.ext rfl (by
      change p.corner + axisStep a p.lowAxis + γ = p.corner + γ + axisStep a p.lowAxis; abel)
  have e₂ : (shift γ).linkMap (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis) =
      Link.forwardFrom (p.corner + γ + axisStep a p.lowAxis) p.highAxis :=
    Link.ext (by
      change p.corner + axisStep a p.lowAxis + γ = p.corner + γ + axisStep a p.lowAxis; abel)
      (by
        change p.corner + axisStep a p.lowAxis + axisStep a p.highAxis + γ =
          p.corner + γ + axisStep a p.lowAxis + axisStep a p.highAxis
        abel)
  have e₃ : (shift γ).linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis) =
      Link.forwardFrom (p.corner + γ + axisStep a p.highAxis) p.lowAxis :=
    Link.ext (by
      change p.corner + axisStep a p.highAxis + γ = p.corner + γ + axisStep a p.highAxis; abel)
      (by
        change p.corner + axisStep a p.highAxis + axisStep a p.lowAxis + γ =
          p.corner + γ + axisStep a p.highAxis + axisStep a p.lowAxis
        abel)
  have e₄ : (shift γ).linkMap (Link.forwardFrom p.corner p.highAxis) =
      Link.forwardFrom (p.corner + γ) p.highAxis :=
    Link.ext rfl (by
      change p.corner + axisStep a p.highAxis + γ = p.corner + γ + axisStep a p.highAxis; abel)
  unfold faceEnergy faceHolonomy
  change _ = 1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
      ((V ((shift γ).linkMap (Link.forwardFrom p.corner p.lowAxis)) *
      V ((shift γ).linkMap (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)) *
      (V ((shift γ).linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)))⁻¹ *
      (V ((shift γ).linkMap (Link.forwardFrom p.corner p.highAxis)))⁻¹ :
        Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re
  rw [e₁, e₂, e₃, e₄]
end PeriodicLift
open PeriodicLift in
theorem periodicLiftAndQuotientEnergies : PeriodicLiftAndQuotientEnergiesStatement := by
  intro a ha Γ
  have hq : ∀ (U : Γ.QuotientField) (r : ElementaryPlaquette a), ∀ γ ∈ Γ.periods,
      faceEnergy (Γ.lift U) ((shift γ).plaquetteMap r) =
        faceEnergy (Γ.lift U) r := fun U r γ hγ => by
    rw [faceEnergy_plaquetteMap_shift ha, lift_shift_invariant Γ U hγ]
  refine ⟨⟨fun U γ hγ => lift_shift_invariant Γ U hγ, continuous_quotientLift Γ, ?_,
    fun p => ⟨?_, fun U => faceEnergy_mem_zero_two _ _⟩⟩, ?_⟩
  · rintro U ⟨_, r, rfl⟩ q ⟨γ, hγ, rfl⟩ q' ⟨γ', hγ', rfl⟩
    rw [hq U r γ hγ, hq U r γ' hγ']
  · exact (continuous_faceEnergy_field _).comp (continuous_quotientLift Γ)
  · intro F _ v γ hγ
    funext U
    refine congrArg F (Subtype.ext (funext fun b => ?_))
    have e : (shift (v + γ)).linkMap b =
        (shift γ).linkMap ((shift v).linkMap b) :=
      Link.ext (add_assoc _ _ _).symm (add_assoc _ _ _).symm
    change Γ.lift U ((shift (v + γ)).linkMap b) =
      Γ.lift U ((shift v).linkMap b)
    rw [e]
    exact congrArg (fun W : GaugeField a => W ((shift v).linkMap b))
      (lift_shift_invariant Γ U hγ)
end YangMills.Construction.InfiniteLattice
