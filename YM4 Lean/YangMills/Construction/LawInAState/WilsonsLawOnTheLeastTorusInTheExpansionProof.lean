import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ConditionalMeansOnBoxes.CalculusOfLinks
import YangMills.Construction.ConditionalMeansOnBoxes.SiteEnergyBoxesAndConditionalMeans
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.LawInAState
open TorusFields WeightedResponses ConditionalMeansOnBoxes BoxResponses
open InfiniteLattice (AmbientSpace)
open BlockAverages (UnitQuaternion)
open Matrices (ComplexMatrix2)
variable {L K M : ℕ}
private theorem meshSize_pos (hL : 0 < L) : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
  zpow_pos (by exact_mod_cast hL) _
private theorem torusSide_zero : PeriodicLattice.torusSide L 0 = 2 := by simp [PeriodicLattice.torusSide]
private theorem torusSide_mul_meshSize (hL : 0 < L) (hM : M = 2 * L ^ K) :
    (M : ℝ) * PeriodicLattice.meshSize L (K : ℤ) = 2 := by
  subst hM
  simp only [PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  push_cast
  field_simp
private def coordSite (L K : ℕ) (n : Fin 4 → ℤ) : PeriodicLattice.Site L 0 (K : ℤ) :=
  ⟨fun μ => (((n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L 0)),
    ⟨n, fun _ => rfl⟩⟩
private theorem coordSite_add (n n' : Fin 4 → ℤ) : coordSite L K (n + n') = coordSite L K n + coordSite L K n' :=
  Subtype.ext (funext fun μ => by simp [coordSite, add_mul])
private theorem coordSite_surjective (x : PeriodicLattice.Site L 0 (K : ℤ)) : ∃ n, coordSite L K n = x := by
  obtain ⟨x, n, hn⟩ := x
  exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
private theorem coordSite_eq_iff (hL : 0 < L) (hM : M = 2 * L ^ K) (n n' : Fin 4 → ℤ) :
    coordSite L K n = coordSite L K n' ↔ ∀ μ, (M : ℤ) ∣ n μ - n' μ := by
  have ha := (meshSize_pos (K := K) hL).ne'
  have hMa := torusSide_mul_meshSize hL hM
  constructor
  · intro h μ
    have h1 := congrFun (congrArg Subtype.val h) μ
    have h2 : (((n μ - n' μ : ℤ) : ℝ) * PeriodicLattice.meshSize L (K : ℤ) : AddCircle (PeriodicLattice.torusSide L 0)) = 0 := by
      have : (((n μ - n' μ : ℤ) : ℝ) * PeriodicLattice.meshSize L (K : ℤ)) =
          (n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) - (n' μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) := by
        push_cast; ring
      rw [this, AddCircle.coe_sub, sub_eq_zero]
      exact h1
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff _).mp h2
    rw [torusSide_zero, ← hMa, zsmul_eq_mul, ← mul_assoc] at hz
    have h3 := mul_right_cancel₀ ha hz
    have h4 : z * (M : ℤ) = n μ - n' μ := by exact_mod_cast h3
    exact ⟨z, by rw [← h4]; ring⟩
  · intro h
    refine Subtype.ext (funext fun μ => ?_)
    obtain ⟨c, hc⟩ := h μ
    have hc' : (n μ : ℝ) = (n' μ : ℝ) + (M : ℝ) * (c : ℝ) := by
      have : n μ = n' μ + (M : ℤ) * c := by omega
      exact_mod_cast this
    have e : (n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) =
        (n' μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) + c • PeriodicLattice.torusSide L 0 := by
      rw [torusSide_zero, ← hMa, hc', zsmul_eq_mul]
      ring
    show (((n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L 0)) = _
    rw [e, AddCircle.coe_add, (AddCircle.coe_eq_zero_iff _).mpr ⟨c, rfl⟩, add_zero]
    rfl
private def coords (x : TorusSite M) : Fin 4 → ℤ := fun i => ((x i).val : ℤ)
private theorem siteOfInt_coords [NeZero M] (x : TorusSite M) : (siteOfInt (coords x) : TorusSite M) = x :=
  funext fun i => by simp [siteOfInt, coords]
abbrev _root_.YangMills.DeltaSharedProofs.p501176 := @siteOfInt_coords
private theorem siteOfInt_eq_iff (n n' : Fin 4 → ℤ) :
    (siteOfInt n : TorusSite M) = siteOfInt n' ↔ ∀ μ, (M : ℤ) ∣ n μ - n' μ := by
  constructor
  · intro h μ
    have h1 := congrFun h μ
    simp only [siteOfInt] at h1
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.symm
    exact this
  · intro h
    funext μ
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h μ)).symm
private def torusSiteOf (L K : ℕ) (x : TorusSite M) : PeriodicLattice.Site L 0 (K : ℤ) := coordSite L K (coords x)
private theorem torusSiteOf_siteOfInt [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (n : Fin 4 → ℤ) :
    torusSiteOf L K (siteOfInt n : TorusSite M) = coordSite L K n :=
  (coordSite_eq_iff hL hM _ _).mpr ((siteOfInt_eq_iff _ _).mp (siteOfInt_coords _))
private theorem torusSiteOf_injective [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) :
    Function.Injective (torusSiteOf L K : TorusSite M → _) := by
  intro x y h
  have h1 := (coordSite_eq_iff hL hM _ _).mp h
  have h2 := (siteOfInt_eq_iff (M := M) _ _).mpr h1
  rwa [siteOfInt_coords, siteOfInt_coords] at h2
private theorem torusSiteOf_surjective [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) :
    Function.Surjective (torusSiteOf L K : TorusSite M → _) := by
  intro y
  obtain ⟨n, rfl⟩ := coordSite_surjective y
  exact ⟨siteOfInt n, torusSiteOf_siteOfInt hL hM n⟩
private theorem periodicUnitStep_eq (μ : Fin 4) :
    PeriodicLattice.unitStep L 0 (K : ℤ) μ = coordSite L K (Pi.single μ 1) := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = μ
  · subst h
    simp [coordSite, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [coordSite, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem unitStep_eq_siteOfInt [NeZero M] (μ : Fin 4) : unitStep M μ = siteOfInt (Pi.single μ 1) := by apply _root_.YangMills.Construction.TorusLumps.unitStep_eq_siteOfInt <;> assumption
private theorem siteOfInt_add_eq (n n' : Fin 4 → ℤ) :
    (siteOfInt (n + n') : TorusSite M) = siteOfInt n + siteOfInt n' := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem torusSiteOf_add_unitStep [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (x : TorusSite M)
    (μ : Fin 4) :
    torusSiteOf L K (x + unitStep M μ) = torusSiteOf L K x + PeriodicLattice.unitStep L 0 (K : ℤ) μ := by
  rw [periodicUnitStep_eq, unitStep_eq_siteOfInt]
  conv_lhs => rw [← siteOfInt_coords x, ← siteOfInt_add_eq, torusSiteOf_siteOfInt hL hM, coordSite_add]
  rfl
private theorem projectPoint_latticePointOf (n : Fin 4 → ℤ) :
    InfiniteLattice.projectPoint L 0 (K : ℤ) (latticePointOf _ n) = coordSite L K n :=
  Subtype.ext (funext fun _ => rfl)
private theorem projectPoint_add (x y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
    InfiniteLattice.projectPoint L 0 (K : ℤ) (x + y) =
      InfiniteLattice.projectPoint L 0 (K : ℤ) x + InfiniteLattice.projectPoint L 0 (K : ℤ) y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [InfiniteLattice.projectPoint, TorusMetric.torusProj]
private abbrev PosBond (L K : ℕ) : Type := PeriodicLattice.PositivelyOrientedBond L 0 (K : ℤ)
private def forwardBond (y : PeriodicLattice.Site L 0 (K : ℤ)) (μ : Fin 4) : PosBond L K :=
  ⟨PeriodicLattice.Bond.forwardFrom y μ, μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem unitStep_add_unitStep_ne_zero (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) (μ ν : Fin 4) :
    PeriodicLattice.unitStep L 0 (K : ℤ) μ + PeriodicLattice.unitStep L 0 (K : ℤ) ν ≠ 0 := by
  intro h
  rw [periodicUnitStep_eq, periodicUnitStep_eq, ← coordSite_add] at h
  have h0 : (0 : PeriodicLattice.Site L 0 (K : ℤ)) = coordSite L K 0 :=
    Subtype.ext (funext fun _ => by simp [coordSite])
  rw [h0] at h
  have h1 := (coordSite_eq_iff hL hM _ _).mp h μ
  have h2 : (M : ℤ) ∣ 1 + (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ := by simpa using h1
  have h4 : 1 + (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ ≤ 2 ∧ 0 < 1 + (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) μ := by
    by_cases e : μ = ν
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have h5 := Int.le_of_dvd h4.2 h2
  omega
private theorem not_opposite_positive (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    {b : PeriodicLattice.Bond L 0 (K : ℤ)} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hν' : b.source - b.target = PeriodicLattice.unitStep L 0 (K : ℤ) ν := hν
  apply unitStep_add_unitStep_ne_zero hL hM h3 μ ν
  rw [← hμ, ← hν']
  abel
private theorem positive_or_opposite (b : PeriodicLattice.Bond L 0 (K : ℤ)) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · exact Or.inr ⟨μ, by
      show b.source - b.target = _
      rw [← neg_sub, h, neg_neg]⟩
private theorem forwardBond_surjective (p : PosBond L K) : ∃ y μ, forwardBond y μ = p := by
  obtain ⟨b, μ, hμ⟩ := p
  refine ⟨b.source, μ, Subtype.ext (PeriodicLattice.Bond.ext rfl ?_)⟩
  show b.source + PeriodicLattice.unitStep L 0 (K : ℤ) μ = b.target
  rw [← hμ]
  abel
private theorem forwardBond_injective (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    {y y' : PeriodicLattice.Site L 0 (K : ℤ)} {μ ν : Fin 4} (h : forwardBond y μ = forwardBond y' ν) :
    y = y' ∧ μ = ν := by
  have h1 : y = y' := congrArg (fun p : PosBond L K => p.1.source) h
  refine ⟨h1, ?_⟩
  subst h1
  have h2 : y + PeriodicLattice.unitStep L 0 (K : ℤ) μ = y + PeriodicLattice.unitStep L 0 (K : ℤ) ν :=
    congrArg (fun p : PosBond L K => p.1.target) h
  have h3' := add_left_cancel h2
  rw [periodicUnitStep_eq, periodicUnitStep_eq] at h3'
  by_contra hne
  have h4 := (coordSite_eq_iff hL hM _ _).mp h3' μ
  have h5 : (M : ℤ) ∣ 1 := by simpa [Pi.single_eq_of_ne hne] using h4
  have h6 := Int.le_of_dvd one_pos h5
  omega
open Classical in
private def fieldOfPositive (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L 0 (K : ℤ)) : ComplexMatrix2.specialUnitary :=
  if h : b.IsPositivelyOriented then v ⟨b, h⟩
  else if h' : b.opposite.IsPositivelyOriented then (v ⟨b.opposite, h'⟩)⁻¹
  else 1
private theorem coe_fieldOfPositive (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L 0 (K : ℤ)) :
    (fieldOfPositive v b : ComplexMatrix2) = PeriodicLattice.gaugeFieldOfPositive v b := by
  unfold fieldOfPositive PeriodicLattice.gaugeFieldOfPositive
  split_ifs
  · rfl
  · exact InfiniteLattice.specialUnitary_coe_inv _
  · rfl
private theorem fieldOfPositive_forward (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (y : PeriodicLattice.Site L 0 (K : ℤ)) (μ : Fin 4) :
    fieldOfPositive v (forwardBond y μ).1 = v (forwardBond y μ) := by
  unfold fieldOfPositive
  rw [dif_pos (forwardBond y μ).2]
private theorem fieldOfPositive_opposite (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) (b : PeriodicLattice.Bond L 0 (K : ℤ)) :
    fieldOfPositive v b.opposite = (fieldOfPositive v b)⁻¹ := by
  rcases positive_or_opposite b with h | h
  · have h' := not_opposite_positive hL hM h3 h
    have h'' : b.opposite.opposite.IsPositivelyOriented := h
    unfold fieldOfPositive
    rw [dif_neg h', dif_pos h'', dif_pos h]
    rfl
  · have h' : ¬ b.IsPositivelyOriented := fun hb => not_opposite_positive hL hM h3 hb h
    unfold fieldOfPositive
    rw [dif_pos h, dif_neg h', dif_pos h, inv_inv]
private theorem gaugeFieldOfPositive_mem (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L 0 (K : ℤ) := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [← coe_fieldOfPositive]
    exact (fieldOfPositive v b).2
  · rw [← coe_fieldOfPositive, ← coe_fieldOfPositive, fieldOfPositive_opposite hL hM h3,
      InfiniteLattice.specialUnitary_coe_inv]
private theorem liftField_apply (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (b : InfiniteLattice.Link (PeriodicLattice.meshSize L (K : ℤ))) :
    (InfiniteLattice.liftField L 0 (K : ℤ) (PeriodicLattice.gaugeFieldOfPositive v)) b =
      fieldOfPositive v (InfiniteLattice.projectLink L 0 (K : ℤ) b) := by
  have e := (dif_pos (gaugeFieldOfPositive_mem hL hM h3 v) : InfiniteLattice.liftField L 0 (K : ℤ)
    (PeriodicLattice.gaugeFieldOfPositive v) = _)
  exact (congrArg (fun C : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) => C.1 b) e).trans
    (Subtype.ext (coe_fieldOfPositive v _).symm)
private def toUnitQuaternion : ComplexMatrix2.specialUnitary →* UnitQuaternion where
  toFun V := ⟨toQuaternion V, by
    rw [Unitary.mem_iff]
    refine ⟨?_, toQuaternion_mul_star V⟩
    rw [← toQuaternion_inv, ← toQuaternion_mul, inv_mul_cancel, toQuaternion_one]⟩
  map_one' := Subtype.ext toQuaternion_one
  map_mul' V W := Subtype.ext (toQuaternion_mul V W)
private theorem continuous_toUnitQuaternion : Continuous toUnitQuaternion :=
  continuous_toQuaternion.subtype_mk _
private theorem toUnitQuaternion_surjective : Function.Surjective toUnitQuaternion := by
  intro w
  have h1 : Quaternion.normSq (w : ℍ[ℝ]) = 1 := by
    have h2 := (Unitary.mem_iff.mp w.2).1
    rw [Quaternion.star_mul_self] at h2
    simpa using congrArg (fun z : ℍ[ℝ] => z.re) h2
  have h3 : ‖(w : ℍ[ℝ])‖ * ‖(w : ℍ[ℝ])‖ = 1 := by rw [← Quaternion.normSq_eq_norm_mul_self, h1]
  have h4 : ‖(w : ℍ[ℝ])‖ = 1 := by nlinarith [norm_nonneg (w : ℍ[ℝ])]
  obtain ⟨V, hV⟩ := exists_toQuaternion_eq_of_norm_eq_one _ h4
  exact ⟨V, Subtype.ext hV⟩
private theorem toUnitQuaternion_re (V : ComplexMatrix2.specialUnitary) :
    ((toUnitQuaternion V : UnitQuaternion) : ℍ[ℝ]).re = (toQuaternion V).re := rfl
private def toTorusField (L K M : ℕ) : (PosBond L K → ComplexMatrix2.specialUnitary) →* TorusField M where
  toFun v x μ := toUnitQuaternion (v (forwardBond (torusSiteOf L K x) μ))
  map_one' := by
    funext x μ
    simp
  map_mul' v w := by
    funext x μ
    simp
private theorem continuous_toTorusField : Continuous (toTorusField L K M) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_toUnitQuaternion.comp (continuous_apply _)
private theorem toTorusField_surjective [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) :
    Function.Surjective (toTorusField L K M) := by
  intro W
  have hb : Function.Bijective fun c : TorusSite M × Fin 4 => forwardBond (torusSiteOf L K c.1) c.2 := by
    constructor
    · rintro ⟨x, μ⟩ ⟨y, ν⟩ h
      obtain ⟨h1, h2⟩ := forwardBond_injective hL hM h3 h
      exact Prod.ext (torusSiteOf_injective hL hM h1) h2
    · intro p
      obtain ⟨y, μ, rfl⟩ := forwardBond_surjective p
      obtain ⟨x, rfl⟩ := torusSiteOf_surjective hL hM y
      exact ⟨(x, μ), rfl⟩
  let e := Equiv.ofBijective _ hb
  choose g hg using toUnitQuaternion_surjective
  refine ⟨fun p => g (W (e.symm p).1 (e.symm p).2), ?_⟩
  funext x μ
  have h1 : e.symm (forwardBond (torusSiteOf L K x) μ) = (x, μ) := e.symm_apply_apply (x, μ)
  show toUnitQuaternion (g (W (e.symm (forwardBond (torusSiteOf L K x) μ)).1
    (e.symm (forwardBond (torusSiteOf L K x) μ)).2)) = W x μ
  rw [h1, hg]
private instance : SecondCountableTopology ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
private instance : SecondCountableTopology ComplexMatrix2.specialUnitary :=
  TopologicalSpace.Subtype.secondCountableTopology (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)
private instance : SecondCountableTopology UnitQuaternion :=
  TopologicalSpace.Subtype.secondCountableTopology (unitary ℍ[ℝ] : Set ℍ[ℝ])
private theorem finite_posBond [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) : Finite (PosBond L K) := by
  refine Finite.of_surjective (fun c : TorusSite M × Fin 4 => forwardBond (torusSiteOf L K c.1) c.2) ?_
  intro p
  obtain ⟨y, μ, rfl⟩ := forwardBond_surjective p
  obtain ⟨x, rfl⟩ := torusSiteOf_surjective hL hM y
  exact ⟨(x, μ), rfl⟩
private theorem haarProb_isHaarMeasure : ComplexMatrix2.haarProb.IsHaarMeasure := by
  unfold ComplexMatrix2.haarProb
  infer_instance
private theorem map_gaugeFieldHaar [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) :
    (PeriodicLattice.gaugeFieldHaar L 0 (K : ℤ)).map (toTorusField L K M) = fieldHaar M := by
  have := finite_posBond hL hM
  let _ := Fintype.ofFinite (PosBond L K)
  have := haarProb_isHaarMeasure
  have e : PeriodicLattice.gaugeFieldHaar L 0 (K : ℤ) =
      Measure.pi fun _ : PosBond L K => ComplexMatrix2.haarProb := by
    unfold PeriodicLattice.gaugeFieldHaar ComplexMatrix2.haarPi
    exact Measure.infinitePi_eq_pi _
  rw [e]
  have : ((Measure.pi fun _ : PosBond L K => ComplexMatrix2.haarProb).map (toTorusField L K M)).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ _ continuous_toTorusField (toTorusField_surjective hL hM h3) (by simp)
  have : IsProbabilityMeasure ((Measure.pi fun _ : PosBond L K => ComplexMatrix2.haarProb).map
      (toTorusField L K M)) :=
    Measure.isProbabilityMeasure_map continuous_toTorusField.measurable.aemeasurable
  have : (fieldHaar M).IsHaarMeasure := by
    have : (Measure.pi fun _ : Fin 4 => haarUnit).IsHaarMeasure := inferInstance
    unfold fieldHaar
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
private def loopValue (v : PosBond L K → ComplexMatrix2.specialUnitary) (y : PeriodicLattice.Site L 0 (K : ℤ))
    (μ ν : Fin 4) : ComplexMatrix2.specialUnitary :=
  v (forwardBond y μ) * v (forwardBond (y + PeriodicLattice.unitStep L 0 (K : ℤ) μ) ν) *
    (v (forwardBond (y + PeriodicLattice.unitStep L 0 (K : ℤ) ν) μ))⁻¹ * (v (forwardBond y ν))⁻¹
private theorem toTorusField_apply (v : PosBond L K → ComplexMatrix2.specialUnitary) (x : TorusSite M)
    (μ : Fin 4) :
    toTorusField L K M v x μ = toUnitQuaternion (v (forwardBond (torusSiteOf L K x) μ)) := rfl
private theorem toUnitQuaternion_loopValue [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) (x : TorusSite M) (μ ν : Fin 4) :
    toUnitQuaternion (loopValue v (torusSiteOf L K x) μ ν) = holonomy (toTorusField L K M v) x μ ν := by
  simp only [loopValue, map_mul, map_inv, holonomy, toTorusField_apply, torusSiteOf_add_unitStep hL hM]
private theorem plaquetteEnergy_eq [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) (x : TorusSite M) (μ ν : Fin 4) :
    plaquetteEnergy (toTorusField L K M v) x μ ν = 1 - (toQuaternion (loopValue v (torusSiteOf L K x) μ ν)).re := by
  unfold plaquetteEnergy
  rw [← toUnitQuaternion_loopValue hL hM, toUnitQuaternion_re]
private theorem plaquetteCost_eq (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) (p : PeriodicLattice.Plaquette L 0 (K : ℤ)) :
    PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeFieldOfPositive v) p =
      1 - (toQuaternion (loopValue v p.origin p.firstAxis p.secondAxis)).re := by
  have hf : ∀ y μ, PeriodicLattice.gaugeFieldOfPositive v (PeriodicLattice.Bond.forwardFrom y μ) =
      (v (forwardBond y μ) : ComplexMatrix2) := fun y μ => by
    rw [← coe_fieldOfPositive]
    exact congrArg (fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2)) (fieldOfPositive_forward v y μ)
  have hr : ∀ y μ, PeriodicLattice.gaugeFieldOfPositive v (PeriodicLattice.Bond.forwardFrom y μ).opposite =
      (((v (forwardBond y μ))⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := fun y μ => by
    rw [← coe_fieldOfPositive, fieldOfPositive_opposite hL hM h3]
    exact congrArg (fun g : ComplexMatrix2.specialUnitary => ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2))
      (fieldOfPositive_forward v y μ)
  have h1 : PeriodicLattice.plaquetteHolonomy (PeriodicLattice.gaugeFieldOfPositive v) p =
      ((loopValue v p.origin p.firstAxis p.secondAxis : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, hf, hr, loopValue, Submonoid.coe_mul, mul_assoc]
  unfold PeriodicLattice.plaquetteCost
  rw [h1, re_fullTrace_eq_two_mul_re]
  ring
private abbrev liftOf (L K : ℕ) (v : PosBond L K → ComplexMatrix2.specialUnitary) :
    InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) :=
  InfiniteLattice.liftField L 0 (K : ℤ) (PeriodicLattice.gaugeFieldOfPositive v)
private theorem projectLink_forwardFrom (y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ)))
    (μ : Fin 4) :
    InfiniteLattice.projectLink L 0 (K : ℤ) (InfiniteLattice.Link.forwardFrom y μ) =
      (forwardBond (InfiniteLattice.projectPoint L 0 (K : ℤ) y) μ).1 :=
  PeriodicLattice.Bond.ext rfl (by
    show InfiniteLattice.projectPoint L 0 (K : ℤ) (y + InfiniteLattice.axisStep _ μ) = _ + _
    rw [projectPoint_add, InfiniteLattice.projectPoint_axisStep])
private theorem liftOf_forwardFrom (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (y : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) (μ : Fin 4) :
    (liftOf L K v) (InfiniteLattice.Link.forwardFrom y μ) =
      v (forwardBond (InfiniteLattice.projectPoint L 0 (K : ℤ) y) μ) := by
  rw [liftField_apply hL hM h3, projectLink_forwardFrom, fieldOfPositive_forward]
private theorem faceEnergy_liftOf (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary)
    (P : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))) :
    InfiniteLattice.faceEnergy (liftOf L K v) P =
      1 - (toQuaternion (loopValue v (InfiniteLattice.projectPoint L 0 (K : ℤ) P.corner) P.lowAxis
        P.highAxis)).re := by
  have h1 : InfiniteLattice.faceHolonomy (liftOf L K v) P =
      loopValue v (InfiniteLattice.projectPoint L 0 (K : ℤ) P.corner) P.lowAxis P.highAxis := by
    simp only [InfiniteLattice.faceHolonomy, liftOf_forwardFrom hL hM h3, projectPoint_add,
      InfiniteLattice.projectPoint_axisStep, loopValue]
  unfold InfiniteLattice.faceEnergy
  rw [h1, re_fullTrace_eq_two_mul_re]
  ring
private theorem sum_plaquettesIn [NeZero M] (g : TorusPlaquette M → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite M)), g p = ∑ᶠ q : OrientedPlaquette M, g q.1 := by
  classical
  have h : ((plaquettesIn (Finset.univ : Finset (TorusSite M)) : Finset (TorusPlaquette M)) :
      Set (TorusPlaquette M)) = {p | p.2.1 < p.2.2} := by
    ext p
    simp [plaquettesIn]
  rw [← finsum_mem_coe_finset, h]
  exact (finsum_set_coe_eq_finsum_mem _).symm
private def torusPlaquetteOf (L K M : ℕ) (q : OrientedPlaquette M) : PeriodicLattice.Plaquette L 0 (K : ℤ) :=
  ⟨torusSiteOf L K q.1.1, q.1.2.1, q.1.2.2, q.2⟩
private theorem torusPlaquetteOf_bijective [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) :
    Function.Bijective (torusPlaquetteOf L K M) := by
  constructor
  · rintro ⟨⟨x, μ, ν⟩, h⟩ ⟨⟨y, μ', ν'⟩, h'⟩ e
    have e1 : torusSiteOf L K x = torusSiteOf L K y := congrArg PeriodicLattice.Plaquette.origin e
    have e2 : μ = μ' := congrArg PeriodicLattice.Plaquette.firstAxis e
    have e3 : ν = ν' := congrArg PeriodicLattice.Plaquette.secondAxis e
    subst e2 e3
    rw [torusSiteOf_injective hL hM e1]
  · rintro ⟨y, μ, ν, h⟩
    obtain ⟨x, rfl⟩ := torusSiteOf_surjective (M := M) hL hM y
    exact ⟨⟨(x, μ, ν), h⟩, rfl⟩
private theorem wilsonAction_eq [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
      TorusFields.wilsonAction Finset.univ (toTorusField L K M v) := by
  unfold PeriodicLattice.wilsonAction TorusFields.wilsonAction
  rw [sum_plaquettesIn (fun p => plaquetteEnergy (toTorusField L K M v) p.1 p.2.1 p.2.2),
    ← finsum_comp_equiv (Equiv.ofBijective _ (torusPlaquetteOf_bijective (K := K) (M := M) hL hM))]
  refine finsum_congr fun q => ?_
  rw [plaquetteEnergy_eq hL hM]
  exact plaquetteCost_eq hL hM h3 v _
private def latticePlaquetteOf (L K M : ℕ) (c : OrientedPlaquette M × (Fin 4 → ℤ)) :
    InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) :=
  ⟨latticePointOf _ (coords c.1.1.1 + (M : ℤ) • c.2), c.1.1.2.1, c.1.1.2.2, c.1.2⟩
private theorem siteOfInt_coords_add [NeZero M] (x : TorusSite M) (z : Fin 4 → ℤ) :
    (siteOfInt (coords x + (M : ℤ) • z) : TorusSite M) = x := by
  funext i
  simp [siteOfInt, coords]
private theorem latticePointOf_injective {a : ℝ} (ha : a ≠ 0) {n n' : Fin 4 → ℤ}
    (h : latticePointOf a n = latticePointOf a n') : n = n' := by
  funext μ
  have h1 := congrFun (congrArg Subtype.val h) μ
  have h2 : (n μ : ℝ) * a = (n' μ : ℝ) * a := h1
  exact_mod_cast mul_right_cancel₀ ha h2
private theorem latticePlaquetteOf_bijective [NeZero M] (hL : 0 < L) :
    Function.Bijective (latticePlaquetteOf L K M) := by
  have ha := (meshSize_pos (K := K) hL).ne'
  constructor
  · rintro ⟨⟨⟨x, μ, ν⟩, h⟩, z⟩ ⟨⟨⟨y, μ', ν'⟩, h'⟩, z'⟩ e
    have e1 : coords x + (M : ℤ) • z = coords y + (M : ℤ) • z' :=
      latticePointOf_injective ha (congrArg InfiniteLattice.ElementaryPlaquette.corner e)
    have e2 : μ = μ' := congrArg InfiniteLattice.ElementaryPlaquette.lowAxis e
    have e3 : ν = ν' := congrArg InfiniteLattice.ElementaryPlaquette.highAxis e
    subst e2 e3
    have e4 : x = y := by
      have := congrArg (fun n => (siteOfInt n : TorusSite M)) e1
      simpa only [siteOfInt_coords_add] using this
    subst e4
    have e5 : z = z' := by
      funext i
      have h1 := congrFun (add_left_cancel e1) i
      have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
      exact mul_left_cancel₀ hM0 (by simpa using h1)
    rw [e5]
  · rintro ⟨⟨b, n, hn⟩, μ, ν, h⟩
    refine ⟨(⟨(siteOfInt n, μ, ν), h⟩, fun i => n i / (M : ℤ)), ?_⟩
    refine InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext (funext fun i => ?_)) rfl rfl
    have h1 : coords (siteOfInt n : TorusSite M) i + (M : ℤ) * (n i / (M : ℤ)) = n i := by
      simp only [coords, siteOfInt, ZMod.val_intCast]
      exact Int.emod_add_mul_ediv _ _
    show (((coords (siteOfInt n : TorusSite M) + (M : ℤ) • fun i => n i / (M : ℤ)) i : ℤ) : ℝ) * _ = b i
    rw [hn i]
    congr 2
private def torusBarycenter (L K : ℕ) (p : TorusPlaquette M) : AmbientSpace :=
  fun i => ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)
private theorem center_latticePlaquetteOf [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K)
    (c : OrientedPlaquette M × (Fin 4 → ℤ)) :
    (latticePlaquetteOf L K M c).center = fun i => torusBarycenter L K c.1.1 i + 2 * (c.2 i : ℝ) := by
  obtain ⟨⟨⟨x, μ, ν⟩, h⟩, z⟩ := c
  have hMa := torusSide_mul_meshSize hL hM
  have hne : μ ≠ ν := ne_of_lt h
  have hP : ((L : ℝ) ^ K)⁻¹ = PeriodicLattice.meshSize L (K : ℤ) := by
    simp [PeriodicLattice.meshSize, zpow_neg]
  have hL0 : ((L : ℝ) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL.ne')
  funext i
  have hv : (x i).val < M := ZMod.val_lt _
  have hd : (doubledBarycentre ((x, μ, ν) : TorusPlaquette M) i).val =
      2 * (x i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) := by
    unfold doubledBarycentre
    apply ZMod.val_natCast_of_lt
    by_cases h1 : i = μ
    · have h2 : i ≠ ν := fun e => hne (h1.symm.trans e)
      simp only [h1, if_true]
      simp only [← h1, if_neg h2]
      omega
    · simp only [if_neg h1]
      split_ifs <;> omega
  have hb : (latticePlaquetteOf L K M (⟨(x, μ, ν), h⟩, z)).center i =
      (((coords x i : ℤ) : ℝ) + (M : ℝ) * (z i : ℝ)) * PeriodicLattice.meshSize L (K : ℤ) +
        (Pi.single μ (PeriodicLattice.meshSize L (K : ℤ) / 2) : AmbientSpace) i +
        (Pi.single ν (PeriodicLattice.meshSize L (K : ℤ) / 2) : AmbientSpace) i := by
    show (((coords x + (M : ℤ) • z) i : ℤ) : ℝ) * _ + _ + _ = _
    simp
    rfl
  rw [hb]
  show _ = ((doubledBarycentre ((x, μ, ν) : TorusPlaquette M) i).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z i : ℝ)
  rw [hd]
  have hq : ∀ t : ℝ, t / (2 * (L : ℝ) ^ K) = t * PeriodicLattice.meshSize L (K : ℤ) / 2 := fun t => by
    rw [← hP]
    field_simp
  rw [hq]
  by_cases h1 : i = μ
  · have h2 : i ≠ ν := fun e => hne (h1.symm.trans e)
    subst h1
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne h2, if_true, if_neg h2, coords]
    push_cast
    linear_combination (z i : ℝ) * hMa
  · by_cases h2 : i = ν
    · subst h2
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne h1, if_true, if_neg h1, coords]
      push_cast
      linear_combination (z i : ℝ) * hMa
    · simp only [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, if_neg h1, if_neg h2, coords]
      push_cast
      linear_combination (z i : ℝ) * hMa
private theorem finite_periodShifts {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) (c : AmbientSpace) :
    {z : Fin 4 → ℤ | f (fun i => c i + 2 * (z i : ℝ)) ≠ 0}.Finite := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  have hC' : ∀ x, f x ≠ 0 → ‖x‖ ≤ C := fun x hx => hC x (subset_tsupport f hx)
  refine (Set.finite_Icc (fun _ => -⌈C + ‖c‖⌉) (fun _ => ⌈C + ‖c‖⌉)).subset ?_
  intro z hz
  have h1 := hC' _ hz
  have hC0 : 0 ≤ C := (norm_nonneg _).trans h1
  have hB : C + ‖c‖ ≤ (⌈C + ‖c‖⌉ : ℝ) := Int.le_ceil _
  have hc0 := norm_nonneg c
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · have h2 := (norm_le_pi_norm (fun i => c i + 2 * (z i : ℝ)) i).trans h1
    have h3 := norm_le_pi_norm c i
    rw [Real.norm_eq_abs, abs_le] at h2 h3
    have : (-(⌈C + ‖c‖⌉ : ℤ) : ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ (⌈C + ‖c‖⌉ : ℝ) := by
      constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
    first
      | exact_mod_cast this.1
      | exact_mod_cast this.2
private theorem finite_support_latticePlaquetteOf [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K)
    {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    {c : OrientedPlaquette M × (Fin 4 → ℤ) | f (latticePlaquetteOf L K M c).center ≠ 0}.Finite := by
  refine (Set.finite_iUnion fun q : OrientedPlaquette M =>
    (finite_periodShifts hf (torusBarycenter L K q.1)).image (Prod.mk q)).subset ?_
  rintro ⟨q, z⟩ h
  refine Set.mem_iUnion.mpr ⟨q, z, ?_, rfl⟩
  have h1 : f (latticePlaquetteOf L K M (q, z)).center ≠ 0 := h
  rw [center_latticePlaquetteOf hL hM] at h1
  exact h1
private def periodicWeight (L K M : ℕ) (f : AmbientSpace → ℝ) : PlaquetteWeight M := fun p =>
  periodizeUnitTorus f fun i => ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)
private theorem smearedEnergy_liftOf [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) (v : PosBond L K → ComplexMatrix2.specialUnitary) :
    InfiniteLattice.smearedEnergy f (liftOf L K v) =
      curvatureObservable (periodicWeight L K M f) (toTorusField L K M v) := by
  have hact : ∀ c : OrientedPlaquette M × (Fin 4 → ℤ),
      InfiniteLattice.faceEnergy (liftOf L K v) (latticePlaquetteOf L K M c) =
        plaquetteEnergyOf (toTorusField L K M v) c.1.1 := by
    rintro ⟨⟨⟨x, μ, ν⟩, h⟩, z⟩
    rw [faceEnergy_liftOf hL hM h3]
    have h1 : InfiniteLattice.projectPoint L 0 (K : ℤ) (latticePlaquetteOf L K M (⟨(x, μ, ν), h⟩, z)).corner =
        torusSiteOf L K x := by
      show InfiniteLattice.projectPoint L 0 (K : ℤ) (latticePointOf _ (coords x + (M : ℤ) • z)) = _
      rw [projectPoint_latticePointOf, ← torusSiteOf_siteOfInt hL hM, siteOfInt_coords_add]
    rw [h1]
    exact (plaquetteEnergy_eq hL hM v x μ ν).symm
  unfold InfiniteLattice.smearedEnergy curvatureObservable
  rw [sum_plaquettesIn (fun p => periodicWeight L K M f p * plaquetteEnergyOf (toTorusField L K M v) p),
    ← finsum_comp_equiv (Equiv.ofBijective _ (latticePlaquetteOf_bijective (K := K) (M := M) hL))]
  simp only [Equiv.ofBijective_apply, smul_eq_mul, hact]
  rw [finsum_curry]
  · refine finsum_congr fun q => ?_
    show ∑ᶠ z, plaquetteEnergyOf (toTorusField L K M v) q.1 * f (latticePlaquetteOf L K M (q, z)).center =
      periodicWeight L K M f q.1 * plaquetteEnergyOf (toTorusField L K M v) q.1
    rw [← mul_finsum, mul_comm]
    congr 1
    unfold periodicWeight periodizeUnitTorus
    refine finsum_congr fun z => ?_
    rw [center_latticePlaquetteOf hL hM]
    rfl
  · refine (finite_support_latticePlaquetteOf (L := L) (K := K) hL hM hf).subset ?_
    intro c hc h0
    exact hc (by simp [show f (latticePlaquetteOf L K M (c.1, c.2)).center = 0 from h0])
private theorem continuous_fieldOfPositive (b : PeriodicLattice.Bond L 0 (K : ℤ)) :
    Continuous fun v : PosBond L K → ComplexMatrix2.specialUnitary => fieldOfPositive v b := by
  unfold fieldOfPositive
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).inv
  · exact continuous_const
private theorem continuous_liftOf (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) :
    Continuous (liftOf L K) := by
  have h : Continuous fun v : PosBond L K → ComplexMatrix2.specialUnitary => (liftOf L K v).1 :=
    continuous_pi fun b => by
      have e : (fun v : PosBond L K → ComplexMatrix2.specialUnitary => (liftOf L K v).1 b) =
          fun v => fieldOfPositive v (InfiniteLattice.projectLink L 0 (K : ℤ) b) :=
        funext fun v => liftField_apply hL hM h3 v b
      rw [e]
      exact continuous_fieldOfPositive _
  exact continuous_induced_rng.2 h
private theorem measurableEmbedding_gaugeFieldOfPositive :
    MeasurableEmbedding (PeriodicLattice.gaugeFieldOfPositive :
      (PosBond L K → ComplexMatrix2.specialUnitary) → PeriodicLattice.Bond L 0 (K : ℤ) → ComplexMatrix2) := by
  have hc : Continuous (PeriodicLattice.gaugeFieldOfPositive :
      (PosBond L K → ComplexMatrix2.specialUnitary) → PeriodicLattice.Bond L 0 (K : ℤ) → ComplexMatrix2) :=
    continuous_pi fun b => by
      have e : (fun v : PosBond L K → ComplexMatrix2.specialUnitary => PeriodicLattice.gaugeFieldOfPositive v b) =
          fun v => (fieldOfPositive v b : ComplexMatrix2) := funext fun v => (coe_fieldOfPositive v b).symm
      rw [e]
      exact continuous_subtype_val.comp (continuous_fieldOfPositive b)
  have hi : Function.Injective (PeriodicLattice.gaugeFieldOfPositive :
      (PosBond L K → ComplexMatrix2.specialUnitary) → PeriodicLattice.Bond L 0 (K : ℤ) → ComplexMatrix2) := by
    intro v w h
    funext p
    have h1 := congrFun h p.1
    rw [← coe_fieldOfPositive, ← coe_fieldOfPositive] at h1
    have h2 : fieldOfPositive v p.1 = fieldOfPositive w p.1 := Subtype.ext h1
    unfold fieldOfPositive at h2
    rwa [dif_pos p.2, dif_pos p.2] at h2
  exact (hc.isClosedEmbedding hi).measurableEmbedding
private theorem continuous_plaquetteEnergyOf (p : TorusPlaquette M) :
    Continuous fun W : TorusField M => plaquetteEnergyOf W p := by
  have hW : ∀ (x : TorusSite M) (i : Fin 4), Continuous fun W : TorusField M => W x i := fun x i =>
    (continuous_apply i).comp (continuous_apply x)
  have h : Continuous fun W : TorusField M => holonomy W p.1 p.2.1 p.2.2 :=
    (((hW _ _).mul (hW _ _)).mul (hW _ _).inv).mul (hW _ _).inv
  exact continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp h))
private theorem curvatureObservable_continuous [NeZero M] (h : PlaquetteWeight M) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private def boltzmannFactor [NeZero M] (β : ℝ) (W : TorusField M) : ℝ :=
  Real.exp (-β * TorusFields.wilsonAction Finset.univ W)
private theorem continuous_boltzmannFactor [NeZero M] (β : ℝ) :
    Continuous (boltzmannFactor β : TorusField M → ℝ) := by
  have h : Continuous fun W : TorusField M => TorusFields.wilsonAction Finset.univ W :=
    continuous_finsetSum _ fun p _ => continuous_plaquetteEnergyOf p
  exact Real.continuous_exp.comp (continuous_const.mul h)
abbrev _root_.YangMills.DeltaSharedProofs.p502405 := @continuous_boltzmannFactor
private theorem continuous_smearedEnergy [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      InfiniteLattice.smearedEnergy f U := by
  have hfin : {P : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) |
      f P.center ≠ 0}.Finite := by
    refine ((finite_support_latticePlaquetteOf (M := M) (L := L) (K := K) hL hM hf).image
      (latticePlaquetteOf L K M)).subset ?_
    intro P hP
    obtain ⟨c, rfl⟩ := (latticePlaquetteOf_bijective (K := K) (M := M) hL).2 P
    exact ⟨c, hP, rfl⟩
  have e : (fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      InfiniteLattice.smearedEnergy f U) =
        fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) => ∑ P ∈ hfin.toFinset,
          InfiniteLattice.faceEnergy U P • f P.center := by
    funext U
    unfold InfiniteLattice.smearedEnergy
    refine finsum_eq_sum_of_support_subset _ ?_
    intro P hP
    have hP' : f P.center ≠ 0 := fun h0 => hP (by simp [h0])
    simpa using hP'
  rw [e]
  refine continuous_finsetSum _ fun P _ => ?_
  simp only [smul_eq_mul]
  refine Continuous.mul ?_ continuous_const
  have hU : ∀ b : InfiniteLattice.Link (PeriodicLattice.meshSize L (K : ℤ)),
      Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) => U b :=
    fun b => (continuous_apply b).comp continuous_induced_dom
  have hv : Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      InfiniteLattice.faceHolonomy U P :=
    (((hU _).mul (hU _)).mul (hU _).inv).mul (hU _).inv
  have hm : Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      ((InfiniteLattice.faceHolonomy U P : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
    continuous_subtype_val.comp hv
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hm.matrix_trace))
private theorem integral_wilsonLaw_eq [NeZero M] (β : ℝ) (g : TorusField M → ℝ) :
    ∫ W, g W ∂wilsonLaw β M =
      (∫ W, boltzmannFactor β W ∂fieldHaar M)⁻¹ * ∫ W, boltzmannFactor β W * g W ∂fieldHaar M := by
  have hZ : 0 ≤ ∫ W, boltzmannFactor β W ∂fieldHaar M := integral_nonneg fun _ => (Real.exp_pos _).le
  have hm : Measurable fun W : TorusField M =>
      ENNReal.ofReal (boltzmannFactor β W / ∫ W', boltzmannFactor β W' ∂fieldHaar M) :=
    ((continuous_boltzmannFactor β).measurable.div_const _).ennreal_ofReal
  show ∫ W, g W ∂(fieldHaar M).withDensity
    (fun W => ENNReal.ofReal (boltzmannFactor β W / ∫ W', boltzmannFactor β W' ∂fieldHaar M)) = _
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun W => ?_)
  have h0 : 0 ≤ boltzmannFactor β W / ∫ W', boltzmannFactor β W' ∂fieldHaar M :=
    div_nonneg (Real.exp_pos _).le hZ
  show (ENNReal.ofReal _).toReal • g W = _
  rw [ENNReal.toReal_ofReal h0, smul_eq_mul]
  ring
private theorem boltzmannWeight_eq [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) (β : ℝ)
    (v : PosBond L K → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) =
      boltzmannFactor β (toTorusField L K M v) := by
  unfold PeriodicLattice.boltzmannWeight boltzmannFactor
  rw [wilsonAction_eq hL hM h3]
private theorem integral_wilsonGibbsMeasure [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) (β : ℝ)
    (h : (PeriodicLattice.Bond L 0 (K : ℤ) → ComplexMatrix2) → ℝ) :
    ∫ X, h X ∂PeriodicLattice.wilsonGibbsMeasure L 0 K β = (PeriodicLattice.partitionFunction L 0 K β)⁻¹ *
      ∫ v, boltzmannFactor β (toTorusField L K M v) * h (PeriodicLattice.gaugeFieldOfPositive v)
        ∂PeriodicLattice.gaugeFieldHaar L 0 (K : ℤ) := by
  have hD : AEMeasurable (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U))
      (PeriodicLattice.productHaarMeasure L 0 (K : ℤ)) := by
    unfold PeriodicLattice.productHaarMeasure
    rw [measurableEmbedding_gaugeFieldOfPositive.aemeasurable_map_iff]
    have e : ((fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U)) ∘
        (PeriodicLattice.gaugeFieldOfPositive : (PosBond L K → ComplexMatrix2.specialUnitary) → _)) =
        fun v => ENNReal.ofReal (boltzmannFactor β (toTorusField L K M v)) :=
      funext fun v => congrArg ENNReal.ofReal (boltzmannWeight_eq hL hM h3 β v)
    rw [e]
    exact (((continuous_boltzmannFactor β).comp continuous_toTorusField).measurable.ennreal_ofReal).aemeasurable
  have hZ : 0 ≤ PeriodicLattice.partitionFunction L 0 K β :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul₀ hD (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, smul_eq_mul]
  congr 1
  unfold PeriodicLattice.productHaarMeasure
  rw [measurableEmbedding_gaugeFieldOfPositive.integral_map]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  show (ENNReal.ofReal (PeriodicLattice.boltzmannWeight β _)).toReal • _ = _
  have h0 : 0 ≤ boltzmannFactor β (toTorusField L K M v) := (Real.exp_pos _).le
  rw [boltzmannWeight_eq hL hM h3, ENNReal.toReal_ofReal h0, smul_eq_mul]
private theorem integral_toTorusField [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M)
    {H : TorusField M → ℝ} (hH : Continuous H) :
    ∫ v, H (toTorusField L K M v) ∂PeriodicLattice.gaugeFieldHaar L 0 (K : ℤ) = ∫ W, H W ∂fieldHaar M := by
  rw [← map_gaugeFieldHaar hL hM h3,
    integral_map (continuous_toTorusField.measurable.aemeasurable) hH.aestronglyMeasurable]
private theorem partitionFunction_eq [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) (β : ℝ) :
    PeriodicLattice.partitionFunction L 0 K β = ∫ W, boltzmannFactor β W ∂fieldHaar M := by
  unfold PeriodicLattice.partitionFunction PeriodicLattice.productHaarMeasure
  rw [measurableEmbedding_gaugeFieldOfPositive.integral_map,
    ← integral_toTorusField hL hM h3 (continuous_boltzmannFactor β)]
  exact integral_congr_ae (ae_of_all _ fun v => boltzmannWeight_eq hL hM h3 β v)
private theorem moments_eq [NeZero M] (hL : 0 < L) (hM : M = 2 * L ^ K) (h3 : 3 ≤ M) (β : ℝ) {p : ℕ}
    (φ : Fin p → AmbientSpace → ℝ) (hφ : ∀ i, HasCompactSupport (φ i)) :
    ∫ U, ∏ i, InfiniteLattice.smearedEnergy (φ i) U ∂InfiniteLattice.liftedWilsonMeasure L 0 K β =
      ∫ W, ∏ i, curvatureObservable (periodicWeight L K M (φ i)) W ∂wilsonLaw β M := by
  have hF : Continuous fun U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      ∏ i, InfiniteLattice.smearedEnergy (φ i) U :=
    continuous_finsetProd _ fun i _ => continuous_smearedEnergy hL hM (hφ i)
  have hext : AEMeasurable (InfiniteLattice.liftField L 0 (K : ℤ))
      (PeriodicLattice.wilsonGibbsMeasure L 0 K β) := by
    have h1 : AEMeasurable (InfiniteLattice.liftField L 0 (K : ℤ))
        (PeriodicLattice.productHaarMeasure L 0 (K : ℤ)) := by
      unfold PeriodicLattice.productHaarMeasure
      rw [measurableEmbedding_gaugeFieldOfPositive.aemeasurable_map_iff]
      exact (continuous_liftOf hL hM h3).measurable.aemeasurable
    unfold PeriodicLattice.wilsonGibbsMeasure
    exact (h1.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure _
  have hH : Continuous fun W : TorusField M =>
      boltzmannFactor β W * ∏ i, curvatureObservable (periodicWeight L K M (φ i)) W :=
    (continuous_boltzmannFactor β).mul (continuous_finsetProd _ fun i _ => curvatureObservable_continuous _)
  unfold InfiniteLattice.liftedWilsonMeasure
  rw [integral_map hext hF.aestronglyMeasurable, integral_wilsonGibbsMeasure hL hM h3, integral_wilsonLaw_eq,
    partitionFunction_eq hL hM h3, ← integral_toTorusField hL hM h3 hH]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  show boltzmannFactor β (toTorusField L K M v) * ∏ i, InfiniteLattice.smearedEnergy (φ i) (liftOf L K v) = _
  congr 1
  exact Finset.prod_congr rfl fun i _ => smearedEnergy_liftOf hL hM h3 (hφ i) v
theorem unitTorusMomentsViaWeights : unitTorusMomentsViaWeightsStatement := by
  intro L K k _ _ hL3 hK hk β p φ hφ
  have hL : 0 < L := by omega
  have hM : fineSide L k (boxSide L K k) = 2 * L ^ K := by
    rw [fineSide_eq]
    unfold boxSide
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  have h3 : 3 ≤ fineSide L k (boxSide L K k) := by
    have h1 : L ≤ L ^ K := Nat.le_self_pow (by omega) L
    omega
  exact moments_eq hL hM h3 β φ fun i => (hφ i).2.2
end YangMills.Construction.LawInAState
end
