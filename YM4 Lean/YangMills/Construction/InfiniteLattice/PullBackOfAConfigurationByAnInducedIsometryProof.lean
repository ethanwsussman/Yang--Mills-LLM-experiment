import YangMills.Construction.InfiniteLattice.CurvatureObservableOnTheInfiniteLatticeProof
import YangMills.Construction.InfiniteLattice.PullBackOfAConfigurationByAnInducedIsometry
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction
namespace InducedPullback
open LatticeCovering (descend spacingIndex period mesh)
open FixedSpacing (Params)
open InfiniteLattice (AmbientSpace hypercubicGroup latticeMotions basisVector)
open PeriodicLattice (Bond CompactGaugeField TorusLatticeSymmetry PositivelyOrientedBond Site FourTorus
  translateByVector unitStep forwardBonds)
theorem smul_basisVector_inj {a b : ℤˣ} {i j : Fin 4}
    (h : (((a : ℤˣ) : ℤ) : ℝ) • basisVector i = (((b : ℤˣ) : ℤ) : ℝ) • basisVector j) :
    a = b ∧ i = j := by
  have hcoord := congrFun h i
  have hij : i = j := by
    by_contra hne
    simp [basisVector, Pi.single_eq_of_ne hne] at hcoord
  subst hij
  simp only [basisVector, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hcoord
  exact ⟨Units.ext (by exact_mod_cast hcoord), rfl⟩
theorem exists_isSignedPermutationData {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) :
    ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ), IsSignedPermutationData w ε σ := by
  obtain ⟨σ, h⟩ := hw
  have hs : ∀ k, ∃ u : ℤˣ, w (basisVector k) = (((u : ℤˣ) : ℤ) : ℝ) • basisVector (σ k) := by
    intro k
    rcases h k with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose ε hε using hs
  exact ⟨σ, ε, hε⟩
theorem existsUnique_isSignedPermutationData {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) :
    ∃! p : (Fin 4 → ℤˣ) × (Fin 4 → Fin 4), IsSignedPermutationData w p.1 p.2 := by
  obtain ⟨σ, ε, h⟩ := exists_isSignedPermutationData hw
  refine ⟨(ε, σ), h, ?_⟩
  rintro ⟨ε', π'⟩ h'
  have key := fun k => smul_basisVector_inj ((h' k).symm.trans (h k))
  exact Prod.ext (funext fun k => (key k).1) (funext fun k => (key k).2)
theorem bijective_of_isSignedPermutationData {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup)
    {ε : Fin 4 → ℤˣ} {π : Fin 4 → Fin 4} (h : IsSignedPermutationData w ε π) : Bijective π := by
  obtain ⟨σ, ε', h'⟩ := exists_isSignedPermutationData hw
  have : π = σ := funext fun k => (smul_basisVector_inj ((h k).symm.trans (h' k))).2
  rw [this]
  exact σ.bijective
section Steps
variable {L m : ℕ} {j : ℤ}
theorem torusProj_meshSize_smul_basisVector (L m : ℕ) (j : ℤ) (k : Fin 4) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m)
        (PeriodicLattice.meshSize L j • basisVector k) =
      ((unitStep L m j k : Site L m j) : FourTorus L m) := by
  funext ν
  by_cases h : ν = k
  · subst h
    simp [TorusMetric.torusProj, basisVector, unitStep, PeriodicLattice.pointOnAxis]
  · simp [TorusMetric.torusProj, basisVector, unitStep, PeriodicLattice.pointOnAxis,
      Pi.single_eq_of_ne h]
theorem torusProj_unit_smul (L m : ℕ) (c : ℤˣ) (x : Fin 4 → ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) ((((c : ℤˣ) : ℤ) : ℝ) • x) =
      ((c : ℤˣ) : ℤ) • TorusMetric.torusProj (PeriodicLattice.torusSide L m) x := by
  have h := map_zsmul (PeriodicLattice.torusProjHom L m) ((c : ℤˣ) : ℤ) x
  have e : ((c : ℤˣ) : ℤ) • x = (((c : ℤˣ) : ℤ) : ℝ) • x := by
    funext μ
    simp
  rw [e] at h
  exact h
end Steps
section Bonds
variable {L m K : ℕ} (s : TorusLatticeSymmetry L m K) {ε : Fin 4 → ℤˣ} {π : Fin 4 → Fin 4}
def ShiftsUnitSteps (s : TorusLatticeSymmetry L m K) (ε : Fin 4 → ℤˣ) (π : Fin 4 → Fin 4) :
    Prop :=
  ∀ (z : Site L m (K : ℤ)) (k : Fin 4),
    s.pointMap (z + unitStep L m (K : ℤ) k) =
      s.pointMap z + ((ε k : ℤˣ) : ℤ) • unitStep L m (K : ℤ) (π k)
variable {s}
theorem exists_isBondImage (hk : ShiftsUnitSteps s ε π) (b : Bond L m (K : ℤ)) :
    ∃ b', s.IsBondImage b b' := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · have hh : b.target = b.source + unitStep L m (K : ℤ) μ := by
      rw [← h]
      abel
    have e := hk b.source μ
    rw [← hh] at e
    rcases Int.units_eq_one_or (ε μ) with hε | hε
    · refine ⟨⟨s.pointMap b.source, s.pointMap b.target, π μ, Or.inl ?_⟩, rfl⟩
      rw [e, hε]
      simp
    · refine ⟨⟨s.pointMap b.source, s.pointMap b.target, π μ, Or.inr ?_⟩, rfl⟩
      rw [e, hε]
      simp
  · have hh : b.source = b.target + unitStep L m (K : ℤ) μ := by
      have h' : b.source - b.target = unitStep L m (K : ℤ) μ := by
        rw [← neg_sub, h, neg_neg]
      rw [← h']
      abel
    have e := hk b.target μ
    rw [← hh] at e
    rcases Int.units_eq_one_or (ε μ) with hε | hε
    · refine ⟨⟨s.pointMap b.source, s.pointMap b.target, π μ, Or.inr ?_⟩, rfl⟩
      rw [e, hε]
      simp
    · refine ⟨⟨s.pointMap b.source, s.pointMap b.target, π μ, Or.inl ?_⟩, rfl⟩
      rw [e, hε]
      simp
theorem linkValue_pullbackConfig (U : CompactGaugeField L m (K : ℤ)) {b b' : Bond L m (K : ℤ)}
    (h : s.IsBondImage b b') : (pullbackConfig s U).linkValue b = U.linkValue b' := by
  have hex : ∃ b', s.IsBondImage b b' := ⟨b', h⟩
  have e₁ : s.bondMap b = hex.choose := dif_pos hex
  have e : s.bondMap b = b' := e₁.trans (s.isBondImage_unique hex.choose_spec h)
  apply Subtype.ext
  change U.1 (s.bondMap b) = U.1 b'
  rw [e]
theorem imageBond_of_eq_one {y : Site L m (K : ℤ)} {k : Fin 4} (h : ε k = 1) :
    imageBond ε π y k = Bond.forwardFrom y (π k) :=
  if_pos h
theorem imageBond_of_eq_neg_one {y : Site L m (K : ℤ)} {k : Fin 4} (h : ε k = -1) :
    imageBond ε π y k = Bond.forwardFrom (y - unitStep L m (K : ℤ) (π k)) (π k) :=
  if_neg (by rw [h]; decide)
theorem isBondImage_of_eq_one (hk : ShiftsUnitSteps s ε π) (z : Site L m (K : ℤ)) {k : Fin 4}
    (h : ε k = 1) :
    s.IsBondImage (Bond.forwardFrom z k) (imageBond ε π (s.pointMap z) k) := by
  rw [imageBond_of_eq_one h]
  change (s.pointMap z, s.pointMap z + unitStep L m (K : ℤ) (π k)) =
    (s.pointMap z, s.pointMap (z + unitStep L m (K : ℤ) k))
  rw [hk z k, h]
  simp
theorem isBondImage_opposite_of_eq_neg_one (hk : ShiftsUnitSteps s ε π) (z : Site L m (K : ℤ))
    {k : Fin 4} (h : ε k = -1) :
    s.IsBondImage (Bond.forwardFrom z k) (imageBond ε π (s.pointMap z) k).opposite := by
  rw [imageBond_of_eq_neg_one h]
  change (s.pointMap z - unitStep L m (K : ℤ) (π k) + unitStep L m (K : ℤ) (π k),
      s.pointMap z - unitStep L m (K : ℤ) (π k)) =
    (s.pointMap z, s.pointMap (z + unitStep L m (K : ℤ) k))
  rw [hk z k, h]
  simp [sub_eq_add_neg]
theorem bondEnds_imageBond (hk : ShiftsUnitSteps s ε π) (z : Site L m (K : ℤ)) (k : Fin 4) :
    bondEnds (imageBond ε π (s.pointMap z) k) =
      {s.toFun z, s.toFun (Bond.forwardFrom z k).target} := by
  rcases Int.units_eq_one_or (ε k) with h | h
  · have hi := isBondImage_of_eq_one hk z h
    have h₁ : (imageBond ε π (s.pointMap z) k).source = s.pointMap z := congrArg Prod.fst hi
    have h₂ : (imageBond ε π (s.pointMap z) k).target =
        s.pointMap (Bond.forwardFrom z k).target :=
      congrArg Prod.snd hi
    unfold bondEnds
    rw [h₁, h₂]
    rfl
  · have hi := isBondImage_opposite_of_eq_neg_one hk z h
    have h₁ : (imageBond ε π (s.pointMap z) k).target = s.pointMap z := congrArg Prod.fst hi
    have h₂ : (imageBond ε π (s.pointMap z) k).source =
        s.pointMap (Bond.forwardFrom z k).target :=
      congrArg Prod.snd hi
    unfold bondEnds
    rw [h₁, h₂, Set.pair_comm]
    rfl
theorem eq_of_bondEnds_eq {j : ℤ} (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {b b' : Bond L m j}
    (hb : b ∈ forwardBonds L m j) (hb' : b' ∈ forwardBonds L m j)
    (h : bondEnds b = bondEnds b') : b = b' := by
  unfold bondEnds at h
  rcases Set.pair_eq_pair_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Bond.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · exfalso
    have hr : b'.opposite = b := Bond.ext (Subtype.ext h₁.symm) (Subtype.ext h₂.symm)
    exact PeriodicLattice.opposite_notMem_positiveBonds hL hj hb' (hr ▸ hb)
theorem bondPermutation_forwardFrom (hL : 2 ≤ L) (hj : -(m : ℤ) < (K : ℤ))
    (z : Site L m (K : ℤ)) (k : Fin 4) :
    bondPermutation s ε π (Bond.forwardFrom z k) = imageBond ε π (s.pointMap z) k := by
  change imageBond ε π (s.pointMap z) (Bond.forwardFrom z k).axis = _
  rw [PeriodicLattice.MatrixValued.axis_forwardFrom hL hj]
theorem imageBond_mem_positiveBonds (y : Site L m (K : ℤ)) (k : Fin 4) :
    imageBond ε π y k ∈ forwardBonds L m (K : ℤ) := by
  unfold imageBond
  split_ifs
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
theorem bijOn_bondPermutation (hk : ShiftsUnitSteps s ε π) (hL : 2 ≤ L) (hj : -(m : ℤ) < (K : ℤ))
    (hfin : Finite (forwardBonds L m (K : ℤ))) (hinj : Injective s.toFun) :
    BijOn (bondPermutation s ε π) (forwardBonds L m (K : ℤ)) (forwardBonds L m (K : ℤ)) := by
  have hmaps : MapsTo (bondPermutation s ε π) (forwardBonds L m (K : ℤ))
      (forwardBonds L m (K : ℤ)) := by
    rintro b ⟨z, k, rfl⟩
    rw [bondPermutation_forwardFrom hL hj]
    exact imageBond_mem_positiveBonds _ _
  have himage : ∀ (z : Site L m (K : ℤ)) (k : Fin 4),
      bondEnds (bondPermutation s ε π (Bond.forwardFrom z k)) =
        s.toFun '' bondEnds (Bond.forwardFrom z k) := by
    intro z k
    rw [bondPermutation_forwardFrom hL hj, bondEnds_imageBond hk]
    unfold bondEnds
    rw [Set.image_pair]
    rfl
  have hinjOn : InjOn (bondPermutation s ε π) (forwardBonds L m (K : ℤ)) := by
    rintro b hb b' hb' h
    obtain ⟨z, k, rfl⟩ := id hb
    obtain ⟨z', k', rfl⟩ := id hb'
    have he : s.toFun '' bondEnds (Bond.forwardFrom z k) =
        s.toFun '' bondEnds (Bond.forwardFrom z' k') := by
      rw [← himage, ← himage, h]
    exact eq_of_bondEnds_eq hL hj hb hb' (Set.image_injective.mpr hinj he)
  refine ⟨hmaps, hinjOn, ?_⟩
  have hf : Injective (hmaps.restrict) := fun a b h =>
    Subtype.ext (hinjOn a.2 b.2 (congrArg Subtype.val h))
  have hs := Finite.injective_iff_surjective.mp hf
  intro y hy
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
theorem linkValue_pullbackConfig_of_mem (hk : ShiftsUnitSteps s ε π) (hL : 2 ≤ L)
    (hj : -(m : ℤ) < (K : ℤ))
    (U : CompactGaugeField L m (K : ℤ)) {b : Bond L m (K : ℤ)}
    (hb : b ∈ forwardBonds L m (K : ℤ)) :
    (pullbackConfig s U).linkValue b =
      U.linkValue (bondPermutation s ε π b) ^ ((bondSign ε b : ℤˣ) : ℤ) := by
  obtain ⟨z, k, rfl⟩ := hb
  have hd : bondSign ε (Bond.forwardFrom z k) = ε k :=
    congrArg ε (PeriodicLattice.MatrixValued.axis_forwardFrom hL hj z k)
  rw [hd, bondPermutation_forwardFrom hL hj]
  rcases Int.units_eq_one_or (ε k) with h | h
  · rw [linkValue_pullbackConfig U (isBondImage_of_eq_one hk z h), h]
    simp
  · rw [linkValue_pullbackConfig U (isBondImage_opposite_of_eq_neg_one hk z h),
      PeriodicLattice.CompactGaugeField.linkValue_opposite, h]
    simp
theorem exists_bond_of_shiftsUnitSteps (hk : ShiftsUnitSteps s ε π) (b : Bond L m (K : ℤ)) :
    ∃ b' : Bond L m (K : ℤ), (b'.source : FourTorus L m) = s.toFun b.source ∧
      (b'.target : FourTorus L m) = s.toFun b.target := by
  obtain ⟨b', hb'⟩ := exists_isBondImage hk b
  have h₁ : b'.source = s.pointMap b.source := congrArg Prod.fst hb'
  have h₂ : b'.target = s.pointMap b.target := congrArg Prod.snd hb'
  exact ⟨b', congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
theorem bondPermutation_forwardFrom_spec (hk : ShiftsUnitSteps s ε π) (hL : 2 ≤ L)
    (hj : -(m : ℤ) < (K : ℤ)) (z : Site L m (K : ℤ)) (k : Fin 4) :
    bondSign ε (Bond.forwardFrom z k) = ε k ∧
      bondPermutation s ε π (Bond.forwardFrom z k) = imageBond ε π (s.pointMap z) k ∧
      bondPermutation s ε π (Bond.forwardFrom z k) ∈ forwardBonds L m (K : ℤ) ∧
      bondEnds (bondPermutation s ε π (Bond.forwardFrom z k)) =
        {s.toFun z, s.toFun (Bond.forwardFrom z k).target} ∧
      ∀ e' ∈ forwardBonds L m (K : ℤ),
        bondEnds e' = {s.toFun z, s.toFun (Bond.forwardFrom z k).target} →
          e' = bondPermutation s ε π (Bond.forwardFrom z k) := by
  have hb : bondPermutation s ε π (Bond.forwardFrom z k) = imageBond ε π (s.pointMap z) k :=
    bondPermutation_forwardFrom hL hj z k
  refine ⟨congrArg ε (PeriodicLattice.MatrixValued.axis_forwardFrom hL hj z k), hb, ?_, ?_, ?_⟩
  · rw [hb]
    exact imageBond_mem_positiveBonds _ _
  · rw [hb]
    exact bondEnds_imageBond hk z k
  · intro b' hb' he
    refine eq_of_bondEnds_eq hL hj hb' (by rw [hb]; exact imageBond_mem_positiveBonds _ _) ?_
    rw [he, hb, bondEnds_imageBond hk z k]
end Bonds
section Measures
variable {L m : ℕ} {j : ℤ}
theorem secondCountable_complexMatrix2 : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem measurableEmbedding_subtype_val (hc : CompactSpace (CompactGaugeField L m j)) :
    MeasurableEmbedding fun U : CompactGaugeField L m j => U.1 := by apply _root_.YangMills.Construction.FixedSpacing.CurvatureObservable.measurableEmbedding_linkValues <;> assumption
theorem gaugeFieldOfPositive_restrict
    (hxor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (U : CompactGaugeField L m j) :
    PeriodicLattice.gaugeFieldOfPositive (PeriodicLattice.restrictToPositiveBonds U) = U.1 := by
  funext b
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h]
    rfl
  · have h' : b.opposite.IsPositivelyOriented := by
      rcases hxor b with q | q
      · exact absurd q.1 h
      · exact q.1
    rw [dif_neg h, dif_pos h']
    exact (U.2.2 b.opposite (mem_univ _)).symm
theorem isProductHaarImage_productHaarOnFields
    (hxor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hc : CompactSpace (CompactGaugeField L m j))
    (e : CompactGaugeField L m j ≃ₜ
      (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary))
    (he : ⇑e = PeriodicLattice.restrictToPositiveBonds) :
    PeriodicLattice.IsProductHaarImage L m j (productHaarOnFields L m j) := by
  have := secondCountable_complexMatrix2
  have := secondCountable_specialUnitary
  have hemb := measurableEmbedding_subtype_val hc
  have hsym : Measurable e.symm := e.symm.continuous.measurable
  have hvals : Measurable
      (PeriodicLattice.restrictToPositiveBonds : CompactGaugeField L m j → _) :=
    he ▸ e.continuous.measurable
  have hinv : ∀ X, PeriodicLattice.restrictToPositiveBonds (e.symm X) = X := fun X => by
    rw [← he]
    exact e.apply_symm_apply X
  have hcomp : (PeriodicLattice.gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _) =
      (fun U : CompactGaugeField L m j => U.1) ∘ e.symm := by
    funext X
    have h := gaugeFieldOfPositive_restrict hxor (e.symm X)
    rw [hinv] at h
    exact h
  have hν : productHaarOnFields L m j =
      (Matrices.ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)).map e.symm := by
    unfold productHaarOnFields PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
    rw [hcomp, ← Measure.map_map hemb.measurable hsym]
    exact hemb.comap_map _
  unfold PeriodicLattice.IsProductHaarImage
  rw [hν, Measure.map_map hvals hsym]
  have hid : PeriodicLattice.restrictToPositiveBonds ∘ e.symm = id := funext hinv
  rw [hid, Measure.map_id]
theorem preservesIntegrals_of_isProductHaarImage {K : ℕ} (s : TorusLatticeSymmetry L m K)
    (R : (PositivelyOrientedBond L m (K : ℤ) → Matrices.ComplexMatrix2.specialUnitary) →
      PositivelyOrientedBond L m (K : ℤ) → Matrices.ComplexMatrix2.specialUnitary)
    (hR : Measurable R)
    (hmap : Measure.map R (Matrices.ComplexMatrix2.haarPi (PositivelyOrientedBond L m (K : ℤ))) =
      Matrices.ComplexMatrix2.haarPi (PositivelyOrientedBond L m (K : ℤ)))
    (hp : Measurable (pullbackConfig s))
    (hv : Measurable (PeriodicLattice.restrictToPositiveBonds :
      CompactGaugeField L m (K : ℤ) → _))
    (hcomm : ∀ U, PeriodicLattice.restrictToPositiveBonds (pullbackConfig s U) =
      R (PeriodicLattice.restrictToPositiveBonds U))
    (huniq : ∃! μ : Measure (CompactGaugeField L m (K : ℤ)),
      PeriodicLattice.IsProductHaarImage L m (K : ℤ) μ)
    {ν : Measure (CompactGaugeField L m (K : ℤ))}
    (hν : PeriodicLattice.IsProductHaarImage L m (K : ℤ) ν) : PreservesIntegrals s ν := by
  have hpush : PeriodicLattice.IsProductHaarImage L m (K : ℤ) (ν.map (pullbackConfig s)) := by
    unfold PeriodicLattice.IsProductHaarImage at hν ⊢
    rw [Measure.map_map hv hp]
    have h : PeriodicLattice.restrictToPositiveBonds ∘ pullbackConfig s =
        R ∘ PeriodicLattice.restrictToPositiveBonds := funext hcomm
    rw [h, ← Measure.map_map hR hv, hν, hmap]
  have heq : ν.map (pullbackConfig s) = ν := huniq.unique hpush hν
  intro Ξ hΞ _
  rw [← integral_map hp.aemeasurable hΞ.aestronglyMeasurable, heq]
end Measures
section Assembly
theorem shiftsUnitSteps_of_descend (D : Params) (r : latticeMotions (mesh D))
    {ε : Fin 4 → ℤˣ} {π : Fin 4 → Fin 4}
    (hmove : ∀ (z : FourTorus D.L D.m) (k : Fin 4),
      descend D r.1 (translateByVector z (mesh D • basisVector k)) =
        translateByVector (descend D r.1 z)
          ((((ε k : ℤˣ) : ℤ) : ℝ) • mesh D • basisVector (π k)))
    (s : TorusLatticeSymmetry D.L D.m (D.K : ℕ)) (hs : s.toFun = descend D r.1) :
    ShiftsUnitSteps s ε π := by
  intro z k
  apply Subtype.ext
  have h := hmove z k
  unfold translateByVector at h
  rw [torusProj_unit_smul, torusProj_meshSize_smul_basisVector,
    torusProj_meshSize_smul_basisVector, ← hs] at h
  exact h
theorem pullbackIsGaugeField (D : Params) (s : TorusLatticeSymmetry D.L D.m (D.K : ℕ)) :
    PullbackIsGaugeField D s :=
  fun U => ⟨(pullbackConfig s U).2, fun _ _ h => linkValue_pullbackConfig U h⟩
theorem pullbackMeasurePreserving_of_bijOn
    (h₃ : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement) (D : Params)
    (s : TorusLatticeSymmetry D.L D.m (D.K : ℕ)) {ε : Fin 4 → ℤˣ} {π : Fin 4 → Fin 4}
    (hL : 2 ≤ D.L) (hj : -((D.m : ℕ) : ℤ) < ((D.K : ℕ) : ℤ))
    (hBij : BijOn (bondPermutation s ε π) (forwardBonds D.L D.m (spacingIndex D))
      (forwardBonds D.L D.m (spacingIndex D)))
    (hval : ∀ (U : CompactGaugeField D.L D.m (spacingIndex D)) (b : Bond D.L D.m (spacingIndex D)),
      b ∈ forwardBonds D.L D.m (spacingIndex D) →
        (pullbackConfig s U).linkValue b =
          U.linkValue (bondPermutation s ε π b) ^ ((bondSign ε b : ℤˣ) : ℤ))
    (hfinP : Finite (PositivelyOrientedBond D.L D.m (spacingIndex D)))
    (hprod : GaugeFieldProduct.ProductStructure D.L D.m (spacingIndex D)) :
    PullbackMeasurePreserving D s := by
  obtain ⟨-, ⟨e, he⟩, hcpt, -, huniq, hhaar, -⟩ := hprod
  have := secondCountable_complexMatrix2
  have := secondCountable_specialUnitary
  obtain ⟨τ, hτ⟩ : ∃ τ : PositivelyOrientedBond D.L D.m (spacingIndex D) ≃
      PositivelyOrientedBond D.L D.m (spacingIndex D),
      ∀ b, (τ b).1 = bondPermutation s ε π b.1 := by
    let f : PositivelyOrientedBond D.L D.m (spacingIndex D) →
        PositivelyOrientedBond D.L D.m (spacingIndex D) := fun b =>
      ⟨bondPermutation s ε π b.1, PeriodicLattice.mem_positiveBonds_iff.mp
        (hBij.mapsTo (PeriodicLattice.mem_positiveBonds_iff.mpr b.2))⟩
    have hf : Bijective f := by
      constructor
      · intro a b h
        exact Subtype.ext (hBij.injOn (PeriodicLattice.mem_positiveBonds_iff.mpr a.2)
          (PeriodicLattice.mem_positiveBonds_iff.mpr b.2) (congrArg Subtype.val h))
      · intro y
        obtain ⟨x, hx, hxy⟩ :=
          hBij.surjOn (PeriodicLattice.mem_positiveBonds_iff.mpr y.2)
        exact ⟨⟨x, PeriodicLattice.mem_positiveBonds_iff.mp hx⟩, Subtype.ext hxy⟩
    exact ⟨Equiv.ofBijective f hf, fun b => rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : PositivelyOrientedBond D.L D.m (spacingIndex D) → ℤˣ,
      ∀ b, ε' b = bondSign ε b.1 :=
    ⟨fun b => bondSign ε b.1, fun _ => rfl⟩
  obtain ⟨hRhomeo, hRmap, -, -⟩ :=
    (h₃ ⟨D.toStandingParameters, D.β, D.β_pos, 0⟩).2.1 _ _ τ ε'
  have hcomm : ∀ U : CompactGaugeField D.L D.m (spacingIndex D),
      PeriodicLattice.restrictToPositiveBonds (pullbackConfig s U) =
        ReflectionPositivity.CutoffMirrors.relabelInvert τ ε'
          (PeriodicLattice.restrictToPositiveBonds U) := by
    intro U
    funext b
    have h := hval U b.1 (PeriodicLattice.mem_positiveBonds_iff.mpr b.2)
    rw [← hτ b, ← hε' b] at h
    exact h
  have hpull : pullbackConfig s =
      e.symm ∘ ReflectionPositivity.CutoffMirrors.relabelInvert τ ε' ∘ e := by
    funext U
    rw [comp_apply, comp_apply, he, ← hcomm, ← he]
    exact (e.symm_apply_apply _).symm
  have hhomeo : IsHomeomorph (pullbackConfig s) := by
    rw [hpull]
    exact e.symm.isHomeomorph.comp (hRhomeo.comp e.isHomeomorph)
  have hpm : Measurable (pullbackConfig s) := hhomeo.continuous.measurable
  have hvm : Measurable (PeriodicLattice.restrictToPositiveBonds :
      CompactGaugeField D.L D.m (spacingIndex D) → _) := he ▸ e.continuous.measurable
  have hRm := hRhomeo.continuous.measurable
  refine ⟨hhomeo, ?_, ?_⟩
  · exact preservesIntegrals_of_isProductHaarImage s _ hRm hRmap hpm hvm hcomm huniq hhaar
  · exact preservesIntegrals_of_isProductHaarImage s _ hRm hRmap hpm hvm hcomm huniq
      (isProductHaarImage_productHaarOnFields
        (fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b) hcpt e he)
end Assembly
theorem holds (h₁ : LatticeCovering.CoveringStatement) (h₂ : GaugeFieldProduct.Statement)
    (h₃ : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement) : Statement := by
  intro D r w hw v hv hr
  have hL : 2 ≤ D.L := by
    have := D.isAdmissible.2
    omega
  have hj : -((D.m : ℕ) : ℤ) < ((D.K : ℕ) : ℤ) := by
    have h₁ := D.m.pos
    have h₂ := D.K.pos
    omega
  obtain ⟨-, -, hIso, hOnto, -, hInv, hStep, -⟩ := (h₁ D).2.2.2.1 r
  refine ⟨existsUnique_isSignedPermutationData hw, ⟨⟨descend D r.1, hIso, hOnto⟩, rfl⟩, ?_⟩
  intro ε π hsign
  have hmove : ∀ (z : FourTorus D.L D.m) (k : Fin 4),
      descend D r.1 (translateByVector z (mesh D • basisVector k)) =
        translateByVector (descend D r.1 z)
          ((((ε k : ℤˣ) : ℤ) : ℝ) • mesh D • basisVector (π k)) := by
    intro z k
    rw [hStep w hw v hv hr z k, hsign k, smul_comm]
  refine ⟨bijective_of_isSignedPermutationData hw hsign,
    ⟨hmove, fun b => exists_bond_of_shiftsUnitSteps
      (shiftsUnitSteps_of_descend D r hmove ⟨descend D r.1, hIso, hOnto⟩ rfl) b, hInv⟩, ?_⟩
  intro s hs
  have hk := shiftsUnitSteps_of_descend D r hmove s hs
  have hinj : Injective s.toFun := by
    obtain ⟨t, -, -, -, hl, -⟩ := hInv
    rw [hs]
    exact hl.injective
  obtain ⟨-, ⟨-, ⟨hfinP, -⟩, -⟩, hprod, -⟩ :=
    h₂.1 D.L D.m (spacingIndex D) D.isAdmissible D.m.pos (by positivity)
  have hfin : Finite (forwardBonds D.L D.m (spacingIndex D)) :=
    Finite.of_injective
      (fun b : forwardBonds D.L D.m (spacingIndex D) =>
        (⟨b.1, PeriodicLattice.mem_positiveBonds_iff.mp b.2⟩ :
          PositivelyOrientedBond D.L D.m (spacingIndex D)))
      (fun a b h => Subtype.ext
        (congrArg (fun x : PositivelyOrientedBond D.L D.m (spacingIndex D) => x.1) h))
  have hBij := bijOn_bondPermutation hk hL hj hfin hinj
  have hval := fun U (b : Bond D.L D.m (spacingIndex D)) hb =>
    linkValue_pullbackConfig_of_mem hk hL hj U (b := b) hb
  exact ⟨pullbackIsGaugeField D s,
    ⟨fun z k => bondPermutation_forwardFrom_spec hk hL hj z k, hBij, hval⟩,
    pullbackMeasurePreserving_of_bijOn h₃ D s hL hj hBij hval hfinP hprod⟩
end InducedPullback
end YangMills.Construction
end
