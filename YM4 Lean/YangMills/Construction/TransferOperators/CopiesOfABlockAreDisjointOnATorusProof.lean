import YangMills.Construction.TransferOperators.CopiesOfABlockAreDisjointOnATorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.TransferOperators.BlockCopies
variable {μ : Fin 4}
theorem level_sub (x y : LatticePoint 1) :
    level μ (x - y) = level μ x - level μ y := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_sub, level_cast, level_cast, level_cast]
  rfl
theorem side_dvd_level (Γ : CubicPeriodSublattice) {γ : LatticePoint 1}
    (hγ : γ ∈ Γ.lattice.periods) : (Γ.side : ℤ) ∣ level μ γ := by
  rw [Γ.periods_eq] at hγ
  obtain ⟨k, hk⟩ := AddSubgroup.mem_addSubgroupOf.mp hγ
  refine ⟨k μ, ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [level_cast, hk μ]
  push_cast
  ring
theorem zsmul_axisStep_mem (Γ : CubicPeriodSublattice) {t : ℤ} (ht : (Γ.side : ℤ) ∣ t) :
    t • axisStep 1 μ ∈ Γ.lattice.periods := by
  obtain ⟨q, rfl⟩ := ht
  rw [Γ.periods_eq]
  refine AddSubgroup.mem_addSubgroupOf.mpr ⟨Pi.single μ q, fun ν => ?_⟩
  change (((Γ.side : ℤ) * q) • (Pi.single μ (1 : ℝ) : AmbientSpace)) ν =
    (((Pi.single μ q : Fin 4 → ℤ) ν : ℤ) : ℝ) * (Γ.side : ℝ)
  by_cases h : ν = μ
  · subst h
    simp
    ring
  · simp [Pi.single_eq_of_ne h]
theorem coe_slicePart (x : LatticePoint 1) :
    ((slicePart μ x : SliceSite μ) : LatticePoint 1) = x - level μ x • axisStep 1 μ := rfl
theorem slicePart_sub_mem (Γ : CubicPeriodSublattice) {v v' : LatticePoint 1}
    (h : v - v' ∈ Γ.lattice.periods) :
    ((slicePart μ v' : SliceSite μ) : LatticePoint 1) - slicePart μ v ∈ Γ.slicePeriods μ := by
  refine AddSubgroup.mem_inf.mpr ⟨?_, (sliceLattice μ).sub_mem (slicePart μ v').2 (slicePart μ v).2⟩
  have hd : (Γ.side : ℤ) ∣ level μ v - level μ v' := by
    rw [← level_sub]
    exact side_dvd_level Γ h
  have e : ((slicePart μ v' : SliceSite μ) : LatticePoint 1) - slicePart μ v =
      (level μ v - level μ v') • axisStep 1 μ - (v - v') := by
    rw [coe_slicePart, coe_slicePart, sub_smul]
    abel
  rw [e]
  exact sub_mem (zsmul_axisStep_mem Γ hd) h
theorem linkClass_translate_eq (Γ : CubicPeriodSublattice) (b : SliceLink μ) {z z' : SliceSite μ}
    (h : (z' : LatticePoint 1) - z ∈ Γ.slicePeriods μ) :
    Γ.linkClass (b.translate z) = Γ.linkClass (b.translate z') := by
  refine Subtype.ext (Γ.linkOrbit_eq_of_mem ?_).symm
  refine ⟨(z' : LatticePoint 1) - z, h, ?_⟩
  change CutoffLattice.translateLink b.1 z' =
    CutoffLattice.translateLink (CutoffLattice.translateLink b.1 z) ((z' : LatticePoint 1) - z)
  rw [CubicPeriodSublattice.translateLink_translateLink]
  congr 1
  abel
theorem eq_of_linkClass_eq {B : Block μ} {i : ℤ} {Q' : AddSubgroup (LatticePoint 1)}
    (hT : B.PairwiseDisjointShifts i Q') {Γ : CubicPeriodSublattice}
    (hQ : Γ.lattice.periods ≤ Q') {v v' : LatticePoint 1} (hv : v ∈ Q') (hv' : v' ∈ Q')
    {b b' : SliceLink μ} (hb : b ∈ B.links) (hb' : b' ∈ B.links)
    (ht : (Γ.side : ℤ) ∣ level μ v' - level μ v)
    (hc : Γ.linkClass (b.translate (slicePart μ v)) = Γ.linkClass (b'.translate (slicePart μ v'))) :
    ∃ γ ∈ Γ.slicePeriods μ,
      CutoffLattice.translateLink b'.1 (slicePart μ v') =
        CutoffLattice.translateLink (CutoffLattice.translateLink b.1 (slicePart μ v)) γ ∧
      v + γ + (level μ v' - level μ v) • axisStep 1 μ = v' := by
  have hmem : b'.translate (slicePart μ v') ∈ Γ.linkOrbit μ (b.translate (slicePart μ v)) := by
    have ho : Γ.linkOrbit μ (b.translate (slicePart μ v)) =
        Γ.linkOrbit μ (b'.translate (slicePart μ v')) := congrArg Subtype.val hc
    rw [ho]
    exact Γ.self_mem_linkOrbit _
  obtain ⟨γ, hγ, e⟩ := hmem
  have e' : CutoffLattice.translateLink b'.1 (slicePart μ v') =
      CutoffLattice.translateLink (CutoffLattice.translateLink b.1 (slicePart μ v)) γ := e
  refine ⟨γ, hγ, e', ?_⟩
  set w : LatticePoint 1 := v + γ + (level μ v' - level μ v) • axisStep 1 μ with hw
  have hwQ : w ∈ Q' :=
    add_mem (add_mem hv (hQ (AddSubgroup.mem_inf.mp hγ).1)) (hQ (zsmul_axisStep_mem Γ ht))
  have key : ∀ y y' : SliceSite μ,
      (y' : LatticePoint 1) + (slicePart μ v' : SliceSite μ) =
        (y : LatticePoint 1) + (slicePart μ v : SliceSite μ) + γ →
      pointAtLevel μ i y + w = pointAtLevel μ i y' + v' := by
    intro y y' h
    have h' : (y' : LatticePoint 1) = (y : LatticePoint 1) + (slicePart μ v : SliceSite μ) + γ -
        (slicePart μ v' : SliceSite μ) := eq_sub_of_add_eq h
    rw [coe_slicePart, coe_slicePart] at h'
    simp only [pointAtLevel]
    rw [h', hw, sub_smul]
    abel
  have hsame : CutoffLattice.translateLink (spatialLink μ i b).1 w =
      CutoffLattice.translateLink (spatialLink μ i b').1 v' :=
    Link.ext (key _ _ (congrArg Link.initial e')) (key _ _ (congrArg Link.terminal e'))
  by_contra hne
  have hd : Disjoint (shiftedLinks (Subtype.val '' B.atLevel i) w)
      (shiftedLinks (Subtype.val '' B.atLevel i) v') :=
    hT (i := ⟨w, hwQ⟩) (j := ⟨v', hv'⟩) (fun h => hne (congrArg Subtype.val h))
  have m₁ : CutoffLattice.translateLink (spatialLink μ i b).1 w ∈
      shiftedLinks (Subtype.val '' B.atLevel i) w :=
    ⟨(spatialLink μ i b).1, ⟨spatialLink μ i b, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
  have m₂ : CutoffLattice.translateLink (spatialLink μ i b).1 w ∈
      shiftedLinks (Subtype.val '' B.atLevel i) v' :=
    ⟨(spatialLink μ i b').1, ⟨spatialLink μ i b', ⟨b', hb', rfl⟩, rfl⟩, hsame.symm⟩
  exact Set.disjoint_left.mp hd m₁ m₂
theorem disjoint_holds : DisjointStatement := by
  intro μ B i Q' _ hT Γ hQ
  refine ⟨?_, ?_, ?_⟩
  · intro v _ v' _ h
    have e : Γ.blockCopy B v = Γ.blockCopy B v' :=
      funext fun b => linkClass_translate_eq Γ b.1 (slicePart_sub_mem Γ h)
    refine ⟨e, ?_, ?_⟩
    · change Set.range (Γ.blockCopy B v) = Set.range (Γ.blockCopy B v')
      rw [e]
    · have hd : (Γ.side : ℤ) ∣ level μ v - level μ v' := by
        rw [← level_sub]
        exact side_dvd_level Γ h
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
      rw [add_sub_add_left_eq_sub, ← neg_sub]
      exact (dvd_neg).mpr hd
  · intro v hv b b' h
    obtain ⟨γ, _, e, hw⟩ := eq_of_linkClass_eq hT hQ hv hv b.2 b'.2
      (by rw [sub_self]; exact dvd_zero _) h
    have hγ : γ = 0 := by
      rw [sub_self, zero_smul, add_zero] at hw
      exact add_eq_left.mp hw
    subst hγ
    refine Subtype.ext (Subtype.ext (Link.ext ?_ ?_))
    · have := congrArg Link.initial e
      exact (add_right_cancel (this.trans (add_zero _))).symm
    · have := congrArg Link.terminal e
      exact (add_right_cancel (this.trans (add_zero _))).symm
  · intro v hv v' hv' hn hl
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨b, rfl⟩ ⟨b', h⟩
    have hl' : (((i + level μ v : ℤ)) : ZMod Γ.side) = ((i + level μ v' : ℤ)) := hl
    have ht : (Γ.side : ℤ) ∣ level μ v' - level μ v := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hl'
      rwa [add_sub_add_left_eq_sub] at this
    obtain ⟨γ, hγ, _, hw⟩ := eq_of_linkClass_eq hT hQ hv hv' b.2 b'.2 ht h.symm
    have hm := add_mem (AddSubgroup.mem_inf.mp hγ).1 (zsmul_axisStep_mem (μ := μ) Γ ht)
    generalize (level μ v' - level μ v) • axisStep 1 μ = T at hw hm
    apply hn
    have e : v - v' = -(γ + T) := by
      rw [← hw]
      abel
    rw [e]
    exact neg_mem hm
end YangMills.Construction.TransferOperators.BlockCopies
end
