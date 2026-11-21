import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.RunningCouplingSlope.ChangeOfGaugeInAGaussianNumberProof
import YangMills.Construction.RunningCouplingSlope.FieldsAtALeastPointAreSmall
import YangMills.Construction.RunningCouplingSlope.LevelMapOfAChainProof
import YangMills.Construction.RunningCouplingSlope.RelationsOfTheChainAtARealPoint
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames Matrices
namespace TreeSlice
section Line
variable {E : Type*} [AddCommGroup E]
private def partialLineSum (f : ℤ → E) (a : ℤ) : E :=
  if 0 ≤ a then ∑ s ∈ Finset.range a.toNat, f s
  else - ∑ s ∈ Finset.range (-a).toNat, f (-(s : ℤ) - 1)
private theorem partialLineSum_zero (f : ℤ → E) : partialLineSum f 0 = 0 := by
  simp [partialLineSum]
private theorem partialLineSum_succ (f : ℤ → E) (a : ℤ) :
    partialLineSum f (a + 1) - partialLineSum f a = f a := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have e1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    have e2 : ((m : ℤ) + 1).toNat = m + 1 := by omega
    have e3 : ((m : ℤ)).toNat = m := by omega
    simp only [partialLineSum, if_pos e1, if_pos h, e2, e3, Finset.sum_range_succ]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = -((m : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
    have e2 : (-(-((m : ℤ) + 1))).toNat = m + 1 := by omega
    have e4 : ¬ (0 ≤ -((m : ℤ) + 1)) := by omega
    have e5 : -(m : ℤ) - 1 = -((m : ℤ) + 1) := by ring
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [partialLineSum]
    · have e1 : ¬ (0 ≤ -((m : ℤ) + 1) + 1) := by omega
      have e3 : (-(-((m : ℤ) + 1) + 1)).toNat = m := by omega
      simp only [partialLineSum, if_neg e1, if_neg e4, e2, e3, Finset.sum_range_succ, e5]
      abel
end Line
section Tree
open ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame} {E : Type*} [AddCommGroup E]
private def axisBondPath (l : Fin 4) (u : Fin 4 → ℤ) (s : ℤ) : Fin 4 → ℤ :=
  fun m => if m < l then u m else if m = l then s else 0
private def treeIntegral (c : F.Cell → E) (ζ : F.Site F.depth × Fin 4 → E) (z : F.Cell) (u : Fin 4 → ℤ) : E :=
  c z + ∑ l : Fin 4, partialLineSum
    (fun s => ζ (cellCentre F.depth z + siteOfCoords F.depth (axisBondPath l u s), l)) (u l)
private theorem treeIntegral_zero (c : F.Cell → E) (ζ : F.Site F.depth × Fin 4 → E) (z : F.Cell) :
    treeIntegral c ζ z 0 = c z := by
  simp [treeIntegral, partialLineSum_zero]
private theorem treeIntegral_step (c : F.Cell → E) (ζ : F.Site F.depth × Fin 4 → E) (z : F.Cell)
    (u : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → u l = 0) :
    treeIntegral c ζ z (u + Pi.single i 1) - treeIntegral c ζ z u =
      ζ (cellCentre F.depth z + siteOfCoords F.depth u, i) := by
  have key : ∀ l : Fin 4,
      partialLineSum (fun s => ζ (cellCentre F.depth z +
          siteOfCoords F.depth (axisBondPath l (u + Pi.single i 1) s), l))
          ((u + Pi.single i 1 : Fin 4 → ℤ) l) -
        partialLineSum (fun s => ζ (cellCentre F.depth z + siteOfCoords F.depth (axisBondPath l u s), l)) (u l) =
      if l = i then ζ (cellCentre F.depth z + siteOfCoords F.depth u, i) else 0 := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · have e1 : (u + Pi.single i 1 : Fin 4 → ℤ) l = u l := by simp [Pi.single_eq_of_ne h.ne]
      have e2 : ∀ s, axisBondPath l (u + Pi.single i 1) s = axisBondPath l u s := by
        intro s
        funext m
        unfold axisBondPath
        by_cases hm : m < l
        · have : m ≠ i := (hm.trans h).ne
          simp [hm, Pi.single_eq_of_ne this]
        · simp [hm]
      simp only [e1, e2, sub_self, if_neg h.ne]
    · subst h
      have e1 : (u + Pi.single l 1 : Fin 4 → ℤ) l = u l + 1 := by simp
      have e2 : ∀ s, axisBondPath l (u + Pi.single l 1) s = axisBondPath l u s := by
        intro s
        funext m
        unfold axisBondPath
        by_cases hm : m < l
        · simp [hm, Pi.single_eq_of_ne hm.ne]
        · simp [hm]
      have e3 : axisBondPath l u (u l) = u := by
        funext m
        unfold axisBondPath
        rcases lt_trichotomy m l with hm | hm | hm
        · simp [hm]
        · simp [hm]
        · simp [not_lt.mpr hm.le, hm.ne', hz m hm]
      simp only [e1, e2, if_true]
      rw [partialLineSum_succ, e3]
    · have e1 : (u + Pi.single i 1 : Fin 4 → ℤ) l = 0 := by simp [Pi.single_eq_of_ne h.ne', hz l h]
      simp only [e1, hz l h, partialLineSum_zero, sub_self, if_neg h.ne']
  unfold treeIntegral
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun l _ => key l]
  simp
private theorem exists_of_treeDifferences (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (c : F.Cell → E) (ζ : F.Site F.depth × Fin 4 → E) :
    ∃ g : F.Site F.depth → E, (∀ z, g (cellCentre F.depth z) = c z) ∧
      ∀ b, IsAxialTreeBond b → g (b.1 + unitStep F.depth b.2) - g b.1 = ζ b := by
  obtain ⟨h1, h2, h3, -⟩ := hS F hL hs
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
    intro i
    have : 0 ≤ halfSide F.blockSide := by
      obtain ⟨m, hm⟩ := hL
      unfold halfSide
      rw [hm]
      push_cast
      omega
    simp only [Pi.zero_apply]
    omega
  have hcen : ∀ z : F.Cell, cellCentre F.depth z + siteOfCoords F.depth 0 =
      (cellCentre F.depth z : F.Site F.depth) := by
    intro z
    funext l
    simp [siteOfCoords]
  refine ⟨fun x => treeIntegral c ζ (enclosingCell x) (cellOffset x), fun z => ?_, fun b hb => ?_⟩
  · have := h1 z 0 h0
    rw [hcen] at this
    simp only [this.1, this.2, treeIntegral_zero]
  · obtain ⟨x, i⟩ := b
    obtain ⟨e, hu⟩ := h2 x
    set z := enclosingCell x with hzdef
    set u := cellOffset x with hudef
    have hne : u i ≠ halfSide F.blockSide := fun h => hb.1 ((h3 x i).mpr h)
    have hc := (YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff u).mp hu
    have hu' : u + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hc l
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · have := hc l
        simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact this
    have hx1 : x + unitStep F.depth i = cellCentre F.depth z + siteOfCoords F.depth (u + Pi.single i 1) := by
      rw [← offset_add_unitStep z u i, e]
    have := h1 z _ hu'
    show treeIntegral c ζ (enclosingCell (x + unitStep F.depth i)) (cellOffset (x + unitStep F.depth i)) -
      treeIntegral c ζ (enclosingCell x) (cellOffset x) = ζ (x, i)
    rw [hx1, this.1, this.2, treeIntegral_step c ζ z u i (fun l hl => hb.2 l hl), e]
private theorem eq_cellCentre_of_treeConst (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {A : Type*} (g : F.Site F.depth → A)
    (hg : ∀ b, IsAxialTreeBond b → g (b.1 + unitStep F.depth b.2) = g b.1)
    (x : F.Site F.depth) : g x = g (cellCentre F.depth (enclosingCell x)) := by
  obtain ⟨h1, h2, h3, -⟩ := hS F hL hs
  set z := enclosingCell x with hzdef
  have hcen : cellCentre F.depth z + siteOfCoords F.depth 0 = (cellCentre F.depth z : F.Site F.depth) := by
    funext l
    simp [siteOfCoords]
  have tree : ∀ v ∈ centredCube F.blockSide, ∀ i : Fin 4, v i ≠ halfSide F.blockSide →
      (∀ l, i < l → v l = 0) →
      g (cellCentre F.depth z + siteOfCoords F.depth (v + Pi.single i 1)) =
        g (cellCentre F.depth z + siteOfCoords F.depth v) := by
    intro v hv i hne hz
    have ho := (h1 z v hv).2
    have := hg (cellCentre F.depth z + siteOfCoords F.depth v, i)
      ⟨fun h => hne (by rw [← ho]; exact (h3 _ i).mp h), fun l hl => by simp only [ho]; exact hz l hl⟩
    rw [← offset_add_unitStep z v i]
    exact this
  have line : ∀ (i : Fin 4) (P : ∀ v ∈ centredCube F.blockSide, v i = 0 → (∀ l, i < l → v l = 0) →
      g (cellCentre F.depth z + siteOfCoords F.depth v) = g (cellCentre F.depth z)) (N : ℕ)
      (u : Fin 4 → ℤ), (u i).natAbs = N →
      u ∈ centredCube F.blockSide → (∀ l, i < l → u l = 0) →
      g (cellCentre F.depth z + siteOfCoords F.depth u) = g (cellCentre F.depth z) := by
    intro i P N
    induction N with
    | zero =>
      intro u hn hu hz
      exact P u hu (by omega) hz
    | succ N ih =>
      intro u hn hu hz
      have hc := (YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff u).mp hu
      rcases lt_or_ge 0 (u i) with hp | hneg
      · set v : Fin 4 → ℤ := u - Pi.single i 1 with hv
        have hvi : v i = u i - 1 := by simp [hv]
        have hvl : ∀ l, l ≠ i → v l = u l := fun l hl => by simp [hv, Pi.single_eq_of_ne hl]
        have hvc : v ∈ centredCube F.blockSide := by
          rw [YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            rw [hvi]
            omega
          · rw [hvl l hl]
            exact hc l
        have hvz : ∀ l, i < l → v l = 0 := fun l hl => by rw [hvl l hl.ne']; exact hz l hl
        have hne : v i ≠ halfSide F.blockSide := by
          have := hc i
          omega
        have e : v + Pi.single i 1 = u := by simp [hv]
        have := tree v hvc i hne hvz
        rw [e] at this
        rw [this]
        exact ih v (by omega) hvc hvz
      · have hlt : u i < 0 := by omega
        set v : Fin 4 → ℤ := u + Pi.single i 1 with hv
        have hvi : v i = u i + 1 := by simp [hv]
        have hvl : ∀ l, l ≠ i → v l = u l := fun l hl => by simp [hv, Pi.single_eq_of_ne hl]
        have hvc : v ∈ centredCube F.blockSide := by
          rw [YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hc l
            have h0 : 0 ≤ halfSide F.blockSide := by omega
            rw [hvi]
            omega
          · rw [hvl l hl]
            exact hc l
        have hvz : ∀ l, i < l → v l = 0 := fun l hl => by rw [hvl l hl.ne']; exact hz l hl
        have hne : u i ≠ halfSide F.blockSide := by
          have := hc i
          omega
        rw [← tree u hu i hne hz]
        exact ih v (by omega) hvc hvz
  have stage : ∀ (m : ℕ) (u : Fin 4 → ℤ), u ∈ centredCube F.blockSide →
      (∀ l : Fin 4, m ≤ l.val → u l = 0) →
      g (cellCentre F.depth z + siteOfCoords F.depth u) = g (cellCentre F.depth z) := by
    intro m
    induction m with
    | zero =>
      intro u hu hz
      have : u = 0 := funext fun l => hz l (Nat.zero_le _)
      rw [this, hcen]
    | succ m ih =>
      intro u hu hz
      by_cases hm : m < 4
      · refine line ⟨m, hm⟩ (fun v hv h0 hz' => ih v hv fun l hl => ?_) _ u rfl hu
          fun l hl => hz l hl
        rcases Nat.eq_or_lt_of_le hl with e | e
        · have : l = ⟨m, hm⟩ := Fin.ext e.symm
          rw [this]
          exact h0
        · exact hz' l e
      · exact ih u hu fun l hl => absurd (l.isLt) (by omega)
  have hx := (h2 x).1
  have := stage 4 (cellOffset x) (h2 x).2 fun l hl => absurd l.isLt (by omega)
  rw [hx] at this
  exact this
end Tree
section Coordinates
variable {L n K : ℕ}
private def coordSite (d : ℤ) (z : Fin 4 → ℤ) : PeriodicLattice.Site L n d :=
  PeriodicLattice.offsetSite 0 z
private theorem coe_coordSite (d : ℤ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L d) := by
    show (PeriodicLattice.sublattice L n d).subtype (coordSite d z) = _
    simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem coordSite_eq_iff {d : ℤ} {P : ℕ} (hs : PeriodicLattice.meshSize L d ≠ 0)
    (hP : (P : ℝ) * PeriodicLattice.meshSize L d = PeriodicLattice.torusSide L n) (z z' : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) d z = coordSite d z' ↔ ∀ ν, ∃ m : ℤ, z ν - z' ν = m * P := by
  have one : ∀ a b : ℤ, ((((a : ℝ) * PeriodicLattice.meshSize L d : ℝ) :
      AddCircle (PeriodicLattice.torusSide L n)) =
      (((b : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) ↔
      ∃ m : ℤ, a - b = m * P := by
    intro a b
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul] at hm
      have := mul_right_cancel₀ hs hm
      exact_mod_cast this.symm
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul]
      congr 1
      exact_mod_cast hm.symm
  constructor
  · intro h ν
    have := congrFun (congrArg (fun x : PeriodicLattice.Site L n d => (x : PeriodicLattice.FourTorus L n)) h) ν
    simp only [coe_coordSite] at this
    exact (one _ _).mp this
  · intro h
    refine Subtype.ext (funext fun ν => ?_)
    rw [coe_coordSite, coe_coordSite]
    exact (one _ _).mpr (h ν)
private theorem exists_coordSite (d : ℤ) (x : PeriodicLattice.Site L n d) :
    ∃ z : Fin 4 → ℤ, x = coordSite d z := by
  obtain ⟨z, hz⟩ := x.2
  refine ⟨z, Subtype.ext (funext fun ν => ?_)⟩
  rw [coe_coordSite, hz ν]
private theorem unitStep_eq_coordSite (d : ℤ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n d μ = coordSite d (Pi.single μ 1) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_coordSite]
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem coordSite_add (d : ℤ) (z z' : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) d z + coordSite d z' = coordSite d (z + z') := by
  simp only [coordSite, PeriodicLattice.offsetSite, zero_add, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]
private theorem meshSize_and_period (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth K j) ≠ 0 ∧
      ((2 * L ^ (n + (K - j)) : ℕ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth K j) =
        PeriodicLattice.torusSide L n := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  refine ⟨by unfold PeriodicLattice.meshSize; exact zpow_ne_zero _ hLr, ?_⟩
  have e : PeriodicLattice.levelDepth K j = ((K - j : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth, Nat.cast_sub hj]
  simp only [PeriodicLattice.meshSize, PeriodicLattice.torusSide, e]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
private def liftSite (j : ℕ) {F : BlockFrame} {l : ℕ} (x : F.Site l) : Vertex L n K j :=
  coordSite (PeriodicLattice.levelDepth K j) (siteCoords x)
private theorem coordSite_cast (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) {z z' : Fin 4 → ℤ}
    (h : ∀ ν, ((z ν : ℤ) : ZMod (F.period l ν)) = (z' ν : ℤ)) :
    coordSite (L := L) (n := n) (PeriodicLattice.levelDepth K j) z =
      coordSite (PeriodicLattice.levelDepth K j) z' := by
  obtain ⟨hs, hP⟩ := meshSize_and_period (n := n) hL0 hj
  rw [coordSite_eq_iff hs hP]
  intro ν
  have h1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (h ν)
  obtain ⟨m, hm⟩ := h1
  rw [hper ν] at hm
  exact ⟨-m, by rw [neg_mul, mul_comm m, ← hm]; ring⟩
private theorem siteCoords_cast {F : BlockFrame} {l : ℕ} (x : F.Site l) (ν : Fin 4) :
    ((siteCoords x ν : ℤ) : ZMod (F.period l ν)) = x ν := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
private theorem liftSite_siteOfCoords (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) (z : Fin 4 → ℤ) :
    (liftSite (L := L) (n := n) (K := K) j (siteOfCoords l z : F.Site l)) =
      coordSite (PeriodicLattice.levelDepth K j) z :=
  coordSite_cast hL0 hj hper fun ν => siteCoords_cast _ ν
private theorem liftSite_add (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) (x : F.Site l) (i : Fin 4) :
    liftSite (L := L) (n := n) (K := K) j (x + unitStep l i) =
      liftSite j x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth K j) i := by
  rw [unitStep_eq_coordSite]
  unfold liftSite
  rw [coordSite_add]
  refine coordSite_cast hL0 hj hper fun ν => ?_
  rw [siteCoords_cast]
  simp only [Pi.add_apply, Int.cast_add, siteCoords_cast, unitStep, siteOfCoords]
private theorem liftSite_injective (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) :
    Function.Injective (liftSite (L := L) (n := n) (K := K) j : F.Site l → Vertex L n K j) := by
  intro x x' h
  obtain ⟨hs, hP⟩ := meshSize_and_period (n := n) hL0 hj
  have h1 := (coordSite_eq_iff hs hP _ _).mp h
  funext ν
  obtain ⟨m, hm⟩ := h1 ν
  rw [← siteCoords_cast x ν, ← siteCoords_cast x' ν, ZMod.intCast_eq_intCast_iff_dvd_sub, hper ν]
  exact ⟨-m, by
    have : siteCoords x' ν - siteCoords x ν = -(siteCoords x ν - siteCoords x' ν) := by ring
    rw [this, hm]
    ring⟩
private theorem liftSite_surjective (hL0 : 0 < L) {j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) :
    Function.Surjective (liftSite (L := L) (n := n) (K := K) j : F.Site l → Vertex L n K j) := by
  intro y
  obtain ⟨z, rfl⟩ := exists_coordSite _ y
  exact ⟨siteOfCoords l z, liftSite_siteOfCoords hL0 hj hper z⟩
private theorem coe_toSublattice (hL0 : 0 < L) {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L n i) :
    ((y.toSublattice i' : PeriodicLattice.Site L n i') : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem restrictVertexFunction_self (hL0 : 0 < L) {j : ℕ} (v : Vertex L n K j → ComplexMatrix2) :
    restrictVertexFunction j v = v := by
  funext x
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  exact Subtype.ext (coe_toSublattice hL0 le_rfl x)
private theorem restrictVertexFunction_trans (hL0 : 0 < L) {i m j : ℕ} (hmi : m ≤ i) (hjm : j ≤ m)
    (v : Vertex L n K j → ComplexMatrix2) :
    restrictVertexFunction i (restrictVertexFunction m v) = restrictVertexFunction i v := by
  funext y
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  refine Subtype.ext ?_
  have h1 : PeriodicLattice.levelDepth K i ≤ PeriodicLattice.levelDepth K m := by
    simp only [PeriodicLattice.levelDepth]; omega
  have h2 : PeriodicLattice.levelDepth K m ≤ PeriodicLattice.levelDepth K j := by
    simp only [PeriodicLattice.levelDepth]; omega
  rw [coe_toSublattice hL0 h2, coe_toSublattice hL0 h1, coe_toSublattice hL0 (h1.trans h2)]
private theorem coordSite_toSublattice (hL0 : 0 < L) (j : ℕ) (w : Fin 4 → ℤ) :
    ((coordSite (L := L) (n := n) (PeriodicLattice.levelDepth K (j + 1)) w).toSublattice
        (PeriodicLattice.levelDepth K j)) =
      coordSite (PeriodicLattice.levelDepth K j) fun ν => (L : ℤ) * w ν := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  have h1 : PeriodicLattice.levelDepth K (j + 1) ≤ PeriodicLattice.levelDepth K j := by
    simp only [PeriodicLattice.levelDepth]; push_cast; omega
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_toSublattice hL0 h1, coe_coordSite, coe_coordSite]
  congr 1
  have e : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth K (j + 1)) =
      (L : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth K j) := by
    simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
    rw [show -((K : ℤ) - ((j + 1 : ℕ) : ℤ)) = 1 + -((K : ℤ) - (j : ℤ)) by push_cast; ring,
      zpow_add₀ hLr, zpow_one]
  rw [e]
  push_cast
  ring
end Coordinates
section Frames
variable {L n K : ℕ}
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N, torusSideBelow L s N = N * L ^ s
  | 0, N => by simp [torusSideBelow]
  | s + 1, N => by
    rw [torusSideBelow, torusSideBelow_eq L s]
    ring
private theorem frameAtStep_numbers (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < K) :
    Odd (frameAtStep L n K j).blockSide ∧ (∀ i, 2 ≤ (frameAtStep L n K j).extent i) ∧
      (∀ ν, (frameAtStep L n K j).period (frameAtStep L n K j).depth ν = 2 * L ^ (n + (K - j))) ∧
      (∀ ν, (frameAtStep L n K j).period (frameAtStep L n K j).top ν = 2 * L ^ (n + (K - (j + 1)))) ∧
      (frameAtStep L n K j).blockSide = L := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hside : ∀ i, (frameAtStep L n K j).extent i = 2 * L ^ (n + (K - (j + 1))) := by
    intro i
    show sideAtStep L n K j = _
    unfold sideAtStep
    rw [torusSideBelow_eq, pow_add]
    ring
  have hFL : (frameAtStep L n K j).blockSide = L := rfl
  refine ⟨hL.1, fun i => ?_, fun ν => ?_, fun ν => ?_, hFL⟩
  · rw [hside]
    have : 0 < L ^ (n + (K - (j + 1))) := pow_pos hL0 _
    omega
  · rw [BlockOffsets.period_depth, hside, hFL]
    have e : n + (K - j) = n + (K - (j + 1)) + 1 := by omega
    rw [e, pow_succ]
    ring
  · rw [BlockOffsets.period_top, hside]
private theorem mem_treeEdges (hS : SiteDecomposition) {F : BlockFrame} (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {b : F.Site F.depth × Fin 4} (hb : IsAxialTreeBond b) : b ∈ treeEdges F := by
  classical
  obtain ⟨-, h2, -, -⟩ := hS F hL hs
  have all : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := by
    intro x
    unfold sitesOfCells
    refine Finset.mem_biUnion.mpr ⟨enclosingCell x, BlockOffsets.mem_finiteCells hs _, ?_⟩
    refine Finset.mem_image.mpr ⟨cellOffset x, ?_, (h2 x).1⟩
    rw [BlockOffsets.top_sub_depth, pow_one]
    exact (h2 x).2
  unfold treeEdges innerBonds
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨all _, Finset.mem_univ _⟩, all _⟩, hb⟩
private def treeDiff {m : ℕ} (j : ℕ) {F : BlockFrame} {l : ℕ} (b : F.Site l × Fin 4)
    (v : Vertex L n K m → ComplexMatrix2) : ComplexMatrix2 :=
  restrictVertexFunction j v (edgeOfCoords (L := L) (n := n) (k := K) j b).target -
    restrictVertexFunction j v (edgeOfCoords (L := L) (n := n) (k := K) j b).source
private theorem treeDiff_eq (hL0 : 0 < L) {m j : ℕ} (hj : j ≤ K) {F : BlockFrame} {l : ℕ}
    (hper : ∀ ν, F.period l ν = 2 * L ^ (n + (K - j))) (b : F.Site l × Fin 4)
    (v : Vertex L n K m → ComplexMatrix2) :
    treeDiff (L := L) (n := n) (K := K) j b v =
      restrictVertexFunction j v (liftSite j (b.1 + unitStep l b.2)) -
        restrictVertexFunction j v (liftSite j b.1) := by
  rw [liftSite_add hL0 hj hper]
  rfl
end Frames
section Algebra
private def ofComponents (b : Fin 3 → ℝ) : ComplexMatrix2 :=
  !![(b 0 : ℂ), (b 2 : ℂ) - Complex.I * (b 1 : ℂ); (b 2 : ℂ) + Complex.I * (b 1 : ℂ), -(b 0 : ℂ)]
private theorem ofComponents_mem (b : Fin 3 → ℝ) : ofComponents b ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ofComponents, Matrix.conjTranspose_apply, Complex.conj_ofReal]
    ring
  · simp [ofComponents, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
private theorem suTwoComponents_ofComponents (b : Fin 3 → ℝ) : suTwoComponents (ofComponents b) = b := by
  funext c
  fin_cases c <;> simp [suTwoComponents, ofComponents]
private theorem eq_zero_of_suTwoComponents {D : ComplexMatrix2} (hD : D ∈ ComplexMatrix2.hermitianTraceless)
    (h : suTwoComponents D = 0) : D = 0 := by
  obtain ⟨h1, h2⟩ := hD
  have c0 := congrFun h 0
  have c1 := congrFun h 1
  have c2 := congrFun h 2
  simp only [suTwoComponents, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.zero_apply] at c0 c1 c2
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp only [Matrix.conjTranspose_apply] at e00 e10
  have t : D 0 0 + D 1 1 = 0 := by simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h2
  have d00 : D 0 0 = 0 := by
    apply Complex.ext
    · simpa using c0
    · have := congrArg Complex.im e00
      simp at this
      simpa using (by linarith : (D 0 0).im = 0)
  have d01 : D 0 1 = 0 := by
    apply Complex.ext
    · simpa using c2
    · simpa using (by linarith : (D 0 1).im = 0)
  have d10 : D 1 0 = 0 := by
    rw [e10, d01]
    simp
  have d11 : D 1 1 = 0 := by
    rw [d00, zero_add] at t
    exact t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d00, d01, d10, d11]
private theorem suTwoComponents_add (A B : ComplexMatrix2) :
    suTwoComponents (A + B) = suTwoComponents A + suTwoComponents B := by apply _root_.YangMills.SharedProofs.p37688 <;> assumption
private theorem suTwoComponents_smul (r : ℝ) (A : ComplexMatrix2) :
    suTwoComponents (r • A) = r • suTwoComponents A := by apply _root_.YangMills.SharedProofs.p5119 <;> assumption
end Algebra
section Slice
variable {L n K : ℕ}
private theorem descending_induction {P : ℕ → Prop} (hK : P K) (step : ∀ j, j < K → P (j + 1) → P j) :
    ∀ j, j ≤ K → P j := by
  have key : ∀ s j, j + s = K → P j := by
    intro s
    induction s with
    | zero =>
      intro j h
      have : j = K := by omega
      rw [this]
      exact hK
    | succ s ih =>
      intro j h
      exact step j (by omega) (ih (j + 1) (by omega))
  intro j hj
  exact key (K - j) j (by omega)
private theorem restrict_cellCentre (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m j : ℕ} (hmj : m ≤ j)
    (hj : j < K) (v : Vertex L n K m → ComplexMatrix2) (z : (frameAtStep L n K j).Cell) :
    restrictVertexFunction j v (liftSite j (cellCentre (frameAtStep L n K j).depth z)) =
      restrictVertexFunction (j + 1) v (liftSite (j + 1) z) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, -, hpt, hpn, hFL⟩ := frameAtStep_numbers (n := n) hL hn hj
  have e1 : (liftSite (L := L) (n := n) (K := K) j (cellCentre (frameAtStep L n K j).depth z)) =
      (liftSite (L := L) (n := n) (K := K) (j + 1) z).toSublattice (PeriodicLattice.levelDepth K j) := by
    unfold liftSite
    rw [coordSite_toSublattice hL0]
    have := liftSite_siteOfCoords (L := L) (n := n) (K := K) hL0 hj.le hpt
      (fun ν => (L : ℤ) * siteCoords z ν)
    unfold liftSite at this
    rw [← this]
    congr 2
    unfold cellCentre
    rw [BlockOffsets.top_sub_depth, hFL, pow_one]
  rw [e1]
  have h := congrFun (restrictVertexFunction_trans (L := L) (n := n) (K := K) hL0 (Nat.le_succ j) hmj v)
    (liftSite (j + 1) z)
  rw [← h]
  rfl
private theorem eq_zero_of_treeDiff (hS : SiteDecomposition) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (v : Vertex L n K 0 → ComplexMatrix2) (hv : ∀ x, v x ∈ ComplexMatrix2.hermitianTraceless)
    (htop : ∀ y, restrictVertexFunction K v y = 0)
    (hd : ∀ (j : Fin K) (b : ↥(treeEdges (frameAtStep L n K j))),
      suTwoComponents (treeDiff (L := L) (n := n) (K := K) j b.1 v) = 0) : v = 0 := by
  have hL0 : 0 < L := by have := hL.2; omega
  have key : ∀ j, j ≤ K → ∀ y : Vertex L n K j, restrictVertexFunction j v y = 0 := by
    refine descending_induction htop fun j hj ih y => ?_
    obtain ⟨hodd, hs, hpt, hpn, hFL⟩ := frameAtStep_numbers (n := n) hL hn hj
    have hmem : ∀ y, restrictVertexFunction j v y ∈ ComplexMatrix2.hermitianTraceless := fun y => hv _
    have hconst : ∀ b, IsAxialTreeBond b →
        restrictVertexFunction j v (liftSite (L := L) (n := n) (K := K) j
          (b.1 + unitStep (frameAtStep L n K j).depth b.2)) =
          restrictVertexFunction j v (liftSite j b.1) := by
      intro b hb
      have h : suTwoComponents (treeDiff (L := L) (n := n) (K := K) j b v) = 0 :=
        hd ⟨j, hj⟩ ⟨b, mem_treeEdges hS hodd hs hb⟩
      rw [treeDiff_eq hL0 hj.le hpt] at h
      exact sub_eq_zero.mp (eq_zero_of_suTwoComponents
        (ComplexMatrix2.hermitianTraceless.sub_mem (hmem _) (hmem _)) h)
    obtain ⟨x, rfl⟩ := liftSite_surjective (n := n) hL0 hj.le hpt y
    have := eq_cellCentre_of_treeConst hS hodd hs
      (fun x => restrictVertexFunction j v (liftSite (L := L) (n := n) (K := K) j x)) hconst x
    refine this.trans ?_
    rw [restrict_cellCentre hL hn (Nat.zero_le j) hj]
    exact ih _
  funext x
  have := key 0 (Nat.zero_le _) x
  rwa [restrictVertexFunction_self hL0] at this
private theorem exists_of_treeDiff (hS : SiteDecomposition) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (y : (j : Fin K) → ↥(treeEdges (frameAtStep L n K j)) → Fin 3 → ℝ) :
    ∃ v : Vertex L n K 0 → ComplexMatrix2, (∀ x, v x ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ w, restrictVertexFunction K v w = 0) ∧
      ∀ (j : Fin K) (b : ↥(treeEdges (frameAtStep L n K j))),
        suTwoComponents (treeDiff (L := L) (n := n) (K := K) j b.1 v) = y j b := by
  classical
  have hL0 : 0 < L := by have := hL.2; omega
  have key : ∀ m, m ≤ K → ∃ g : Vertex L n K m → ComplexMatrix2,
      (∀ x, g x ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ w, restrictVertexFunction K g w = 0) ∧ ∀ (j : Fin K), m ≤ j →
        ∀ b : ↥(treeEdges (frameAtStep L n K j)),
        suTwoComponents (treeDiff (L := L) (n := n) (K := K) j b.1 g) = y j b := by
    refine descending_induction ⟨0, fun _ => ComplexMatrix2.hermitianTraceless.zero_mem,
      fun w => ?_, fun j hj => ?_⟩ ?_
    · simp [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
    · have := j.isLt
      omega
    intro j hj ⟨g, hg, htop, htree⟩
    obtain ⟨hodd, hs, hpt, hpn, hFL⟩ := frameAtStep_numbers (n := n) hL hn hj
    set F := frameAtStep L n K j with hF
    let c : F.Cell → ↥ComplexMatrix2.hermitianTraceless := fun z => ⟨g (liftSite j.succ z), hg _⟩
    let ζ : F.Site F.depth × Fin 4 → ↥ComplexMatrix2.hermitianTraceless := fun b =>
      if h : b ∈ treeEdges F then ⟨ofComponents (y ⟨j, hj⟩ ⟨b, h⟩), ofComponents_mem _⟩ else 0
    obtain ⟨f, hc, hζ⟩ := exists_of_treeDifferences hS hodd hs c ζ
    have hinj := liftSite_injective (n := n) (K := K) hL0 hj.le hpt
    have hsurj := liftSite_surjective (n := n) (K := K) hL0 hj.le hpt
    let g' : Vertex L n K j → ComplexMatrix2 := fun w => (f (Function.surjInv hsurj w) : ComplexMatrix2)
    have hg' : ∀ x, g' (liftSite j x) = (f x : ComplexMatrix2) := fun x => by
      show ((f (Function.surjInv hsurj (liftSite j x)) : ↥ComplexMatrix2.hermitianTraceless) :
        ComplexMatrix2) = _
      rw [Function.leftInverse_surjInv ⟨hinj, hsurj⟩ x]
    have hr : restrictVertexFunction (j + 1) g' = g := by
      funext w
      obtain ⟨z, rfl⟩ := liftSite_surjective (n := n) (K := K) hL0 hj hpn w
      have h := restrict_cellCentre (L := L) (n := n) (K := K) hL hn le_rfl hj g' z
      rw [restrictVertexFunction_self hL0, hg', hc] at h
      exact h.symm
    refine ⟨g', fun w => (f _).2, fun w => ?_, fun i hi b => ?_⟩
    · rw [← restrictVertexFunction_trans hL0 (show j + 1 ≤ K from hj) (Nat.le_succ j), hr]
      exact htop w
    · rcases Nat.eq_or_lt_of_le hi with e | e
      · obtain ⟨i, hi'⟩ := i
        simp only at e
        subst e
        rw [treeDiff_eq hL0 hj.le hpt, restrictVertexFunction_self hL0, hg', hg']
        have h := hζ b.1 (Finset.mem_filter.mp b.2).2
        have h2 := congrArg Subtype.val h
        simp only [AddSubgroupClass.coe_sub] at h2
        rw [h2]
        have hz : ζ b.1 = ⟨ofComponents (y ⟨j, hj⟩ ⟨b.1, b.2⟩), ofComponents_mem _⟩ := dif_pos b.2
        show suTwoComponents ((ζ b.1 : ↥ComplexMatrix2.hermitianTraceless) : ComplexMatrix2) = _
        rw [hz]
        exact suTwoComponents_ofComponents _
      · have e2 : restrictVertexFunction (i : ℕ) g' = restrictVertexFunction i g := by
          rw [← hr, restrictVertexFunction_trans hL0 e (Nat.le_succ j)]
        have := htree i e b
        unfold treeDiff at this ⊢
        rw [e2]
        exact this
  obtain ⟨g, h1, h2, h3⟩ := key 0 (Nat.zero_le _)
  exact ⟨g, h1, h2, fun j b => h3 j (Nat.zero_le _) b⟩
private theorem treeDiff_add {j : ℕ} {F : BlockFrame} {l : ℕ} (b : F.Site l × Fin 4)
    (v w : Vertex L n K 0 → ComplexMatrix2) :
    treeDiff (L := L) (n := n) (K := K) j b (v + w) =
      treeDiff (L := L) (n := n) (K := K) j b v + treeDiff (L := L) (n := n) (K := K) j b w := by
  simp only [treeDiff, restrictVertexFunction, PeriodicLattice.restrictGaugeMap, Pi.add_apply]
  abel
private theorem treeDiff_smul {j : ℕ} {F : BlockFrame} {l : ℕ} (r : ℝ) (b : F.Site l × Fin 4)
    (v : Vertex L n K 0 → ComplexMatrix2) :
    treeDiff (L := L) (n := n) (K := K) j b (r • v) =
      r • treeDiff (L := L) (n := n) (K := K) j b v := by
  simp only [treeDiff, restrictVertexFunction, PeriodicLattice.restrictGaugeMap, Pi.smul_apply, smul_sub]
private def treeDiffMap (L n K : ℕ) :
    ↥(topVanishingGauges L n K) →ₗ[ℝ] EuclideanSpace ℝ (TreeChainCoord L n K) where
  toFun v := WithLp.toLp 2 fun e => suTwoComponents (treeDiff (L := L) (n := n) (K := K) e.1 e.2.1.1
    ((v : vertexFunctionSpace L n K 0) : Vertex L n K 0 → ComplexMatrix2)) e.2.2
  map_add' v w := by
    refine PiLp.ext fun e => ?_
    simp [treeDiff_add, suTwoComponents_add]
  map_smul' r v := by
    refine PiLp.ext fun e => ?_
    simp [treeDiff_smul, suTwoComponents_smul]
private theorem treeDiffMap_bijective (hS : SiteDecomposition) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) : Function.Bijective (treeDiffMap L n K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    refine Subtype.ext (Subtype.ext ?_)
    refine eq_zero_of_treeDiff hS hL hn _ (fun x => v.1.2 x (Set.mem_univ x)) (fun y => v.2 y)
      fun j b => ?_
    funext c
    exact congrArg (fun f : EuclideanSpace ℝ (TreeChainCoord L n K) => f ⟨j, (b, c)⟩) hv
  · intro t
    obtain ⟨v, hv, htop, hd⟩ := exists_of_treeDiff hS hL hn
      (fun j b c => t ⟨j, (b, c)⟩ : (j : Fin K) → ↥(treeEdges (frameAtStep L n K j)) → Fin 3 → ℝ)
    refine ⟨⟨⟨v, fun x _ => hv x⟩, htop⟩, PiLp.ext fun e => ?_⟩
    obtain ⟨j, b, c⟩ := e
    exact congrFun (hd j b) c
end Slice
section Volume
open LinearConstraint Module
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
private theorem det_adjoint (f : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.det_adjoint_eq <;> assumption
private theorem absDetOfMap_pos (A : V →ₗ[ℝ] W) (hA : Function.Bijective A) : 0 < absDetOfMap A := by
  have hfin : finrank ℝ W = finrank ℝ V := (LinearEquiv.ofBijective A hA).finrank_eq.symm
  let e : W ≃ₗᵢ[ℝ] V := (stdOrthonormalBasis ℝ W).equiv
    ((stdOrthonormalBasis ℝ V).reindex (finCongr hfin.symm)) (Equiv.refl _)
  have h : LinearMap.adjoint A ∘ₗ A =
      LinearMap.adjoint (e.toLinearEquiv.toLinearMap ∘ₗ A) ∘ₗ (e.toLinearEquiv.toLinearMap ∘ₗ A) := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp
  have hd : LinearMap.det (e.toLinearEquiv.toLinearMap ∘ₗ A) ≠ 0 :=
    (LinearEquiv.isUnit_det' ((LinearEquiv.ofBijective A hA).trans e.toLinearEquiv)).ne_zero
  rw [absDetOfMap, h, LinearMap.det_comp, det_adjoint]
  exact Real.sqrt_pos.mpr (mul_self_pos.mpr hd)
end Volume
section OnTheGenerators
open LinearConstraint
variable {L n K : ℕ}
private def generatorVolume {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (h : VertexFunctionsEuclidean L n K 0) (T : ↥(topVanishingGauges L n K) →ₗ[ℝ] Y) : ℝ :=
  haveI := h.1
  letI := h.2.choose.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore h.2.choose.toCore
  absDetOfMap T
private theorem generatorVolume_pos {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (h : VertexFunctionsEuclidean L n K 0)
    (T : ↥(topVanishingGauges L n K) →ₗ[ℝ] Y) (hT : Function.Bijective T) :
    0 < generatorVolume h T := by
  haveI := h.1
  letI := h.2.choose.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore h.2.choose.toCore
  exact absDetOfMap_pos T hT
private theorem sliceOrbitVolume_eq {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (h : VertexFunctionsEuclidean L n K 0) (X : ChainPoint L n K)
    (l : LevelForms L n K →ₗ[ℝ] Y) :
    sliceOrbitVolume X l = generatorVolume h (l ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L n K).subtype) := by
  unfold sliceOrbitVolume generatorVolume
  rw [dif_pos h]
end OnTheGenerators
end TreeSlice
open TreeSlice in
theorem treeCoordsTransversalSlice_holds (hS : SiteDecomposition)
    (hRel : ChainRelationsAtCompactPoint) (hF : MinimizerFieldsNearOne)
    (hLv : ChainLevelIsStepMinimizer)
    (hB : FramePositiveEdgesBijective)
    (hE : FormOnAFibre.VertexFunctionsAreEuclidean.Statement) :
    TreeCoordsTransversalSlice := by
  classical
  intro a ha L hL k n hn ρ h0 h1
  have hL0 : 0 < L := by have := hL.2; omega
  have hE0 := hE L n (k + 1) 0 hL hn (Nat.zero_le _)
  have hbij := treeDiffMap_bijective (K := k + 1) hS hL hn
  refine ⟨generatorVolume hE0 (treeDiffMap L n (k + 1)), generatorVolume_pos hE0 _ hbij, ?_⟩
  have hε : 0 < PeriodicLattice.averagingRadiusCap L := by
    unfold PeriodicLattice.averagingRadiusCap
    positivity
  filter_upwards [hF a ha L hL (k + 1) n (by omega) hn _ hε] with V hV W hW X hX hR l hl
  have hsmall : LevelCurvaturesSmall X := fun j hj p => (hV W hW X hX).1 j hj.le p
  obtain ⟨-, -, -, -, -, hmove⟩ := hRel L hL (k + 1) n (by omega) hn X hX.compact hsmall
  have key : l ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L n (k + 1)).subtype = treeDiffMap L n (k + 1) := by
    refine LinearMap.ext fun v => PiLp.ext fun e => ?_
    obtain ⟨j, b, c⟩ := e
    have hj : (j : ℕ) < k + 1 := j.isLt
    obtain ⟨hodd, hs, hpt, hpn, hFL⟩ := frameAtStep_numbers (n := n) (K := k + 1) hL hn hj
    have hpos := (hB L hL n (k + 1) j hn hj.le (frameAtStep L n (k + 1) j) _ hpt).1 b.1
    have hW1 : levelField X j (edgeOfCoords j b.1) = 1 := by
      have htree : IsAxialTreeBond b.1 := (Finset.mem_filter.mp b.2).2
      rw [hLv a ρ L hL (k + 1) n hn V X hR j hj b.1]
      have h1' : fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n (k + 1) j V) 0 b.1.1 b.1.2 = 1 := by
        unfold fieldAboveFrame chartedField
        rw [if_neg htree.1, if_pos htree]
      rw [h1']
      exact SoftAverages.quaternionToMatrix_one
    show l (gaugeOrbitMap X v.1) ⟨j, (b, c)⟩ = _
    rw [hl]
    show suTwoComponents (tangentTransport X (gaugeOrbitMap X v.1) j (edgeOfCoords j b.1)) c =
      suTwoComponents (treeDiff (L := L) (n := n) (K := k + 1) j b.1
        ((v.1 : vertexFunctionSpace L n (k + 1) 0) : Vertex L n (k + 1) 0 → ComplexMatrix2)) c
    rw [(hmove v.1 j hj.le).1]
    congr 2
    unfold covDiff extendOddly treeDiff
    rw [if_pos hpos]
    beta_reduce
    rw [hW1]
    simp [ComplexMatrix2.conjugateBy]
  refine ⟨?_, ?_⟩
  · unfold IsTransversalSlice
    rw [key]
    exact hbij
  · rw [sliceOrbitVolume_eq hE0, key]
end YangMills.Construction.RunningCouplingSlope
end
