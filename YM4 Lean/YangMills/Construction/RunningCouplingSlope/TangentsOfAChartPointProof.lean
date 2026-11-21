import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.ColdStepAtMirrorFrames.ChartIsReadOffItsFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChartProof
import YangMills.Construction.RunningCouplingSlope.TangentsOfAChartPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace RunningCouplingSlope
namespace ChartDifferentialsBasis
open ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame}
private theorem basis_zero_re : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem basis_one_re : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem basis_two_re : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem basis_zero_imI : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imI = 1 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_zero_imJ : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_zero_imK : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imK = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_one_imI : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imI = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_one_imJ : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 1 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_one_imK : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imK = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_two_imI : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imI = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_two_imJ : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 0 := by
  simp [imaginaryBasis, toImaginary]
private theorem basis_two_imK : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imK = 1 := by
  simp [imaginaryBasis, toImaginary]
private theorem imaginaryCoord_eq_re_mul (m : Fin 3) (q : ℍ[ℝ]) :
    imaginaryCoord m q = (((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) * star q).re :=
  Quaternion.inner_def _ _
private theorem imaginaryCoord_zero (q : ℍ[ℝ]) : imaginaryCoord 0 q = q.imI := by
  rw [imaginaryCoord_eq_re_mul]
  simp [Quaternion.re_mul, basis_zero_re, basis_zero_imI, basis_zero_imJ, basis_zero_imK]
private theorem imaginaryCoord_one (q : ℍ[ℝ]) : imaginaryCoord 1 q = q.imJ := by
  rw [imaginaryCoord_eq_re_mul]
  simp [Quaternion.re_mul, basis_one_re, basis_one_imI, basis_one_imJ, basis_one_imK]
private theorem imaginaryCoord_two (q : ℍ[ℝ]) : imaginaryCoord 2 q = q.imK := by
  rw [imaginaryCoord_eq_re_mul]
  simp [Quaternion.re_mul, basis_two_re, basis_two_imI, basis_two_imJ, basis_two_imK]
private theorem imaginaryCoord_basis (m m' : Fin 3) :
    imaginaryCoord m ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) m m' := by
  fin_cases m <;> fin_cases m' <;>
    simp [imaginaryCoord_zero, imaginaryCoord_one, imaginaryCoord_two, basis_zero_imI, basis_zero_imJ,
      basis_zero_imK, basis_one_imI, basis_one_imJ, basis_one_imK, basis_two_imI, basis_two_imJ, basis_two_imK]
private theorem adjointMatrix_one : adjointMatrix (1 : UnitQuaternion) = 1 := by
  funext m m'
  unfold adjointMatrix
  simp [imaginaryCoord_basis]
private def site (z : F.Cell) (u : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth z + siteOfCoords F.depth u
private theorem site_add_unitStep (z : F.Cell) (u : Fin 4 → ℤ) (i : Fin 4) :
    site z u + unitStep F.depth i = site z (u + Pi.single i 1) := offset_add_unitStep z u i
private theorem site_zero_offset (z : F.Cell) : site z 0 = cellCentre F.depth z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.blockSite_zero <;> assumption
private theorem halfSide_nonneg (hL : Odd F.blockSide) : 0 ≤ halfSide F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.halfSide_nonneg <;> assumption
private theorem zero_mem_centredCube (hL : Odd F.blockSide) : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.GaugeFixing.zero_mem_centredCube <;> assumption
private theorem add_single_mem_centredCube {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide) (k : Fin 4) (c : ℤ)
    (h : -halfSide F.blockSide ≤ u k + c ∧ u k + c ≤ halfSide F.blockSide) :
    u + Pi.single k c ∈ centredCube F.blockSide := by
  have hc := (mem_centredCube_iff u).mp hu
  rw [mem_centredCube_iff]
  intro l
  by_cases hl : l = k
  · subst hl
    simpa using h
  · simpa [Pi.single_eq_of_ne hl] using hc l
private theorem enclosingCell_site (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) {u : Fin 4 → ℤ}
    (hu : u ∈ centredCube F.blockSide) : enclosingCell (site z u) = z := enclosingCell_offset hL hs z u hu
private theorem cellOffset_site (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) {u : Fin 4 → ℤ}
    (hu : u ∈ centredCube F.blockSide) : cellOffset (site z u) = u := cellOffset_offset hL hs z u hu
private theorem site_injective (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {z z' : F.Cell}
    {u u' : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide) (hu' : u' ∈ centredCube F.blockSide)
    (e : site z u = site z' u') : z = z' ∧ u = u' := by
  refine ⟨?_, ?_⟩
  · rw [← enclosingCell_site hL hs z hu, ← enclosingCell_site hL hs z' hu', e]
  · rw [← cellOffset_site hL hs z hu, ← cellOffset_site hL hs z' hu', e]
private theorem isAxialTreeBond_site_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond (site z u, i) ↔ u i ≠ halfSide F.blockSide ∧ ∀ l, i < l → u l = 0 := by apply _root_.YangMills.Construction.TopLevelSites.isAxialTreeBond_iff <;> assumption
private theorem isBlockCentre_site_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide) : IsBlockCentre F.top (site z u) ↔ u = 0 := by
  constructor
  · rintro ⟨y, e⟩
    have e1 : site z u = site y 0 := by
      rw [site_zero_offset]
      exact e
    exact (site_injective hL hs hu (zero_mem_centredCube hL) e1).2
  · rintro rfl
    exact ⟨z, site_zero_offset z⟩
private theorem mem_sitesOfCells (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) : x ∈ sitesOfCells (finiteCells F) F.depth :=
  hcover F hL (fun i => by have := hs i; omega) x
private theorem mem_innerBonds (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ innerBonds (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.mem_innerBonds <;> assumption
private theorem exists_eq_site (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) : ∃ z, ∃ u ∈ centredCube F.blockSide, x = site z u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.exists_blockSite <;> assumption
private def offsetNorm (v : Fin 4 → ℤ) : ℕ := ∑ l, (v l).natAbs
private theorem offsetNorm_add_single_lt {v : Fin 4 → ℤ} {k : Fin 4} {c : ℤ}
    (h : (v k + c).natAbs < (v k).natAbs) : offsetNorm (v + Pi.single k c) < offsetNorm v := by
  unfold offsetNorm
  refine Finset.sum_lt_sum (fun l _ => ?_) ⟨k, Finset.mem_univ _, by simpa using h⟩
  by_cases hl : l = k
  · subst hl
    simpa using h.le
  · simp [Pi.single_eq_of_ne hl]
private theorem exists_last_ne_zero {v : Fin 4 → ℤ} (hv : v ≠ 0) : ∃ k, v k ≠ 0 ∧ ∀ l, k < l → v l = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.exists_last_ne_zero <;> assumption
private def farEnd (x : F.Site F.depth) (i : Fin 4) : F.Site F.depth :=
  if 0 ≤ cellOffset x i then x + unitStep F.depth i else x
private theorem farEnd_site (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) {u : Fin 4 → ℤ}
    (hu : u ∈ centredCube F.blockSide) (i : Fin 4) (hne : u i ≠ halfSide F.blockSide) :
    ∃ v ∈ centredCube F.blockSide, farEnd (site z u) i = site z v ∧ v i ≠ 0 ∧ (∀ l, l ≠ i → v l = u l) ∧
      ((0 < v i ∧ v = u + Pi.single i 1) ∨ (v i < 0 ∧ v = u)) := by
  have hc := (mem_centredCube_iff u).mp hu
  unfold farEnd
  rw [cellOffset_site hL hs z hu]
  by_cases h : 0 ≤ u i
  · rw [if_pos h, site_add_unitStep]
    have hvi : (u + Pi.single i 1 : Fin 4 → ℤ) i = u i + 1 := by simp
    refine ⟨_, add_single_mem_centredCube hu i 1 ?_, rfl, ?_, fun l hl => ?_, Or.inl ⟨?_, rfl⟩⟩
    · have := hc i
      omega
    · rw [hvi]
      omega
    · simp [Pi.single_eq_of_ne hl]
    · rw [hvi]
      omega
  · rw [if_neg h]
    exact ⟨u, hu, rfl, by omega, fun _ _ => rfl, Or.inr ⟨by omega, rfl⟩⟩
private theorem exists_treeBond_farEnd (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    {v : Fin 4 → ℤ} (hv : v ∈ centredCube F.blockSide) (h0 : v ≠ 0) :
    ∃ (i : Fin 4) (a a' : Fin 4 → ℤ), a' ∈ centredCube F.blockSide ∧ offsetNorm a' < offsetNorm v ∧
      IsAxialTreeBond (site z a, i) ∧ farEnd (site z a) i = site z v ∧
      ((a = a' ∧ site z a + unitStep F.depth i = site z v) ∨
        (a = v ∧ site z a + unitStep F.depth i = site z a')) := by
  obtain ⟨k, k1, k2⟩ := exists_last_ne_zero h0
  have hc := (mem_centredCube_iff v).mp hv
  have hh := halfSide_nonneg (F := F) hL
  rcases lt_or_gt_of_ne k1 with hneg | hpos
  · have hm : v + Pi.single k 1 ∈ centredCube F.blockSide :=
      add_single_mem_centredCube hv k 1 (by have := hc k; omega)
    refine ⟨k, v, v + Pi.single k 1, hm, offsetNorm_add_single_lt (by omega), ?_, ?_,
      Or.inr ⟨rfl, site_add_unitStep z v k⟩⟩
    · exact (isAxialTreeBond_site_iff hL hs z hv k).mpr ⟨by omega, k2⟩
    · unfold farEnd
      rw [cellOffset_site hL hs z hv, if_neg (by omega)]
  · have hm : v + Pi.single k (-1) ∈ centredCube F.blockSide :=
      add_single_mem_centredCube hv k (-1) (by have := hc k; omega)
    have hback : v + Pi.single k (-1) + Pi.single k 1 = v := by
      funext l
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Pi.single_eq_of_ne hl]
    have hvk : (v + Pi.single k (-1) : Fin 4 → ℤ) k = v k - 1 := by simp [sub_eq_add_neg]
    have hend : site z (v + Pi.single k (-1)) + unitStep F.depth k = site z v := by
      rw [site_add_unitStep, hback]
    refine ⟨k, v + Pi.single k (-1), v + Pi.single k (-1), hm, offsetNorm_add_single_lt (by omega), ?_, ?_,
      Or.inl ⟨rfl, hend⟩⟩
    · refine (isAxialTreeBond_site_iff hL hs z hm k).mpr ⟨?_, fun l hl => ?_⟩
      · rw [hvk]
        have := hc k
        omega
      · simp [Pi.single_eq_of_ne hl.ne', k2 l hl]
    · unfold farEnd
      rw [cellOffset_site hL hs z hm, if_pos (by rw [hvk]; omega), hend]
private theorem eq_zero_of_treeBonds (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (f : F.Site F.depth → ℝ) (hc : ∀ z, f (cellCentre F.depth z) = 0)
    (ht : ∀ b, IsAxialTreeBond b → f b.1 = f (b.1 + unitStep F.depth b.2)) (x : F.Site F.depth) : f x = 0 := by
  obtain ⟨z, u, hu, rfl⟩ := exists_eq_site hcover hL hs x
  induction h : offsetNorm u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases h0 : u = 0
    · rw [h0, site_zero_offset]
      exact hc z
    · obtain ⟨i, a, a', ha', hlt, htree, -, hcase⟩ := exists_treeBond_farEnd hL hs z hu h0
      have hb := ht _ htree
      simp only at hb
      have h1 := ih (offsetNorm a') (h ▸ hlt) a' ha' rfl
      rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e2, e1] at hb
        rw [← hb]
        exact h1
      · rw [e2, e1] at hb
        rw [hb]
        exact h1
private abbrev AxialTreeBond (F : BlockFrame) : Type := {b : F.Site F.depth × Fin 4 // IsAxialTreeBond b}
private abbrev OffCentreSite (F : BlockFrame) : Type := {x : F.Site F.depth // ¬ IsBlockCentre F.top x}
private theorem farEnd_not_isBlockCentre (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (b : AxialTreeBond F) : ¬ IsBlockCentre F.top (farEnd b.1.1 b.1.2) := by
  obtain ⟨⟨x, i⟩, ht⟩ := b
  obtain ⟨z, u, hu, rfl⟩ := exists_eq_site hcover hL hs x
  obtain ⟨a1, -⟩ := (isAxialTreeBond_site_iff hL hs z hu i).mp ht
  obtain ⟨v, hv, c1, c2, -, -⟩ := farEnd_site hL hs z hu i a1
  simp only
  rw [c1, isBlockCentre_site_iff hL hs z hv]
  rintro rfl
  exact c2 rfl
private def farEndMap (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    AxialTreeBond F → OffCentreSite F := fun b => ⟨farEnd b.1.1 b.1.2, farEnd_not_isBlockCentre hcover hL hs b⟩
private theorem farEndMap_bijective (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) : Function.Bijective (farEndMap hcover hL hs) := by
  constructor
  · rintro ⟨⟨x, i⟩, ht⟩ ⟨⟨x', i'⟩, ht'⟩ h
    have h' : farEnd x i = farEnd x' i' := congrArg Subtype.val h
    obtain ⟨z, u, hu, rfl⟩ := exists_eq_site hcover hL hs x
    obtain ⟨z', u', hu', rfl⟩ := exists_eq_site hcover hL hs x'
    obtain ⟨a1, a2⟩ := (isAxialTreeBond_site_iff hL hs z hu i).mp ht
    obtain ⟨b1, b2⟩ := (isAxialTreeBond_site_iff hL hs z' hu' i').mp ht'
    obtain ⟨v, hv, c1, c2, c3, c4⟩ := farEnd_site hL hs z hu i a1
    obtain ⟨v', hv', d1, d2, d3, d4⟩ := farEnd_site hL hs z' hu' i' b1
    rw [c1, d1] at h'
    obtain ⟨hz, hvv⟩ := site_injective hL hs hv hv' h'
    subst hz
    subst hvv
    have hi : i = i' := by
      rcases lt_trichotomy i i' with hlt | he | hlt
      · exact absurd ((c3 i' hlt.ne').trans (a2 i' hlt)) d2
      · exact he
      · exact absurd ((d3 i hlt.ne').trans (b2 i hlt)) c2
    subst hi
    have hu2 : u = u' := by
      rcases c4 with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;> rcases d4 with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · exact add_right_cancel (p2.symm.trans q2)
      · omega
      · omega
      · exact p2.symm.trans q2
    subst hu2
    rfl
  · rintro ⟨y, hy⟩
    obtain ⟨z, v, hv, rfl⟩ := exists_eq_site hcover hL hs y
    have h0 : v ≠ 0 := fun h => hy ((isBlockCentre_site_iff hL hs z hv).mpr h)
    obtain ⟨i, a, a', -, -, htree, hch, -⟩ := exists_treeBond_farEnd hL hs z hv h0
    exact ⟨⟨(site z a, i), htree⟩, Subtype.ext hch⟩
private def treeBondOf (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    OffCentreSite F ≃ AxialTreeBond F :=
  (Equiv.ofBijective _ (farEndMap_bijective hcover hL hs)).symm
private theorem treeBondOf_farEndMap (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (b : AxialTreeBond F) : treeBondOf hcover hL hs (farEndMap hcover hL hs b) = b :=
  (Equiv.ofBijective _ (farEndMap_bijective hcover hL hs)).symm_apply_apply b
private theorem mem_chordBonds_iff (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ↔ b ∈ innerBonds (finiteCells F) F.depth ∧ ¬ IsAxialTreeBond b := by
  classical
  unfold chordBonds
  simp only [Finset.mem_filter]
private def componentBond (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    ReferenceDensity.ChartCoord F ⊕ OffCentreComponent F F.depth F.top → LinkComponent F F.depth
  | .inl q => (⟨q.1.1, ((mem_chordBonds_iff _).mp q.1.2).1⟩, q.2)
  | .inr s => (⟨(treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).1, mem_innerBonds hcover hL hs _⟩, s.1.2)
private theorem componentBond_bijective (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) : Function.Bijective (componentBond hcover hL hs) := by
  constructor
  · rintro (q | s) (q' | s') h
    · have h1 : q.1.1 = q'.1.1 := congrArg (fun p : LinkComponent F F.depth => p.1.1) h
      have h2 : q.2 = q'.2 := congrArg (fun p : LinkComponent F F.depth => p.2) h
      exact congrArg Sum.inl (Prod.ext (Subtype.ext h1) h2)
    · exfalso
      have h1 : q.1.1 = (treeBondOf hcover hL hs ⟨s'.1.1.1, s'.2⟩).1 :=
        congrArg (fun p : LinkComponent F F.depth => p.1.1) h
      exact ((mem_chordBonds_iff _).mp q.1.2).2 (h1 ▸ (treeBondOf hcover hL hs ⟨s'.1.1.1, s'.2⟩).2)
    · exfalso
      have h1 : (treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).1 = q'.1.1 :=
        congrArg (fun p : LinkComponent F F.depth => p.1.1) h
      exact ((mem_chordBonds_iff _).mp q'.1.2).2 (h1 ▸ (treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).2)
    · have h1 : (treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).1 = (treeBondOf hcover hL hs ⟨s'.1.1.1, s'.2⟩).1 :=
        congrArg (fun p : LinkComponent F F.depth => p.1.1) h
      have h2 : s.1.2 = s'.1.2 := congrArg (fun p : LinkComponent F F.depth => p.2) h
      have h3 := (treeBondOf hcover hL hs).injective (Subtype.ext h1)
      have h4 : s.1.1.1 = s'.1.1.1 := congrArg (fun y : OffCentreSite F => y.1) h3
      exact congrArg Sum.inr (Subtype.ext (Prod.ext (Subtype.ext h4) h2))
  · rintro ⟨⟨b, hb⟩, m⟩
    by_cases ht : IsAxialTreeBond b
    · refine ⟨.inr ⟨(⟨(farEndMap hcover hL hs ⟨b, ht⟩).1, mem_sitesOfCells hcover hL hs _⟩, m),
        (farEndMap hcover hL hs ⟨b, ht⟩).2⟩, ?_⟩
      exact Prod.ext (Subtype.ext (congrArg (fun y : AxialTreeBond F => y.1)
        (treeBondOf_farEndMap hcover hL hs ⟨b, ht⟩))) rfl
    · exact ⟨.inl (⟨b, (mem_chordBonds_iff _).mpr ⟨hb, ht⟩⟩, m), rfl⟩
open Classical in
private def siteValue (v : OffCentreComponent F F.depth F.top → ℝ) (m : Fin 3) (x : F.Site F.depth) : ℝ :=
  if h : x ∈ sitesOfCells (finiteCells F) F.depth ∧ ¬ IsBlockCentre F.top x then v ⟨(⟨x, h.1⟩, m), h.2⟩ else 0
private theorem sum_indicator_eq_siteValue [Fintype (OffCentreComponent F F.depth F.top)]
    (v : OffCentreComponent F F.depth F.top → ℝ) (m : Fin 3) (x : F.Site F.depth)
    [∀ s : OffCentreComponent F F.depth F.top, Decidable (s.1.1.1 = x ∧ s.1.2 = m)] :
    ∑ s : OffCentreComponent F F.depth F.top, (if s.1.1.1 = x ∧ s.1.2 = m then (1 : ℝ) else 0) * v s =
      siteValue v m x := by
  classical
  unfold siteValue
  by_cases h : x ∈ sitesOfCells (finiteCells F) F.depth ∧ ¬ IsBlockCentre F.top x
  · rw [dif_pos h, Finset.sum_eq_single (⟨(⟨x, h.1⟩, m), h.2⟩ : OffCentreComponent F F.depth F.top)]
    · simp
    · intro s _ hs
      rw [if_neg, zero_mul]
      rintro ⟨e1, e2⟩
      exact hs (Subtype.ext (Prod.ext (Subtype.ext e1) e2))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg, zero_mul]
    rintro ⟨e1, -⟩
    exact h ⟨e1 ▸ s.1.1.2, e1 ▸ s.2⟩
private theorem row_sum_at_one [Fintype (OffCentreComponent F F.depth F.top)]
    (v : OffCentreComponent F F.depth F.top → ℝ) (p : LinkComponent F F.depth) :
    ∑ s, offCentreGaugeDifferential (F := F) (fun _ _ => 1) p s * v s =
      siteValue v p.2 p.1.1.1 - siteValue v p.2 (p.1.1.1 + unitStep F.depth p.1.1.2) := by
  classical
  rw [← sum_indicator_eq_siteValue v p.2 p.1.1.1,
    ← sum_indicator_eq_siteValue v p.2 (p.1.1.1 + unitStep F.depth p.1.1.2), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← sub_mul]
  congr 1
  have h : ∀ (C D D' : Prop) [Decidable C] [Decidable D] [Decidable D'] [Decidable (C ∧ D')], (D ↔ D') →
      (if C then (if D then (1 : ℝ) else 0) else 0) = if C ∧ D' then 1 else 0 := by
    intro C D D' _ _ _ _ hd
    by_cases c : C <;> by_cases d : D' <;> simp [c, d, hd]
  simp only [offCentreGaugeDifferential, gaugeDifferential, Matrix.submatrix_apply, id, adjointMatrix_one,
    Matrix.one_apply]
  rw [h _ _ _ eq_comm]
private theorem treeBlock_det_ne_zero [Fintype (OffCentreComponent F F.depth F.top)]
    [DecidableEq (OffCentreComponent F F.depth F.top)]
    (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    ((offCentreGaugeDifferential (F := F) (fun _ _ => 1)).submatrix
      (fun s => componentBond hcover hL hs (.inr s)) id).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hrow : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → ∀ m,
      siteValue v m b.1 = siteValue v m (b.1 + unitStep F.depth b.2) := by
    intro b ht m
    set y := farEndMap hcover hL hs ⟨b, ht⟩ with hy
    set s : OffCentreComponent F F.depth F.top := ⟨(⟨y.1, mem_sitesOfCells hcover hL hs _⟩, m), y.2⟩ with hs'
    have h : ∑ j, offCentreGaugeDifferential (F := F) (fun _ _ => 1)
        (componentBond hcover hL hs (.inr s)) j * v j = 0 :=
      congrFun hv s
    rw [row_sum_at_one] at h
    have e : (componentBond hcover hL hs (.inr s)).1.1 = b :=
      congrArg (fun y : AxialTreeBond F => y.1) (treeBondOf_farEndMap hcover hL hs ⟨b, ht⟩)
    have e2 : (componentBond hcover hL hs (.inr s)).2 = m := rfl
    rw [e, e2] at h
    exact sub_eq_zero.mp h
  have hz : ∀ m x, siteValue v m x = 0 := by
    intro m
    refine eq_zero_of_treeBonds hcover hL hs _ (fun z => ?_) (fun b ht => hrow b ht m)
    unfold siteValue
    rw [dif_neg]
    rintro ⟨-, h⟩
    exact h ⟨z, rfl⟩
  funext s
  have h := hz s.1.2 s.1.1.1
  unfold siteValue at h
  rw [dif_pos ⟨s.1.1.2, s.2⟩] at h
  exact h
end ChartDifferentialsBasis
open ChartDifferentialsBasis in
theorem chartAndGaugeDifferentialsBasis_holds (hcover : BlocksCoverLowerLevel) :
    ChartAndGaugeDifferentialsBasis := by
  classical
  intro F hL hs
  let e := Equiv.ofBijective _ (componentBond_bijective hcover hL hs)
  set D := (offCentreGaugeDifferential (F := F) (fun _ _ => 1)).submatrix
    (fun s => componentBond hcover hL hs (.inr s)) id with hD
  refine ⟨e, D.det, treeBlock_det_ne_zero hcover hL hs, fun w W hW => ?_⟩
  set M := Matrix.fromCols (chartDifferential w) (offCentreGaugeDifferential W) with hM
  have h1 : (M.submatrix id e.symm).det = (M.submatrix e id).det := by
    rw [← Matrix.det_submatrix_equiv_self e (M.submatrix id e.symm)]
    congr 1
    ext i j
    simp
  set A := (chartDifferential w).submatrix (fun q => componentBond hcover hL hs (.inl q)) id with hA
  set B := (offCentreGaugeDifferential W).submatrix (fun q => componentBond hcover hL hs (.inl q)) id with hB
  have h2 : M.submatrix e id = Matrix.fromBlocks A B 0 D := by
    ext i j
    rcases i with q | s <;> rcases j with q' | s'
    · rfl
    · rfl
    · have ht : IsAxialTreeBond (componentBond hcover hL hs (.inr s)).1.1 :=
        (treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).2
      change chartDifferential w (componentBond hcover hL hs (.inr s)) q' = 0
      unfold chartDifferential
      rw [if_neg]
      intro e0
      exact ((mem_chordBonds_iff _).mp q'.1.2).2 (e0 ▸ ht)
    · have ht : IsAxialTreeBond (componentBond hcover hL hs (.inr s)).1.1 :=
        (treeBondOf hcover hL hs ⟨s.1.1.1, s.2⟩).2
      change offCentreGaugeDifferential W (componentBond hcover hL hs (.inr s)) s' =
        offCentreGaugeDifferential (F := F) (fun _ _ => 1) (componentBond hcover hL hs (.inr s)) s'
      have hw := hW _ ht
      simp only [offCentreGaugeDifferential, gaugeDifferential, Matrix.submatrix_apply, id]
      rw [hw]
  have h3 : A = (Matrix.blockDiagonal fun b : ↥(chordBonds (finiteCells F)) =>
      leftExpDifferential (w b.1.1 b.1.2)).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext q q'
    change (if q.1.1 = q'.1.1 then leftExpDifferential (w q'.1.1.1 q'.1.1.2) q.2 q'.2 else 0) =
      (if q.1 = q'.1 then leftExpDifferential (w q.1.1.1 q.1.1.2) q.2 q'.2 else 0)
    by_cases hq : q.1 = q'.1
    · rw [if_pos hq, if_pos (congrArg Subtype.val hq), hq]
    · rw [if_neg hq, if_neg fun h => hq (Subtype.ext h)]
  rw [h1, h2]
  refine Eq.trans (?_ : _ = A.det * D.det) ?_
  · convert Matrix.det_fromBlocks_zero₂₁ A B D
  · rw [h3, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, mul_comm]
end RunningCouplingSlope
end YangMills.Construction
end
