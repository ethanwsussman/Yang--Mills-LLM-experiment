import YangMills.Construction.HoleBesideASecondHole.BoxesAtACellClose
import YangMills.Construction.HoleBesideASecondHole.BoxesOfNeighboursAgree
import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.HoleBesideASecondHole.CurvatureAtAQuietCell
import YangMills.Construction.HoleBesideASecondHole.FieldWithTheBoxesFilled
import YangMills.Construction.HoleBesideASecondHole.FlatGaugeOnTheShellOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings Holes HoleSites LatticeGauge CornerBoxes BlockSites
namespace HoleSavings
namespace FilledField
attribute [local irreducible] _root_.YangMills.Construction.LumpContours.cellBall
variable {F : BlockFrame} {g : LumpGrid F.blockSide} {a s θ : ℝ} {J₀ : ℕ}
structure Setting (D : HoleData F g a s θ J₀) (C : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) : Prop where
  blockSide_odd : Odd F.blockSide
  extent_ge : ∀ i, 4096 ≤ F.extent i
  blockSide_gt : 4 * (11 * 2 ^ 12 * J₀) < F.blockSide
  one_le : 1 ≤ J₀
  family : D.IsHoleFamily C idx o
  uncrowded : ExcludedBoxesAtUncrowdedCell
  neighbours : ExcludedBoxesOfNeighboursAgree
variable {D : HoleData F g a s θ J₀} {C : ℝ} {idx : Finset (Finset (F.Site F.depth)) → ℕ}
  {o : Finset (Finset (F.Site F.depth)) → F.Site F.depth}
theorem Setting.extent_pos (X : Setting D C idx o) (i : Fin 4) : 0 < F.extent i := by
  have := X.extent_ge i
  omega
theorem Setting.excludedBoxes_spec (X : Setting D C idx o) {y : F.Cell}
    (hc : ¬ IsCrowded J₀ D.hotFineLumps y) :
    IsLeastSeparatedCover (lumpSeeds D.hotFineLumps y) (excludedBoxes J₀ D.hotFineLumps y) ∧
      ∑ Z ∈ excludedBoxes J₀ D.hotFineLumps y, largestSide Z ≤ 11 * 2 ^ 12 * J₀ ∧
      (∀ Z ∈ excludedBoxes J₀ D.hotFineLumps y, ∃ lo hi : Fin 4 → ℤ, Z = boxSites F.depth lo hi ∧
        ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ ((11 * 2 ^ 12 * J₀ : ℕ) : ℤ)) ∧
      ∀ Z ∈ excludedBoxes J₀ D.hotFineLumps y, ∀ Z',
        IsSeparatedCover ((lumpSeeds D.hotFineLumps y).filter fun l => l ⊆ Z) Z' → ∃ B ∈ Z', Z ⊆ B := by
  have := X.uncrowded F g J₀ D.hotFineLumps y X.blockSide_odd (fun i => by have := X.extent_ge i; omega)
    (by have := X.blockSide_gt; omega) D.isLump_of_mem_hotFineLumps hc
  refine ⟨this.1, this.2.1, fun Z hZ => ?_, this.2.2.2⟩
  obtain ⟨lo, hi, h1, h2⟩ := this.2.2.1 Z hZ
  refine ⟨lo, hi, h1, fun i => ⟨(h2 i).1, ?_⟩⟩
  have := (h2 i).2
  push_cast
  exact this
theorem Setting.le_blockSide (X : Setting D C idx o) : 11 * 2 ^ 12 * J₀ ≤ F.blockSide := by
  have := X.blockSide_gt
  omega
theorem Setting.mem_cutBelow_cellBall (X : Setting D C idx o) {y : F.Cell}
    (hc : ¬ IsCrowded J₀ D.hotFineLumps y) {Z : Finset (F.Site F.depth)}
    (hZ : Z ∈ excludedBoxes J₀ D.hotFineLumps y) {u : F.Cell} {z₀ x : F.Site F.depth} (hz₀ : z₀ ∈ Z)
    (hu : z₀ ∈ sitesBelow F.depth u) (hx : x ∈ Z) :
    x ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall u 1) :=
  mem_cutBelow_cellBall_of_boxSites X.blockSide_odd
    (by have := X.le_blockSide; omega : 11 * 2 ^ 12 * J₀ ≤ F.blockSide * 1)
    ((X.excludedBoxes_spec hc).2.2.1 Z hZ) hz₀ hu hx
theorem Setting.isSmallBox_innerBox (X : Setting D C idx o) {H : Hole F} (hH : H ∈ D.holesAt C idx o) :
    IsSmallBox F H.innerBox := by
  have h1 := X.family.radius_bounds H hH
  refine ⟨_, _, fun i => ⟨?_, ?_⟩, thicken_singleton H.radius H.centre⟩
  · omega
  · have : 2 * H.radius + 1 < F.blockSide := by nlinarith [h1.1, h1.2]
    have h2 : ((2 * H.radius + 1 : ℕ) : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast this
    push_cast at h2
    omega
theorem Setting.exists_hole_of_box [∀ i, NeZero (F.period F.depth i)] [∀ i, NeZero (F.period F.top i)]
    (X : Setting D C idx o) {y : F.Cell}
    (hy : y ∈ D.coreCells C 5) {Z : Finset (F.Site F.depth)} (hZ : Z ∈ excludedBoxes J₀ D.hotFineLumps y)
    (hm : (Z ∩ sitesBelow F.depth y).Nonempty) :
    ∃ H ∈ D.holesAt C idx o, Z ⊆ H.innerBox := by
  classical
  have hc := D.not_isCrowded_of_mem_coreCells (by omega) hy
  obtain ⟨c₁, c₂, c₃, c₄⟩ := X.excludedBoxes_spec hc
  have hseed : ((lumpSeeds D.hotFineLumps y).filter fun l => l ⊆ Z).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨B, hB, -⟩ := c₄ Z hZ ∅ ⟨by simp, by rw [hne]; simp, by simp⟩
    simp at hB
  obtain ⟨s₀, hs₀⟩ := hseed
  obtain ⟨hs₁, hs₂⟩ := Finset.mem_filter.mp hs₀
  obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hs₁
  have hhot₀ : l₀ ∈ D.hotFineLumps := (Finset.mem_filter.mp hl₀).1
  obtain ⟨u₀, hu₀, hl₀u, x₀, hx₀⟩ :=
    D.exists_subset_sitesBelow_of_mem_hotFineLumps X.blockSide_odd X.extent_pos hhot₀
  have hx₀Z : x₀ ∈ Z := hs₂ (subset_thicken _ _ hx₀)
  obtain ⟨z₀, hz₀⟩ := hm
  obtain ⟨m₁, m₂⟩ := Finset.mem_inter.mp hz₀
  obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (X.mem_cutBelow_cellBall hc hZ m₁ m₂ hx₀Z)
  have hvu : v = u₀ := eq_of_mem_sitesBelow X.blockSide_odd X.extent_pos hxv (hl₀u hx₀)
  subst hvu
  have hcd : cellSupDist y v ≤ 1 :=
    cellSupDist_le_one_of_mem_cellBall (fun i => by have := X.extent_ge i; omega) hv
  have hcore : v ∈ D.coreCells C 4 := D.mem_coreCells_of_supDist_le_one hy hu₀ hcd
  obtain ⟨H, hH, hl₀H⟩ :=
    X.family.exists_hole_of_core l₀ hhot₀ v (D.coreCells_antitone (by omega) hcore) hl₀u
  refine ⟨H, hH, ?_⟩
  have hcover : IsSeparatedCover ((lumpSeeds D.hotFineLumps y).filter fun l => l ⊆ Z) {H.innerBox} := by
    refine ⟨fun B hB => ?_, fun s' hs' => ?_, fun B hB B' hB' hne => ?_⟩
    · rw [Finset.mem_singleton.mp hB]
      exact X.isSmallBox_innerBox hH
    rotate_left
    · rw [Finset.mem_singleton.mp hB, Finset.mem_singleton.mp hB'] at hne
      exact absurd rfl hne
    obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hs'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h₁
    have hhot : l ∈ D.hotFineLumps := (Finset.mem_filter.mp hl).1
    obtain ⟨-, -, -, x₁, hx₁⟩ :=
      D.exists_subset_sitesBelow_of_mem_hotFineLumps X.blockSide_odd X.extent_pos hhot
    have hx₁Z : x₁ ∈ Z := h₂ (subset_thicken _ _ hx₁)
    have hdist : supDist x₀ x₁ ≤ holeScale J₀ 1 := by
      obtain ⟨lo, hi, hZe, hw⟩ := c₃ Z hZ
      rw [hZe] at hx₀Z hx₁Z
      obtain ⟨d, hd, e⟩ := exists_offset_of_mem_boxSites (fun i => (hw i).2) hx₁Z hx₀Z
      rw [e]
      have := supDist_add_le (x := x₀) (d := d) (m := 11 * 2 ^ 12 * J₀) hd (fun i => by
        rw [period_depth]
        have h2 : 2 * F.blockSide ≤ F.extent i * F.blockSide :=
          Nat.mul_le_mul_right _ (by have := X.extent_ge i; omega)
        have h3 := X.blockSide_gt
        have : 2 * (11 * 2 ^ 12 * J₀) < F.extent i * F.blockSide := by omega
        exact_mod_cast this)
      refine this.trans ?_
      have hs : holeScale J₀ 1 = 16 * 2 ^ 12 * (40 * J₀) := by simp [holeScale, lumpRange]
      rw [hs]
      omega
    have hlH : l ∈ H.lumps := X.family.closed_under_nearby H hH l₀ hl₀H l hhot
      ⟨x₀, subset_thicken _ _ hx₀, x₁, subset_thicken _ _ hx₁, hdist⟩
    exact ⟨H.innerBox, Finset.mem_singleton_self _, X.family.collar_subset H hH l hlH⟩
  obtain ⟨B, hB, hZB⟩ := c₄ Z hZ {H.innerBox} hcover
  rwa [Finset.mem_singleton.mp hB] at hZB
def latticeField {j : ℕ} (W : F.GaugeField j) : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion :=
  fun a i => W (siteOfCoords j a) i
theorem siteOfCoords_add_unitVec {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfCoords j (a + unitVec i) : F.Site j) = siteOfCoords j a + unitStep j i :=
  _root_.YangMills.Construction.BlockSites.siteOfCoords_add a _
theorem plaquetteHolonomy_eq {j : ℕ} (W : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    BlockAverages.plaquetteHolonomy W (x, μ, ν) =
      W x μ * W (x + unitStep j μ) ν * (W (x + unitStep j ν) μ)⁻¹ * (W x ν)⁻¹ := by
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + -unitStep j μ - unitStep j ν = x := by abel
  simp only [BlockAverages.plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true,
    Bool.false_eq_true, if_false, e1, e2, mul_one]
  group
theorem latticeField_plaquetteHolonomy {j : ℕ} (W : F.GaugeField j) (a : Fin 4 → ℤ) (μ ν : Fin 4) :
    LatticeGauge.plaquetteHolonomy (latticeField W) a μ ν =
      BlockAverages.plaquetteHolonomy W (siteOfCoords j a, μ, ν) := by
  rw [plaquetteHolonomy_eq]
  simp only [LatticeGauge.plaquetteHolonomy, latticeField, siteOfCoords_add_unitVec]
theorem plaquetteDefect_comm (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (a : Fin 4 → ℤ) (μ ν : Fin 4) :
    LatticeGauge.plaquetteDefect X a μ ν = LatticeGauge.plaquetteDefect X a ν μ := by
  have e : LatticeGauge.plaquetteHolonomy X a ν μ = (LatticeGauge.plaquetteHolonomy X a μ ν)⁻¹ := by
    simp only [LatticeGauge.plaquetteHolonomy]
    group
  rw [LatticeGauge.plaquetteDefect, LatticeGauge.plaquetteDefect, e]
  have := quatDist_inv (LatticeGauge.plaquetteHolonomy X a μ ν) 1
  rw [inv_one] at this
  exact this.symm
theorem Setting.mem_cutPlaquettes_of_not_subset [∀ i, NeZero (F.period F.depth i)]
    [∀ i, NeZero (F.period F.top i)] (X : Setting D C idx o) {y : F.Cell}
    (hy : y ∈ D.coreCells C 5) {p : F.Site F.depth × Fin 4 × Fin 4} (hord : p.2.1 < p.2.2)
    (hS : plaquetteCorners p ⊆ cutBelow F.depth D.cells)
    (hball : plaquetteCorners p ⊆ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1))
    (hno : ∀ B ∈ excludedBoxes J₀ D.hotFineLumps y, ¬ plaquetteCorners p ⊆ B) :
    p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)) := by
  classical
  have hc := D.not_isCrowded_of_mem_coreCells (by omega) hy
  obtain ⟨c₁, -, -, -⟩ := X.excludedBoxes_spec hc
  have hne : p.2.1 ≠ p.2.2 := hord.ne
  have hoff : ∀ x ∈ plaquetteCorners p, x ∉ lumpsNeighbourhood D.hotFineLumps := by
    intro x hx hN
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hN
    obtain ⟨u, hu, hlu, -⟩ := D.exists_subset_sitesBelow_of_mem_hotFineLumps X.blockSide_odd X.extent_pos hl
    obtain ⟨x₀, hx₀, d, hd, rfl⟩ := mem_thicken_iff.mp hxl
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (hball hx)
    have hback : x₀ ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall v 1) := by
      have := add_mem_cutBelow_cellBall X.blockSide_odd hxv (-d) 1 fun i => by
        have h1 := hd i
        have h2 := X.blockSide_gt
        have h3 : ((lumpRange : ℕ) : ℤ) ≤ (F.blockSide : ℤ) := by
          have : lumpRange ≤ F.blockSide := by
            have := X.one_le
            simp only [lumpRange]
            omega
          exact_mod_cast this
        simp only [Pi.neg_apply, abs_neg]
        push_cast
        linarith
      have e : x₀ + siteOfCoords F.depth d + siteOfCoords F.depth (-d) = x₀ := by
        have : (siteOfCoords F.depth (-d) : F.Site F.depth) = - siteOfCoords F.depth d := by
          funext i
          simp [siteOfCoords]
        rw [this]
        abel
      rwa [e] at this
    obtain ⟨v', hv', hx₀v⟩ := Finset.mem_biUnion.mp hback
    have hvu : v' = u := eq_of_mem_sitesBelow X.blockSide_odd X.extent_pos hx₀v (hlu hx₀)
    subst hvu
    have hd₁ : cellSupDist y v ≤ 1 :=
      cellSupDist_le_one_of_mem_cellBall (fun i => by have := X.extent_ge i; omega) hv
    have hball2 : v' ∈ _root_.YangMills.Construction.LumpContours.cellBall y 2 := mem_cellBall_add hv' hd₁
    have hbeside : l ∈ nearbyLumps D.hotFineLumps y := Finset.mem_filter.mpr ⟨hl, fun z hz =>
      Finset.mem_biUnion.mpr ⟨v', hball2, hlu hz⟩⟩
    obtain ⟨B, hB, hlB⟩ := c₁.1.2.1 (lumpCollar l) (Finset.mem_image_of_mem _ hbeside)
    refine hno B hB fun z hz => hlB ?_
    obtain ⟨e, he, rfl⟩ := exists_step_of_mem_plaquetteCorners hne hx hz
    refine mem_thicken_iff.mpr ⟨x₀, hx₀, d + e, fun i => ?_, ?_⟩
    · have h1 := hd i
      have h2 := he i
      rw [abs_le] at h1 h2 ⊢
      simp only [Pi.add_apply]
      push_cast at h1 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [_root_.YangMills.Construction.BlockSites.siteOfCoords_add, add_assoc]
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hord, fun x hx => ?_⟩
  · have h0 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS h0, hoff _ h0⟩, hball h0⟩
  · simp
  · exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS hx, hoff _ hx⟩, hball hx⟩
theorem coords_eq_of_mem_box {lo hi : Fin 4 → ℤ} (hper : ∀ i, hi i - lo i + 2 ≤ F.period F.depth i)
    {a a' : Fin 4 → ℤ} (ha : a ∈ box lo hi) (ha' : a' ∈ box lo hi)
    (h : (siteOfCoords F.depth a : F.Site F.depth) = siteOfCoords F.depth a') : a = a' := by
  funext i
  have h1 := siteOfCoords_eq_iff.mp h i
  have h2 := ha i
  have h3 := ha' i
  have h4 := hper i
  have h5 := Int.eq_zero_of_abs_lt_dvd h1 (by
    rw [abs_lt]
    constructor <;> omega)
  omega
theorem Setting.exists_flat_gauge [∀ i, NeZero (F.period F.depth i)] [∀ i, NeZero (F.period F.top i)]
    (X : Setting D C idx o) (hflat : FlatGaugeOnBoxBoundary) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : ∀ y ∈ D.coreCells C 5, ∀ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)),
      BlockAverages.plaquetteDefect D.fineField p ≤ ε)
    {y : F.Cell} (hy : y ∈ D.coreCells C 5) {Z : Finset (F.Site F.depth)}
    (hZ : Z ∈ excludedBoxes J₀ D.hotFineLumps y) (hm : (Z ∩ sitesBelow F.depth y).Nonempty) :
    ∃ G : F.Site F.depth → UnitQuaternion, (∀ x ∈ Z, G x = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
        ‖((_root_.YangMills.Construction.BlockAverages.gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          40 * ((11 * 2 ^ 12 * J₀ + 2 : ℕ) : ℝ) ^ 2 * ε := by
  classical
  have hc := D.not_isCrowded_of_mem_coreCells (by omega) hy
  obtain ⟨c₁, -, c₃, -⟩ := X.excludedBoxes_spec hc
  obtain ⟨H, hH, hZH⟩ := X.exists_hole_of_box hy hZ hm
  obtain ⟨lo, hi, hZe, hw⟩ := c₃ Z hZ
  set M := 11 * 2 ^ 12 * J₀ + 2 with hMdef
  have hlam := X.blockSide_gt
  have hone := X.one_le
  let LO : Fin 4 → ℤ := fun i => lo i - ((1 : ℕ) : ℤ)
  let HI : Fin 4 → ℤ := fun i => hi i + ((1 : ℕ) : ℤ)
  have hEnl : thicken 1 Z = boxSites F.depth LO HI := by
    rw [hZe]
    exact thicken_boxSites 1 lo hi fun i => (hw i).1
  have hPer : ∀ i, (M : ℤ) + 3 ≤ F.period F.depth i := by
    intro i
    rw [period_depth]
    have h2 : 2 * F.blockSide ≤ F.extent i * F.blockSide :=
      Nat.mul_le_mul_right _ (by have := X.extent_ge i; omega)
    have : M + 3 ≤ F.extent i * F.blockSide := by omega
    exact_mod_cast this
  have hwM : ∀ i, HI i - LO i + 1 ≤ (M : ℤ) + 1 := by
    intro i
    have := (hw i).2
    simp only [HI, LO, hMdef]
    push_cast at this ⊢
    omega
  have hperL : ∀ i, HI i - LO i + 2 ≤ F.period F.depth i := fun i => by
    have := hwM i
    have := hPer i
    omega
  have hcorn : ∃ lo' hi' : Fin 4 → ℤ, thicken 1 Z = boxSites F.depth lo' hi' ∧
      ∀ i, lo' i ≤ hi' i ∧ hi' i - lo' i + 1 ≤ ((M + 1 : ℕ) : ℤ) :=
    ⟨LO, HI, hEnl, fun i => ⟨by
      have := (hw i).1
      simp only [LO, HI]
      omega, by
      have := hwM i
      push_cast
      omega⟩⟩
  obtain ⟨z₀, hz₀⟩ := hm
  obtain ⟨m₁, m₂⟩ := Finset.mem_inter.mp hz₀
  have hinS : ∀ x ∈ thicken 1 Z, x ∈ cutBelow F.depth D.cells := by
    intro x hx
    obtain ⟨z, hz, d, hd, rfl⟩ := mem_thicken_iff.mp hx
    have hw' := X.family.walls H hH (z + siteOfCoords F.depth d) (mem_thicken_iff.mpr
      ⟨z, innerBox_subset_outerBox H (hZH hz), d, fun i => by
        have h1 := hd i
        have h2 : ((1 : ℕ) : ℤ) ≤ ((F.blockSide / 2 : ℕ) : ℤ) := by
          have : 1 ≤ F.blockSide / 2 := by omega
          exact_mod_cast this
        linarith, rfl⟩)
    exact (mem_cutBelow_iff X.blockSide_odd X.extent_pos).mpr hw'.1
  have hinB : ∀ x ∈ thicken 1 Z, x ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1) := fun x hx =>
    mem_cutBelow_cellBall_of_boxSites X.blockSide_odd (by omega : M + 1 ≤ F.blockSide * 1) hcorn
      (subset_thicken _ _ m₁) m₂ hx
  have hshellZ : ∀ a ∈ boxBoundary LO HI, (siteOfCoords F.depth a : F.Site F.depth) ∈ boxShell Z := by
    intro a ha
    obtain ⟨ha₁, i, hi'⟩ := ha
    refine Finset.mem_sdiff.mpr ⟨?_, fun hin => ?_⟩
    · rw [hEnl]
      exact (mem_boxOfCorners (q := (LO, HI))).mpr ⟨a, ha₁, rfl⟩
    · rw [hZe] at hin
      obtain ⟨b, hb, he⟩ := (mem_boxOfCorners (q := (lo, hi))).mp hin
      have hbb : b ∈ box LO HI := fun l => by
        have := hb l
        simp only [LO, HI]
        simp only at this
        omega
      have := coords_eq_of_mem_box hperL hbb ha₁ he
      subst this
      have h1 := hb i
      simp only [LO, HI] at hi'
      simp only at h1
      omega
  have hother : ∀ B ∈ excludedBoxes J₀ D.hotFineLumps y, ∀ x ∈ boxShell Z, x ∉ B := by
    intro B hB x hx hxB
    obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.mp hx
    by_cases hBZ : B = Z
    · exact h₂ (hBZ ▸ hxB)
    obtain ⟨z, hz, d, hd, e⟩ := mem_thicken_iff.mp h₁
    refine c₁.1.2.2 Z hZ B hB (Ne.symm hBZ) ⟨z, hz, x, hxB, ?_⟩
    rw [e]
    have := supDist_add_le (x := z) (d := d) (m := 1) hd (fun i => by
      have := hPer i
      push_cast
      omega)
    omega
  have key : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν → a ∈ boxBoundary LO HI →
      a + unitVec μ ∈ boxBoundary LO HI → a + unitVec ν ∈ boxBoundary LO HI →
      a + unitVec μ + unitVec ν ∈ boxBoundary LO HI →
      LatticeGauge.plaquetteDefect (latticeField D.fineField) a μ ν ≤ ε := by
    intro a μ ν hμν h₁ h₂ h₃ h₄
    have hsub : plaquetteCorners ((siteOfCoords F.depth a : F.Site F.depth), μ, ν) ⊆ boxShell Z := by
      intro x hx
      simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hshellZ a h₁
      · have := hshellZ _ h₂
        rwa [siteOfCoords_add_unitVec] at this
      · have := hshellZ _ h₃
        rwa [siteOfCoords_add_unitVec] at this
      · have := hshellZ _ h₄
        rwa [siteOfCoords_add_unitVec, siteOfCoords_add_unitVec] at this
    have hp := X.mem_cutPlaquettes_of_not_subset hy
      (p := ((siteOfCoords F.depth a : F.Site F.depth), μ, ν)) hμν
      (fun x hx => hinS x (Finset.mem_sdiff.mp (hsub hx)).1)
      (fun x hx => hinB x (Finset.mem_sdiff.mp (hsub hx)).1)
      (fun B hB hs => hother B hB _
        (hsub (show (siteOfCoords F.depth a : F.Site F.depth) ∈ plaquetteCorners _ by simp [plaquetteCorners]))
        (hs (by simp [plaquetteCorners])))
    have := hq y hy _ hp
    rw [LatticeGauge.plaquetteDefect, latticeField_plaquetteHolonomy]
    exact this
  obtain ⟨γ, hγ⟩ := hflat (latticeField D.fineField) LO HI M ε (fun i => ⟨by
      have := (hw i).1
      simp only [LO, HI]
      push_cast
      omega, by
      have := hwM i
      omega⟩) hε (fun a μ ν hμν h₁ h₂ h₃ h₄ => by
    rcases lt_or_gt_of_ne hμν with c | c
    · exact key a μ ν c h₁ h₂ h₃ h₄
    · have e : a + unitVec μ + unitVec ν = a + unitVec ν + unitVec μ := by abel
      have := key a ν μ c h₁ h₃ h₂ (e ▸ h₄)
      rw [← plaquetteDefect_comm] at this
      exact this)
  let G : F.Site F.depth → UnitQuaternion := fun x =>
    if x ∈ Z then 1 else
      if h : ∃ a, a ∈ box LO HI ∧ (siteOfCoords F.depth a : F.Site F.depth) = x then γ h.choose else 1
  have hlift : ∀ x ∈ boxShell Z, ∃ a, a ∈ box LO HI ∧ (siteOfCoords F.depth a : F.Site F.depth) = x := by
    intro x hx
    have h₁ := (Finset.mem_sdiff.mp hx).1
    rw [hEnl] at h₁
    obtain ⟨a, ha, he⟩ := (mem_boxOfCorners (q := (LO, HI))).mp h₁
    exact ⟨a, ha, he⟩
  have hGat : ∀ x ∈ boxShell Z, ∀ a, a ∈ box LO HI →
      (siteOfCoords F.depth a : F.Site F.depth) = x → G x = γ a := by
    intro x hx a ha he
    have hxZ := (Finset.mem_sdiff.mp hx).2
    have h : ∃ a, a ∈ box LO HI ∧ (siteOfCoords F.depth a : F.Site F.depth) = x := ⟨a, ha, he⟩
    simp only [G, if_neg hxZ, dif_pos h]
    rw [coords_eq_of_mem_box hperL h.choose_spec.1 ha (h.choose_spec.2.trans he.symm)]
  have hshell : ∀ x ∈ boxShell Z, ∀ a, a ∈ box LO HI →
      (siteOfCoords F.depth a : F.Site F.depth) = x → a ∈ boxBoundary LO HI := by
    intro x hx a ha he
    refine ⟨ha, ?_⟩
    by_contra hno
    push_neg at hno
    have hxZ := (Finset.mem_sdiff.mp hx).2
    refine hxZ ?_
    rw [hZe, ← he]
    refine (mem_boxOfCorners (q := (lo, hi))).mpr ⟨a, fun l => ?_, rfl⟩
    have h₁ := ha l
    have h₂ := hno l
    simp only [LO, HI] at h₁ h₂ ⊢
    push_cast at h₁ h₂
    omega
  refine ⟨G, fun x hx => if_pos hx, ?_⟩
  rintro ⟨x, i⟩ hb hb'
  simp only at hb hb' ⊢
  obtain ⟨a, ha, hax⟩ := hlift x hb
  obtain ⟨a₂, ha₂, hax₂⟩ := hlift _ hb'
  have e₂ : a₂ = a + unitVec i := by
    funext l
    have h1 : (siteOfCoords F.depth a₂ : F.Site F.depth) = siteOfCoords F.depth (a + unitVec i) := by
      rw [hax₂, siteOfCoords_add_unitVec, hax]
    have h2 := siteOfCoords_eq_iff.mp h1 l
    have h3 := ha l
    have h4 := ha₂ l
    have h5 := hwM l
    have h6 := hPer l
    have h7 : (a + unitVec i) l = a l + if l = i then 1 else 0 := by
      by_cases hl : l = i
      · subst hl
        simp [unitVec]
      · simp [unitVec, hl]
    have h8 : |(a + unitVec i) l - a₂ l| < (F.period F.depth l : ℤ) := by
      rw [abs_lt, h7]
      split_ifs <;> constructor <;> omega
    have h9 := Int.eq_zero_of_abs_lt_dvd h2 h8
    omega
  subst e₂
  have g₁ := hGat x hb a ha hax
  have g₂ := hGat _ hb' _ ha₂ hax₂
  have h₁ := hγ a i (hshell x hb a ha hax) (hshell _ hb' _ ha₂ hax₂)
  simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform, g₁, g₂]
  rw [← hax]
  exact h₁
theorem mem_coreBoxes {Z : Finset (F.Site F.depth)} :
    Z ∈ D.coreBoxes C ↔ ∃ y ∈ D.coreCells C 5, Z ∈ excludedBoxes J₀ D.hotFineLumps y ∧
      (Z ∩ sitesBelow F.depth y).Nonempty := by
  classical
  simp only [HoleData.coreBoxes, boxFamily, Finset.mem_biUnion, Finset.mem_filter]
theorem Setting.mem_excludedBoxes_of_adj [∀ i, NeZero (F.period F.depth i)] (X : Setting D C idx o)
    {y y' : F.Cell} (hy : y ∈ D.coreCells C 5) (hy' : y' ∈ D.coreCells C 5)
    (hd : cellSupDist y y' ≤ 1) {Z : Finset (F.Site F.depth)} (hZ : Z ∈ excludedBoxes J₀ D.hotFineLumps y)
    (hm : (Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) :
    Z ∈ excludedBoxes J₀ D.hotFineLumps y' :=
  (X.neighbours F g J₀ D.hotFineLumps X.blockSide_odd (fun i => by have := X.extent_ge i; omega)
    X.blockSide_gt D.isLump_of_mem_hotFineLumps).1 y y'
    (D.not_isCrowded_of_mem_coreCells (by omega) hy) (D.not_isCrowded_of_mem_coreCells (by omega) hy')
    hd Z hZ hm
theorem Setting.not_areWithin (X : Setting D C idx o) {Z Z' : Finset (F.Site F.depth)}
    (hZ : Z ∈ D.coreBoxes C) (hZ' : Z' ∈ D.coreBoxes C) (hne : Z ≠ Z') :
    ¬ AreWithin 2 Z Z' := by
  obtain ⟨y, hy, h₁, h₂⟩ := mem_coreBoxes.mp hZ
  obtain ⟨y', hy', h₁', h₂'⟩ := mem_coreBoxes.mp hZ'
  exact (X.neighbours F g J₀ D.hotFineLumps X.blockSide_odd (fun i => by have := X.extent_ge i; omega)
    X.blockSide_gt D.isLump_of_mem_hotFineLumps).2 y y'
    (D.not_isCrowded_of_mem_coreCells (by omega) hy) (D.not_isCrowded_of_mem_coreCells (by omega) hy')
    Z h₁ Z' h₁' h₂ h₂' hne
theorem Setting.eq_of_mem_thicken [∀ i, NeZero (F.period F.depth i)] (X : Setting D C idx o)
    {Z Z' : Finset (F.Site F.depth)} (hZ : Z ∈ D.coreBoxes C) (hZ' : Z' ∈ D.coreBoxes C)
    {x : F.Site F.depth} (hx : x ∈ thicken 1 Z) (hx' : x ∈ thicken 1 Z') : Z = Z' := by
  by_contra hne
  obtain ⟨z, hz, d, hd, e⟩ := mem_thicken_iff.mp hx
  obtain ⟨z', hz', d', hd', e'⟩ := mem_thicken_iff.mp hx'
  have hper : ∀ i, 2 * ((1 : ℕ) : ℤ) < F.period F.depth i := fun i => by
    rw [period_depth]
    have h2 : 2 * F.blockSide ≤ F.extent i * F.blockSide :=
      Nat.mul_le_mul_right _ (by have := X.extent_ge i; omega)
    have h3 := X.blockSide_gt
    have h4 := X.one_le
    have : 2 * 1 < F.extent i * F.blockSide := by omega
    exact_mod_cast this
  have h₁ : supDist z x ≤ 1 := by
    rw [e]
    exact supDist_add_le hd hper
  have h₂ : supDist z' x ≤ 1 := by
    rw [e']
    exact supDist_add_le hd' hper
  refine X.not_areWithin hZ hZ' hne ⟨z, hz, z', hz', ?_⟩
  have := supDist_triangle z x z'
  rw [_root_.YangMills.Construction.BlockSites.supDist_comm x z'] at this
  omega
theorem quatDist_conj_one (a b : UnitQuaternion) : quatDist (a * b * a⁻¹) 1 = quatDist b 1 := by
  rw [quatDist_mul_inv_one (a * b) a]
  have := quatDist_mul_left a b 1
  rwa [mul_one] at this
theorem plaquetteDefect_gaugeTransform (G : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth)
    (p : F.Site F.depth × Fin 4 × Fin 4) :
    BlockAverages.plaquetteDefect (_root_.YangMills.Construction.BlockAverages.gaugeTransform G W) p = BlockAverages.plaquetteDefect W p := by
  obtain ⟨x, μ, ν⟩ := p
  have e : BlockAverages.plaquetteHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform G W) (x, μ, ν) =
      G x * BlockAverages.plaquetteHolonomy W (x, μ, ν) * (G x)⁻¹ := by
    rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
    simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform]
    rw [add_right_comm x (unitStep F.depth ν) (unitStep F.depth μ)]
    group
  have e1 : BlockAverages.plaquetteDefect (_root_.YangMills.Construction.BlockAverages.gaugeTransform G W) (x, μ, ν) =
      quatDist (BlockAverages.plaquetteHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform G W) (x, μ, ν)) 1 := rfl
  have e2 : BlockAverages.plaquetteDefect W (x, μ, ν) =
      quatDist (BlockAverages.plaquetteHolonomy W (x, μ, ν)) 1 := rfl
  rw [e1, e2, e, quatDist_conj_one]
theorem quatDist_plaquette_le {v₁ v₂ v₃ v₄ : UnitQuaternion} {k : ℝ} (h₁ : quatDist v₁ 1 ≤ k)
    (h₂ : quatDist v₂ 1 ≤ k) (h₃ : quatDist v₃ 1 ≤ k) (h₄ : quatDist v₄ 1 ≤ k) :
    quatDist (v₁ * v₂ * v₃⁻¹ * v₄⁻¹) 1 ≤ 4 * k := by
  have a₃ : quatDist v₃⁻¹ 1 ≤ k := by
    have := quatDist_inv v₃ 1
    rw [inv_one] at this
    rwa [this]
  have a₄ : quatDist v₄⁻¹ 1 ≤ k := by
    have := quatDist_inv v₄ 1
    rw [inv_one] at this
    rwa [this]
  have s₁ := quatDist_mul_mul v₁ v₂ 1 1
  have s₂ := quatDist_mul_mul (v₁ * v₂) v₃⁻¹ 1 1
  have s₃ := quatDist_mul_mul (v₁ * v₂ * v₃⁻¹) v₄⁻¹ 1 1
  simp only [mul_one] at s₁ s₂ s₃
  linarith
theorem Setting.quatDist_gaugeTransform_le [∀ i, NeZero (F.period F.depth i)] (X : Setting D C idx o)
    {Wt : F.GaugeField F.depth} {G : F.Site F.depth → UnitQuaternion} {k : ℝ} (hk : 0 ≤ k)
    (hfil : ∀ Z ∈ D.coreBoxes C,
      (∀ b : F.Site F.depth × Fin 4, BondTouches Z b → gaugeTransform G Wt b.1 b.2 = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
        ‖((gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ k)
    (hoff : ∀ b : F.Site F.depth × Fin 4, (∀ Z ∈ D.coreBoxes C, ¬ BondTouches Z b) →
      Wt b.1 b.2 = D.fineField b.1 b.2)
    {Z : Finset (F.Site F.depth)} (hZ : Z ∈ D.coreBoxes C) {b : F.Site F.depth × Fin 4}
    (h₁ : b.1 ∈ thicken 1 Z) (h₂ : b.1 + unitStep F.depth b.2 ∈ thicken 1 Z) :
    quatDist (_root_.YangMills.Construction.BlockAverages.gaugeTransform G Wt b.1 b.2) 1 ≤ k := by
  by_cases hm : BondTouches Z b
  · rw [(hfil Z hZ).1 b hm, quatDist_self]
    exact hk
  · have hm₁ : b.1 ∉ Z := fun h => hm (Or.inl h)
    have hm₂ : b.1 + unitStep F.depth b.2 ∉ Z := fun h => hm (Or.inr h)
    have hnone : ∀ Z' ∈ D.coreBoxes C, ¬ BondTouches Z' b := by
      intro Z' hZ' hb
      rcases hb with hb | hb
      · have := X.eq_of_mem_thicken hZ hZ' h₁ (subset_thicken _ _ hb)
        exact hm₁ (this ▸ hb)
      · have := X.eq_of_mem_thicken hZ hZ' h₂ (subset_thicken _ _ hb)
        exact hm₂ (this ▸ hb)
    have e : _root_.YangMills.Construction.BlockAverages.gaugeTransform G Wt b.1 b.2 = _root_.YangMills.Construction.BlockAverages.gaugeTransform G D.fineField b.1 b.2 := by
      simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform, hoff b hnone]
    rw [e]
    exact (hfil Z hZ).2 b (Finset.mem_sdiff.mpr ⟨h₁, hm₁⟩) (Finset.mem_sdiff.mpr ⟨h₂, hm₂⟩)
theorem card_plaquettes_at_corner_le {j : ℕ} (P : Finset (F.Site j × Fin 4 × Fin 4))
    (hP : ∀ p ∈ P, p.2.1 < p.2.2) (x : F.Site j) :
    (P.filter fun p => x ∈ plaquetteCorners p).card ≤ 24 := by
  classical
  let T : Finset ((Fin 4 × Fin 4) × Bool × Bool) :=
    (Finset.univ.filter fun m : Fin 4 × Fin 4 => m.1 < m.2) ×ˢ Finset.univ
  have hT : T.card = 24 := by decide
  let f : (Fin 4 × Fin 4) × Bool × Bool → F.Site j × Fin 4 × Fin 4 := fun u =>
    (x - (if u.2.1 then unitStep j u.1.1 else 0) - (if u.2.2 then unitStep j u.1.2 else 0), u.1.1, u.1.2)
  have hsub : (P.filter fun p => x ∈ plaquetteCorners p) ⊆ T.image f := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨z, μ, ν⟩ := p
    have hlt : μ < ν := hP _ hp₁
    have hmem : ∀ b b' : Bool,
        z = x - (if b then unitStep j μ else 0) - (if b' then unitStep j ν else 0) →
        (z, μ, ν) ∈ T.image f := fun b b' he => Finset.mem_image.mpr
      ⟨((μ, ν), b, b'), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩,
        Finset.mem_univ _⟩, by
        simp only [f]
        rw [← he]⟩
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hp₂
    rcases hp₂ with h | h | h | h
    · exact hmem false false (by simp [h])
    · exact hmem true false (by simp [h])
    · exact hmem false true (by simp [h])
    · exact hmem true true (by simp [h]; abel)
  calc _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = 24 := hT
theorem card_boxSites_le {j : ℕ} {lo hi : Fin 4 → ℤ} {m : ℕ} (hw : ∀ i, hi i - lo i + 1 ≤ (m : ℤ)) :
    (boxSites j lo hi : Finset (F.Site j)).card ≤ m ^ 4 := by
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset]
  have := Finset.prod_le_pow_card (Finset.univ : Finset (Fin 4))
    (fun i => (Finset.Icc (lo i) (hi i)).card) m (fun i _ => by
      rw [Int.card_Icc]
      have := hw i
      omega)
  simpa using this
theorem card_excludedBoxes_le (X : Setting D C idx o) {y : F.Cell} (hc : ¬ IsCrowded J₀ D.hotFineLumps y) :
    (excludedBoxes J₀ D.hotFineLumps y).card ≤ 11 * 2 ^ 12 * J₀ := by
  obtain ⟨c₁, c₂, -, -⟩ := X.excludedBoxes_spec hc
  refine le_trans ?_ c₂
  have h1 : ∀ Z ∈ excludedBoxes J₀ D.hotFineLumps y, 1 ≤ largestSide Z := by
    intro Z hZ
    obtain ⟨lo, hi, hb, rfl⟩ := c₁.1.1 Z hZ
    have hne : (boxSites F.depth lo hi : Finset (F.Site F.depth)).Nonempty :=
      ⟨siteOfCoords F.depth lo, (mem_boxOfCorners (q := (lo, hi))).mpr ⟨lo, fun i => ⟨le_rfl, (hb i).1⟩, rfl⟩⟩
    have h2 : (((boxSites F.depth lo hi : Finset (F.Site F.depth))).image fun x => x 0).card ≤
        largestSide (boxSites F.depth lo hi : Finset (F.Site F.depth)) :=
      Finset.le_sup
        (f := fun i : Fin 4 => (((boxSites F.depth lo hi : Finset (F.Site F.depth))).image fun x => x i).card)
        (Finset.mem_univ 0)
    have h3 : 0 < (((boxSites F.depth lo hi : Finset (F.Site F.depth))).image fun x => x 0).card :=
      Finset.card_pos.mpr (hne.image _)
    omega
  have := Finset.card_nsmul_le_sum _ _ 1 h1
  simpa using this
theorem Setting.sum_plaquetteDefect_sq_le [∀ i, NeZero (F.period F.depth i)] [∀ i, NeZero (F.period F.top i)]
    (X : Setting D C idx o) {Wt : F.GaugeField F.depth}
    {G : F.Site F.depth → UnitQuaternion} {k E₀ : ℝ} (hk : 0 ≤ k)
    (hfil : ∀ Z ∈ D.coreBoxes C,
      (∀ b : F.Site F.depth × Fin 4, BondTouches Z b → gaugeTransform G Wt b.1 b.2 = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
        ‖((gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ k)
    (hoff : ∀ b : F.Site F.depth × Fin 4, (∀ Z ∈ D.coreBoxes C, ¬ BondTouches Z b) →
      Wt b.1 b.2 = D.fineField b.1 b.2)
    (hquiet : ∀ y ∈ D.coreCells C 5, ∑ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)),
      BlockAverages.plaquetteDefect D.fineField p ^ 2 ≤ E₀)
    {y y' : F.Cell} (hy : y ∈ D.coreCells C 5) (hy' : y' ∈ D.coreCells C 5) (hd : cellSupDist y y' ≤ 1) :
    ∑ p ∈ cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y'), BlockAverages.plaquetteDefect Wt p ^ 2 ≤
      E₀ + (24 * ((11 * 2 ^ 12 * J₀ : ℕ) : ℝ) ^ 5) * (4 * k) ^ 2 := by
  classical
  set P := cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y') with hP
  have hord : ∀ p ∈ P, p.2.1 < p.2.2 := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hcor : ∀ p ∈ P, plaquetteCorners p ⊆ sitesBelow F.depth y ∪ sitesBelow F.depth y' :=
    fun p hp => (Finset.mem_filter.mp hp).2.2
  have hsideb : ∀ i, 2 < F.extent i := fun i => by have := X.extent_ge i; omega
  have hyball : y ∈ _root_.YangMills.Construction.LumpContours.cellBall y 1 := mem_cellBall_iff.mpr ⟨0, fun i => by simp, by
    have : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [this, add_zero]⟩
  have hy'ball : y' ∈ _root_.YangMills.Construction.LumpContours.cellBall y 1 := by
    obtain ⟨c, hc, e⟩ := exists_offset_of_supDist_le hd
    exact mem_cellBall_iff.mpr ⟨c, hc, e⟩
  have hS₁ := ((D.mem_coreCells).mp hy).1
  have hS₂ := ((D.mem_coreCells).mp hy').1
  have hin : ∀ c ∈ sitesBelow F.depth y ∪ sitesBelow F.depth y',
      c ∈ cutBelow F.depth D.cells ∧ c ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1) := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact ⟨Finset.mem_biUnion.mpr ⟨y, hS₁, h⟩, Finset.mem_biUnion.mpr ⟨y, hyball, h⟩⟩
    · exact ⟨Finset.mem_biUnion.mpr ⟨y', hS₂, h⟩, Finset.mem_biUnion.mpr ⟨y', hy'ball, h⟩⟩
  have hdy : cellSupDist y' y ≤ 1 := by
    have e : cellSupDist y' y = cellSupDist y y' := _root_.YangMills.Construction.BlockSites.supDist_comm y' y
    omega
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z)]
  have hA : ∀ p ∈ P.filter (fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
      BlockAverages.plaquetteDefect Wt p ^ 2 ≤ (4 * k) ^ 2 := by
    intro p hp
    obtain ⟨hpP, Z, hZ, c, hc, hcZ⟩ := Finset.mem_filter.mp hp
    have hne : p.2.1 ≠ p.2.2 := (hord p hpP).ne
    have henl : ∀ z ∈ plaquetteCorners p, z ∈ thicken 1 Z := fun z hz => by
      obtain ⟨e, he, rfl⟩ := exists_step_of_mem_plaquetteCorners hne hc hz
      exact mem_thicken_iff.mpr ⟨c, hcZ, e, fun i => by exact_mod_cast he i, rfl⟩
    obtain ⟨x, μ, ν⟩ := p
    simp only at hne
    have m₁ : x ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
    have m₂ : x + unitStep F.depth μ ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
    have m₃ : x + unitStep F.depth ν ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
    have m₄ : x + unitStep F.depth μ + unitStep F.depth ν ∈ plaquetteCorners (x, μ, ν) := by
      simp [plaquetteCorners]
    have b₁ := X.quatDist_gaugeTransform_le hk hfil hoff hZ (b := (x, μ)) (henl _ m₁) (henl _ m₂)
    have b₂ := X.quatDist_gaugeTransform_le hk hfil hoff hZ (b := (x + unitStep F.depth μ, ν))
      (henl _ m₂) (henl _ m₄)
    have b₃ := X.quatDist_gaugeTransform_le hk hfil hoff hZ (b := (x + unitStep F.depth ν, μ))
      (henl _ m₃) (by rw [add_right_comm]; exact henl _ m₄)
    have b₄ := X.quatDist_gaugeTransform_le hk hfil hoff hZ (b := (x, ν)) (henl _ m₁) (henl _ m₃)
    have h₄ := quatDist_plaquette_le b₁ b₂ b₃ b₄
    have e1 : BlockAverages.plaquetteDefect (_root_.YangMills.Construction.BlockAverages.gaugeTransform G Wt) (x, μ, ν) =
        quatDist (BlockAverages.plaquetteHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform G Wt) (x, μ, ν)) 1 := rfl
    have h₅ : BlockAverages.plaquetteDefect Wt (x, μ, ν) ≤ 4 * k := by
      rw [← _root_.YangMills.Construction.HoleSavings.FilledField.plaquetteDefect_gaugeTransform G, e1, plaquetteHolonomy_eq]
      exact h₄
    have h₆ : 0 ≤ BlockAverages.plaquetteDefect Wt (x, μ, ν) := norm_nonneg _
    nlinarith
  have hcardA : ((P.filter fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z).card : ℝ) ≤
      24 * ((11 * 2 ^ 12 * J₀ : ℕ) : ℝ) ^ 5 := by
    set U := (excludedBoxes J₀ D.hotFineLumps y).biUnion id with hU
    have hc₀ := D.not_isCrowded_of_mem_coreCells (by omega) hy
    have hUcard : U.card ≤ (11 * 2 ^ 12 * J₀) ^ 5 := by
      refine Finset.card_biUnion_le.trans ?_
      have h1 : ∀ B ∈ excludedBoxes J₀ D.hotFineLumps y,
          (id B : Finset (F.Site F.depth)).card ≤ (11 * 2 ^ 12 * J₀) ^ 4 := by
        intro B hB
        obtain ⟨lo, hi, rfl, hw⟩ := (X.excludedBoxes_spec hc₀).2.2.1 B hB
        exact card_boxSites_le fun i => (hw i).2
      have h2 := Finset.sum_le_card_nsmul _ _ _ h1
      have h3 := card_excludedBoxes_le X hc₀
      rw [smul_eq_mul] at h2
      refine h2.trans ?_
      calc _ ≤ (11 * 2 ^ 12 * J₀) * (11 * 2 ^ 12 * J₀) ^ 4 := Nat.mul_le_mul_right _ h3
        _ = _ := by ring
    have hsub : (P.filter fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z) ⊆
        U.biUnion fun c => P.filter fun p => c ∈ plaquetteCorners p := by
      intro p hp
      obtain ⟨hpP, Z, hZ, c, hc, hcZ⟩ := Finset.mem_filter.mp hp
      obtain ⟨y₀, hy₀, hZ₀, z₀, hz₀⟩ := mem_coreBoxes.mp hZ
      obtain ⟨a₁, a₂⟩ := Finset.mem_inter.mp hz₀
      have hc₁ := D.not_isCrowded_of_mem_coreCells (by omega) hy₀
      obtain ⟨v₂, hv₂, hcv⟩ := Finset.mem_biUnion.mp (X.mem_cutBelow_cellBall hc₁ hZ₀ a₁ a₂ hcZ)
      have hdist := cellSupDist_le_one_of_mem_cellBall hsideb hv₂
      have hZy : Z ∈ excludedBoxes J₀ D.hotFineLumps y := by
        rcases Finset.mem_union.mp (hcor p hpP hc) with h | h
        · have := eq_of_mem_sitesBelow X.blockSide_odd X.extent_pos hcv h
          subst this
          exact X.mem_excludedBoxes_of_adj hy₀ hy hdist hZ₀ (Or.inl ⟨z₀, hz₀⟩)
        · have := eq_of_mem_sitesBelow X.blockSide_odd X.extent_pos hcv h
          subst this
          have h3 := X.mem_excludedBoxes_of_adj hy₀ hy' hdist hZ₀ (Or.inl ⟨z₀, hz₀⟩)
          exact X.mem_excludedBoxes_of_adj hy' hy hdy h3 (Or.inl ⟨c, Finset.mem_inter.mpr ⟨hcZ, h⟩⟩)
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_biUnion.mpr ⟨Z, hZy, hcZ⟩, Finset.mem_filter.mpr ⟨hpP, hc⟩⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 := Finset.sum_le_card_nsmul U (fun c => (P.filter fun p => c ∈ plaquetteCorners p).card) 24
      (fun c _ => card_plaquettes_at_corner_le P hord c)
    rw [smul_eq_mul] at h2
    have h3 : (P.filter fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z).card ≤
        24 * (11 * 2 ^ 12 * J₀) ^ 5 := by
      have : U.card * 24 ≤ (11 * 2 ^ 12 * J₀) ^ 5 * 24 := Nat.mul_le_mul_right _ hUcard
      omega
    exact_mod_cast h3
  have hpart1 := Finset.sum_le_card_nsmul _ _ _ hA
  rw [nsmul_eq_mul] at hpart1
  have hpart1' : ∑ p ∈ P.filter (fun p => ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
      BlockAverages.plaquetteDefect Wt p ^ 2 ≤ (24 * ((11 * 2 ^ 12 * J₀ : ℕ) : ℝ) ^ 5) * (4 * k) ^ 2 :=
    hpart1.trans (mul_le_mul_of_nonneg_right hcardA (sq_nonneg _))
  have hB : ∀ p ∈ P.filter (fun p => ¬ ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
      BlockAverages.plaquetteDefect Wt p = BlockAverages.plaquetteDefect D.fineField p ∧
        p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)) := by
    intro p hp
    obtain ⟨hpP, hno⟩ := Finset.mem_filter.mp hp
    have hnone : ∀ Z ∈ D.coreBoxes C, ∀ x ∈ plaquetteCorners p, x ∉ Z :=
      fun Z hZ x hx hxZ => hno ⟨Z, hZ, x, hx, hxZ⟩
    constructor
    · obtain ⟨x, μ, ν⟩ := p
      have m₁ : x ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
      have m₂ : x + unitStep F.depth μ ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
      have m₃ : x + unitStep F.depth ν ∈ plaquetteCorners (x, μ, ν) := by simp [plaquetteCorners]
      have m₄ : x + unitStep F.depth μ + unitStep F.depth ν ∈ plaquetteCorners (x, μ, ν) := by
        simp [plaquetteCorners]
      have bond : ∀ b : F.Site F.depth × Fin 4, b.1 ∈ plaquetteCorners (x, μ, ν) →
          b.1 + unitStep F.depth b.2 ∈ plaquetteCorners (x, μ, ν) →
          Wt b.1 b.2 = D.fineField b.1 b.2 := fun b h₁ h₂ => hoff b fun Z hZ hm => by
        rcases hm with hm | hm
        · exact hnone Z hZ _ h₁ hm
        · exact hnone Z hZ _ h₂ hm
      have e : BlockAverages.plaquetteHolonomy Wt (x, μ, ν) =
          BlockAverages.plaquetteHolonomy D.fineField (x, μ, ν) := by
        rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq, bond (x, μ) m₁ m₂,
          bond (x + unitStep F.depth μ, ν) m₂ m₄,
          bond (x + unitStep F.depth ν, μ) m₃ (by rw [add_right_comm]; exact m₄), bond (x, ν) m₁ m₃]
      simp only [BlockAverages.plaquetteDefect, e]
    · refine X.mem_cutPlaquettes_of_not_subset hy (hord p hpP) (fun c hc => (hin c (hcor p hpP hc)).1)
        (fun c hc => (hin c (hcor p hpP hc)).2) fun B hBm hsub => ?_
      have h0 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
      have hb := hsub h0
      rcases Finset.mem_union.mp (hcor p hpP h0) with h | h
      · exact hnone B (mem_coreBoxes.mpr ⟨y, hy, hBm, p.1, Finset.mem_inter.mpr ⟨hb, h⟩⟩) _ h0 hb
      · have h3 := X.mem_excludedBoxes_of_adj hy hy' hd hBm (Or.inr ⟨p.1, Finset.mem_inter.mpr ⟨hb, h⟩⟩)
        exact hnone B (mem_coreBoxes.mpr ⟨y', hy', h3, p.1, Finset.mem_inter.mpr ⟨hb, h⟩⟩) _ h0 hb
  have hpart2 : ∑ p ∈ P.filter (fun p => ¬ ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
      BlockAverages.plaquetteDefect Wt p ^ 2 ≤ E₀ := by
    have h1 : ∑ p ∈ P.filter (fun p => ¬ ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
          BlockAverages.plaquetteDefect Wt p ^ 2 =
        ∑ p ∈ P.filter (fun p => ¬ ∃ Z ∈ D.coreBoxes C, ∃ x ∈ plaquetteCorners p, x ∈ Z),
          BlockAverages.plaquetteDefect D.fineField p ^ 2 :=
      Finset.sum_congr rfl fun p hp => by rw [(hB p hp).1]
    rw [h1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (hB p hp).2)
      fun _ _ _ => sq_nonneg _) (hquiet y hy)
  linarith
theorem exists_hotLump_of_mem_holesAt {H : Hole F} (hH : H ∈ D.holesAt C idx o) :
    ∃ l ∈ H.lumps, l ∈ D.hotFineLumps := by
  classical
  unfold HoleData.holesAt allHoles at hH
  obtain ⟨k, -, hH₂⟩ := Finset.mem_biUnion.mp hH
  unfold componentHoles at hH₂
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hH₂
  obtain ⟨h₁, -⟩ := Finset.mem_filter.mp hk'
  unfold linkComponents at h₁
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h₁
  exact ⟨l, Finset.mem_filter.mpr ⟨hl, Relation.ReflTransGen.refl⟩, hl⟩
theorem Setting.disjoint_of_nearbyLumps_eq_empty [∀ i, NeZero (F.period F.depth i)]
    [∀ i, NeZero (F.period F.top i)] (X : Setting D C idx o) {y : F.Cell}
    (hy : y ∈ D.coreCells C 5) (hemp : nearbyLumps D.hotFineLumps y = ∅) :
    (∀ H ∈ D.holesAt C idx o, H.outerBox ∩ sitesBelow F.depth y = ∅) ∧
      ∀ Z ∈ D.coreBoxes C, Z ∩ sitesBelow F.depth y = ∅ := by
  classical
  have first : ∀ H ∈ D.holesAt C idx o, H.outerBox ∩ sitesBelow F.depth y = ∅ := by
    intro H hH
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hlH, hl⟩ := exists_hotLump_of_mem_holesAt hH
    obtain ⟨l₁, hl₁, d, hd, rfl⟩ := mem_thicken_iff.mp (X.family.outer_subset H hH l hlH hx₁)
    obtain ⟨u, hu, hlu, -⟩ := D.exists_subset_sitesBelow_of_mem_hotFineLumps X.blockSide_odd X.extent_pos hl
    have hback : l₁ ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1) := by
      have := add_mem_cutBelow_cellBall X.blockSide_odd hx₂ (-d) 1 fun i => by
        have h1 := hd i
        have h2 := X.family.radius_bounds H hH
        have h3 : 3 * H.radius ≤ F.blockSide := by nlinarith [h2.1, h2.2]
        have h4 : ((3 * H.radius : ℕ) : ℤ) ≤ (F.blockSide : ℤ) := by exact_mod_cast h3
        simp only [Pi.neg_apply, abs_neg]
        push_cast at h1 h4 ⊢
        linarith
      have e : l₁ + siteOfCoords F.depth d + siteOfCoords F.depth (-d) = l₁ := by
        have : (siteOfCoords F.depth (-d) : F.Site F.depth) = - siteOfCoords F.depth d := by
          funext i
          simp [siteOfCoords]
        rw [this]
        abel
      rwa [e] at this
    obtain ⟨v, hv, hlv⟩ := Finset.mem_biUnion.mp hback
    have hvu : v = u := eq_of_mem_sitesBelow X.blockSide_odd X.extent_pos hlv (hlu hl₁)
    subst hvu
    have hself : cellSupDist y y ≤ 1 := by rw [cellSupDist_self]; omega
    have hball : v ∈ _root_.YangMills.Construction.LumpContours.cellBall y 2 := mem_cellBall_add hv hself
    have hbeside : l ∈ nearbyLumps D.hotFineLumps y := Finset.mem_filter.mpr ⟨hl, fun z hz =>
      Finset.mem_biUnion.mpr ⟨v, hball, hlu hz⟩⟩
    rw [hemp] at hbeside
    simp at hbeside
  refine ⟨first, fun Z hZ => ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨y₀, hy₀, hZ₀, hm⟩ := mem_coreBoxes.mp hZ
  obtain ⟨H, hH, hZH⟩ := X.exists_hole_of_box hy₀ hZ₀ hm
  have := first H hH
  rw [Finset.eq_empty_iff_forall_notMem] at this
  exact this x (Finset.mem_inter.mpr ⟨innerBox_subset_outerBox H (hZH hx₁), hx₂⟩)
theorem Setting.exists_isFilledField [∀ i, NeZero (F.period F.depth i)] [∀ i, NeZero (F.period F.top i)]
    (X : Setting D C idx o)
    (hflat : FlatGaugeOnBoxBoundary) {E₀ ρ CJ : ℝ} (hρ : 0 ≤ ρ) (hE : E₀ ≤ ρ ^ 2)
    (hquiet : ∀ y ∈ D.coreCells C 5, ∑ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)),
      BlockAverages.plaquetteDefect D.fineField p ^ 2 ≤ E₀)
    (h₁ : 40 * ((11 * 2 ^ 12 * J₀ + 2 : ℕ) : ℝ) ^ 2 * ρ ≤ CJ * s)
    (h₂ : E₀ + (24 * ((11 * 2 ^ 12 * J₀ : ℕ) : ℝ) ^ 5) *
      (4 * (40 * ((11 * 2 ^ 12 * J₀ + 2 : ℕ) : ℝ) ^ 2 * ρ)) ^ 2 ≤ CJ * s ^ 2) :
    ∃ Wt : F.GaugeField F.depth, D.IsFilledField C CJ idx o Wt := by
  classical
  have hpt : ∀ y ∈ D.coreCells C 5, ∀ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)),
      BlockAverages.plaquetteDefect D.fineField p ≤ ρ := by
    intro y hy p hp
    have h3 := Finset.single_le_sum (f := fun p => BlockAverages.plaquetteDefect D.fineField p ^ 2)
      (fun _ _ => sq_nonneg _) hp
    have h4 := (h3.trans (hquiet y hy)).trans hE
    exact (abs_le_of_sq_le_sq' h4 hρ).2
  set k := 40 * ((11 * 2 ^ 12 * J₀ + 2 : ℕ) : ℝ) ^ 2 * ρ with hk
  have hk0 : 0 ≤ k := by positivity
  have hG : ∀ Z ∈ D.coreBoxes C, ∃ G : F.Site F.depth → UnitQuaternion, (∀ x ∈ Z, G x = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
        ‖((_root_.YangMills.Construction.BlockAverages.gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ k := by
    intro Z hZ
    obtain ⟨y, hy, hZy, hm⟩ := mem_coreBoxes.mp hZ
    exact X.exists_flat_gauge hflat hρ hpt hy hZy hm
  choose! Gf hGf₁ hGf₂ using hG
  let Gh : F.Site F.depth → UnitQuaternion := fun x =>
    if h : ∃ Z ∈ D.coreBoxes C, x ∈ thicken 1 Z then Gf h.choose x else 1
  have hGh : ∀ Z ∈ D.coreBoxes C, ∀ x ∈ thicken 1 Z, Gh x = Gf Z x := by
    intro Z hZ x hx
    have h : ∃ Z ∈ D.coreBoxes C, x ∈ thicken 1 Z := ⟨Z, hZ, hx⟩
    simp only [Gh, dif_pos h]
    rw [X.eq_of_mem_thicken h.choose_spec.1 hZ h.choose_spec.2 hx]
  let Wt : F.GaugeField F.depth := fun x i =>
    if ∃ Z ∈ D.coreBoxes C, BondTouches Z (x, i) then (Gh x)⁻¹ * Gh (x + unitStep F.depth i)
    else D.fineField x i
  have hoff : ∀ b : F.Site F.depth × Fin 4, (∀ Z ∈ D.coreBoxes C, ¬ BondTouches Z b) →
      Wt b.1 b.2 = D.fineField b.1 b.2 := by
    rintro ⟨x, i⟩ hb
    have : ¬ ∃ Z ∈ D.coreBoxes C, BondTouches Z (x, i) := fun ⟨Z, hZ, hm⟩ => hb Z hZ hm
    simp only [Wt, if_neg this]
  have hfil : ∀ Z ∈ D.coreBoxes C,
      (∀ b : F.Site F.depth × Fin 4, BondTouches Z b → _root_.YangMills.Construction.BlockAverages.gaugeTransform Gh Wt b.1 b.2 = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
        ‖((_root_.YangMills.Construction.BlockAverages.gaugeTransform Gh D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ k := by
    intro Z hZ
    refine ⟨?_, ?_⟩
    · rintro ⟨x, i⟩ hm
      have h : ∃ Z ∈ D.coreBoxes C, BondTouches Z (x, i) := ⟨Z, hZ, hm⟩
      simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform, Wt, if_pos h]
      group
    · rintro ⟨x, i⟩ hb hb'
      have e₁ := hGh Z hZ x (Finset.mem_sdiff.mp hb).1
      have e₂ := hGh Z hZ _ (Finset.mem_sdiff.mp hb').1
      have := hGf₂ Z hZ (x, i) hb hb'
      simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform] at this ⊢
      rw [e₁, e₂]
      exact this
  refine ⟨Wt, ⟨fun y hy y' hy' hd Z hZ hm => X.mem_excludedBoxes_of_adj hy hy' hd hZ hm,
    fun Z hZ Z' hZ' hne => X.not_areWithin hZ hZ' hne,
    fun Z hZ => ?_, ⟨Gh, fun Z hZ => ⟨fun x hx => ?_, (hfil Z hZ).1,
      fun b hb hb' => ((hfil Z hZ).2 b hb hb').trans ?_⟩⟩,
    hoff, fun y hy y' hy' hd => ?_, fun y hy hemp => X.disjoint_of_nearbyLumps_eq_empty hy hemp⟩⟩
  · obtain ⟨y, hy, hZy, hm⟩ := mem_coreBoxes.mp hZ
    exact X.exists_hole_of_box hy hZy hm
  · rw [hGh Z hZ x (subset_thicken _ _ hx)]
    exact hGf₁ Z hZ x hx
  · exact h₁
  · exact (X.sum_plaquetteDefect_sq_le hk0 hfil hoff hquiet hy hy' hd).trans h₂
end FilledField
open FilledField in
theorem filledFieldStatement_holds (hcl : ExcludedBoxesAtUncrowdedCell)
    (hnb : ExcludedBoxesOfNeighboursAgree) (hflat : FlatGaugeOnBoxBoundary)
    (hq : quietCellCurvatureStatement) :
    filledFieldStatement := by
  intro J₀ a C hJ ha hC
  obtain ⟨K, hK, L₁, hq⟩ := hq
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((11 * 2 ^ 12 * J₀ : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((11 * 2 ^ 12 * J₀ + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = Real.sqrt (K * C) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ₀ := by rw [hρ₀]; exact Real.sqrt_nonneg _
  have hρsq : ρ₀ ^ 2 = K * C := by
    rw [hρ₀, Real.sq_sqrt (by positivity)]
  refine ⟨K * C + (24 * m ^ 5) * (4 * (40 * M ^ 2 * ρ₀)) ^ 2 + 40 * M ^ 2 * ρ₀ + 1, by positivity,
    max L₁ (4 * (11 * 2 ^ 12 * J₀) + 1), fun L hodd hL g => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
  refine ⟨1 / (2 * (L : ℝ) ^ 2 * (ρ₀ + 1)), by positivity, fun s hs hss θ F D hFL hcub idx o hst => ?_⟩
  subst hFL
  have hLmax₁ : L₁ ≤ F.blockSide := le_trans (le_max_left _ _) hL
  have hLmax₂ : 4 * (11 * 2 ^ 12 * J₀) + 1 ≤ F.blockSide := le_trans (le_max_right _ _) hL
  have hside : ∀ i, 4096 ≤ F.extent i := fun i => by
    have h1 := hcub.1 i
    have h2 := hcub.2
    omega
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by
    rw [period_depth]
    exact Nat.mul_ne_zero (by have := hside i; omega) hodd.pos.ne'⟩
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [period_top]
    have := hside i
    omega⟩
  have X : Setting D C idx o := ⟨hodd, hside, by omega, hJ, hst, hcl, hnb⟩
  have hsmall : K * C * s ^ 2 < (F.blockSide : ℝ) ^ (-4 : ℤ) := by
    have h1 : ρ₀ * s ≤ 1 / (2 * (F.blockSide : ℝ) ^ 2) := by
      have h2 : s * (2 * (F.blockSide : ℝ) ^ 2 * (ρ₀ + 1)) ≤ 1 := by
        rwa [le_div_iff₀ (by positivity)] at hss
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_pos hs (by positivity : (0 : ℝ) < 2 * (F.blockSide : ℝ) ^ 2)]
    have h3 : (ρ₀ * s) ^ 2 ≤ (1 / (2 * (F.blockSide : ℝ) ^ 2)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) h1
    have h4 : K * C * s ^ 2 = (ρ₀ * s) ^ 2 := by
      rw [mul_pow, hρsq]
    rw [h4]
    have h5 : (F.blockSide : ℝ) ^ (-4 : ℤ) = 1 / ((F.blockSide : ℝ) ^ 2) ^ 2 := by
      rw [zpow_neg]
      norm_cast
      rw [one_div, ← pow_mul]
    rw [h5]
    have h6 : (1 / (2 * (F.blockSide : ℝ) ^ 2)) ^ 2 = (1 / ((F.blockSide : ℝ) ^ 2) ^ 2) / 4 := by
      field_simp
      norm_num
    have h7 : 0 < 1 / ((F.blockSide : ℝ) ^ 2) ^ 2 := by positivity
    rw [h6] at h3
    linarith
  have hquiet : ∀ y ∈ D.coreCells C 5, ∑ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y 1)),
      BlockAverages.plaquetteDefect D.fineField p ^ 2 ≤ K * C * s ^ 2 := fun y hy =>
    hq a C s θ J₀ F.blockSide g F D ha hC hs hodd hLmax₁ rfl hcub hsmall y ((D.mem_coreCells).mp hy).1
      (D.not_mem_badCells_of_mem_coreCells (by omega) hy)
  have hsq : K * C * s ^ 2 ≤ (ρ₀ * s) ^ 2 := by
    rw [mul_pow, hρsq]
  refine X.exists_isFilledField hflat (by positivity) hsq hquiet ?_ ?_
  · rw [← hM]
    have : 40 * M ^ 2 * (ρ₀ * s) = (40 * M ^ 2 * ρ₀) * s := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ hs.le
    have : 0 ≤ K * C + (24 * m ^ 5) * (4 * (40 * M ^ 2 * ρ₀)) ^ 2 := by positivity
    linarith
  · rw [← hM, ← hm]
    have e : K * C * s ^ 2 + (24 * m ^ 5) * (4 * (40 * M ^ 2 * (ρ₀ * s))) ^ 2 =
        (K * C + (24 * m ^ 5) * (4 * (40 * M ^ 2 * ρ₀)) ^ 2) * s ^ 2 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ 40 * M ^ 2 * ρ₀ := by positivity
    linarith
end HoleSavings
end YangMills.Construction
end
