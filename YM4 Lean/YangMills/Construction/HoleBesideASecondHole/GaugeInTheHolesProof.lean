import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.HoleBesideASecondHole.GaugeInTheHoles
import YangMills.Construction.HoleBesideASecondHole.GaugeOnABoxOfTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleGauge
open BlockAverages
attribute [local irreducible] LumpContours.cellBall
variable {F : BlockFrame}
def fieldOnLattice (W : F.GaugeField F.depth) : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion :=
  fun a i => W (siteOfCoords F.depth a) i
def holeLower (H : Holes.Hole F) : Fin 4 → ℤ := fun i => siteCoords H.centre i - ((2 * H.radius : ℕ) : ℤ)
def holeUpper (H : Holes.Hole F) : Fin 4 → ℤ := fun i => siteCoords H.centre i + ((2 * H.radius : ℕ) : ℤ)
theorem outerBox_eq_boxSites (H : Holes.Hole F) :
    H.outerBox = LumpContours.boxSites F.depth (holeLower H) (holeUpper H) :=
  HoleSites.thicken_singleton _ _
def blockWall (L : ℕ) (lo hi : ℤ) : ℤ :=
  if lo - 1 + ((((L : ℤ) - 1) / 2 - (lo - 1)) % L) ≤ hi then lo - 1 + ((((L : ℤ) - 1) / 2 - (lo - 1)) % L) else lo - 1
theorem blockWall_spec {L : ℕ} (hodd : Odd L) {lo hi : ℤ} (hle : lo ≤ hi) (hw : hi - lo + 2 ≤ L) :
    lo - 1 ≤ blockWall L lo hi ∧ blockWall L lo hi ≤ hi ∧
      ∀ n : ℤ, (hi + 1 ≤ L * n + ((L : ℤ) - 1) / 2 ∨ L * n + ((L : ℤ) - 1) / 2 ≤ blockWall L lo hi) ∧
        (L * n + ((L : ℤ) - 1) / 2 + 1 ≤ lo - 1 ∨ blockWall L lo hi < L * n + ((L : ℤ) - 1) / 2 + 1) := by
  obtain ⟨k, hk⟩ := hodd
  have hLz : (L : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hh : ((L : ℤ) - 1) / 2 = k := by omega
  have hLp : (0 : ℤ) < L := by omega
  rw [hh]
  set r := ((k : ℤ) - (lo - 1)) % L with hr
  have r₀ : 0 ≤ r := Int.emod_nonneg _ hLp.ne'
  have r₁ : r < L := Int.emod_lt_of_pos _ hLp
  have hq := Int.emod_add_mul_ediv ((k : ℤ) - (lo - 1)) (L : ℤ)
  rw [← hr] at hq
  set q := ((k : ℤ) - (lo - 1)) / L with hqd
  have hv : ∀ n : ℤ, (L : ℤ) * n + k = lo - 1 + r + L * (n + q) := fun n => by
    have := mul_add (L : ℤ) n q
    linarith
  have up : ∀ n : ℤ, 1 ≤ n + q → lo - 1 + r + L ≤ L * n + k := fun n h => by
    have h1 := hv n
    have h2 : (L : ℤ) ≤ L * (n + q) := by nlinarith
    linarith
  have same : ∀ n : ℤ, 0 ≤ n + q → lo - 1 + r ≤ L * n + k := fun n h => by
    have h1 := hv n
    have h2 : (0 : ℤ) ≤ L * (n + q) := by positivity
    linarith
  have below : ∀ n : ℤ, n + q ≤ 0 → L * n + k ≤ lo - 1 + r := fun n h => by
    have h1 := hv n
    have h2 : (L : ℤ) * (n + q) ≤ 0 := by nlinarith
    linarith
  have down : ∀ n : ℤ, n + q ≤ -1 → L * n + k + L ≤ lo - 1 + r := fun n h => by
    have h1 := hv n
    have h2 : (L : ℤ) * (n + q) ≤ -L := by nlinarith
    linarith
  unfold blockWall
  rw [hh, ← hr]
  by_cases hW : lo - 1 + r ≤ hi
  · rw [if_pos hW]
    refine ⟨by omega, hW, fun n => ⟨?_, ?_⟩⟩
    · by_cases hd : n + q ≤ 0
      · exact Or.inr (below n hd)
      · have := up n (by omega)
        left
        omega
    · by_cases hd : 0 ≤ n + q
      · have := same n hd
        right
        omega
      · have := down n (by omega)
        left
        omega
  · rw [if_neg hW]
    refine ⟨le_rfl, by omega, fun n => ⟨?_, ?_⟩⟩
    · by_cases hd : 0 ≤ n + q
      · have := same n hd
        left
        omega
      · have := down n (by omega)
        right
        omega
    · by_cases hv' : lo - 1 < L * n + k + 1
      · exact Or.inr hv'
      · left
        omega
def holeWall (H : Holes.Hole F) : Fin 4 → ℤ := fun i => blockWall F.blockSide (holeLower H i) (holeUpper H i)
theorem mem_sitesBelow_of_abs_le (Y a : Fin 4 → ℤ)
    (h : ∀ l, |a l - F.blockSide * Y l| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    (siteOfCoords F.depth a : F.Site F.depth) ∈ LumpContours.sitesBelow F.depth (siteOfCoords F.top Y : F.Cell) := by
  refine BlockSites.mem_sitesBelow_iff.mpr
    ⟨fun l => a l - F.blockSide * Y l, h, BlockSites.siteOfCoords_eq_iff.mpr fun l => ?_⟩
  have h1 : ((Y l : ℤ) : ZMod (F.period F.top l)) =
      ((siteCoords (siteOfCoords F.top Y : F.Cell) l : ℤ) : ZMod (F.period F.top l)) := by
    rw [BlockSites.intCast_siteCoords]
    rfl
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  exact BlockSites.dvd_period_depth_of_dvd_period_top l h2 (by ring)
theorem eq_of_toSite_eq {lo hi : Fin 4 → ℤ} (hper : ∀ i, hi i - lo i + 2 ≤ F.period F.depth i) {a a' : Fin 4 → ℤ}
    (ha : a ∈ LatticeGauge.box lo hi) (ha' : a' ∈ LatticeGauge.box lo hi)
    (h : (siteOfCoords F.depth a : F.Site F.depth) = siteOfCoords F.depth a') : a = a' := by
  funext i
  have h1 := BlockSites.siteOfCoords_eq_iff.mp h i
  have h2 := ha i
  have h3 := ha' i
  have h4 := hper i
  have h5 := Int.eq_zero_of_abs_lt_dvd h1 (by
    rw [abs_lt]
    constructor <;> omega)
  omega
theorem toSite_add_unitVec {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfCoords j (a + LatticeGauge.unitVec i) : F.Site j) = siteOfCoords j a + unitStep j i :=
  BlockSites.siteOfCoords_add a _
theorem plaquetteHolonomy_expand {j : ℕ} (W : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    BlockAverages.plaquetteHolonomy W (x, μ, ν) =
      W x μ * W (x + unitStep j μ) ν * (W (x + unitStep j ν) μ)⁻¹ * (W x ν)⁻¹ := by
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + -unitStep j μ - unitStep j ν = x := by abel
  simp only [BlockAverages.plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true,
    Bool.false_eq_true, if_false, e1, e2, mul_one]
  group
theorem plaquetteHolonomy_fieldOnLattice (W : F.GaugeField F.depth) (a : Fin 4 → ℤ) (μ ν : Fin 4) :
    LatticeGauge.plaquetteHolonomy (fieldOnLattice W) a μ ν =
      BlockAverages.plaquetteHolonomy W (siteOfCoords F.depth a, μ, ν) := by
  rw [plaquetteHolonomy_expand]
  simp only [LatticeGauge.plaquetteHolonomy, fieldOnLattice, toSite_add_unitVec]
theorem mem_box_widen_iff {lo hi x : Fin 4 → ℤ} :
    x ∈ LatticeGauge.box (lo - 1) (hi + 1) ↔ ∀ l, lo l - 1 ≤ x l ∧ x l ≤ hi l + 1 := by
  simp [LatticeGauge.box]
structure GaugeHypotheses (𝓗 : Finset (Holes.Hole F)) (Cc : Finset F.Cell) (A B : F.GaugeField F.depth) (E : ℝ) :
    Prop where
  blockSide_odd : Odd F.blockSide
  extent_ge : ∀ i, 4096 ≤ F.extent i
  E_nonneg : 0 ≤ E
  radius_bounds : ∀ H ∈ 𝓗, 99 ≤ H.radius ∧ 100 * H.radius ^ 2 ≤ F.blockSide
  holes_apart : ∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' →
      ¬ LumpContours.AreWithin (5 * max H.radius H'.radius) H.outerBox H'.outerBox
  agree_off_holes : ∀ b ∈ LumpContours.cutBonds (LumpContours.cutBelow F.depth Cc),
      b.1 ∉ Holes.holeSupport 𝓗 → b.1 + unitStep F.depth b.2 ∉ Holes.holeSupport 𝓗 → A b.1 b.2 = B b.1 b.2
  defect_left : ∀ y ∈ Cc, ∀ y' ∈ Cc, cellSupDist y y' ≤ 1 →
      ∑ p ∈ LumpContours.cutPlaquettes (LumpContours.sitesBelow F.depth y ∪ LumpContours.sitesBelow F.depth y'),
        BlockAverages.plaquetteDefect A p ^ 2 ≤ E ^ 2
  defect_right : ∀ y ∈ Cc, ∀ y' ∈ Cc, cellSupDist y y' ≤ 1 →
      ∑ p ∈ LumpContours.cutPlaquettes (LumpContours.sitesBelow F.depth y ∪ LumpContours.sitesBelow F.depth y'),
        BlockAverages.plaquetteDefect B p ^ 2 ≤ E ^ 2
variable {𝓗 : Finset (Holes.Hole F)} {Cc : Finset F.Cell} {A B : F.GaugeField F.depth} {E : ℝ}
theorem GaugeHypotheses.extent_pos (S : GaugeHypotheses 𝓗 Cc A B E) (i : Fin 4) : 0 < F.extent i := by
  have := S.extent_ge i
  omega
theorem GaugeHypotheses.period_ge (S : GaugeHypotheses 𝓗 Cc A B E) (i : Fin 4) :
    8 * (F.blockSide : ℤ) ≤ F.period F.depth i := by
  rw [BlockSites.period_depth]
  have h2 : 8 * F.blockSide ≤ F.extent i * F.blockSide :=
    Nat.mul_le_mul_right _ (by have := S.extent_ge i; omega)
  exact_mod_cast h2
theorem GaugeHypotheses.hole_width_le (S : GaugeHypotheses 𝓗 Cc A B E) {H : Holes.Hole F} (hH : H ∈ 𝓗) :
    4 * H.radius + 6 ≤ F.blockSide := by
  have h := S.radius_bounds H hH
  nlinarith [h.1, h.2]
theorem holeUpper_sub_holeLower (H : Holes.Hole F) (i : Fin 4) :
    holeUpper H i - holeLower H i = 4 * (H.radius : ℤ) := by
  simp only [holeUpper, holeLower]
  push_cast
  ring
theorem GaugeHypotheses.widened_width_le (S : GaugeHypotheses 𝓗 Cc A B E) {H : Holes.Hole F} (hH : H ∈ 𝓗)
    (i : Fin 4) : (holeUpper H + 1) i - (holeLower H - 1) i + 2 ≤ F.period F.depth i := by
  have h1 := S.period_ge i
  have h2 := holeUpper_sub_holeLower H i
  have h3 := S.hole_width_le hH
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  omega
theorem mem_box_widen {lo hi : Fin 4 → ℤ} {a : Fin 4 → ℤ} (h : a ∈ LatticeGauge.box lo hi) :
    a ∈ LatticeGauge.box (lo - 1) (hi + 1) := by
  intro l
  have := h l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  omega
theorem GaugeHypotheses.hole_eq_of_mem [∀ i, NeZero (F.period F.depth i)] (S : GaugeHypotheses 𝓗 Cc A B E)
    {H H' : Holes.Hole F} (hH : H ∈ 𝓗) (hH' : H' ∈ 𝓗)
    {x : F.Site F.depth} (hx : x ∈ H.outerBox) (hx' : x ∈ H'.outerBox) : H = H' := by
  by_contra hne
  refine S.holes_apart H hH H' hH' hne ⟨x, hx, x, hx', ?_⟩
  simp [LumpContours.supDist]
theorem GaugeHypotheses.not_mem_holeSupport [∀ i, NeZero (F.period F.depth i)] (S : GaugeHypotheses 𝓗 Cc A B E)
    {H : Holes.Hole F} (hH : H ∈ 𝓗) {a : Fin 4 → ℤ}
    (hd : a ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1))
    (hn : a ∉ LatticeGauge.box (holeLower H) (holeUpper H)) :
    (siteOfCoords F.depth a : F.Site F.depth) ∉ Holes.holeSupport 𝓗 := by
  intro hin
  obtain ⟨H', hH', hx⟩ := Finset.mem_biUnion.mp hin
  by_cases he : H' = H
  · subst he
    rw [outerBox_eq_boxSites] at hx
    obtain ⟨b, hb, e⟩ := (CornerBoxes.mem_boxOfCorners (q := (holeLower H', holeUpper H'))).mp hx
    have hbb : b ∈ LatticeGauge.box (holeLower H') (holeUpper H') := hb
    have := eq_of_toSite_eq (S.widened_width_le hH) (mem_box_widen hbb) hd e
    exact hn (this ▸ hbb)
  · have hle : ∀ l, holeLower H l ≤ holeUpper H l := fun l => by
      have := holeUpper_sub_holeLower H l
      omega
    let z : Fin 4 → ℤ := fun l => max (holeLower H l) (min (holeUpper H l) (a l))
    have hz : z ∈ LatticeGauge.box (holeLower H) (holeUpper H) := fun l =>
      ⟨le_max_left _ _, max_le (hle l) (min_le_left _ _)⟩
    have hzo : (siteOfCoords F.depth z : F.Site F.depth) ∈ H.outerBox := by
      rw [outerBox_eq_boxSites]
      exact (CornerBoxes.mem_boxOfCorners (q := (holeLower H, holeUpper H))).mpr ⟨z, hz, rfl⟩
    have hzd : ∀ l, |(a - z) l| ≤ ((1 : ℕ) : ℤ) := by
      intro l
      have := mem_box_widen_iff.mp hd l
      have h2 := hle l
      simp only [Pi.sub_apply, z]
      rw [abs_le]
      rcases le_total (holeUpper H l) (a l) with c1 | c1 <;>
        rcases le_total (holeLower H l) (min (holeUpper H l) (a l)) with c2 | c2 <;>
        simp only [min_eq_left c1, min_eq_right c1, max_eq_left c2, max_eq_right c2] at c2 ⊢ <;>
        push_cast <;> omega
    have e : (siteOfCoords F.depth a : F.Site F.depth) = siteOfCoords F.depth z + siteOfCoords F.depth (a - z) := by
      rw [← BlockSites.siteOfCoords_add]
      congr 1
      abel
    have hdist : LumpContours.supDist (siteOfCoords F.depth z : F.Site F.depth) (siteOfCoords F.depth a) ≤ 1 := by
      rw [e]
      refine BlockSites.supDist_add_le hzd fun l => ?_
      have h1 := S.period_ge l
      have h3 := S.hole_width_le hH
      have h4 : (6 : ℤ) ≤ (F.blockSide : ℤ) := by exact_mod_cast (by omega : 6 ≤ F.blockSide)
      push_cast
      omega
    refine S.holes_apart H hH H' hH' (Ne.symm he) ⟨_, hzo, _, hx, hdist.trans ?_⟩
    have := (S.radius_bounds H hH).1
    have h5 : H.radius ≤ max H.radius H'.radius := le_max_left _ _
    omega
theorem GaugeHypotheses.sum_sq_defect_le (S : GaugeHypotheses 𝓗 Cc A B E) (X : F.GaugeField F.depth)
    {y₁ y₂ : F.Cell}
    (hX : ∑ p ∈ LumpContours.cutPlaquettes (LumpContours.sitesBelow F.depth y₁ ∪ LumpContours.sitesBelow F.depth y₂),
      BlockAverages.plaquetteDefect X p ^ 2 ≤ E ^ 2)
    {kl kh : Fin 4 → ℤ} (hper : ∀ i, kh i - kl i + 2 ≤ F.period F.depth i)
    (hK : ∀ x ∈ LatticeGauge.box kl kh,
      (siteOfCoords F.depth x : F.Site F.depth) ∈ LumpContours.sitesBelow F.depth y₁ ∪ LumpContours.sitesBelow F.depth y₂)
    (Q : Finset ((Fin 4 → ℤ) × Fin 4)) (hQ : ∀ q ∈ Q, q ∈ BoxGauge.firstAxisPlaquettes kl kh) :
    ∑ q ∈ Q, LatticeGauge.plaquetteDefect (fieldOnLattice X) q.1 0 q.2 ^ 2 ≤ E ^ 2 := by
  classical
  let φ : (Fin 4 → ℤ) × Fin 4 → F.Site F.depth × Fin 4 × Fin 4 := fun q => (siteOfCoords F.depth q.1, 0, q.2)
  have hinj : Set.InjOn φ Q := by
    intro q hq q' hq' he
    have h1 : (siteOfCoords F.depth q.1 : F.Site F.depth) = siteOfCoords F.depth q'.1 := congrArg Prod.fst he
    have h2 : q.2 = q'.2 := congrArg (fun p : F.Site F.depth × Fin 4 × Fin 4 => p.2.2) he
    exact Prod.ext (eq_of_toSite_eq hper (hQ q hq).2.1 (hQ q' hq').2.1 h1) h2
  have e : ∑ q ∈ Q, LatticeGauge.plaquetteDefect (fieldOnLattice X) q.1 0 q.2 ^ 2 =
      ∑ p ∈ Q.image φ, BlockAverages.plaquetteDefect X p ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LatticeGauge.plaquetteDefect, plaquetteHolonomy_fieldOnLattice]
    rfl
  rw [e]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _) hX
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := hQ q hq
  have hlt : (0 : Fin 4) < q.2 := Fin.pos_iff_ne_zero.mpr h₀
  have base := hK _ h₁
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨base, by simp⟩, hlt, fun x hx => ?_⟩
  simp only [plaquetteCorners, φ, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact base
  · have := hK _ h₂
    rwa [toSite_add_unitVec] at this
  · have := hK _ h₃
    rwa [toSite_add_unitVec] at this
  · have := hK _ h₄
    rwa [toSite_add_unitVec, toSite_add_unitVec] at this
theorem GaugeHypotheses.bond_near_hole [∀ i, NeZero (F.period F.depth i)] [∀ i, NeZero (F.period F.top i)]
    (S : GaugeHypotheses 𝓗 Cc A B E)
    (hbox : BoxGauge.GaugeFixedNearBox) {H : Holes.Hole F} (hH : H ∈ 𝓗) (a : Fin 4 → ℤ) (i : Fin 4)
    (hd : a ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1))
    (hd' : a + LatticeGauge.unitVec i ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1))
    (hy : enclosingCell (siteOfCoords F.depth a : F.Site F.depth) ∈ Cc)
    (hy' : enclosingCell (siteOfCoords F.depth (a + LatticeGauge.unitVec i) : F.Site F.depth) ∈ Cc) :
    LatticeGauge.quatDist
        (BoxGauge.boxGaugeTransform (fieldOnLattice A) (fieldOnLattice B) (holeLower H) (holeUpper H) (holeWall H) a *
          fieldOnLattice A a i *
          (BoxGauge.boxGaugeTransform (fieldOnLattice A) (fieldOnLattice B) (holeLower H) (holeUpper H) (holeWall H)
            (a + LatticeGauge.unitVec i))⁻¹) (fieldOnLattice B a i) ≤
      2 * ((4 * H.radius + 3 : ℕ) : ℝ) * E := by
  classical
  obtain ⟨k, hk⟩ := S.blockSide_odd
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by omega
  have hLp : (0 : ℤ) < F.blockSide := by omega
  let Y : Fin 4 → ℤ := fun l => (a l + k) / F.blockSide
  have hY : ∀ l, -(k : ℤ) ≤ a l - F.blockSide * Y l ∧ a l - F.blockSide * Y l ≤ k := by
    intro l
    have h1 := Int.emod_add_mul_ediv (a l + k) (F.blockSide : ℤ)
    have h2 := Int.emod_nonneg (a l + k) hLp.ne'
    have h3 := Int.emod_lt_of_pos (a l + k) hLp
    simp only [Y]
    constructor <;> linarith
  let Y₂ : Fin 4 → ℤ := if a i - F.blockSide * Y i = k then Y + LatticeGauge.unitVec i else Y
  have hcoordi : ∀ l, (a + LatticeGauge.unitVec i) l = a l + if l = i then 1 else 0 := fun l => by
    by_cases hl : l = i
    · subst hl
      simp [LatticeGauge.unitVec]
    · simp [LatticeGauge.unitVec, hl]
  have hY₂ : ∀ l, Y₂ l = Y l + if l = i ∧ a i - F.blockSide * Y i = k then 1 else 0 := fun l => by
    by_cases hc : a i - F.blockSide * Y i = k
    · simp only [Y₂, if_pos hc]
      by_cases hl : l = i
      · subst hl
        simp [LatticeGauge.unitVec, hc]
      · simp [LatticeGauge.unitVec, hl]
    · simp [Y₂, if_neg hc, hc]
  have hY₂a : ∀ l, -(k : ℤ) ≤ (a + LatticeGauge.unitVec i) l - F.blockSide * Y₂ l ∧
      (a + LatticeGauge.unitVec i) l - F.blockSide * Y₂ l ≤ k := by
    intro l
    rw [hcoordi, hY₂]
    have h1 := hY l
    by_cases hl : l = i
    · subst hl
      by_cases hc : a l - F.blockSide * Y l = k
      · simp only [if_true, hc, and_self, true_and]
        rw [mul_add]
        constructor <;> linarith
      · simp only [if_true, hc, and_false, if_false, true_and, add_zero]
        constructor <;> omega
    · simp only [hl, if_false, false_and, add_zero]
      exact h1
  let y₁ : F.Cell := siteOfCoords F.top Y
  let y₂ : F.Cell := siteOfCoords F.top Y₂
  have m₁ : (siteOfCoords F.depth a : F.Site F.depth) ∈ LumpContours.sitesBelow F.depth y₁ :=
    mem_sitesBelow_of_abs_le Y a fun l => by
      rw [hh, abs_le]
      exact hY l
  have m₂ : (siteOfCoords F.depth (a + LatticeGauge.unitVec i) : F.Site F.depth) ∈
      LumpContours.sitesBelow F.depth y₂ :=
    mem_sitesBelow_of_abs_le Y₂ _ fun l => by
      rw [hh, abs_le]
      exact hY₂a l
  have c₁ : y₁ ∈ Cc := by
    have := BlockSites.enclosingCell_eq_of_mem_sitesBelow S.blockSide_odd S.extent_pos m₁
    rwa [this] at hy
  have c₂ : y₂ ∈ Cc := by
    have := BlockSites.enclosingCell_eq_of_mem_sitesBelow S.blockSide_odd S.extent_pos m₂
    rwa [this] at hy'
  have hdist : cellSupDist y₁ y₂ ≤ 1 := by
    by_cases hc : a i - F.blockSide * Y i = k
    · have e : y₂ = y₁ + siteOfCoords F.top (LatticeGauge.unitVec i) := by
        simp only [y₂, y₁, Y₂, if_pos hc]
        exact BlockSites.siteOfCoords_add _ _
      rw [e]
      refine BlockSites.cellSupDist_add_le (m := 1) (fun l => ?_) fun l => ?_
      · by_cases hl : l = i
        · subst hl
          simp [LatticeGauge.unitVec]
        · simp [LatticeGauge.unitVec, hl]
      · rw [BlockSites.period_top]
        have := S.extent_ge l
        push_cast
        omega
    · have e : y₂ = y₁ := by
        simp only [y₂, y₁, Y₂, if_neg hc]
      rw [e, HoleSites.cellSupDist_self]
      omega
  let kl : Fin 4 → ℤ := fun l => F.blockSide * Y l - k
  let kh : Fin 4 → ℤ := fun l => F.blockSide * Y₂ l + k
  have hK : ∀ x ∈ LatticeGauge.box kl kh, (siteOfCoords F.depth x : F.Site F.depth) ∈
      LumpContours.sitesBelow F.depth y₁ ∪ LumpContours.sitesBelow F.depth y₂ := by
    intro x hx
    by_cases hfirst : ∀ l, x l ≤ F.blockSide * Y l + k
    · refine Finset.mem_union_left _ (mem_sitesBelow_of_abs_le Y x fun l => ?_)
      have h1 := (hx l).1
      have h2 := hfirst l
      simp only [kl] at h1
      rw [hh, abs_le]
      constructor <;> linarith
    · push_neg at hfirst
      obtain ⟨l₀, hl₀⟩ := hfirst
      have h₀ := (hx l₀).2
      simp only [kh] at h₀
      rw [hY₂] at h₀
      have hc : l₀ = i ∧ a i - F.blockSide * Y i = k := by
        by_contra hno
        rw [if_neg hno, add_zero] at h₀
        omega
      refine Finset.mem_union_right _ (mem_sitesBelow_of_abs_le Y₂ x fun l => ?_)
      have h1 := (hx l).1
      have h2 := (hx l).2
      simp only [kl, kh] at h1 h2
      rw [hh, abs_le]
      by_cases hl : l = i
      · subst hl
        have e₀ := hc.1
        subst e₀
        have e := hY₂ l₀
        rw [if_pos ⟨rfl, hc.2⟩] at e
        rw [e] at h2 ⊢
        rw [mul_add] at h2 ⊢
        constructor <;> linarith
      · have e : Y₂ l = Y l := by
          rw [hY₂, if_neg fun h => hl h.1, add_zero]
        rw [e] at h2 ⊢
        constructor <;> linarith
  have hper : ∀ l, kh l - kl l + 2 ≤ F.period F.depth l := by
    intro l
    have h1 := S.period_ge l
    simp only [kh, kl]
    rw [hY₂]
    have h2 : (F.blockSide : ℤ) * (Y l + if l = i ∧ a i - F.blockSide * Y i = k then 1 else 0) ≤
        F.blockSide * Y l + F.blockSide := by
      split_ifs <;> nlinarith
    omega
  have hrad := S.radius_bounds H hH
  have hwidth := S.hole_width_le hH
  have hle : ∀ l, holeLower H l ≤ holeUpper H l := fun l => by
    have := holeUpper_sub_holeLower H l
    omega
  have ws : ∀ l, holeUpper H l - holeLower H l + 2 ≤ (F.blockSide : ℤ) := fun l => by
    have := holeUpper_sub_holeLower H l
    omega
  have wall := fun l => blockWall_spec S.blockSide_odd (hle l) (ws l)
  rw [hh] at *
  have hkl : ∀ l, kl l = F.blockSide * (Y l - 1) + k + 1 := fun l => by
    simp only [kl]
    rw [hLz]
    ring
  have hKa : a ∈ LatticeGauge.box kl kh := fun l => by
    have h1 := hY l
    simp only [kl, kh]
    rw [hY₂]
    have h2 : (F.blockSide : ℤ) * Y l ≤
        F.blockSide * (Y l + if l = i ∧ a i - F.blockSide * Y i = k then 1 else 0) := by
      split_ifs <;> nlinarith
    constructor <;> linarith
  have hKa' : a + LatticeGauge.unitVec i ∈ LatticeGauge.box kl kh := fun l => by
    have h1 := hY₂a l
    have h3 := hY l
    have h4 := hcoordi l
    simp only [kl, kh]
    refine ⟨?_, by linarith⟩
    rw [h4]
    split_ifs <;> linarith
  have hoff : ∀ a' j, a' ∈ LatticeGauge.box kl kh → a' + LatticeGauge.unitVec j ∈ LatticeGauge.box kl kh →
      a' ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1) →
      a' + LatticeGauge.unitVec j ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1) →
      a' ∉ LatticeGauge.box (holeLower H) (holeUpper H) →
      a' + LatticeGauge.unitVec j ∉ LatticeGauge.box (holeLower H) (holeUpper H) →
      fieldOnLattice A a' j = fieldOnLattice B a' j := by
    intro a' j k₁ k₂ d₁ d₂ n₁ n₂
    have inCc : ∀ x ∈ LatticeGauge.box kl kh,
        (siteOfCoords F.depth x : F.Site F.depth) ∈ LumpContours.cutBelow F.depth Cc := by
      intro x hx
      rcases Finset.mem_union.mp (hK x hx) with h | h
      · exact Finset.mem_biUnion.mpr ⟨y₁, c₁, h⟩
      · exact Finset.mem_biUnion.mpr ⟨y₂, c₂, h⟩
    have hb : ((siteOfCoords F.depth a' : F.Site F.depth), j) ∈
        LumpContours.cutBonds (LumpContours.cutBelow F.depth Cc) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨inCc _ k₁, by simp⟩, ?_⟩
      have := inCc _ k₂
      rwa [toSite_add_unitVec] at this
    have o₂ := S.not_mem_holeSupport hH d₂ n₂
    rw [toSite_add_unitVec] at o₂
    exact S.agree_off_holes _ hb (S.not_mem_holeSupport hH d₁ n₁) o₂
  exact_mod_cast hbox (fieldOnLattice A) (fieldOnLattice B) (holeLower H) (holeUpper H) (holeWall H) kl kh
    (4 * H.radius + 3) E
    (fun l => ⟨hle l, by
      have := holeUpper_sub_holeLower H l
      push_cast
      omega⟩) S.E_nonneg
    (wall 0).1 (wall 0).2.1 (wall 1).1 (wall 1).2.1
    ((wall 0).2.2 (Y₂ 0)).1 (by
      have := ((wall 0).2.2 (Y 0 - 1)).2
      rw [← hkl] at this
      exact this)
    ((wall 1).2.2 (Y₂ 1)).1 (by
      have := ((wall 1).2.2 (Y 1 - 1)).2
      rw [← hkl] at this
      exact this)
    hoff
    (S.sum_sq_defect_le A (S.defect_left y₁ c₁ y₂ c₂ hdist) hper hK)
    (S.sum_sq_defect_le B (S.defect_right y₁ c₁ y₂ c₂ hdist) hper hK)
    a i hKa hKa' hd hd'
def holeGaugeTransform (A B : F.GaugeField F.depth) (H : Holes.Hole F) (x : F.Site F.depth) : UnitQuaternion := by
  classical
  exact
    if h : ∃ a, a ∈ LatticeGauge.box (holeLower H) (holeUpper H) ∧ (siteOfCoords F.depth a : F.Site F.depth) = x then
      BoxGauge.boxGaugeTransform (fieldOnLattice A) (fieldOnLattice B) (holeLower H) (holeUpper H) (holeWall H)
        h.choose
    else 1
def holesGauge (𝓗 : Finset (Holes.Hole F)) (A B : F.GaugeField F.depth) (x : F.Site F.depth) : UnitQuaternion := by
  classical exact if h : ∃ H ∈ 𝓗, x ∈ H.outerBox then holeGaugeTransform A B h.choose x else 1
theorem GaugeHypotheses.holesGauge_eq [∀ i, NeZero (F.period F.depth i)] (S : GaugeHypotheses 𝓗 Cc A B E)
    {H : Holes.Hole F} (hH : H ∈ 𝓗) {a : Fin 4 → ℤ}
    (hd : a ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1)) :
    holesGauge 𝓗 A B (siteOfCoords F.depth a) =
      BoxGauge.boxGaugeTransform (fieldOnLattice A) (fieldOnLattice B) (holeLower H) (holeUpper H) (holeWall H) a := by
  classical
  by_cases ha : a ∈ LatticeGauge.box (holeLower H) (holeUpper H)
  · have hx : (siteOfCoords F.depth a : F.Site F.depth) ∈ H.outerBox := by
      rw [outerBox_eq_boxSites]
      exact (CornerBoxes.mem_boxOfCorners (q := (holeLower H, holeUpper H))).mpr ⟨a, ha, rfl⟩
    have h : ∃ H ∈ 𝓗, (siteOfCoords F.depth a : F.Site F.depth) ∈ H.outerBox := ⟨H, hH, hx⟩
    have e : h.choose = H := S.hole_eq_of_mem h.choose_spec.1 hH h.choose_spec.2 hx
    have h₂ : ∃ a', a' ∈ LatticeGauge.box (holeLower H) (holeUpper H) ∧
        (siteOfCoords F.depth a' : F.Site F.depth) = siteOfCoords F.depth a := ⟨a, ha, rfl⟩
    have e₂ : h₂.choose = a :=
      eq_of_toSite_eq (S.widened_width_le hH) (mem_box_widen h₂.choose_spec.1) hd h₂.choose_spec.2
    simp only [holesGauge, dif_pos h, e, holeGaugeTransform, dif_pos h₂, e₂]
  · have hn := S.not_mem_holeSupport hH hd ha
    have h : ¬ ∃ H ∈ 𝓗, (siteOfCoords F.depth a : F.Site F.depth) ∈ H.outerBox := fun ⟨H', hH', hx⟩ =>
      hn (Finset.mem_biUnion.mpr ⟨H', hH', hx⟩)
    simp only [holesGauge, dif_neg h, BoxGauge.boxGaugeTransform, if_neg ha]
theorem holeGaugeStatement_holds (hbox : BoxGauge.GaugeFixedNearBox) : holeGaugeStatement := by
  classical
  intro F 𝓗 Cc A B E hodd hside hE hrad hap hagree hA hB
  have S : GaugeHypotheses 𝓗 Cc A B E := ⟨hodd, hside, hE, hrad, hap, hagree, hA, hB⟩
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by
    rw [BlockSites.period_depth]
    exact Nat.mul_ne_zero (S.extent_pos i).ne' hodd.pos.ne'⟩
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [BlockSites.period_top]
    exact (S.extent_pos i).ne'⟩
  refine ⟨holesGauge 𝓗 A B, fun x hx => ?_, ?_⟩
  · have h : ¬ ∃ H ∈ 𝓗, x ∈ H.outerBox := fun ⟨H', hH', hx'⟩ => hx (Finset.mem_biUnion.mpr ⟨H', hH', hx'⟩)
    simp only [holesGauge, dif_neg h]
  rintro ⟨x, i⟩ hy hy'
  simp only at hy hy' ⊢
  have hone : ∀ x, x ∉ Holes.holeSupport 𝓗 → holesGauge 𝓗 A B x = 1 := fun x hx => by
    have h : ¬ ∃ H ∈ 𝓗, x ∈ H.outerBox := fun ⟨H', hH', hx'⟩ => hx (Finset.mem_biUnion.mpr ⟨H', hH', hx'⟩)
    simp only [holesGauge, dif_neg h]
  have hbound : ∀ H ∈ 𝓗, 2 * ((4 * H.radius + 3 : ℕ) : ℝ) * E ≤ Real.sqrt F.blockSide * E := by
    intro H hH
    refine mul_le_mul_of_nonneg_right ?_ hE
    refine Real.le_sqrt_of_sq_le ?_
    have h1 := hrad H hH
    have h2 : (2 * (4 * H.radius + 3)) ^ 2 ≤ F.blockSide := by nlinarith [h1.1, h1.2]
    have h3 : (((2 * (4 * H.radius + 3)) ^ 2 : ℕ) : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast h2
    push_cast at h3 ⊢
    linarith
  have lift : ∀ H ∈ 𝓗, ∀ z ∈ H.outerBox, ∃ c, c ∈ LatticeGauge.box (holeLower H) (holeUpper H) ∧
      (siteOfCoords F.depth c : F.Site F.depth) = z := by
    intro H _ z hz
    rw [outerBox_eq_boxSites] at hz
    obtain ⟨c, hc, e⟩ := (CornerBoxes.mem_boxOfCorners (q := (holeLower H, holeUpper H))).mp hz
    exact ⟨c, hc, e⟩
  have finish : ∀ H ∈ 𝓗, ∀ a : Fin 4 → ℤ, (siteOfCoords F.depth a : F.Site F.depth) = x →
      a ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1) →
      a + LatticeGauge.unitVec i ∈ LatticeGauge.box (holeLower H - 1) (holeUpper H + 1) →
      ‖((gaugeTransform (holesGauge 𝓗 A B) A x i : UnitQuaternion) : ℍ[ℝ]) - ((B x i : UnitQuaternion) : ℍ[ℝ])‖ ≤
        Real.sqrt F.blockSide * E := by
    rintro H hH a rfl hd hd'
    have h1 := S.bond_near_hole hbox hH a i hd hd' hy (by rwa [toSite_add_unitVec])
    have g₁ := S.holesGauge_eq hH hd
    have g₂ := S.holesGauge_eq hH hd'
    have e₀ : ‖((gaugeTransform (holesGauge 𝓗 A B) A (siteOfCoords F.depth a) i : UnitQuaternion) : ℍ[ℝ]) -
          ((B (siteOfCoords F.depth a) i : UnitQuaternion) : ℍ[ℝ])‖ =
        LatticeGauge.quatDist (gaugeTransform (holesGauge 𝓗 A B) A (siteOfCoords F.depth a) i)
          (B (siteOfCoords F.depth a) i) :=
      rfl
    rw [e₀]
    simp only [gaugeTransform]
    rw [← toSite_add_unitVec, g₁, g₂]
    exact h1.trans (hbound H hH)
  by_cases hx : x ∈ Holes.holeSupport 𝓗
  · obtain ⟨H, hH, hxH⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨c, hc, e⟩ := lift H hH x hxH
    refine finish H hH c e (mem_box_widen hc) (mem_box_widen_iff.mpr fun l => ?_)
    have h1 := hc l
    by_cases hl : l = i
    · subst hl
      simp [LatticeGauge.unitVec]
      omega
    · simp [LatticeGauge.unitVec, hl]
      omega
  by_cases hx' : x + unitStep F.depth i ∈ Holes.holeSupport 𝓗
  · obtain ⟨H, hH, hxH⟩ := Finset.mem_biUnion.mp hx'
    obtain ⟨c, hc, e⟩ := lift H hH _ hxH
    refine finish H hH (c - LatticeGauge.unitVec i) ?_ (mem_box_widen_iff.mpr fun l => ?_)
      (mem_box_widen (by simpa using hc))
    · have h1 : (siteOfCoords F.depth (c - LatticeGauge.unitVec i + LatticeGauge.unitVec i) : F.Site F.depth) =
          x + unitStep F.depth i := by
        rw [sub_add_cancel]
        exact e
      rw [toSite_add_unitVec] at h1
      exact add_right_cancel h1
    · have h1 := hc l
      by_cases hl : l = i
      · subst hl
        simp [LatticeGauge.unitVec]
        omega
      · simp [LatticeGauge.unitVec, hl]
        omega
  · have hb : (x, i) ∈ LumpContours.cutBonds (LumpContours.cutBelow F.depth Cc) := by
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(BlockSites.mem_cutBelow_iff hodd S.extent_pos).mpr hy, by simp⟩, ?_⟩
      exact (BlockSites.mem_cutBelow_iff hodd S.extent_pos).mpr hy'
    have he := hagree _ hb hx hx'
    have e₁ := hone x hx
    have e₂ := hone _ hx'
    simp only at he
    simp only [gaugeTransform, e₁, e₂, he]
    simp
    exact mul_nonneg (Real.sqrt_nonneg _) hE
end YangMills.Construction.HoleGauge
end
