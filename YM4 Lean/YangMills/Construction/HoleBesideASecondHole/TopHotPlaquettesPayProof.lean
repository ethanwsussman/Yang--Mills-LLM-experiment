import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChainProof
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPay
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours
namespace HoleSavings
namespace TopHotPlaquetteCost
variable {F : BlockFrame}
section offsets
variable {L : ℕ} (hL : Odd L)
include hL
theorem abs_offsetFromCentre_le (c : ℤ) : |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by
  obtain ⟨q, rfl⟩ := hL
  have hh : (((2 * q + 1 : ℕ) : ℤ) - 1) / 2 = q := by
    push_cast
    omega
  unfold offsetFromCentre
  rw [hh]
  have h1 := Int.emod_nonneg (c + q) (show ((2 * q + 1 : ℕ) : ℤ) ≠ 0 by positivity)
  have h2 := Int.emod_lt_of_pos (c + q) (show (0 : ℤ) < ((2 * q + 1 : ℕ) : ℤ) by positivity)
  push_cast at h1 h2 ⊢
  rw [abs_le]
  constructor <;> omega
theorem dvd_sub_offsetFromCentre (c : ℤ) : (L : ℤ) ∣ c - offsetFromCentre L c := by
  unfold offsetFromCentre
  refine ⟨(c + ((L : ℤ) - 1) / 2) / L, ?_⟩
  have := Int.emod_add_mul_ediv (c + ((L : ℤ) - 1) / 2) L
  linarith
theorem offsetFromCentre_add (t o : ℤ) (ht : (L : ℤ) ∣ t) (ho : |o| ≤ ((L : ℤ) - 1) / 2) :
    offsetFromCentre L (t + o) = o := by
  obtain ⟨q, rfl⟩ := hL
  have hh : (((2 * q + 1 : ℕ) : ℤ) - 1) / 2 = q := by
    push_cast
    omega
  rw [hh] at ho
  unfold offsetFromCentre
  rw [hh]
  have ho' := abs_le.1 ho
  obtain ⟨r, rfl⟩ := ht
  have e : ((2 * q + 1 : ℕ) : ℤ) * r + o + q = (o + q) + ((2 * q + 1 : ℕ) : ℤ) * r := by ring
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  ring
end offsets
def lumpLower {L : ℕ} (g : LumpGrid L) (c : ℤ) : ℤ := c - offsetFromCentre L c + g.lower (offsetFromCentre L c)
def lumpUpper {L : ℕ} (g : LumpGrid L) (c : ℤ) : ℤ := c - offsetFromCentre L c + g.upper (offsetFromCentre L c)
section lumpBounds
variable {L : ℕ} (g : LumpGrid L) (hL : Odd L)
include hL
theorem lumpLower_le (c : ℤ) : lumpLower g c ≤ c := by
  have := (g.mem_interval _ (abs_offsetFromCentre_le hL c)).2.1
  unfold lumpLower
  linarith
theorem le_lumpUpper (c : ℤ) : c ≤ lumpUpper g c := by
  have := (g.mem_interval _ (abs_offsetFromCentre_le hL c)).2.2.1
  unfold lumpUpper
  linarith
theorem lumpBounds_eq_of_mem (c c' : ℤ) (h1 : lumpLower g c ≤ c') (h2 : c' ≤ lumpUpper g c) :
    lumpLower g c' = lumpLower g c ∧ lumpUpper g c' = lumpUpper g c := by
  unfold lumpLower at h1 ⊢
  unfold lumpUpper at h2 ⊢
  have hb := abs_offsetFromCentre_le hL c
  have hg := g.mem_interval _ hb
  set o := offsetFromCentre L c with ho
  set t := c - o with ht
  have ho1 : g.lower o ≤ c' - t := by linarith
  have ho2 : c' - t ≤ g.upper o := by linarith
  have hr : |c' - t| ≤ ((L : ℤ) - 1) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hg.1, hg.2.2.2]
  have e : offsetFromCentre L c' = c' - t := by
    have := offsetFromCentre_add hL t (c' - t) (dvd_sub_offsetFromCentre hL c) hr
    rwa [add_sub_cancel] at this
  have hs := g.interval_eq o (c' - t) hb ho1 ho2
  rw [e, hs.1, hs.2]
  constructor <;> ring
theorem lumpUpper_sub_lumpLower (c : ℤ) : 2 ^ 14 ≤ lumpUpper g c - lumpLower g c + 1 := by
  have := (g.interval_length _ (abs_offsetFromCentre_le hL c)).1
  unfold lumpUpper lumpLower
  linarith
theorem lumpBounds_add (c D : ℤ) (hD : (L : ℤ) ∣ D) :
    lumpLower g (c + D) = lumpLower g c + D ∧ lumpUpper g (c + D) = lumpUpper g c + D := by
  have e : offsetFromCentre L (c + D) = offsetFromCentre L c := by
    have h1 := offsetFromCentre_add hL (c - offsetFromCentre L c + D) (offsetFromCentre L c)
      (dvd_add (dvd_sub_offsetFromCentre hL c) hD) (abs_offsetFromCentre_le hL c)
    have e2 : c - offsetFromCentre L c + D + offsetFromCentre L c = c + D := by ring
    rwa [e2] at h1
  unfold lumpLower lumpUpper
  rw [e]
  constructor <;> ring
end lumpBounds
def lumpOfCoords {L : ℕ} (g : LumpGrid L) (z : Fin 4 → ℤ) : Finset F.Cell :=
  boxSites F.top (fun i => lumpLower g (z i)) (fun i => lumpUpper g (z i))
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem lumpOf_eq_lumpOfCoords {L : ℕ} (g : LumpGrid L) (x : F.Cell) : lumpOf g x = lumpOfCoords g (siteCoords x) :=
  rfl
theorem lumpOfCoords_congr {L : ℕ} (g : LumpGrid L) {z z' : Fin 4 → ℤ}
    (h : ∀ i, lumpLower g (z i) = lumpLower g (z' i) ∧ lumpUpper g (z i) = lumpUpper g (z' i)) :
    lumpOfCoords (F := F) g z = lumpOfCoords g z' := by
  unfold lumpOfCoords
  have e1 : (fun i => lumpLower g (z i)) = fun i => lumpLower g (z' i) := funext fun i => (h i).1
  have e2 : (fun i => lumpUpper g (z i)) = fun i => lumpUpper g (z' i) := funext fun i => (h i).2
  rw [e1, e2]
theorem boxSites_add_period (lo hi D : Fin 4 → ℤ) (hD : siteOfCoords (F := F) F.top D = 0) :
    boxSites (F := F) F.top (lo + D) (hi + D) = boxSites F.top lo hi := by
  have hadd : ∀ a : Fin 4 → ℤ, siteOfCoords (F := F) F.top (a + D) = siteOfCoords F.top a := by
    intro a
    funext k
    have := congrFun hD k
    simp only [siteOfCoords, Pi.add_apply, Int.cast_add, Pi.zero_apply] at this ⊢
    rw [this, add_zero]
  ext x
  simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a - D, fun i => ?_, ?_⟩
    · have := ha i
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply]
      constructor <;> linarith [this.1, this.2]
    · rw [← hadd (a - D)]
      simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a + D, fun i => ?_, hadd a⟩
    have := ha i
    simp only [Pi.add_apply]
    constructor <;> linarith [this.1, this.2]
theorem lumpOfCoords_add {L : ℕ} (g : LumpGrid L) (hL : Odd L) (z D : Fin 4 → ℤ) (hLD : ∀ i, (L : ℤ) ∣ D i)
    (hD : siteOfCoords (F := F) F.top D = 0) : lumpOfCoords (F := F) g (z + D) = lumpOfCoords g z := by
  unfold lumpOfCoords
  have e1 : (fun i => lumpLower g ((z + D) i)) = (fun i => lumpLower g (z i)) + D :=
    funext fun i => (lumpBounds_add g hL (z i) (D i) (hLD i)).1
  have e2 : (fun i => lumpUpper g ((z + D) i)) = (fun i => lumpUpper g (z i)) + D :=
    funext fun i => (lumpBounds_add g hL (z i) (D i) (hLD i)).2
  rw [e1, e2, boxSites_add_period _ _ _ hD]
theorem lumpOfCoords_of_mem {L : ℕ} (g : LumpGrid L) (hL : Odd L) (hs : ∀ i, L ∣ F.extent i) {x : F.Cell}
    {w : F.Cell} (hw : w ∈ lumpOf g x) {z : Fin 4 → ℤ} (hz : siteOfCoords F.top z = w) :
    lumpOfCoords g z = lumpOf g x := by
  rw [lumpOf_eq_lumpOfCoords] at hw ⊢
  unfold lumpOfCoords boxSites at hw
  simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  have e1 : lumpOfCoords (F := F) g u = lumpOfCoords g (siteCoords x) :=
    lumpOfCoords_congr g fun i => lumpBounds_eq_of_mem g hL _ _ (hu i).1 (hu i).2
  rw [← e1]
  have hD : siteOfCoords (F := F) F.top (z - u) = 0 := by
    funext k
    have := congrFun hz k
    simp only [siteOfCoords, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at this ⊢
    rw [this, sub_self]
  have hLD : ∀ i, (L : ℤ) ∣ (z - u) i := by
    intro i
    have := congrFun hD i
    simp only [siteOfCoords, Pi.zero_apply] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, period_top] at this
    exact dvd_trans (by exact_mod_cast hs i) this
  have := lumpOfCoords_add (F := F) g hL u (z - u) hLD hD
  rwa [add_sub_cancel] at this
theorem card_lumps_near_le {L : ℕ} (g : LumpGrid L) (hL : Odd L) (hs : ∀ i, L ∣ F.extent i) (y : F.Cell) (r : ℕ)
    (hr : 2 * r + 1 ≤ 2 ^ 14) (A : Finset (Finset F.Cell))
    (hA : ∀ l ∈ A, IsLump g l ∧ ∃ w ∈ l, cellSupDist w y ≤ r) : A.card ≤ 16 := by
  classical
  let e : (Fin 4 → Bool) → Fin 4 → ℤ := fun ε i => siteCoords y i + if ε i then (r : ℤ) else -(r : ℤ)
  have hsub : A ⊆ (Finset.univ : Finset (Fin 4 → Bool)).image fun ε => lumpOfCoords (F := F) g (e ε) := by
    intro l hl
    obtain ⟨⟨x, rfl⟩, w, hw, hd⟩ := hA l hl
    let d : Fin 4 → ℤ := fun i => ((w i - y i).valMinAbs)
    have hd' : ∀ i, |d i| ≤ (r : ℤ) := by
      intro i
      have h1 : ((w i - y i).valMinAbs).natAbs ≤ cellSupDist w y :=
        Finset.le_sup (f := fun i => ((w i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
      have h2 : ((w i - y i).valMinAbs).natAbs ≤ r := h1.trans hd
      show |((w i - y i).valMinAbs)| ≤ (r : ℤ)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
    have hz : siteOfCoords F.top (siteCoords y + d) = w := by
      funext k
      simp only [siteOfCoords, Pi.add_apply, Int.cast_add, siteCoords_cast]
      simp only [d, ZMod.coe_valMinAbs]
      ring
    have hl1 := lumpOfCoords_of_mem g hL hs hw hz
    have hpick : ∀ i, ∃ b : Bool, lumpLower g (e (fun _ => b) i) = lumpLower g ((siteCoords y + d) i) ∧
        lumpUpper g (e (fun _ => b) i) = lumpUpper g ((siteCoords y + d) i) := by
      intro i
      set c := (siteCoords y + d) i with hc
      have hci : c = siteCoords y i + d i := rfl
      have b := abs_le.1 (hd' i)
      have h1 := lumpLower_le g hL c
      have h2 := le_lumpUpper g hL c
      have h3 := lumpUpper_sub_lumpLower g hL c
      by_cases hlo : lumpLower g c ≤ siteCoords y i - r
      · refine ⟨false, ?_⟩
        have : e (fun _ => false) i = siteCoords y i - r := by simp [e, sub_eq_add_neg]
        rw [this]
        exact lumpBounds_eq_of_mem g hL _ _ hlo (by linarith [b.2, b.1])
      · refine ⟨true, ?_⟩
        have : e (fun _ => true) i = siteCoords y i + r := by simp [e]
        rw [this]
        push_neg at hlo
        exact lumpBounds_eq_of_mem g hL _ _ (by linarith [b.2, b.1]) (by linarith [b.2, b.1])
    choose ε hε using hpick
    refine Finset.mem_image.2 ⟨ε, Finset.mem_univ _, ?_⟩
    rw [← hl1]
    refine lumpOfCoords_congr g fun i => ?_
    have : e ε i = e (fun _ => ε i) i := rfl
    rw [this]
    exact hε i
  calc A.card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 → Bool)).card := Finset.card_image_le
    _ = 16 := by simp
section sums
theorem sum_sum_le_mul_of_multiplicity {A B : Type} (Ps : Finset A) (Q : Finset B) (Qp : A → Finset B) (G : B → ℝ)
    (hG : ∀ q, 0 ≤ G q) (K : ℕ) (hsub : ∀ p ∈ Ps, Qp p ⊆ Q)
    (hmul : ∀ q ∈ Q, ∀ [DecidablePred fun p => q ∈ Qp p], ((Ps.filter fun p => q ∈ Qp p).card) ≤ K) :
    ∑ p ∈ Ps, ∑ q ∈ Qp p, G q ≤ K * ∑ q ∈ Q, G q := by apply _root_.YangMills.Construction.CoercivityProof.sum_sum_le_mul_of_multiplicity <;> assumption
theorem sum_sum_le_mul_sdiff {A B : Type} [DecidableEq B] (Ps : Finset A) (Q Q₁ : Finset B) (Qp : A → Finset B)
    (G : B → ℝ) (hG : ∀ q, 0 ≤ G q) (K : ℕ) (hQ : Q₁ ⊆ Q) (hsub : ∀ p ∈ Ps, Qp p ⊆ Q)
    (hdis : ∀ p ∈ Ps, Disjoint (Qp p) Q₁)
    (hmul : ∀ q ∈ Q, ∀ [DecidablePred fun p => q ∈ Qp p], ((Ps.filter fun p => q ∈ Qp p).card) ≤ K) :
    ∑ p ∈ Ps, ∑ q ∈ Qp p, G q ≤ K * (∑ q ∈ Q, G q - ∑ q ∈ Q₁, G q) := by
  have h := sum_sum_le_mul_of_multiplicity Ps (Q \ Q₁) Qp G hG K
    (fun p hp q hq => Finset.mem_sdiff.2 ⟨hsub p hp hq, Finset.disjoint_left.1 (hdis p hp) hq⟩)
    (fun q hq => hmul q (Finset.mem_sdiff.1 hq).1)
  have e := Finset.sum_sdiff (f := G) hQ
  have e' : ∑ q ∈ Q \ Q₁, G q = ∑ q ∈ Q, G q - ∑ q ∈ Q₁, G q := by linarith
  rwa [e'] at h
end sums
section cuts
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} : o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i} (hz : z ∈ sitesBelow i w) :
    z ∈ sitesBelow i x := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.sitesBelow_trans <;> assumption
theorem eq_of_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide) {x : F.Site i}
    {y y' : F.Site j} (h1 : x ∈ sitesBelow i y) (h2 : x ∈ sitesBelow i y') : y = y' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.eq_of_mem_sitesBelow_of_mem_sitesBelow <;> assumption
theorem card_filter_cutBelow_le {ι : Type} {i : ℕ} (hi : i ≤ F.top) (hL : Odd F.blockSide) (A : Finset ι)
    (X : ι → Finset F.Cell) (K : ℕ)
    (hK : ∀ y, ∀ [DecidablePred fun l => y ∈ X l], (A.filter fun l => y ∈ X l).card ≤ K)
    (x : F.Site i) [DecidablePred fun l => x ∈ cutBelow i (X l)] :
    (A.filter fun l => x ∈ cutBelow i (X l)).card ≤ K := by
  classical
  by_cases h : (A.filter fun l => x ∈ cutBelow i (X l)) = ∅
  · rw [h]
    simp
  · obtain ⟨l₀, hl₀⟩ := Finset.nonempty_iff_ne_empty.2 h
    have h0 := (Finset.mem_filter.1 hl₀).2
    simp only [cutBelow, Finset.mem_biUnion] at h0
    obtain ⟨z, hz, hxz⟩ := h0
    refine le_trans (Finset.card_le_card ?_) (hK z)
    intro l hl
    obtain ⟨hlA, hl'⟩ := Finset.mem_filter.1 hl
    simp only [cutBelow, Finset.mem_biUnion] at hl'
    obtain ⟨z', hz', hxz'⟩ := hl'
    have := eq_of_mem_sitesBelow hi le_rfl hL hxz hxz'
    exact Finset.mem_filter.2 ⟨hlA, this ▸ hz'⟩
theorem cellSupDist_symm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_le_add (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
end cuts
section corners
theorem natAbs_valMinAbs_intCast_le {p : ℕ} (hp : 0 < p) (c : ℤ) :
    ((c : ZMod p).valMinAbs).natAbs ≤ c.natAbs := by
  haveI : NeZero p := ⟨hp.ne'⟩
  exact ZMod.natAbs_min_of_le_div_two p _ _ (by rw [ZMod.coe_valMinAbs]) (ZMod.natAbs_valMinAbs_le _)
theorem exists_corner_offset {p : F.Site F.top × Fin 4 × Fin 4} (hp : p.2.1 < p.2.2) {x : F.Cell}
    (hx : x ∈ plaquetteCorners p) :
    ∃ d : Fin 4 → ℤ, (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧ x = p.1 + siteOfCoords F.top d := by
  have hne : p.2.1 ≠ p.2.2 := ne_of_lt hp
  have hadd : ∀ a b : Fin 4 → ℤ,
      siteOfCoords (F := F) F.top (a + b) = siteOfCoords F.top a + siteOfCoords F.top b := by
    intro a b
    funext k
    simp [siteOfCoords]
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine ⟨0, fun i => by simp, ?_⟩
    have : siteOfCoords (F := F) F.top (0 : Fin 4 → ℤ) = 0 := by
      funext k
      simp [siteOfCoords]
    rw [this, add_zero]
  · refine ⟨Pi.single p.2.1 1, fun i => ?_, rfl⟩
    by_cases h : i = p.2.1
    · subst h
      simp
    · simp [Pi.single_apply, h]
  · refine ⟨Pi.single p.2.2 1, fun i => ?_, rfl⟩
    by_cases h : i = p.2.2
    · subst h
      simp
    · simp [Pi.single_apply, h]
  · refine ⟨Pi.single p.2.1 1 + Pi.single p.2.2 1, fun i => ?_, ?_⟩
    · have hval : (Pi.single p.2.1 (1 : ℤ) + Pi.single p.2.2 1 : Fin 4 → ℤ) i =
          (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0) := by
        simp [Pi.single_apply]
      rw [hval]
      by_cases h : i = p.2.1
      · have h' : i ≠ p.2.2 := h ▸ hne
        simp [h, hne]
      · by_cases h' : i = p.2.2
        · rw [if_neg h, if_pos h']
          norm_num
        · rw [if_neg h, if_neg h']
          norm_num
    · rw [hadd, add_assoc]
      rfl
theorem cellSupDist_corners_le_one (hs : ∀ i, 0 < F.extent i) {p : F.Site F.top × Fin 4 × Fin 4}
    (hp : p.2.1 < p.2.2) {x y : F.Cell} (hx : x ∈ plaquetteCorners p) (hy : y ∈ plaquetteCorners p) :
    cellSupDist x y ≤ 1 := by
  obtain ⟨d, hd, rfl⟩ := exists_corner_offset hp hx
  obtain ⟨d', hd', rfl⟩ := exists_corner_offset hp hy
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hper : 0 < F.period F.top i := by rw [period_top]; exact hs i
  have e : (p.1 + siteOfCoords (F := F) F.top d : F.Cell) i - (p.1 + siteOfCoords (F := F) F.top d' : F.Cell) i =
      ((d i - d' i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le hper _).trans ?_
  have := hd i
  have := hd' i
  omega
end corners
section energies
theorem plaquetteEnergy_nonneg (W : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) : 0 ≤ plaquetteEnergy W p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem re_mul_unitQuaternion_le_norm (q : ℍ[ℝ]) (g : UnitQuaternion) :
    (q * ((g : UnitQuaternion) : ℍ[ℝ])).re ≤ ‖q‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.re_mul_unitQuaternion_le_norm <;> assumption
theorem blockFit_nonneg {l : ℕ} (W : F.GaugeField l) (V : F.GaugeField (l + 1)) (c : F.Site (l + 1) × Fin 4) :
    0 ≤ blockFit W V c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem contourFit_nonneg (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) : 0 ≤ contourFit J₀ h b W V c := by
  unfold contourFit
  linarith [re_mul_unitQuaternion_le_norm (contourMean J₀ h b W c) ((V c.1 c.2)⁻¹)]
theorem mem_sitesBelow_self {j : ℕ} (hL : Odd F.blockSide) (x : F.Site j) : x ∈ sitesBelow j x := by
  refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have e : (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = siteCoords x := by
      funext k
      simp
    show siteOfCoords j (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = x
    rw [e]
    exact siteOfCoords_siteCoords x
theorem cutPlaquettes_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutPlaquettes Z ⊆ cutPlaquettes Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutPlaquettes_mono <;> assumption
theorem cutBonds_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') : cutBonds Z ⊆ cutBonds Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutBonds_mono <;> assumption
theorem cutBelow_mono {m : ℕ} (i : ℕ) {Z Z' : Finset (F.Site m)} (h : Z ⊆ Z') :
    cutBelow i Z ⊆ cutBelow i Z' := Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem sum_anchored_le {ι B : Type} {i : ℕ} (hi : i ≤ F.top) (hL : Odd F.blockSide)
    (Y : Finset F.Cell → Finset B) (site : B → F.Site i) (G : B → ℝ) (hG : ∀ q, 0 ≤ G q)
    (hmono : ∀ Z Z', Z ⊆ Z' → Y Z ⊆ Y Z') (hanch : ∀ Z, ∀ q ∈ Y Z, site q ∈ cutBelow i Z)
    (A : Finset ι) (X : ι → Finset F.Cell) (S S₁ : Finset F.Cell) (K : ℕ) (hS : S₁ ⊆ S)
    (hX : ∀ l ∈ A, X l ⊆ S) (hd : ∀ l ∈ A, Disjoint (X l) S₁)
    (hK : ∀ y, ∀ [DecidablePred fun l => y ∈ X l], (A.filter fun l => y ∈ X l).card ≤ K) :
    ∑ l ∈ A, ∑ q ∈ Y (X l), G q ≤ K * (∑ q ∈ Y S, G q - ∑ q ∈ Y S₁, G q) := by
  classical
  refine sum_sum_le_mul_sdiff A (Y S) (Y S₁) (fun l => Y (X l)) G hG K (hmono _ _ hS)
    (fun l hl => hmono _ _ (hX l hl)) ?_ ?_
  · intro l hl
    refine Finset.disjoint_left.2 fun q hq hq' => ?_
    have h1 := hanch _ q hq
    have h2 := hanch _ q hq'
    simp only [cutBelow, Finset.mem_biUnion] at h1 h2
    obtain ⟨z, hz, hxz⟩ := h1
    obtain ⟨z', hz', hxz'⟩ := h2
    have := eq_of_mem_sitesBelow hi le_rfl hL hxz hxz'
    exact Finset.disjoint_left.1 (hd l hl) hz (this ▸ hz')
  · intro q _ _
    refine le_trans (Finset.card_le_card ?_) (card_filter_cutBelow_le hi hL A X K (fun y _ => ?_) (site q))
    · intro l hl
      obtain ⟨hlA, hl'⟩ := Finset.mem_filter.1 hl
      exact Finset.mem_filter.2 ⟨hlA, hanch _ q hl'⟩
    · convert hK y
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
theorem mem_cutBelow_of_chainSites {i : ℕ} (hi : i ≤ F.depth) (hL : Odd F.blockSide) {Z : Finset F.Cell}
    {x : F.Site i} (hx : x ∈ cutBelow i (D.chainSites ∩ cutBelow F.depth Z)) : x ∈ cutBelow i Z := by
  simp only [cutBelow, Finset.mem_biUnion, Finset.mem_inter] at hx ⊢
  obtain ⟨w, ⟨_, z, hz, hw⟩, hxw⟩ := hx
  exact ⟨z, hz, sitesBelow_trans hi (Nat.le_succ _) le_rfl hL z hw hxw⟩
theorem chainSites_inter_mono {Z Z' : Finset F.Cell} (h : Z ⊆ Z') :
    D.chainSites ∩ cutBelow F.depth Z ⊆ D.chainSites ∩ cutBelow F.depth Z' :=
  Finset.inter_subset_inter_left (cutBelow_mono _ h)
theorem sum_energyOn_le {ι : Type} (ha : 0 ≤ a) (hL : Odd F.blockSide) (A : Finset ι) (X : ι → Finset F.Cell)
    (S₁ : Finset F.Cell) (K : ℕ) (hS : S₁ ⊆ D.cells) (hX : ∀ l ∈ A, X l ⊆ D.cells)
    (hd : ∀ l ∈ A, Disjoint (X l) S₁)
    (hK : ∀ y, ∀ [DecidablePred fun l => y ∈ X l], (A.filter fun l => y ∈ X l).card ≤ K) :
    ∑ l ∈ A, D.energyOn (X l) ≤ K * (D.totalEnergy - D.energyOn S₁) := by
  classical
  have hP := sum_anchored_le (i := 0) (Nat.zero_le _) hL
    (fun Z => cutPlaquettes (cutBelow 0 (D.chainSites ∩ cutBelow F.depth Z))) (fun p => p.1)
    (plaquetteEnergy (D.chain 0)) (plaquetteEnergy_nonneg _)
    (fun Z Z' h => cutPlaquettes_mono (cutBelow_mono _ (chainSites_inter_mono D h)))
    (fun Z q hq => mem_cutBelow_of_chainSites D (Nat.zero_le _) hL (by
      simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product] at hq
      exact hq.1.1)) A X D.cells S₁ K hS hX hd hK
  have hB : ∀ i ∈ Finset.range F.depth, _ := fun i hi => sum_anchored_le (i := i + 1)
    (Nat.succ_le_succ (Finset.mem_range.1 hi).le) hL
    (fun Z => cutBonds (cutBelow (i + 1) (D.chainSites ∩ cutBelow F.depth Z))) (fun c => c.1)
    (blockFit (D.chain i) (D.chain (i + 1))) (blockFit_nonneg _ _)
    (fun Z Z' h => cutBonds_mono (cutBelow_mono _ (chainSites_inter_mono D h)))
    (fun Z q hq => mem_cutBelow_of_chainSites D (Finset.mem_range.1 hi) hL (by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product] at hq
      exact hq.1.1)) A X D.cells S₁ K hS hX hd hK
  have hT := sum_anchored_le (i := F.top) le_rfl hL (fun Z => cutBonds Z) (fun c => c.1) D.topBondFit
    (fun c => contourFit_nonneg _ _ _ _ _ _) (fun Z Z' h => cutBonds_mono h)
    (fun Z q hq => by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product] at hq
      exact Finset.mem_biUnion.2 ⟨_, hq.1.1, mem_sitesBelow_self hL _⟩) A X D.cells S₁ K hS hX hd hK
  have hB' : ∑ l ∈ A, ∑ i ∈ Finset.range F.depth,
      ∑ c ∈ cutBonds (cutBelow (i + 1) (D.chainSites ∩ cutBelow F.depth (X l))),
      blockFit (D.chain i) (D.chain (i + 1)) c ≤ K * (∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1)
        (D.chainSites ∩ cutBelow F.depth D.cells)), blockFit (D.chain i) (D.chain (i + 1)) c -
        ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) (D.chainSites ∩ cutBelow F.depth S₁)),
        blockFit (D.chain i) (D.chain (i + 1)) c) := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum hB
  have e : ∑ l ∈ A, D.energyOn (X l) =
      ∑ l ∈ A, ∑ p ∈ cutPlaquettes (cutBelow 0 (D.chainSites ∩ cutBelow F.depth (X l))),
        plaquetteEnergy (D.chain 0) p +
      a * ∑ l ∈ A, ∑ i ∈ Finset.range F.depth,
        ∑ c ∈ cutBonds (cutBelow (i + 1) (D.chainSites ∩ cutBelow F.depth (X l))),
        blockFit (D.chain i) (D.chain (i + 1)) c + a * ∑ l ∈ A, ∑ c ∈ cutBonds (X l), D.topBondFit c := by
    simp only [HoleData.energyOn, cutChainEnergy, Finset.sum_add_distrib, Finset.mul_sum]
  rw [e]
  simp only [HoleData.totalEnergy, HoleData.energyOn, cutChainEnergy]
  have h1 := mul_le_mul_of_nonneg_left hB' ha
  have h2 := mul_le_mul_of_nonneg_left hT ha
  nlinarith [hP, h1, h2]
end energies
section near
theorem mem_lumpOf {L : ℕ} (g : LumpGrid L) (hL : Odd L) {j : ℕ} (x : F.Site j) : x ∈ lumpOf g x := by
  unfold lumpOf boxSites
  refine Finset.mem_image.2 ⟨siteCoords x, ?_, siteOfCoords_siteCoords x⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  exact ⟨lumpLower_le g hL (siteCoords x i), le_lumpUpper g hL (siteCoords x i)⟩
theorem mem_thicken {j : ℕ} (m : ℕ) {l : Finset (F.Site j)} {x : F.Site j} (hx : x ∈ l) : x ∈ thicken m l := by
  refine Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨0, ?_, ?_⟩⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have : siteOfCoords (F := F) j (0 : Fin 4 → ℤ) = 0 := by
      funext k
      simp [siteOfCoords]
    rw [this, add_zero]
theorem mem_lumpsNeighbourhood {j : ℕ} {H : Finset (Finset (F.Site j))} {l : Finset (F.Site j)} (hl : l ∈ H)
    {x : F.Site j} (hx : x ∈ l) : x ∈ lumpsNeighbourhood H :=
  Finset.mem_biUnion.2 ⟨l, hl, mem_thicken _ hx⟩
theorem mem_cellBall {y z : F.Cell} {r : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube (2 * r + 1))
    (e : y + siteOfCoords F.top h = z) : z ∈ cellBall y r := Finset.mem_image.2 ⟨h, hh, e⟩
theorem exists_hot_plaquette_of_mem_hotLumps {L : ℕ} (g : LumpGrid L) (hL : Odd L) {s : ℝ} {j : ℕ}
    {X : Finset (F.Site j)} {W : F.GaugeField j} {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) :
    ∃ p ∈ cutPlaquettes X, s ≤ plaquetteDefect W p ∧ ∃ x ∈ plaquetteCorners p, l = lumpOf g x := by
  classical
  unfold hotLumps at hl
  obtain ⟨p, hp, hl⟩ := Finset.mem_biUnion.1 hl
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hl
  exact ⟨p, hp1, hp2, x, hx, rfl⟩
theorem plaquetteCorners_subset {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X := by
  simp only [cutPlaquettes, Finset.mem_filter] at hp
  exact hp.2
theorem exists_step_towards (d : ℤ) (hd : |d| ≤ 3) :
    ∃ e : ℤ, |e| ≤ 1 ∧ |d - e| ≤ 2 := by
  rw [abs_le] at hd
  by_cases h1 : 1 ≤ d
  · exact ⟨1, by simp, by rw [abs_le]; constructor <;> omega⟩
  · by_cases h2 : d ≤ -1
    · exact ⟨-1, by simp, by rw [abs_le]; constructor <;> omega⟩
    · exact ⟨0, by simp, by rw [abs_le]; constructor <;> omega⟩
theorem cellSupDist_add_le (hs : ∀ i, 0 < F.extent i) (x : F.Cell) (h : Fin 4 → ℤ) (r : ℕ)
    (hh : ∀ i, |h i| ≤ (r : ℤ)) : cellSupDist (x + siteOfCoords F.top h) x ≤ r := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hper : 0 < F.period F.top i := by rw [period_top]; exact hs i
  have e : (x + siteOfCoords (F := F) F.top h : F.Cell) i - x i = ((h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le hper _).trans ?_
  have := hh i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem mem_torusCells (hs : ∀ i, 0 < F.extent i) (x : F.Cell) : x ∈ torusCells F := by
  unfold torusCells boxSites
  refine Finset.mem_image.2 ⟨siteCoords x, ?_, siteOfCoords_siteCoords x⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]
  intro i
  have hp : 0 < F.period F.top i := by rw [period_top]; exact hs i
  haveI : NeZero (F.period F.top i) := ⟨hp.ne'⟩
  have hv := ZMod.val_lt (x i)
  have hc : siteCoords x i = ((x i).val : ℤ) := by
    unfold siteCoords
    rw [← ZMod.natCast_val]
  rw [hc]
  have hside : F.period F.top i = F.extent i := period_top i
  constructor
  · positivity
  · have : ((x i).val : ℤ) + 1 ≤ F.extent i := by
      rw [← hside]
      exact_mod_cast hv
    linarith
theorem card_centredCube_three : (centredCube 3).card = 81 := by
  have h3 : ∀ i : Fin 4, (Finset.Icc (-((((3 : ℕ) : ℤ) - 1) / 2)) ((((3 : ℕ) : ℤ) - 1) / 2)).card = 3 := by
    intro i
    rw [Int.card_Icc]
    norm_num
    rfl
  rw [centredCube, Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => h3 i]
  simp
theorem mem_nearbyLumps {h : Finset (Finset (F.Site F.depth))} {y z : F.Cell} {l : Finset (F.Site F.depth)}
    (hl : l ∈ h) (hb : y ∈ cellBall z 2) (hly : l ⊆ sitesBelow F.depth y) : l ∈ nearbyLumps h z := by
  classical
  unfold nearbyLumps
  rw [Finset.mem_filter]
  refine ⟨hl, ?_⟩
  intro u hu
  have h1 : u ∈ sitesBelow F.depth y := hly hu
  unfold cutBelow
  rw [Finset.mem_biUnion]
  exact ⟨y, hb, h1⟩
theorem exists_cell_between (hs : ∀ i, 0 < F.extent i) {x y : F.Cell} (hxy : cellSupDist x y ≤ 3) :
    ∃ e ∈ centredCube 3, cellSupDist (x + siteOfCoords F.top e) x ≤ 1 ∧
      cellSupDist y (x + siteOfCoords F.top e) ≤ 2 ∧ y ∈ cellBall (x + siteOfCoords F.top e) 2 := by
  let d : Fin 4 → ℤ := fun i => ((y i - x i).valMinAbs)
  have hd : ∀ i, |d i| ≤ 3 := by
    intro i
    have h1 : ((y i - x i).valMinAbs).natAbs ≤ cellSupDist y x :=
      Finset.le_sup (f := fun i => ((y i - x i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : ((y i - x i).valMinAbs).natAbs ≤ 3 := by
      rw [cellSupDist_symm] at h1
      exact h1.trans hxy
    show |((y i - x i).valMinAbs)| ≤ 3
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hyd : y = x + siteOfCoords F.top d := by
    funext k
    simp only [siteOfCoords, Pi.add_apply]
    simp only [d, ZMod.coe_valMinAbs]
    ring
  choose e he1 he2 using fun i => exists_step_towards (d i) (hd i)
  have hadd : ∀ u v : Fin 4 → ℤ,
      siteOfCoords (F := F) F.top (u + v) = siteOfCoords F.top u + siteOfCoords F.top v := by
    intro u v
    funext k
    simp [siteOfCoords]
  have hyz : (x + siteOfCoords F.top e) + siteOfCoords F.top (d - e) = y := by
    rw [add_assoc, ← hadd]
    simpa using hyd.symm
  have he3 : e ∈ centredCube 3 := by
    refine mem_centredCube_iff.2 fun k => ?_
    have := he1 k
    simpa using this
  have hc5 : d - e ∈ centredCube (2 * 2 + 1) := by
    refine mem_centredCube_iff.2 fun k => ?_
    have := he2 k
    simpa using this
  refine ⟨e, he3, cellSupDist_add_le hs x e 1 (by simpa using he1), ?_, mem_cellBall hc5 hyz⟩
  have := cellSupDist_add_le hs (x + siteOfCoords F.top e) (d - e) 2 (fun i => by simpa using he2 i)
  rwa [hyz] at this
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
theorem card_near_core_le (hF : Odd F.blockSide) (hL : Odd L) (hs : ∀ i, 0 < F.extent i) (C : ℝ)
    (X : Finset F.Cell) (hX : X ⊆ D.coreCells C 5) (A : Finset (Finset (F.Site F.depth)))
    (hA : ∀ l ∈ A, l ∈ D.hotFineLumps ∧ ∃ x ∈ X, ∃ y, cellSupDist x y ≤ 3 ∧ l ⊆ sitesBelow F.depth y) :
    A.card ≤ X.card * 81 * J₀ := by
  classical
  let nb : F.Cell × (Fin 4 → ℤ) → F.Cell := fun q => q.1 + siteOfCoords F.top q.2
  let Q : Finset (F.Cell × (Fin 4 → ℤ)) :=
    (X ×ˢ centredCube 3).filter fun q => ¬ IsCrowded J₀ D.hotFineLumps (nb q)
  have hsub : A ⊆ Q.biUnion fun q => nearbyLumps D.hotFineLumps (nb q) := by
    intro l hl
    obtain ⟨hh, x, hx, y, hxy, hly⟩ := hA l hl
    obtain ⟨p, hp, _, w, hw, hlw⟩ := exists_hot_plaquette_of_mem_hotLumps g hL hh
    have hwl : w ∈ l := hlw ▸ mem_lumpOf g hL w
    have hwS : w ∈ cutBelow F.depth D.cells := (plaquetteCorners_subset hp).2 hw
    obtain ⟨y', hy', hwy'⟩ := Finset.mem_biUnion.1 hwS
    have hyy : y = y' := eq_of_mem_sitesBelow (Nat.le_succ _) le_rfl hF (hly hwl) hwy'
    subst hyy
    obtain ⟨e, he3, dxz, dyz, hb⟩ := exists_cell_between hs hxy
    have hzS : nb (x, e) ∈ D.cells := by
      by_contra hzS
      have := D.wall_free _ hh y hy' hly (nb (x, e)) (Finset.mem_sdiff.2 ⟨mem_torusCells hs _, hzS⟩)
      have h2 : cellSupDist y (nb (x, e)) ≤ 2 := dyz
      omega
    have hcore' := (Finset.mem_filter.1 (hX hx)).2
    have hnot : ¬ IsCrowded J₀ D.hotFineLumps (nb (x, e)) := by
      intro hc
      have hmem : nb (x, e) ∈ D.badCells C :=
        Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hzS, hc⟩))
      have h5 := hcore' _ hmem
      rw [cellSupDist_symm] at h5
      have h1 : cellSupDist (nb (x, e)) x ≤ 1 := dxz
      omega
    exact Finset.mem_biUnion.2 ⟨(x, e), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, he3⟩, hnot⟩,
      mem_nearbyLumps hh hb hly⟩
  have hc3 := card_centredCube_three
  calc A.card ≤ _ := Finset.card_le_card hsub
    _ ≤ Q.card * J₀ := by
        refine Finset.card_biUnion_le_card_mul _ _ _ fun q hq => ?_
        have := (Finset.mem_filter.1 hq).2
        unfold IsCrowded at this
        omega
    _ ≤ X.card * 81 * J₀ := by
        refine Nat.mul_le_mul_right _ ?_
        calc Q.card ≤ (X ×ˢ centredCube 3).card := Finset.card_filter_le _ _
          _ = X.card * 81 := by rw [Finset.card_product, hc3]
end near
section payment
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
theorem keptCells_subset : D.keptCells ⊆ D.cells := Finset.sdiff_subset
omit D in
theorem mem_of_eq_lumpOf (hL : Odd L) {l : Finset F.Cell} {x : F.Cell} (h : l = lumpOf g x) : x ∈ l := by
  subst h
  exact mem_lumpOf g hL x
theorem exists_hot_plaquette_choice (hL : Odd L) :
    ∃ (p : Finset F.Cell → F.Cell × Fin 4 × Fin 4) (x : Finset F.Cell → F.Cell),
      ∀ l ∈ D.hotTopLumps, p l ∈ cutPlaquettes D.cells ∧ θ ≤ plaquetteDefect D.topField (p l) ∧
        x l ∈ plaquetteCorners (p l) ∧ l = lumpOf g (x l) := by
  classical
  have h : ∀ l : Finset F.Cell, ∃ q : (F.Cell × Fin 4 × Fin 4) × F.Cell, l ∈ D.hotTopLumps →
      q.1 ∈ cutPlaquettes D.cells ∧ θ ≤ plaquetteDefect D.topField q.1 ∧ q.2 ∈ plaquetteCorners q.1 ∧
        l = lumpOf g q.2 := by
    intro l
    by_cases hl : l ∈ D.hotTopLumps
    · obtain ⟨p, hp, hh, x, hx, hlx⟩ := exists_hot_plaquette_of_mem_hotLumps g hL hl
      exact ⟨(p, x), fun _ => ⟨hp, hh, hx, hlx⟩⟩
    · exact ⟨((0, 0, 0), 0), fun h' => absurd h' hl⟩
  choose q hq using h
  exact ⟨fun l => (q l).1, fun l => (q l).2, fun l hl => hq l hl⟩
theorem corner_not_mem_keptCells (hL : Odd L) {p : F.Cell × Fin 4 × Fin 4} (hp : p ∈ cutPlaquettes D.cells)
    (hh : θ ≤ plaquetteDefect D.topField p) {c : F.Cell} (hc : c ∈ plaquetteCorners p) : c ∉ D.keptCells := by
  classical
  intro hk
  refine (Finset.mem_sdiff.1 hk).2 (mem_lumpsNeighbourhood (l := lumpOf g c) ?_ (mem_lumpOf g hL c))
  unfold HoleData.hotTopLumps hotLumps
  exact Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨hp, hh⟩, Finset.mem_image.2 ⟨c, hc, rfl⟩⟩
theorem hotTopLumps_paid (hF : Odd F.blockSide) (hL : Odd L) (ha : 0 ≤ a) (hs : ∀ i, 0 < F.extent i)
    (hdiv : D.hotTopLumps ≠ ∅ → ∀ i, L ∣ F.extent i) (C cH : ℝ)
    (hprice : ∀ p ∈ cutPlaquettes D.cells, θ ≤ plaquetteDefect D.topField p → plaquetteCorners p ⊆ D.coreCells C 5 →
      cH ≤ D.energyOn (plaquetteCorners p))
    (S₁ : Finset F.Cell) (hS₁ : S₁ ⊆ D.keptCells) :
    ∃ v : ℕ, D.HasCoreHotLumps C v ∧ (cH / 16) * v ≤ D.totalEnergy - D.energyOn S₁ ∧
      D.hotTopLumps.card ≤ v + 16 * ((D.excitedCells C).card + (D.crowdedCells).card) := by
  classical
  obtain ⟨p, x, hpx⟩ := exists_hot_plaquette_choice D hL
  have hnear : ∀ (A : Finset (Finset F.Cell)) (y : F.Cell) (r : ℕ), 2 * r + 1 ≤ 2 ^ 14 →
      (∀ l ∈ A, l ∈ D.hotTopLumps ∧ cellSupDist (x l) y ≤ r) → A.card ≤ 16 := by
    intro A y r hr hA
    by_cases hE : D.hotTopLumps = ∅
    · have : A = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
        have := (hA l hl).1
        rw [hE] at this
        simp at this
      rw [this]
      simp
    · refine card_lumps_near_le g hL (hdiv hE) y r hr A fun l hl => ?_
      obtain ⟨hl1, hl2⟩ := hA l hl
      obtain ⟨_, _, _, hlx⟩ := hpx l hl1
      exact ⟨⟨x l, hlx⟩, x l, mem_of_eq_lumpOf (g := g) hL hlx, hl2⟩
  let h1 : Finset (Finset F.Cell) := D.hotTopLumps.filter fun l => plaquetteCorners (p l) ⊆ D.coreCells C 5
  have hh1 : ∀ l ∈ h1, l ∈ D.hotTopLumps ∧ plaquetteCorners (p l) ⊆ D.coreCells C 5 :=
    fun l hl => Finset.mem_filter.1 hl
  refine ⟨h1.card, ⟨h1, p, Finset.filter_subset _ _, rfl, fun l hl => ?_⟩, ?_, ?_⟩
  · obtain ⟨ht, hc⟩ := hh1 l hl
    obtain ⟨a1, a2, a3, a4⟩ := hpx l ht
    exact ⟨a1, a2, hc, x l, a3, mem_of_eq_lumpOf (g := g) hL a4⟩
  · have hsum := sum_energyOn_le D ha hF h1 (fun l => plaquetteCorners (p l)) S₁ 16
      (hS₁.trans (keptCells_subset D))
      (fun l hl => (plaquetteCorners_subset (hpx l (hh1 l hl).1).1).2)
      (fun l hl => Finset.disjoint_left.2 fun c hc hc' =>
        corner_not_mem_keptCells D hL (hpx l (hh1 l hl).1).1 (hpx l (hh1 l hl).1).2.1 hc (hS₁ hc'))
      (fun y _ => by
        refine hnear _ y 1 (by norm_num) fun l hl => ?_
        obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
        have ht := (hh1 l hl1).1
        obtain ⟨a1, _, a3, _⟩ := hpx l ht
        exact ⟨ht, cellSupDist_corners_le_one hs (plaquetteCorners_subset a1).1 a3 hl2⟩)
    have hlow : h1.card • cH ≤ ∑ l ∈ h1, D.energyOn (plaquetteCorners (p l)) :=
      Finset.card_nsmul_le_sum _ _ _ fun l hl =>
        hprice _ (hpx l (hh1 l hl).1).1 (hpx l (hh1 l hl).1).2.1 (hh1 l hl).2
    rw [nsmul_eq_mul] at hlow
    push_cast at hsum
    linarith
  · have hsub : D.hotTopLumps \ h1 ⊆ (D.badCells C).biUnion fun z =>
        D.hotTopLumps.filter fun l => cellSupDist (x l) z ≤ 5 := by
      intro l hl
      obtain ⟨ht, hn⟩ := Finset.mem_sdiff.1 hl
      obtain ⟨a1, _, a3, _⟩ := hpx l ht
      have hnot : ¬ plaquetteCorners (p l) ⊆ D.coreCells C 5 := fun h => hn (Finset.mem_filter.2 ⟨ht, h⟩)
      obtain ⟨c, hc, hcc⟩ := Finset.not_subset.1 hnot
      have hcS : c ∈ D.cells := (plaquetteCorners_subset a1).2 hc
      have : ¬ ∀ z ∈ D.badCells C, 5 ≤ cellSupDist c z := fun h => hcc (Finset.mem_filter.2 ⟨hcS, h⟩)
      push_neg at this
      obtain ⟨z, hz, hd⟩ := this
      have h2 := cellSupDist_le_add (x l) c z
      have h3 := cellSupDist_corners_le_one hs (plaquetteCorners_subset a1).1 a3 hc
      exact Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_filter.2 ⟨ht, by omega⟩⟩
    have hc1 : (D.hotTopLumps \ h1).card ≤ (D.badCells C).card * 16 :=
      (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ _ fun z _ =>
        hnear _ z 5 (by norm_num) fun l hl => Finset.mem_filter.1 hl)
    have hc2 : (D.badCells C).card ≤ (D.excitedCells C).card + (D.crowdedCells).card := Finset.card_union_le _ _
    have hc3 := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset (fun l => plaquetteCorners (p l) ⊆ D.coreCells C 5) D.hotTopLumps)
    have hc4 : (D.hotTopLumps \ h1).card + h1.card = D.hotTopLumps.card := hc3
    omega
end payment
section top
theorem mem_sitesOfCells_top (hL : Odd F.blockSide) {S : Finset F.Cell} {x : F.Cell} (hx : x ∈ S) :
    x ∈ sitesOfCells S F.top := by
  refine Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨0, ?_, ?_⟩⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have h0 : siteOfCoords (F := F) F.top (0 : Fin 4 → ℤ) = 0 := by
      funext k
      simp [siteOfCoords]
    have hc : cellCentre F.top x = x := by
      unfold cellCentre
      simp only [Nat.sub_self, pow_zero, one_mul]
      exact siteOfCoords_siteCoords x
    rw [h0, add_zero, hc]
theorem mem_innerPlaquettes_top (hL : Odd F.blockSide) {S : Finset F.Cell} {p : F.Cell × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes S) : p ∈ innerPlaquettes S F.top := by
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨mem_sitesOfCells_top hL hp.1, hp.2.1, fun c hc => mem_sitesOfCells_top hL (hp.2.2 hc)⟩
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
theorem hotTopLumps_eq_empty_of_cold (hL : Odd F.blockSide) (hL' : Odd L)
    (hc : IsCold D.cells F.top θ D.topField) : D.hotTopLumps = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  obtain ⟨p, hp, hh, _⟩ := exists_hot_plaquette_of_mem_hotLumps g hL' hl
  exact absurd hh (not_le.2 (hc p (mem_innerPlaquettes_top hL hp)))
theorem energyOn_corners_ge (hF : Odd F.blockSide) (hL : Odd L) (hs : ∀ i, 0 < F.extent i) (C cK e Θ : ℝ)
    (hcK : 0 < cK) (he : 0 ≤ e) (hΘ : 1 ≤ Θ) (hs0 : 0 < s) (hθ : θ = Θ * s)
    (hsmall : (Θ * s) ^ 2 ≤ (F.blockSide : ℝ) ^ (-4 : ℤ))
    (heJ : e * (4 * 81 * J₀ : ℕ) ≤ cK / 2) (U2 : F.FieldChain) (htop : U2 F.top = D.topField)
    (hK : ∀ p : F.Cell × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      cK * min (plaquetteDefect (U2 F.top) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
        cutChainEnergy a F.top (plaquetteCorners p) U2)
    (hcut : ∀ X ⊆ D.coreCells C 5,
      cutChainEnergy a F.top X U2 ≤ D.energyOn X + e * s ^ 2 * (D.nearbyFineLumps X).card)
    (p : F.Cell × Fin 4 × Fin 4) (hp : p ∈ cutPlaquettes D.cells) (hh : θ ≤ plaquetteDefect D.topField p)
    (hc : plaquetteCorners p ⊆ D.coreCells C 5) : cK / 2 * s ^ 2 ≤ D.energyOn (plaquetteCorners p) := by
  classical
  have h1 := hK p (plaquetteCorners_subset hp).1
  rw [htop] at h1
  have h2 := hcut _ hc
  have hcard : (D.nearbyFineLumps (plaquetteCorners p)).card ≤ 4 * 81 * J₀ := by
    refine (card_near_core_le D hF hL hs C (plaquetteCorners p) hc _ fun l hl => ?_).trans ?_
    · exact Finset.mem_filter.1 hl
    · have : (plaquetteCorners p).card ≤ 4 := Finset.card_le_four
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  have hΘs : 0 ≤ Θ * s := by positivity
  have hsq : (Θ * s) ^ 2 ≤ min (plaquetteDefect D.topField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) :=
    le_min (pow_le_pow_left₀ hΘs (hθ ▸ hh) 2) hsmall
  have hss : s ^ 2 ≤ (Θ * s) ^ 2 := pow_le_pow_left₀ hs0.le (le_mul_of_one_le_left hs0.le hΘ) 2
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have h3 : cK * s ^ 2 ≤ cK * min (plaquetteDefect D.topField p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) :=
    mul_le_mul_of_nonneg_left (hss.trans hsq) hcK.le
  have h4 : e * s ^ 2 * (D.nearbyFineLumps (plaquetteCorners p)).card ≤ cK / 2 * s ^ 2 := by
    have hcast : ((D.nearbyFineLumps (plaquetteCorners p)).card : ℝ) ≤ ((4 * 81 * J₀ : ℕ) : ℝ) := by
      exact_mod_cast hcard
    calc e * s ^ 2 * (D.nearbyFineLumps (plaquetteCorners p)).card
        ≤ e * s ^ 2 * ((4 * 81 * J₀ : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcast (mul_nonneg he hs2)
      _ = (e * ((4 * 81 * J₀ : ℕ) : ℝ)) * s ^ 2 := by ring
      _ ≤ cK / 2 * s ^ 2 := mul_le_mul_of_nonneg_right heJ hs2
  linarith
end top
end TopHotPlaquetteCost
theorem topHotPlaquettesPaid_holds (hK : ChainCoercivity) : topHotPlaquettesPaidStatement := by
  obtain ⟨cK, hc0, _, L₁, hco⟩ := hK
  refine ⟨cK / 32, by positivity, fun J₀ _ => ⟨cK / (2 * (((4 * 81 * J₀ : ℕ) : ℝ) + 1)), by positivity,
    fun a Θ C CJ ha hΘ hC hCJ => ⟨L₁, fun L hLo hLL g => ?_⟩⟩⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLo.pos
  have hΘ0 : 0 < Θ := by linarith
  refine ⟨1 / (Θ * (L : ℝ) ^ 2), by positivity, fun s hs0 hs F D U2 S₁ hFL hcub hth hfill hS₁ => ?_⟩
  subst hFL
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    rw [hcub.1 i]
    have := hcub.2
    omega
  have hamb : IsAdmissibleAmbient F := Or.inr fun i => by
    rw [hcub.1 i]
    have := hcub.2
    omega
  have hlevel := (hco a F.blockSide ha hLo hLL F rfl hamb F.top le_rfl).1
  have hsmall : (Θ * s) ^ 2 ≤ (F.blockSide : ℝ) ^ (-4 : ℤ) := by
    have h1 : Θ * s ≤ 1 / (F.blockSide : ℝ) ^ 2 := by
      have h2 : Θ * s ≤ Θ * (1 / (Θ * (F.blockSide : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hs hΘ0.le
      have h3 : Θ * (1 / (Θ * (F.blockSide : ℝ) ^ 2)) = 1 / (F.blockSide : ℝ) ^ 2 := by
        field_simp
      linarith
    have h4 : (F.blockSide : ℝ) ^ (-4 : ℤ) = (1 / (F.blockSide : ℝ) ^ 2) ^ 2 := by
      rw [zpow_neg]
      have : (F.blockSide : ℝ) ^ (4 : ℤ) = (F.blockSide : ℝ) ^ 4 := by norm_cast
      rw [this]
      field_simp
    rw [h4]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have heJ : cK / (2 * (((4 * 81 * J₀ : ℕ) : ℝ) + 1)) * ((4 * 81 * J₀ : ℕ) : ℝ) ≤ cK / 2 := by
    have hN : (0 : ℝ) ≤ ((4 * 81 * J₀ : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hprice := TopHotPlaquetteCost.energyOn_corners_ge D hLo hLo hpos C cK _ Θ hc0 (by positivity) hΘ hs0 rfl
    hsmall heJ U2 hfill.1 (fun p hp => hlevel p _ hp) hfill.2.1
  have hdiv : D.hotTopLumps ≠ ∅ → ∀ i, F.blockSide ∣ F.extent i := by
    intro hne i
    rcases hth with ⟨H, _, hd, _⟩ | ⟨_, hc⟩
    · rw [hcub.1 i]
      exact hd
    · exact absurd (TopHotPlaquetteCost.hotTopLumps_eq_empty_of_cold D hLo hLo hc) hne
  obtain ⟨v, h1, h2, h3⟩ :=
    TopHotPlaquetteCost.hotTopLumps_paid D hLo hLo (by linarith) hpos hdiv C (cK / 2 * s ^ 2) hprice S₁ hS₁
  refine ⟨v, h1, ?_, h3⟩
  have e : cK / 32 * s ^ 2 * (v : ℝ) = cK / 2 * s ^ 2 / 16 * v := by ring
  rw [e]
  exact h2
end HoleSavings
end YangMills.Construction
end
