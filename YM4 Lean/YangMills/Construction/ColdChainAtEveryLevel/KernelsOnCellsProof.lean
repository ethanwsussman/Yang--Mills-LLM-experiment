import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.ColdChainAtEveryLevel.FallOfTheVariations
import YangMills.Construction.ColdChainAtEveryLevel.KernelsOnCells
import YangMills.Construction.ColdChainAtEveryLevel.PowerWeightsThroughTheKernel
import YangMills.Construction.ColdChainAtEveryLevel.SharesAcrossABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.PatchPoints YangMills.Construction.GaugeMap YangMills.Construction.LatticeFractionalIntegration
namespace CellKernels
section Counting
def centredBox (r : ℕ) : Finset Lattice4 := Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r
theorem mem_centredBox {r : ℕ} {v : Lattice4} : v ∈ centredBox r ↔ ∀ i, |v i| ≤ r := by
  simp [centredBox, Fintype.mem_piFinset, abs_le]
theorem card_centredBox (r : ℕ) : (centredBox r).card = (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
theorem mem_centredBox_iff_supNorm {r : ℕ} {v : Lattice4} : v ∈ centredBox r ↔ supNorm v ≤ r := by
  rw [mem_centredBox]
  constructor
  · intro h
    refine Finset.sup_le fun i _ => ?_
    have := h i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  · intro h i
    have h1 : (v i).natAbs ≤ supNorm v :=
      Finset.le_sup (f := fun i => (v i).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans h
theorem card_clippedRadius_eq_le (N : ℕ) (p : Lattice4) (E : Finset Lattice4) {k : ℕ} (hk : k < N) (hk1 : 1 ≤ k) :
    (E.filter fun a => clippedRadius N p a = k).card ≤ 81 * k ^ 3 := by
  classical
  have hmem : ∀ a ∈ E.filter (fun a => clippedRadius N p a = k), max 1 (supNorm (a - p)) = k := by
    intro a ha
    have h1 := (Finset.mem_filter.1 ha).2
    unfold clippedRadius at h1
    omega
  have hinj : Set.InjOn (fun a : Lattice4 => a - p) (E.filter fun a => clippedRadius N p a = k : Finset Lattice4) :=
    fun a _ b _ h => sub_left_injective h
  rw [← Finset.card_image_of_injOn hinj]
  rcases Nat.lt_or_ge 1 k with h2 | h2
  · have hsub : (E.filter fun a => clippedRadius N p a = k).image (fun a : Lattice4 => a - p) ⊆
        centredBox k \ centredBox (k - 1) := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
      have h3 := hmem a ha
      refine Finset.mem_sdiff.2 ⟨mem_centredBox_iff_supNorm.2 (by omega), fun h4 => ?_⟩
      have := mem_centredBox_iff_supNorm.1 h4
      omega
    refine (Finset.card_le_card hsub).trans ?_
    have hc : (centredBox (k - 1)).card ≤ (centredBox k).card := by
      rw [card_centredBox, card_centredBox]
      exact Nat.pow_le_pow_left (by omega) 4
    have hs : centredBox (k - 1) ⊆ centredBox k := fun v hv =>
      mem_centredBox_iff_supNorm.2 ((mem_centredBox_iff_supNorm.1 hv).trans (by omega))
    rw [Finset.card_sdiff_of_subset hs, card_centredBox, card_centredBox]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e : (2 * (j + 1) + 1) ^ 4 = (2 * j + 1) ^ 4 + (64 * (j + 1) ^ 3 + 16 * (j + 1)) := by ring
    have e2 : 16 * (j + 1) ≤ 17 * (j + 1) ^ 3 := by nlinarith [Nat.zero_le j, sq_nonneg (j + 1)]
    omega
  · have hk' : k = 1 := by omega
    subst hk'
    have hsub : (E.filter fun a => clippedRadius N p a = 1).image (fun a : Lattice4 => a - p) ⊆ centredBox 1 := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
      have h3 := hmem a ha
      exact mem_centredBox_iff_supNorm.2 (by omega)
    refine (Finset.card_le_card hsub).trans ?_
    rw [card_centredBox]
    norm_num
theorem one_le_clippedRadius (N : ℕ) (hN : 1 ≤ N) (p a : Lattice4) : 1 ≤ clippedRadius N p a := by
  unfold clippedRadius
  omega
theorem clippedRadius_le (N : ℕ) (p a : Lattice4) : clippedRadius N p a ≤ N := by
  unfold clippedRadius
  omega
theorem sum_clippedRadius_rpow_le (N : ℕ) (hN : 1 ≤ N) (p : Lattice4) (E : Finset Lattice4) (hE : E.card ≤ N ^ 4)
    {γ : ℝ} (h0 : 0 ≤ γ) (h3 : γ ≤ 3) : ∑ a ∈ E, ((clippedRadius N p a : ℝ) / N) ^ (-γ) ≤ 83 * (N : ℝ) ^ 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmap : ∀ a ∈ E, clippedRadius N p a ∈ Finset.Icc 1 N := fun a _ =>
    Finset.mem_Icc.2 ⟨one_le_clippedRadius N hN p a, clippedRadius_le N p a⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hterm : ∀ k ∈ Finset.Icc 1 N, ∑ a ∈ E.filter (fun a => clippedRadius N p a = k),
      ((clippedRadius N p a : ℝ) / N) ^ (-γ) ≤ (if k = N then (N : ℝ) ^ 4 else 0) + 81 * (N : ℝ) ^ 3 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk1
    have e : ∑ a ∈ E.filter (fun a => clippedRadius N p a = k), ((clippedRadius N p a : ℝ) / N) ^ (-γ) =
        ((E.filter fun a => clippedRadius N p a = k).card : ℝ) * ((k : ℝ) / N) ^ (-γ) := by
      rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const, nsmul_eq_mul]
    rw [e]
    rcases Nat.lt_or_ge k N with hlt | hge
    · rw [if_neg (by omega), zero_add]
      have hc := card_clippedRadius_eq_le N p E hlt hk1
      have hc' : ((E.filter fun a => clippedRadius N p a = k).card : ℝ) ≤ 81 * (k : ℝ) ^ 3 := by exact_mod_cast hc
      set t : ℝ := (k : ℝ) / N with ht
      have ht0 : 0 < t := by positivity
      have ht1 : t ≤ 1 := by
        rw [ht, div_le_one hNr]
        exact_mod_cast hk2
      have hk3 : (k : ℝ) ^ 3 = t ^ (3 : ℕ) * (N : ℝ) ^ 3 := by
        rw [ht, div_pow]
        field_simp
      have h4 : t ^ (3 : ℕ) * t ^ (-γ) ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
        exact Real.rpow_le_one ht0.le ht1 (by push_cast; linarith)
      have hp0 : 0 ≤ t ^ (-γ) := (Real.rpow_pos_of_pos ht0 _).le
      calc _ ≤ 81 * (k : ℝ) ^ 3 * t ^ (-γ) := mul_le_mul_of_nonneg_right hc' hp0
        _ = 81 * (N : ℝ) ^ 3 * (t ^ (3 : ℕ) * t ^ (-γ)) := by rw [hk3]; ring
        _ ≤ 81 * (N : ℝ) ^ 3 * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    · have hkN : k = N := le_antisymm hk2 hge
      subst hkN
      rw [if_pos rfl, div_self hNr.ne', Real.one_rpow, mul_one]
      have h5 : ((E.filter fun a => clippedRadius k p a = k).card : ℝ) ≤ (k : ℝ) ^ 4 := by
        exact_mod_cast (Finset.card_filter_le _ _).trans hE
      have : (0 : ℝ) ≤ 81 * (k : ℝ) ^ 3 := by positivity
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have h6 : ∑ k ∈ Finset.Icc 1 N, (if k = N then (N : ℝ) ^ 4 else 0) = (N : ℝ) ^ 4 := by
    rw [Finset.sum_ite_eq']
    simp [hN]
  rw [h6]
  have e7 : ((N + 1 - 1 : ℕ) : ℝ) = N := by simp
  rw [e7]
  have : (N : ℝ) * (81 * (N : ℝ) ^ 3) = 81 * (N : ℝ) ^ 4 := by ring
  rw [this]
  have : (0 : ℝ) ≤ (N : ℝ) ^ 4 := by positivity
  linarith
end Counting
section Chart
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem min_max_sup_congr (N : ℕ) (hN : 1 ≤ N) (d e : Fin 4 → ℕ) (h : ∀ i, d i = e i ∨ (N ≤ d i ∧ N ≤ e i)) :
    min N (max 1 (Finset.univ.sup d)) = min N (max 1 (Finset.univ.sup e)) := by
  by_cases hx : ∃ i, N ≤ d i
  · obtain ⟨i, hi⟩ := hx
    have h1 : d i ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ i)
    have h2 : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
    have h3 : N ≤ e i := by
      rcases h i with h4 | h4
      · omega
      · exact h4.2
    omega
  · have hx : ∀ i, d i < N := fun i => not_le.1 fun hi => hx ⟨i, hi⟩
    have : d = e := by
      funext i
      rcases h i with h4 | h4
      · exact h4
      · have := hx i
        omega
    rw [this]
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem natAbs_valMinAbs_patchSite_sub (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (p : F.Site 0) {a : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) (i : Fin 4) :
    (((patchSite S z a - p) i).valMinAbs).natAbs = (a i - patchChart S z p i).natAbs ∨
      (F.blockSide ^ F.top ≤ (((patchSite S z a - p) i).valMinAbs).natAbs ∧
        F.blockSide ^ F.top ≤ (a i - patchChart S z p i).natAbs) := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set B : ℤ := closedOrthant S z i * (a i - patchChart S z p i) with hB
  have hcast : (patchSite S z a - p) i = ((B : ℤ) : ZMod (F.period 0 i)) := by
    conv_lhs => rw [← patchSite_patchChart he p]
    simp only [patchSite, siteOfCoords, Pi.sub_apply, Pi.add_apply, hB]
    push_cast
    ring
  have hBabs : B.natAbs = (a i - patchChart S z p i).natAbs := by
    rw [hB, Int.natAbs_mul]
    rcases he i with h | h <;> rw [h] <;> simp
  have hNn : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  rw [hcast, ← hBabs]
  rcases period_zero_eq_zero_or hamb hL i with hp | hp
  · left
    rw [valMinAbs_intCast_of_small (Or.inl hp)]
  · by_cases hs : 2 * |B| < (F.period 0 i : ℤ)
    · left
      rw [valMinAbs_intCast_of_small (Or.inr hs)]
    · right
      set v : ℤ := ((B : ZMod (F.period 0 i))).valMinAbs with hv
      set val : ℤ := ((p - cellCentre 0 z) i).valMinAbs with hval
      have hper0 : (F.period 0 i : ℤ) ≠ 0 := by omega
      have hpos : 0 < F.period 0 i := by
        rcases Nat.eq_zero_or_pos (F.period 0 i) with h | h
        · exact absurd (by exact_mod_cast h) hper0
        · exact h
      have : NeZero (F.period 0 i) := ⟨hpos.ne'⟩
      have hvb : 2 * |v| ≤ (F.period 0 i : ℤ) := by
        have := ZMod.natAbs_valMinAbs_le (n := F.period 0 i) ((B : ZMod (F.period 0 i)))
        rw [Int.abs_eq_natAbs]
        omega
      have hvalb : 2 * |val| ≤ (F.period 0 i : ℤ) := by
        have := ZMod.natAbs_valMinAbs_le (n := F.period 0 i) ((p - cellCentre 0 z) i)
        rw [Int.abs_eq_natAbs]
        omega
      have hdiv : (F.period 0 i : ℤ) ∣ B - v := by
        have h2 : ((v : ℤ) : ZMod (F.period 0 i)) = ((B : ℤ) : ZMod (F.period 0 i)) := ZMod.coe_valMinAbs _
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
        exact this
      have hBform : |B| ≤ |val| + 22 * cellSideLength F := by
        have e : B = closedOrthant S z i * (a i - (cellSideLength F - 1) / 2) - val := by
          simp only [hB, patchChart, hval]
          have := closedOrthant_mul_self he i
          calc _ = closedOrthant S z i * (a i - (cellSideLength F - 1) / 2) -
                (closedOrthant S z i * closedOrthant S z i) * ((p - cellCentre 0 z) i).valMinAbs := by ring
            _ = _ := by rw [this, one_mul]
        have h3 : |closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)| ≤ 22 * cellSideLength F := by
          rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
          have := ha i
          constructor <;> omega
        rw [e]
        have h4 := abs_sub (closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)) val
        omega
      have hBN : cellSideLength F ≤ |B| := by
        have hs := not_lt.1 hs
        omega
      have g1 : cellSideLength F ≤ |v| := by
        by_cases hz : B = v
        · rw [← hz]
          exact hBN
        · have hge : (F.period 0 i : ℤ) ≤ |B - v| :=
            Int.le_of_dvd (abs_pos.2 (sub_ne_zero.2 hz)) ((dvd_abs _ _).2 hdiv)
          have h5 := abs_sub B v
          omega
      constructor
      · have h6 : ((F.blockSide ^ F.top : ℕ) : ℤ) ≤ (v.natAbs : ℤ) := by
          rw [hNn, ← Int.abs_eq_natAbs]
          exact g1
        exact_mod_cast h6
      · have h6 : ((F.blockSide ^ F.top : ℕ) : ℤ) ≤ (B.natAbs : ℤ) := by
          rw [hNn, ← Int.abs_eq_natAbs]
          exact hBN
        exact_mod_cast h6
theorem scaleRadius_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (p : F.Site 0) {a : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) :
    scaleRadius F 0 p (patchSite S z a) = (clippedRadius (F.blockSide ^ F.top) (patchChart S z p) a : ℝ) := by
  have hL := hodd.pos
  have hN1 : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
  have h := min_max_sup_congr (F.blockSide ^ F.top) hN1
    (fun i => (((patchSite S z a - p) i).valMinAbs).natAbs)
    (fun i => (a i - patchChart S z p i).natAbs) (natAbs_valMinAbs_patchSite_sub hamb hodd he p ha)
  have e1 : baseDistance (patchSite S z a) p =
      Finset.univ.sup fun i => (((patchSite S z a - p) i).valMinAbs).natAbs := by
    simp only [baseDistance, baseSite_zero]
  have e2 : supNorm (a - patchChart S z p) =
      Finset.univ.sup fun i => (a i - patchChart S z p i).natAbs := rfl
  simp only [scaleRadius, clippedRadius, pow_zero]
  rw [e1, e2]
  rw [← h]
  push_cast
  rfl
end Chart
section Sums
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem sum_patchSiteSet (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (g : F.Site 0 → ℝ) : ∑ t ∈ patchSiteSet S z, g t = ∑ a ∈ patchDomain S z, g (patchSite S z a) := by apply _root_.YangMills.Construction.BondShares.sum_patchSiteSet_eq <;> assumption
theorem patchCubicKernel_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (f : F.Site 0 → ℝ) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    patchCubicKernel S z f (patchSite S z a) =
      ∑ b ∈ patchDomain S z, cubicKernel (a - b) * f (patchSite S z b) := by apply _root_.YangMills.Construction.BondShares.patchCubicKernel_patchSite_eq <;> assumption
theorem sum_cellSites_patchCubicKernel_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hP : patchSiteSet S z ⊆ sitesOfCells S 0) {q : ℝ} (hq : 0 < q) (w f : F.Site 0 → ℝ) (y : F.Cell) :
    ∑ x ∈ cellSites S y, |w x * patchCubicKernel S z f x| ^ q ≤
      ∑ a ∈ patchDomain S z,
        |w (patchSite S z a) * ∑ b ∈ patchDomain S z, cubicKernel (a - b) * f (patchSite S z b)| ^ q := by
  classical
  have h1 : ∑ x ∈ cellSites S y, |w x * patchCubicKernel S z f x| ^ q =
      ∑ x ∈ (cellSites S y).filter (fun x => x ∈ patchSiteSet S z), |w x * patchCubicKernel S z f x| ^ q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · simp [patchCubicKernel, h, Real.zero_rpow hq.ne']
  rw [h1]
  have h2 : ∑ x ∈ (cellSites S y).filter (fun x => x ∈ patchSiteSet S z), |w x * patchCubicKernel S z f x| ^ q ≤
      ∑ x ∈ patchSiteSet S z, |w x * patchCubicKernel S z f x| ^ q :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.1 hx).2)
      fun _ _ _ => Real.rpow_nonneg (abs_nonneg _) _
  refine h2.trans (le_of_eq ?_)
  rw [sum_patchSiteSet hamb hodd he]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [patchCubicKernel_patchSite hamb hodd he f ha]
theorem patch_lpNorm_le_sum_cellBall (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) {q : ℝ} (hq : 1 ≤ q) (w f : F.Site 0 → ℝ) :
    (∑ b ∈ patchDomain S z, |w (patchSite S z b) * f (patchSite S z b)| ^ q) ^ (1 / q) ≤
      ∑ y ∈ cellBall S z 20, weightedLpNormOnCell q S w (restrictToPatch S z f) y := by
  classical
  have hq0 : 0 < q := by linarith
  set g : F.Site 0 → ℝ := fun x => |w x * restrictToPatch S z f x| ^ q with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have h1 : ∑ b ∈ patchDomain S z, |w (patchSite S z b) * f (patchSite S z b)| ^ q =
      ∑ t ∈ patchSiteSet S z, g t := by
    rw [sum_patchSiteSet hamb hodd he]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hs : patchSite S z b ∈ patchSiteSet S z := Finset.mem_image_of_mem _ hb
    simp [hg, restrictToPatch, hs]
  have hsub : patchSiteSet S z ⊆ (cellBall S z 20).biUnion (cellSites S) := by
    intro t ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨h1, h2⟩ := enclosingCell_patchSite hamb hodd hreg hm hb
    refine Finset.mem_biUnion.2 ⟨enclosingCell (patchSite S z b), Finset.mem_filter.2 ⟨h1, ?_⟩, ?_⟩
    · rw [cellSupDist_symm]
      exact h2
    · exact Finset.mem_filter.2 ⟨patchSite_mem_sitesOfCells hamb hodd hreg hm hb, rfl⟩
  have h2 : ∑ t ∈ patchSiteSet S z, g t ≤ ∑ y ∈ cellBall S z 20, ∑ x ∈ cellSites S y, g x := by
    rw [← Finset.sum_biUnion]
    · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hg0 _
    · intro y _ y' _ hne
      refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
      rw [← (Finset.mem_filter.1 hx).2, ← (Finset.mem_filter.1 hx').2]
  rw [h1]
  have hr : 0 < 1 / q := by positivity
  have hr1 : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq
  calc _ ≤ (∑ y ∈ cellBall S z 20, ∑ x ∈ cellSites S y, g x) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => hg0 _) h2 hr.le
    _ ≤ ∑ y ∈ cellBall S z 20, (∑ x ∈ cellSites S y, g x) ^ (1 / q) :=
        rpow_sum_le_sum_rpow_of_le_one _ _ (fun _ _ => Finset.sum_nonneg fun _ _ => hg0 _) hr hr1
    _ = _ := rfl
theorem patchSiteSet_subset (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) :
    patchSiteSet S z ⊆ sitesOfCells S 0 := by
  intro t ht
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht
  exact patchSite_mem_sitesOfCells hamb hodd hreg hm hb
end Sums
section Generic
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem rpow_inv_le_of_le_rpow {q X K Y : ℝ} (hq : 0 < q) (hX : 0 ≤ X) (hKY : 0 ≤ K * Y) (h : X ≤ (K * Y) ^ q) :
    X ^ (1 / q) ≤ K * Y := by
  have h1 := Real.rpow_le_rpow hX h (by positivity : 0 ≤ 1 / q)
  rwa [← Real.rpow_mul hKY, show q * (1 / q) = 1 by field_simp, Real.rpow_one] at h1
theorem rpow_four_eq_pow (x : ℝ) : x ^ (4 : ℝ) = x ^ 4 := by apply _root_.YangMills.Construction.VariationDecay.rpow_four_eq_pow <;> assumption
theorem rpow_two_eq_pow (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [← Real.rpow_natCast]
  norm_num
theorem card_centredCube_of_odd {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_cellSites_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) :
    (cellSites S z).card ≤ (F.blockSide ^ F.top) ^ 4 := by
  classical
  have hsub : cellSites S z ⊆ (centredCube (F.blockSide ^ F.top)).image fun h => cellCentre 0 z + siteOfCoords 0 h := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.1 hx1
    have hh' : h ∈ centredCube (F.blockSide ^ F.top) := by simpa using hh
    rw [enclosingCell_cellCentre_add hodd y h hh] at hx2
    subst hx2
    exact Finset.mem_image_of_mem _ hh'
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [card_centredCube_of_odd (hodd.pow)]
theorem cellSideLength_cast (F : BlockFrame) : (cellSideLength F : ℝ) = ((F.blockSide ^ F.top : ℕ) : ℝ) := by
  simp [cellSideLength]
theorem patchChart_mem_patchDomain_of_mem_cellSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x : F.Site 0} (hx : x ∈ cellSites S z) :
    patchChart S z x ∈ patchDomain S z := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx1
  rw [enclosingCell_cellCentre_add hodd y h hh] at hx2
  subst hx2
  have hd : cellSupDist y y ≤ 10 := by
    simp [cellSupDist]
  exact patchChart_mem_patchDomain hamb hodd he hy hd (by simpa using hh)
theorem weightedLpNormOnCell_le_of_exponent_lt (hodd : Odd F.blockSide) {Q P : ℝ} (hQ : 0 < Q) (hQP : Q < P)
    (hd : 1 / Q - 1 / P = 1 / 4) (S : Finset F.Cell) (w f : F.Site 0 → ℝ) (z : F.Cell) :
    weightedLpNormOnCell Q S w f z ≤ 1 * (cellSideLength F : ℝ) * weightedLpNormOnCell P S w f z := by
  have h := lpNorm_le_card_rpow_mul_lpNorm (cellSites S z) (fun x => |w x * f x|) (fun _ => abs_nonneg _) hQ hQP
  simp only [weightedLpNormOnCell]
  refine h.trans ?_
  rw [one_mul]
  refine mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _)
  rw [hd]
  have hc : ((cellSites S z).card : ℝ) ≤ (cellSideLength F : ℝ) ^ (4 : ℕ) := by
    rw [cellSideLength_cast]
    exact_mod_cast card_cellSites_le hodd S z
  have hN : (0 : ℝ) ≤ (cellSideLength F : ℝ) := by
    have := cellSideLength_pos (F := F) hodd.pos
    exact_mod_cast this.le
  calc ((cellSites S z).card : ℝ) ^ (1 / 4 : ℝ) ≤ ((cellSideLength F : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hc (by norm_num)
    _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
        norm_num
theorem weightedLpNormOnCell_shift_le (hodd : Odd F.blockSide) {q c : ℝ} (hq : 1 ≤ q) (hc : 0 ≤ c)
    (w : F.Site 0 → ℝ)
    (hw : ∀ x ∈ sitesOfCells S 0, ∀ st : PathStep, x + stepDisplacement 0 st ∈ sitesOfCells S 0 →
      |w x| ≤ c * |w (x + stepDisplacement 0 st)|)
    (st : PathStep) (f : F.Site 0 → ℝ) (z : F.Cell) (hf : ∀ x, x ∉ sitesOfCells S 0 → f x = 0) :
    weightedLpNormOnCell q S w (fun x => f (x + stepDisplacement 0 st)) z ≤
      c * ∑ y ∈ cellBall S z 1, weightedLpNormOnCell q S w f y := by
  classical
  have hq0 : 0 < q := by linarith
  set g : F.Site 0 → ℝ := fun x => |w x * f x| ^ q with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hterm : ∀ x ∈ cellSites S z, |w x * f (x + stepDisplacement 0 st)| ^ q ≤
      c ^ q * (if x + stepDisplacement 0 st ∈ sitesOfCells S 0 then g (x + stepDisplacement 0 st) else 0) := by
    intro x hx
    by_cases h : x + stepDisplacement 0 st ∈ sitesOfCells S 0
    · rw [if_pos h]
      have hxs : x ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hx).1
      have h1 : |w x * f (x + stepDisplacement 0 st)| ≤
          c * |w (x + stepDisplacement 0 st) * f (x + stepDisplacement 0 st)| := by
        rw [abs_mul, abs_mul]
        calc _ ≤ (c * |w (x + stepDisplacement 0 st)|) * |f (x + stepDisplacement 0 st)| :=
              mul_le_mul_of_nonneg_right (hw x hxs st h) (abs_nonneg _)
          _ = _ := by ring
      calc _ ≤ (c * |w (x + stepDisplacement 0 st) * f (x + stepDisplacement 0 st)|) ^ q :=
            Real.rpow_le_rpow (abs_nonneg _) h1 hq0.le
        _ = _ := Real.mul_rpow hc (abs_nonneg _)
    · rw [if_neg h, hf _ h]
      simp [Real.zero_rpow hq0.ne']
  set A := (cellSites S z).filter (fun x => x + stepDisplacement 0 st ∈ sitesOfCells S 0) with hA
  have hsum : ∑ x ∈ cellSites S z,
      (if x + stepDisplacement 0 st ∈ sitesOfCells S 0 then g (x + stepDisplacement 0 st) else 0) ≤
      ∑ y ∈ cellBall S z 1, ∑ x ∈ cellSites S y, g x := by
    rw [← Finset.sum_filter, ← hA]
    have e1 : ∑ x ∈ A, g (x + stepDisplacement 0 st) = ∑ x ∈ A.image (fun x => x + stepDisplacement 0 st), g x :=
      (Finset.sum_image fun a _ b _ h => add_right_cancel h).symm
    rw [e1, ← Finset.sum_biUnion]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hg0 _
      intro x' hx'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨hx3, hx4⟩ := Finset.mem_filter.1 hx1
      obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx3
      have hh' : h ∈ centredCube (F.blockSide ^ F.top) := by simpa using hh
      rw [enclosingCell_cellCentre_add hodd y h hh] at hx4
      subst hx4
      refine Finset.mem_biUnion.2 ⟨enclosingCell (cellCentre 0 y + siteOfCoords 0 h + stepDisplacement 0 st),
        Finset.mem_filter.2 ⟨?_, ?_⟩, Finset.mem_filter.2 ⟨hx2, rfl⟩⟩
      · obtain ⟨y', hy', h', hh2, e⟩ := mem_sitesOfCells.1 hx2
        rw [e, enclosingCell_cellCentre_add hodd y' h' hh2]
        exact hy'
      · rw [cellSupDist_symm]
        exact cellSupDist_enclosingCell_step hodd hh' st
    · intro y _ y' _ hne
      refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
      rw [← (Finset.mem_filter.1 hx).2, ← (Finset.mem_filter.1 hx').2]
  have hcq : 0 ≤ c ^ q := Real.rpow_nonneg hc _
  have hr : 0 < 1 / q := by positivity
  have hr1 : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq
  have hTot : 0 ≤ ∑ y ∈ cellBall S z 1, ∑ x ∈ cellSites S y, g x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg0 _
  calc _ ≤ (c ^ q * ∑ y ∈ cellBall S z 1, ∑ x ∈ cellSites S y, g x) ^ (1 / q) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) ?_ hr.le
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hsum hcq
    _ = c * (∑ y ∈ cellBall S z 1, ∑ x ∈ cellSites S y, g x) ^ (1 / q) := by
        rw [Real.mul_rpow hcq hTot, ← Real.rpow_mul hc, show q * (1 / q) = 1 by field_simp, Real.rpow_one]
    _ ≤ c * ∑ y ∈ cellBall S z 1, (∑ x ∈ cellSites S y, g x) ^ (1 / q) :=
        mul_le_mul_of_nonneg_left
          (rpow_sum_le_sum_rpow_of_le_one _ _ (fun _ _ => Finset.sum_nonneg fun _ _ => hg0 _) hr hr1) hc
    _ = _ := rfl
end Generic
section Weighted
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem one_le_scaleRadius (hL : 0 < F.blockSide) (p x : F.Site 0) : 1 ≤ scaleRadius F 0 p x := by
  simp only [scaleRadius, pow_zero]
  have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ (by exact_mod_cast hL)
  exact le_min h1 (le_max_left _ _)
theorem scaleRadius_le (p x : F.Site 0) : scaleRadius F 0 p x ≤ (F.blockSide : ℝ) ^ F.top := min_le_left _ _
theorem scaleRadius_div_pos (hL : 0 < F.blockSide) (p x : F.Site 0) :
    0 < scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top := by
  have h1 := one_le_scaleRadius hL p x
  positivity
theorem scaleRadius_div_le_one (hL : 0 < F.blockSide) (p x : F.Site 0) :
    scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top ≤ 1 := by
  have h2 : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  rw [div_le_one h2]
  exact scaleRadius_le p x
theorem sum_scaleRadius_rpow_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (p : F.Site 0) {γ : ℝ} (h0 : 0 ≤ γ) (h3 : γ ≤ 3) :
    ∑ x ∈ cellSites S z, (scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top) ^ (-γ) ≤
      83 * ((F.blockSide : ℝ) ^ F.top) ^ 4 := by
  classical
  have hN1 : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hodd.pos
  have hinj : Set.InjOn (patchChart S z) (cellSites S z : Set (F.Site 0)) := by
    intro x _ y _ h
    rw [← patchSite_patchChart he x, h, patchSite_patchChart he y]
  have hcard : ((cellSites S z).image (patchChart S z)).card ≤ (F.blockSide ^ F.top) ^ 4 :=
    Finset.card_image_le.trans (card_cellSites_le hodd S z)
  have hs := sum_clippedRadius_rpow_le (F.blockSide ^ F.top) hN1 (patchChart S z p) _ hcard h0 h3
  rw [Finset.sum_image hinj] at hs
  push_cast at hs
  refine le_trans (le_of_eq ?_) hs
  refine Finset.sum_congr rfl fun x hx => ?_
  have ha := patchChart_mem_patchDomain_of_mem_cellSites hamb hodd he hx
  have e := scaleRadius_patchSite hamb hodd he p (a := patchChart S z x) (patchDomain_coord_bounds ha)
  rw [patchSite_patchChart he] at e
  rw [e]
theorem rpow_pow_eq (r : ℝ) (hr : 0 < r) (β : ℝ) (n : ℕ) : (r ^ β) ^ n = r ^ (β * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
theorem rpow_le_rpow_neg_abs {r β : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : r ^ β ≤ r ^ (-|β|) :=
  Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith [neg_abs_le β])
theorem classWeight_of_mem_cellSites (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) {x : F.Site 0}
    (hx : x ∈ cellSites S z) :
    classWeight F φ θ p 0 x = Real.exp (φ z) * (scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := by
  have : enclosingCell x = z := (Finset.mem_filter.1 hx).2
  simp [classWeight, this]
theorem weighted_norms_const_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (φ : F.Cell → ℝ) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) :
    weightedLpNormOnCell 4 S (classWeight F φ θ p 0) (fun _ => 1) z +
        weightedLpNormOnCell 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) (fun _ => 1) z ≤
      14 * (cellSideLength F : ℝ) * Real.exp (φ z) := by
  have hL := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  have hNc : (cellSideLength F : ℝ) = N := by simp [cellSideLength, hN]
  set A : ℝ := Real.exp (φ z) with hA
  have hA0 : 0 < A := Real.exp_pos _
  rw [hNc]
  have h1 : weightedLpNormOnCell 4 S (classWeight F φ θ p 0) (fun _ => 1) z ≤ 4 * (N * A) := by
    refine rpow_inv_le_of_le_rpow (by norm_num)
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity) ?_
    have hb : ∀ x ∈ cellSites S z, |classWeight F φ θ p 0 x * 1| ^ (4 : ℝ) ≤
        A ^ 4 * (scaleRadius F 0 p x / N) ^ (-|4 * θ|) := by
      intro x hx
      have hr0 : 0 < scaleRadius F 0 p x / N := scaleRadius_div_pos hL p x
      have hr1 : scaleRadius F 0 p x / N ≤ 1 := scaleRadius_div_le_one hL p x
      set r := scaleRadius F 0 p x / N with hr
      have hw : classWeight F φ θ p 0 x = A * r ^ (-θ) := classWeight_of_mem_cellSites φ θ p hx
      have hrp : 0 < r ^ (-θ) := Real.rpow_pos_of_pos hr0 _
      rw [mul_one, hw, abs_of_pos (by positivity), rpow_four_eq_pow, mul_pow, rpow_pow_eq r hr0 (-θ) 4]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := rpow_le_rpow_neg_abs (β := -θ * ((4 : ℕ) : ℝ)) hr0 hr1
      refine this.trans (le_of_eq ?_)
      congr 2
      push_cast
      rw [show -θ * 4 = -(4 * θ) by ring, abs_neg]
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have hs := sum_scaleRadius_rpow_le hamb hodd he (S := S) (z := z) p (γ := |4 * θ|) (abs_nonneg _)
      (by rw [abs_mul]; norm_num; linarith)
    rw [rpow_four_eq_pow]
    calc _ ≤ A ^ 4 * (83 * N ^ 4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (4 * (N * A)) ^ 4 := by
          have : 0 ≤ N ^ 4 * A ^ 4 := by positivity
          nlinarith
  have h2 : weightedLpNormOnCell 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) (fun _ => 1) z ≤
      10 * (N * A) := by
    refine rpow_inv_le_of_le_rpow (by norm_num)
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity) ?_
    have hb : ∀ x ∈ cellSites S z, |classWeight F φ θ p 0 x / scaleRadius F 0 p x * 1| ^ (2 : ℝ) ≤
        A ^ 2 / N ^ 2 * (scaleRadius F 0 p x / N) ^ (-(2 + |2 * θ|)) := by
      intro x hx
      have hr0 : 0 < scaleRadius F 0 p x / N := scaleRadius_div_pos hL p x
      have hr1 : scaleRadius F 0 p x / N ≤ 1 := scaleRadius_div_le_one hL p x
      have hρ : 0 < scaleRadius F 0 p x := by linarith [one_le_scaleRadius hL p x]
      set r := scaleRadius F 0 p x / N with hr
      have eρ : scaleRadius F 0 p x = r * N := by rw [hr]; field_simp
      have hw : classWeight F φ θ p 0 x = A * r ^ (-θ) := classWeight_of_mem_cellSites φ θ p hx
      have hrp : 0 < r ^ (-θ) := Real.rpow_pos_of_pos hr0 _
      rw [mul_one, hw, eρ, rpow_two_eq_pow, abs_of_pos (by positivity), div_pow, mul_pow, mul_pow,
        rpow_pow_eq r hr0 (-θ) 2]
      have e1 : r ^ (-(2 + |2 * θ|)) = r ^ (-|2 * θ|) * (r ^ 2)⁻¹ := by
        rw [neg_add, Real.rpow_add hr0, mul_comm, Real.rpow_neg hr0.le, ← Real.rpow_natCast r 2]
        norm_num
      rw [e1]
      have h3 := rpow_le_rpow_neg_abs (β := -θ * ((2 : ℕ) : ℝ)) hr0 hr1
      have h4 : r ^ (-|(-θ * ((2 : ℕ) : ℝ))|) = r ^ (-|2 * θ|) := by
        congr 2
        push_cast
        rw [show -θ * 2 = -(2 * θ) by ring, abs_neg]
      rw [h4] at h3
      calc A ^ 2 * r ^ (-θ * ((2 : ℕ) : ℝ)) / (r ^ 2 * N ^ 2)
          = A ^ 2 / N ^ 2 * (r ^ (-θ * ((2 : ℕ) : ℝ)) * (r ^ 2)⁻¹) := by field_simp
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h3 (by positivity)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have hθ2 : |2 * θ| ≤ 1 / 4 := by rw [abs_mul]; norm_num; linarith
    have hs := sum_scaleRadius_rpow_le hamb hodd he (S := S) (z := z) p (γ := 2 + |2 * θ|) (by positivity)
      (by linarith)
    rw [rpow_two_eq_pow]
    calc _ ≤ A ^ 2 / N ^ 2 * (83 * N ^ 4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 83 * (N * A) ^ 2 := by field_simp
      _ ≤ (10 * (N * A)) ^ 2 := by nlinarith [sq_nonneg (N * A)]
  linarith
end Weighted
section Instances
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem exp_mul_sum_abs_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (φ : F.Cell → ℝ) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) (f : F.Site 0 → ℝ) :
    Real.exp (φ z) * ∑ x ∈ cellSites S z, |f x| ≤
      83 * (cellSideLength F : ℝ) ^ 3 * weightedLpNormOnCell 4 S (classWeight F φ θ p 0) f z := by
  have hL := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  have hNc : (cellSideLength F : ℝ) = N := by simp [cellSideLength, hN]
  rw [hNc]
  set A : ℝ := Real.exp (φ z) with hA
  set q : ℝ := 4 / (4 - 1) with hq
  have hq0 : 0 < q := by rw [hq]; norm_num
  have hpq : (4 : ℝ).HolderConjugate q := Real.HolderConjugate.conjExponent (by norm_num)
  set r : F.Site 0 → ℝ := fun x => scaleRadius F 0 p x / N with hr
  have hr0 : ∀ x, 0 < r x := fun x => scaleRadius_div_pos hL p x
  have hr1 : ∀ x, r x ≤ 1 := fun x => scaleRadius_div_le_one hL p x
  have h1 := Real.inner_le_Lp_mul_Lq (cellSites S z) (fun x => |classWeight F φ θ p 0 x * f x|)
    (fun x => r x ^ θ) hpq
  have e1 : A * ∑ x ∈ cellSites S z, |f x| =
      ∑ x ∈ cellSites S z, |classWeight F φ θ p 0 x * f x| * r x ^ θ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hw : classWeight F φ θ p 0 x = A * r x ^ (-θ) := classWeight_of_mem_cellSites φ θ p hx
    have hrp : 0 < r x ^ (-θ) := Real.rpow_pos_of_pos (hr0 x) _
    rw [hw, abs_mul, abs_of_pos (show 0 < A * r x ^ (-θ) by positivity)]
    have e2 : r x ^ (-θ) * r x ^ θ = 1 := by
      rw [← Real.rpow_add (hr0 x)]
      simp
    calc A * |f x| = A * (r x ^ (-θ) * r x ^ θ) * |f x| := by rw [e2, mul_one]
      _ = _ := by ring
  rw [e1]
  refine h1.trans ?_
  have hS0 : 0 ≤ ∑ x ∈ cellSites S z, |r x ^ θ| ^ q :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have h2 : ∑ x ∈ cellSites S z, |r x ^ θ| ^ q ≤ 83 * N ^ 4 := by
    have hs := sum_scaleRadius_rpow_le hamb hodd he (S := S) (z := z) p (γ := |θ * q|) (abs_nonneg _)
      (by rw [abs_mul, abs_of_pos hq0, hq]; norm_num; linarith)
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) hs
    rw [abs_of_pos (Real.rpow_pos_of_pos (hr0 x) _), ← Real.rpow_mul (hr0 x).le]
    exact rpow_le_rpow_neg_abs (hr0 x) (hr1 x)
  have h3 : (∑ x ∈ cellSites S z, |r x ^ θ| ^ q) ^ (1 / q) ≤ 83 * N ^ 3 := by
    have e3 : 1 / q = 3 / 4 := by rw [hq]; norm_num
    rw [e3]
    calc _ ≤ (83 * N ^ 4) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hS0 h2 (by norm_num)
      _ = (83 : ℝ) ^ (3 / 4 : ℝ) * N ^ 3 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast N 4, ← Real.rpow_mul hN0.le,
            ← Real.rpow_natCast N 3]
          norm_num
      _ ≤ 83 * N ^ 3 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (83 : ℝ) ^ (3 / 4 : ℝ) ≤ (83 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 83 := Real.rpow_one _
  have e4 : ∑ x ∈ cellSites S z, |(|classWeight F φ θ p 0 x * f x|)| ^ (4 : ℝ) =
      ∑ x ∈ cellSites S z, |classWeight F φ θ p 0 x * f x| ^ (4 : ℝ) := by
    simp only [abs_abs]
  rw [e4]
  have h4 : 0 ≤ weightedLpNormOnCell 4 S (classWeight F φ θ p 0) f z :=
    Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  calc _ = weightedLpNormOnCell 4 S (classWeight F φ θ p 0) f z *
        (∑ x ∈ cellSites S z, |r x ^ θ| ^ q) ^ (1 / q) := rfl
    _ ≤ weightedLpNormOnCell 4 S (classWeight F φ θ p 0) f z * (83 * N ^ 3) := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by ring
theorem radialPowerWeight_pos (N : ℕ) (hN : 1 ≤ N) (p : Lattice4) (θ : ℝ) (a : Lattice4) :
    0 < radialPowerWeight N p θ a := by
  unfold radialPowerWeight
  have h1 : (1 : ℝ) ≤ clippedRadius N p a := by exact_mod_cast one_le_clippedRadius N hN p a
  exact Real.rpow_pos_of_pos (by positivity) _
theorem classWeight_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) {a : Lattice4}
    (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) :
    classWeight F φ θ p 0 (patchSite S z a) = Real.exp (φ (enclosingCell (patchSite S z a))) *
      radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a := by
  simp only [classWeight, radialPowerWeight]
  rw [scaleRadius_patchSite hamb hodd he p ha]
  push_cast
  rfl
theorem exp_le_exp_three_mul {φ : F.Cell → ℝ} {del : ℝ} (hdel : |del| ≤ 1 / 8)
    (hlip : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y')
    {y y' : F.Cell} (hd : cellSupDist y y' ≤ 24) : Real.exp (φ y) ≤ Real.exp 3 * Real.exp (φ y') := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := (abs_le.1 (hlip y y')).2
  have h2 : (cellSupDist y y' : ℝ) ≤ 24 := by exact_mod_cast hd
  have h3 : |del| * cellSupDist y y' ≤ 1 / 8 * 24 :=
    mul_le_mul hdel h2 (by positivity) (by norm_num)
  linarith
theorem weighted_kernel_bound_core {C1 E A : ℝ} (hC0 : 0 ≤ C1) (P : Finset Lattice4)
    (wS wr fS pw pwr Tn T ft : Lattice4 → ℝ) (hE1 : 1 ≤ E)
    (hA : 0 < A) (hw0 : ∀ a ∈ P, 0 ≤ wS a) (hpw0 : ∀ a, 0 < pw a) (hup : ∀ a ∈ P, wS a ≤ E * A * pw a)
    (hlo : ∀ a ∈ P, A * pw a ≤ E * wS a) (hwr : ∀ a ∈ P, |wr a| ≤ E * A * pwr a) (hpwr : ∀ a, 0 ≤ pwr a)
    (hTn0 : ∀ a, 0 ≤ Tn a) (hT : ∀ a, |T a| ≤ Tn a) (hft : ∀ b, ft b = |fS b|)
    (hF1 : ∑ a ∈ P, (pw a * Tn a) ^ 4 ≤ C1 * (∑ b ∈ P, (pw b * ft b) ^ 2) ^ 2)
    (hF2 : ∑ a ∈ P, (pwr a * Tn a) ^ 2 ≤ C1 * ∑ b ∈ P, (pw b * ft b) ^ 2) :
    (∑ a ∈ P, |wS a * T a| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) + (∑ a ∈ P, |wr a * T a| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      (2 * (E ^ 2 * (1 + C1))) * (∑ b ∈ P, |wS b * fS b| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hE0 : 0 < E := by linarith
  obtain ⟨Bq, hBqd⟩ : ∃ Bq, Bq = ∑ b ∈ P, (pw b * ft b) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = ∑ b ∈ P, |wS b * fS b| ^ (2 : ℝ) := ⟨_, rfl⟩
  rw [← hBqd] at hF1 hF2
  rw [← hQd]
  have hQ0 : 0 ≤ Q := hQd ▸ Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hBq0 : 0 ≤ Bq := hBqd ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hBQ : A ^ 2 * Bq ≤ E ^ 2 * Q := by
    rw [hBqd, hQd, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have e : |wS b * fS b| ^ (2 : ℝ) = wS b ^ 2 * ft b ^ 2 := by
      rw [rpow_two_eq_pow, abs_mul, mul_pow, sq_abs, hft]
    rw [e]
    have h3 := hlo b hb
    have h4 : 0 ≤ A * pw b := mul_nonneg hA.le (hpw0 b).le
    have h5 : (A * pw b) ^ 2 ≤ (E * wS b) ^ 2 := pow_le_pow_left₀ h4 h3 2
    have h6 : 0 ≤ ft b ^ 2 := sq_nonneg _
    have h7 := mul_le_mul_of_nonneg_right h5 h6
    calc A ^ 2 * (pw b * ft b) ^ 2 = (A * pw b) ^ 2 * ft b ^ 2 := by ring
      _ ≤ (E * wS b) ^ 2 * ft b ^ 2 := h7
      _ = _ := by ring
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = Q ^ (1 / (2 : ℝ)) := ⟨_, rfl⟩
  rw [← hYd]
  have hY0 : 0 ≤ Y := hYd ▸ Real.rpow_nonneg hQ0 _
  have hY2 : Y ^ 2 = Q := by
    rw [hYd, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hQ0
  obtain ⟨K, hKd⟩ : ∃ K, K = E ^ 2 * (1 + C1) := ⟨_, rfl⟩
  rw [← hKd]
  have hK1 : 1 ≤ 1 + C1 := by linarith
  have hK0 : 0 ≤ K := hKd ▸ mul_nonneg (sq_nonneg _) (by linarith)
  have h4 : (∑ a ∈ P, |wS a * T a| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) ≤ K * Y := by
    refine rpow_inv_le_of_le_rpow (by norm_num) (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
      (mul_nonneg hK0 hY0) ?_
    have hb : ∀ a ∈ P, |wS a * T a| ^ (4 : ℝ) ≤ (E * A) ^ 4 * (pw a * Tn a) ^ 4 := by
      intro a ha
      rw [rpow_four_eq_pow, ← mul_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
      rw [abs_mul, abs_of_nonneg (hw0 a ha)]
      calc wS a * |T a| ≤ (E * A * pw a) * Tn a :=
            mul_le_mul (hup a ha) (hT a) (abs_nonneg _) (mul_nonneg (mul_nonneg hE0.le hA.le) (hpw0 a).le)
        _ = _ := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum, rpow_four_eq_pow]
    have hEA : 0 ≤ (E * A) ^ 4 := by positivity
    calc (E * A) ^ 4 * ∑ a ∈ P, (pw a * Tn a) ^ 4 ≤ (E * A) ^ 4 * (C1 * Bq ^ 2) :=
          mul_le_mul_of_nonneg_left hF1 hEA
      _ = E ^ 4 * C1 * (A ^ 2 * Bq) ^ 2 := by ring
      _ ≤ E ^ 4 * C1 * (E ^ 2 * Q) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBQ 2) (by positivity)
      _ = E ^ 8 * C1 * Y ^ 4 := by rw [← hY2]; ring
      _ ≤ E ^ 8 * (1 + C1) ^ 4 * Y ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : (1 + C1) ^ 1 ≤ (1 + C1) ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
          linarith
      _ = _ := by rw [hKd]; ring
  have h2 : (∑ a ∈ P, |wr a * T a| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ K * Y := by
    refine rpow_inv_le_of_le_rpow (by norm_num) (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
      (mul_nonneg hK0 hY0) ?_
    have hb : ∀ a ∈ P, |wr a * T a| ^ (2 : ℝ) ≤ (E * A) ^ 2 * (pwr a * Tn a) ^ 2 := by
      intro a ha
      rw [rpow_two_eq_pow, ← mul_pow, ← sq_abs (E * A * (pwr a * Tn a))]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg hE0.le hA.le)
        (mul_nonneg (hpwr a) (hTn0 a)))]
      calc |wr a| * |T a| ≤ (E * A * pwr a) * Tn a :=
            mul_le_mul (hwr a ha) (hT a) (abs_nonneg _) (mul_nonneg (mul_nonneg hE0.le hA.le) (hpwr a))
        _ = _ := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum, rpow_two_eq_pow]
    have hEA : 0 ≤ (E * A) ^ 2 := by positivity
    calc (E * A) ^ 2 * ∑ a ∈ P, (pwr a * Tn a) ^ 2 ≤ (E * A) ^ 2 * (C1 * Bq) :=
          mul_le_mul_of_nonneg_left hF2 hEA
      _ = E ^ 2 * C1 * (A ^ 2 * Bq) := by ring
      _ ≤ E ^ 2 * C1 * (E ^ 2 * Q) := mul_le_mul_of_nonneg_left hBQ (by positivity)
      _ = E ^ 4 * C1 * Y ^ 2 := by rw [← hY2]; ring
      _ ≤ E ^ 4 * (1 + C1) ^ 2 * Y ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : (1 + C1) ^ 1 ≤ (1 + C1) ^ 2 := pow_le_pow_right₀ hK1 (by norm_num)
          linarith
      _ = _ := by rw [hKd]; ring
  linarith
theorem weighted_patchCubicKernel_le {C1 : ℝ} (hC0 : 0 ≤ C1)
    (hC1 : ∀ (N : ℕ) (p : Lattice4) (θ : ℝ) (D E : Finset Lattice4) (f : Lattice4 → ℝ),
      1 ≤ N → |θ| ≤ 1 / 8 → (∀ y, 0 ≤ f y) →
      ∑ x ∈ E, (radialPowerWeight N p θ x * ∑ y ∈ D, truncatedCubicKernel 64 N (x - y) * f y) ^ 4 ≤
        C1 * (∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2) ^ 2 ∧
      ∑ x ∈ E, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
          ∑ y ∈ D, truncatedCubicKernel 64 N (x - y) * f y) ^ 2 ≤
        C1 * ∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (φ : F.Cell → ℝ) {θ del : ℝ} (p : F.Site 0) (hθ : |θ| ≤ 1 / 8) (hdel : |del| ≤ 1 / 8)
    (hlip : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') (f : F.Site 0 → ℝ) (y : F.Cell) :
    weightedLpNormOnCell 4 S (classWeight F φ θ p 0) (patchCubicKernel S z f) y +
        weightedLpNormOnCell 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
          (patchCubicKernel S z f) y ≤
      (2 * (Real.exp 3 ^ 2 * (1 + C1))) *
        ∑ x ∈ cellBall S z 20, weightedLpNormOnCell 2 S (classWeight F φ θ p 0) (restrictToPatch S z f) x := by
  classical
  have hL := hodd.pos
  have hN1 : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
  have hE1 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hpw0 : ∀ a, 0 < radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a := fun a =>
    radialPowerWeight_pos _ hN1 _ θ a
  have hinv0 : ∀ v, 0 ≤ cubicKernel v := fun v => by
    unfold cubicKernel
    positivity
  have hcut0 : ∀ a, (0 : ℝ) < (clippedRadius (F.blockSide ^ F.top) (patchChart S z p) a : ℝ) := fun a => by
    exact_mod_cast one_le_clippedRadius _ hN1 _ a
  have hwa : ∀ a ∈ patchDomain S z, classWeight F φ θ p 0 (patchSite S z a) =
      Real.exp (φ (enclosingCell (patchSite S z a))) *
        radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a := fun a ha =>
    classWeight_patchSite hamb hodd he φ θ p (patchDomain_coord_bounds ha)
  have hcell : ∀ a ∈ patchDomain S z, cellSupDist (enclosingCell (patchSite S z a)) z ≤ 24 ∧
      cellSupDist z (enclosingCell (patchSite S z a)) ≤ 24 := by
    intro a ha
    have h2 := (enclosingCell_patchSite hamb hodd hreg hm ha).2
    refine ⟨h2.trans (by norm_num), ?_⟩
    rw [cellSupDist_symm]
    exact h2.trans (by norm_num)
  have hup : ∀ a ∈ patchDomain S z, classWeight F φ θ p 0 (patchSite S z a) ≤
      Real.exp 3 * Real.exp (φ z) * radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a := by
    intro a ha
    rw [hwa a ha]
    exact mul_le_mul_of_nonneg_right (exp_le_exp_three_mul hdel hlip (hcell a ha).1) (hpw0 a).le
  have hlo : ∀ a ∈ patchDomain S z,
      Real.exp (φ z) * radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a ≤
      Real.exp 3 * classWeight F φ θ p 0 (patchSite S z a) := by
    intro a ha
    rw [hwa a ha, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (exp_le_exp_three_mul hdel hlip (hcell a ha).2) (hpw0 a).le
  have hw0 : ∀ a ∈ patchDomain S z, 0 ≤ classWeight F φ θ p 0 (patchSite S z a) := fun a ha => by
    rw [hwa a ha]
    exact mul_nonneg (Real.exp_pos _).le (hpw0 a).le
  have hrk : ∀ a ∈ patchDomain S z, ∀ b ∈ patchDomain S z,
      truncatedCubicKernel 64 (F.blockSide ^ F.top) (a - b) = cubicKernel (a - b) := by
    intro a ha b hb
    unfold truncatedCubicKernel
    rw [if_pos]
    refine Finset.sup_le fun i _ => ?_
    have h1 := patchDomain_coord_bounds ha i
    have h2 := patchDomain_coord_bounds hb i
    have hN0 := cellSideLength_pos (F := F) hL
    have hNc : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
    have : (((a - b) i).natAbs : ℤ) ≤ ((64 * F.blockSide ^ F.top : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Nat.cast_mul, hNc, abs_le]
      simp only [Pi.sub_apply]
      push_cast
      constructor <;> omega
    exact_mod_cast this
  obtain ⟨hF1, hF2⟩ := hC1 (F.blockSide ^ F.top) (patchChart S z p) θ (patchDomain S z) (patchDomain S z)
    (fun b => |f (patchSite S z b)|) hN1 hθ (fun _ => abs_nonneg _)
  have eK : ∀ a ∈ patchDomain S z,
      ∑ b ∈ patchDomain S z, truncatedCubicKernel 64 (F.blockSide ^ F.top) (a - b) * |f (patchSite S z b)| =
      ∑ b ∈ patchDomain S z, cubicKernel (a - b) * |f (patchSite S z b)| := fun a ha =>
    Finset.sum_congr rfl fun b hb => by rw [hrk a ha b hb]
  rw [Finset.sum_congr rfl (fun a ha => by rw [eK a ha])] at hF1 hF2
  have hcore := weighted_kernel_bound_core hC0 (patchDomain S z)
    (fun a => classWeight F φ θ p 0 (patchSite S z a))
    (fun a => classWeight F φ θ p 0 (patchSite S z a) / scaleRadius F 0 p (patchSite S z a))
    (fun a => f (patchSite S z a))
    (radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ)
    (fun a => radialPowerWeight (F.blockSide ^ F.top) (patchChart S z p) θ a /
      (clippedRadius (F.blockSide ^ F.top) (patchChart S z p) a : ℝ))
    (fun a => ∑ b ∈ patchDomain S z, cubicKernel (a - b) * |f (patchSite S z b)|)
    (fun a => ∑ b ∈ patchDomain S z, cubicKernel (a - b) * f (patchSite S z b))
    (fun b => |f (patchSite S z b)|)
    hE1 (Real.exp_pos (φ z)) hw0 hpw0 hup hlo ?_ ?_ ?_ ?_ (fun _ => rfl) hF1 hF2
  · have hP' : patchSiteSet S z ⊆ sitesOfCells S 0 := patchSiteSet_subset hamb hodd hreg hm
    have hl4 := sum_cellSites_patchCubicKernel_le hamb hodd he hP' (q := 4) (by norm_num)
      (classWeight F φ θ p 0) f y
    have hl2 := sum_cellSites_patchCubicKernel_le hamb hodd he hP' (q := 2) (by norm_num)
      (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) f y
    have r4 := Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) hl4
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have r2 := Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) hl2
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hYc := patch_lpNorm_le_sum_cellBall hamb hodd he hreg hm (q := 2) (by norm_num)
      (classWeight F φ θ p 0) f (z := z)
    have hK : 0 ≤ 2 * (Real.exp 3 ^ 2 * (1 + C1)) := by positivity
    calc _ ≤ _ := add_le_add r4 r2
      _ ≤ _ := hcore
      _ ≤ _ := mul_le_mul_of_nonneg_left hYc hK
  · intro a ha
    have hra : scaleRadius F 0 p (patchSite S z a) =
        (clippedRadius (F.blockSide ^ F.top) (patchChart S z p) a : ℝ) :=
      scaleRadius_patchSite hamb hodd he p (patchDomain_coord_bounds ha)
    have hc := hcut0 a
    show |classWeight F φ θ p 0 (patchSite S z a) / scaleRadius F 0 p (patchSite S z a)| ≤ _
    rw [hra, abs_of_nonneg (div_nonneg (hw0 a ha) hc.le), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hup a ha) hc.le
  · exact fun a => div_nonneg (hpw0 a).le (hcut0 a).le
  · exact fun a => Finset.sum_nonneg fun b _ => mul_nonneg (hinv0 _) (abs_nonneg _)
  · intro a
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_of_nonneg (hinv0 _)]
end Instances
section Assembly
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem patchCubicKernel_lpNorm_le {C2 : ℝ} (hC0 : 0 ≤ C2)
    (hC2 : ∀ (D E : Finset Lattice4) (f : Lattice4 → ℝ),
      (∑ x ∈ E, |∑ y ∈ D, cubicKernel (x - y) * f y| ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) ≤
        C2 * (∑ y ∈ D, |f y| ^ (12 / 7 : ℝ)) ^ (1 / (12 / 7 : ℝ)))
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (f : F.Site 0 → ℝ) (y : F.Cell) :
    weightedLpNormOnCell 3 S (fun _ => 1) (patchCubicKernel S z f) y ≤
      C2 * ∑ x ∈ cellBall S z 20, weightedLpNormOnCell (12 / 7) S (fun _ => 1) (restrictToPatch S z f) x := by
  have hP' : patchSiteSet S z ⊆ sitesOfCells S 0 := patchSiteSet_subset hamb hodd hreg hm
  have h1 := sum_cellSites_patchCubicKernel_le hamb hodd he hP' (q := 3) (by norm_num) (fun _ => 1) f y
  have h2 := hC2 (patchDomain S z) (patchDomain S z) (fun b => f (patchSite S z b))
  have h3 := patch_lpNorm_le_sum_cellBall hamb hodd he hreg hm (q := 12 / 7) (by norm_num) (fun _ => 1) f (z := z)
  simp only [one_mul] at h1 h3
  calc _ ≤ (∑ a ∈ patchDomain S z,
        |∑ b ∈ patchDomain S z, cubicKernel (a - b) * f (patchSite S z b)| ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) ?_ (by norm_num)
        simpa using h1
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hC0
theorem scaleRadius_step_le (hL : 0 < F.blockSide) (p x : F.Site 0) (st : PathStep) :
    scaleRadius F 0 p x ≤ 2 * scaleRadius F 0 p (x + stepDisplacement 0 st) ∧
      scaleRadius F 0 p (x + stepDisplacement 0 st) ≤ 2 * scaleRadius F 0 p x := by
  have hd : baseDistance (x + stepDisplacement 0 st) p ≤ baseDistance x p + 1 ∧
      baseDistance x p ≤ baseDistance (x + stepDisplacement 0 st) p + 1 := by
    have hle : ∀ (u : F.Site 0) i, ((((baseSite u - p) i).valMinAbs).natAbs) ≤ baseDistance u p := fun u i =>
      Finset.le_sup (f := fun i => (((baseSite u - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
    constructor
    · refine Finset.sup_le fun i _ => ?_
      have e : (baseSite (x + stepDisplacement 0 st) - p : F.Site 0) i =
          (baseSite x - p : F.Site 0) i + (stepDisplacement (F := F) 0 st) i := by
        rw [baseSite_zero, baseSite_zero]
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [e]
      have h1 := natAbs_valMinAbs_add_le_add _ ((baseSite x - p : F.Site 0) i) ((stepDisplacement (F := F) 0 st) i)
      have h2 := hle x i
      have h3 := natAbs_valMinAbs_stepDisplacement_le (F := F) st i
      omega
    · refine Finset.sup_le fun i _ => ?_
      have e : (baseSite x - p : F.Site 0) i =
          (baseSite (x + stepDisplacement 0 st) - p : F.Site 0) i + (-(stepDisplacement (F := F) 0 st) i) := by
        rw [baseSite_zero, baseSite_zero]
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [e]
      have h1 := natAbs_valMinAbs_add_le_add _ ((baseSite (x + stepDisplacement 0 st) - p : F.Site 0) i)
        (-(stepDisplacement (F := F) 0 st) i)
      have h2 := hle (x + stepDisplacement 0 st) i
      have h3 := natAbs_valMinAbs_stepDisplacement_le (F := F) st i
      rw [ZMod.natAbs_valMinAbs_neg] at h1
      omega
  have hone : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := one_le_pow₀ (by exact_mod_cast hL)
  have hstep : ∀ d d' : ℕ, d ≤ d' + 1 → min ((F.blockSide : ℝ) ^ F.top) (max 1 (d : ℝ)) ≤
      2 * min ((F.blockSide : ℝ) ^ F.top) (max 1 (d' : ℝ)) := by
    intro d d' h
    have hr : (d : ℝ) ≤ d' + 1 := by exact_mod_cast h
    rcases le_total ((F.blockSide : ℝ) ^ F.top) (max 1 (d' : ℝ)) with h1 | h1
    · rw [min_eq_left h1]
      have := min_le_left ((F.blockSide : ℝ) ^ F.top) (max 1 (d : ℝ))
      linarith
    · rw [min_eq_right h1]
      refine (min_le_right _ _).trans ?_
      have h2 := le_max_left 1 (d' : ℝ)
      have h3 := le_max_right 1 (d' : ℝ)
      exact max_le (by linarith) (by linarith)
  simp only [scaleRadius, pow_zero]
  exact ⟨hstep _ _ hd.2, hstep _ _ hd.1⟩
theorem rpow_neg_le_two {t θ : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 2) (hθ : |θ| ≤ 1) : t ^ (-θ) ≤ 2 := by
  have ht : 0 < t := by linarith
  rcases le_total 1 t with h | h
  · calc t ^ (-θ) ≤ t ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h (by linarith [(abs_le.1 hθ).1])
      _ = t := Real.rpow_one _
      _ ≤ 2 := h2
  · calc t ^ (-θ) ≤ t ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [(abs_le.1 hθ).2])
      _ = t⁻¹ := Real.rpow_neg_one _
      _ ≤ 2 := by
          rw [inv_le_comm₀ ht (by norm_num)]
          linarith
theorem classWeight_le_step (hodd : Odd F.blockSide) {φ : F.Cell → ℝ} {θ del : ℝ} (p : F.Site 0)
    (hθ : |θ| ≤ 1 / 8) (hdel : |del| ≤ 1 / 8)
    (hlip : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') {x : F.Site 0} (hx : x ∈ sitesOfCells S 0)
    (st : PathStep) :
    classWeight F φ θ p 0 x ≤ (2 * Real.exp 3) * classWeight F φ θ p 0 (x + stepDisplacement 0 st) := by
  have hL := hodd.pos
  obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  set x := cellCentre 0 y + siteOfCoords 0 h with hxd
  have hcx : enclosingCell x = y := enclosingCell_cellCentre_add hodd y h hh
  have hd : cellSupDist (enclosingCell x) (enclosingCell (x + stepDisplacement 0 st)) ≤ 24 := by
    rw [hcx, cellSupDist_symm]
    exact (cellSupDist_enclosingCell_step hodd (by simpa using hh) st).trans (by norm_num)
  have h1 := exp_le_exp_three_mul hdel hlip hd
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN0 : 0 < N := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  set ρ := scaleRadius F 0 p x with hρ
  set ρ' := scaleRadius F 0 p (x + stepDisplacement 0 st) with hρ'
  have hρ0 : 0 < ρ := by linarith [one_le_scaleRadius hL p x]
  have hρ0' : 0 < ρ' := by linarith [one_le_scaleRadius hL p (x + stepDisplacement 0 st)]
  obtain ⟨h2, h3⟩ := scaleRadius_step_le hL p x st
  rw [← hρ, ← hρ'] at h2 h3
  have e : (ρ / N) ^ (-θ) = (ρ / ρ') ^ (-θ) * (ρ' / N) ^ (-θ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have h4 : (ρ / ρ') ^ (-θ) ≤ 2 := by
    refine rpow_neg_le_two ?_ ?_ (hθ.trans (by norm_num))
    · rw [le_div_iff₀ hρ0']
      linarith
    · rw [div_le_iff₀ hρ0']
      linarith
  have hp' : 0 < (ρ' / N) ^ (-θ) := Real.rpow_pos_of_pos (by positivity) _
  simp only [classWeight]
  rw [← hρ, ← hρ', ← hN, e]
  calc Real.exp (φ (enclosingCell x)) * ((ρ / ρ') ^ (-θ) * (ρ' / N) ^ (-θ))
      ≤ (Real.exp 3 * Real.exp (φ (enclosingCell (x + stepDisplacement 0 st)))) * (2 * (ρ' / N) ^ (-θ)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h4 hp'.le) (by positivity) (by positivity)
    _ = _ := by ring
theorem classWeight_pos (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p x : F.Site 0) :
    0 < classWeight F φ θ p 0 x := by
  have := scaleRadius_div_pos hL p x
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos this _)
theorem card_cellSites_le_cellSideLength_pow (hodd : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) :
    ((cellSites S z).card : ℝ) ≤ (cellSideLength F : ℝ) ^ (4 : ℕ) := by
  rw [cellSideLength_cast]
  exact_mod_cast card_cellSites_le hodd S z
end Assembly
end CellKernels
open CellKernels in
theorem BlockAverages.cellKernelBoundsStatement_holds (hP : powerWeightKernelStatement)
    (hH : hardyLittlewoodSobolevStatement) : cellKernelBoundsStatement := by
  obtain ⟨C1, hC1p, hC1⟩ := hP 64
  obtain ⟨C2, hC2p, hC2⟩ := hH (12 / 7) 3 (by norm_num) (by norm_num) (by norm_num)
  set E : ℝ := Real.exp 3 with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by norm_num)
  set C : ℝ := 100 + 8 * E + 2 * (E ^ 2 * (1 + C1)) + C2 with hC
  have hCk : 2 * (E ^ 2 * (1 + C1)) ≤ C := by
    rw [hC]
    linarith
  have hC100 : 100 ≤ C := by
    have : 0 ≤ 2 * (E ^ 2 * (1 + C1)) := by positivity
    rw [hC]
    linarith
  have hCE : 8 * E ≤ C := by
    have : 0 ≤ 2 * (E ^ 2 * (1 + C1)) := by positivity
    rw [hC]
    linarith
  have hC2le : C2 ≤ C := by
    have : 0 ≤ 2 * (E ^ 2 * (1 + C1)) := by positivity
    rw [hC]
    linarith
  refine ⟨C, by linarith, fun F m S hodd hamb hm hreg => ⟨fun φ θ del p hθ hdel hlip => ?_, ?_⟩⟩
  · have hL := hodd.pos
    have hN : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
    have hes : ∀ z : F.Cell, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := fun z =>
      (closedOrthant_spec (S := S) hreg (by omega) z).1
    set w := classWeight F φ θ p 0 with hw
    have hw0 : ∀ x, 0 < w x := classWeight_pos hL φ θ p
    have hmd := weightedLpNormOnCell_isCellSeminorm (q := 4) (by norm_num) S w
    have hrho := weightedLpNormOnCell_isCellSeminorm (q := 2) (by norm_num) S (fun x => w x / scaleRadius F 0 p x)
    have hsr := weightedLpNormOnCell_isCellSeminorm (q := 2) (by norm_num) S w
    have hstep : ∀ x ∈ sitesOfCells S 0, ∀ st : PathStep, x + stepDisplacement 0 st ∈ sitesOfCells S 0 →
        |w x| ≤ (2 * E) * |w (x + stepDisplacement 0 st)| := by
      intro x hx st _
      rw [abs_of_pos (hw0 _), abs_of_pos (hw0 _)]
      exact classWeight_le_step hodd p hθ hdel hlip hx st
    have hstepρ : ∀ x ∈ sitesOfCells S 0, ∀ st : PathStep, x + stepDisplacement 0 st ∈ sitesOfCells S 0 →
        |w x / scaleRadius F 0 p x| ≤
          (4 * E) * |w (x + stepDisplacement 0 st) / scaleRadius F 0 p (x + stepDisplacement 0 st)| := by
      intro x hx st _
      have h1 := one_le_scaleRadius hL p x
      have h2 := one_le_scaleRadius hL p (x + stepDisplacement 0 st)
      have hρ0 : 0 < scaleRadius F 0 p x := by linarith
      have hρ1 : 0 < scaleRadius F 0 p (x + stepDisplacement 0 st) := by linarith
      have h3 := (scaleRadius_step_le hL p x st).2
      have h4 := classWeight_le_step hodd p hθ hdel hlip hx st
      have hwx := hw0 x
      have hwy := hw0 (x + stepDisplacement 0 st)
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity), div_le_iff₀ hρ0]
      calc w x ≤ (2 * E) * w (x + stepDisplacement 0 st) := h4
        _ = (2 * E) * (w (x + stepDisplacement 0 st) / scaleRadius F 0 p (x + stepDisplacement 0 st)) *
              scaleRadius F 0 p (x + stepDisplacement 0 st) := by
              rw [mul_assoc (2 * E), div_mul_cancel₀ _ hρ1.ne']
        _ ≤ (2 * E) * (w (x + stepDisplacement 0 st) / scaleRadius F 0 p (x + stepDisplacement 0 st)) *
              (2 * scaleRadius F 0 p x) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    refine ⟨hmd, hmd.add hrho, hsr, fun f z => ?_, fun f z => ?_, fun z hz f y => ?_, fun z => ?_, fun f z => ?_,
      fun z => Real.exp_pos _, fun y z hd => ?_, fun st f z hf => ?_, fun st f z hf => ?_⟩
    · exact le_add_of_nonneg_right (hrho.nonneg f z)
    · have h1 := weightedLpNormOnCell_le_of_exponent_lt hodd (Q := 2) (P := 4) (by norm_num) (by norm_num)
        (by norm_num) S w f z
      refine h1.trans ?_
      have h2 := hmd.nonneg f z
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN.le) h2
      linarith
    · have h1 := weighted_patchCubicKernel_le hC1p.le (fun N p θ D E f a b c => hC1 N p θ D E f a b c) hamb hodd
        hreg (by omega) (hes z) φ p hθ hdel hlip f y
      refine h1.trans (mul_le_mul_of_nonneg_right hCk ?_)
      exact Finset.sum_nonneg fun _ _ => hsr.nonneg _ _
    · have h1 := weighted_norms_const_le hamb hodd (hes z) φ hθ p
      refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN.le) (Real.exp_pos _).le)
      linarith
    · have h1 := exp_mul_sum_abs_le hamb hodd (hes z) φ hθ p f
      refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
        (hmd.nonneg f z))
      linarith
    · have h1 := exp_le_exp_three_mul hdel hlip (hd.trans (by norm_num))
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith
    · have h1 := weightedLpNormOnCell_shift_le hodd (c := 2 * E) (q := 4) (by norm_num) (by positivity) w hstep
        st f z hf
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => hmd.nonneg _ _))
      linarith
    · have h1 := weightedLpNormOnCell_shift_le hodd (c := 2 * E) (q := 4) (by norm_num) (by positivity) w hstep
        st f z hf
      have h2 := weightedLpNormOnCell_shift_le hodd (c := 4 * E) (q := 2) (by norm_num) (by positivity)
        (fun x => w x / scaleRadius F 0 p x) hstepρ st f z hf
      have hs1 : ∑ y ∈ cellBall S z 1, weightedLpNormOnCell 4 S w f y ≤ ∑ y ∈ cellBall S z 1,
          (weightedLpNormOnCell 4 S w f y + weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) :=
        Finset.sum_le_sum fun y _ => by linarith [hrho.nonneg f y]
      have hs2 : ∑ y ∈ cellBall S z 1, weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y ≤
          ∑ y ∈ cellBall S z 1,
          (weightedLpNormOnCell 4 S w f y + weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) :=
        Finset.sum_le_sum fun y _ => by linarith [hmd.nonneg f y]
      have hT : 0 ≤ ∑ y ∈ cellBall S z 1,
          (weightedLpNormOnCell 4 S w f y + weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) :=
        Finset.sum_nonneg fun y _ => add_nonneg (hmd.nonneg f y) (hrho.nonneg f y)
      calc _ ≤ (2 * E) * ∑ y ∈ cellBall S z 1,
              (weightedLpNormOnCell 4 S w f y + weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) +
            (4 * E) * ∑ y ∈ cellBall S z 1,
              (weightedLpNormOnCell 4 S w f y + weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left hs1 (by positivity)))
              (h2.trans (mul_le_mul_of_nonneg_left hs2 (by positivity)))
        _ ≤ C * ∑ y ∈ cellBall S z 1,
              (weightedLpNormOnCell 4 S w f y +
                weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) := by
            have : (6 * E) * ∑ y ∈ cellBall S z 1,
                (weightedLpNormOnCell 4 S w f y +
                  weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) ≤
                C * ∑ y ∈ cellBall S z 1,
                (weightedLpNormOnCell 4 S w f y +
                  weightedLpNormOnCell 2 S (fun x => w x / scaleRadius F 0 p x) f y) :=
              mul_le_mul_of_nonneg_right (by linarith) hT
            linarith
  · have hL := hodd.pos
    have hNz : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
    have hes : ∀ z : F.Cell, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := fun z =>
      (closedOrthant_spec (S := S) hreg (by omega) z).1
    have hmd := weightedLpNormOnCell_isCellSeminorm (q := 3) (by norm_num) S (fun _ : F.Site 0 => (1 : ℝ))
    have hsr := weightedLpNormOnCell_isCellSeminorm (q := 12 / 7) (by norm_num) S (fun _ : F.Site 0 => (1 : ℝ))
    have hstep : ∀ x ∈ sitesOfCells S 0, ∀ st : PathStep, x + stepDisplacement 0 st ∈ sitesOfCells S 0 →
        |(1 : ℝ)| ≤ 1 * |(1 : ℝ)| := fun _ _ _ _ => by simp
    have hC1' : (1 : ℝ) ≤ C := by linarith
    refine ⟨hmd, hmd, hsr, fun _ _ => le_rfl, fun f z => ?_, fun z hz f y => ?_, fun z => ?_, fun f z => ?_,
      fun z => Real.rpow_pos_of_pos hNz _, fun y z _ => ?_, fun st f z hf => ?_, fun st f z hf => ?_⟩
    · have h1 := weightedLpNormOnCell_le_of_exponent_lt hodd (Q := 12 / 7) (P := 3) (by norm_num) (by norm_num)
        (by norm_num) S (fun _ => 1) f z
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1' hNz.le) (hmd.nonneg f z)
    · have h1 := patchCubicKernel_lpNorm_le hC2p.le (fun D E f => hC2 D E f) hamb hodd hreg (by omega) (hes z) f y
      refine h1.trans (mul_le_mul_of_nonneg_right hC2le ?_)
      exact Finset.sum_nonneg fun _ _ => hsr.nonneg _ _
    · have e1 : weightedLpNormOnCell 3 S (fun _ => 1) (fun _ => 1) z =
          ((cellSites S z).card : ℝ) ^ (1 / (3 : ℝ)) := by
        simp [weightedLpNormOnCell]
      rw [e1]
      have hc := card_cellSites_le_cellSideLength_pow hodd S z
      calc ((cellSites S z).card : ℝ) ^ (1 / (3 : ℝ)) ≤ ((cellSideLength F : ℝ) ^ (4 : ℕ)) ^ (1 / (3 : ℝ)) :=
            Real.rpow_le_rpow (by positivity) hc (by norm_num)
        _ = (cellSideLength F : ℝ) * (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNz.le]
            nth_rewrite 2 [← Real.rpow_one (cellSideLength F : ℝ)]
            rw [← Real.rpow_add hNz]
            norm_num
        _ ≤ C * (cellSideLength F : ℝ) * (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg hNz.le _)
    · have h1 := lpNorm_le_card_rpow_mul_lpNorm (cellSites S z) (fun x => |f x|) (fun _ => abs_nonneg _)
        (Q := 1) (P := 3) (by norm_num) (by norm_num)
      simp only [Real.rpow_one, div_one] at h1
      have e2 : (∑ i ∈ cellSites S z, |f i| ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) =
          weightedLpNormOnCell 3 S (fun _ => 1) f z := by
        simp [weightedLpNormOnCell]
      rw [e2] at h1
      have hc := card_cellSites_le_cellSideLength_pow hodd S z
      have h2 : ((cellSites S z).card : ℝ) ^ ((1 : ℝ) - 1 / 3) ≤ (cellSideLength F : ℝ) ^ ((8 : ℝ) / 3) := by
        calc ((cellSites S z).card : ℝ) ^ ((1 : ℝ) - 1 / 3) ≤
              ((cellSideLength F : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) - 1 / 3) :=
              Real.rpow_le_rpow (by positivity) hc (by norm_num)
          _ = _ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hNz.le]
              norm_num
      have hM := hmd.nonneg f z
      have hp : 0 ≤ (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hNz.le _
      calc (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) * ∑ x ∈ cellSites S z, |f x|
          ≤ (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) *
              ((cellSideLength F : ℝ) ^ ((8 : ℝ) / 3) * weightedLpNormOnCell 3 S (fun _ => 1) f z) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hM)) hp
        _ = (cellSideLength F : ℝ) ^ 3 * weightedLpNormOnCell 3 S (fun _ => 1) f z := by
            rw [← mul_assoc, ← Real.rpow_add hNz, ← Real.rpow_natCast]
            norm_num
        _ ≤ C * (cellSideLength F : ℝ) ^ 3 * weightedLpNormOnCell 3 S (fun _ => 1) f z := by
            refine mul_le_mul_of_nonneg_right ?_ hM
            have : 0 ≤ (cellSideLength F : ℝ) ^ 3 := by positivity
            nlinarith
    · have hp : 0 ≤ (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hNz.le _
      show (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) ≤ C * (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3)
      nlinarith
    · have h1 := weightedLpNormOnCell_shift_le hodd (c := 1) (q := 3) (by norm_num) (by norm_num) (fun _ => 1)
        hstep st f z hf
      refine h1.trans (mul_le_mul_of_nonneg_right hC1' (Finset.sum_nonneg fun _ _ => hmd.nonneg _ _))
    · have h1 := weightedLpNormOnCell_shift_le hodd (c := 1) (q := 3) (by norm_num) (by norm_num) (fun _ => 1)
        hstep st f z hf
      refine h1.trans (mul_le_mul_of_nonneg_right hC1' (Finset.sum_nonneg fun _ _ => hmd.nonneg _ _))
end YangMills.Construction
end
