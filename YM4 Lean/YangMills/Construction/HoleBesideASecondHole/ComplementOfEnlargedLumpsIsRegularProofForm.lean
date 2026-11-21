import YangMills.Construction.HoleBesideASecondHole.ComplementOfEnlargedLumpsIsRegular
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPayProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.HoleBounds
namespace ThickenedComplement
variable {F : BlockFrame}
theorem lumpRange_eq : lumpRange = 4096 := by norm_num [lumpRange]
section line
variable {p : ℕ} (G : PeriodicLineGrid p)
theorem right_right (c : ℤ) : G.right (G.right c) = G.right c := (G.interval_eq c (G.right c) (by linarith [G.left_le c, G.le_right c]) le_rfl).2
theorem left_left (c : ℤ) : G.left (G.left c) = G.left c := (G.interval_eq c (G.left c) le_rfl (by linarith [G.left_le c, G.le_right c])).1
theorem right_pred_left (c : ℤ) : G.right (G.left c - 1) = G.left c - 1 := by
  have h1 := G.le_right (G.left c - 1)
  by_contra hne
  have h2 : G.left c ≤ G.right (G.left c - 1) := by omega
  have h3 := (G.interval_eq (G.left c - 1) (G.left c) (by linarith [G.left_le (G.left c - 1)]) h2).1
  rw [left_left] at h3
  have := G.left_le (G.left c - 1)
  omega
theorem edges_far (c c' : ℤ) : 8188 < |(G.right c' + 4096) - (G.left c - 4096)| := by
  rw [lt_abs]
  by_cases h : G.left c ≤ G.right c'
  · left
    omega
  · set d := G.left c - 1 with hd
    have hd1 : G.right d = d := right_pred_left G c
    by_cases h2 : G.left d ≤ G.right c'
    · have h3 := (G.interval_eq d (G.right c') h2 (by omega)).2
      rw [right_right, hd1] at h3
      left
      omega
    · right
      have := (G.interval_length d).1
      norm_num at this
      omega
theorem exists_sign_preserving (u : ℤ) : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ∀ c x y : ℤ, |x - u| ≤ 4094 → |y - u| ≤ 4094 →
    0 ≤ e * (y - x) → G.left c - 4096 ≤ y → y ≤ G.right c + 4096 →
    G.left c - 4096 ≤ x ∧ x ≤ G.right c + 4096 := by
  by_cases hb : ∃ c1, u - 4094 < G.left c1 - 4096 ∧ G.left c1 - 4096 ≤ u + 4094
  · obtain ⟨c1, h1, h2⟩ := hb
    refine ⟨-1, Or.inr rfl, fun c x y hx hy he hl hh => ?_⟩
    have hx' := abs_le.1 hx
    have hy' := abs_le.1 hy
    refine ⟨by omega, ?_⟩
    by_contra hc
    have hap := edges_far G c1 c
    rw [lt_abs] at hap
    omega
  · refine ⟨1, Or.inl rfl, fun c x y hx hy he hl hh => ?_⟩
    have hx' := abs_le.1 hx
    have hy' := abs_le.1 hy
    refine ⟨?_, by omega⟩
    by_contra hc
    exact hb ⟨c, by omega, by omega⟩
theorem add_mul_period (m : ℤ) (c : ℤ) :
    G.left (c + m * p) = G.left c + m * p ∧ G.right (c + m * p) = G.right c + m * p := by
  induction m using Int.induction_on generalizing c with
  | zero => simp
  | succ k ih =>
    have e : c + ((k : ℤ) + 1) * p = (c + (k : ℤ) * p) + p := by ring
    rw [e, (G.periodic _).1, (G.periodic _).2, (ih c).1, (ih c).2]
    constructor <;> ring
  | pred k ih =>
    have e : c + (-(k : ℤ) - 1) * p + p = c + (-(k : ℤ)) * p := by ring
    have h1 := G.periodic (c + (-(k : ℤ) - 1) * p)
    rw [e, (ih c).1, (ih c).2] at h1
    constructor <;> linarith [h1.1, h1.2]
end line
theorem zmodCast_bounds {p : ℕ} (hp : 0 < p) (x : ZMod p) : 0 ≤ (ZMod.cast x : ℤ) ∧ (ZMod.cast x : ℤ) ≤ (p : ℤ) - 1 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [← ZMod.natCast_val]
  have := ZMod.val_lt x
  constructor
  · positivity
  · have h : ((x.val : ℕ) : ℤ) + 1 ≤ p := by exact_mod_cast this
    push_cast
    linarith
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) : ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem mem_torusCells (hs : ∀ i, 0 < F.extent i) (x : F.Cell) : x ∈ torusCells F := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.mem_torusCells <;> assumption
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) : siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem isOrthantRegular_cellsOffLumps (G : (i : Fin 4) → PeriodicLineGrid (F.extent i)) (H : Finset (Finset F.Cell))
    (hs : ∀ i, 0 < F.extent i) (hH : ∀ l ∈ H, ∃ c, l = gridBox G c) : IsOrthantRegular (cellsOffLumps F H) 2047 := by
  intro z
  choose e he hkeep using fun i => exists_sign_preserving (G i) (siteCoords z i)
  refine ⟨e, he, ?_⟩
  intro q hq hd h hsign hsize
  unfold cellsOffLumps at hq ⊢
  have hq' := Finset.mem_sdiff.1 hq
  refine Finset.mem_sdiff.2 ⟨mem_torusCells hs _, fun hin => hq'.2 ?_⟩
  simp only [lumpsNeighbourhood, Finset.mem_biUnion] at hin ⊢
  obtain ⟨l, hl, hnear⟩ := hin
  refine ⟨l, hl, ?_⟩
  obtain ⟨c, rfl⟩ := hH l hl
  simp only [lumpNeighbourhood, thicken, Finset.mem_biUnion, Finset.mem_image] at hnear
  suffices hgoal : ∃ x'' ∈ gridBox G c, ∃ k'' ∈ centredCube (2 * lumpRange + 1), x'' + siteOfCoords F.top k'' = q by
    simp only [lumpNeighbourhood, thicken, Finset.mem_biUnion, Finset.mem_image]
    exact hgoal
  obtain ⟨x', hx', k, hk, hxk⟩ := hnear
  simp only [gridBox, boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc] at hx'
  obtain ⟨a, ha, rfl⟩ := hx'
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, lumpRange_eq] at hk
  have hw : (((2 * 4096 + 1 : ℕ) : ℤ) - 1) / 2 = 4096 := by norm_num
  rw [hw] at hk
  set qt : Fin 4 → ℤ := fun i => siteCoords z i + ((q - z) i).valMinAbs with hqt
  have hq1 : siteOfCoords F.top qt = q := by
    funext i
    simp only [siteOfCoords, hqt]
    rw [Int.cast_add, siteCoords_cast, ZMod.coe_valMinAbs]
    simp
  have hdist : ∀ i, |((q - z) i).valMinAbs| ≤ 2047 := by
    intro i
    have h1 : ((q i - z i).valMinAbs).natAbs ≤ cellSupDist q z :=
      Finset.le_sup (f := fun i => ((q i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : ((q i - z i).valMinAbs).natAbs ≤ 2047 := h1.trans hd
    have h3 : |(q i - z i).valMinAbs| = (((q i - z i).valMinAbs).natAbs : ℤ) := Int.abs_eq_natAbs _
    simp only [Pi.sub_apply]
    rw [h3]
    exact_mod_cast h2
  have hshift : ∀ i, ∃ m : ℤ, qt i + h i = a i + k i + m * (F.extent i : ℤ) := by
    intro i
    have h1 := congrFun hxk i
    have h2 : ((qt i + h i : ℤ) : ZMod (F.period F.top i)) = ((a i + k i : ℤ) : ZMod (F.period F.top i)) := by
      have e1 : (q + siteOfCoords F.top h : F.Cell) i = ((qt i + h i : ℤ) : ZMod (F.period F.top i)) := by
        rw [← hq1]
        simp [siteOfCoords]
      have e2 : (siteOfCoords F.top a + siteOfCoords F.top k : F.Cell) i = ((a i + k i : ℤ) : ZMod (F.period F.top i)) := by
        simp [siteOfCoords]
      rw [← e1, ← e2]
      exact h1.symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_top] at h2
    obtain ⟨m, hm⟩ := h2
    exact ⟨-m, by rw [neg_mul, mul_comm m]; linarith⟩
  choose m hm using hshift
  have hgrid : ∀ i, (G i).left (c i) + m i * (F.extent i : ℤ) - 4096 ≤ qt i ∧
      qt i ≤ (G i).right (c i) + m i * (F.extent i : ℤ) + 4096 := by
    intro i
    have hp := add_mul_period (G i) (m i) (c i)
    have hx : |qt i - siteCoords z i| ≤ 4094 := by
      have := abs_le.1 (hdist i)
      rw [abs_le]
      simp only [hqt]
      constructor <;> linarith
    have hy : |qt i + h i - siteCoords z i| ≤ 4094 := by
      have a1 := abs_le.1 (hdist i)
      have a2 := abs_le.1 (hsize i)
      push_cast at a2
      rw [abs_le]
      simp only [hqt]
      constructor <;> linarith
    have hk1 := hk i
    have ha1 := ha i
    have := hkeep i (c i + m i * (F.extent i : ℤ)) (qt i) (qt i + h i) hx hy
      (by rw [add_sub_cancel_left]; exact hsign i)
      (by rw [hp.1, hm i]; linarith [hk1.1, ha1.1])
      (by rw [hp.2, hm i]; linarith [hk1.2, ha1.2])
    rw [hp.1, hp.2] at this
    exact this
  set b : Fin 4 → ℤ := fun i => max ((G i).left (c i)) (min ((G i).right (c i)) (qt i - m i * (F.extent i : ℤ))) with hb
  have hlohi : ∀ i, (G i).left (c i) ≤ (G i).right (c i) := fun i => ((G i).left_le (c i)).trans ((G i).le_right (c i))
  have hbm : siteOfCoords F.top b ∈ gridBox G c := by
    refine Finset.mem_image.2 ⟨b, Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_, rfl⟩
    simp only [hb]
    exact ⟨le_max_left _ _, max_le (hlohi i) (min_le_left _ _)⟩
  have hkm : (fun i => qt i - m i * (F.extent i : ℤ) - b i) ∈ centredCube (2 * lumpRange + 1) := by
    simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, lumpRange_eq]
    rw [hw]
    intro i
    have := hgrid i
    simp only [hb]
    rcases le_total ((G i).right (c i)) (qt i - m i * (F.extent i : ℤ)) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (hlohi i)]
      constructor <;> linarith [this.1, this.2]
    · rw [min_eq_right h1]
      rcases le_total ((G i).left (c i)) (qt i - m i * (F.extent i : ℤ)) with h2 | h2
      · rw [max_eq_right h2]
        constructor <;> linarith
      · rw [max_eq_left h2]
        constructor <;> linarith [this.1, this.2]
  have hsum : siteOfCoords F.top b + siteOfCoords F.top (fun i => qt i - m i * (F.extent i : ℤ) - b i) = q := by
    rw [← siteOfCoords_add]
    funext i
    have e : (siteOfCoords F.top (b + fun i => qt i - m i * (F.extent i : ℤ) - b i) : F.Cell) i =
        ((qt i - m i * (F.extent i : ℤ) : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e, ← hq1]
    simp only [siteOfCoords]
    have hz : (((F.extent i : ℕ) : ℤ) : ZMod (F.period F.top i)) = 0 := by
      rw [period_top]
      simp
    rw [Int.cast_sub, Int.cast_mul, hz]
    simp
  exact ⟨siteOfCoords F.top b, hbm, fun i => qt i - m i * (F.extent i : ℤ) - b i, hkm, hsum⟩
section block
variable {L : ℕ} (hL : Odd L)
include hL
theorem offsetFromCentre_abs_le (c : ℤ) : |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.abs_offsetFromCentre_le <;> assumption
theorem dvd_sub_offsetFromCentre (c : ℤ) : (L : ℤ) ∣ c - offsetFromCentre L c := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.dvd_sub_offsetFromCentre <;> assumption
theorem offsetFromCentre_add (t o : ℤ) (ht : (L : ℤ) ∣ t) (ho : |o| ≤ ((L : ℤ) - 1) / 2) : offsetFromCentre L (t + o) = o := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.offsetFromCentre_add <;> assumption
end block
def lineGridOfLumpGrid {L : ℕ} (g : LumpGrid L) (hL : Odd L) (p : ℕ) (hp : L ∣ p) : PeriodicLineGrid p where
  left := fun c => c - offsetFromCentre L c + g.lower (offsetFromCentre L c)
  right := fun c => c - offsetFromCentre L c + g.upper (offsetFromCentre L c)
  left_le := fun c => by
    have := (g.mem_interval _ (offsetFromCentre_abs_le hL c)).2.1
    linarith
  le_right := fun c => by
    have := (g.mem_interval _ (offsetFromCentre_abs_le hL c)).2.2.1
    linarith
  interval_eq := fun c c' h1 h2 => by
    have hb := offsetFromCentre_abs_le hL c
    have hg := g.mem_interval _ hb
    set o := offsetFromCentre L c with ho
    set t := c - o with ht
    have ho' : c' - t ∈ Set.Icc (g.lower o) (g.upper o) := ⟨by linarith, by linarith⟩
    have hr : |c' - t| ≤ ((L : ℤ) - 1) / 2 := by
      rw [abs_le]
      have := ho'.1
      have := ho'.2
      constructor <;> linarith [hg.1, hg.2.2.2]
    have e : offsetFromCentre L c' = c' - t := by
      have := offsetFromCentre_add hL t (c' - t) (dvd_sub_offsetFromCentre hL c) hr
      rwa [add_sub_cancel] at this
    have hs := g.interval_eq o (c' - t) hb ho'.1 ho'.2
    rw [e, hs.1, hs.2]
    constructor <;> ring
  interval_length := fun c => by
    have := g.interval_length _ (offsetFromCentre_abs_le hL c)
    constructor
    · linarith [this.1]
    · linarith [this.2]
  periodic := fun c => by
    have e : offsetFromCentre L (c + p) = offsetFromCentre L c := by
      have h1 := offsetFromCentre_add hL (c - offsetFromCentre L c + p) (offsetFromCentre L c)
        (dvd_add (dvd_sub_offsetFromCentre hL c) (by exact_mod_cast hp)) (offsetFromCentre_abs_le hL c)
      have e2 : c - offsetFromCentre L c + p + offsetFromCentre L c = c + p := by ring
      rwa [e2] at h1
    rw [e]
    constructor <;> ring
end ThickenedComplement
theorem complementOfThickenedLumpsRegular : ComplementOfThickenedLumpsRegular := by
  refine ⟨fun F G H hs hH => ThickenedComplement.isOrthantRegular_cellsOffLumps G H hs hH, ?_⟩
  intro L g F H hL hs hd hH
  refine ThickenedComplement.isOrthantRegular_cellsOffLumps
    (fun i => ThickenedComplement.lineGridOfLumpGrid g hL (F.extent i) (hd i)) H hs ?_
  intro l hl
  obtain ⟨x, rfl⟩ := hH l hl
  exact ⟨siteCoords x, rfl⟩
end YangMills.Construction.LumpContours
end
