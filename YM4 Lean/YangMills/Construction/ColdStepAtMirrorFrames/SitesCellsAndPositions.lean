import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfAFormInOneDirection
import YangMills.Construction.ColdStepAtMirrorFrames.PiecesOfTheTestOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.PositionsAboutAPointForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def sitePosition {j : ℕ} (z : F.Site j) : Fin 4 → ℝ := fun i => cellCoordinate z i
theorem distToMultiples_zero (n : ℝ) : distToMultiples n 0 = 0 := by
  simp [distToMultiples]
theorem distFromPoint_sitePosition_self {j : ℕ} (z : F.Site j) : distFromPoint (sitePosition z) z = 0 := by
  refine le_antisymm ?_ (distFromPoint_nonneg _ _)
  unfold distFromPoint
  refine Finset.sup'_le _ _ fun i _ => ?_
  simp [sitePosition, distToMultiples_zero]
theorem eq_add_siteOfCoords_valMinAbs {j : ℕ} (p z : F.Site j) :
    p = z + siteOfCoords j (fun i => ((p - z) i).valMinAbs) := by
  funext i
  simp only [siteOfCoords, Pi.add_apply]
  rw [ZMod.coe_valMinAbs]
  simp
theorem natAbs_valMinAbs_le_siteSupDist {j : ℕ} (p z : F.Site j) (i : Fin 4) :
    (((p - z) i).valMinAbs).natAbs ≤ siteSupDist p z :=
  Finset.le_sup (f := fun i => ((p i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem distFromPoint_le_add_siteSupDist (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (p z : F.Site j) (c : Fin 4 → ℝ) :
    distFromPoint c p ≤ distFromPoint c z + (siteSupDist p z : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  conv_lhs => rw [eq_add_siteOfCoords_valMinAbs p z]
  refine distFromPoint_add_le hL hs z _ c _ fun i => ?_
  refine div_le_div_of_nonneg_right ?_ hM.le
  have h := natAbs_valMinAbs_le_siteSupDist p z i
  have h2 : ((((p - z) i).valMinAbs.natAbs : ℕ) : ℝ) ≤ (siteSupDist p z : ℝ) := by exact_mod_cast h
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  simpa using h2
theorem siteSupDist_le_of_distFromPoint (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (p z : F.Site j) (r : ℕ)
    (h : distFromPoint (sitePosition z) p * (F.blockSide : ℝ) ^ (F.top - j) ≤ r) : siteSupDist p z ≤ r := by
  have hMp : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  refine Finset.sup_le fun i _ => ?_
  have hper : 0 < F.period j i := period_pos hL.pos hs j i
  have : NeZero (F.period j i) := ⟨hper.ne'⟩
  set d : ℤ := siteCoords p i - siteCoords z i with hd
  set s : ℝ := (F.extent i : ℝ) with hsdef
  set M : ℝ := (F.blockSide : ℝ) ^ (F.top - j) with hMdef
  set u : ℝ := cellCoordinate p i - sitePosition z i with hu
  have hu2 : u = (d : ℝ) / M := by
    rw [hu, hd]
    simp only [sitePosition, cellCoordinate]
    push_cast
    ring
  set k : ℤ := round (u / s) with hk
  have hgap : distToMultiples s u = |u - s * k| := rfl
  have hle := le_distFromPoint (sitePosition z) p i
  set w : ℤ := d - (F.period j i : ℤ) * k with hw
  have hw2 : u - s * k = (w : ℝ) / M := by
    rw [hw, hu2]
    have : (F.period j i : ℝ) = s * M := by
      rw [period_eq_extent_mul, hsdef, hMdef]
      push_cast
      rfl
    push_cast
    rw [this]
    field_simp
  have hcast : ((w : ℤ) : ZMod (F.period j i)) = p i - z i := by
    rw [hw, hd]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, sub_zero]
    have e1 : ((siteCoords p i : ℤ) : ZMod (F.period j i)) = p i := ZMod.intCast_zmod_cast (p i)
    have e2 : ((siteCoords z i : ℤ) : ZMod (F.period j i)) = z i := ZMod.intCast_zmod_cast (z i)
    rw [e1, e2]
  have hmin : ((p i - z i).valMinAbs).natAbs ≤ w.natAbs := by
    refine ZMod.natAbs_min_of_le_div_two _ _ _ ?_ (ZMod.natAbs_valMinAbs_le _)
    rw [ZMod.coe_valMinAbs, hcast]
  have hwr : ((w.natAbs : ℕ) : ℝ) ≤ r := by
    have h1 : |(w : ℝ)| / M ≤ distFromPoint (sitePosition z) p := by
      rw [← abs_of_pos hMp, ← abs_div, ← hw2, ← hgap]
      exact hle
    have h2 : |(w : ℝ)| ≤ distFromPoint (sitePosition z) p * M := by
      rwa [div_le_iff₀ hMp] at h1
    have h3 : ((w.natAbs : ℕ) : ℝ) = |(w : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      rfl
    rw [h3]
    exact h2.trans h
  have : w.natAbs ≤ r := by exact_mod_cast hwr
  exact hmin.trans this
theorem exists_centredCube_ancestorSite (hL : Odd F.blockSide) {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ F.top)
    (x : F.Site j) :
    ∃ h : Fin 4 → ℤ, h ∈ centredCube (F.blockSide ^ (l - j)) ∧
      x = refineSite j l (ancestorSite l x) + siteOfCoords j h := by
  obtain ⟨k, hk⟩ := hL.pow (n := l - j)
  have hMpos : (0 : ℤ) < ((F.blockSide ^ (l - j) : ℕ) : ℤ) := by
    have : 0 < F.blockSide ^ (l - j) := by omega
    exact_mod_cast this
  have hcast : ((F.blockSide ^ (l - j) : ℕ) : ℤ) = (F.blockSide : ℤ) ^ (l - j) := by push_cast; rfl
  have hMk : (F.blockSide : ℤ) ^ (l - j) = 2 * k + 1 := by
    rw [← hcast, hk]
    push_cast
    ring
  have e0 : ((F.blockSide : ℤ) ^ (l - j) - 1) / 2 = k := by
    rw [hMk]
    omega
  refine ⟨fun i => siteCoords x i - (F.blockSide : ℤ) ^ (l - j) *
    ((siteCoords x i + k) / (F.blockSide : ℤ) ^ (l - j)), ?_, ?_⟩
  · rw [mem_centredCube_iff hk]
    intro i
    have hp : (0 : ℤ) < (F.blockSide : ℤ) ^ (l - j) := by rw [← hcast]; exact hMpos
    have e1 := Int.emod_add_mul_ediv (siteCoords x i + k) ((F.blockSide : ℤ) ^ (l - j))
    have e2 := Int.emod_nonneg (siteCoords x i + k) hp.ne'
    have e3 := Int.emod_lt_of_pos (siteCoords x i + k) hp
    constructor <;> nlinarith
  · unfold ancestorSite
    rw [refineSite_siteOfCoords hjl hl, ← siteOfCoords_add, e0]
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    congr 1
    funext i
    simp only [Pi.add_apply]
    ring
theorem distFromPoint_ancestorSite_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j l : ℕ}
    (hjl : j ≤ l) (hl : l ≤ F.top) (x : F.Site j) (c : Fin 4 → ℝ) :
    distFromPoint c (ancestorSite l x) ≤ distFromPoint c x + 1 / (F.blockSide : ℝ) ^ (F.top - l) := by
  obtain ⟨h, hh, hx⟩ := exists_centredCube_ancestorSite hL hjl hl x
  obtain ⟨k, hk⟩ := hL.pow (n := l - j)
  have hb := (mem_centredCube_iff hk h).1 hh
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have e : refineSite j l (ancestorSite l x) = x + siteOfCoords j (-h) := by
    conv_rhs => rw [hx]
    rw [siteOfCoords_neg, add_neg_cancel_right]
  rw [← distFromPoint_refineSite hL hs hjl hl, e]
  refine distFromPoint_add_le hL hs x _ c _ fun i => ?_
  have hM : (F.blockSide : ℝ) ^ (F.top - j) =
      (F.blockSide : ℝ) ^ (F.top - l) * (F.blockSide : ℝ) ^ (l - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hM, div_le_div_iff₀ (by positivity) (by positivity)]
  have q := hb i
  have hz : (((F.blockSide ^ (l - j) : ℕ) : ℤ) : ℝ) = (F.blockSide : ℝ) ^ (l - j) := by push_cast; rfl
  have h1 : |(-h) i| ≤ ((F.blockSide ^ (l - j) : ℕ) : ℤ) := by
    have : ((F.blockSide ^ (l - j) : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    rw [this, abs_le]
    simp only [Pi.neg_apply]
    constructor <;> omega
  have h2 : ((|(-h) i| : ℤ) : ℝ) ≤ (((F.blockSide ^ (l - j) : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
  rw [hz] at h2
  push_cast at h2
  have hq : 0 < (F.blockSide : ℝ) ^ (F.top - l) := by positivity
  calc |((-h) i : ℝ)| * (F.blockSide : ℝ) ^ (F.top - l)
        ≤ (F.blockSide : ℝ) ^ (l - j) * (F.blockSide : ℝ) ^ (F.top - l) := by
        refine mul_le_mul_of_nonneg_right ?_ hq.le
        simpa using h2
    _ = _ := by ring
theorem enclosingCell_eq_ancestorSite {j : ℕ} (x : F.Site j) : enclosingCell x = ancestorSite F.top x := rfl
theorem distFromPoint_enclosingCell_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (x : F.Site j) (c : Fin 4 → ℝ) :
    distFromPoint c (enclosingCell x) ≤ distFromPoint c x + 1 := by
  have := distFromPoint_ancestorSite_le hL hs hj le_rfl x c
  rw [enclosingCell_eq_ancestorSite]
  simpa using this
theorem distFromPoint_le_enclosingCell (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (x : F.Site j) (c : Fin 4 → ℝ) :
    distFromPoint c x ≤ distFromPoint c (enclosingCell x) + 1 := by
  obtain ⟨h, hh, hx⟩ := exists_centredCube_ancestorSite hL hj le_rfl x
  obtain ⟨k, hk⟩ := hL.pow (n := F.top - j)
  have hb := (mem_centredCube_iff hk h).1 hh
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  rw [enclosingCell_eq_ancestorSite, ← distFromPoint_refineSite hL hs hj le_rfl (ancestorSite F.top x) c]
  conv_lhs => rw [hx]
  refine distFromPoint_add_le hL hs _ h c 1 fun i => ?_
  rw [div_le_one hM]
  have q := hb i
  have h1 : |h i| ≤ ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) := by
    have : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    rw [this, abs_le]
    constructor <;> omega
  have h2 : ((|h i| : ℤ) : ℝ) ≤ (((F.blockSide ^ (F.top - j) : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  simpa using h2
theorem weightedCurlNormSq_le_weightedNormSq (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (u v : F.Site j → ℝ) (h0 : ∀ x, u x ^ 2 ≤ v x ^ 2)
    (h1 : ∀ x k, u x ^ 2 ≤ v (x + unitStep j k) ^ 2) (X : LevelForm F j) :
    weightedCurlNormSq u X ≤ 96 * weightedNormSq v X := by
  rw [weightedCurlNormSq_eq_sum_orientedPlanes]
  have hp : ∀ e ∈ orientedPlanes, ∑ x ∈ allSites F j, (u x * plaquetteCurl X x e.1 e.2) ^ 2 ≤
      16 * weightedNormSq v X := by
    intro e _
    set W := weightedNormSq v X with hW
    have t : ∀ (k l : Fin 4),
        ∑ x ∈ allSites F j, (v (x + unitStep j k) * X (x + unitStep j k) l) ^ 2 ≤ W := by
      intro k l
      have := sum_allSites_add_right hL hs hj (unitStep j k) (fun x => (v x * X x l) ^ 2)
      rw [this]
      exact sum_sq_component_le_weightedNormSq v X l
    have t1 := sum_sq_component_le_weightedNormSq v X e.1
    have t2 := sum_sq_component_le_weightedNormSq v X e.2
    have t3 := t e.1 e.2
    have t4 := t e.2 e.1
    calc _ ≤ ∑ x ∈ allSites F j, 4 * ((v x * X x e.1) ^ 2 +
          (v (x + unitStep j e.1) * X (x + unitStep j e.1) e.2) ^ 2 +
          (v (x + unitStep j e.2) * X (x + unitStep j e.2) e.1) ^ 2 + (v x * X x e.2) ^ 2) := by
          refine Finset.sum_le_sum fun x _ => ?_
          unfold plaquetteCurl
          set p := X x e.1
          set q := X (x + unitStep j e.1) e.2
          set r := X (x + unitStep j e.2) e.1
          set s := X x e.2
          have a0 := h0 x
          have a1 := h1 x e.1
          have a2 := h1 x e.2
          have b : (p + q - r - s) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) := by
            nlinarith [sq_nonneg (p - q), sq_nonneg (p + r), sq_nonneg (p + s), sq_nonneg (q + r),
              sq_nonneg (q + s), sq_nonneg (r - s)]
          calc (u x * (p + q - r - s)) ^ 2 = u x ^ 2 * (p + q - r - s) ^ 2 := by ring
            _ ≤ u x ^ 2 * (4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2)) :=
                mul_le_mul_of_nonneg_left b (sq_nonneg _)
            _ = 4 * (u x ^ 2 * p ^ 2 + u x ^ 2 * q ^ 2 + u x ^ 2 * r ^ 2 + u x ^ 2 * s ^ 2) := by ring
            _ ≤ 4 * (v x ^ 2 * p ^ 2 + v (x + unitStep j e.1) ^ 2 * q ^ 2 +
                v (x + unitStep j e.2) ^ 2 * r ^ 2 + v x ^ 2 * s ^ 2) := by
                have c1 := mul_le_mul_of_nonneg_right a0 (sq_nonneg p)
                have c2 := mul_le_mul_of_nonneg_right a1 (sq_nonneg q)
                have c3 := mul_le_mul_of_nonneg_right a2 (sq_nonneg r)
                have c4 := mul_le_mul_of_nonneg_right a0 (sq_nonneg s)
                linarith
            _ = _ := by ring
      _ = 4 * (∑ x ∈ allSites F j, (v x * X x e.1) ^ 2 +
          ∑ x ∈ allSites F j, (v (x + unitStep j e.1) * X (x + unitStep j e.1) e.2) ^ 2 +
          ∑ x ∈ allSites F j, (v (x + unitStep j e.2) * X (x + unitStep j e.2) e.1) ^ 2 +
          ∑ x ∈ allSites F j, (v x * X x e.2) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ _ := by linarith
  calc _ ≤ ∑ _e ∈ orientedPlanes, 16 * weightedNormSq v X := Finset.sum_le_sum hp
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_orientedPlanes]
        push_cast
        ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
