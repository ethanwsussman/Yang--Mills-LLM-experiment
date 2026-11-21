import YangMills.Construction.ColdStepAtMirrorFrames.NormsOfTheShiftOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def energyBelowTop (a : ℝ) (X : FormChain F) : ℝ :=
  (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (X 0) x e.1 e.2 ^ 2) +
    a * ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit X j y i ^ 2
def polarBelowTop (a : ℝ) (X Y : FormChain F) : ℝ :=
  (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (X 0) x e.1 e.2 * plaquetteCurl (Y 0) x e.1 e.2) +
    a * ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit X j y i * chainMisfit Y j y i
theorem plaquetteCurl_add {j : ℕ} (B D : LevelForm F j) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl (B + D) x k l = plaquetteCurl B x k l + plaquetteCurl D x k l := by
  simp only [plaquetteCurl, Pi.add_apply]
  ring
theorem chainMisfit_add (X Y : FormChain F) (j : ℕ) :
    chainMisfit (fun j => X j + Y j) j = chainMisfit X j + chainMisfit Y j := by
  funext y i
  simp only [chainMisfit, lineAverage_add, Pi.add_apply]
  ring
theorem energyBelowTop_add (a : ℝ) (X Y : FormChain F) :
    energyBelowTop a (fun j => X j + Y j) = energyBelowTop a X + 2 * polarBelowTop a X Y + energyBelowTop a Y := by
  unfold energyBelowTop polarBelowTop
  simp only [chainMisfit_add, Pi.add_apply, plaquetteCurl_add]
  have hsq : ∀ (p q : F.Site 0 → Fin 4 × Fin 4 → ℝ),
      ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, (p x e + q x e) ^ 2 =
      (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, p x e ^ 2) + 2 * (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, p x e * q x e) +
        ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, q x e ^ 2 := by
    intro p q
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hmis : ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, (chainMisfit X j y i + chainMisfit Y j y i) ^ 2 =
      (∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit X j y i ^ 2) +
      2 * (∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit X j y i * chainMisfit Y j y i) +
      ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit Y j y i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsq (fun x e => plaquetteCurl (X 0) x e.1 e.2) (fun x e => plaquetteCurl (Y 0) x e.1 e.2), hmis]
  ring
theorem IsFlatChain.polarBelowTop_add_eq_zero {a : ℝ} {c : F.Site F.top × Fin 4} {B : FormChain F}
    (hB : IsFlatChain a c B) (C : FormChain F) :
    polarBelowTop a B C + a * ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * lineAverage (C F.depth) y i = 0 := by
  set D : FormChain F := fun j => if j = F.top then 0 else C j with hD
  have hDtop : D F.top = 0 := if_pos rfl
  have hD0 : D 0 = C 0 := if_neg (by unfold BlockFrame.top; omega)
  have h := hB.stationary D hDtop
  unfold chainEnergyPolar at h
  rw [hD0] at h
  have hlow : ∀ j ∈ Finset.range F.depth, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      chainMisfit B j y i * chainMisfit D j y i =
      ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit B j y i * chainMisfit C j y i := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h1 : D j = C j := if_neg (by unfold BlockFrame.top; omega)
    have h2 : D (j + 1) = C (j + 1) := if_neg (by unfold BlockFrame.top; omega)
    unfold chainMisfit
    rw [h1, h2]
  have hhigh : ∑ y ∈ sitesOfCells (finiteCells F) (F.depth + 1), ∑ i : Fin 4, chainMisfit B F.depth y i * chainMisfit D F.depth y i =
      ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * lineAverage (C F.depth) y i := by
    have h1 : D F.depth = C F.depth := if_neg (by unfold BlockFrame.top; omega)
    have h2 : D (F.depth + 1) = 0 := if_pos rfl
    unfold chainMisfit
    rw [h1, h2]
    simp
  have hsplit : ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      chainMisfit B j y i * chainMisfit D j y i =
      (∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit B j y i * chainMisfit C j y i) +
      ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * lineAverage (C F.depth) y i := by
    show ∑ j ∈ Finset.range (F.depth + 1), _ = _
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hlow, hhigh]
  rw [hsplit] at h
  unfold polarBelowTop
  linarith
theorem sum_sq_cutoff_mix_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) {l : ℕ}
    (hl : l ≤ F.depth) (c : Fin 4 → ℝ) (i : Fin 4) (m : ℕ) (hm : m ≤ F.blockSide) (G : F.Site l → ℝ) :
    ∑ x ∈ allSites F l, ((1 - cutoff c l x) * G x + cutoff c l x * G (x + axisOffset l i (shiftLength F m l))) ^ 2 ≤
      ∑ x ∈ allSites F l, G x ^ 2 +
        (m : ℝ) / (2 * F.blockSide) * ∑ x ∈ allSites F l, (ballIndicator c 5 l x * G x) ^ 2 := by
  have hlt : l ≤ F.top := by
    unfold BlockFrame.top
    omega
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  set s := axisOffset l i (shiftLength F m l) with hs'
  have hpt : ∀ x, ((1 - cutoff c l x) * G x + cutoff c l x * G (x + s)) ^ 2 ≤
      G x ^ 2 + cutoff c l x * G (x + s) ^ 2 - cutoff c l x * G x ^ 2 := by
    intro x
    have a0 := cutoff_nonneg c x
    have a1 := cutoff_le_one c x
    set t := cutoff c l x
    nlinarith [mul_nonneg (mul_nonneg a0 (by linarith : (0 : ℝ) ≤ 1 - t)) (sq_nonneg (G x - G (x + s)))]
  have hshift : ∑ x ∈ allSites F l, cutoff c l x * G (x + s) ^ 2 =
      ∑ x ∈ allSites F l, cutoff c l (x - s) * G x ^ 2 := by
    have := sum_allSites_add_right hL hs hlt s (fun x => cutoff c l (x - s) * G x ^ 2)
    simp only [add_sub_cancel_right] at this
    exact this
  have hdiff : ∀ x, (cutoff c l (x - s) - cutoff c l x) * G x ^ 2 ≤
      (m : ℝ) / (2 * F.blockSide) * (ballIndicator c 5 l x * G x) ^ 2 := by
    intro x
    have hd : |distFromPoint c x - distFromPoint c (x - s)| ≤ (m : ℝ) / F.blockSide := by
      have := abs_distFromPoint_shiftLength_sub_le hL hs hl (x - s) i m c
      simpa [hs'] using this
    have hm1 : (m : ℝ) / F.blockSide ≤ 1 := by
      rw [div_le_one hLpos]
      exact_mod_cast hm
    by_cases hx : distFromPoint c x ≤ 5
    · have e : ballIndicator c 5 l x = 1 := by
        unfold ballIndicator
        rw [if_pos hx]
      rw [e, one_mul]
      have hc := abs_cutoff_sub_le c x (x - s)
      have : cutoff c l (x - s) - cutoff c l x ≤ (m : ℝ) / (2 * F.blockSide) := by
        have h5 := (le_abs_self _).trans hc
        rw [abs_sub_comm] at h5
        have e2 : (m : ℝ) / (2 * F.blockSide) = 1 / 2 * ((m : ℝ) / F.blockSide) := by
          field_simp
        rw [e2]
        nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    · push Not at hx
      have c1 : cutoff c l x = 0 := cutoff_eq_zero c x (by linarith)
      have c2 : cutoff c l (x - s) = 0 := cutoff_eq_zero c _ (by
        have := (abs_le.1 hd).2
        linarith)
      rw [c1, c2]
      simp only [sub_self, zero_mul]
      positivity
  calc _ ≤ ∑ x ∈ allSites F l, (G x ^ 2 + cutoff c l x * G (x + s) ^ 2 - cutoff c l x * G x ^ 2) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ allSites F l, G x ^ 2 + ∑ x ∈ allSites F l, (cutoff c l (x - s) - cutoff c l x) * G x ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift]
        have e : ∑ x ∈ allSites F l, (cutoff c l (x - s) - cutoff c l x) * G x ^ 2 =
            ∑ x ∈ allSites F l, cutoff c l (x - s) * G x ^ 2 - ∑ x ∈ allSites F l, cutoff c l x * G x ^ 2 := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
        rw [e]
        ring
    _ ≤ _ := by
        refine add_le_add_right ?_ _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun x _ => hdiff x
theorem weightedCurlNormSq_iteratedLineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {U : (j : ℕ) → F.Site j → ℝ} (hU : IsReadMonotone U) (X : LevelForm F 0) {j : ℕ} (hj : j ≤ F.top) :
    weightedCurlNormSq (U j) (iteratedLineAverage X j) ≤ weightedCurlNormSq (U 0) X := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have h1 := weightedCurlNormSq_lineAverage_le hL hs hj (U (j + 1)) (U j) 1 zero_le_one (iteratedLineAverage X j)
      (fun k l y h hh m hm m' hm' => by
        rw [one_mul]
        exact hU j hj y k l h hh m hm m' hm')
    rw [one_mul] at h1
    exact h1.trans (ih (by omega))
theorem weightedCurlNormSq_one_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (X : LevelForm F j) :
    weightedCurlNormSq (fun _ => (1 : ℝ)) X ≤ 96 * weightedNormSq (fun _ => (1 : ℝ)) X := by
  rw [weightedCurlNormSq_eq_sum_orientedPlanes]
  have hp : ∀ e ∈ orientedPlanes, ∑ x ∈ allSites F j, (1 * plaquetteCurl X x e.1 e.2) ^ 2 ≤
      16 * weightedNormSq (fun _ => (1 : ℝ)) X := by
    intro e _
    set W := weightedNormSq (fun _ => (1 : ℝ)) X with hW
    have t : ∀ (u : F.Site j) (k : Fin 4), ∑ x ∈ allSites F j, X (x + u) k ^ 2 ≤ W := by
      intro u k
      have := sum_allSites_add_right hL hs hj u (fun x => X x k ^ 2)
      rw [this]
      have := sum_sq_component_le_weightedNormSq (fun _ => (1 : ℝ)) X k
      simpa using this
    have t0 : ∑ x ∈ allSites F j, X x e.1 ^ 2 ≤ W := by
      have := t 0 e.1
      simpa using this
    have t1 : ∑ x ∈ allSites F j, X x e.2 ^ 2 ≤ W := by
      have := t 0 e.2
      simpa using this
    have t2 := t (unitStep j e.1) e.2
    have t3 := t (unitStep j e.2) e.1
    calc _ ≤ ∑ x ∈ allSites F j, 4 * (X x e.1 ^ 2 + X (x + unitStep j e.1) e.2 ^ 2 +
          X (x + unitStep j e.2) e.1 ^ 2 + X x e.2 ^ 2) := by
          refine Finset.sum_le_sum fun x _ => ?_
          unfold plaquetteCurl
          set p := X x e.1
          set q := X (x + unitStep j e.1) e.2
          set r := X (x + unitStep j e.2) e.1
          set u := X x e.2
          nlinarith [sq_nonneg (p - q), sq_nonneg (p + r), sq_nonneg (p + u), sq_nonneg (q + r),
            sq_nonneg (q + u), sq_nonneg (r - u)]
      _ = 4 * (∑ x ∈ allSites F j, X x e.1 ^ 2 + ∑ x ∈ allSites F j, X (x + unitStep j e.1) e.2 ^ 2 +
          ∑ x ∈ allSites F j, X (x + unitStep j e.2) e.1 ^ 2 + ∑ x ∈ allSites F j, X x e.2 ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ _ := by linarith
  calc _ ≤ ∑ _e ∈ orientedPlanes, 16 * weightedNormSq (fun _ => (1 : ℝ)) X := Finset.sum_le_sum hp
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_orientedPlanes]
        push_cast
        ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
