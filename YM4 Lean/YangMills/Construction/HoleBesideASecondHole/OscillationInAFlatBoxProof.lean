import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGaugeProof
import YangMills.Construction.HoleBesideASecondHole.OscillationInAFlatBox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open LatticeFractionalIntegration
namespace FlatBoxes
abbrev LatticeSite : Type := Lattice4
def cornerBox (c : LatticeSite) (n : Fin 4 → ℕ) : Finset LatticeSite :=
  Fintype.piFinset fun j => Finset.Ico (c j) (c j + n j)
theorem mem_cornerBox {c : LatticeSite} {n : Fin 4 → ℕ} {x : LatticeSite} :
    x ∈ cornerBox c n ↔ ∀ j, c j ≤ x j ∧ x j < c j + n j := by
  simp [cornerBox, Fintype.mem_piFinset]
theorem card_cornerBox (c : LatticeSite) (n : Fin 4 → ℕ) : (cornerBox c n).card = ∏ j, n j := by
  simp [cornerBox, Fintype.card_piFinset]
def axisShift (j : Fin 4) (t : ℤ) : LatticeSite := fun k => if k = j then t else 0
theorem axisShift_apply (j k : Fin 4) (t : ℤ) : axisShift j t k = if k = j then t else 0 := rfl
theorem basisVector_apply (j k : Fin 4) : basisVector j k = if k = j then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
theorem axisShift_add_one (j : Fin 4) (t : ℤ) : axisShift j (t + 1) = axisShift j t + basisVector j := by
  funext k
  by_cases h : k = j <;> simp [axisShift, basisVector_apply, h]
theorem axisShift_zero (j : Fin 4) : axisShift j 0 = 0 := by
  funext k
  simp [axisShift]
theorem sum_cornerBox_translate {M : Type} [AddCommMonoid M] (c v : LatticeSite) (n : Fin 4 → ℕ)
    (g : LatticeSite → M) :
    ∑ x ∈ cornerBox (c + v) n, g x = ∑ u ∈ cornerBox c n, g (u + v) := by
  refine Finset.sum_nbij' (fun x => x - v) (fun u => u + v) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_cornerBox] at hx ⊢
    intro j
    have := hx j
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    omega
  · intro x hx
    rw [mem_cornerBox] at hx ⊢
    intro j
    have := hx j
    simp only [Pi.add_apply] at this ⊢
    omega
  · intro x _
    simp
  · intro x _
    simp
  · intro x _
    simp
theorem cornerBox_double_side (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) :
    cornerBox c (Function.update n j (2 * n j)) = cornerBox c n ∪ cornerBox (c + axisShift j (n j)) n := by
  ext x
  simp only [Finset.mem_union, mem_cornerBox, Pi.add_apply, axisShift_apply]
  constructor
  · intro h
    by_cases hx : x j < c j + n j
    · left
      intro k
      by_cases hk : k = j
      · subst hk
        have := h k
        simp at this
        omega
      · have := h k
        simpa [Function.update_of_ne hk] using this
    · right
      intro k
      by_cases hk : k = j
      · subst hk
        have := h k
        simp at this
        simp
        push_cast at this
        omega
      · have := h k
        simpa [Function.update_of_ne hk, hk] using this
  · rintro (h | h) k
    · by_cases hk : k = j
      · subst hk
        have := h k
        simp
        omega
      · have := h k
        simpa [Function.update_of_ne hk] using this
    · by_cases hk : k = j
      · subst hk
        have := h k
        simp at this
        simp
        omega
      · have := h k
        simpa [Function.update_of_ne hk, hk] using this
theorem disjoint_cornerBox_halves (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) :
    Disjoint (cornerBox c n) (cornerBox (c + axisShift j (n j)) n) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [mem_cornerBox] at h1 h2
  have a := h1 j
  have b := h2 j
  simp only [Pi.add_apply, axisShift_apply, if_true] at b
  omega
theorem sum_cornerBox_double_side {M : Type} [AddCommMonoid M] (c : LatticeSite) (n : Fin 4 → ℕ)
    (j : Fin 4) (g : LatticeSite → M) :
    ∑ x ∈ cornerBox c (Function.update n j (2 * n j)), g x =
      ∑ x ∈ cornerBox c n, g x + ∑ x ∈ cornerBox (c + axisShift j (n j)) n, g x := by
  rw [cornerBox_double_side, Finset.sum_union (disjoint_cornerBox_halves c n j)]
theorem cornerBox_subset_double_left (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) :
    cornerBox c n ⊆ cornerBox c (Function.update n j (2 * n j)) := by
  rw [cornerBox_double_side]
  exact Finset.subset_union_left
theorem cornerBox_subset_double_right (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) :
    cornerBox (c + axisShift j (n j)) n ⊆ cornerBox c (Function.update n j (2 * n j)) := by
  rw [cornerBox_double_side]
  exact Finset.subset_union_right
def sideVolume (n : Fin 4 → ℕ) : ℝ := ∏ j, (n j : ℝ)
theorem sideVolume_double_side (n : Fin 4 → ℕ) (j : Fin 4) :
    sideVolume (Function.update n j (2 * n j)) = 2 * sideVolume n := by
  unfold sideVolume
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => (n k : ℝ)) (Finset.mem_univ j)]
  have : ∏ x ∈ Finset.univ.erase j, ((Function.update n j (2 * n j) x : ℕ) : ℝ) =
      ∏ x ∈ Finset.univ.erase j, (n x : ℝ) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this]
  simp
  ring
theorem card_cornerBox_real (c : LatticeSite) (n : Fin 4 → ℕ) :
    ((cornerBox c n).card : ℝ) = sideVolume n := by
  rw [card_cornerBox]
  simp [sideVolume]
def boxMean (c : LatticeSite) (n : Fin 4 → ℕ) (f : LatticeSite → ℍ[ℝ]) : ℍ[ℝ] :=
  (sideVolume n)⁻¹ • ∑ x ∈ cornerBox c n, f x
theorem boxMean_double_side (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) (f : LatticeSite → ℍ[ℝ])
    (hv : sideVolume n ≠ 0) :
    boxMean c (Function.update n j (2 * n j)) f =
      (1 / 2 : ℝ) • (boxMean c n f + boxMean (c + axisShift j (n j)) n f) := by
  unfold boxMean
  rw [sum_cornerBox_double_side, sideVolume_double_side, ← smul_add, smul_smul, mul_inv]
  congr 1
  ring
theorem sum_pow_four_le {α : Type} (s : Finset α) (g : α → ℝ) :
    (∑ x ∈ s, g x) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ x ∈ s, g x ^ 4 := by apply _root_.YangMills.Construction.PinnedGauge.sum_pow_four_le <;> assumption
def GradientBoundedOn (Q : Finset LatticeSite) (f : LatticeSite → ℍ[ℝ]) (w : LatticeSite → ℝ) : Prop :=
  ∀ x ∈ Q, ∀ j, x + basisVector j ∈ Q → ‖f (x + basisVector j) - f x‖ ≤ w x
theorem GradientBoundedOn.mono {Q Q' : Finset LatticeSite} (h : Q ⊆ Q') {f : LatticeSite → ℍ[ℝ]}
    {w : LatticeSite → ℝ} (hb : GradientBoundedOn Q' f w) :
    GradientBoundedOn Q f w := fun x hx j hxj => hb x (h hx) j (h hxj)
theorem norm_sum_translate_sub_le (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4) (f : LatticeSite → ℍ[ℝ])
    (w : LatticeSite → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hb : GradientBoundedOn (cornerBox c (Function.update n j (2 * n j))) f w) :
    ‖∑ u ∈ cornerBox c n, (f (u + axisShift j (n j)) - f u)‖ ≤
      (n j : ℝ) * ∑ x ∈ cornerBox c (Function.update n j (2 * n j)), w x := by
  have step : ∀ t : ℕ, t ≤ n j → ∀ u ∈ cornerBox c n,
      ‖f (u + axisShift j t) - f u‖ ≤ ∑ s ∈ Finset.range t, w (u + axisShift j s) := by
    intro t
    induction t with
    | zero =>
      intro _ u _
      simp [axisShift_zero]
    | succ t ih =>
      intro ht u hu
      have h1 := ih (by omega) u hu
      have hmem : u + axisShift j t ∈ cornerBox c (Function.update n j (2 * n j)) := by
        rw [mem_cornerBox] at hu ⊢
        intro k
        have := hu k
        by_cases hk : k = j
        · subst hk
          simp [axisShift_apply]
          omega
        · simpa [axisShift_apply, hk, Function.update_of_ne hk] using this
      have hmem2 : u + axisShift j t + basisVector j ∈ cornerBox c (Function.update n j (2 * n j)) := by
        rw [mem_cornerBox] at hu ⊢
        intro k
        have := hu k
        by_cases hk : k = j
        · subst hk
          simp [axisShift_apply, basisVector_apply]
          omega
        · simpa [axisShift_apply, basisVector_apply, hk, Function.update_of_ne hk] using this
      have h2 := hb _ hmem j hmem2
      rw [Finset.sum_range_succ]
      have e : u + axisShift j ((t + 1 : ℕ) : ℤ) = u + axisShift j t + basisVector j := by
        push_cast
        rw [axisShift_add_one, add_assoc]
      rw [e]
      calc ‖f (u + axisShift j t + basisVector j) - f u‖
          = ‖(f (u + axisShift j t + basisVector j) - f (u + axisShift j t)) +
              (f (u + axisShift j t) - f u)‖ := by
            congr 1
            abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := by linarith
  have hsum : ∀ s : ℕ, s < n j →
      ∑ u ∈ cornerBox c n, w (u + axisShift j s) ≤
        ∑ x ∈ cornerBox c (Function.update n j (2 * n j)), w x := by
    intro s hs
    rw [← sum_cornerBox_translate c (axisShift j s) n w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hw x
    intro x hx
    rw [mem_cornerBox] at hx ⊢
    intro k
    have := hx k
    by_cases hk : k = j
    · subst hk
      simp [axisShift_apply] at this ⊢
      omega
    · simpa [axisShift_apply, hk, Function.update_of_ne hk] using this
  calc ‖∑ u ∈ cornerBox c n, (f (u + axisShift j (n j)) - f u)‖
      ≤ ∑ u ∈ cornerBox c n, ‖f (u + axisShift j (n j)) - f u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ cornerBox c n, ∑ s ∈ Finset.range (n j), w (u + axisShift j s) :=
        Finset.sum_le_sum fun u hu => step _ le_rfl u hu
    _ = ∑ s ∈ Finset.range (n j), ∑ u ∈ cornerBox c n, w (u + axisShift j s) := Finset.sum_comm
    _ ≤ ∑ s ∈ Finset.range (n j), ∑ x ∈ cornerBox c (Function.update n j (2 * n j)), w x :=
        Finset.sum_le_sum fun s hs => hsum s (Finset.mem_range.1 hs)
    _ = _ := by simp
theorem norm_boxMean_neighbour_sub_le (c : LatticeSite) (n : Fin 4 → ℕ) (j : Fin 4)
    (f : LatticeSite → ℍ[ℝ]) (w : LatticeSite → ℝ) (E D : ℝ)
    (hv : 0 < sideVolume n) (hE : 0 ≤ E) (hD : 0 ≤ D) (hw : ∀ x, 0 ≤ w x)
    (hb : GradientBoundedOn (cornerBox c (Function.update n j (2 * n j))) f w)
    (hs : ∑ x ∈ cornerBox c (Function.update n j (2 * n j)), w x ^ 4 ≤ E ^ 4)
    (hD4 : 8 * (n j : ℝ) ^ 4 ≤ D ^ 4 * sideVolume n) :
    ‖boxMean (c + axisShift j (n j)) n f - boxMean c n f‖ ≤ D * E := by
  set B' := cornerBox c (Function.update n j (2 * n j)) with hB'
  set S := ∑ x ∈ B', w x with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => hw x
  have hT := norm_sum_translate_sub_le c n j f w hw hb
  have e : boxMean (c + axisShift j (n j)) n f - boxMean c n f =
      (sideVolume n)⁻¹ • ∑ u ∈ cornerBox c n, (f (u + axisShift j (n j)) - f u) := by
    unfold boxMean
    rw [sum_cornerBox_translate, Finset.sum_sub_distrib, smul_sub]
  have hnorm : ‖boxMean (c + axisShift j (n j)) n f - boxMean c n f‖ ≤
      (sideVolume n)⁻¹ * ((n j : ℝ) * S) := by
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hv)]
    exact mul_le_mul_of_nonneg_left hT (inv_pos.2 hv).le
  have h4 : S ^ 4 ≤ (2 * sideVolume n) ^ 3 * E ^ 4 := by
    have := sum_pow_four_le B' w
    rw [hB', card_cornerBox_real, sideVolume_double_side] at this
    calc S ^ 4 ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  refine hnorm.trans ?_
  have hr : 0 ≤ D * E := by positivity
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hr ?_
  have hmain : ((sideVolume n)⁻¹ * ((n j : ℝ) * S)) ^ 4 * sideVolume n =
      (sideVolume n)⁻¹ ^ 3 * ((n j : ℝ) ^ 4 * S ^ 4) := by
    field_simp
  have hv' : sideVolume n ≠ 0 := hv.ne'
  have key : ((sideVolume n)⁻¹ * ((n j : ℝ) * S)) ^ 4 * sideVolume n ≤ (D * E) ^ 4 * sideVolume n := by
    rw [hmain]
    calc (sideVolume n)⁻¹ ^ 3 * ((n j : ℝ) ^ 4 * S ^ 4)
        ≤ (sideVolume n)⁻¹ ^ 3 * ((n j : ℝ) ^ 4 * ((2 * sideVolume n) ^ 3 * E ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 8 * (n j : ℝ) ^ 4 * E ^ 4 := by
          field_simp
          ring
      _ ≤ D ^ 4 * sideVolume n * E ^ 4 := mul_le_mul_of_nonneg_right hD4 (by positivity)
      _ = (D * E) ^ 4 * sideVolume n := by ring
  exact le_of_mul_le_mul_right key hv
def OscillationBound (n : Fin 4 → ℕ) (B : ℝ) : Prop :=
  ∀ (c : LatticeSite) (f : LatticeSite → ℍ[ℝ]) (w : LatticeSite → ℝ) (E : ℝ), 0 ≤ E → (∀ x, 0 ≤ w x) →
    GradientBoundedOn (cornerBox c n) f w →
    ∑ x ∈ cornerBox c n, w x ^ 4 ≤ E ^ 4 → ∀ x ∈ cornerBox c n, ‖f x - boxMean c n f‖ ≤ B * E
theorem OscillationBound.double_side (n : Fin 4 → ℕ) (j : Fin 4) (B D : ℝ) (hv : 0 < sideVolume n)
    (hD : 0 ≤ D) (hD4 : 8 * (n j : ℝ) ^ 4 ≤ D ^ 4 * sideVolume n) (h : OscillationBound n B) :
    OscillationBound (Function.update n j (2 * n j)) (B + D / 2) := by
  intro c f w E hE hw hb hs x hx
  have hwn : ∀ {Q : Finset LatticeSite}, Q ⊆ cornerBox c (Function.update n j (2 * n j)) →
      ∑ x ∈ Q, w x ^ 4 ≤ E ^ 4 := by
    intro Q hQ
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hQ fun x _ _ => ?_) hs
    have := hw x
    positivity
  have hnb := norm_boxMean_neighbour_sub_le c n j f w E D hv hE hD hw hb hs hD4
  have hmean := boxMean_double_side c n j f hv.ne'
  rw [cornerBox_double_side, Finset.mem_union] at hx
  rw [hmean]
  rcases hx with hx | hx
  · have h1 := h c f w E hE hw (GradientBoundedOn.mono (cornerBox_subset_double_left c n j) hb)
      (hwn (cornerBox_subset_double_left c n j)) x hx
    have e : f x - (1 / 2 : ℝ) • (boxMean c n f + boxMean (c + axisShift j (n j)) n f) =
        (f x - boxMean c n f) - (1 / 2 : ℝ) • (boxMean (c + axisShift j (n j)) n f - boxMean c n f) := by
      rw [smul_add, smul_sub]
      have : f x - boxMean c n f = f x - ((1 / 2 : ℝ) • boxMean c n f + (1 / 2 : ℝ) • boxMean c n f) := by
        rw [← add_smul]
        norm_num
      rw [this]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith
  · have h1 := h (c + axisShift j (n j)) f w E hE hw
      (GradientBoundedOn.mono (cornerBox_subset_double_right c n j) hb)
      (hwn (cornerBox_subset_double_right c n j)) x hx
    have e : f x - (1 / 2 : ℝ) • (boxMean c n f + boxMean (c + axisShift j (n j)) n f) =
        (f x - boxMean (c + axisShift j (n j)) n f) +
          (1 / 2 : ℝ) • (boxMean (c + axisShift j (n j)) n f - boxMean c n f) := by
      rw [smul_add, smul_sub]
      have : f x - boxMean (c + axisShift j (n j)) n f =
          f x - ((1 / 2 : ℝ) • boxMean (c + axisShift j (n j)) n f +
            (1 / 2 : ℝ) • boxMean (c + axisShift j (n j)) n f) := by
        rw [← add_smul]
        norm_num
      rw [this]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith
def slabSides (i : Fin 4) (K : ℕ) (S : Finset (Fin 4)) : Fin 4 → ℕ :=
  fun j => if j = i then 1 else if j ∈ S then 2 ^ (K + 1) else 2 ^ K
theorem sideVolume_slabSides_ge (i : Fin 4) (K : ℕ) (S : Finset (Fin 4)) :
    ((2 : ℝ) ^ K) ^ 3 ≤ sideVolume (slabSides i K S) := by
  unfold sideVolume
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have h1 : ((slabSides i K S i : ℕ) : ℝ) = 1 := by simp [slabSides]
  rw [h1, one_mul]
  have h2 : ∏ _x ∈ Finset.univ.erase i, ((2 : ℝ) ^ K) ≤
      ∏ x ∈ Finset.univ.erase i, ((slabSides i K S x : ℕ) : ℝ) := by
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun k hk => ?_
    have hki := Finset.ne_of_mem_erase hk
    simp only [slabSides, hki, if_false]
    by_cases hS : k ∈ S
    · simp only [hS, if_true]
      push_cast
      rw [pow_succ]
      have : (0 : ℝ) < 2 ^ K := by positivity
      nlinarith
    · simp [hS]
  have h3 : (Finset.univ.erase i).card = 3 := by simp
  simpa [h3] using h2
theorem OscillationBound.mono {n : Fin 4 → ℕ} {B B' : ℝ} (hB : B ≤ B') (h : OscillationBound n B) :
    OscillationBound n B' := by
  intro c f w E hE hw hb hs x hx
  exact (h c f w E hE hw hb hs x hx).trans (mul_le_mul_of_nonneg_right hB hE)
theorem oscillationBound_slab_zero (i : Fin 4) : OscillationBound (slabSides i 0 ∅) 0 := by
  intro c f w E _ _ _ _ x hx
  have hone : ∀ j, slabSides i 0 ∅ j = 1 := by
    intro j
    by_cases h : j = i <;> simp [slabSides, h]
  have hbox : cornerBox c (slabSides i 0 ∅) = {c} := by
    ext y
    rw [mem_cornerBox, Finset.mem_singleton]
    constructor
    · intro h
      funext j
      have := h j
      rw [hone j] at this
      push_cast at this
      omega
    · rintro rfl j
      rw [hone j]
      push_cast
      omega
  have hv : sideVolume (slabSides i 0 ∅) = 1 := by
    simp [sideVolume, hone]
  rw [hbox, Finset.mem_singleton] at hx
  subst hx
  simp [boxMean, hbox, hv]
theorem slabSides_insert (i j : Fin 4) (K : ℕ) (S : Finset (Fin 4)) (hj : j ≠ i) (hS : j ∉ S) :
    slabSides i K (insert j S) = Function.update (slabSides i K S) j (2 * slabSides i K S j) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [slabSides, hj, hS, pow_succ, mul_comm]
  · rw [Function.update_of_ne hk]
    simp [slabSides, hk]
theorem oscillationBound_slabSides_add (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 4 = 2) (i : Fin 4) (K : ℕ) (B : ℝ)
    (h : OscillationBound (slabSides i K ∅) B) (S : Finset (Fin 4)) (hS : S ⊆ Finset.univ.erase i) :
    OscillationBound (slabSides i K S) (B + S.card * ρ ^ K) := by
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert j S hjS ih =>
    have hSS : S ⊆ Finset.univ.erase i := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have hji : j ≠ i := Finset.ne_of_mem_erase (hS (Finset.mem_insert_self j S))
    have ih' := ih hSS
    have hv := sideVolume_slabSides_ge i K S
    have hv0 : 0 < sideVolume (slabSides i K S) := lt_of_lt_of_le (by positivity) hv
    have hnj : ((slabSides i K S j : ℕ) : ℝ) = 2 ^ K := by
      simp [slabSides, hji, hjS]
    have hD4 : 8 * ((slabSides i K S j : ℕ) : ℝ) ^ 4 ≤
        (2 * ρ ^ K) ^ 4 * sideVolume (slabSides i K S) := by
      rw [hnj]
      have e : (2 * ρ ^ K) ^ 4 = 16 * (2 : ℝ) ^ K := by
        rw [mul_pow, ← pow_mul, mul_comm K 4, pow_mul, hρ]
        norm_num
      rw [e]
      calc 8 * ((2 : ℝ) ^ K) ^ 4 ≤ 16 * (2 : ℝ) ^ K * ((2 : ℝ) ^ K) ^ 3 := by
            have : 0 ≤ ((2 : ℝ) ^ K) ^ 4 := by positivity
            nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
    have := OscillationBound.double_side (slabSides i K S) j _ (2 * ρ ^ K) hv0 (by positivity) hD4 ih'
    rw [slabSides_insert i j K S hji hjS, Finset.card_insert_of_notMem hjS]
    refine OscillationBound.mono ?_ this
    push_cast
    linarith
theorem slabSides_univ_erase (i : Fin 4) (K : ℕ) :
    slabSides i K (Finset.univ.erase i) = slabSides i (K + 1) ∅ := by
  funext j
  by_cases h : j = i <;> simp [slabSides, h]
theorem oscillationBound_slab (ρ : ℝ) (hρ1 : 1 < ρ) (hρ : ρ ^ 4 = 2) (i : Fin 4) (K : ℕ) :
    OscillationBound (slabSides i K ∅) (3 / (ρ - 1) * ρ ^ K) := by
  have hd : 0 < ρ - 1 := by linarith
  induction K with
  | zero =>
    refine OscillationBound.mono ?_ (oscillationBound_slab_zero i)
    positivity
  | succ K ih =>
    have h := oscillationBound_slabSides_add ρ (by linarith) hρ i K _ ih (Finset.univ.erase i) subset_rfl
    rw [slabSides_univ_erase] at h
    refine OscillationBound.mono ?_ h
    have hc : (((Finset.univ.erase i).card : ℕ) : ℝ) = 3 := by simp
    rw [hc, pow_succ]
    have e : 3 / (ρ - 1) * (ρ ^ K * ρ) - (3 / (ρ - 1) * ρ ^ K + 3 * ρ ^ K) = 0 := by
      field_simp
      ring
    linarith
theorem mem_boxBetween_iff {lo hi x : LatticeSite} :
    x ∈ boxBetween lo hi ↔ ∀ j, lo j ≤ x j ∧ x j ≤ hi j := by
  simp [boxBetween, Fintype.mem_piFinset]
theorem norm_sub_le_of_close_in_boxBetween (i : Fin 4) (K : ℕ) (lo hi : LatticeSite) (f : LatticeSite → ℍ[ℝ])
    (w : LatticeSite → ℝ) (E B : ℝ)
    (hosc : OscillationBound (slabSides i K ∅) B) (hlo : lo i = hi i)
    (hside : ∀ j, j ≠ i → (2 : ℤ) ^ K ≤ hi j - lo j + 1) (hE : 0 ≤ E) (hw : ∀ x, 0 ≤ w x)
    (hb : GradientBoundedOn (boxBetween lo hi) f w) (hs : ∑ x ∈ boxBetween lo hi, w x ^ 4 ≤ E ^ 4)
    (u v : LatticeSite) (hu : u ∈ boxBetween lo hi) (hv : v ∈ boxBetween lo hi)
    (huv : ∀ j, u j - v j ≤ 2 ^ K - 1 ∧ v j - u j ≤ 2 ^ K - 1) :
    ‖f u - f v‖ ≤ 2 * (B * E) := by
  rw [mem_boxBetween_iff] at hu hv
  set c : LatticeSite := fun j => if j = i then lo i else min (min (u j) (v j)) (hi j - 2 ^ K + 1) with hc
  have hside' : ∀ j, slabSides i K ∅ j = if j = i then 1 else 2 ^ K := by
    intro j
    by_cases h : j = i <;> simp [slabSides, h]
  have hsub : cornerBox c (slabSides i K ∅) ⊆ boxBetween lo hi := by
    intro x hx
    rw [mem_cornerBox] at hx
    rw [mem_boxBetween_iff]
    intro j
    have h1 := hx j
    rw [hside'] at h1
    by_cases h : j = i
    · subst h
      simp only [hc, if_true] at h1
      push_cast at h1
      omega
    · simp only [hc, h, if_false] at h1
      push_cast at h1
      have h2 := hside j h
      have h3 := hu j
      have h4 := hv j
      generalize (2 : ℤ) ^ K = s at *
      omega
  have hin : ∀ x, (∀ j, lo j ≤ x j ∧ x j ≤ hi j) → (∀ j, c j ≤ x j ∧ x j < c j + 2 ^ K ∨ j = i) →
      x ∈ cornerBox c (slabSides i K ∅) := by
    intro x h1 h2
    rw [mem_cornerBox]
    intro j
    rw [hside']
    by_cases h : j = i
    · subst h
      have h3 := h1 j
      simp only [hc, if_true]
      push_cast
      omega
    · simp only [h, if_false]
      push_cast
      rcases h2 j with h3 | h3
      · exact h3
      · exact absurd h3 h
  have hu' : u ∈ cornerBox c (slabSides i K ∅) := by
    refine hin u hu fun j => ?_
    by_cases h : j = i
    · exact Or.inr h
    · left
      simp only [hc, h, if_false]
      have h2 := hside j h
      have h3 := hu j
      have h4 := hv j
      have h5 := huv j
      generalize (2 : ℤ) ^ K = s at *
      omega
  have hv' : v ∈ cornerBox c (slabSides i K ∅) := by
    refine hin v hv fun j => ?_
    by_cases h : j = i
    · exact Or.inr h
    · left
      simp only [hc, h, if_false]
      have h2 := hside j h
      have h3 := hu j
      have h4 := hv j
      have h5 := huv j
      generalize (2 : ℤ) ^ K = s at *
      omega
  have hsum : ∑ x ∈ cornerBox c (slabSides i K ∅), w x ^ 4 ≤ E ^ 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => ?_) hs
    have := hw x
    positivity
  have h1 := hosc c f w E hE hw (GradientBoundedOn.mono hsub hb) hsum u hu'
  have h2 := hosc c f w E hE hw (GradientBoundedOn.mono hsub hb) hsum v hv'
  calc ‖f u - f v‖ = ‖(f u - boxMean c (slabSides i K ∅) f) - (f v - boxMean c (slabSides i K ∅) f)‖ := by
        congr 1
        abel
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := by linarith
theorem norm_sub_le_of_chain (lo hi : LatticeSite) (f : LatticeSite → ℍ[ℝ]) (s : ℤ) (hs1 : 1 ≤ s) (D : ℝ)
    (hD : 0 ≤ D)
    (hl : ∀ u ∈ boxBetween lo hi, ∀ v ∈ boxBetween lo hi, (∀ j, u j - v j ≤ s ∧ v j - u j ≤ s) →
      ‖f u - f v‖ ≤ D) (t : ℕ) :
    ∀ x ∈ boxBetween lo hi, ∀ y ∈ boxBetween lo hi, (∀ j, x j - y j ≤ t * s ∧ y j - x j ≤ t * s) →
      ‖f x - f y‖ ≤ t * D := by
  induction t with
  | zero =>
    intro x _ y _ h
    have : x = y := by
      funext j
      have := h j
      simp at this
      omega
    subst this
    simp
  | succ t ih =>
    intro x hx y hy h
    set z : LatticeSite := fun j => max (x j - s) (min (x j + s) (y j)) with hz
    have hx' := mem_boxBetween_iff.1 hx
    have hy' := mem_boxBetween_iff.1 hy
    have hzj : ∀ j, (lo j ≤ z j ∧ z j ≤ hi j) ∧ (x j - z j ≤ s ∧ z j - x j ≤ s) ∧
        (z j - y j ≤ t * s ∧ y j - z j ≤ t * s) := by
      intro j
      have h1 := h j
      have h2 := hx' j
      have h3 := hy' j
      have e : ((t + 1 : ℕ) : ℤ) * s = (t : ℤ) * s + s := by
        push_cast
        ring
      rw [e] at h1
      have ht : 0 ≤ (t : ℤ) * s := by positivity
      simp only [hz]
      generalize (t : ℤ) * s = T at *
      omega
    have hzm : z ∈ boxBetween lo hi := mem_boxBetween_iff.2 fun j => (hzj j).1
    have h1 := hl x hx z hzm fun j => (hzj j).2.1
    have h2 := ih z hzm y hy fun j => (hzj j).2.2
    calc ‖f x - f y‖ = ‖(f x - f z) + (f z - f y)‖ := by
          congr 1
          abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by
          push_cast
          linarith
theorem flatBoxOscillation : flatBoxOscillationStatement := by
  obtain ⟨ρ, hρ1, hρ⟩ : ∃ ρ : ℝ, 1 < ρ ∧ ρ ^ 4 = 2 := by
    refine ⟨Real.sqrt (Real.sqrt 2), ?_, ?_⟩
    · rw [Real.lt_sqrt (by norm_num), Real.lt_sqrt (by norm_num)]
      norm_num
    · have h1 : Real.sqrt (Real.sqrt 2) ^ 2 = Real.sqrt 2 := Real.sq_sqrt (Real.sqrt_nonneg 2)
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc Real.sqrt (Real.sqrt 2) ^ 4 = (Real.sqrt (Real.sqrt 2) ^ 2) ^ 2 := by ring
        _ = 2 := by rw [h1, h2]
  set A : ℝ := 3 / (ρ - 1) with hA
  refine ⟨(64 * A) ^ 4, by positivity, ?_⟩
  intro i n lo hi f w E hn hlo hside hE hw hb hs x hx y hy
  set K := Nat.log 2 n with hK
  have hK1 : 2 ^ K ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hK2 : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hKpos : 1 ≤ K := by
    rw [hK]
    exact Nat.log_pos (by norm_num) hn
  have hs2 : (2 : ℤ) ≤ 2 ^ K := by
    have : (2 : ℕ) ≤ 2 ^ K := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hKpos
    exact_mod_cast this
  have hK1' : (2 : ℤ) ^ K ≤ n := by exact_mod_cast hK1
  have hK2' : (n : ℤ) < 2 * 2 ^ K := by
    have : n < 2 * 2 ^ K := by
      rw [pow_succ] at hK2
      omega
    exact_mod_cast this
  have hosc := oscillationBound_slab ρ hρ1 hρ i K
  set D : ℝ := 2 * (A * ρ ^ K * E) with hD
  have hD0 : 0 ≤ D := by positivity
  have hlink : ∀ u ∈ boxBetween lo hi, ∀ v ∈ boxBetween lo hi,
      (∀ j, u j - v j ≤ 2 ^ K - 1 ∧ v j - u j ≤ 2 ^ K - 1) → ‖f u - f v‖ ≤ D := by
    intro u hu v hv huv
    exact norm_sub_le_of_close_in_boxBetween i K lo hi f w E _ hosc hlo
      (fun j hj => by have := (hside j hj).1; omega) hE hw hb hs u v hu hv huv
  have hch := norm_sub_le_of_chain lo hi f (2 ^ K - 1) (by omega) D hD0 hlink 32 x hx y hy (by
    intro j
    have h1 := (mem_boxBetween_iff.1 hx) j
    have h2 := (mem_boxBetween_iff.1 hy) j
    by_cases hj : j = i
    · subst hj
      push_cast
      constructor <;> omega
    · have h3 := hside j hj
      push_cast
      generalize (2 : ℤ) ^ K = s at *
      constructor <;> omega)
  have hnorm : ‖f x - f y‖ ^ 4 ≤ (((32 : ℕ) : ℝ) * D) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hch 4
  refine hnorm.trans ?_
  have e : (((32 : ℕ) : ℝ) * D) ^ 4 = (64 * A) ^ 4 * (ρ ^ 4) ^ K * E ^ 4 := by
    rw [hD, ← pow_mul, mul_comm 4 K, pow_mul]
    push_cast
    ring
  rw [e, hρ]
  have h2n : (2 : ℝ) ^ K ≤ n := by exact_mod_cast hK1
  have : 0 ≤ (64 * A) ^ 4 := by positivity
  have hE4 : 0 ≤ E ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2n this) hE4
end FlatBoxes
end YangMills.Construction
end
