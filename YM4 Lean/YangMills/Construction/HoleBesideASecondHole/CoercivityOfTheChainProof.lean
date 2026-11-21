import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvatureProof
import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours SquareDescent BondContours GroupMeans
namespace CoercivityProof
variable {F : BlockFrame}
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem pow_mul_cast_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) {a b : ℤ}
    (h : (a : ZMod (F.period j k)) = b) :
    (((F.blockSide : ℤ) ^ (j - i) * a : ℤ) : ZMod (F.period i k)) =
      (((F.blockSide : ℤ) ^ (j - i) * b : ℤ) : ZMod (F.period i k)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.pow_mul_cast_eq <;> assumption
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_smul_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • (Pi.single i 1 : Fin 4 → ℤ)) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem siteOfCoords_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (c h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (j - i))) :
    siteOfCoords i (fun k => (F.blockSide : ℤ) ^ (j - i) * c k + h k) ∈
      sitesBelow i (siteOfCoords (F := F) j c) := by
  refine Finset.mem_image.2 ⟨h, hh, ?_⟩
  funext k
  simp only [siteOfCoords]
  have h1 : ((siteCoords (siteOfCoords (F := F) j c) k : ℤ) : ZMod (F.period j k)) =
      (c k : ZMod (F.period j k)) := by
    rw [siteCoords_cast]
    rfl
  have h2 := pow_mul_cast_eq hij hj k h1
  push_cast at h2 ⊢
  rw [h2]
theorem odd_blockSide_pow (hL : Odd F.blockSide) (e : ℕ) : Odd (F.blockSide ^ e) := hL.pow
theorem sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top)
    (hL : Odd F.blockSide) (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i}
    (hz : z ∈ sitesBelow i w) : z ∈ sitesBelow i x := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.sitesBelow_trans <;> assumption
theorem self_mem_sitesBelow {j : ℕ} (hL : Odd F.blockSide) (x : F.Site j) : x ∈ sitesBelow j x := by
  refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have e : (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) =
        siteCoords x := by
      funext k
      simp
    show siteOfCoords j (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = x
    rw [e]
    exact siteOfCoords_siteCoords x
theorem rectangle_mem_sitesBelow_corner {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top)
    (hL : Odd F.blockSide) (y : F.Site j) (μ ν : Fin 4) (hne : μ ≠ ν) {x : F.Site i}
    (hx : x ∈ sitesBelow i y) (r1 r2 : ℕ) (h1 : r1 ≤ F.blockSide ^ (j - i))
    (h2 : r2 ≤ F.blockSide ^ (j - i)) :
    ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧
      x + r1 • unitStep i μ + r2 • unitStep i ν ∈
        sitesBelow i (y + a • unitStep j μ + b • unitStep j ν) := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  have hh1 := mem_centredCube_iff.1 hh
  set n := F.blockSide ^ (j - i) with hn
  obtain ⟨q, hq⟩ := odd_blockSide_pow hL (j - i)
  rw [← hn] at hq
  have hhalf : ((n : ℤ) - 1) / 2 = q := by
    rw [hq]
    push_cast
    omega
  rw [hhalf] at hh1
  have hc : ∀ (k : Fin 4) (r : ℕ), r ≤ n → ∃ a : ℕ, a ≤ 1 ∧ |h k + (r : ℤ) - (a : ℤ) * n| ≤ q := by
    intro k r hr
    have hk := abs_le.1 (hh1 k)
    by_cases hcase : h k + r ≤ q
    · refine ⟨0, by omega, ?_⟩
      rw [abs_le]
      push_cast
      constructor <;> omega
    · refine ⟨1, le_rfl, ?_⟩
      rw [abs_le]
      push_cast
      constructor <;> omega
  obtain ⟨a, ha, ha'⟩ := hc μ r1 h1
  obtain ⟨b, hb, hb'⟩ := hc ν r2 h2
  refine ⟨a, b, ha, hb, ?_⟩
  set c' : Fin 4 → ℤ := siteCoords y + (a : ℤ) • (Pi.single μ 1 : Fin 4 → ℤ) +
    (b : ℤ) • (Pi.single ν 1 : Fin 4 → ℤ) with hc'
  set h' : Fin 4 → ℤ := h + ((r1 : ℤ) - a * n) • (Pi.single μ 1 : Fin 4 → ℤ) +
    ((r2 : ℤ) - b * n) • (Pi.single ν 1 : Fin 4 → ℤ) with hh'
  have hmem : h' ∈ centredCube n := by
    refine mem_centredCube_iff.2 fun k => ?_
    rw [hhalf]
    by_cases e1 : k = μ
    · subst e1
      have : h' k = h k + (r1 : ℤ) - a * n := by
        simp [hh', Pi.single_apply, hne]
        ring
      rw [this]
      exact ha'
    · by_cases e2 : k = ν
      · subst e2
        have : h' k = h k + (r2 : ℤ) - b * n := by
          simp [hh', Pi.single_apply, e1]
          ring
        rw [this]
        exact hb'
      · have : h' k = h k := by
          simp [hh', Pi.single_apply, e1, e2]
        rw [this]
        exact hh1 k
  have hu := siteOfCoords_mem_sitesBelow hij hj c' h' hmem
  have e1 : siteOfCoords (F := F) j c' = y + a • unitStep j μ + b • unitStep j ν := by
    rw [hc', siteOfCoords_add, siteOfCoords_add, siteOfCoords_smul_single, siteOfCoords_smul_single,
      siteOfCoords_siteCoords, natCast_zsmul, natCast_zsmul]
  rw [e1] at hu
  convert hu using 1
  have e2 : (fun k => (F.blockSide : ℤ) ^ (j - i) * c' k + h' k) =
      (fun k => (F.blockSide : ℤ) ^ (j - i) * siteCoords y k + h k) +
        (r1 : ℤ) • (Pi.single μ 1 : Fin 4 → ℤ) + (r2 : ℤ) • (Pi.single ν 1 : Fin 4 → ℤ) := by
    funext k
    have hnn : (F.blockSide : ℤ) ^ (j - i) = n := by rw [hn]; push_cast; rfl
    simp only [hc', hh', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hnn]
    ring
  rw [e2, siteOfCoords_add, siteOfCoords_add, siteOfCoords_smul_single, siteOfCoords_smul_single,
    natCast_zsmul, natCast_zsmul]
theorem rectangle_mem_cutBelow {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top)
    (hL : Odd F.blockSide) (X : Finset (F.Site m)) (p : F.Site j × Fin 4 × Fin 4)
    (hp : p ∈ cutPlaquettes (cutBelow j X)) {x : F.Site i} (hx : x ∈ sitesBelow i p.1) (r1 r2 : ℕ)
    (h1 : r1 ≤ F.blockSide ^ (j - i)) (h2 : r2 ≤ F.blockSide ^ (j - i)) :
    x + r1 • unitStep i p.2.1 + r2 • unitStep i p.2.2 ∈ cutBelow i X := by
  simp only [cutPlaquettes, Finset.mem_filter] at hp
  obtain ⟨-, hlt, hc⟩ := hp
  obtain ⟨a, b, ha, hb, hu⟩ :=
    rectangle_mem_sitesBelow_corner hij (hjm.trans hm) hL p.1 p.2.1 p.2.2 hlt.ne hx r1 r2 h1 h2
  have hcorner : p.1 + a • unitStep j p.2.1 + b • unitStep j p.2.2 ∈ plaquetteCorners p := by
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton]
    interval_cases a <;> interval_cases b <;> simp
  have hin := hc hcorner
  simp only [cutBelow, Finset.mem_biUnion] at hin ⊢
  obtain ⟨x0, hx0, hw⟩ := hin
  exact ⟨x0, hx0, sitesBelow_trans hij hjm hm hL x0 hw hu⟩
theorem refineSite_add_injective {i : ℕ} (hi : i < F.top) (hL : Odd F.blockSide)
    {x x' : F.Site (i + 1)} {h h' : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide)
    (hh' : h' ∈ centredCube F.blockSide)
    (e : refineSite x + siteOfCoords i h = refineSite x' + siteOfCoords i h') :
    x = x' ∧ h = h' := by apply _root_.YangMills.Construction.BlockLines.refineSite_add_injective <;> assumption
def ellTwo {A : Type} (Y : Finset A) (f : A → ℝ) : ℝ := Real.sqrt (∑ x ∈ Y, f x ^ 2)
theorem ellTwo_nonneg {A : Type} (Y : Finset A) (f : A → ℝ) : 0 ≤ ellTwo Y f := Real.sqrt_nonneg _
theorem ellTwo_sq {A : Type} (Y : Finset A) (f : A → ℝ) : ellTwo Y f ^ 2 = ∑ x ∈ Y, f x ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem ellTwo_le {A : Type} (Y : Finset A) (f : A → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∑ x ∈ Y, f x ^ 2 ≤ R ^ 2) : ellTwo Y f ≤ R := Real.sqrt_le_iff.2 ⟨hR, h⟩
theorem ellTwo_add {A : Type} (Y : Finset A) (f g : A → ℝ) :
    ellTwo Y (fun x => f x + g x) ≤ ellTwo Y f + ellTwo Y g := by
  refine ellTwo_le Y _ (add_nonneg (ellTwo_nonneg _ _) (ellTwo_nonneg _ _)) ?_
  have h1 : ∑ x ∈ Y, f x * g x ≤ ellTwo Y f * ellTwo Y g := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Y f g
    have hc' : (∑ x ∈ Y, f x * g x) ^ 2 ≤ (ellTwo Y f * ellTwo Y g) ^ 2 := by
      rw [mul_pow, ellTwo_sq, ellTwo_sq]
      exact hc
    exact (abs_le_of_sq_le_sq' hc' (mul_nonneg (ellTwo_nonneg _ _) (ellTwo_nonneg _ _))).2
  have e : ∑ x ∈ Y, (f x + g x) ^ 2 =
      ∑ x ∈ Y, f x ^ 2 + 2 * ∑ x ∈ Y, f x * g x + ∑ x ∈ Y, g x ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e, ← ellTwo_sq, ← ellTwo_sq]
  nlinarith
theorem ellTwo_mono {A : Type} (Y : Finset A) {f g : A → ℝ} (h0 : ∀ x ∈ Y, 0 ≤ f x)
    (h : ∀ x ∈ Y, f x ≤ g x) : ellTwo Y f ≤ ellTwo Y g := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun x hx => ?_)
  exact pow_le_pow_left₀ (h0 x hx) (h x hx) 2
theorem ellTwo_const_mul {A : Type} (Y : Finset A) (f : A → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ellTwo Y (fun x => c * f x) = c * ellTwo Y f := by
  unfold ellTwo
  have e : ∑ x ∈ Y, (c * f x) ^ 2 = c ^ 2 * ∑ x ∈ Y, f x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
def sideOffset (l n : ℕ) (μ ν : Fin 4) (s : Fin 4) (r : ℕ) : F.Site l :=
  ![r • unitStep l μ, n • unitStep l μ + r • unitStep l ν,
    n • unitStep l μ + n • unitStep l ν - (r + 1) • unitStep l μ,
    n • unitStep l ν - (r + 1) • unitStep l ν] s
def sideDirection (μ ν : Fin 4) (s : Fin 4) : Fin 4 := ![μ, ν, μ, ν] s
theorem sumAroundSquare_eq_sum_sides {l : ℕ} (f : F.Site l × Fin 4 → ℝ) (x : F.Site l) (n : ℕ)
    (μ ν : Fin 4) :
    sumAroundSquare f x n μ ν = ∑ q ∈ Finset.range n ×ˢ (Finset.univ : Finset (Fin 4)),
      f (x + sideOffset l n μ ν q.2 q.1, sideDirection μ ν q.2) := by
  unfold sumAroundSquare
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.sum_univ_four]
  simp only [sideOffset, sideDirection, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [add_assoc, add_sub_assoc]
theorem card_sideIndex (n : ℕ) :
    ((Finset.range n ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) = 4 * n := by
  simp
  ring
theorem sum_translate_le {l : ℕ} (Y : Finset (F.Site l)) (C : Finset (F.Site l × Fin 4))
    (G : F.Site l × Fin 4 → ℝ) (hG : ∀ c, 0 ≤ G c) (o : F.Site l) (d : Fin 4)
    (hC : ∀ x ∈ Y, (x + o, d) ∈ C) : ∑ x ∈ Y, G (x + o, d) ≤ ∑ c ∈ C, G c := by
  classical
  have hinj : Set.InjOn (fun x : F.Site l => (x + o, d)) Y := by
    intro x _ x' _ h
    exact add_right_cancel (congrArg Prod.fst h)
  have := Finset.sum_image (f := G) hinj
  rw [← this]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hG c
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  exact hC x hx
theorem sum_sq_sumAroundSquare_le {l : ℕ} (Y : Finset (F.Site l)) (C : Finset (F.Site l × Fin 4))
    (f : F.Site l × Fin 4 → ℝ) (n : ℕ) (μ ν : Fin 4)
    (hC : ∀ x ∈ Y, ∀ r < n, ∀ s, (x + sideOffset l n μ ν s r, sideDirection μ ν s) ∈ C) :
    ∑ x ∈ Y, sumAroundSquare f x n μ ν ^ 2 ≤ (4 * n : ℝ) ^ 2 * ∑ c ∈ C, f c ^ 2 := by
  have h1 : ∀ x ∈ Y, sumAroundSquare f x n μ ν ^ 2 ≤ (4 * n : ℝ) *
      ∑ q ∈ Finset.range n ×ˢ (Finset.univ : Finset (Fin 4)),
        f (x + sideOffset l n μ ν q.2 q.1, sideDirection μ ν q.2) ^ 2 := by
    intro x _
    rw [sumAroundSquare_eq_sum_sides, ← card_sideIndex]
    exact sq_sum_le_card_mul_sum_sq
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ q ∈ Finset.range n ×ˢ (Finset.univ : Finset (Fin 4)),
      ∑ x ∈ Y, f (x + sideOffset l n μ ν q.2 q.1, sideDirection μ ν q.2) ^ 2 ≤ ∑ c ∈ C, f c ^ 2 := by
    intro q hq
    exact sum_translate_le Y C (fun c => f c ^ 2) (fun c => sq_nonneg _) _ _
      fun x hx => hC x hx q.1 (Finset.mem_range.1 (Finset.mem_product.1 hq).1) q.2
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_const, nsmul_eq_mul, card_sideIndex] at h3
  calc (4 * n : ℝ) * _ ≤ (4 * n : ℝ) * ((4 * n : ℝ) * ∑ c ∈ C, f c ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring
theorem sum_sumAroundSquare_le {l : ℕ} (Y : Finset (F.Site l)) (C : Finset (F.Site l × Fin 4))
    (f : F.Site l × Fin 4 → ℝ) (hf : ∀ c, 0 ≤ f c) (n : ℕ) (μ ν : Fin 4)
    (hC : ∀ x ∈ Y, ∀ r < n, ∀ s, (x + sideOffset l n μ ν s r, sideDirection μ ν s) ∈ C) :
    ∑ x ∈ Y, sumAroundSquare f x n μ ν ≤ (4 * n : ℝ) * ∑ c ∈ C, f c := by
  simp only [sumAroundSquare_eq_sum_sides]
  rw [Finset.sum_comm]
  have h2 : ∀ q ∈ Finset.range n ×ˢ (Finset.univ : Finset (Fin 4)),
      ∑ x ∈ Y, f (x + sideOffset l n μ ν q.2 q.1, sideDirection μ ν q.2) ≤ ∑ c ∈ C, f c := by
    intro q hq
    exact sum_translate_le Y C f hf _ _
      fun x hx => hC x hx q.1 (Finset.mem_range.1 (Finset.mem_product.1 hq).1) q.2
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_const, nsmul_eq_mul, card_sideIndex] at h3
  exact h3
theorem unitStep_apply_self (j : ℕ) (i : Fin 4) : (unitStep j i : F.Site j) i = 1 := by
  simp [unitStep, siteOfCoords]
theorem natCast_injective_of_lt {p r r' : ℕ} (h : (r : ZMod p) = r') (hp : p = 0 ∨ (r < p ∧ r' < p)) :
    r = r' := by apply _root_.YangMills.Construction.BondContours.natCast_zmod_injective_of_lt <;> assumption
theorem nsmul_unitStep_injective {l n r r' : ℕ} (i : Fin 4) (hp : F.period l i = 0 ∨ n ≤ F.period l i)
    (hr : r < n) (hr' : r' < n) (h : r • (unitStep l i : F.Site l) = r' • unitStep l i) : r = r' := by
  have c := congrFun h i
  simp only [Pi.smul_apply, unitStep_apply_self, nsmul_eq_mul, mul_one] at c
  refine natCast_injective_of_lt c ?_
  rcases hp with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ⟨by omega, by omega⟩
theorem sideOffset_injOn {l : ℕ} (n : ℕ) (μ ν : Fin 4) (hp : ∀ k, F.period l k = 0 ∨ n ≤ F.period l k)
    (s : Fin 4) :
    Set.InjOn (fun r => (sideOffset l n μ ν s r : F.Site l)) (Finset.range n : Finset ℕ) := by
  intro r hr r' hr' h
  have hr1 : r < n := by simpa using hr
  have hr2 : r' < n := by simpa using hr'
  simp only at h
  fin_cases s
  · simp only [sideOffset, Fin.zero_eta, Matrix.cons_val_zero] at h
    exact nsmul_unitStep_injective μ (hp μ) hr1 hr2 h
  · simp only [sideOffset, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h
    exact nsmul_unitStep_injective ν (hp ν) hr1 hr2 (add_left_cancel h)
  · have h2 : (r + 1) • (unitStep l μ : F.Site l) = (r' + 1) • unitStep l μ := by
      have := h
      simp only [sideOffset, Matrix.cons_val] at this
      exact sub_right_injective this
    rw [add_smul, add_smul] at h2
    exact nsmul_unitStep_injective μ (hp μ) hr1 hr2 (add_right_cancel h2)
  · have h2 : (r + 1) • (unitStep l ν : F.Site l) = (r' + 1) • unitStep l ν := by
      have := h
      simp only [sideOffset, Matrix.cons_val] at this
      exact sub_right_injective this
    rw [add_smul, add_smul] at h2
    exact nsmul_unitStep_injective ν (hp ν) hr1 hr2 (add_right_cancel h2)
theorem sumAroundSquare_le_four_mul {l : ℕ} (C : Finset (F.Site l × Fin 4)) (f : F.Site l × Fin 4 → ℝ)
    (hf : ∀ c, 0 ≤ f c) (x : F.Site l) (n : ℕ) (μ ν : Fin 4)
    (hp : ∀ k, F.period l k = 0 ∨ n ≤ F.period l k)
    (hC : ∀ r < n, ∀ s, (x + sideOffset l n μ ν s r, sideDirection μ ν s) ∈ C) :
    sumAroundSquare f x n μ ν ≤ 4 * ∑ c ∈ C, f c := by
  classical
  rw [sumAroundSquare_eq_sum_sides, Finset.sum_product_right]
  have h2 : ∀ s ∈ (Finset.univ : Finset (Fin 4)),
      ∑ r ∈ Finset.range n, f (x + sideOffset l n μ ν s r, sideDirection μ ν s) ≤ ∑ c ∈ C, f c := by
    intro s _
    have hinj : Set.InjOn (fun r => ((x + sideOffset l n μ ν s r, sideDirection μ ν s) :
        F.Site l × Fin 4)) (Finset.range n : Finset ℕ) := by
      intro r hr r' hr' h
      exact sideOffset_injOn n μ ν hp s hr hr' (add_left_cancel (congrArg Prod.fst h))
    have := Finset.sum_image (f := f) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hf c
    intro c hc
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hc
    exact hC r (Finset.mem_range.1 hr) s
  have h3 := Finset.sum_le_sum h2
  simpa using h3
theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
theorem ellTwo_blockAverage_le {i : ℕ} (hi : i < F.top) (hL : Odd F.blockSide)
    (Y : Finset (F.Site (i + 1))) (Z : Finset (F.Site i)) (T : F.Site i → ℝ)
    (hZ : ∀ x ∈ Y, ∀ h ∈ centredCube F.blockSide, refineSite x + siteOfCoords i h ∈ Z) :
    ellTwo Y (fun x => average (centredCube F.blockSide) fun h => T (refineSite x + siteOfCoords i h)) ≤
      ((F.blockSide : ℝ) ^ 2)⁻¹ * ellTwo Z T := by
  classical
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hc := card_centredCube F.blockSide hL
  have hRnn : 0 ≤ ((F.blockSide : ℝ) ^ 2)⁻¹ * ellTwo Z T := mul_nonneg (by positivity) (ellTwo_nonneg _ _)
  refine ellTwo_le Y _ hRnn ?_
  have h1 : ∀ x ∈ Y, (average (centredCube F.blockSide) fun h => T (refineSite x + siteOfCoords i h)) ^ 2 ≤
      ((F.blockSide : ℝ) ^ 4)⁻¹ *
        ∑ h ∈ centredCube F.blockSide, T (refineSite x + siteOfCoords i h) ^ 2 := by
    intro x _
    unfold average
    have h2 := sq_sum_le_card_mul_sum_sq (s := centredCube F.blockSide)
      (f := fun h => T (refineSite x + siteOfCoords i h))
    rw [hc] at h2 ⊢
    rw [mul_pow, div_pow, one_pow]
    have h3 : (0 : ℝ) < (F.blockSide : ℝ) ^ 4 := by positivity
    calc 1 / ((F.blockSide : ℝ) ^ 4) ^ 2 *
          (∑ h ∈ centredCube F.blockSide, T (refineSite x + siteOfCoords i h)) ^ 2
        ≤ 1 / ((F.blockSide : ℝ) ^ 4) ^ 2 * ((F.blockSide : ℝ) ^ 4 *
          ∑ h ∈ centredCube F.blockSide, T (refineSite x + siteOfCoords i h) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, ← Finset.sum_product']
  have hinj : Set.InjOn (fun q : F.Site (i + 1) × (Fin 4 → ℤ) => refineSite q.1 + siteOfCoords i q.2)
      (Y ×ˢ centredCube F.blockSide : Finset _) := by
    rintro ⟨x, h⟩ hq ⟨x', h'⟩ hq' e
    have a1 := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    have a2 := Finset.mem_product.1 (Finset.mem_coe.1 hq')
    obtain ⟨b1, b2⟩ := refineSite_add_injective hi hL a1.2 a2.2 e
    exact Prod.ext b1 b2
  have h4 : ∑ q ∈ Y ×ˢ centredCube F.blockSide, T (refineSite q.1 + siteOfCoords i q.2) ^ 2 ≤
      ∑ z ∈ Z, T z ^ 2 := by
    have := Finset.sum_image (f := fun z => T z ^ 2) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => sq_nonneg _
    intro c hc'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hc'
    have a1 := Finset.mem_product.1 hq
    exact hZ q.1 a1.1 q.2 a1.2
  rw [mul_pow, ellTwo_sq, inv_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)
theorem sumAroundSquare_add {l : ℕ} (f g : F.Site l × Fin 4 → ℝ) (x : F.Site l) (n : ℕ) (μ ν : Fin 4) :
    sumAroundSquare (fun c => f c + g c) x n μ ν = sumAroundSquare f x n μ ν + sumAroundSquare g x n μ ν := by
  simp only [sumAroundSquare_eq_sum_sides, Finset.sum_add_distrib]
theorem sumAroundSquare_const_mul {l : ℕ} (a : ℝ) (f : F.Site l × Fin 4 → ℝ) (x : F.Site l) (n : ℕ)
    (μ ν : Fin 4) :
    sumAroundSquare (fun c => a * f c) x n μ ν = a * sumAroundSquare f x n μ ν := by
  simp only [sumAroundSquare_eq_sum_sides, Finset.mul_sum]
theorem sumAroundSquare_nonneg {l : ℕ} (f : F.Site l × Fin 4 → ℝ) (hf : ∀ c, 0 ≤ f c) (x : F.Site l)
    (n : ℕ) (μ ν : Fin 4) : 0 ≤ sumAroundSquare f x n μ ν := by
  rw [sumAroundSquare_eq_sum_sides]
  exact Finset.sum_nonneg fun q _ => hf _
section chain
variable (hs : SquareDescentEstimate) (hb : ContourVarianceCurvatureBound)
structure PlaneCut (F : BlockFrame) (m j : ℕ) (X : Finset (F.Site m)) (μ ν : Fin 4)
    (Y : Finset (F.Site j)) : Prop where
  ordered : μ < ν
  level_le : j ≤ m
  le_top : m ≤ F.top
  odd_side : Odd F.blockSide
  admissible : IsAdmissibleAmbient F
  four_le : 4 ≤ F.blockSide
  mem_cut : ∀ y ∈ Y, (y, μ, ν) ∈ cutPlaquettes (cutBelow j X)
variable {m j : ℕ} {X : Finset (F.Site m)} {μ ν : Fin 4} {Y : Finset (F.Site j)}
theorem PlaneCut.rectangle_mem (D : PlaneCut F m j X μ ν Y) {l : ℕ} (hl : l ≤ j) {x : F.Site l}
    (hx : x ∈ cutBelow l Y) (r1 r2 : ℕ) (h1 : r1 ≤ F.blockSide ^ (j - l))
    (h2 : r2 ≤ F.blockSide ^ (j - l)) :
    x + r1 • unitStep l μ + r2 • unitStep l ν ∈ cutBelow l X := by
  simp only [cutBelow, Finset.mem_biUnion] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact rectangle_mem_cutBelow hl D.level_le D.le_top D.odd_side X (y, μ, ν) (D.mem_cut y hy) hxy
    r1 r2 h1 h2
theorem sides_mem_cutBonds (D : PlaneCut F m j X μ ν Y) {l : ℕ} (hl : l ≤ j) {x : F.Site l}
    (hx : x ∈ cutBelow l Y) (r : ℕ) (hr : r < F.blockSide ^ (j - l)) (s : Fin 4) :
    (x + sideOffset l (F.blockSide ^ (j - l)) μ ν s r, sideDirection μ ν s) ∈
      cutBonds (cutBelow l X) := by
  set n := F.blockSide ^ (j - l) with hn
  obtain ⟨q, hq⟩ : ∃ q, n = q + (r + 1) := ⟨n - (r + 1), by omega⟩
  have R := fun r1 r2 h1 h2 => D.rectangle_mem hl hx r1 r2 h1 h2
  simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  have hnq : ∀ e : F.Site l, n • e = q • e + (r + 1) • e := by
    intro e
    rw [hq, add_smul]
  fin_cases s
  · constructor
    · have := R r 0 hr.le (Nat.zero_le _)
      convert this using 1
      simp [sideOffset]
    · have := R (r + 1) 0 hr (Nat.zero_le _)
      convert this using 1
      simp only [sideOffset, sideDirection, Fin.zero_eta, Matrix.cons_val_zero, zero_smul, add_zero,
        add_smul, one_smul, add_assoc]
  · constructor
    · have := R n r le_rfl hr.le
      convert this using 1
      simp only [sideOffset, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_assoc]
    · have := R n (r + 1) le_rfl hr
      convert this using 1
      simp only [sideOffset, sideDirection, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        add_smul, one_smul, add_assoc]
  · constructor
    · show x + (n • unitStep l μ + n • unitStep l ν - (r + 1) • unitStep l μ) ∈ cutBelow l X
      have e : x + (n • unitStep l μ + n • unitStep l ν - (r + 1) • unitStep l μ) =
          x + q • unitStep l μ + n • unitStep l ν := by
        rw [hnq (unitStep l μ)]
        abel
      rw [e]
      exact R q n (by omega) le_rfl
    · show x + (n • unitStep l μ + n • unitStep l ν - (r + 1) • unitStep l μ) + unitStep l μ ∈
        cutBelow l X
      have e : x + (n • unitStep l μ + n • unitStep l ν - (r + 1) • unitStep l μ) + unitStep l μ =
          x + (q + 1) • unitStep l μ + n • unitStep l ν := by
        rw [hnq (unitStep l μ), add_smul q 1, one_smul]
        abel
      rw [e]
      exact R (q + 1) n (by omega) le_rfl
  · constructor
    · show x + (n • unitStep l ν - (r + 1) • unitStep l ν) ∈ cutBelow l X
      have e : x + (n • unitStep l ν - (r + 1) • unitStep l ν) =
          x + 0 • unitStep l μ + q • unitStep l ν := by
        rw [hnq (unitStep l ν), zero_smul]
        abel
      rw [e]
      exact R 0 q (Nat.zero_le _) (by omega)
    · show x + (n • unitStep l ν - (r + 1) • unitStep l ν) + unitStep l ν ∈ cutBelow l X
      have e : x + (n • unitStep l ν - (r + 1) • unitStep l ν) + unitStep l ν =
          x + 0 • unitStep l μ + (q + 1) • unitStep l ν := by
        rw [hnq (unitStep l ν), zero_smul, add_smul q 1, one_smul]
        abel
      rw [e]
      exact R 0 (q + 1) (Nat.zero_le _) (by omega)
theorem period_eq_zero_or_le (D : PlaneCut F m j X μ ν Y) {l : ℕ} (hl : l ≤ j) (k : Fin 4) :
    F.period l k = 0 ∨ F.blockSide ^ (j - l) ≤ F.period l k := by
  have hj : j ≤ F.top := D.level_le.trans D.le_top
  have hs : F.extent k = 0 ∨ 64 ≤ F.extent k := by
    rcases D.admissible with h | h
    · exact Or.inl (h k)
    · exact Or.inr (h k)
  rcases hs with h | h
  · left
    simp [BlockFrame.period, h]
  · right
    have hL : 1 ≤ F.blockSide := D.odd_side.pos
    have h1 : F.blockSide ^ (j - l) ≤ F.blockSide ^ (F.top - l) := Nat.pow_le_pow_right hL (by omega)
    have h2 : F.blockSide ^ (F.top - l) ≤ F.extent k * F.blockSide ^ (F.top - l) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact h1.trans h2
theorem blockFit_nonneg {l : ℕ} (W : F.GaugeField l) (V : F.GaugeField (l + 1))
    (c : F.Site (l + 1) × Fin 4) : 0 ≤ blockFit W V c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
def levelDefectNorm (U : F.FieldChain) (j l : ℕ) (μ ν : Fin 4) (Y : Finset (F.Site j)) : ℝ :=
  ellTwo (cutBelow l Y) fun x => squareHolonomyDefect (U l) x (F.blockSide ^ (j - l)) μ ν
def scaledDefectNorm (U : F.FieldChain) (j l : ℕ) (μ ν : Fin 4) (Y : Finset (F.Site j)) : ℝ :=
  levelDefectNorm U j l μ ν Y / ((F.blockSide : ℝ) ^ (j - l)) ^ 2
def cutFitSum (X : Finset (F.Site m)) (U : F.FieldChain) (l : ℕ) : ℝ :=
  ∑ c ∈ cutBonds (cutBelow (l + 1) X), blockFit (U l) (U (l + 1)) c
def cutVarianceSum (X : Finset (F.Site m)) (U : F.FieldChain) (l : ℕ) : ℝ :=
  ∑ c ∈ cutBonds (cutBelow (l + 1) X), contourVariance (U l) c
theorem contourVariance_nonneg {l : ℕ} (W : F.GaugeField l) (c : F.Site (l + 1) × Fin 4) :
    0 ≤ contourVariance W c := by
  unfold contourVariance variance average
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => sq_nonneg _)
theorem refineSite_add_mem_cutBelow (D : PlaneCut F m j X μ ν Y) {l : ℕ} (hl : l < j)
    {x : F.Site (l + 1)} (hx : x ∈ cutBelow (l + 1) Y) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) :
    refineSite x + siteOfCoords l h ∈ cutBelow l Y := by
  simp only [cutBelow, Finset.mem_biUnion] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨y, hy, sitesBelow_trans (by omega) hl (D.level_le.trans D.le_top) D.odd_side y hxy ?_⟩
  have e : l + 1 - l = 1 := by omega
  simp only [sitesBelow, e, pow_one]
  refine Finset.mem_image.2 ⟨h, hh, ?_⟩
  funext k
  simp [refineSite, siteOfCoords]
include hs in
theorem squareHolonomyDefect_succ_le {l : ℕ} (hl' : l < F.top) (hL : Odd F.blockSide)
    (U : F.FieldChain) (x : F.Site (l + 1)) (n K : ℕ) (μ ν : Fin 4) (hnL : n * F.blockSide = K) :
    squareHolonomyDefect (U (l + 1)) x n μ ν ≤
      (average (centredCube F.blockSide) fun h =>
        squareHolonomyDefect (U l) (refineSite x + siteOfCoords l h) K μ ν) +
      sumAroundSquare (fun c => 2 * Real.sqrt (blockFit (U l) (U (l + 1)) c)) x n μ ν +
      (2 * (n : ℝ) + 2) * sumAroundSquare (contourVariance (U l)) x n μ ν := by
  have h1 := hs F l hl' hL (U l) (U (l + 1)) x n μ ν
  rw [hnL, sumAroundSquare_add, sumAroundSquare_const_mul 2 (contourVariance (U l))] at h1
  have e : (2 * (n : ℝ) + 2) * sumAroundSquare (contourVariance (U l)) x n μ ν =
      2 * sumAroundSquare (contourVariance (U l)) x n μ ν +
        2 * (n : ℝ) * sumAroundSquare (contourVariance (U l)) x n μ ν := by
    ring
  rw [e, ← add_assoc]
  refine h1.trans (le_of_eq ?_)
  ring
theorem ellTwo_fit_term_le {l : ℕ} (Y1 : Finset (F.Site (l + 1))) (C : Finset (F.Site (l + 1) × Fin 4))
    (W : F.GaugeField l) (V : F.GaugeField (l + 1)) (n : ℕ) (μ ν : Fin 4)
    (hCs : ∀ x ∈ Y1, ∀ r < n, ∀ s, (x + sideOffset (l + 1) n μ ν s r, sideDirection μ ν s) ∈ C) :
    ellTwo Y1 (fun x => sumAroundSquare (fun c => 2 * Real.sqrt (blockFit W V c)) x n μ ν) ≤
      8 * (n : ℝ) * Real.sqrt (∑ c ∈ C, blockFit W V c) := by
  have hf0 : ∀ c, 0 ≤ blockFit W V c := blockFit_nonneg W V
  have hfs : 0 ≤ ∑ c ∈ C, blockFit W V c := Finset.sum_nonneg fun c _ => hf0 c
  refine ellTwo_le Y1 _ (by positivity) ?_
  refine (sum_sq_sumAroundSquare_le Y1 C _ n μ ν hCs).trans (le_of_eq ?_)
  have e1 : ∑ c ∈ C, (2 * Real.sqrt (blockFit W V c)) ^ 2 = 4 * ∑ c ∈ C, blockFit W V c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_pow, Real.sq_sqrt (hf0 c)]
    norm_num
  rw [e1, mul_pow, mul_pow, Real.sq_sqrt hfs]
  ring
theorem ellTwo_variance_term_le {l : ℕ} (Y1 : Finset (F.Site (l + 1)))
    (C : Finset (F.Site (l + 1) × Fin 4)) (W : F.GaugeField l) (n : ℕ) (μ ν : Fin 4)
    (hCs : ∀ x ∈ Y1, ∀ r < n, ∀ s, (x + sideOffset (l + 1) n μ ν s r, sideDirection μ ν s) ∈ C)
    (hp : ∀ k, F.period (l + 1) k = 0 ∨ n ≤ F.period (l + 1) k) :
    ellTwo Y1 (fun x => sumAroundSquare (contourVariance W) x n μ ν) ≤
      4 * Real.sqrt (n : ℝ) * ∑ c ∈ C, contourVariance W c := by
  have hs0 : ∀ c, 0 ≤ contourVariance W c := contourVariance_nonneg W
  have hss : 0 ≤ ∑ c ∈ C, contourVariance W c := Finset.sum_nonneg fun c _ => hs0 c
  have hn0 : (0 : ℝ) ≤ n := by positivity
  refine ellTwo_le Y1 _ (by positivity) ?_
  have h1 : ∀ x ∈ Y1, sumAroundSquare (contourVariance W) x n μ ν ^ 2 ≤
      (4 * ∑ c ∈ C, contourVariance W c) * sumAroundSquare (contourVariance W) x n μ ν := by
    intro x hx
    have h2 := sumAroundSquare_le_four_mul C (contourVariance W) hs0 x n μ ν hp
      (fun r hr s => hCs x hx r hr s)
    have h3 := sumAroundSquare_nonneg (contourVariance W) hs0 x n μ ν
    rw [sq]
    exact mul_le_mul_of_nonneg_right h2 h3
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h4 := sum_sumAroundSquare_le Y1 C (contourVariance W) hs0 n μ ν hCs
  calc 4 * (∑ c ∈ C, contourVariance W c) * _ ≤
        4 * (∑ c ∈ C, contourVariance W c) * (4 * (n : ℝ) * ∑ c ∈ C, contourVariance W c) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hn0]
        ring
theorem ellTwo_le_three {A : Type} (Y : Finset A) (T a g b : A → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hnn : ∀ x ∈ Y, 0 ≤ T x) (hpt : ∀ x ∈ Y, T x ≤ a x + g x + c * b x) :
    ellTwo Y T ≤ ellTwo Y a + ellTwo Y g + c * ellTwo Y b := by
  have h1 := ellTwo_mono Y hnn hpt
  have s1 := ellTwo_add Y (fun x => a x + g x) (fun x => c * b x)
  have s2 := ellTwo_add Y a g
  rw [ellTwo_const_mul Y _ hc] at s1
  linarith
include hs in
theorem levelDefectNorm_succ_le (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) {l : ℕ} (hl : l < j) :
    levelDefectNorm U j (l + 1) μ ν Y ≤ ((F.blockSide : ℝ) ^ 2)⁻¹ * levelDefectNorm U j l μ ν Y +
      8 * ((F.blockSide ^ (j - (l + 1)) : ℕ) : ℝ) * Real.sqrt (cutFitSum X U l) +
      (2 * ((F.blockSide ^ (j - (l + 1)) : ℕ) : ℝ) + 2) *
        (4 * Real.sqrt ((F.blockSide ^ (j - (l + 1)) : ℕ) : ℝ) * cutVarianceSum X U l) := by
  have hl' : l < F.top := by have := D.level_le; have := D.le_top; omega
  have hnL : F.blockSide ^ (j - (l + 1)) * F.blockSide = F.blockSide ^ (j - l) := by
    rw [← pow_succ]
    congr 1
    omega
  have hCs : ∀ x ∈ cutBelow (l + 1) Y, ∀ r < F.blockSide ^ (j - (l + 1)), ∀ s,
      (x + sideOffset (l + 1) (F.blockSide ^ (j - (l + 1))) μ ν s r, sideDirection μ ν s) ∈
        cutBonds (cutBelow (l + 1) X) :=
    fun x hx r hr s => sides_mem_cutBonds D hl hx r hr s
  have hA := ellTwo_blockAverage_le hl' D.odd_side (cutBelow (l + 1) Y) (cutBelow l Y)
    (fun z => squareHolonomyDefect (U l) z (F.blockSide ^ (j - l)) μ ν)
    (fun x hx h hh => refineSite_add_mem_cutBelow D hl hx hh)
  have hG := ellTwo_fit_term_le (cutBelow (l + 1) Y) (cutBonds (cutBelow (l + 1) X)) (U l) (U (l + 1))
    (F.blockSide ^ (j - (l + 1))) μ ν hCs
  have hB := ellTwo_variance_term_le (cutBelow (l + 1) Y) (cutBonds (cutBelow (l + 1) X)) (U l)
    (F.blockSide ^ (j - (l + 1))) μ ν hCs (fun k => period_eq_zero_or_le D hl k)
  have hc : (0 : ℝ) ≤ 2 * ((F.blockSide ^ (j - (l + 1)) : ℕ) : ℝ) + 2 := by positivity
  have h3 := ellTwo_le_three (cutBelow (l + 1) Y)
    (fun x => squareHolonomyDefect (U (l + 1)) x (F.blockSide ^ (j - (l + 1))) μ ν)
    (fun x => average (centredCube F.blockSide) fun h =>
      squareHolonomyDefect (U l) (refineSite x + siteOfCoords l h) (F.blockSide ^ (j - l)) μ ν)
    (fun x => sumAroundSquare (fun c => 2 * Real.sqrt (blockFit (U l) (U (l + 1)) c)) x
      (F.blockSide ^ (j - (l + 1))) μ ν)
    (fun x => sumAroundSquare (contourVariance (U l)) x (F.blockSide ^ (j - (l + 1))) μ ν) hc
    (fun x _ => norm_nonneg _)
    (fun x _ => squareHolonomyDefect_succ_le hs hl' D.odd_side U x _ _ μ ν hnL)
  exact h3.trans (add_le_add (add_le_add hA hG) (mul_le_mul_of_nonneg_left hB hc))
theorem inv_sqrt_pow_le_half_pow (hL : 4 ≤ F.blockSide) (k : ℕ) :
    (1 / Real.sqrt ((F.blockSide : ℝ) ^ k)) ≤ (1 / 2 : ℝ) ^ k := by
  have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ (F.blockSide : ℝ) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : (2 : ℝ) ^ 2 ≤ F.blockSide := by
      have : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
      linarith
    exact pow_le_pow_left₀ (by norm_num) this k
  have h2 : (2 : ℝ) ^ k ≤ Real.sqrt ((F.blockSide : ℝ) ^ k) := Real.le_sqrt_of_sq_le h1
  have h3 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [one_div_pow]
  exact one_div_le_one_div_of_le h3 h2
include hs in
theorem scaledDefectNorm_succ_le (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) {l : ℕ} (hl : l < j) :
    scaledDefectNorm U j (l + 1) μ ν Y ≤ scaledDefectNorm U j l μ ν Y +
      (8 * Real.sqrt (cutFitSum X U l) + 16 * cutVarianceSum X U l) * (1 / 2 : ℝ) ^ (j - (l + 1)) := by
  have h1 := levelDefectNorm_succ_le hs D U hl
  rw [Nat.cast_pow] at h1
  have hL4 : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast D.four_le
  set k := j - (l + 1) with hk
  have hn1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ k := one_le_pow₀ (by linarith)
  set nn := (F.blockSide : ℝ) ^ k with hnn
  set sn := Real.sqrt nn with hsn
  have hs2 : sn ^ 2 = nn := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ sn := by
    rw [hsn]
    exact Real.one_le_sqrt.2 hn1
  have hw := inv_sqrt_pow_le_half_pow D.four_le k
  rw [← hnn, ← hsn] at hw
  set P := Real.sqrt (cutFitSum X U l) with hP
  set Q := cutVarianceSum X U l with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun c _ => contourVariance_nonneg (U l) c
  have e0 : ((F.blockSide : ℝ) ^ (j - l)) = nn * F.blockSide := by
    rw [hnn, ← pow_succ]
    congr 1
    omega
  unfold scaledDefectNorm
  have e1 : j - (l + 1) = k := rfl
  rw [e1, ← hnn, e0]
  set N1 := levelDefectNorm U j (l + 1) μ ν Y
  set N0 := levelDefectNorm U j l μ ν Y
  have key : N1 / nn ^ 2 ≤ N0 / (nn * F.blockSide) ^ 2 + (8 * P + 16 * Q) * (1 / sn) := by
    have a1 : N1 / nn ^ 2 ≤ (((F.blockSide : ℝ) ^ 2)⁻¹ * N0 + 8 * nn * P +
        (2 * nn + 2) * (4 * sn * Q)) / nn ^ 2 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    refine a1.trans ?_
    have a2 : ((F.blockSide : ℝ) ^ 2)⁻¹ * N0 / nn ^ 2 = N0 / (nn * F.blockSide) ^ 2 := by
      field_simp
    have a3 : 8 * nn * P / nn ^ 2 ≤ 8 * P * (1 / sn) := by
      have : 8 * nn * P / nn ^ 2 = 8 * P * (1 / nn) := by
        field_simp
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine one_div_le_one_div_of_le (by linarith) ?_
      nlinarith
    have a4 : (2 * nn + 2) * (4 * sn * Q) / nn ^ 2 ≤ 16 * Q * (1 / sn) := by
      rw [div_le_iff₀ (by positivity)]
      have e : 16 * Q * (1 / sn) * nn ^ 2 = 16 * Q * nn * sn := by
        rw [← hs2]
        field_simp
      rw [e]
      have : (2 * nn + 2) * (4 * sn * Q) ≤ (4 * nn) * (4 * sn * Q) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have split : (((F.blockSide : ℝ) ^ 2)⁻¹ * N0 + 8 * nn * P + (2 * nn + 2) * (4 * sn * Q)) / nn ^ 2 =
        ((F.blockSide : ℝ) ^ 2)⁻¹ * N0 / nn ^ 2 + 8 * nn * P / nn ^ 2 +
          (2 * nn + 2) * (4 * sn * Q) / nn ^ 2 := by
      rw [add_div, add_div]
    rw [split, a2]
    linarith
  have hz : (8 * P + 16 * Q) * (1 / sn) ≤ (8 * P + 16 * Q) * (1 / 2 : ℝ) ^ k :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  linarith
include hs in
theorem scaledDefectNorm_top_le (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) {P Q : ℝ}
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ l < j, Real.sqrt (cutFitSum X U l) ≤ P) (hQ : ∀ l < j, cutVarianceSum X U l ≤ Q) :
    scaledDefectNorm U j j μ ν Y ≤ scaledDefectNorm U j 0 μ ν Y + 2 * (8 * P + 16 * Q) := by
  have hd : ∀ d, d ≤ j → scaledDefectNorm U j j μ ν Y ≤ scaledDefectNorm U j (j - d) μ ν Y +
      (8 * P + 16 * Q) * (2 - 2 * (1 / 2 : ℝ) ^ d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have hl : j - (d + 1) < j := by omega
      have h2 := scaledDefectNorm_succ_le hs D U hl
      have e1 : j - (d + 1) + 1 = j - d := by omega
      have e2 : j - (j - (d + 1) + 1) = d := by omega
      rw [e1] at h2
      rw [show j - (j - d) = d by omega] at h2
      have h3 : (8 * Real.sqrt (cutFitSum X U (j - (d + 1))) + 16 * cutVarianceSum X U (j - (d + 1))) *
          (1 / 2 : ℝ) ^ d ≤ (8 * P + 16 * Q) * (1 / 2 : ℝ) ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [hP _ hl, hQ _ hl]
      have e3 : (8 * P + 16 * Q) * (2 - 2 * (1 / 2 : ℝ) ^ (d + 1)) =
          (8 * P + 16 * Q) * (2 - 2 * (1 / 2 : ℝ) ^ d) + (8 * P + 16 * Q) * (1 / 2 : ℝ) ^ d := by
        rw [pow_succ]
        ring
      rw [e3]
      linarith
  have h := hd j le_rfl
  rw [Nat.sub_self] at h
  have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  have : (8 * P + 16 * Q) * (2 - 2 * (1 / 2 : ℝ) ^ j) ≤ (8 * P + 16 * Q) * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith
theorem squareHolonomyDefect_one {l : ℕ} (Xf : F.GaugeField l) (x : F.Site l) (μ ν : Fin 4) :
    squareHolonomyDefect Xf x 1 μ ν = plaquetteDefect Xf (x, μ, ν) := by
  simp [squareHolonomyDefect, plaquetteDefect, squarePath, plaquetteHolonomy]
theorem ellTwo_curvature_le_scaled (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) :
    ellTwo Y (fun y => plaquetteDefect (U j) (y, μ, ν)) ≤ scaledDefectNorm U j j μ ν Y := by
  unfold scaledDefectNorm levelDefectNorm
  simp only [Nat.sub_self, pow_zero, one_pow, div_one, squareHolonomyDefect_one]
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro y hy
  simp only [cutBelow, Finset.mem_biUnion]
  exact ⟨y, hy, self_mem_sitesBelow D.odd_side y⟩
def curvatureEnergy {l : ℕ} (Z : Finset (F.Site l)) (W : F.GaugeField l) : ℝ :=
  ∑ p ∈ cutPlaquettes Z, plaquetteDefect W p ^ 2
theorem curvatureEnergy_nonneg {l : ℕ} (Z : Finset (F.Site l)) (W : F.GaugeField l) :
    0 ≤ curvatureEnergy Z W :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
include hb in
theorem scaledDefectNorm_zero_le (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) :
    scaledDefectNorm U j 0 μ ν Y ≤ Real.sqrt (curvatureEnergy (cutBelow 0 X) (U 0)) := by
  classical
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast D.odd_side.pos
  set N := F.blockSide ^ j with hN
  have hNr : (F.blockSide : ℝ) ^ (j - 0) = (N : ℝ) := by rw [hN]; push_cast; rfl
  unfold scaledDefectNorm
  rw [hNr]
  have hN1 : (1 : ℝ) ≤ N := by
    rw [← hNr]
    exact one_le_pow₀ hL1
  set E := curvatureEnergy (cutBelow 0 X) (U 0) with hE
  have hE0 : 0 ≤ E := curvatureEnergy_nonneg _ _
  rw [div_le_iff₀ (by positivity)]
  have hI : ((Finset.range N ×ˢ Finset.range N).card : ℝ) = (N : ℝ) ^ 2 := by
    simp
    ring
  have hrow : ∀ q ∈ Finset.range N ×ˢ Finset.range N,
      ∑ x ∈ cutBelow 0 Y, plaquetteDefect (U 0) (x + q.1 • unitStep 0 μ + q.2 • unitStep 0 ν, μ, ν) ^ 2 ≤
        E := by
    intro q hq
    have hq' := Finset.mem_product.1 hq
    have h1 : q.1 < N := Finset.mem_range.1 hq'.1
    have h2 : q.2 < N := Finset.mem_range.1 hq'.2
    have hinj : Set.InjOn (fun x : F.Site 0 => ((x + q.1 • unitStep 0 μ + q.2 • unitStep 0 ν, μ, ν) :
        F.Site 0 × Fin 4 × Fin 4)) (cutBelow 0 Y) := by
      intro x _ x' _ h
      have := congrArg Prod.fst h
      exact add_right_cancel (add_right_cancel this)
    have := Finset.sum_image (f := fun p => plaquetteDefect (U 0) p ^ 2) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    have R := fun (r1 r2 : ℕ) (a : r1 ≤ F.blockSide ^ (j - 0)) (b : r2 ≤ F.blockSide ^ (j - 0)) =>
      D.rectangle_mem (Nat.zero_le j) hx r1 r2 a b
    have hb0 := R q.1 q.2 h1.le h2.le
    have hb1 := R (q.1 + 1) q.2 h1 h2.le
    have hb2 := R q.1 (q.2 + 1) h1.le h2
    have hb3 := R (q.1 + 1) (q.2 + 1) h1 h2
    simp only [add_smul, one_smul] at hb1 hb2 hb3
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨hb0, D.ordered, ?_⟩
    intro w hw
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hb0
    · convert hb1 using 1
      first | abel | simp only [add_comm, add_left_comm, add_assoc]
    · convert hb2 using 1
      first | abel | simp only [add_comm, add_left_comm, add_assoc]
    · convert hb3 using 1
      first | abel | simp only [add_comm, add_left_comm, add_assoc]
  have hpt : ∀ x ∈ cutBelow 0 Y, squareHolonomyDefect (U 0) x N μ ν ^ 2 ≤ (N : ℝ) ^ 2 *
      ∑ q ∈ Finset.range N ×ˢ Finset.range N,
        plaquetteDefect (U 0) (x + q.1 • unitStep 0 μ + q.2 • unitStep 0 ν, μ, ν) ^ 2 := by
    intro x _
    have h1 := hb.2 F 0 (U 0) x N μ ν D.ordered
    rw [← Finset.sum_product'] at h1
    have h0 : 0 ≤ squareHolonomyDefect (U 0) x N μ ν := norm_nonneg _
    refine (pow_le_pow_left₀ h0 h1 2).trans ?_
    rw [← hI]
    exact sq_sum_le_card_mul_sum_sq
  refine ellTwo_le _ _ (by positivity) ?_
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h3 := Finset.sum_le_sum hrow
  rw [Finset.sum_const, nsmul_eq_mul, hI] at h3
  calc (N : ℝ) ^ 2 * _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * E) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt hE0]
        ring
include hs hb in
theorem ellTwo_plane_curvature_le (D : PlaneCut F m j X μ ν Y) (U : F.FieldChain) {P Q : ℝ}
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ l < j, Real.sqrt (cutFitSum X U l) ≤ P) (hQ : ∀ l < j, cutVarianceSum X U l ≤ Q) :
    ellTwo Y (fun y => plaquetteDefect (U j) (y, μ, ν)) ≤
      Real.sqrt (curvatureEnergy (cutBelow 0 X) (U 0)) + 2 * (8 * P + 16 * Q) := by
  have h1 := ellTwo_curvature_le_scaled D U
  have h2 := scaledDefectNorm_top_le hs D U hP0 hQ0 hP hQ
  have h3 := scaledDefectNorm_zero_le hb D U
  linarith
include hs hb in
theorem sqrt_curvatureEnergy_le (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (h4 : 4 ≤ F.blockSide) (X : Finset (F.Site m)) (U : F.FieldChain)
    {P Q : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ l < j, Real.sqrt (cutFitSum X U l) ≤ P) (hQ : ∀ l < j, cutVarianceSum X U l ≤ Q) :
    Real.sqrt (curvatureEnergy (cutBelow j X) (U j)) ≤
      4 * (Real.sqrt (curvatureEnergy (cutBelow 0 X) (U 0)) + 2 * (8 * P + 16 * Q)) := by
  classical
  set R := Real.sqrt (curvatureEnergy (cutBelow 0 X) (U 0)) + 2 * (8 * P + 16 * Q) with hR
  have hplane : ∀ pl : Fin 4 × Fin 4,
      ∑ p ∈ (cutPlaquettes (cutBelow j X)).filter (fun p => p.2 = pl), plaquetteDefect (U j) p ^ 2 ≤
        R ^ 2 := by
    rintro ⟨μ, ν⟩
    by_cases hlt : μ < ν
    · set Yp := ((cutPlaquettes (cutBelow j X)).filter (fun p => p.2 = (μ, ν))).image Prod.fst with hYp
      have D : PlaneCut F m j X μ ν Yp := by
        refine ⟨hlt, hjm, hm, hL, hA, h4, ?_⟩
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
        have hp' := Finset.mem_filter.1 hp
        have : p = (p.1, μ, ν) := Prod.ext rfl hp'.2
        rw [← this]
        exact hp'.1
      have h1 := ellTwo_plane_curvature_le hs hb D U hP0 hQ0 hP hQ
      have e : ∑ p ∈ (cutPlaquettes (cutBelow j X)).filter (fun p => p.2 = (μ, ν)),
          plaquetteDefect (U j) p ^ 2 = ∑ y ∈ Yp, plaquetteDefect (U j) (y, μ, ν) ^ 2 := by
        rw [hYp, Finset.sum_image]
        · refine Finset.sum_congr rfl fun p hp => ?_
          have hp' := Finset.mem_filter.1 hp
          have : p = (p.1, μ, ν) := Prod.ext rfl hp'.2
          rw [← this]
        · intro p hp p' hp' h
          have a := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
          have b := (Finset.mem_filter.1 (Finset.mem_coe.1 hp')).2
          exact Prod.ext h (a.trans b.symm)
      rw [e, ← ellTwo_sq]
      exact pow_le_pow_left₀ (ellTwo_nonneg _ _) h1 2
    · have e : (cutPlaquettes (cutBelow j X)).filter (fun p => p.2 = (μ, ν)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun p hp h => hlt ?_
        have := (Finset.mem_filter.1 hp).2.1
        rw [h] at this
        exact this
      rw [e]
      simp only [Finset.sum_empty]
      positivity
  have hsum : curvatureEnergy (cutBelow j X) (U j) ≤ (4 * R) ^ 2 := by
    unfold curvatureEnergy
    rw [← Finset.sum_fiberwise (s := cutPlaquettes (cutBelow j X)) (g := fun p => p.2)]
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4 × Fin 4))) fun pl _ => hplane pl
    refine this.trans (le_of_eq ?_)
    simp
    ring
  exact Real.sqrt_le_iff.2 ⟨by positivity, hsum⟩
theorem sum_sum_le_mul_of_multiplicity {A B : Type} (Ps : Finset A) (Q : Finset B) (Qp : A → Finset B)
    (G : B → ℝ) (hG : ∀ q, 0 ≤ G q) (K : ℕ) (hsub : ∀ p ∈ Ps, Qp p ⊆ Q)
    (hmul : ∀ q ∈ Q, ∀ [DecidablePred fun p => q ∈ Qp p], ((Ps.filter fun p => q ∈ Qp p).card) ≤ K) :
    ∑ p ∈ Ps, ∑ q ∈ Qp p, G q ≤ K * ∑ q ∈ Q, G q := by
  classical
  calc ∑ p ∈ Ps, ∑ q ∈ Qp p, G q
      = ∑ p ∈ Ps, ∑ q ∈ Q, (if q ∈ Qp p then G q else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hsub p hp)]
    _ = ∑ q ∈ Q, ∑ p ∈ Ps, (if q ∈ Qp p then G q else 0) := Finset.sum_comm
    _ ≤ ∑ q ∈ Q, (K : ℝ) * G q := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmul q hq) (hG q)
    _ = _ := (Finset.mul_sum _ _ _).symm
theorem sitesBelow_unique {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide)
    {x : F.Site i} {y y' : F.Site j} (h1 : x ∈ sitesBelow i y) (h2 : x ∈ sitesBelow i y') : y = y' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.eq_of_mem_sitesBelow_of_mem_sitesBelow <;> assumption
theorem cutPlaquettes_subset_of_subset {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutPlaquettes Z ⊆ cutPlaquettes Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutPlaquettes_mono <;> assumption
theorem cutBonds_subset_of_subset {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutBonds Z ⊆ cutBonds Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutBonds_mono <;> assumption
theorem cutBelow_subset_of_subset {m : ℕ} (i : ℕ) {Z Z' : Finset (F.Site m)} (h : Z ⊆ Z') :
    cutBelow i Z ⊆ cutBelow i Z' := Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem sitesBelow_subset_cutBelow {l : ℕ} (hl : l < m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    {X : Finset (F.Site m)} {w : F.Site (l + 1)} (hw : w ∈ cutBelow (l + 1) X) :
    sitesBelow l w ⊆ cutBelow l X := by
  intro z hz
  simp only [cutBelow, Finset.mem_biUnion] at hw ⊢
  obtain ⟨x0, hx0, hx⟩ := hw
  exact ⟨x0, hx0, sitesBelow_trans (by omega) hl hm hL x0 hx hz⟩
include hb in
theorem cutVarianceSum_le (hm : m ≤ F.top) (hL : Odd F.blockSide) (hA : IsAdmissibleAmbient F)
    (X : Finset (F.Site m)) (U : F.FieldChain) {l : ℕ} (hl : l < m) :
    cutVarianceSum X U l ≤ 128 * (F.blockSide : ℝ) ^ 2 * curvatureEnergy (cutBelow l X) (U l) := by
  classical
  have hl' : l < F.top := by omega
  have h1 : ∀ c ∈ cutBonds (cutBelow (l + 1) X), contourVariance (U l) c ≤
      16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect (U l) p ^ 2 :=
    fun c _ => hb.1 F l hl' hL hA (U l) c
  have h2 : ∑ c ∈ cutBonds (cutBelow (l + 1) X), ∑ p ∈ blockPairPlaquettes c, plaquetteDefect (U l) p ^ 2 ≤
      ((8 : ℕ) : ℝ) * curvatureEnergy (cutBelow l X) (U l) := by
    refine sum_sum_le_mul_of_multiplicity _ _ _ _ (fun q => sq_nonneg _) 8 ?_ ?_
    · intro c hc
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
      refine cutPlaquettes_subset_of_subset ?_
      exact Finset.union_subset (sitesBelow_subset_cutBelow hl hm hL hc.1)
        (sitesBelow_subset_cutBelow hl hm hL hc.2)
    · intro p _ _
      by_cases hne : ∃ c0 ∈ cutBonds (cutBelow (l + 1) X), p ∈ blockPairPlaquettes c0
      · obtain ⟨c0, _, hc0⟩ := hne
        have hmem : ∀ c, p ∈ blockPairPlaquettes c →
            p.1 ∈ sitesBelow l c.1 ∨ p.1 ∈ sitesBelow l (c.1 + unitStep (l + 1) c.2) := by
          intro c hc
          simp only [blockPairPlaquettes, cutPlaquettes, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, and_true] at hc
          exact Finset.mem_union.1 hc.1
        obtain ⟨y0, hy0⟩ : ∃ y0 : F.Site (l + 1), p.1 ∈ sitesBelow l y0 := by
          rcases hmem c0 hc0 with h | h
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
        have hsub : ((cutBonds (cutBelow (l + 1) X)).filter fun c => p ∈ blockPairPlaquettes c) ⊆
            (Finset.univ : Finset (Fin 4 × Bool)).image fun e =>
              if e.2 then ((y0, e.1) : F.Site (l + 1) × Fin 4) else (y0 - unitStep (l + 1) e.1, e.1) := by
          intro c hc
          have hc' := (Finset.mem_filter.1 hc).2
          refine Finset.mem_image.2 ?_
          rcases hmem c hc' with h | h
          · have := sitesBelow_unique (by omega) hl' hL h hy0
            exact ⟨(c.2, true), Finset.mem_univ _, by simp [← this]⟩
          · have := sitesBelow_unique (by omega) hl' hL h hy0
            refine ⟨(c.2, false), Finset.mem_univ _, ?_⟩
            simp [← this]
        refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
        simp
      · have : ((cutBonds (cutBelow (l + 1) X)).filter fun c => p ∈ blockPairPlaquettes c) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun c hc h => hne ⟨c, hc, h⟩
        rw [this]
        simp
  have hL2 : (0 : ℝ) ≤ 16 * (F.blockSide : ℝ) ^ 2 := by positivity
  calc cutVarianceSum X U l ≤ ∑ c ∈ cutBonds (cutBelow (l + 1) X),
        16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect (U l) p ^ 2 :=
        Finset.sum_le_sum h1
    _ = 16 * (F.blockSide : ℝ) ^ 2 * ∑ c ∈ cutBonds (cutBelow (l + 1) X),
        ∑ p ∈ blockPairPlaquettes c, plaquetteDefect (U l) p ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 16 * (F.blockSide : ℝ) ^ 2 * (((8 : ℕ) : ℝ) * curvatureEnergy (cutBelow l X) (U l)) :=
        mul_le_mul_of_nonneg_left h2 hL2
    _ = _ := by
        push_cast
        ring
theorem norm_sub_one_sq (z : UnitQuaternion) : ‖(z : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (z : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem plaquetteDefect_sq_eq (W : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteDefect W p ^ 2 = 2 * plaquetteEnergy W p := by
  unfold plaquetteDefect plaquetteEnergy
  rw [norm_sub_one_sq]
  ring
theorem plaquetteEnergy_nonneg (W : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy W p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem cutChainEnergy_bounds {a : ℝ} (ha : 1 ≤ a) (X : Finset (F.Site m)) (U : F.FieldChain) :
    curvatureEnergy (cutBelow 0 X) (U 0) ≤ 2 * cutChainEnergy a m X U ∧
      ∀ l < m, cutFitSum X U l ≤ cutChainEnergy a m X U := by
  have hf : ∀ i, 0 ≤ cutFitSum X U i := fun i => Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _
  have hs : 0 ≤ ∑ i ∈ Finset.range m, cutFitSum X U i := Finset.sum_nonneg fun i _ => hf i
  have he : 0 ≤ ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p :=
    Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ _
  have hT : cutChainEnergy a m X U = ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p +
      a * ∑ i ∈ Finset.range m, cutFitSum X U i := rfl
  constructor
  · have e : curvatureEnergy (cutBelow 0 X) (U 0) =
        2 * ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p := by
      unfold curvatureEnergy
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => plaquetteDefect_sq_eq _ _
    rw [e, hT]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a) hs]
  · intro l hl
    have h1 : cutFitSum X U l ≤ ∑ i ∈ Finset.range m, cutFitSum X U i :=
      Finset.single_le_sum (f := fun i => cutFitSum X U i) (fun i _ => hf i) (Finset.mem_range.2 hl)
    rw [hT]
    nlinarith
include hs hb in
theorem sqrt_curvatureEnergy_le_of_small {a : ℝ} (ha : 1 ≤ a) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (h4 : 4 ≤ F.blockSide) (X : Finset (F.Site m)) (U : F.FieldChain)
    {b : ℝ} (hbdef : b = 72 * Real.sqrt (cutChainEnergy a m X U))
    (hsmall : 65536 * (F.blockSide : ℝ) ^ 2 * b ≤ 1) :
    ∀ j ≤ m, Real.sqrt (curvatureEnergy (cutBelow j X) (U j)) ≤ 2 * b := by
  obtain ⟨h0, hfit⟩ := cutChainEnergy_bounds (m := m) ha X U
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  set P := Real.sqrt (cutChainEnergy a m X U) with hP
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hE0 : Real.sqrt (curvatureEnergy (cutBelow 0 X) (U 0)) ≤ 2 * P := by
    refine (Real.sqrt_le_sqrt h0).trans ?_
    have hT0 : 0 ≤ cutChainEnergy a m X U := by
      have := curvatureEnergy_nonneg (cutBelow 0 X) (U 0)
      linarith
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, hP, Real.sq_sqrt hT0]
    linarith
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    set Q := 128 * (F.blockSide : ℝ) ^ 2 * (2 * b) ^ 2 with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have h1 := sqrt_curvatureEnergy_le hs hb hj hm hL hA h4 X U hP0 hQ0
      (fun l hl => Real.sqrt_le_sqrt (hfit l (by omega)))
      (fun l hl => by
        refine (cutVarianceSum_le hb hm hL hA X U (by omega)).trans ?_
        have h2 := ih l hl (by omega)
        have h3 : curvatureEnergy (cutBelow l X) (U l) ≤ (2 * b) ^ 2 :=
          (Real.sqrt_le_left (by positivity)).1 h2
        exact mul_le_mul_of_nonneg_left h3 (by positivity))
    refine h1.trans ?_
    have h5 : 128 * Q ≤ b := by
      have : 128 * Q = (65536 * (F.blockSide : ℝ) ^ 2 * b) * b := by
        rw [hQ]
        ring
      rw [this]
      nlinarith
    linarith
include hs hb in
theorem plaquette_coercive {a : ℝ} (ha : 1 ≤ a) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (h4 : 4 ≤ F.blockSide) (p : F.Site m × Fin 4 × Fin 4)
    (hp : p.2.1 < p.2.2) (U : F.FieldChain) :
    (1 / 4718592 ^ 2 : ℝ) * min (plaquetteDefect (U m) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
      cutChainEnergy a m (plaquetteCorners p) U := by
  obtain ⟨h0, -⟩ := cutChainEnergy_bounds (m := m) ha (plaquetteCorners p) U
  have hT0 : 0 ≤ cutChainEnergy a m (plaquetteCorners p) U := by
    have := curvatureEnergy_nonneg (cutBelow 0 (plaquetteCorners p)) (U 0)
    linarith
  set A := cutChainEnergy a m (plaquetteCorners p) U with hAdef
  set b := 72 * Real.sqrt A with hb'
  have hmin := min_le_left (plaquetteDefect (U m) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ))
  have hmin2 := min_le_right (plaquetteDefect (U m) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ))
  have hpm : p ∈ cutPlaquettes (cutBelow m (plaquetteCorners p)) := by
    have hsub : plaquetteCorners p ⊆ cutBelow m (plaquetteCorners p) := by
      intro y hy
      simp only [cutBelow, Finset.mem_biUnion]
      exact ⟨y, hy, self_mem_sitesBelow hL y⟩
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨hsub ?_, hp, hsub⟩
    simp [plaquetteCorners]
  have hcE : plaquetteDefect (U m) p ^ 2 ≤ curvatureEnergy (cutBelow m (plaquetteCorners p)) (U m) :=
    Finset.single_le_sum (f := fun q => plaquetteDefect (U m) q ^ 2) (fun _ _ => sq_nonneg _) hpm
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hT0
  by_cases hsmall : 65536 * (F.blockSide : ℝ) ^ 2 * b ≤ 1
  · have h1 := sqrt_curvatureEnergy_le_of_small hs hb ha hm hL hA h4 (plaquetteCorners p) U hb'
      hsmall m le_rfl
    have h2 : curvatureEnergy (cutBelow m (plaquetteCorners p)) (U m) ≤ (2 * b) ^ 2 :=
      (Real.sqrt_le_left (by positivity)).1 h1
    have h3 : (2 * b) ^ 2 = 20736 * A := by
      rw [hb', mul_pow, mul_pow, hsA]
      ring
    have h4' : (1 / 4718592 ^ 2 : ℝ) * min (plaquetteDefect (U m) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
        (1 / 4718592 ^ 2 : ℝ) * (20736 * A) :=
      mul_le_mul_of_nonneg_left (hmin.trans (hcE.trans (h2.trans h3.le))) (by positivity)
    refine h4'.trans ?_
    nlinarith
  · rw [not_le] at hsmall
    have hK2 : (1 : ℝ) < (4718592 * (F.blockSide : ℝ) ^ 2 * Real.sqrt A) ^ 2 := by nlinarith
    have hK3 : (4718592 * (F.blockSide : ℝ) ^ 2 * Real.sqrt A) ^ 2 =
        4718592 ^ 2 * (F.blockSide : ℝ) ^ 4 * A := by
      rw [mul_pow, mul_pow, hsA]
      ring
    rw [hK3] at hK2
    have e : (F.blockSide : ℝ) ^ (-4 : ℤ) = ((F.blockSide : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [e] at hmin2
    have h5 : (1 / 4718592 ^ 2 : ℝ) * min (plaquetteDefect (U m) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
        (1 / 4718592 ^ 2 : ℝ) * ((F.blockSide : ℝ) ^ 4)⁻¹ := by
      rw [e]
      exact mul_le_mul_of_nonneg_left hmin2 (by positivity)
    refine h5.trans ?_
    have h6 : (1 / 4718592 ^ 2 : ℝ) * ((F.blockSide : ℝ) ^ 4)⁻¹ =
        1 / (4718592 ^ 2 * (F.blockSide : ℝ) ^ 4) := by
      field_simp
    rw [h6, div_le_iff₀ (by positivity)]
    nlinarith
theorem card_filter_mem_corners_le {i : ℕ} (hi : i ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site i) (Ps : Finset (F.Site m × Fin 4 × Fin 4))
    [DecidablePred fun p : F.Site m × Fin 4 × Fin 4 => x ∈ cutBelow i (plaquetteCorners p)] :
    (Ps.filter fun p => x ∈ cutBelow i (plaquetteCorners p)).card ≤ 64 := by
  classical
  by_cases hne : ∃ p0 ∈ Ps, x ∈ cutBelow i (plaquetteCorners p0)
  · obtain ⟨p0, _, h0⟩ := hne
    simp only [cutBelow, Finset.mem_biUnion] at h0
    obtain ⟨y0, _, hy0⟩ := h0
    have hsub : (Ps.filter fun p => x ∈ cutBelow i (plaquetteCorners p)) ⊆
        (Finset.univ : Finset (Fin 4 × Fin 4 × Bool × Bool)).image fun e =>
          ((y0 - (if e.2.2.1 then unitStep m e.1 else 0) - (if e.2.2.2 then unitStep m e.2.1 else 0),
            e.1, e.2.1) : F.Site m × Fin 4 × Fin 4) := by
      rintro ⟨b, μ, ν⟩ hp
      have hp' := (Finset.mem_filter.1 hp).2
      simp only [cutBelow, Finset.mem_biUnion] at hp'
      obtain ⟨y, hy, hxy⟩ := hp'
      have hyy := sitesBelow_unique hi hm hL hxy hy0
      subst hyy
      simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
      refine Finset.mem_image.2 ?_
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨(μ, ν, false, false), Finset.mem_univ _, by simp⟩
      · exact ⟨(μ, ν, true, false), Finset.mem_univ _, by simp⟩
      · exact ⟨(μ, ν, false, true), Finset.mem_univ _, by simp⟩
      · exact ⟨(μ, ν, true, true), Finset.mem_univ _, by
          simp only [if_true, Prod.mk.injEq, and_true]
          abel⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    simp
  · have : (Ps.filter fun p => x ∈ cutBelow i (plaquetteCorners p)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun p hp h => hne ⟨p, hp, h⟩
    rw [this]
    simp
theorem sum_cutChainEnergy_corners_le {a : ℝ} (ha : 0 ≤ a) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (Xc : Finset (F.Site m)) (U : F.FieldChain) :
    ∑ p ∈ cutPlaquettes Xc, cutChainEnergy a m (plaquetteCorners p) U ≤ 64 * cutChainEnergy a m Xc U := by
  classical
  have hc : ∀ p ∈ cutPlaquettes Xc, plaquetteCorners p ⊆ Xc := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2.2
  have h0 : ∑ p ∈ cutPlaquettes Xc, ∑ q ∈ cutPlaquettes (cutBelow 0 (plaquetteCorners p)),
      plaquetteEnergy (U 0) q ≤
      ((64 : ℕ) : ℝ) * ∑ q ∈ cutPlaquettes (cutBelow 0 Xc), plaquetteEnergy (U 0) q := by
    refine sum_sum_le_mul_of_multiplicity _ _ _ _ (fun q => plaquetteEnergy_nonneg _ _) 64 ?_ ?_
    · intro p hp
      exact cutPlaquettes_subset_of_subset (cutBelow_subset_of_subset 0 (hc p hp))
    · intro q _ _
      refine le_trans (Finset.card_le_card ?_)
        (card_filter_mem_corners_le (Nat.zero_le m) hm hL q.1 (cutPlaquettes Xc))
      intro p hp
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨hp'.1, ?_⟩
      have := hp'.2
      simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
      exact this.1
  have h1 : ∀ i ∈ Finset.range m, ∑ p ∈ cutPlaquettes Xc,
      ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)), blockFit (U i) (U (i + 1)) c ≤
      ((64 : ℕ) : ℝ) * ∑ c ∈ cutBonds (cutBelow (i + 1) Xc), blockFit (U i) (U (i + 1)) c := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    refine sum_sum_le_mul_of_multiplicity _ _ _ _ (fun q => blockFit_nonneg _ _ _) 64 ?_ ?_
    · intro p hp
      exact cutBonds_subset_of_subset (cutBelow_subset_of_subset (i + 1) (hc p hp))
    · intro c _ _
      refine le_trans (Finset.card_le_card ?_)
        (card_filter_mem_corners_le hi' hm hL c.1 (cutPlaquettes Xc))
      intro p hp
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨hp'.1, ?_⟩
      have := hp'.2
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
      exact this.1
  have e : ∑ p ∈ cutPlaquettes Xc, cutChainEnergy a m (plaquetteCorners p) U =
      ∑ p ∈ cutPlaquettes Xc, ∑ q ∈ cutPlaquettes (cutBelow 0 (plaquetteCorners p)),
        plaquetteEnergy (U 0) q +
      a * ∑ i ∈ Finset.range m, ∑ p ∈ cutPlaquettes Xc,
        ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)), blockFit (U i) (U (i + 1)) c := by
    unfold cutChainEnergy
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (s := cutPlaquettes Xc)]
  rw [e]
  have h2 := Finset.sum_le_sum h1
  rw [← Finset.mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 ha
  unfold cutChainEnergy
  push_cast at h0 h3 ⊢
  nlinarith
end chain
end CoercivityProof
theorem CoercivityProof.chainCoercivity_holds (hs : SquareDescentEstimate)
    (hb : ContourVarianceCurvatureBound) : ChainCoercivity := by
  refine ⟨1 / 4718592 ^ 2 / 64, by positivity, by norm_num, 4, ?_⟩
  intro a L ha hodd hL4 F hFL hA j hj
  subst hFL
  have hone := fun (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) (U : F.FieldChain) =>
    CoercivityProof.plaquette_coercive hs hb ha hj hodd hA hL4 p hp U
  constructor
  · intro p U hp
    have h1 := hone p hp U
    have h0 : 0 ≤ min (plaquetteDefect (U j) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) :=
      le_min (sq_nonneg _) (by positivity)
    refine le_trans ?_ h1
    have : (1 / 4718592 ^ 2 / 64 : ℝ) ≤ 1 / 4718592 ^ 2 := by norm_num
    exact mul_le_mul_of_nonneg_right this h0
  · intro X V
    haveI : Nonempty {U : F.FieldChain // U j = V} :=
      ⟨⟨Function.update (fun i _ _ => (1 : UnitQuaternion)) j V, by simp⟩⟩
    refine le_ciInf ?_
    rintro ⟨U, rfl⟩
    have h1 : ∑ p ∈ cutPlaquettes X, (1 / 4718592 ^ 2 : ℝ) *
        min (plaquetteDefect (U j) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
        ∑ p ∈ cutPlaquettes X, cutChainEnergy a j (plaquetteCorners p) U :=
      Finset.sum_le_sum fun p hp => hone p (Finset.mem_filter.1 hp).2.1 U
    have h2 := CoercivityProof.sum_cutChainEnergy_corners_le (by linarith : (0 : ℝ) ≤ a) hj hodd X U
    rw [← Finset.mul_sum] at h1
    show (1 / 4718592 ^ 2 / 64 : ℝ) * _ ≤ cutChainEnergy a j X U
    have := h1.trans h2
    linarith
end YangMills.Construction
end
