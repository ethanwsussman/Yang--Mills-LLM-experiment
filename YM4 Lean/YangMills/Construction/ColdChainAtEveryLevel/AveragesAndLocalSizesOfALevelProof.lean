import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def averagesAndLocalSizesStatement : Prop :=
  ∀ (F : BlockFrame) (D : Finset F.Cell) (j : ℕ) (f : F.Site j → Fin 4 → ℝ), Odd F.blockSide → j + 1 ≤ F.top → (∀ x i, 0 ≤ f x i) →
    (∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ r, r < F.blockSide →
      (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds D j) ∧
    (∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 4 ≤ ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4) ∧
    (∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 2 ≤ (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 2) ∧
    ∃ T : F.Site (j + 1) → ℝ, (∀ y, 0 ≤ T y) ∧ (∀ c ∈ innerBonds D (j + 1), BoundedOnAdjacentBlocks f c (T c.1)) ∧
      (∀ y ∈ sitesOfCells D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ k, h + Pi.single k 1 ∈ centredCube F.blockSide →
        f (refineSite y + siteOfCoords j h) k ≤ T y) ∧
      (∀ y, T y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4) ∧
      (∑ c ∈ innerBonds D (j + 1), T c.1 ^ 4 ≤ 16 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4) ∧
      ∑ y ∈ sitesOfCells D (j + 1), T y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4
end BlockAverages
end YangMills.Construction
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace LocalQuarticNorms
open LatticeFractionalIntegration
variable {F : BlockFrame}
theorem siteOfCoords_zsmul (j : ℕ) (r : ℤ) (a : Lattice4) :
    siteOfCoords (F := F) j (r • a) = r • siteOfCoords j a := by
  funext i
  simp [siteOfCoords]
theorem refineSite_cellCentre (j : ℕ) (hj : j + 1 ≤ F.top) (z : F.Cell) :
    refineSite (cellCentre (j + 1) z) = cellCentre j z := by
  funext i
  have h := intCast_mul_eq_of_eq (period_eq_succ_mul j hj i)
    (siteCoords_cast (F := F) (j := j + 1) (fun i => (F.blockSide : ℤ) ^ (F.top - (j + 1)) * siteCoords z i) i)
  have e : F.top - j = (F.top - (j + 1)) + 1 := by omega
  simp only [refineSite, cellCentre, siteOfCoords] at h ⊢
  rw [h, e, pow_succ]
  congr 1
  ring
theorem mul_add_mem_centredCube {L M : ℕ} (hL : Odd L) (hM : Odd M) {g h : Lattice4}
    (hg : g ∈ centredCube M) (hh : h ∈ centredCube L) :
    (fun i => (L : ℤ) * g i + h i) ∈ centredCube (L * M) := by
  obtain ⟨v, rfl⟩ := hL
  obtain ⟨u, rfl⟩ := hM
  rw [LatticePaths.mem_centredCube_iff]
  intro i
  have h1 := (LatticePaths.mem_centredCube_iff _ g).1 hg i
  have h2 := (LatticePaths.mem_centredCube_iff _ h).1 hh i
  have ku : (((2 * u + 1 : ℕ) : ℤ) - 1) / 2 = u := by omega
  have kv : (((2 * v + 1 : ℕ) : ℤ) - 1) / 2 = v := by omega
  have kw : ((((2 * v + 1) * (2 * u + 1) : ℕ) : ℤ) - 1) / 2 = (2 * v + 1) * u + v := by
    push_cast
    have : ((2 * (v : ℤ) + 1) * (2 * u + 1) - 1) = 2 * ((2 * v + 1) * u + v) := by ring
    rw [this]
    omega
  rw [ku] at h1
  rw [kv] at h2
  rw [kw]
  have hp : (0 : ℤ) ≤ 2 * (v : ℤ) + 1 := by positivity
  have a1 := mul_le_mul_of_nonneg_left h1.2 hp
  have a2 := mul_le_mul_of_nonneg_left h1.1 hp
  push_cast
  constructor <;> nlinarith [h2.1, h2.2]
variable {D : Finset F.Cell}
theorem refineSite_add_mem_sitesOfCells (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells D (j + 1))
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) : refineSite y + siteOfCoords j h ∈ sitesOfCells D j := by
  obtain ⟨z, hz, g, hg, rfl⟩ := mem_sitesOfCells.1 hy
  rw [refineSite_add j hj, refineSite_cellCentre j hj]
  refine mem_sitesOfCells.2 ⟨z, hz, fun i => (F.blockSide : ℤ) * g i + h i, ?_, ?_⟩
  · have e : F.blockSide ^ (F.top - j) = F.blockSide * F.blockSide ^ (F.top - (j + 1)) := by
      have : F.top - j = (F.top - (j + 1)) + 1 := by omega
      rw [this, pow_succ, mul_comm]
    rw [e]
    exact mul_add_mem_centredCube hL (hL.pow) hg hh
  · rw [add_assoc, ← siteOfCoords_add]
    rfl
def blockPoint {j : ℕ} (c : F.Site (j + 1) × Fin 4) (a : Lattice4) : F.Site j :=
  refineSite c.1 + siteOfCoords j a
theorem blockPoint_mem_sitesOfCells (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) {a : Lattice4}
    (ha : a ∈ centredCube F.blockSide ∨ a - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) :
    blockPoint c a ∈ sitesOfCells D j := by
  have hc1 : c.1 ∈ sitesOfCells D (j + 1) := (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  have hc2 : c.1 + unitStep (j + 1) c.2 ∈ sitesOfCells D (j + 1) := (Finset.mem_filter.1 hc).2
  rcases ha with ha | ha
  · exact refineSite_add_mem_sitesOfCells hL hj hc1 ha
  · have := refineSite_add_mem_sitesOfCells hL hj hc2 ha
    rw [unitStep_eq, refineSite_add j hj, add_assoc, ← siteOfCoords_add] at this
    have e : (fun i => (F.blockSide : ℤ) * basisVector c.2 i) + (a - (F.blockSide : ℤ) • basisVector c.2) = a := by
      funext i
      simp
    rwa [e] at this
theorem add_smul_basisVector_mem_or {L : ℕ} (hL : Odd L) {h : Lattice4} (hh : h ∈ centredCube L)
    (i : Fin 4) {r : ℕ} (hr : r ≤ L) :
    h + (r : ℤ) • basisVector i ∈ centredCube L ∨
      (h + (r : ℤ) • basisVector i) - (L : ℤ) • basisVector i ∈ centredCube L := by
  obtain ⟨v, rfl⟩ := hL
  have kv : (((2 * v + 1 : ℕ) : ℤ) - 1) / 2 = v := by omega
  have hb := (LatticePaths.mem_centredCube_iff _ h).1 hh
  rw [kv] at hb
  by_cases hcase : h i + r ≤ v
  · left
    rw [LatticePaths.mem_centredCube_iff, kv]
    intro μ
    by_cases hμ : μ = i
    · subst hμ
      have := hb μ
      simp [basisVector]
      omega
    · have := hb μ
      simp [basisVector, hμ]
      omega
  · right
    rw [LatticePaths.mem_centredCube_iff, kv]
    intro μ
    by_cases hμ : μ = i
    · subst hμ
      have := hb μ
      simp [basisVector]
      omega
    · have := hb μ
      simp [basisVector, hμ]
      omega
theorem blockPoint_add_unitStep {j : ℕ} (c : F.Site (j + 1) × Fin 4) (a : Lattice4) (k : Fin 4) :
    blockPoint c a + unitStep j k = blockPoint c (a + basisVector k) := by
  simp only [blockPoint, unitStep_eq, siteOfCoords_add, add_assoc]
theorem refineSite_add_smul_unitStep {j : ℕ} (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (r : ℕ) :
    refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 = blockPoint c (h + (r : ℤ) • basisVector c.2) := by
  simp only [blockPoint, unitStep_eq, siteOfCoords_add, siteOfCoords_zsmul, add_assoc]
theorem line_mem_innerBonds (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1))
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) {r : ℕ} (hr : r < F.blockSide) :
    (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds D j := by
  rw [refineSite_add_smul_unitStep]
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨blockPoint_mem_sitesOfCells hL hj hc
    (add_smul_basisVector_mem_or hL hh c.2 hr.le), Finset.mem_univ _⟩, ?_⟩
  show blockPoint c _ + unitStep j c.2 ∈ sitesOfCells D j
  rw [blockPoint_add_unitStep]
  have e : h + (r : ℤ) • basisVector c.2 + basisVector c.2 = h + ((r + 1 : ℕ) : ℤ) • basisVector c.2 := by
    funext i
    simp
    ring
  rw [e]
  exact blockPoint_mem_sitesOfCells hL hj hc (add_smul_basisVector_mem_or hL hh c.2 hr)
theorem refineSite_add_injective (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {y y' : F.Site (j + 1)}
    {h h' : Lattice4} (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : refineSite y + siteOfCoords j h = refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by
  have key : ∀ i, y i = y' i ∧ h i = h' i := by
    intro i
    have ei := congrFun e i
    simp only [refineSite, siteOfCoords, Pi.add_apply] at ei
    rw [← Int.cast_add, ← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub, period_eq_succ_mul j hj i] at ei
    obtain ⟨w, hw⟩ := ei
    set P : ℤ := ((F.period (j + 1) i : ℕ) : ℤ)
    have hdvd : (F.blockSide : ℤ) ∣ h' i - h i := by
      refine ⟨P * w - (siteCoords y' i - siteCoords y i), ?_⟩
      linear_combination hw
    have hbi := (LatticePaths.mem_centredCube_iff _ h).1 hh i
    have hbi' := (LatticePaths.mem_centredCube_iff _ h').1 hh' i
    obtain ⟨v, hv⟩ := hL
    have kv : ((F.blockSide : ℤ) - 1) / 2 = v := by rw [hv]; push_cast; omega
    rw [kv] at hbi hbi'
    have hLz : (F.blockSide : ℤ) = 2 * v + 1 := by rw [hv]; push_cast; ring
    have heq : h' i - h i = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hdvd
      rw [abs_lt]
      constructor <;> omega
    have hhi : h i = h' i := by omega
    refine ⟨?_, hhi⟩
    have hmul : (F.blockSide : ℤ) * (siteCoords y' i - siteCoords y i) = (F.blockSide : ℤ) * (P * w) := by
      linear_combination hw - heq
    have hL0 : (F.blockSide : ℤ) ≠ 0 := by rw [hLz]; omega
    have hc : siteCoords y' i - siteCoords y i = P * w := mul_left_cancel₀ hL0 hmul
    have : ((siteCoords y i : ℤ) : ZMod (F.period (j + 1) i)) =
        ((siteCoords y' i : ℤ) : ZMod (F.period (j + 1) i)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨w, hc⟩
    have t1 := congrFun (siteOfCoords_siteCoords y) i
    have t2 := congrFun (siteOfCoords_siteCoords y') i
    simp only [siteOfCoords] at t1 t2
    rw [← t1, ← t2]
    exact this
  exact ⟨funext fun i => (key i).1, funext fun i => (key i).2⟩
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] {P : Finset α} {Ω : Finset β} {φ : β → ℝ}
    {Φ : α → β} (hφ : ∀ b, 0 ≤ φ b) (hmap : ∀ p ∈ P, Φ p ∈ Ω) (hinj : Set.InjOn Φ P) :
    ∑ p ∈ P, φ (Φ p) ≤ ∑ b ∈ Ω, φ b := by
  rw [← Finset.sum_image (f := φ) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hφ _)
  intro b hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
  exact hmap p hp
open Classical in
theorem sum_line_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {φ : F.Site j × Fin 4 → ℝ}
    (hφ : ∀ b, 0 ≤ φ b) {r : ℕ} (hr : r < F.blockSide) :
    ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide,
        φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ≤
      ∑ b ∈ innerBonds D j, φ b := by
  rw [← Finset.sum_product']
  refine sum_comp_le_of_injOn (Φ := fun p : (F.Site (j + 1) × Fin 4) × Lattice4 =>
    (refineSite p.1.1 + siteOfCoords j p.2 + (r : ℤ) • unitStep j p.1.2, p.1.2)) hφ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact line_mem_innerBonds hL hj h1 h2 hr
  · intro p hp q hq e
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    obtain ⟨q1, q2⟩ := Finset.mem_product.1 hq
    have e2 : p.1.2 = q.1.2 := congrArg (fun b : F.Site j × Fin 4 => b.2) e
    have e1 : refineSite p.1.1 + siteOfCoords j p.2 + (r : ℤ) • unitStep j p.1.2 =
        refineSite q.1.1 + siteOfCoords j q.2 + (r : ℤ) • unitStep j q.1.2 :=
      congrArg (fun b : F.Site j × Fin 4 => b.1) e
    rw [e2] at e1
    have e3 := add_right_cancel e1
    obtain ⟨a1, a2⟩ := refineSite_add_injective hL hj p2 q2 e3
    exact Prod.ext (Prod.ext a1 e2) a2
open Classical in
theorem sum_lines_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {φ : F.Site j × Fin 4 → ℝ}
    (hφ : ∀ b, 0 ≤ φ b) :
    ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ≤
      (F.blockSide : ℝ) * ∑ b ∈ innerBonds D j, φ b := by
  calc ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2)
      = ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide,
        φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) := by
        have e1 : ∀ c : F.Site (j + 1) × Fin 4, ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) =
            ∑ r ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
            φ (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) := fun c => Finset.sum_comm
        simp only [e1]
        exact Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.range F.blockSide, ∑ b ∈ innerBonds D j, φ b :=
        Finset.sum_le_sum fun r hr => sum_line_le hL hj hφ (Finset.mem_range.1 hr)
    _ = (F.blockSide : ℝ) * ∑ b ∈ innerBonds D j, φ b := by simp
theorem card_centredCube_product_range (hL : Odd F.blockSide) :
    ((centredCube F.blockSide ×ˢ Finset.range F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 5 := by
  rw [Finset.card_product, LatticePaths.card_centredCube hL, Finset.card_range]
  push_cast
  ring
theorem lineBlockAverage_pow_four_le (hL : Odd F.blockSide) {j : ℕ} {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) (c : F.Site (j + 1) × Fin 4) :
    lineBlockAverage f c ^ 4 ≤ (1 / (F.blockSide : ℝ)) * ∑ h ∈ centredCube F.blockSide,
      ∑ r ∈ Finset.range F.blockSide, f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 4 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold lineBlockAverage
  rw [← Finset.sum_product', ← Finset.sum_product']
  set I := centredCube F.blockSide ×ˢ Finset.range F.blockSide
  set g : Lattice4 × ℕ → ℝ := fun p => f (refineSite c.1 + siteOfCoords j p.1 + (p.2 : ℤ) • unitStep j c.2) c.2
    with hg
  have h1 := pow_sum_div_card_le_sum_pow (s := I) (f := g) (fun _ _ => hf _ _) 3
  have hc : ((I.card : ℕ) : ℝ) = (F.blockSide : ℝ) ^ 5 := card_centredCube_product_range hL
  rw [hc] at h1
  have e : (1 / (F.blockSide : ℝ) ^ 4 * ∑ p ∈ I, g p) ^ 4 =
      (1 / (F.blockSide : ℝ)) * ((∑ p ∈ I, g p) ^ (3 + 1) / ((F.blockSide : ℝ) ^ 5) ^ 3) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
theorem lineBlockAverage_sq_le (hL : Odd F.blockSide) {j : ℕ} {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) (c : F.Site (j + 1) × Fin 4) :
    lineBlockAverage f c ^ 2 ≤ (1 / (F.blockSide : ℝ) ^ 3) * ∑ h ∈ centredCube F.blockSide,
      ∑ r ∈ Finset.range F.blockSide, f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 2 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold lineBlockAverage
  rw [← Finset.sum_product', ← Finset.sum_product']
  set I := centredCube F.blockSide ×ˢ Finset.range F.blockSide
  set g : Lattice4 × ℕ → ℝ := fun p => f (refineSite c.1 + siteOfCoords j p.1 + (p.2 : ℤ) • unitStep j c.2) c.2
    with hg
  have h1 := pow_sum_div_card_le_sum_pow (s := I) (f := g) (fun _ _ => hf _ _) 1
  have hc : ((I.card : ℕ) : ℝ) = (F.blockSide : ℝ) ^ 5 := card_centredCube_product_range hL
  rw [hc] at h1
  have e : (1 / (F.blockSide : ℝ) ^ 4 * ∑ p ∈ I, g p) ^ 2 =
      (1 / (F.blockSide : ℝ) ^ 3) * ((∑ p ∈ I, g p) ^ (1 + 1) / ((F.blockSide : ℝ) ^ 5) ^ 1) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
theorem sum_lineBlockAverage_pow_four_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) :
    ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 4 ≤ ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have h1 := sum_lines_le (D := D) hL hj (φ := fun b => f b.1 b.2 ^ 4)
    (fun b => by have := hf b.1 b.2; positivity)
  calc ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 4
      ≤ ∑ c ∈ innerBonds D (j + 1), (1 / (F.blockSide : ℝ)) * ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide,
          f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 4 :=
        Finset.sum_le_sum fun c _ => lineBlockAverage_pow_four_le hL hf c
    _ = (1 / (F.blockSide : ℝ)) * ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide,
          f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (1 / (F.blockSide : ℝ)) * ((F.blockSide : ℝ) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4 := by field_simp
theorem sum_lineBlockAverage_sq_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) :
    ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 2 ≤
      (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 2 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have h1 := sum_lines_le (D := D) hL hj (φ := fun b => f b.1 b.2 ^ 2)
    (fun b => by have := hf b.1 b.2; positivity)
  calc ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 2
      ≤ ∑ c ∈ innerBonds D (j + 1), (1 / (F.blockSide : ℝ) ^ 3) * ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide,
          f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 2 :=
        Finset.sum_le_sum fun c _ => lineBlockAverage_sq_le hL hf c
    _ = (1 / (F.blockSide : ℝ) ^ 3) * ∑ c ∈ innerBonds D (j + 1), ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide,
          f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / (F.blockSide : ℝ) ^ 3) * ((F.blockSide : ℝ) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 2 := by field_simp
section Norms
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by
  have e : Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
  rw [e, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]
theorem le_sqrt_sqrt_of_pow_four_le {a x : ℝ} (ha : 0 ≤ a) (h : a ^ 4 ≤ x) : a ≤ Real.sqrt (Real.sqrt x) := by
  have hx : 0 ≤ x := le_trans (by positivity) h
  have hs := sqrt_sqrt_pow_four hx
  have hn : 0 ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_nonneg _
  rw [← hs] at h
  exact le_of_pow_le_pow_left₀ (by norm_num) hn h
end Norms
section Main
def localQuarticSum {j : ℕ} (D : Finset F.Cell) (a : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ := by
  classical exact ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4,
    if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0
def localQuarticNorm {j : ℕ} (D : Finset F.Cell) (a : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  Real.sqrt (Real.sqrt (localQuarticSum D a c))
theorem localQuarticSum_nonneg {j : ℕ} {a : F.Site j → Fin 4 → ℝ} (c : F.Site (j + 1) × Fin 4) :
    0 ≤ localQuarticSum D a c := by
  classical
  unfold localQuarticSum
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs
  · positivity
  · exact le_rfl
theorem localQuarticNorm_nonneg {j : ℕ} {a : F.Site j → Fin 4 → ℝ} (c : F.Site (j + 1) × Fin 4) :
    0 ≤ localQuarticNorm D a c := Real.sqrt_nonneg _
theorem localQuarticNorm_pow_four {j : ℕ} {a : F.Site j → Fin 4 → ℝ} (c : F.Site (j + 1) × Fin 4) :
    localQuarticNorm D a c ^ 4 = localQuarticSum D a c := sqrt_sqrt_pow_four (localQuarticSum_nonneg c)
theorem le_localQuarticNorm {j : ℕ} {a : F.Site j → Fin 4 → ℝ} (ha : ∀ x i, 0 ≤ a x i)
    {c : F.Site (j + 1) × Fin 4} {x : Lattice4} (hx : x ∈ centredCube (3 * F.blockSide)) {k : Fin 4}
    (hb : (blockPoint c x, k) ∈ innerBonds D j) : a (blockPoint c x) k ≤ localQuarticNorm D a c := by
  classical
  refine le_sqrt_sqrt_of_pow_four_le (ha _ _) ?_
  unfold localQuarticSum
  have t : ∀ (x' : Lattice4) (k' : Fin 4),
      0 ≤ if (blockPoint c x', k') ∈ innerBonds D j then a (blockPoint c x') k' ^ 4 else 0 := by
    intro x' k'
    split_ifs
    · positivity
    · exact le_rfl
  have h1 : (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0) ≤
      ∑ k' : Fin 4, if (blockPoint c x, k') ∈ innerBonds D j then a (blockPoint c x) k' ^ 4 else 0 :=
    Finset.single_le_sum
      (f := fun k' => if (blockPoint c x, k') ∈ innerBonds D j then a (blockPoint c x) k' ^ 4 else 0)
      (fun k' _ => t x k') (Finset.mem_univ k)
  have h2 := Finset.single_le_sum (f := fun x' => ∑ k' : Fin 4,
      if (blockPoint c x', k') ∈ innerBonds D j then a (blockPoint c x') k' ^ 4 else 0)
      (fun x' _ => Finset.sum_nonneg fun k' _ => t x' k') hx
  rw [if_pos hb] at h1
  exact h1.trans h2
theorem mem_centredCube_three_mul {L : ℕ} (hL : Odd L) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ centredCube L ∨ a - (L : ℤ) • basisVector i ∈ centredCube L) : a ∈ centredCube (3 * L) := by
  obtain ⟨v, rfl⟩ := hL
  have kv : (((2 * v + 1 : ℕ) : ℤ) - 1) / 2 = v := by omega
  have kw : (((3 * (2 * v + 1) : ℕ) : ℤ) - 1) / 2 = 3 * v + 1 := by push_cast; omega
  rw [LatticePaths.mem_centredCube_iff, kw]
  intro μ
  rcases ha with ha | ha
  · have := (LatticePaths.mem_centredCube_iff _ a).1 ha μ
    rw [kv] at this
    omega
  · have := (LatticePaths.mem_centredCube_iff _ _).1 ha μ
    rw [kv] at this
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector] at this
      omega
    · simp [basisVector, hμ] at this
      omega
theorem boundedOnAdjacentBlocks_localQuarticNorm (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {a : F.Site j → Fin 4 → ℝ} (ha : ∀ x i, 0 ≤ a x i) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds D (j + 1)) :
    BoundedOnAdjacentBlocks a c (localQuarticNorm D a c) := by
  have bond_of : ∀ {x : Lattice4} {k : Fin 4},
      (x ∈ centredCube F.blockSide ∨ x - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) →
      (x + basisVector k ∈ centredCube F.blockSide ∨
        x + basisVector k - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) →
      (blockPoint c x, k) ∈ innerBonds D j := by
    intro x k h1 h2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨blockPoint_mem_sitesOfCells hL hj hc h1, Finset.mem_univ _⟩, ?_⟩
    show blockPoint c x + unitStep j k ∈ sitesOfCells D j
    rw [blockPoint_add_unitStep]
    exact blockPoint_mem_sitesOfCells hL hj hc h2
  refine ⟨fun h hh k hk => ⟨?_, ?_⟩, fun h hh r hr => ?_⟩
  · have e1 : (h ∈ centredCube F.blockSide ∨ h - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) :=
      Or.inl hh
    exact le_localQuarticNorm ha (mem_centredCube_three_mul hL e1) (bond_of e1 (Or.inl hk))
  · have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
        blockPoint c (h + (F.blockSide : ℤ) • basisVector c.2) := by
      rw [unitStep_eq, refineSite_add j hj]
      simp only [blockPoint, add_assoc, ← siteOfCoords_add]
      congr 2
      funext i
      simp [add_comm]
    have e1 : (h + (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide ∨
        (h + (F.blockSide : ℤ) • basisVector c.2) - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) :=
      Or.inr (by simpa using hh)
    have e2 : (h + (F.blockSide : ℤ) • basisVector c.2 + basisVector k ∈ centredCube F.blockSide ∨
        (h + (F.blockSide : ℤ) • basisVector c.2 + basisVector k) - (F.blockSide : ℤ) • basisVector c.2 ∈
          centredCube F.blockSide) := by
      right
      have : h + (F.blockSide : ℤ) • basisVector c.2 + basisVector k - (F.blockSide : ℤ) • basisVector c.2 =
          h + basisVector k := by abel
      rw [this]
      exact hk
    rw [e]
    exact le_localQuarticNorm ha (mem_centredCube_three_mul hL e1) (bond_of e1 e2)
  · have hr' := Finset.mem_range.1 hr
    have hb := line_mem_innerBonds hL hj hc hh hr'
    rw [refineSite_add_smul_unitStep] at hb ⊢
    exact le_localQuarticNorm ha (mem_centredCube_three_mul hL (add_smul_basisVector_mem_or hL hh c.2 hr'.le)) hb
theorem card_centredCube_three_mul (hL : Odd F.blockSide) :
    ((centredCube (3 * F.blockSide)).card : ℝ) = (3 * (F.blockSide : ℝ)) ^ 4 := by
  have : Odd (3 * F.blockSide) := Odd.mul (by decide) hL
  rw [LatticePaths.card_centredCube this]
  push_cast
  ring
theorem sum_localQuarticSum_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {a : F.Site j → Fin 4 → ℝ}
    (ha : ∀ x i, 0 ≤ a x i) :
    ∑ c ∈ innerBonds D (j + 1), localQuarticSum D a c ≤
      16 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 := by
  classical
  set S := ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => by have := ha b.1 b.2; positivity
  have one : ∀ (x : Lattice4) (k i : Fin 4), ∑ c ∈ (innerBonds D (j + 1)).filter (fun c => c.2 = i),
      (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0) ≤ S := by
    intro x k i
    rw [← Finset.sum_filter]
    refine sum_comp_le_of_injOn (φ := fun b : F.Site j × Fin 4 => a b.1 b.2 ^ 4)
      (Φ := fun c => (blockPoint c x, k))
      (fun b => by have := ha b.1 b.2; positivity) (fun c hc => (Finset.mem_filter.1 hc).2) ?_
    intro c hc c' hc' e
    have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hc).1).2
    have h2 := (Finset.mem_filter.1 (Finset.mem_filter.1 hc').1).2
    have e1 : refineSite c.1 + siteOfCoords j x = refineSite c'.1 + siteOfCoords j x :=
      congrArg (fun b : F.Site j × Fin 4 => b.1) e
    have e2 := add_right_cancel e1
    have z0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [LatticePaths.mem_centredCube_iff]
      intro i
      have : 0 < F.blockSide := hL.pos
      simp
      omega
    have e3 : refineSite c.1 + siteOfCoords j (0 : Lattice4) = refineSite c'.1 + siteOfCoords j 0 := by rw [e2]
    exact Prod.ext (refineSite_add_injective hL hj z0 z0 e3).1 (h1.trans h2.symm)
  have two : ∀ (x : Lattice4) (k : Fin 4), ∑ c ∈ innerBonds D (j + 1),
      (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0) ≤ 4 * S := by
    intro x k
    rw [← Finset.sum_fiberwise (innerBonds D (j + 1)) (fun c => c.2)]
    calc ∑ i : Fin 4, ∑ c ∈ (innerBonds D (j + 1)).filter (fun c => c.2 = i),
          (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0)
        ≤ ∑ _i : Fin 4, S := Finset.sum_le_sum fun i _ => one x k i
      _ = 4 * S := by simp
  unfold localQuarticSum
  calc ∑ c ∈ innerBonds D (j + 1), ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4,
        (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0)
      = ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4, ∑ c ∈ innerBonds D (j + 1),
        (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ ≤ ∑ _x ∈ centredCube (3 * F.blockSide), ∑ _k : Fin 4, 4 * S :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => two x k
    _ = 16 * (3 * (F.blockSide : ℝ)) ^ 4 * S := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [card_centredCube_three_mul hL]
        push_cast
        ring
theorem localQuarticSum_le (hL : Odd F.blockSide) {j : ℕ} {a : F.Site j → Fin 4 → ℝ} (ha : ∀ x i, 0 ≤ a x i)
    (c : F.Site (j + 1) × Fin 4) :
    localQuarticSum D a c ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 := by
  classical
  set S := ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => by have := ha b.1 b.2; positivity
  unfold localQuarticSum
  have t : ∀ (x : Lattice4) (k : Fin 4),
      (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0) ≤ S := by
    intro x k
    split_ifs with hb
    · exact Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => a b.1 b.2 ^ 4)
        (fun b _ => by have := ha b.1 b.2; positivity) hb
    · exact hS0
  calc ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4,
        (if (blockPoint c x, k) ∈ innerBonds D j then a (blockPoint c x) k ^ 4 else 0)
      ≤ ∑ _x ∈ centredCube (3 * F.blockSide), ∑ _k : Fin 4, S :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => t x k
    _ = 4 * (3 * (F.blockSide : ℝ)) ^ 4 * S := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [card_centredCube_three_mul hL]
        push_cast
        ring
theorem sum_sites_localQuarticSum_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {a : F.Site j → Fin 4 → ℝ} (ha : ∀ x i, 0 ≤ a x i) :
    ∑ y ∈ sitesOfCells D (j + 1), localQuarticSum D a (y, 0) ≤
      4 * (3 * (F.blockSide : ℝ)) ^ 4 * ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 := by
  classical
  set S := ∑ b ∈ innerBonds D j, a b.1 b.2 ^ 4 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => by have := ha b.1 b.2; positivity
  have one : ∀ (x : Lattice4) (k : Fin 4), ∑ y ∈ sitesOfCells D (j + 1),
      (if (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x, k) ∈ innerBonds D j then
        a (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x) k ^ 4 else 0) ≤ S := by
    intro x k
    rw [← Finset.sum_filter]
    refine sum_comp_le_of_injOn (φ := fun b : F.Site j × Fin 4 => a b.1 b.2 ^ 4)
      (Φ := fun y => (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x, k))
      (fun b => by have := ha b.1 b.2; positivity) (fun c hc => (Finset.mem_filter.1 hc).2) ?_
    intro y _ y' _ e
    have e1 : refineSite y + siteOfCoords j x = refineSite y' + siteOfCoords j x :=
      congrArg (fun b : F.Site j × Fin 4 => b.1) e
    have e2 := add_right_cancel e1
    have z0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [LatticePaths.mem_centredCube_iff]
      intro i
      have : 0 < F.blockSide := hL.pos
      simp
      omega
    have e3 : refineSite y + siteOfCoords j (0 : Lattice4) = refineSite y' + siteOfCoords j 0 := by rw [e2]
    exact (refineSite_add_injective hL hj z0 z0 e3).1
  unfold localQuarticSum
  calc ∑ y ∈ sitesOfCells D (j + 1), ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4,
        (if (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x, k) ∈ innerBonds D j then
          a (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x) k ^ 4 else 0)
      = ∑ x ∈ centredCube (3 * F.blockSide), ∑ k : Fin 4, ∑ y ∈ sitesOfCells D (j + 1),
        (if (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x, k) ∈ innerBonds D j then
          a (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) x) k ^ 4 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ ≤ ∑ _x ∈ centredCube (3 * F.blockSide), ∑ _k : Fin 4, S :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => one x k
    _ = 4 * (3 * (F.blockSide : ℝ)) ^ 4 * S := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [card_centredCube_three_mul hL]
        push_cast
        ring
theorem le_localQuarticNorm_site (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {a : F.Site j → Fin 4 → ℝ}
    (ha : ∀ x i, 0 ≤ a x i) {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells D (j + 1)) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) {k : Fin 4} (hk : h + Pi.single k 1 ∈ centredCube F.blockSide) :
    a (refineSite y + siteOfCoords j h) k ≤ localQuarticNorm D a (y, 0) := by
  have hb : (blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) h, k) ∈ innerBonds D j := by
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨refineSite_add_mem_sitesOfCells hL hj hy hh,
      Finset.mem_univ _⟩, ?_⟩
    show blockPoint ((y, 0) : F.Site (j + 1) × Fin 4) h + unitStep j k ∈ sitesOfCells D j
    rw [blockPoint_add_unitStep]
    exact refineSite_add_mem_sitesOfCells hL hj hy hk
  exact le_localQuarticNorm ha (mem_centredCube_three_mul hL (i := 0) (Or.inl hh)) hb
end Main
end LocalQuarticNorms
open LocalQuarticNorms in
theorem averagesAndLocalSizes_holds : averagesAndLocalSizesStatement := by
  intro F D j f hL hj hf
  refine ⟨fun c hc h hh r hr => line_mem_innerBonds hL hj hc hh hr, sum_lineBlockAverage_pow_four_le hL hj hf,
    sum_lineBlockAverage_sq_le hL hj hf,
    fun y => localQuarticNorm D f (y, 0), fun y => localQuarticNorm_nonneg _, fun c hc => ?_,
    fun y hy h hh k hk => le_localQuarticNorm_site hL hj hf hy hh hk, ?_, ?_, ?_⟩
  · exact boundedOnAdjacentBlocks_localQuarticNorm hL hj hf hc
  · intro y
    rw [localQuarticNorm_pow_four]
    exact localQuarticSum_le hL hf _
  · have e : ∀ c : F.Site (j + 1) × Fin 4, localQuarticNorm D f (c.1, 0) ^ 4 = localQuarticSum D f c := fun c => by
      rw [localQuarticNorm_pow_four]
      rfl
    simp only [e]
    exact sum_localQuarticSum_le hL hj hf
  · simp only [localQuarticNorm_pow_four]
    exact sum_sites_localQuarticSum_le hL hj hf
end BlockAverages
end YangMills.Construction
end
