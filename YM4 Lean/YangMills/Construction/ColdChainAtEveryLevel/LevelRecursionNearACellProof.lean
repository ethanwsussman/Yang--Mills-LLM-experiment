import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open LatticeFractionalIntegration (Lattice4 basisVector)
namespace QuarticRecursion
variable {F : BlockFrame}
theorem siteOfCoords_zsmul (j : ℕ) (r : ℤ) (a : Lattice4) :
    siteOfCoords (F := F) j (r • a) = r • siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.siteOfCoords_zsmul <;> assumption
variable {D : Finset F.Cell}
theorem refineSite_add_mem_sitesOfCells (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells D (j + 1))
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) : _root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j h ∈ sitesOfCells D j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_mem_sitesOfCells <;> assumption
def blockPoint {j : ℕ} (c : F.Site (j + 1) × Fin 4) (a : Lattice4) : F.Site j :=
  _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j a
theorem blockPoint_mem_sitesOfCells (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) {a : Lattice4}
    (ha : a ∈ centredCube F.blockSide ∨ a - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) :
    blockPoint c a ∈ sitesOfCells D j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.blockPoint_mem_sitesOfCells <;> assumption
theorem offset_add_smul_mem {L : ℕ} (hL : Odd L) {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4)
    {r : ℕ} (hr : r ≤ L) :
    h + (r : ℤ) • basisVector i ∈ centredCube L ∨
      (h + (r : ℤ) • basisVector i) - (L : ℤ) • basisVector i ∈ centredCube L := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.add_smul_basisVector_mem_or <;> assumption
theorem blockPoint_add_unitStep {j : ℕ} (c : F.Site (j + 1) × Fin 4) (a : Lattice4) (k : Fin 4) :
    blockPoint c a + unitStep j k = blockPoint c (a + basisVector k) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.blockPoint_add_unitStep <;> assumption
theorem refineSite_line_eq_blockPoint {j : ℕ} (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (r : ℕ) :
    _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 = blockPoint c (h + (r : ℤ) • basisVector c.2) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_smul_unitStep <;> assumption
theorem line_mem_innerBonds (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds D (j + 1)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) {r : ℕ}
    (hr : r < F.blockSide) :
    (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds D j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.line_mem_innerBonds <;> assumption
theorem refineSite_add_injective (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {y y' : F.Site (j + 1)}
    {h h' : Lattice4} (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : _root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j h = _root_.YangMills.Construction.BlockAverages.refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_injective <;> assumption
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] {P : Finset α} {Ω : Finset β} {φ : β → ℝ}
    {Φ : α → β} (hφ : ∀ b, 0 ≤ φ b) (hmap : ∀ p ∈ P, Φ p ∈ Ω) (hinj : Set.InjOn Φ P) :
    ∑ p ∈ P, φ (Φ p) ≤ ∑ b ∈ Ω, φ b := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sum_comp_le_of_injOn <;> assumption
theorem lineBlockAverage_nonneg {j : ℕ} {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i)
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ lineBlockAverage f c := by
  unfold lineBlockAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _)
theorem sum_lineBlockAverage_pow_four_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) :
    ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 4 ≤ ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sum_lineBlockAverage_pow_four_le <;> assumption
theorem sum_lineBlockAverage_sq_le (hL : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) :
    ∑ c ∈ innerBonds D (j + 1), lineBlockAverage f c ^ 2 ≤
      (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, f b.1 b.2 ^ 2 := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sum_lineBlockAverage_sq_le <;> assumption
section LpNorms
variable {ι : Type} {s : Finset ι}
theorem sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem le_sqrt_sqrt_of_pow_four_le {a x : ℝ} (ha : 0 ≤ a) (h : a ^ 4 ≤ x) : a ≤ Real.sqrt (Real.sqrt x) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.le_sqrt_sqrt_of_pow_four_le <;> assumption
theorem sqrt_sqrt_le_of_le_pow_four {a x : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 4) : Real.sqrt (Real.sqrt x) ≤ a := by
  have e : Real.sqrt (Real.sqrt (a ^ 4)) = a := by
    have e1 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e1, Real.sqrt_sq (by positivity), Real.sqrt_sq ha]
  calc Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt (a ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = a := e
theorem minkowski_two {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := f) (g := g) (p := 2) (by norm_num) hf hg
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h
theorem minkowski_four {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, (f i + g i) ^ 4)) ≤
      Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) + Real.sqrt (Real.sqrt (∑ i ∈ s, g i ^ 4)) := by
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := f) (g := g) (p := 4) (by norm_num) hf hg
  have e : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ 4 := fun x => by
    rw [← Real.rpow_natCast]
    norm_num
  simp only [e] at h
  rw [sqrt_sqrt_eq_rpow (Finset.sum_nonneg fun i hi => by have := hf i hi; have := hg i hi; positivity),
    sqrt_sqrt_eq_rpow (Finset.sum_nonneg fun i hi => by have := hf i hi; positivity),
    sqrt_sqrt_eq_rpow (Finset.sum_nonneg fun i hi => by have := hg i hi; positivity)]
  exact h
theorem lfour_le_ltwo {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) := by
  have hS : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h : ∑ i ∈ s, f i ^ 4 ≤ (∑ i ∈ s, f i ^ 2) ^ 2 := by
    rw [sq (∑ i ∈ s, f i ^ 2), Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : f i ^ 2 ≤ ∑ i ∈ s, f i ^ 2 :=
      Finset.single_le_sum (f := fun i => f i ^ 2) (fun i _ => by positivity) hi
    have e : f i ^ 4 = f i ^ 2 * f i ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine Real.sqrt_le_sqrt ?_
  calc Real.sqrt (∑ i ∈ s, f i ^ 4) ≤ Real.sqrt ((∑ i ∈ s, f i ^ 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = ∑ i ∈ s, f i ^ 2 := Real.sqrt_sq hS
end LpNorms
section Recursion
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
    (ha : a ∈ centredCube L ∨ a - (L : ℤ) • basisVector i ∈ centredCube L) : a ∈ centredCube (3 * L) := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.mem_centredCube_three_mul <;> assumption
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
  · have e1 : (h ∈ centredCube F.blockSide ∨
        h - (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide) := Or.inl hh
    exact le_localQuarticNorm ha (mem_centredCube_three_mul hL e1) (bond_of e1 (Or.inl hk))
  · have e : _root_.YangMills.Construction.BlockAverages.refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
        blockPoint c (h + (F.blockSide : ℤ) • basisVector c.2) := by
      rw [unitStep_eq, refineSite_add j hj]
      simp only [blockPoint, add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
      congr 2
      funext i
      simp [add_comm]
    have e1 : (h + (F.blockSide : ℤ) • basisVector c.2 ∈ centredCube F.blockSide ∨
        (h + (F.blockSide : ℤ) • basisVector c.2) - (F.blockSide : ℤ) • basisVector c.2 ∈
          centredCube F.blockSide) :=
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
    rw [refineSite_line_eq_blockPoint] at hb ⊢
    exact le_localQuarticNorm ha (mem_centredCube_three_mul hL (offset_add_smul_mem hL hh c.2 hr'.le)) hb
theorem card_centredCube_three_mul (hL : Odd F.blockSide) :
    ((centredCube (3 * F.blockSide)).card : ℝ) = (3 * (F.blockSide : ℝ)) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.card_centredCube_three_mul <;> assumption
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
    have e1 : _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j x = _root_.YangMills.Construction.BlockAverages.refineSite c'.1 + siteOfCoords j x :=
      congrArg (fun b : F.Site j × Fin 4 => b.1) e
    have e2 := add_right_cancel e1
    have z0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [LatticePaths.mem_centredCube_iff]
      intro i
      have : 0 < F.blockSide := hL.pos
      simp
      omega
    have e3 : _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (0 : Lattice4) = _root_.YangMills.Construction.BlockAverages.refineSite c'.1 + siteOfCoords j 0 := by rw [e2]
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
theorem card_innerBonds_le (hL : Odd F.blockSide) (j : ℕ) :
    ((innerBonds D j).card : ℝ) ≤ 4 * (D.card : ℝ) * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 4 := by
  classical
  have h1 : (innerBonds D j).card ≤ (sitesOfCells D j ×ˢ (Finset.univ : Finset (Fin 4))).card :=
    Finset.card_filter_le _ _
  have h2 : (sitesOfCells D j).card ≤ D.card * (F.blockSide ^ (F.top - j)) ^ 4 := by
    unfold sitesOfCells
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ z ∈ D, ((centredCube (F.blockSide ^ (F.top - j))).image fun h => cellCentre j z + siteOfCoords j h).card
        ≤ ∑ _z ∈ D, (F.blockSide ^ (F.top - j)) ^ 4 := by
          refine Finset.sum_le_sum fun z _ => Finset.card_image_le.trans ?_
          rw [LatticePaths.card_centredCube hL.pow]
      _ = D.card * (F.blockSide ^ (F.top - j)) ^ 4 := by simp
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have h3 : (innerBonds D j).card ≤ 4 * D.card * (F.blockSide ^ (F.top - j)) ^ 4 := by
    nlinarith
  exact_mod_cast h3
def quarticConst (L : ℕ) : ℝ := 16 * (3 * (L : ℝ)) ^ 4
def localConst (L : ℕ) : ℝ := 4 * (3 * (L : ℝ)) ^ 4
def scaleConst (L W : ℕ) : ℝ := 4 * (W : ℝ) * quarticConst L + 1
def closingConst (L W : ℕ) (K : ℝ) : ℝ :=
  256 * K ^ 2 * quarticConst L + 64 * K ^ 2 * scaleConst L W + 16 * K ^ 2 * localConst L ^ 2 + 1
theorem one_le_localConst {L : ℕ} (h : 1 ≤ L) : 1 ≤ localConst L := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast h
  have h2 : (1 : ℝ) ≤ (3 * (L : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
  unfold localConst
  linarith
theorem quarticConst_nonneg (L : ℕ) : 0 ≤ quarticConst L := by unfold quarticConst; positivity
theorem one_le_scaleConst (L W : ℕ) : 1 ≤ scaleConst L W := by
  have := quarticConst_nonneg L
  unfold scaleConst
  have h : 0 ≤ 4 * (W : ℝ) * quarticConst L := by positivity
  linarith
theorem one_le_closingConst (L W : ℕ) (K : ℝ) : 1 ≤ closingConst L W K := by
  have h1 := quarticConst_nonneg L
  have h2 := one_le_scaleConst L W
  unfold closingConst
  have a1 : 0 ≤ 256 * K ^ 2 * quarticConst L := by positivity
  have a2 : 0 ≤ 64 * K ^ 2 * scaleConst L W := by positivity
  have a3 : 0 ≤ 16 * K ^ 2 * localConst L ^ 2 := by positivity
  linarith
def levelSource (D : Finset F.Cell) (K s : ℝ) (a : (j : ℕ) → F.Site j → Fin 4 → ℝ)
    (m : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  m j c.1 c.2 + K * localQuarticNorm D (a j) c ^ 2 +
    2 * K * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 * localQuarticNorm D (a j) c +
    K * m j c.1 c.2 * localQuarticNorm D (a j) c
theorem sqrt_sum_sq_le_of_le_sq {ι : Type} {s : Finset ι} {f : ι → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (h : ∑ i ∈ s, f i ^ 2 ≤ x ^ 2) : Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ x := by
  rw [← Real.sqrt_sq hx]
  exact Real.sqrt_le_sqrt h
theorem recursion_constants_close {K s B c1 A M k1 k2 k4 G : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hB0 : 0 ≤ B)
    (hsc : s ≤ c1) (hBc : B ≤ c1) (hc1 : 4 * G * c1 ≤ 1) (hA0 : 0 ≤ A) (hA : A ≤ 4 * B) (k1p : 0 ≤ k1)
    (k2p : 0 ≤ k2) (k4p : 0 ≤ k4) (hM0 : 0 ≤ M) (hMB : M ≤ B ^ 2)
    (hG : 256 * K ^ 2 * k1 + 64 * K ^ 2 * k4 + 16 * K ^ 2 * k2 ^ 2 + 1 ≤ G) (hG1 : 1 ≤ G) :
    4 * (M + K ^ 2 * (k1 * A ^ 4) + 4 * K ^ 2 * s ^ 2 * (k4 * A ^ 2) + K ^ 2 * ((k2 * A) ^ 2 * M)) ≤
      (12 / 5 * B) ^ 2 := by
  have hc0 : 0 ≤ c1 := hs0.trans hsc
  have hA2 : A ^ 2 ≤ 16 * B ^ 2 := by
    have := pow_le_pow_left₀ hA0 hA 2
    calc A ^ 2 ≤ (4 * B) ^ 2 := this
      _ = 16 * B ^ 2 := by ring
  have hA4 : A ^ 4 ≤ 256 * (B ^ 2 * B ^ 2) := by
    have := pow_le_pow_left₀ hA0 hA 4
    calc A ^ 4 ≤ (4 * B) ^ 4 := this
      _ = 256 * (B ^ 2 * B ^ 2) := by ring
  set a := 256 * K ^ 2 * k1 with ha
  set b := 64 * K ^ 2 * k4 with hb
  set c := 16 * K ^ 2 * k2 ^ 2 with hc
  have a0 : 0 ≤ a := by positivity
  have b0 : 0 ≤ b := by positivity
  have c0' : 0 ≤ c := by positivity
  have t1 : K ^ 2 * (k1 * A ^ 4) ≤ a * (B ^ 2 * B ^ 2) := by
    have : (K ^ 2 * k1) * A ^ 4 ≤ (K ^ 2 * k1) * (256 * (B ^ 2 * B ^ 2)) :=
      mul_le_mul_of_nonneg_left hA4 (by positivity)
    calc K ^ 2 * (k1 * A ^ 4) = (K ^ 2 * k1) * A ^ 4 := by ring
      _ ≤ (K ^ 2 * k1) * (256 * (B ^ 2 * B ^ 2)) := this
      _ = a * (B ^ 2 * B ^ 2) := by rw [ha]; ring
  have t2 : 4 * K ^ 2 * s ^ 2 * (k4 * A ^ 2) ≤ b * (s ^ 2 * B ^ 2) := by
    have : (4 * K ^ 2 * s ^ 2 * k4) * A ^ 2 ≤ (4 * K ^ 2 * s ^ 2 * k4) * (16 * B ^ 2) :=
      mul_le_mul_of_nonneg_left hA2 (by positivity)
    calc 4 * K ^ 2 * s ^ 2 * (k4 * A ^ 2) = (4 * K ^ 2 * s ^ 2 * k4) * A ^ 2 := by ring
      _ ≤ (4 * K ^ 2 * s ^ 2 * k4) * (16 * B ^ 2) := this
      _ = b * (s ^ 2 * B ^ 2) := by rw [hb]; ring
  have t3 : K ^ 2 * ((k2 * A) ^ 2 * M) ≤ c * (B ^ 2 * B ^ 2) := by
    have h1 : A ^ 2 * M ≤ (16 * B ^ 2) * B ^ 2 := mul_le_mul hA2 hMB hM0 (by positivity)
    have : (K ^ 2 * k2 ^ 2) * (A ^ 2 * M) ≤ (K ^ 2 * k2 ^ 2) * ((16 * B ^ 2) * B ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc K ^ 2 * ((k2 * A) ^ 2 * M) = (K ^ 2 * k2 ^ 2) * (A ^ 2 * M) := by ring
      _ ≤ (K ^ 2 * k2 ^ 2) * ((16 * B ^ 2) * B ^ 2) := this
      _ = c * (B ^ 2 * B ^ 2) := by rw [hc]; ring
  have hB2 : B ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ hB0 hBc 2
  have hs2 : s ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ hs0 hsc 2
  have hc14 : c1 ≤ 1 / 4 := by
    have : 4 * c1 ≤ 4 * G * c1 := by nlinarith
    linarith
  have hGc : G * c1 ^ 2 ≤ 1 / 16 := by
    have h1 : (4 * G * c1) * c1 ≤ 1 * (1 / 4) := mul_le_mul hc1 hc14 hc0 zero_le_one
    nlinarith
  have w1 : a * B ^ 2 + b * s ^ 2 + c * B ^ 2 ≤ G * c1 ^ 2 := by
    have u1 : a * B ^ 2 ≤ a * c1 ^ 2 := mul_le_mul_of_nonneg_left hB2 a0
    have u2 : b * s ^ 2 ≤ b * c1 ^ 2 := mul_le_mul_of_nonneg_left hs2 b0
    have u3 : c * B ^ 2 ≤ c * c1 ^ 2 := mul_le_mul_of_nonneg_left hB2 c0'
    have u4 : (a + b + c) * c1 ^ 2 ≤ G * c1 ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have w2 : a * (B ^ 2 * B ^ 2) + b * (s ^ 2 * B ^ 2) + c * (B ^ 2 * B ^ 2) ≤ 1 / 16 * B ^ 2 := by
    have : (a * B ^ 2 + b * s ^ 2 + c * B ^ 2) * B ^ 2 ≤ (1 / 16) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (w1.trans hGc) (by positivity)
    calc a * (B ^ 2 * B ^ 2) + b * (s ^ 2 * B ^ 2) + c * (B ^ 2 * B ^ 2)
        = (a * B ^ 2 + b * s ^ 2 + c * B ^ 2) * B ^ 2 := by ring
      _ ≤ _ := this
  have e : (12 / 5 * B) ^ 2 = 144 / 25 * B ^ 2 := by ring
  rw [e]
  linarith
theorem sqrt_sum_levelSource_sq_le (hL : Odd F.blockSide) {W : ℕ} (hD : D.card ≤ W) {j : ℕ}
    (hj : j + 1 ≤ F.top) {K s B c1 : ℝ}
    {a : (j : ℕ) → F.Site j → Fin 4 → ℝ} {m : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ}
    (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hB0 : 0 ≤ B) (hsc : s ≤ c1) (hBc : B ≤ c1)
    (hc1 : 4 * closingConst F.blockSide W K * c1 ≤ 1)
    (ha : ∀ x i, 0 ≤ a j x i) (hm : ∀ x i, 0 ≤ m j x i)
    (hA : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B)
    (hM : Real.sqrt (∑ c ∈ innerBonds D (j + 1), m j c.1 c.2 ^ 2) ≤ B) :
    Real.sqrt (∑ c ∈ innerBonds D (j + 1), levelSource D K s a m j c ^ 2) ≤ 12 / 5 * B := by
  have hLp : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  set S := ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => by have := ha b.1 b.2; positivity
  set A := Real.sqrt (Real.sqrt S) with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA4 : A ^ 4 = S := sqrt_sqrt_pow_four hS0
  set Ω := innerBonds D (j + 1) with hΩ
  set T : F.Site (j + 1) × Fin 4 → ℝ := fun c => localQuarticNorm D (a j) c with hT
  have hT0 : ∀ c, 0 ≤ T c := fun c => localQuarticNorm_nonneg c
  set M : ℝ := (F.blockSide : ℝ) ^ (F.top - (j + 1)) with hMdef
  have hM1 : 1 ≤ M := one_le_pow₀ hLp
  have hlev : (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) = 1 / M := by rw [hMdef, one_div_pow]
  set ℓ : ℝ := (1 / M) ^ 2 with hℓ
  set sumM := ∑ c ∈ Ω, m j c.1 c.2 ^ 2 with hsumM
  have hsumM0 : 0 ≤ sumM := Finset.sum_nonneg fun c _ => by positivity
  have hsumMB : sumM ≤ B ^ 2 := by
    have := Real.sq_sqrt hsumM0
    nlinarith [Real.sqrt_nonneg sumM]
  have hK2 := one_le_localConst (L := F.blockSide) hL.pos
  have hTA : ∀ c, T c ≤ localConst F.blockSide * A := by
    intro c
    refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
    have h1 := localQuarticSum_le (D := D) hL (ha) c
    have e : 4 * (3 * (F.blockSide : ℝ)) ^ 4 = localConst F.blockSide := rfl
    rw [e] at h1
    have h2 : localConst F.blockSide ≤ localConst F.blockSide ^ 4 := le_self_pow₀ hK2 (by norm_num)
    calc localQuarticSum D (a j) c ≤ localConst F.blockSide * S := h1
      _ ≤ localConst F.blockSide ^ 4 * S := mul_le_mul_of_nonneg_right h2 hS0
      _ = (localConst F.blockSide * A) ^ 4 := by rw [mul_pow, hA4]
  have hT4 : ∑ c ∈ Ω, T c ^ 4 ≤ quarticConst F.blockSide * A ^ 4 := by
    have h1 := sum_localQuarticSum_le (D := D) hL hj (a := a j) ha
    have e : ∀ c, T c ^ 4 = localQuarticSum D (a j) c := fun c => localQuarticNorm_pow_four c
    simp only [e]
    rw [hA4]
    exact h1
  set P := ∑ c ∈ Ω, (ℓ * T c) ^ 2 with hP
  have hPK : P ≤ scaleConst F.blockSide W * A ^ 2 := by
    have h1 : P ^ 2 ≤ (Ω.card : ℝ) * ∑ c ∈ Ω, ((ℓ * T c) ^ 2) ^ 2 := sq_sum_le_card_mul_sum_sq
    have e1 : ∑ c ∈ Ω, ((ℓ * T c) ^ 2) ^ 2 = ℓ ^ 4 * ∑ c ∈ Ω, T c ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    have h2 : (Ω.card : ℝ) ≤ 4 * (W : ℝ) * M ^ 4 := by
      have := card_innerBonds_le (D := D) hL (j + 1)
      have hDW : (D.card : ℝ) ≤ W := by exact_mod_cast hD
      refine this.trans ?_
      have : 0 ≤ M ^ 4 := by positivity
      nlinarith
    have h3 : (Ω.card : ℝ) * ℓ ^ 4 ≤ 4 * (W : ℝ) := by
      have e2 : M ^ 4 * ℓ ^ 4 ≤ 1 := by
        have : M ^ 4 * ℓ ^ 4 = 1 / M ^ 4 := by rw [hℓ]; field_simp
        rw [this, div_le_one (by positivity)]
        exact one_le_pow₀ hM1
      have hl4 : 0 ≤ ℓ ^ 4 := by positivity
      calc (Ω.card : ℝ) * ℓ ^ 4 ≤ 4 * (W : ℝ) * M ^ 4 * ℓ ^ 4 := mul_le_mul_of_nonneg_right h2 hl4
        _ = 4 * (W : ℝ) * (M ^ 4 * ℓ ^ 4) := by ring
        _ ≤ 4 * (W : ℝ) * 1 := by gcongr
        _ = 4 * (W : ℝ) := by ring
    have h4 : P ^ 2 ≤ 4 * (W : ℝ) * (quarticConst F.blockSide * A ^ 4) := by
      rw [e1] at h1
      calc P ^ 2 ≤ (Ω.card : ℝ) * (ℓ ^ 4 * ∑ c ∈ Ω, T c ^ 4) := h1
        _ = ((Ω.card : ℝ) * ℓ ^ 4) * ∑ c ∈ Ω, T c ^ 4 := by ring
        _ ≤ (4 * (W : ℝ)) * (quarticConst F.blockSide * A ^ 4) := by
            refine mul_le_mul h3 hT4 (Finset.sum_nonneg fun c _ => by have := hT0 c; positivity) (by positivity)
    have h5 : P ^ 2 ≤ (scaleConst F.blockSide W * A ^ 2) ^ 2 := by
      have k1 := one_le_scaleConst F.blockSide W
      have k2 : scaleConst F.blockSide W ≤ scaleConst F.blockSide W ^ 2 := le_self_pow₀ k1 (by norm_num)
      have k3 : 4 * (W : ℝ) * quarticConst F.blockSide ≤ scaleConst F.blockSide W := by
        unfold scaleConst; linarith
      calc P ^ 2 ≤ 4 * (W : ℝ) * (quarticConst F.blockSide * A ^ 4) := h4
        _ = (4 * (W : ℝ) * quarticConst F.blockSide) * A ^ 4 := by ring
        _ ≤ scaleConst F.blockSide W ^ 2 * A ^ 4 := mul_le_mul_of_nonneg_right (k3.trans k2) (by positivity)
        _ = (scaleConst F.blockSide W * A ^ 2) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' h5 (by have := one_le_scaleConst F.blockSide W; positivity)).2
  have hmT : ∑ c ∈ Ω, (m j c.1 c.2 * T c) ^ 2 ≤ (localConst F.blockSide * A) ^ 2 * sumM := by
    rw [hsumM, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h1 := hTA c
    have h2 := hT0 c
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h2 h1 2) (by positivity)
  have hsum : ∑ c ∈ Ω, levelSource D K s a m j c ^ 2 ≤
      4 * (sumM + K ^ 2 * (quarticConst F.blockSide * A ^ 4) +
        4 * K ^ 2 * s ^ 2 * (scaleConst F.blockSide W * A ^ 2) +
        K ^ 2 * ((localConst F.blockSide * A) ^ 2 * sumM)) := by
    have hpt : ∀ c ∈ Ω, levelSource D K s a m j c ^ 2 ≤ 4 * (m j c.1 c.2 ^ 2 + K ^ 2 * T c ^ 4 +
        4 * K ^ 2 * s ^ 2 * (ℓ * T c) ^ 2 + K ^ 2 * (m j c.1 c.2 * T c) ^ 2) := by
      intro c _
      unfold levelSource
      rw [hlev]
      have e : ∀ x y z w : ℝ, (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
        intro x y z w
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z),
          sq_nonneg (y - w), sq_nonneg (z - w)]
      have := e (m j c.1 c.2) (K * T c ^ 2) (2 * K * s * ℓ * T c) (K * m j c.1 c.2 * T c)
      calc _ ≤ _ := this
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have b1 : K ^ 2 * ∑ c ∈ Ω, T c ^ 4 ≤ K ^ 2 * (quarticConst F.blockSide * A ^ 4) := by gcongr
    have b2 : 4 * K ^ 2 * s ^ 2 * P ≤ 4 * K ^ 2 * s ^ 2 * (scaleConst F.blockSide W * A ^ 2) := by gcongr
    have b3 : K ^ 2 * ∑ c ∈ Ω, (m j c.1 c.2 * T c) ^ 2 ≤
        K ^ 2 * ((localConst F.blockSide * A) ^ 2 * sumM) := by gcongr
    linarith
  exact sqrt_sum_sq_le_of_le_sq (by positivity) (hsum.trans (recursion_constants_close hK hs0 hB0 hsc hBc hc1
    hA0 hA (quarticConst_nonneg _) (le_trans zero_le_one hK2) (le_trans zero_le_one (one_le_scaleConst _ _))
    hsumM0 hsumMB (by unfold closingConst; linarith [one_le_scaleConst F.blockSide W])
    (one_le_closingConst F.blockSide W K)))
def iteratedAverage (a0 : F.Site 0 → Fin 4 → ℝ) : (j : ℕ) → F.Site j → Fin 4 → ℝ
  | 0 => a0
  | j + 1 => fun y i => lineBlockAverage (iteratedAverage a0 j) (y, i)
def carriedSource (ρ : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ) : (j : ℕ) → F.Site j → Fin 4 → ℝ
  | 0 => fun _ _ => 0
  | j + 1 => fun y i => lineBlockAverage (carriedSource ρ j) (y, i) + ρ j (y, i)
theorem iteratedAverage_nonneg {a0 : F.Site 0 → Fin 4 → ℝ} (h : ∀ x i, 0 ≤ a0 x i) (j : ℕ) :
    ∀ x i, 0 ≤ iteratedAverage a0 j x i := by
  induction j with
  | zero => exact h
  | succ j ih => exact fun y i => lineBlockAverage_nonneg ih _
theorem carriedSource_nonneg {ρ : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ} (h : ∀ j c, 0 ≤ ρ j c) (j : ℕ) :
    ∀ x i, 0 ≤ carriedSource ρ j x i := by
  induction j with
  | zero => exact fun _ _ => le_rfl
  | succ j ih => exact fun y i => add_nonneg (lineBlockAverage_nonneg ih _) (h _ _)
theorem sum_iteratedAverage_pow_four_le (hL : Odd F.blockSide) {a0 : F.Site 0 → Fin 4 → ℝ}
    (h : ∀ x i, 0 ≤ a0 x i) {B : ℝ} (hB : 0 ≤ B)
    (h0 : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, a0 b.1 b.2 ^ 4)) ≤ B) (j : ℕ) (hj : j ≤ F.top) :
    ∑ b ∈ innerBonds D j, iteratedAverage a0 j b.1 b.2 ^ 4 ≤ B ^ 4 := by
  induction j with
  | zero =>
    have hS : 0 ≤ ∑ b ∈ innerBonds D 0, a0 b.1 b.2 ^ 4 :=
      Finset.sum_nonneg fun b _ => by have := h b.1 b.2; positivity
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h0 4
    rwa [sqrt_sqrt_pow_four hS] at this
  | succ j ih =>
    exact (sum_lineBlockAverage_pow_four_le hL hj (iteratedAverage_nonneg h j)).trans (ih (by omega))
theorem lineBlockAverage_le_add {j : ℕ} (hL : Odd F.blockSide) (hj : j + 1 ≤ F.top) {a v e : F.Site j → Fin 4 → ℝ}
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1))
    (h : ∀ b ∈ innerBonds D j, a b.1 b.2 ≤ v b.1 b.2 + e b.1 b.2) :
    lineBlockAverage a c ≤ lineBlockAverage v c + lineBlockAverage e c := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold lineBlockAverage
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx => ?_) (by positivity)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun r hr => h _ (line_mem_innerBonds hL hj hc hx (Finset.mem_range.1 hr))
end Recursion
theorem quartic_bound_of_recursion (hL : Odd F.blockSide) (h5 : 5 ≤ F.blockSide) {W : ℕ} (hD : D.card ≤ W)
    {K c0 c1 s B : ℝ} (hK : 0 ≤ K) (hc0 : 0 < c0)
    (hc1 : 4 * closingConst F.blockSide W K * c1 ≤ 1) (hc2 : 4 * localConst F.blockSide * c1 ≤ c0)
    {a : (j : ℕ) → F.Site j → Fin 4 → ℝ} {m : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ c1) (hB0 : 0 ≤ B) (hB : B ≤ c1)
    (ha : ∀ j x i, 0 ≤ a j x i) (hm : ∀ j x i, 0 ≤ m j x i)
    (h0 : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, a 0 b.1 b.2 ^ 4)) ≤ B)
    (hM : ∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ innerBonds D (j + 1), m j c.1 c.2 ^ 2) ≤ B)
    (hrec : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds D (j + 1), ∀ t : ℝ, 0 ≤ t → t ≤ c0 → m j c.1 c.2 ≤ c0 →
        BoundedOnAdjacentBlocks (a j) c t →
        a (j + 1) c.1 c.2 ≤ m j c.1 c.2 + lineBlockAverage (a j) c +
          K * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 + m j c.1 c.2 +
            s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3) * t)) :
    ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B := by
  have hLp : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  have hL5 : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast h5
  have hK2 := one_le_localConst (L := F.blockSide) hL.pos
  set v := iteratedAverage (a 0) with hv
  set e := carriedSource (F := F) (levelSource D K s a m) with he
  have hρ0 : ∀ j c, 0 ≤ levelSource D K s a m j c := by
    intro j c
    unfold levelSource
    have h1 := hm j c.1 c.2
    have h2 : 0 ≤ localQuarticNorm D (a j) c := localQuarticNorm_nonneg c
    positivity
  have hv0 : ∀ j x i, 0 ≤ v j x i := fun j => iteratedAverage_nonneg (ha 0) j
  have he0 : ∀ j x i, 0 ≤ e j x i := fun j => carriedSource_nonneg hρ0 j
  have hvn : ∀ j, j ≤ F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, v j b.1 b.2 ^ 4)) ≤ B := fun j hj =>
    sqrt_sqrt_le_of_le_pow_four hB0 (sum_iteratedAverage_pow_four_le hL (ha 0) hB0 h0 j hj)
  have main : ∀ j, j < F.top → (∀ b ∈ innerBonds D j, a j b.1 b.2 ≤ v j b.1 b.2 + e j b.1 b.2) ∧
      Real.sqrt (∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2) ≤ 3 * B ∧
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun b _ => ?_, ?_, ?_⟩
      · show a 0 b.1 b.2 ≤ a 0 b.1 b.2 + 0
        linarith
      · have : ∑ b ∈ innerBonds D 0, e 0 b.1 b.2 ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          show (0 : ℝ) ^ 2 = 0
          norm_num
        rw [this, Real.sqrt_zero]
        positivity
      · linarith
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have hjn : j + 1 ≤ F.top := by omega
      set A := Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) with hA
      have hS0 : 0 ≤ ∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4 :=
        Finset.sum_nonneg fun b _ => by have := ha j b.1 b.2; positivity
      have hMj := hM j hj
      have pt : ∀ c ∈ innerBonds D (j + 1), a (j + 1) c.1 c.2 ≤ v (j + 1) c.1 c.2 + e (j + 1) c.1 c.2 := by
        intro c hc
        have hT0 : 0 ≤ localQuarticNorm D (a j) c := localQuarticNorm_nonneg c
        have hTA : localQuarticNorm D (a j) c ≤ localConst F.blockSide * A := by
          refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
          have h1 := localQuarticSum_le (D := D) hL (ha j) c
          have h2 : localConst F.blockSide ≤ localConst F.blockSide ^ 4 := le_self_pow₀ hK2 (by norm_num)
          rw [mul_pow, hA, sqrt_sqrt_pow_four hS0]
          exact h1.trans (mul_le_mul_of_nonneg_right h2 hS0)
        have hTc : localQuarticNorm D (a j) c ≤ c0 := by
          calc localQuarticNorm D (a j) c ≤ localConst F.blockSide * A := hTA
            _ ≤ localConst F.blockSide * (4 * c1) := by
                refine mul_le_mul_of_nonneg_left ?_ (by linarith)
                linarith
            _ = 4 * localConst F.blockSide * c1 := by ring
            _ ≤ c0 := hc2
        have hmB : m j c.1 c.2 ≤ B := by
          refine le_trans ?_ hMj
          refine Real.le_sqrt_of_sq_le ?_
          exact Finset.single_le_sum (f := fun c : F.Site (j + 1) × Fin 4 => m j c.1 c.2 ^ 2)
            (fun c _ => by positivity) hc
        have hmc : m j c.1 c.2 ≤ c0 := by
          have : c1 ≤ c0 := by nlinarith
          linarith
        have hr := hrec j hj c hc _ hT0 hTc hmc (boundedOnAdjacentBlocks_localQuarticNorm hL hjn (ha j) hc)
        have hadd := lineBlockAverage_le_add hL hjn hc i1
        have hl1 : (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) ≤ 1 := by
          refine pow_le_one₀ (by positivity) ?_
          rw [div_le_one (by linarith)]
          exact hLp
        set l := (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) with hl
        have hl3 : l ^ 3 ≤ l ^ 2 := by nlinarith [sq_nonneg l]
        have hs3 : s * l ^ 3 ≤ s * l ^ 2 := mul_le_mul_of_nonneg_left hl3 hs0
        have hfin : K * (localQuarticNorm D (a j) c ^ 2 +
              (s * l ^ 2 + m j c.1 c.2 + s * l ^ 3) * localQuarticNorm D (a j) c) ≤
            K * localQuarticNorm D (a j) c ^ 2 + 2 * K * s * l ^ 2 * localQuarticNorm D (a j) c +
              K * m j c.1 c.2 * localQuarticNorm D (a j) c := by
          have : (s * l ^ 3) * localQuarticNorm D (a j) c ≤ (s * l ^ 2) * localQuarticNorm D (a j) c :=
            mul_le_mul_of_nonneg_right hs3 hT0
          have := mul_le_mul_of_nonneg_left this hK
          nlinarith
        have ev : v (j + 1) c.1 c.2 = lineBlockAverage (v j) c := rfl
        have ee : e (j + 1) c.1 c.2 = lineBlockAverage (e j) c + levelSource D K s a m j c := rfl
        rw [ev, ee]
        unfold levelSource
        rw [← hl]
        linarith
      have hE : Real.sqrt (∑ b ∈ innerBonds D (j + 1), e (j + 1) b.1 b.2 ^ 2) ≤ 3 * B := by
        have hρ := sqrt_sum_levelSource_sq_le hL hD hjn hK hs0 hB0 hs hB hc1 (ha j) (hm j) i3 hMj
        have hQ : Real.sqrt (∑ c ∈ innerBonds D (j + 1), lineBlockAverage (e j) c ^ 2) ≤ 3 / 5 * B := by
          have h1 := sum_lineBlockAverage_sq_le (D := D) hL hjn (he0 j)
          have hE0 : 0 ≤ ∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2 :=
            Finset.sum_nonneg fun b _ => by positivity
          have h2 : Real.sqrt (∑ c ∈ innerBonds D (j + 1), lineBlockAverage (e j) c ^ 2) ≤
              (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2) := by
            have e1 : (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2 =
                ((1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hE0]
              field_simp
            rw [e1] at h1
            exact sqrt_sum_sq_le_of_le_sq (by positivity) h1
          have h3 : 1 / (F.blockSide : ℝ) ≤ 1 / 5 := by
            exact one_div_le_one_div_of_le (by norm_num) hL5
          calc _ ≤ (1 / (F.blockSide : ℝ)) * Real.sqrt (∑ b ∈ innerBonds D j, e j b.1 b.2 ^ 2) := h2
            _ ≤ (1 / 5) * (3 * B) := mul_le_mul h3 i2 (Real.sqrt_nonneg _) (by norm_num)
            _ = 3 / 5 * B := by ring
        have hmk := minkowski_two (s := innerBonds D (j + 1)) (f := fun c => lineBlockAverage (e j) c)
          (g := fun c => levelSource D K s a m j c) (fun c _ => lineBlockAverage_nonneg (he0 j) c)
          (fun c _ => hρ0 j c)
        have ee : ∀ c : F.Site (j + 1) × Fin 4,
            e (j + 1) c.1 c.2 = lineBlockAverage (e j) c + levelSource D K s a m j c := fun c => rfl
        simp only [ee]
        linarith
      refine ⟨pt, hE, ?_⟩
      have h1 : ∑ b ∈ innerBonds D (j + 1), a (j + 1) b.1 b.2 ^ 4 ≤
          ∑ b ∈ innerBonds D (j + 1), (v (j + 1) b.1 b.2 + e (j + 1) b.1 b.2) ^ 4 :=
        Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (ha _ _ _) (pt c hc) 4
      have h2 := minkowski_four (s := innerBonds D (j + 1)) (f := fun b => v (j + 1) b.1 b.2)
        (g := fun b => e (j + 1) b.1 b.2) (fun b _ => hv0 _ _ _) (fun b _ => he0 _ _ _)
      have h3 := lfour_le_ltwo (s := innerBonds D (j + 1)) (f := fun b => e (j + 1) b.1 b.2)
        (fun b _ => he0 _ _ _)
      have h4 := hvn (j + 1) (by omega)
      calc Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D (j + 1), a (j + 1) b.1 b.2 ^ 4))
          ≤ Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D (j + 1), (v (j + 1) b.1 b.2 + e (j + 1) b.1 b.2) ^ 4)) :=
            Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
        _ ≤ 4 * B := by linarith
  exact fun j hj => (main j hj).2.2
end QuarticRecursion
open QuarticRecursion in
theorem uniformQuarticBoundAcrossLevels_proof : UniformQuarticBoundAcrossLevels := by
  intro L W K c0 hL h5 hK hc0
  have hG := one_le_closingConst L W K
  have hK2 := one_le_localConst (L := L) hL.pos
  have hGp : 0 < closingConst L W K := by linarith
  have hKp : 0 < localConst L := by linarith
  refine ⟨min (c0 / (4 * localConst L)) (1 / (4 * closingConst L W K)), lt_min (by positivity) (by positivity), ?_⟩
  intro F D a m s B hFL hD hs0 hs hB0 hB ha hm h0 hM hrec
  subst hFL
  set c1 := min (c0 / (4 * localConst F.blockSide)) (1 / (4 * closingConst F.blockSide W K)) with hc1
  have e1 : 4 * closingConst F.blockSide W K * c1 ≤ 1 := by
    have : c1 ≤ 1 / (4 * closingConst F.blockSide W K) := min_le_right _ _
    calc 4 * closingConst F.blockSide W K * c1 ≤
          4 * closingConst F.blockSide W K * (1 / (4 * closingConst F.blockSide W K)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := by field_simp
  have e2 : 4 * localConst F.blockSide * c1 ≤ c0 := by
    have : c1 ≤ c0 / (4 * localConst F.blockSide) := min_le_left _ _
    calc 4 * localConst F.blockSide * c1 ≤ 4 * localConst F.blockSide * (c0 / (4 * localConst F.blockSide)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c0 := by field_simp
  exact quartic_bound_of_recursion hL h5 hD hK hc0 e1 e2 hs0 hs hB0 hB ha hm h0 hM hrec
end YangMills.Construction.BlockAverages
end
