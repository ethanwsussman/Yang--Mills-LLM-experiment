import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACellProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverTheSitesOfATorus
import YangMills.Construction.TorusForms.CompositionOfBlockAveragesProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ColdStepAtMirrorFrames
noncomputable section
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def axisOffset (j : ℕ) (i : Fin 4) (m : ℤ) : F.Site j := siteOfCoords j (Pi.single i m)
theorem axisOffset_add (j : ℕ) (i : Fin 4) (m m' : ℤ) :
    (axisOffset j i (m + m') : F.Site j) = axisOffset j i m + axisOffset j i m' := by
  unfold axisOffset
  rw [← siteOfCoords_add, Pi.single_add]
theorem axisOffset_zero (j : ℕ) (i : Fin 4) : (axisOffset j i 0 : F.Site j) = 0 := by
  unfold axisOffset
  rw [Pi.single_zero, siteOfCoords_zero]
theorem axisOffset_one (j : ℕ) (i : Fin 4) : (axisOffset j i 1 : F.Site j) = unitStep j i := rfl
theorem axisOffset_succ (j : ℕ) (i : Fin 4) (m : ℕ) :
    (axisOffset j i ((m + 1 : ℕ) : ℤ) : F.Site j) = axisOffset j i (m : ℤ) + unitStep j i := by
  rw [← axisOffset_one, ← axisOffset_add]
  push_cast
  rfl
def weightedNormSq {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) : ℝ :=
  ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) ^ 2
def weightedCurlNormSq {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) : ℝ :=
  ∑ x ∈ allSites F j, ∑ e ∈ orientedPlanes, (u x * plaquetteCurl B x e.1 e.2) ^ 2
theorem weightedNormSq_nonneg {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) :
    0 ≤ weightedNormSq u B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem weightedCurlNormSq_nonneg {j : ℕ} (u : F.Site j → ℝ) (B : LevelForm F j) :
    0 ≤ weightedCurlNormSq u B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem plaquetteCurl_swap {j : ℕ} (B : LevelForm F j) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl B x k l = - plaquetteCurl B x l k := by
  unfold plaquetteCurl
  ring
theorem plaquetteCurl_self {j : ℕ} (B : LevelForm F j) (x : F.Site j) (k : Fin 4) :
    plaquetteCurl B x k k = 0 := by
  unfold plaquetteCurl
  ring
theorem sq_plaquetteCurl_le_sum {j : ℕ} (B : LevelForm F j) (x : F.Site j) (c : ℝ) (k l : Fin 4) :
    (c * plaquetteCurl B x k l) ^ 2 ≤ ∑ e ∈ orientedPlanes, (c * plaquetteCurl B x e.1 e.2) ^ 2 := by
  have key : ∀ k l : Fin 4, k < l →
      (c * plaquetteCurl B x k l) ^ 2 ≤ ∑ e ∈ orientedPlanes, (c * plaquetteCurl B x e.1 e.2) ^ 2 := by
    intro k l h
    have hm : (k, l) ∈ orientedPlanes := by simp [orientedPlanes, h]
    exact Finset.single_le_sum (f := fun e : Fin 4 × Fin 4 => (c * plaquetteCurl B x e.1 e.2) ^ 2)
      (fun _ _ => sq_nonneg _) hm
  rcases lt_trichotomy k l with h | h | h
  · exact key k l h
  · subst h
    rw [plaquetteCurl_self]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · have := key l k h
    rw [plaquetteCurl_swap]
    simpa using this
theorem card_centredCube {M k : ℕ} (hM : M = 2 * k + 1) : (centredCube M).card = M ^ 4 := by
  have e : ((M : ℤ) - 1) / 2 = k := by
    rw [hM]
    push_cast
    omega
  unfold centredCube
  rw [Fintype.card_piFinset]
  simp only [e, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [hM]
  omega
theorem sq_sum_sum_le_card_mul {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, f a b) ^ 2 ≤ (s.card * t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, f a b ^ 2 := by
  have e : ∀ g : α → β → ℝ, ∑ a ∈ s, ∑ b ∈ t, g a b = ∑ p ∈ s ×ˢ t, g p.1 p.2 :=
    fun g => (Finset.sum_product s t (fun p => g p.1 p.2)).symm
  rw [e f, e (fun a b => f a b ^ 2)]
  have := sq_sum_le_card_mul_sum_sq (s := s ×ˢ t) (f := fun p : α × β => f p.1 p.2)
  simpa [Finset.card_product] using this
theorem blockRefine_eq_refineSite {j : ℕ} (y : F.Site (j + 1)) :
    BlockAverages.refineSite y = ColdStepAtMirrorFrames.refineSite j (j + 1) y := by
  unfold BlockAverages.refineSite ColdStepAtMirrorFrames.refineSite
  simp
theorem sum_allSites_eq_sum_blocks_succ (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top) (g : F.Site j → ℝ) :
    ∑ x ∈ allSites F j, g x =
      ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide,
        g (BlockAverages.refineSite y + siteOfCoords j h) := by
  have := sum_allSites_eq_sum_blocks hL hs (Nat.le_succ j) hj g
  simpa [blockRefine_eq_refineSite] using this
theorem sum_blocks_lines (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j + 1 ≤ F.top)
    (i : Fin 4) (G : F.Site j → ℝ) :
    ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        G (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) =
      (F.blockSide : ℝ) * ∑ x ∈ allSites F j, G x := by
  have hj' : j ≤ F.top := by omega
  have e : ∀ l : ℕ, ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide,
      G (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) =
      ∑ x ∈ allSites F j, G x := by
    intro l
    rw [← sum_allSites_eq_sum_blocks_succ hL hs hj (fun x => G (x + axisOffset j i (l : ℤ)))]
    exact sum_allSites_add_right hL hs hj' _ G
  calc _ = ∑ y ∈ allSites F (j + 1), ∑ l ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
        G (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ l ∈ Finset.range F.blockSide, ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide,
        G (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) := Finset.sum_comm
    _ = _ := by
        simp [e]
theorem blockRefine_siteOfCoords {j : ℕ} (hj : j + 1 ≤ F.top) (q : Fin 4 → ℤ) :
    BlockAverages.refineSite (siteOfCoords (j + 1) q : F.Site (j + 1)) =
      siteOfCoords j fun i => (F.blockSide : ℤ) * q i := by
  rw [blockRefine_eq_refineSite, refineSite_siteOfCoords (Nat.le_succ j) hj]
  simp
theorem blockRefine_add_siteOfCoords {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (q : Fin 4 → ℤ) :
    BlockAverages.refineSite (y + siteOfCoords (j + 1) q) =
      BlockAverages.refineSite y + siteOfCoords j fun i => (F.blockSide : ℤ) * q i := by apply _root_.YangMills.Construction.BlockAverages.refineSite_add <;> assumption
theorem mul_single (i : Fin 4) (c m : ℤ) :
    (fun k => c * (Pi.single i m : Fin 4 → ℤ) k) = Pi.single i (c * m) := by
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
theorem blockRefine_add_unitStep {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    BlockAverages.refineSite (y + unitStep (j + 1) i) =
      BlockAverages.refineSite y + axisOffset j i (F.blockSide : ℤ) := by
  unfold unitStep
  rw [blockRefine_add_siteOfCoords hj, mul_single]
  simp [axisOffset]
def latticeGradient {j : ℕ} (φ : F.Site j → ℝ) : LevelForm F j :=
  fun x i => φ (x + unitStep j i) - φ x
def lineSum {j : ℕ} (Z : LevelForm F j) (x : F.Site j) (i : Fin 4) (m : ℕ) : ℝ :=
  ∑ l ∈ Finset.range m, Z (x + axisOffset j i (l : ℤ)) i
theorem lineSum_latticeGradient {j : ℕ} (φ : F.Site j → ℝ) (x : F.Site j) (i : Fin 4) (m : ℕ) :
    lineSum (latticeGradient φ) x i m = φ (x + axisOffset j i (m : ℤ)) - φ x := by
  induction m with
  | zero => simp [lineSum, axisOffset_zero]
  | succ m ih =>
    unfold lineSum at *
    rw [Finset.sum_range_succ, ih, axisOffset_succ]
    unfold latticeGradient
    rw [add_assoc]
    ring
theorem lineAverage_eq_lineSum {j : ℕ} (B : LevelForm F j) (y : F.Site (j + 1)) (i : Fin 4) :
    lineAverage B y i = (1 / (F.blockSide : ℝ) ^ 4) *
      ∑ h ∈ centredCube F.blockSide, lineSum B (BlockAverages.refineSite y + siteOfCoords j h) i F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.lineAverage_eq <;> assumption
theorem lineAverage_latticeGradient {j : ℕ} (hj : j + 1 ≤ F.top) (φ : F.Site j → ℝ) :
    lineAverage (latticeGradient φ) = latticeGradient (blockAverage φ) := by
  funext y i
  rw [lineAverage_eq_lineSum]
  simp only [lineSum_latticeGradient]
  unfold latticeGradient blockAverage
  rw [blockRefine_add_unitStep hj, Finset.sum_sub_distrib, mul_sub]
  congr 2
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [add_right_comm]
theorem lineAverage_add {j : ℕ} (B D : LevelForm F j) :
    lineAverage (B + D) = lineAverage B + lineAverage D := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.lineAverage_add <;> assumption
theorem lineAverage_sub {j : ℕ} (B D : LevelForm F j) :
    lineAverage (B - D) = lineAverage B - lineAverage D := by
  funext y i
  simp only [lineAverage, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
theorem sum_sq_lineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top) (i : Fin 4)
    (u : F.Site (j + 1) → ℝ) (v : F.Site j → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (g : F.Site j → ℝ)
    (hw : ∀ y, ∀ h ∈ centredCube F.blockSide, ∀ l ∈ Finset.range F.blockSide,
      u y ^ 2 ≤ κ * v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2) :
    ∑ y ∈ allSites F (j + 1), (u y * ((1 / (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))) ^ 2 ≤
      κ / (F.blockSide : ℝ) ^ 2 * ∑ x ∈ allSites F j, (v x * g x) ^ 2 := by
  obtain ⟨k, hk⟩ := id hL
  have hLr : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube hk]
    push_cast
    rfl
  have hy : ∀ y, (u y * ((1 / (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))) ^ 2 ≤
      κ / (F.blockSide : ℝ) ^ 3 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
    intro y
    have c1 := sq_sum_sum_le_card_mul (centredCube F.blockSide) (Finset.range F.blockSide)
      (fun h l => g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))
    rw [hc, Finset.card_range] at c1
    have c2 : u y ^ 2 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2 ≤
        κ * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw y h hh l hl) (sq_nonneg _)
    have hu := sq_nonneg (u y)
    calc _ = u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) *
          (∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
          field_simp
      _ ≤ u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) * (((F.blockSide : ℝ) ^ 4 * (F.blockSide : ℝ)) *
          ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ = (1 / (F.blockSide : ℝ) ^ 3) * (u y ^ 2 *
          ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2) := by
          field_simp
      _ ≤ (1 / (F.blockSide : ℝ) ^ 3) * (κ * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2) :=
          mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = _ := by
          field_simp
  calc _ ≤ ∑ y ∈ allSites F (j + 1), κ / (F.blockSide : ℝ) ^ 3 *
        ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 :=
        Finset.sum_le_sum fun y _ => hy y
    _ = κ / (F.blockSide : ℝ) ^ 3 * ((F.blockSide : ℝ) * ∑ x ∈ allSites F j, (v x * g x) ^ 2) := by
        rw [← Finset.mul_sum, sum_blocks_lines hL hs hj i (fun x => (v x * g x) ^ 2)]
    _ = _ := by
        field_simp
theorem weightedNormSq_lineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top)
    (u : F.Site (j + 1) → ℝ) (v : F.Site j → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (B : LevelForm F j)
    (hw : ∀ i y, ∀ h ∈ centredCube F.blockSide, ∀ l ∈ Finset.range F.blockSide,
      u y ^ 2 ≤ κ * v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2) :
    weightedNormSq u (lineAverage B) ≤ κ / (F.blockSide : ℝ) ^ 2 * weightedNormSq v B := by
  unfold weightedNormSq
  rw [Finset.sum_comm, Finset.sum_comm (s := allSites F j), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact sum_sq_lineAverage_le hL hs hj i u v κ hκ (fun x => B x i) (hw i)
theorem sub_lineSum_eq_sum_plaquetteCurl {j : ℕ} (Z : LevelForm F j) (x : F.Site j) (i k : Fin 4) (m : ℕ) :
    Z (x + axisOffset j i (m : ℤ)) k - Z x k - (lineSum Z (x + unitStep j k) i m - lineSum Z x i m) =
      ∑ l ∈ Finset.range m, plaquetteCurl Z (x + axisOffset j i (l : ℤ)) i k := by
  induction m with
  | zero => simp [lineSum, axisOffset_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold lineSum plaquetteCurl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, axisOffset_succ]
    have e1 : x + (axisOffset j i (m : ℤ) + unitStep j i) = x + axisOffset j i (m : ℤ) + unitStep j i := by
      rw [add_assoc]
    have e2 : x + unitStep j k + axisOffset j i (m : ℤ) = x + axisOffset j i (m : ℤ) + unitStep j k :=
      add_right_comm _ _ _
    rw [e1, e2]
    ring
theorem sum_plaquetteCurl_square {j : ℕ} (B : LevelForm F j) (p : F.Site j) (k l : Fin 4) (M n : ℕ) :
    ∑ m ∈ Finset.range n, ∑ m' ∈ Finset.range M,
        plaquetteCurl B (p + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) k l =
      lineSum B p k n + lineSum B (p + axisOffset j k (n : ℤ)) l M -
        lineSum B (p + axisOffset j l (M : ℤ)) k n - lineSum B p l M := by
  induction n with
  | zero => simp [lineSum, axisOffset_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have e : ∑ m' ∈ Finset.range M, plaquetteCurl B (p + axisOffset j k (n : ℤ) + axisOffset j l (m' : ℤ)) k l =
        - (∑ m' ∈ Finset.range M, plaquetteCurl B (p + axisOffset j k (n : ℤ) + axisOffset j l (m' : ℤ)) l k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => plaquetteCurl_swap _ _ _ _
    rw [e, ← sub_lineSum_eq_sum_plaquetteCurl B (p + axisOffset j k (n : ℤ)) l k M]
    have e3 : lineSum B p k (n + 1) = lineSum B p k n + B (p + axisOffset j k (n : ℤ)) k :=
      Finset.sum_range_succ _ _
    have e4 : lineSum B (p + axisOffset j l (M : ℤ)) k (n + 1) =
        lineSum B (p + axisOffset j l (M : ℤ)) k n + B (p + axisOffset j k (n : ℤ) + axisOffset j l (M : ℤ)) k := by
      rw [add_right_comm]
      exact Finset.sum_range_succ _ _
    have e5 : p + axisOffset j k ((n + 1 : ℕ) : ℤ) = p + axisOffset j k (n : ℤ) + unitStep j k := by
      rw [axisOffset_succ, add_assoc]
    rw [e3, e4, e5]
    ring
theorem plaquetteCurl_lineAverage {j : ℕ} (hj : j + 1 ≤ F.top) (B : LevelForm F j) (y : F.Site (j + 1))
    (k l : Fin 4) :
    plaquetteCurl (lineAverage B) y k l = (1 / (F.blockSide : ℝ) ^ 4) *
      ∑ h ∈ centredCube F.blockSide, ∑ m ∈ Finset.range F.blockSide, ∑ m' ∈ Finset.range F.blockSide,
        plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
          axisOffset j l (m' : ℤ)) k l := by
  have e : ∀ h, ∑ m ∈ Finset.range F.blockSide, ∑ m' ∈ Finset.range F.blockSide,
      plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
        axisOffset j l (m' : ℤ)) k l =
      lineSum B (BlockAverages.refineSite y + siteOfCoords j h) k F.blockSide +
        lineSum B (BlockAverages.refineSite (y + unitStep (j + 1) k) + siteOfCoords j h) l F.blockSide
        - lineSum B (BlockAverages.refineSite (y + unitStep (j + 1) l) + siteOfCoords j h) k F.blockSide
        - lineSum B (BlockAverages.refineSite y + siteOfCoords j h) l F.blockSide := by
    intro h
    rw [sum_plaquetteCurl_square, blockRefine_add_unitStep hj, blockRefine_add_unitStep hj,
      add_right_comm (BlockAverages.refineSite y) (axisOffset j k _),
      add_right_comm (BlockAverages.refineSite y) (axisOffset j l _)]
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  show lineAverage B y k + lineAverage B (y + unitStep (j + 1) k) l -
    lineAverage B (y + unitStep (j + 1) l) k - lineAverage B y l = _
  rw [lineAverage_eq_lineSum, lineAverage_eq_lineSum, lineAverage_eq_lineSum, lineAverage_eq_lineSum]
  ring
theorem sum_blocks_squares (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j + 1 ≤ F.top)
    (k l : Fin 4) (G : F.Site j → ℝ) :
    ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ m ∈ Finset.range F.blockSide,
        ∑ m' ∈ Finset.range F.blockSide,
        G (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) =
      (F.blockSide : ℝ) ^ 2 * ∑ x ∈ allSites F j, G x := by
  have hj' : j ≤ F.top := by omega
  rw [sum_blocks_lines hL hs hj k
    (fun x => ∑ m' ∈ Finset.range F.blockSide, G (x + axisOffset j l (m' : ℤ))), Finset.sum_comm]
  have e : ∀ m' : ℕ, ∑ x ∈ allSites F j, G (x + axisOffset j l (m' : ℤ)) = ∑ x ∈ allSites F j, G x :=
    fun m' => sum_allSites_add_right hL hs hj' _ G
  simp only [e]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring
theorem sum_sq_plaquetteCurl_lineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top) (k l : Fin 4) (u : F.Site (j + 1) → ℝ) (v : F.Site j → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (B : LevelForm F j)
    (hw : ∀ y, ∀ h ∈ centredCube F.blockSide, ∀ m ∈ Finset.range F.blockSide, ∀ m' ∈ Finset.range F.blockSide,
      u y ^ 2 ≤ κ * v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
        axisOffset j l (m' : ℤ)) ^ 2) :
    ∑ y ∈ allSites F (j + 1), (u y * plaquetteCurl (lineAverage B) y k l) ^ 2 ≤
      κ * ∑ x ∈ allSites F j, (v x * plaquetteCurl B x k l) ^ 2 := by
  obtain ⟨a, ha⟩ := id hL
  have hLr : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube ha]
    push_cast
    rfl
  have hy : ∀ y, (u y * plaquetteCurl (lineAverage B) y k l) ^ 2 ≤ κ / (F.blockSide : ℝ) ^ 2 *
      ∑ h ∈ centredCube F.blockSide, ∑ m ∈ Finset.range F.blockSide, ∑ m' ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) *
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
            axisOffset j l (m' : ℤ)) k l) ^ 2 := by
    intro y
    rw [plaquetteCurl_lineAverage hj]
    set t := Finset.range F.blockSide ×ˢ Finset.range F.blockSide with ht
    have ec : ∀ g : ℕ → ℕ → ℝ, ∑ m ∈ Finset.range F.blockSide, ∑ m' ∈ Finset.range F.blockSide, g m m' =
        ∑ p ∈ t, g p.1 p.2 := fun g => (Finset.sum_product _ _ (fun p => g p.1 p.2)).symm
    have hct : (t.card : ℝ) = (F.blockSide : ℝ) ^ 2 := by
      rw [ht, Finset.card_product, Finset.card_range]
      push_cast
      ring
    simp only [ec]
    have c1 := sq_sum_sum_le_card_mul (centredCube F.blockSide) t
      (fun h p => plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
        axisOffset j l (p.2 : ℤ)) k l)
    rw [hc, hct] at c1
    have c2 : u y ^ 2 * ∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l ^ 2 ≤
        κ * ∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) + axisOffset j l (p.2 : ℤ)) *
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      rw [mul_pow, ← mul_assoc]
      have hp' := Finset.mem_product.1 hp
      exact mul_le_mul_of_nonneg_right (hw y h hh p.1 hp'.1 p.2 hp'.2) (sq_nonneg _)
    have hu := sq_nonneg (u y)
    calc _ = u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) * (∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l) ^ 2 := by
          field_simp
      _ ≤ u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) * (((F.blockSide : ℝ) ^ 4 * (F.blockSide : ℝ) ^ 2) *
          ∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l ^ 2) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ = (1 / (F.blockSide : ℝ) ^ 2) * (u y ^ 2 * ∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l ^ 2) := by
          field_simp
      _ ≤ (1 / (F.blockSide : ℝ) ^ 2) * (κ * ∑ h ∈ centredCube F.blockSide, ∑ p ∈ t,
          (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) + axisOffset j l (p.2 : ℤ)) *
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (p.1 : ℤ) +
            axisOffset j l (p.2 : ℤ)) k l) ^ 2) :=
          mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = _ := by
          field_simp
  calc _ ≤ ∑ y ∈ allSites F (j + 1), κ / (F.blockSide : ℝ) ^ 2 *
      ∑ h ∈ centredCube F.blockSide, ∑ m ∈ Finset.range F.blockSide, ∑ m' ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) *
          plaquetteCurl B (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
            axisOffset j l (m' : ℤ)) k l) ^ 2 :=
        Finset.sum_le_sum fun y _ => hy y
    _ = κ / (F.blockSide : ℝ) ^ 2 *
        ((F.blockSide : ℝ) ^ 2 * ∑ x ∈ allSites F j, (v x * plaquetteCurl B x k l) ^ 2) := by
        rw [← Finset.mul_sum, sum_blocks_squares hL hs hj k l (fun x => (v x * plaquetteCurl B x k l) ^ 2)]
    _ = _ := by
        field_simp
theorem weightedCurlNormSq_lineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top)
    (u : F.Site (j + 1) → ℝ) (v : F.Site j → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (B : LevelForm F j)
    (hw : ∀ k l y, ∀ h ∈ centredCube F.blockSide, ∀ m ∈ Finset.range F.blockSide,
      ∀ m' ∈ Finset.range F.blockSide,
      u y ^ 2 ≤ κ * v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (m : ℤ) +
        axisOffset j l (m' : ℤ)) ^ 2) :
    weightedCurlNormSq u (lineAverage B) ≤ κ * weightedCurlNormSq v B := by
  unfold weightedCurlNormSq
  rw [Finset.sum_comm, Finset.sum_comm (s := allSites F j), Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  exact sum_sq_plaquetteCurl_lineAverage_le hL hs hj e.1 e.2 u v κ hκ B (hw e.1 e.2)
theorem sum_range_mul_eq (M L : ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ Finset.range (M * L), f l =
      ∑ l₁ ∈ Finset.range L, ∑ l₂ ∈ Finset.range M, f (M * l₁ + l₂) := by apply _root_.YangMills.Construction.BlockSpin.AverageComposition.sum_range_mul_eq_sum_sum <;> assumption
theorem sum_centredCube_mul {M L a b : ℕ} (hM : M = 2 * a + 1) (hL : L = 2 * b + 1)
    (f : (Fin 4 → ℤ) → ℝ) :
    ∑ h ∈ centredCube (M * L), f h =
      ∑ h₁ ∈ centredCube L, ∑ h₂ ∈ centredCube M, f (fun i => (M : ℤ) * h₁ i + h₂ i) := by
  have hML : M * L = 2 * (2 * a * b + a + b) + 1 := by
    rw [hM, hL]
    ring
  have hMz : (M : ℤ) = 2 * a + 1 := by exact_mod_cast hM
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun p => fun i => (M : ℤ) * p.1 i + p.2 i) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨h₁, h₂⟩ hp
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    rw [mem_centredCube_iff hML]
    rw [mem_centredCube_iff hL] at p1
    rw [mem_centredCube_iff hM] at p2
    intro i
    have q1 := p1 i
    have q2 := p2 i
    rw [hMz]
    push_cast
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩ hp ⟨h₁', h₂'⟩ hp' he
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    obtain ⟨p1', p2'⟩ := Finset.mem_product.1 hp'
    rw [mem_centredCube_iff hM] at p2 p2'
    have e2 : h₂ = h₂' := by
      funext i
      have ei := congrFun he i
      have q : -(a : ℤ) ≤ h₂ i ∧ h₂ i ≤ a := p2 i
      have q' : -(a : ℤ) ≤ h₂' i ∧ h₂' i ≤ a := p2' i
      have d : (M : ℤ) ∣ h₂ i - h₂' i := ⟨h₁' i - h₁ i, by linear_combination ei⟩
      have h0 : h₂ i - h₂' i = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd d
        rw [hMz, abs_lt]
        constructor <;> omega
      omega
    have e1 : h₁ = h₁' := by
      funext i
      have ei := congrFun he i
      have ei2 : (M : ℤ) * h₁ i + h₂ i = (M : ℤ) * h₁' i + h₂' i := ei
      rw [e2] at ei2
      have hne : (M : ℤ) ≠ 0 := by
        rw [hMz]
        omega
      exact mul_left_cancel₀ hne (by linarith)
    rw [e1, e2]
  · intro h hh
    rw [Finset.mem_coe, mem_centredCube_iff hML] at hh
    have hMp : (0 : ℤ) < M := by
      rw [hMz]
      omega
    refine ⟨(fun i => (h i + a) / (M : ℤ), fun i => h i - (M : ℤ) * ((h i + a) / (M : ℤ))), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product]
      constructor
      · show (fun i => (h i + a) / (M : ℤ)) ∈ centredCube L
        rw [mem_centredCube_iff hL]
        intro i
        have e1 := Int.emod_add_mul_ediv (h i + a) (M : ℤ)
        have e2 := Int.emod_nonneg (h i + a) hMp.ne'
        have e3 := Int.emod_lt_of_pos (h i + a) hMp
        have q := hh i
        push_cast at q
        show -(b : ℤ) ≤ (h i + a) / (M : ℤ) ∧ (h i + a) / (M : ℤ) ≤ b
        set d := (h i + a) / (M : ℤ)
        set r := (h i + a) % (M : ℤ)
        rw [hMz] at e1 e3
        constructor
        · by_contra hc
          have : d ≤ -(b : ℤ) - 1 := by omega
          nlinarith
        · by_contra hc
          have : (b : ℤ) + 1 ≤ d := by omega
          nlinarith
      · show (fun i => h i - (M : ℤ) * ((h i + a) / (M : ℤ))) ∈ centredCube M
        rw [mem_centredCube_iff hM]
        intro i
        have e1 := Int.emod_add_mul_ediv (h i + a) (M : ℤ)
        have e2 := Int.emod_nonneg (h i + a) hMp.ne'
        have e3 := Int.emod_lt_of_pos (h i + a) hMp
        show -(a : ℤ) ≤ h i - (M : ℤ) * ((h i + a) / (M : ℤ)) ∧
          h i - (M : ℤ) * ((h i + a) / (M : ℤ)) ≤ a
        constructor <;> linarith
    · funext i
      simp only
      ring
theorem centredCube_one : centredCube 1 = {0} := by apply _root_.YangMills.Construction.TorusChain.centredCube_one <;> assumption
theorem refineSite_self {j : ℕ} (y : F.Site j) : ColdStepAtMirrorFrames.refineSite j j y = y := by
  unfold ColdStepAtMirrorFrames.refineSite
  simp only [Nat.sub_self, pow_zero, one_mul]
  exact siteOfCoords_siteCoords y
def iteratedBlockAverage (φ : F.Site 0 → ℝ) : (j : ℕ) → F.Site j → ℝ
  | 0 => φ
  | j + 1 => blockAverage (iteratedBlockAverage φ j)
theorem blockRefine_add_siteOfCoords_eq {j : ℕ} (y : F.Site (j + 1)) (h : Fin 4 → ℤ) :
    BlockAverages.refineSite y + siteOfCoords j h =
      siteOfCoords j fun i => (F.blockSide : ℤ) * siteCoords y i + h i := by
  unfold BlockAverages.refineSite
  rw [← siteOfCoords_add]
  rfl
theorem iteratedBlockAverage_eq (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (φ : F.Site 0 → ℝ)
    (y : F.Site j) :
    iteratedBlockAverage φ j y = (1 / ((F.blockSide ^ j : ℕ) : ℝ) ^ 4) *
      ∑ h ∈ centredCube (F.blockSide ^ j),
        φ (ColdStepAtMirrorFrames.refineSite 0 j y + siteOfCoords 0 h) := by
  induction j with
  | zero =>
    simp only [pow_zero, centredCube_one, Finset.sum_singleton, siteOfCoords_zero, add_zero, refineSite_self]
    simp [iteratedBlockAverage]
  | succ j ih =>
    have hj' : j ≤ F.top := by omega
    obtain ⟨a, ha⟩ := hL.pow (n := j)
    obtain ⟨b, hb⟩ := id hL
    show blockAverage (iteratedBlockAverage φ j) y = _
    unfold blockAverage
    simp only [ih hj']
    have hLne : (F.blockSide : ℝ) ≠ 0 := by
      have : 0 < F.blockSide := hL.pos
      positivity
    have hp : F.blockSide ^ (j + 1) = F.blockSide ^ j * F.blockSide := pow_succ _ _
    rw [hp, sum_centredCube_mul ha hb]
    have e : ∀ h₁ h₂ : Fin 4 → ℤ,
        ColdStepAtMirrorFrames.refineSite 0 j (BlockAverages.refineSite y + siteOfCoords j h₁) +
          siteOfCoords 0 h₂ =
        ColdStepAtMirrorFrames.refineSite 0 (j + 1) y +
          siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) * h₁ i + h₂ i) := by
      intro h₁ h₂
      rw [blockRefine_add_siteOfCoords_eq, refineSite_siteOfCoords (Nat.zero_le j) hj', ← siteOfCoords_add]
      unfold ColdStepAtMirrorFrames.refineSite
      rw [← siteOfCoords_add]
      congr 1
      funext i
      simp only [Pi.add_apply, Nat.sub_zero]
      push_cast
      ring
    simp only [e]
    rw [← Finset.mul_sum]
    push_cast
    field_simp
theorem iteratedLineAverage_eq (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (B : LevelForm F 0)
    (y : F.Site j) (k : Fin 4) :
    iteratedLineAverage B j y k = (1 / ((F.blockSide ^ j : ℕ) : ℝ) ^ 4) *
      ∑ h ∈ centredCube (F.blockSide ^ j),
        lineSum B (ColdStepAtMirrorFrames.refineSite 0 j y + siteOfCoords 0 h) k (F.blockSide ^ j) := by
  induction j with
  | zero =>
    simp only [pow_zero, centredCube_one, Finset.sum_singleton, siteOfCoords_zero, add_zero, refineSite_self]
    simp [iteratedLineAverage, lineSum, axisOffset_zero]
  | succ j ih =>
    have hj' : j ≤ F.top := by omega
    obtain ⟨a, ha⟩ := hL.pow (n := j)
    obtain ⟨b, hb⟩ := id hL
    show lineAverage (iteratedLineAverage B j) y k = _
    unfold lineAverage
    simp only [ih hj']
    have hLne : (F.blockSide : ℝ) ≠ 0 := by
      have : 0 < F.blockSide := hL.pos
      positivity
    have hp : F.blockSide ^ (j + 1) = F.blockSide ^ j * F.blockSide := pow_succ _ _
    rw [hp, sum_centredCube_mul ha hb]
    unfold lineSum
    simp only [sum_range_mul_eq]
    have e : ∀ (h₁ h₂ : Fin 4 → ℤ) (l₁ l₂ : ℕ),
        ColdStepAtMirrorFrames.refineSite 0 j (BlockAverages.refineSite y + siteOfCoords j h₁ +
          siteOfCoords j (Pi.single k (l₁ : ℤ))) + siteOfCoords 0 h₂ + axisOffset 0 k (l₂ : ℤ) =
        ColdStepAtMirrorFrames.refineSite 0 (j + 1) y +
          siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) * h₁ i + h₂ i) +
          axisOffset 0 k ((F.blockSide ^ j * l₁ + l₂ : ℕ) : ℤ) := by
      intro h₁ h₂ l₁ l₂
      rw [blockRefine_add_siteOfCoords_eq, ← siteOfCoords_add, refineSite_siteOfCoords (Nat.zero_le j) hj']
      unfold ColdStepAtMirrorFrames.refineSite axisOffset
      rw [← siteOfCoords_add, ← siteOfCoords_add, ← siteOfCoords_add, ← siteOfCoords_add]
      congr 1
      funext i
      by_cases hik : i = k
      · subst hik
        simp only [Pi.add_apply, Nat.sub_zero, Pi.single_eq_same]
        push_cast
        ring
      · simp only [Pi.add_apply, Nat.sub_zero, Pi.single_eq_of_ne hik]
        push_cast
        ring
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h₁ _ => ?_
    simp only [Finset.mul_sum, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h₂ _ => ?_
    refine Finset.sum_congr rfl fun l₁ _ => ?_
    refine Finset.sum_congr rfl fun l₂ _ => ?_
    push_cast
    field_simp
end
end YangMills.Construction.ColdStepAtMirrorFrames
