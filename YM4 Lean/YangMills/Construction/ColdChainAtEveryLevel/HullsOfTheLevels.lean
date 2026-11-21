import YangMills.Construction.ColdChainAtEveryLevel.ComplexLevels
import YangMills.Construction.ColdChainAtEveryLevel.WeightedRecursion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HullBounds
open BlockAverages LevelRecursion ComplexLevels ComplexRemainders BlockLines LatticePaths WeightedAverages
  WeightedAverages.Chains LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
def blockBondPairs (L : ℕ) : Finset (Lattice4 × Fin 4) :=
  (centredCube L ×ˢ Finset.univ).filter fun q => q.1 + Pi.single q.2 1 ∈ centredCube L
theorem bondHullSum_eq_sum (c : F.Site (j + 1) × Fin 4) (f : F.Site j → Fin 4 → ℝ) :
    bondHullSum c f = ∑ q ∈ blockBondPairs F.blockSide, f (refineSite c.1 + siteOfCoords j q.1) q.2 +
      ∑ q ∈ blockBondPairs F.blockSide, f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2 +
      ∑ q ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
        f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 := by
  have hA : ∀ ψ : Lattice4 × Fin 4 → ℝ, ∑ q ∈ blockBondPairs F.blockSide, ψ q =
      ∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4,
        if h + Pi.single k 1 ∈ centredCube F.blockSide then ψ (h, k) else 0 := by
    intro ψ
    unfold blockBondPairs
    rw [Finset.sum_filter, Finset.sum_product]
  unfold bondHullSum
  have hB : ∑ q ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
      f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 =
      ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, f (lineBond c h r).1 (lineBond c h r).2 :=
    Finset.sum_product _ _ (fun q : Lattice4 × ℕ => f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2)
  rw [hA (fun q => f (refineSite c.1 + siteOfCoords j q.1) q.2),
    hA (fun q => f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2), hB]
  have e1 : ∀ (h : Lattice4) (k : Fin 4), (if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else (0 : ℝ)) =
      (if h + Pi.single k 1 ∈ centredCube F.blockSide then f (refineSite c.1 + siteOfCoords j h) k else 0) +
      (if h + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) := by
    intro h k
    split_ifs <;> simp
  simp only [e1, Finset.sum_add_distrib]
theorem card_blockBondPairs_le (hodd : Odd F.blockSide) :
    ((blockBondPairs F.blockSide).card : ℝ) ≤ 4 * (F.blockSide : ℝ) ^ 4 := by
  have h1 : (blockBondPairs F.blockSide).card ≤
      (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))).card := Finset.card_filter_le _ _
  rw [Finset.card_product, card_centredCube hodd, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((blockBondPairs F.blockSide).card : ℝ) ≤ ((F.blockSide ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith
theorem sum_pow_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (P : ℕ)
    (hP : 1 ≤ P) {H : ℝ} (hH : (s.card : ℝ) ≤ H) : (∑ i ∈ s, f i) ^ P ≤ H ^ (P - 1) * ∑ i ∈ s, f i ^ P := by
  have h := sum_pow_le_of_pos_weights s f (fun _ => 1) hf (fun _ _ => one_pos) P hP
  simp only [inv_one, one_pow, mul_one, Finset.sum_const, nsmul_eq_mul] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) _)
  exact pow_le_pow_left₀ (by positivity) hH _
theorem bondHullSum_pow_le (hodd : Odd F.blockSide) (c : F.Site (j + 1) × Fin 4) {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x d, 0 ≤ f x d) (P : ℕ) (hP : 1 ≤ P) :
    bondHullSum c f ^ P ≤ (3 * hullBondCount F.blockSide) ^ (P - 1) * bondHullSum c (fun x d => f x d ^ P) := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hL4 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := by positivity
  have hL5 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := by positivity
  set H := hullBondCount F.blockSide with hH
  have hHe : H = 8 * (F.blockSide : ℝ) ^ 4 + (F.blockSide : ℝ) ^ 5 := rfl
  have hc1 : ((blockBondPairs F.blockSide).card : ℝ) ≤ H := by
    have := card_blockBondPairs_le hodd
    linarith
  have hc2 : ((centredCube F.blockSide ×ˢ Finset.range F.blockSide).card : ℝ) ≤ H := by
    rw [Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    have : (F.blockSide : ℝ) ^ 4 * F.blockSide = (F.blockSide : ℝ) ^ 5 := by ring
    linarith
  set x₁ := ∑ q ∈ blockBondPairs F.blockSide, f (refineSite c.1 + siteOfCoords j q.1) q.2 with hx₁
  set x₂ := ∑ q ∈ blockBondPairs F.blockSide,
    f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2 with hx₂
  set x₃ := ∑ q ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
    f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 with hx₃
  have h1 := sum_pow_le_card_mul (blockBondPairs F.blockSide) (fun q => f (refineSite c.1 + siteOfCoords j q.1) q.2)
    (fun _ _ => hf _ _) P hP hc1
  have h2 := sum_pow_le_card_mul (blockBondPairs F.blockSide)
    (fun q => f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2)
    (fun _ _ => hf _ _) P hP hc1
  have h3 := sum_pow_le_card_mul (centredCube F.blockSide ×ˢ Finset.range F.blockSide)
    (fun q => f (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2) (fun _ _ => hf _ _) P hP hc2
  have hn1 : 0 ≤ x₁ := Finset.sum_nonneg fun _ _ => hf _ _
  have hn2 : 0 ≤ x₂ := Finset.sum_nonneg fun _ _ => hf _ _
  have hn3 : 0 ≤ x₃ := Finset.sum_nonneg fun _ _ => hf _ _
  have h4 := sum_pow_le_card_mul (Finset.univ : Finset (Fin 3)) ![x₁, x₂, x₃] (fun i _ => by
    fin_cases i <;> simp [hn1, hn2, hn3]) P hP (H := 3) (by simp)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h4
  rw [bondHullSum_eq_sum, bondHullSum_eq_sum, ← hx₁, ← hx₂, ← hx₃]
  refine h4.trans ?_
  rw [mul_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hH00 : 0 ≤ H := by
    rw [hHe]
    positivity
  have := mul_add (H ^ (P - 1)) (∑ i ∈ blockBondPairs F.blockSide, f (refineSite c.1 + siteOfCoords j i.1) i.2 ^ P +
    ∑ i ∈ blockBondPairs F.blockSide, f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j i.1) i.2 ^ P)
    (∑ i ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide, f (lineBond c i.1 i.2).1 (lineBond c i.1 i.2).2 ^ P)
  rw [this, mul_add]
  linarith
theorem sum_comp_le_of_injOn {α β : Type} (Y : Finset α) (Z : Finset β) (φ : α → β) (hinj : Set.InjOn φ Y)
    (hmap : ∀ c ∈ Y, φ c ∈ Z) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) : ∑ c ∈ Y, g (φ c) ≤ ∑ b ∈ Z, g b := by
  classical
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hg b
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
  exact hmap c hc
theorem sum_shifted_innerBonds_le {D : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    {G : F.Site j × Fin 4 → ℝ} (hG : ∀ b, 0 ≤ G b) {h : Lattice4} {k : Fin 4} (hh : h ∈ centredCube F.blockSide)
    (hk : h + Pi.single k 1 ∈ centredCube F.blockSide) :
    ∑ c ∈ innerBonds D (j + 1), G (refineSite c.1 + siteOfCoords j h, k) ≤ 4 * ∑ b ∈ innerBonds D j, G b ∧
      ∑ c ∈ innerBonds D (j + 1), G (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h, k) ≤
        4 * ∑ b ∈ innerBonds D j, G b := by
  classical
  have hs : ∀ φ : F.Site (j + 1) × Fin 4 → F.Site j × Fin 4,
      (∀ d : Fin 4, Set.InjOn φ ((innerBonds D (j + 1)).filter fun c => c.2 = d : Finset _)) →
      (∀ c ∈ innerBonds D (j + 1), φ c ∈ innerBonds D j) →
        ∑ c ∈ innerBonds D (j + 1), G (φ c) ≤ 4 * ∑ b ∈ innerBonds D j, G b := by
    intro φ hinj hmap
    rw [← Finset.sum_fiberwise (s := innerBonds D (j + 1)) (g := fun c => c.2) (f := fun c => G (φ c))]
    refine (Finset.sum_le_card_nsmul _ _ (∑ b ∈ innerBonds D j, G b) fun d _ => ?_).trans ?_
    · exact sum_comp_le_of_injOn _ _ φ (hinj d) (fun c hc => hmap c (Finset.mem_filter.1 hc).1) G hG
    · simp
  constructor
  · refine hs (fun c => (refineSite c.1 + siteOfCoords j h, k)) (fun d c hc c' hc' e => ?_) fun c hc => ?_
    · have e1 : refineSite c.1 + siteOfCoords j h = refineSite c'.1 + siteOfCoords j h := congrArg Prod.fst e
      obtain ⟨a, -⟩ := refineSite_add_injective hj hodd c.1 c'.1 h h hh hh e1
      have hc1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
      have hc2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
      exact Prod.ext a (hc1.trans hc2.symm)
    · exact bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc h k (mem_twoBlockHull_of_mem_centredCube hh _)
        (mem_twoBlockHull_of_mem_centredCube hk _)
  · refine hs (fun c => (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h, k))
      (fun d c hc c' hc' e => ?_) fun c hc => ?_
    · have e1 : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
          refineSite (c'.1 + unitStep (j + 1) c'.2) + siteOfCoords j h :=
        congrArg Prod.fst e
      obtain ⟨a, -⟩ := refineSite_add_injective hj hodd _ _ h h hh hh e1
      have hc1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
      have hc2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
      have hd : c.2 = c'.2 := hc1.trans hc2.symm
      rw [hd] at a
      exact Prod.ext (add_right_cancel a) hd
    · have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
          refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + h) := by
        rw [refineSite_add_unitStep hj, siteOfCoords_add, add_assoc]
      show (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h, k) ∈ innerBonds D j
      rw [e]
      refine bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc _ k (shift_mem_twoBlockHull hh _) ?_
      have e2 : (F.blockSide : ℤ) • basisVector c.2 + h + basisVector k =
          (F.blockSide : ℤ) • basisVector c.2 + (h + Pi.single k 1) := by
        rw [add_assoc]
        rfl
      rw [e2]
      exact shift_mem_twoBlockHull hk _
theorem sum_bondHullSum_le {D : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    {g : F.Site j → Fin 4 → ℝ} (hg : ∀ x d, 0 ≤ g x d) :
    ∑ c ∈ innerBonds D (j + 1), bondHullSum c g ≤
      (32 * (F.blockSide : ℝ) ^ 4 + F.blockSide) * ∑ b ∈ innerBonds D j, g b.1 b.2 := by
  set S := ∑ b ∈ innerBonds D j, g b.1 b.2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => hg _ _
  have hq : ∀ q ∈ blockBondPairs F.blockSide,
      q.1 ∈ centredCube F.blockSide ∧ q.1 + Pi.single q.2 1 ∈ centredCube F.blockSide := fun q hq => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
    exact ⟨(Finset.mem_product.1 h1).1, h2⟩
  simp only [bondHullSum_eq_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm,
    Finset.sum_comm (s := innerBonds D (j + 1)) (t := blockBondPairs F.blockSide)
      (f := fun c q => g (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2)]
  have hb1 : ∑ q ∈ blockBondPairs F.blockSide, ∑ c ∈ innerBonds D (j + 1),
      g (refineSite c.1 + siteOfCoords j q.1) q.2 ≤ (blockBondPairs F.blockSide).card * (4 * S) := by
    have := Finset.sum_le_card_nsmul (blockBondPairs F.blockSide) _ (4 * S) fun q hqm =>
      (sum_shifted_innerBonds_le (D := D) hj hodd (G := fun b => g b.1 b.2) (fun _ => hg _ _)
        (hq q hqm).1 (hq q hqm).2).1
    simpa using this
  have hb2 : ∑ q ∈ blockBondPairs F.blockSide, ∑ c ∈ innerBonds D (j + 1),
      g (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j q.1) q.2 ≤
        (blockBondPairs F.blockSide).card * (4 * S) := by
    have := Finset.sum_le_card_nsmul (blockBondPairs F.blockSide) _ (4 * S) fun q hqm =>
      (sum_shifted_innerBonds_le (D := D) hj hodd (G := fun b => g b.1 b.2) (fun _ => hg _ _)
        (hq q hqm).1 (hq q hqm).2).2
    simpa using this
  have hb3 : ∑ c ∈ innerBonds D (j + 1), ∑ q ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
      g (lineBond c q.1 q.2).1 (lineBond c q.1 q.2).2 ≤ F.blockSide * S := by
    have := sum_lineBond_sum_le (B := D) hj hodd (innerBonds D (j + 1)) subset_rfl (fun b => g b.1 b.2)
      (fun _ => hg _ _)
    simp only [Finset.sum_product]
    exact this
  have hcard := card_blockBondPairs_le hodd
  have hc4 : ((blockBondPairs F.blockSide).card : ℝ) * (4 * S) ≤ 4 * (F.blockSide : ℝ) ^ 4 * (4 * S) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  nlinarith
section ScaleRatios
theorem scaleRadius_ratio (hodd : Odd F.blockSide) {l : ℕ} (hl : l < F.top) (y : F.Site (l + 1)) (g : Lattice4)
    (hg : ∀ i, (g i).natAbs ≤ 2 * F.blockSide) (p : F.Site 0) :
    scaleRadius F (l + 1) p y ≤ (1 + 3 * (F.blockSide : ℝ)) * scaleRadius F l p (refineSite y + siteOfCoords l g) ∧
      scaleRadius F l p (refineSite y + siteOfCoords l g) ≤ 3 * scaleRadius F (l + 1) p y := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨a, b⟩ := baseDistance_refineSite_add hl y g (2 * F.blockSide) hg p
  set dx : ℝ := ((baseDistance (refineSite y + siteOfCoords l g) p : ℕ) : ℝ) with hdx
  set dy : ℝ := ((baseDistance y p : ℕ) : ℝ) with hdy
  set B : ℝ := (F.blockSide : ℝ) ^ l with hB
  have hBpos : 0 < B := by positivity
  have e1 : (F.blockSide : ℝ) ^ (l + 1) = B * F.blockSide := pow_succ _ _
  have hc : ((F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) = 2 * (B * F.blockSide) := by
    push_cast
    ring
  have a' : dx ≤ dy + 2 * (B * F.blockSide) := by
    have : ((baseDistance (refineSite y + siteOfCoords l g) p : ℕ) : ℝ) ≤
        ((baseDistance y p + F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) := by
      exact_mod_cast a
    rw [Nat.cast_add, hc] at this
    exact this
  have b' : dy ≤ dx + 2 * (B * F.blockSide) := by
    have : ((baseDistance y p : ℕ) : ℝ) ≤
        ((baseDistance (refineSite y + siteOfCoords l g) p + F.blockSide ^ l * (2 * F.blockSide) : ℕ) : ℝ) := by
      exact_mod_cast b
    rw [Nat.cast_add, hc] at this
    exact this
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hNpos : 0 < N := by positivity
  have hBL : B ≤ B * F.blockSide := by nlinarith
  have e2 : scaleRadius F (l + 1) p y = min N (max (B * F.blockSide) dy) := by
    simp only [scaleRadius]
    rw [e1]
  have e3 : scaleRadius F l p (refineSite y + siteOfCoords l g) = min N (max B dx) := rfl
  rw [e2, e3]
  constructor
  · set m := max B dx with hm
    have hmB : B ≤ m := le_max_left _ _
    have hmx : dx ≤ m := le_max_right _ _
    rcases le_total N m with h | h
    · rw [min_eq_left h]
      have : min N (max (B * F.blockSide) dy) ≤ N := min_le_left _ _
      nlinarith
    · rw [min_eq_right h]
      have h3 : min N (max (B * F.blockSide) dy) ≤ max (B * F.blockSide) dy := min_le_right _ _
      have h4 : B * F.blockSide ≤ m * F.blockSide := mul_le_mul_of_nonneg_right hmB (by linarith)
      have h5 : max (B * F.blockSide) dy ≤ (1 + 3 * (F.blockSide : ℝ)) * m := by
        refine max_le ?_ ?_
        · nlinarith
        · nlinarith
      linarith
  · set m := max (B * F.blockSide) dy with hm
    have hmB : B * F.blockSide ≤ m := le_max_left _ _
    have hmy : dy ≤ m := le_max_right _ _
    rcases le_total N m with h | h
    · rw [min_eq_left h]
      have : min N (max B dx) ≤ N := min_le_left _ _
      linarith
    · rw [min_eq_right h]
      have h3 : min N (max B dx) ≤ max B dx := min_le_right _ _
      have h5 : max B dx ≤ 3 * m := by
        refine max_le ?_ ?_
        · linarith
        · linarith
      linarith
theorem scaleWeight_ratio_le (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {l : ℕ} (hl : l < F.top)
    (y : F.Site (l + 1)) (g : Lattice4) (hg : ∀ i, (g i).natAbs ≤ 2 * F.blockSide) (p : F.Site 0) :
    scaleWeight p θ (l + 1) y ≤ 4 * (F.blockSide : ℝ) * scaleWeight p θ l (refineSite y + siteOfCoords l g) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨h1, h2⟩ := scaleRadius_ratio hodd hl y g hg p
  set ρ₁ := scaleRadius F (l + 1) p y with hρ₁
  set ρ₀ := scaleRadius F l p (refineSite y + siteOfCoords l g) with hρ₀
  have p₁ : 0 < ρ₁ := scaleRadius_pos hodd.pos _ _ _
  have p₀ : 0 < ρ₀ := scaleRadius_pos hodd.pos _ _ _
  have hθ1 := abs_le.1 hθ
  have key : ρ₁ ^ (-θ) = (ρ₀ / ρ₁) ^ θ * ρ₀ ^ (-θ) := by
    rw [Real.div_rpow p₀.le p₁.le, Real.rpow_neg p₁.le, Real.rpow_neg p₀.le]
    have a1 : ρ₀ ^ θ ≠ 0 := (Real.rpow_pos_of_pos p₀ _).ne'
    have a2 : ρ₁ ^ θ ≠ 0 := (Real.rpow_pos_of_pos p₁ _).ne'
    field_simp
  show ρ₁ ^ (-θ) ≤ 4 * (F.blockSide : ℝ) * ρ₀ ^ (-θ)
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg p₀.le _)
  rcases le_total 0 θ with h | h
  · have h3 : ρ₀ / ρ₁ ≤ 3 := by
      rw [div_le_iff₀ p₁]
      exact h2
    have h4 : (ρ₀ / ρ₁) ^ θ ≤ (3 : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) h3 h
    have h5 : (3 : ℝ) ^ θ ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 3) (by norm_num) (by linarith : θ ≤ 1)
      simpa using this
    linarith
  · have h3 : ρ₁ / ρ₀ ≤ 1 + 3 * (F.blockSide : ℝ) := by
      rw [div_le_iff₀ p₀]
      exact h1
    have e : (ρ₀ / ρ₁) ^ θ = (ρ₁ / ρ₀) ^ (-θ) := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    rw [e]
    have h4 : (ρ₁ / ρ₀) ^ (-θ) ≤ (1 + 3 * (F.blockSide : ℝ)) ^ (-θ) :=
      Real.rpow_le_rpow (by positivity) h3 (by linarith)
    have h5 : (1 + 3 * (F.blockSide : ℝ)) ^ (-θ) ≤ 1 + 3 * (F.blockSide : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 1 + 3 * (F.blockSide : ℝ)) (by linarith)
        (by linarith : -θ ≤ 1)
      simpa using this
    linarith
theorem bondHullSum_mono_of_holdsOnHull (c : F.Site (j + 1) × Fin 4) {f g : F.Site j → Fin 4 → ℝ}
    (h : HoldsOnHull c (fun x d => f x d ≤ g x d)) : bondHullSum c f ≤ bondHullSum c g := by
  refine add_le_add (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun d _ => ?_)
    (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun r hr => h.2 k hk r hr)
  split_ifs with hd
  · have := h.1 k hk d hd
    exact add_le_add this.1 this.2
  · exact le_rfl
theorem natAbs_le_of_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    (h i).natAbs ≤ L := by
  have := (mem_centredCube_iff L h).1 hh i
  omega
theorem scaleWeight_holdsOnHull (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (hj : j < F.top)
    (c : F.Site (j + 1) × Fin 4) (p : F.Site 0) {g : F.Site j → Fin 4 → ℝ} (hg : ∀ x d, 0 ≤ g x d) :
    HoldsOnHull c (fun x d => scaleWeight p θ (j + 1) c.1 * g x d ≤
      4 * (F.blockSide : ℝ) * (scaleWeight p θ j x * g x d)) := by
  have hL : 1 ≤ F.blockSide := hodd.pos
  have key : ∀ (G : Lattice4), (∀ i, (G i).natAbs ≤ 2 * F.blockSide) → ∀ d,
      scaleWeight p θ (j + 1) c.1 * g (refineSite c.1 + siteOfCoords j G) d ≤
        4 * (F.blockSide : ℝ) * (scaleWeight p θ j (refineSite c.1 + siteOfCoords j G) *
          g (refineSite c.1 + siteOfCoords j G) d) := by
    intro G hG d
    have h1 := scaleWeight_ratio_le hodd hθ hj c.1 G hG p
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (hg _ _)
  have hunit : ∀ (i μ : Fin 4), ((F.blockSide : ℤ) • basisVector i) μ = if μ = i then (F.blockSide : ℤ) else 0 := by
    intro i μ
    by_cases h : μ = i
    · subst h
      simp [basisVector]
    · simp [basisVector, h]
  refine ⟨fun h hh k _ => ⟨?_, ?_⟩, fun h hh r hr => ?_⟩
  · exact key h (fun i => by
      have := natAbs_le_of_mem_centredCube hh i
      omega) k
  · have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
        refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + h) := by
      rw [refineSite_add_unitStep hj, siteOfCoords_add, add_assoc]
    rw [e]
    refine key _ (fun i => ?_) k
    have h1 := natAbs_le_of_mem_centredCube hh i
    simp only [Pi.add_apply, hunit]
    split_ifs <;> omega
  · have e : (lineBond c h r).1 = refineSite c.1 + siteOfCoords j (h + (r : ℤ) • basisVector c.2) :=
      lineBond_fst c h r
    have e2 : (lineBond c h r).2 = c.2 := rfl
    rw [e, e2]
    refine key _ (fun i => ?_) c.2
    have h1 := natAbs_le_of_mem_centredCube hh i
    have hr' := Finset.mem_range.1 hr
    have e3 : ((r : ℤ) • basisVector c.2) i = if i = c.2 then (r : ℤ) else 0 := by
      by_cases h : i = c.2
      · subst h
        simp [basisVector]
      · simp [basisVector, h]
    simp only [Pi.add_apply, e3]
    split_ifs <;> omega
def hullFactor (L : ℕ) : ℝ := 4 * (L : ℝ) * (3 * hullBondCount L) * (32 * (L : ℝ) ^ 4 + L)
theorem one_le_hullFactor_parts (hodd : Odd F.blockSide) :
    1 ≤ 3 * hullBondCount F.blockSide ∧ 1 ≤ 32 * (F.blockSide : ℝ) ^ 4 + F.blockSide ∧
      1 ≤ 4 * (F.blockSide : ℝ) := by
  have hL : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have h4 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL
  have h5 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := one_le_pow₀ hL
  unfold hullBondCount
  refine ⟨by linarith, by linarith, by linarith⟩
theorem weightedScaleNorm_bondHullSum_le {D : Finset F.Cell} (hodd : Odd F.blockSide) {θ : ℝ} (hθ : |θ| ≤ 1 / 8)
    (hj : j < F.top) (p : F.Site 0) (P : ℕ) (hP : 1 ≤ P) {g : F.Site j → Fin 4 → ℝ} (hg : ∀ x d, 0 ≤ g x d) :
    weightedScaleNorm D p θ P (j + 1) (fun y d => bondHullSum (y, d) g) ≤
      hullFactor F.blockSide * weightedScaleNorm D p θ P j g := by
  obtain ⟨h3H, hM, h4L⟩ := one_le_hullFactor_parts (F := F) hodd
  set M := 32 * (F.blockSide : ℝ) ^ 4 + F.blockSide with hMd
  set W : F.Site j → Fin 4 → ℝ := fun x d => scaleWeight p θ j x * g x d with hW
  have hW0 : ∀ x d, 0 ≤ W x d := fun x d => mul_nonneg (scaleWeight_pos hodd p θ j x).le (hg x d)
  have hK : 0 ≤ hullFactor F.blockSide := by
    unfold hullFactor
    have : (0 : ℝ) ≤ hullBondCount F.blockSide := by
      unfold hullBondCount
      positivity
    positivity
  refine finsetLpNorm_le_of_sum_pow_le hP _ _ _ _ hK ?_
  have hone : ∀ c ∈ innerBonds D (j + 1), |scaleWeight p θ (j + 1) c.1 * bondHullSum (c.1, c.2) g| ^ P ≤
      (4 * (F.blockSide : ℝ)) ^ P *
        ((3 * hullBondCount F.blockSide) ^ (P - 1) * bondHullSum c (fun x d => W x d ^ P)) := by
    intro c _
    have hv := scaleWeight_pos hodd p θ (j + 1) c.1
    have hs : 0 ≤ bondHullSum c g := bondHullSum_nonneg c hg
    have e : (c.1, c.2) = c := rfl
    rw [e, abs_of_nonneg (by positivity)]
    have h1 := bondHullSum_mono_of_holdsOnHull c (scaleWeight_holdsOnHull hodd hθ hj c p hg)
    rw [bondHullSum_smul, bondHullSum_smul] at h1
    have h2 := bondHullSum_pow_le hodd c hW0 P hP
    calc _ ≤ (4 * (F.blockSide : ℝ) * bondHullSum c W) ^ P :=
          pow_le_pow_left₀ (by positivity) h1 P
      _ = (4 * (F.blockSide : ℝ)) ^ P * bondHullSum c W ^ P := by rw [mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsum := sum_bondHullSum_le (D := D) hj hodd (g := fun x d => W x d ^ P) (fun x d => pow_nonneg (hW0 x d) _)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have e : ∑ b ∈ innerBonds D j, |scaleWeight p θ j b.1 * g b.1 b.2| ^ P = ∑ b ∈ innerBonds D j, W b.1 b.2 ^ P := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [abs_of_nonneg (hW0 _ _)]
  rw [e]
  set Sg := ∑ b ∈ innerBonds D j, W b.1 b.2 ^ P with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun _ _ => pow_nonneg (hW0 _ _) _
  have hA : (3 * hullBondCount F.blockSide) ^ (P - 1) * M ≤ (3 * hullBondCount F.blockSide) ^ P * M ^ P := by
    have a1 : (3 * hullBondCount F.blockSide) ^ (P - 1) ≤ (3 * hullBondCount F.blockSide) ^ P :=
      pow_le_pow_right₀ h3H (by omega)
    have a2 : M ≤ M ^ P := by
      calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ P := pow_le_pow_right₀ hM hP
    exact mul_le_mul a1 a2 (by linarith) (by positivity)
  have hfac : hullFactor F.blockSide ^ P =
      (4 * (F.blockSide : ℝ)) ^ P * ((3 * hullBondCount F.blockSide) ^ P * M ^ P) := by
    unfold hullFactor
    rw [mul_pow, mul_pow]
    ring
  rw [hfac]
  calc (4 * (F.blockSide : ℝ)) ^ P * ((3 * hullBondCount F.blockSide) ^ (P - 1) *
        ∑ c ∈ innerBonds D (j + 1), bondHullSum c fun x d => W x d ^ P)
      ≤ (4 * (F.blockSide : ℝ)) ^ P * ((3 * hullBondCount F.blockSide) ^ (P - 1) * (M * Sg)) := by
        gcongr
    _ = (4 * (F.blockSide : ℝ)) ^ P * (((3 * hullBondCount F.blockSide) ^ (P - 1) * M) * Sg) := by ring
    _ ≤ (4 * (F.blockSide : ℝ)) ^ P * (((3 * hullBondCount F.blockSide) ^ P * M ^ P) * Sg) := by
        gcongr
    _ = _ := by ring
end ScaleRatios
section Closing
theorem finsetLpNorm_two_mul_le {ι : Type} (s : Finset ι) (x y : ι → ℝ) :
    finsetLpNorm 2 s (fun i => x i * y i) ≤ finsetLpNorm 4 s x * finsetLpNorm 4 s y := by
  rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_four_eq_sqrt_sqrt, finsetLpNorm_four_eq_sqrt_sqrt,
    ← Real.sqrt_mul (Real.sqrt_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => x i ^ 2) (fun i => y i ^ 2)
  have e : ∀ i, (x i * y i) ^ 2 = x i ^ 2 * y i ^ 2 := fun i => by ring
  simp only [e]
  refine h.trans (le_of_eq ?_)
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
theorem weightedScaleNorm_four_le_of_small (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell)
    (p : F.Site 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 8)
    (a : (m : ℕ) → F.Site m → Fin 4 → ℝ) (b e : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (ha : ∀ m x d, 0 ≤ a m x d) (hb : ∀ m y d, 0 ≤ b m y d) (he : ∀ m y d, 0 ≤ e m y d)
    (hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + (b m c.1 c.2 + e m c.1 c.2 * bondHullSum c (a m)))
    {ε S : ℝ} (hε0 : 0 ≤ ε) (hS0 : 0 ≤ S)
    (hε : ∀ m, m + 1 < F.top → finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => e m c.1 c.2) ≤ ε)
    (hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1) (b m) ≤ S)
    (hsmall : 568 * ε * hullFactor F.blockSide ≤ 1) (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m (a m) ≤ 2 * (20000 * weightedScaleNorm D p θ 4 0 (a 0) + 284 * S) := by
  set T := 2 * (20000 * weightedScaleNorm D p θ 4 0 (a 0) + 284 * S) with hT
  have hA0 : 0 ≤ weightedScaleNorm D p θ 4 0 (a 0) := finsetLpNorm_nonneg _ _ _
  have hT0 : 0 ≤ T := by positivity
  set K := hullFactor F.blockSide with hK
  have hK0 : 0 ≤ K := by
    obtain ⟨h3H, hM, h4L⟩ := one_le_hullFactor_parts (F := F) hodd
    have hL : (0 : ℝ) ≤ F.blockSide := by positivity
    rw [hK]
    unfold hullFactor
    have e1 : 0 ≤ 3 * hullBondCount F.blockSide := by linarith
    have e2 : 0 ≤ 32 * (F.blockSide : ℝ) ^ 4 + F.blockSide := by linarith
    positivity
  set s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ :=
    fun m y d => b m y d + e m y d * bondHullSum (y, d) (a m) with hs
  have hs0 : ∀ m y d, 0 ≤ s m y d := fun m y d =>
    add_nonneg (hb _ _ _) (mul_nonneg (he _ _ _) (bondHullSum_nonneg _ (ha m)))
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hB : ∀ i, i + 1 ≤ m → weightedScaleNorm D p θ 2 (i + 1) (s i) ≤ S + ε * (K * T) := by
      intro i hi
      have hin : i + 1 < F.top := by omega
      have h1 := finsetLpNorm_add_le (P := 2) (by norm_num) (innerBonds D (i + 1))
        (fun c => scaleWeight p θ (i + 1) c.1 * b i c.1 c.2)
        (fun c => e i c.1 c.2 * (scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)))
      have h3 := finsetLpNorm_two_mul_le (innerBonds D (i + 1)) (fun c => e i c.1 c.2)
        (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i))
      have h4 : finsetLpNorm 4 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) ≤ K * T := by
        have h5 := weightedScaleNorm_bondHullSum_le (D := D) hodd hθ (by omega : i < F.top) p 4 (by norm_num) (ha i)
        have h6 := ih i (by omega) (by omega)
        exact h5.trans (mul_le_mul_of_nonneg_left h6 hK0)
      have h7 : weightedScaleNorm D p θ 2 (i + 1) (s i) ≤ finsetLpNorm 2 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * b i c.1 c.2 +
            e i c.1 c.2 * (scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i))) := by
        refine le_of_eq ?_
        unfold weightedScaleNorm finsetLpNorm
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 2
        simp only [hs]
        ring
      have h8 : finsetLpNorm 4 (innerBonds D (i + 1)) (fun c => e i c.1 c.2) *
          finsetLpNorm 4 (innerBonds D (i + 1)) (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) ≤
            ε * (K * T) :=
        mul_le_mul (hε i hin) h4 (finsetLpNorm_nonneg _ _ _) hε0
      have h9 := hS i hin
      unfold weightedScaleNorm at h9
      exact h7.trans (h1.trans (by linarith))
    have hrec' : ∀ m', m' + 1 < F.top → ∀ c ∈ innerBonds D (m' + 1),
        a (m' + 1) c.1 c.2 ≤ lineBlockAverage (a m') c + s m' c.1 c.2 := fun m' hm' c hc => hrec m' hm' c hc
    have hmain := (weightedScaleNorm_le_of_recursion hodd h2 D p hθ a s ha hs0 hrec' m hB (by positivity) hm).1
    have h10 : 284 * (ε * (K * T)) ≤ T / 2 := by
      have : 568 * ε * K * T ≤ 1 * T := mul_le_mul_of_nonneg_right hsmall hT0
      nlinarith
    calc _ ≤ 20000 * weightedScaleNorm D p θ 4 0 (a 0) + 284 * (S + ε * (K * T)) := hmain
      _ ≤ T := by
          rw [hT] at h10 ⊢
          nlinarith
theorem weightedScaleNorm_two_le_of_small (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) (D : Finset F.Cell)
    (p : F.Site 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 8)
    (a : (m : ℕ) → F.Site m → Fin 4 → ℝ) (b e : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ)
    (ha : ∀ m x d, 0 ≤ a m x d) (hb : ∀ m y d, 0 ≤ b m y d) (he : ∀ m y d, 0 ≤ e m y d)
    (hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + (b m c.1 c.2 + e m c.1 c.2 * bondHullSum c (a m)))
    {ε S : ℝ} (hε0 : 0 ≤ ε) (hS0 : 0 ≤ S)
    (hε : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), e m c.1 c.2 ≤ ε)
    (hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1) (b m) ≤ S)
    (hsmall : 568 * ε * hullFactor F.blockSide ≤ 1) (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 2 m (a m) ≤ 2 * (142 * weightedScaleNorm D p θ 2 0 (a 0) + 284 * S) := by
  set T := 2 * (142 * weightedScaleNorm D p θ 2 0 (a 0) + 284 * S) with hT
  have hA0 : 0 ≤ weightedScaleNorm D p θ 2 0 (a 0) := finsetLpNorm_nonneg _ _ _
  have hT0 : 0 ≤ T := by positivity
  set K := hullFactor F.blockSide with hK
  have hK0 : 0 ≤ K := by
    obtain ⟨h3H, hM, h4L⟩ := one_le_hullFactor_parts (F := F) hodd
    have hL : (0 : ℝ) ≤ F.blockSide := by positivity
    rw [hK]
    unfold hullFactor
    have e1 : 0 ≤ 3 * hullBondCount F.blockSide := by linarith
    have e2 : 0 ≤ 32 * (F.blockSide : ℝ) ^ 4 + F.blockSide := by linarith
    positivity
  set s : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ :=
    fun m y d => b m y d + e m y d * bondHullSum (y, d) (a m) with hs
  have hs0 : ∀ m y d, 0 ≤ s m y d := fun m y d =>
    add_nonneg (hb _ _ _) (mul_nonneg (he _ _ _) (bondHullSum_nonneg _ (ha m)))
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hB : ∀ i, i + 1 ≤ m → weightedScaleNorm D p θ 2 (i + 1) (s i) ≤ S + ε * (K * T) := by
      intro i hi
      have hin : i + 1 < F.top := by omega
      have h1 := finsetLpNorm_add_le (P := 2) (by norm_num) (innerBonds D (i + 1))
        (fun c => scaleWeight p θ (i + 1) c.1 * b i c.1 c.2)
        (fun c => scaleWeight p θ (i + 1) c.1 * (e i c.1 c.2 * bondHullSum c (a i)))
      have h4 : finsetLpNorm 2 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) ≤ K * T := by
        have h5 := weightedScaleNorm_bondHullSum_le (D := D) hodd hθ (by omega : i < F.top) p 2 (by norm_num) (ha i)
        have h6 := ih i (by omega) (by omega)
        exact h5.trans (mul_le_mul_of_nonneg_left h6 hK0)
      have h3 : finsetLpNorm 2 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * (e i c.1 c.2 * bondHullSum c (a i))) ≤
          ε * finsetLpNorm 2 (innerBonds D (i + 1)) (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) := by
        refine finsetLpNorm_le_of_sum_pow_le (by norm_num) _ _ _ _ hε0 ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c hc => ?_
        have hv := scaleWeight_pos hodd p θ (i + 1) c.1
        have hh := bondHullSum_nonneg c (ha i)
        have he1 := hε i hin c hc
        have he0 := he i c.1 c.2
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        have : scaleWeight p θ (i + 1) c.1 * (e i c.1 c.2 * bondHullSum c (a i)) ≤
            ε * (scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) := by
          have h6 : 0 ≤ scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i) := by positivity
          nlinarith
        calc _ ≤ (ε * (scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i))) ^ 2 :=
              pow_le_pow_left₀ (by positivity) this 2
          _ = _ := by rw [mul_pow]
      have h7 : weightedScaleNorm D p θ 2 (i + 1) (s i) ≤ finsetLpNorm 2 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * b i c.1 c.2 +
            scaleWeight p θ (i + 1) c.1 * (e i c.1 c.2 * bondHullSum c (a i))) := by
        refine le_of_eq ?_
        unfold weightedScaleNorm finsetLpNorm
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 2
        simp only [hs]
        ring
      have h9 := hS i hin
      unfold weightedScaleNorm at h9
      have h8 : ε * finsetLpNorm 2 (innerBonds D (i + 1))
          (fun c => scaleWeight p θ (i + 1) c.1 * bondHullSum c (a i)) ≤ ε * (K * T) :=
        mul_le_mul_of_nonneg_left h4 hε0
      exact h7.trans (h1.trans (by linarith))
    have hrec' : ∀ m', m' + 1 < F.top → ∀ c ∈ innerBonds D (m' + 1),
        a (m' + 1) c.1 c.2 ≤ lineBlockAverage (a m') c + s m' c.1 c.2 := fun m' hm' c hc => hrec m' hm' c hc
    have hmain := (weightedScaleNorm_le_of_recursion hodd h2 D p hθ a s ha hs0 hrec' m hB (by positivity) hm).2
    have h10 : 284 * (ε * (K * T)) ≤ T / 2 := by
      have : 568 * ε * K * T ≤ 1 * T := mul_le_mul_of_nonneg_right hsmall hT0
      nlinarith
    calc _ ≤ 142 * weightedScaleNorm D p θ 2 0 (a 0) + 284 * (S + ε * (K * T)) := hmain
      _ ≤ T := by
          rw [hT] at h10 ⊢
          nlinarith
end Closing
end YangMills.Construction.HullBounds
end
