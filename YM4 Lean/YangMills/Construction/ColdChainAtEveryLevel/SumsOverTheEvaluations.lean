import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.EvaluationSums
open BlockAverages BlockAverages.VariationRates LatticeFractionalIntegration
variable {F : BlockAverages.BlockFrame} {S : Finset F.Cell} {j : ℕ}
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : Set.InjOn f s) (hmaps : ∀ a ∈ s, f a ∈ t) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) :
    ∑ a ∈ s, w (f a) ≤ ∑ b ∈ t, w b := by
  rw [← Finset.sum_image (f := w) (g := f) hf]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun b hb => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb; exact hmaps a ha) fun b _ _ => hw b
theorem sum_mul_bondSum_le {α : Type} (Ys : Finset α) (κ : α → ℝ) (hκ : ∀ a, 0 ≤ κ a) (g : F.Site j → Fin 4 → ℝ)
    (hg : ∀ x i, 0 ≤ g x i) (B : Finset (F.Site j × Fin 4)) (l : List PathStep) (f : α → F.Site j)
    (hf : Set.InjOn f Ys) (hB : ∀ a ∈ Ys, ∀ b, LiesOnPath b (f a) l → b ∈ B) :
    ∑ a ∈ Ys, κ a * bondSum g (f a) l ≤
      l.length * (√(∑ a ∈ Ys, κ a ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2)) := by
  classical
  induction l generalizing f with
  | nil => simp [bondSum]
  | cons st r ih =>
    simp only [bondSum, mul_add, Finset.sum_add_distrib, List.length_cons]
    have h1 := ih (fun a => f a + stepDisplacement j st) (fun a ha a' ha' e => hf ha ha' (add_right_cancel e))
      (fun a ha b hb => hB a ha b (Or.inr hb))
    set b₀ : α → F.Site j × Fin 4 := fun a =>
      if st.2 then (f a, st.1) else (f a - unitStep j st.1, st.1) with hb₀
    have hv : ∀ a, (if st.2 then g (f a) st.1 else g (f a - unitStep j st.1) st.1) = g (b₀ a).1 (b₀ a).2 := by
      intro a
      simp only [hb₀]
      split_ifs <;> rfl
    have hinj : Set.InjOn b₀ Ys := by
      intro a ha a' ha' e
      apply hf ha ha'
      simp only [hb₀] at e
      split_ifs at e
      · exact congrArg Prod.fst e
      · exact sub_left_injective (congrArg Prod.fst e)
    have hin : ∀ a ∈ Ys, b₀ a ∈ B := by
      intro a ha
      refine hB a ha _ (Or.inl ?_)
      simp only [hb₀]
      split_ifs <;> rfl
    have h2 : ∑ a ∈ Ys, κ a * (if st.2 then g (f a) st.1 else g (f a - unitStep j st.1) st.1) ≤
        √(∑ a ∈ Ys, κ a ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2) := by
      simp only [hv]
      refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      exact sum_comp_le_of_injOn Ys B b₀ hinj hin (fun b => g b.1 b.2 ^ 2) fun b => sq_nonneg _
    push_cast
    linarith
theorem sqrt_sum_sq_filter_le {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (κ : α → ℝ) :
    √(∑ a ∈ s.filter p, κ a ^ 2) ≤ √(∑ a ∈ s, κ a ^ 2) :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _)
theorem sum_plaquette_bondSum_le (P : Finset (F.Site 0 × Fin 4 × Fin 4)) (κ : F.Site 0 × Fin 4 × Fin 4 → ℝ)
    (hκ : ∀ p, 0 ≤ κ p) (g : F.Site 0 → Fin 4 → ℝ) (hg : ∀ x i, 0 ≤ g x i) (B : Finset (F.Site 0 × Fin 4))
    (hB : ∀ p ∈ P, ∀ b, LiesOnPath b p.1 (plaquetteBoundary p) → b ∈ B) :
    ∑ p ∈ P, κ p * bondSum g p.1 (plaquetteBoundary p) ≤
      64 * (√(∑ p ∈ P, κ p ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2)) := by
  classical
  rw [← Finset.sum_fiberwise P (fun p => p.2)]
  have h1 : ∀ d : Fin 4 × Fin 4, ∑ p ∈ P with p.2 = d, κ p * bondSum g p.1 (plaquetteBoundary p) ≤
      4 * (√(∑ p ∈ P, κ p ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2)) := by
    intro d
    set l : List PathStep := [(d.1, true), (d.2, true), (d.1, false), (d.2, false)] with hl
    have e : ∀ p ∈ P.filter (fun p => p.2 = d), plaquetteBoundary p = l := by
      intro p hp
      rw [hl, ← (Finset.mem_filter.1 hp).2]
      rfl
    have h2 := sum_mul_bondSum_le (P.filter fun p => p.2 = d) κ hκ g hg B l (fun p => p.1)
      (fun p hp p' hp' e' => Prod.ext e' (by
        rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hp')).2]))
      (fun p hp b hb => hB p (Finset.mem_filter.1 hp).1 b (by rw [e p hp]; exact hb))
    have h3 : ∑ p ∈ P with p.2 = d, κ p * bondSum g p.1 (plaquetteBoundary p) =
        ∑ p ∈ P with p.2 = d, κ p * bondSum g p.1 l :=
      Finset.sum_congr rfl fun p hp => by rw [e p hp]
    rw [h3]
    refine h2.trans ?_
    have hl4 : ((l.length : ℕ) : ℝ) = 4 := by simp [hl]
    rw [hl4]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right (sqrt_sum_sq_filter_le _ _ _) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum fun d _ => h1 d).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
def maxContourLength (L : ℕ) : ℕ :=
  (centredCube L).sup fun a => Finset.univ.sup fun π : Equiv.Perm (Fin 4) => Finset.univ.sup fun i : Fin 4 =>
    (bondContour L a π i).length
theorem length_bondContour_le {L : ℕ} {a : Lattice4} (ha : a ∈ centredCube L) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L a π i).length ≤ maxContourLength L := by
  unfold maxContourLength
  refine le_trans ?_ (Finset.le_sup (f := fun a => Finset.univ.sup fun π : Equiv.Perm (Fin 4) =>
    Finset.univ.sup fun i : Fin 4 => (bondContour L a π i).length) ha)
  refine le_trans ?_ (Finset.le_sup (f := fun π : Equiv.Perm (Fin 4) => Finset.univ.sup fun i : Fin 4 =>
    (bondContour L a π i).length) (Finset.mem_univ π))
  exact Finset.le_sup (f := fun i : Fin 4 => (bondContour L a π i).length) (Finset.mem_univ i)
theorem contour_average_const (hodd : Odd F.blockSide) (v : ℝ) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ _a ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), v = v := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LatticePaths.card_centredCube hodd, nsmul_eq_mul]
  have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [this]
  push_cast
  field_simp
theorem sum_contourBondSum_le (hodd : Odd F.blockSide) (hinj : Function.Injective (refineSite (F := F) (j := j)))
    (C : Finset (F.Site (j + 1) × Fin 4)) (κ : F.Site (j + 1) × Fin 4 → ℝ) (hκ : ∀ c, 0 ≤ κ c)
    (g : F.Site j → Fin 4 → ℝ) (hg : ∀ x i, 0 ≤ g x i) (B : Finset (F.Site j × Fin 4))
    (hB : ∀ c ∈ C, ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ b,
      LiesOnPath b (refineSite c.1) (bondContour F.blockSide a π c.2) → b ∈ B) :
    ∑ c ∈ C, κ c * contourBondSum g c ≤
      (4 * maxContourLength F.blockSide) * (√(∑ c ∈ C, κ c ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2)) := by
  classical
  set X := √(∑ c ∈ C, κ c ^ 2) * √(∑ b ∈ B, g b.1 b.2 ^ 2) with hX
  have h1 : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ∑ c ∈ C, κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2) ≤
        (4 * maxContourLength F.blockSide) * X := by
    intro a ha π
    rw [← Finset.sum_fiberwise C (fun c => c.2)]
    have h2 : ∀ i : Fin 4, ∑ c ∈ C with c.2 = i, κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2) ≤
        maxContourLength F.blockSide * X := by
      intro i
      have e : ∀ c ∈ C.filter (fun c => c.2 = i), bondContour F.blockSide a π c.2 = bondContour F.blockSide a π i := by
        intro c hc
        rw [(Finset.mem_filter.1 hc).2]
      have h3 := sum_mul_bondSum_le (C.filter fun c => c.2 = i) κ hκ g hg B (bondContour F.blockSide a π i)
        (fun c => refineSite c.1) (fun c hc c' hc' e' => Prod.ext (hinj e') (by
          rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2]))
        (fun c hc b hb => hB c (Finset.mem_filter.1 hc).1 a ha π b (by rw [e c hc]; exact hb))
      have h4 : ∑ c ∈ C with c.2 = i, κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2) =
          ∑ c ∈ C with c.2 = i, κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π i) :=
        Finset.sum_congr rfl fun c hc => by rw [e c hc]
      rw [h4]
      refine h3.trans ?_
      have h5 : ((bondContour F.blockSide a π i).length : ℝ) ≤ maxContourLength F.blockSide := by
        exact_mod_cast length_bondContour_le ha π i
      refine mul_le_mul h5 ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
      exact mul_le_mul_of_nonneg_right (sqrt_sum_sq_filter_le _ _ _) (Real.sqrt_nonneg _)
    refine (Finset.sum_le_sum fun i _ => h2 i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  unfold contourBondSum
  have e2 : ∑ c ∈ C, κ c * ((1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ a ∈ centredCube F.blockSide,
      ∑ π : Equiv.Perm (Fin 4), bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2)) =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ∑ c ∈ C, κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2) := by
    have e3 : ∀ c, κ c * ((1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ a ∈ centredCube F.blockSide,
        ∑ π : Equiv.Perm (Fin 4), bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2)) =
        (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          κ c * bondSum g (refineSite c.1) (bondContour F.blockSide a π c.2) := by
      intro c
      rw [mul_left_comm]
      congr 1
      simp only [Finset.mul_sum]
    simp only [e3]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [e2]
  calc _ ≤ (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (4 * maxContourLength F.blockSide) * X := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun π _ => h1 a ha π
    _ = _ := contour_average_const hodd _
theorem sum_far_link_le (C : Finset (F.Site (j + 1) × Fin 4)) (κ : F.Site (j + 1) × Fin 4 → ℝ)
    (g : F.Site (j + 1) → ℝ) (hg : ∀ y, 0 ≤ g y) (Y : Finset (F.Site (j + 1)))
    (hY : ∀ c ∈ C, c.1 + unitStep (j + 1) c.2 ∈ Y) :
    ∑ c ∈ C, κ c * g (c.1 + unitStep (j + 1) c.2) ≤ 4 * (√(∑ c ∈ C, κ c ^ 2) * √(∑ y ∈ Y, g y ^ 2)) := by
  classical
  rw [← Finset.sum_fiberwise C (fun c => c.2)]
  have h2 : ∀ i : Fin 4, ∑ c ∈ C with c.2 = i, κ c * g (c.1 + unitStep (j + 1) c.2) ≤
      √(∑ c ∈ C, κ c ^ 2) * √(∑ y ∈ Y, g y ^ 2) := by
    intro i
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    refine mul_le_mul (sqrt_sum_sq_filter_le _ _ _) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine sum_comp_le_of_injOn (C.filter fun c => c.2 = i) Y (fun c => c.1 + unitStep (j + 1) c.2) ?_
      (fun c hc => hY c (Finset.mem_filter.1 hc).1) (fun y => g y ^ 2) fun y => sq_nonneg _
    intro c hc c' hc' e
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
    simp only [h1, h2] at e
    exact Prod.ext (add_right_cancel e) (by rw [h1, h2])
  refine (Finset.sum_le_sum fun i _ => h2 i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
theorem geom_sum_le_two {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) (n : ℕ) : ∑ i ∈ Finset.range n, ρ ^ i ≤ 2 := by
  have : ∑ i ∈ Finset.range n, ρ ^ i ≤ 2 - 2 * ρ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have := pow_nonneg h0 n
      nlinarith
  have := pow_nonneg h0 n
  linarith
def levelScale (F : BlockAverages.BlockFrame) (j : ℕ) : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - j)
def farContribution (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (g : VariationSlot F → ℝ) (t : F.ActionTerm) : ℝ :=
  actionTermSize a W k t * levelScale F (actionTermLevel t) * farWeight g t
theorem levelScale_nonneg (F : BlockAverages.BlockFrame) (j : ℕ) : 0 ≤ levelScale F j := by apply _root_.YangMills.Construction.ReferenceBounds.zero_le_levelScale <;> assumption
theorem farWeight_nonneg' {g : VariationSlot F → ℝ} (hg : ∀ u, 0 ≤ g u) (t : F.ActionTerm) : 0 ≤ farWeight g t := by
  rcases t with p | c
  · exact bondSum_nonneg (fun _ _ => hg _) _ _
  · refine add_nonneg (hg _) ?_
    unfold contourBondSum
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun π _ => bondSum_nonneg (fun _ _ => hg _) _ _
theorem farContribution_nonneg {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain) (k : F.SiteGauge) {g : VariationSlot F → ℝ}
    (hg : ∀ u, 0 ≤ g u) (t : F.ActionTerm) : 0 ≤ farContribution a W k g t :=
  mul_nonneg (mul_nonneg (actionTermSize_nonneg ha W k t) (levelScale_nonneg F _)) (farWeight_nonneg' hg t)
def contourSumConstant (L : ℕ) : ℝ := 64 + 2 * (4 + 4 * maxContourLength L)
theorem contourSumConstant_pos (L : ℕ) : 0 < contourSumConstant L := by
  unfold contourSumConstant
  positivity
open Classical in
theorem sum_farPart_le (hodd : Odd F.blockSide)
    (hinj : ∀ j, j < F.top → Function.Injective (refineSite (F := F) (j := j)))
    {a : ℝ} (ha : 0 ≤ a) (W : F.FieldChain) (k : F.SiteGauge) (T' : Finset F.ActionTerm) (hT : T' ⊆ actionTerms S)
    (Bs : (j : ℕ) → Finset (F.Site j × Fin 4)) (Ys : (j : ℕ) → Finset (F.Site (j + 1)))
    (g : VariationSlot F → ℝ) (hg : ∀ u, 0 ≤ g u) {Bd κ₀ ρ : ℝ} (hBd : 0 ≤ Bd) (hκ₀ : 0 ≤ κ₀) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1 / 2)
    (hplaq : ∀ p, Sum.inl p ∈ T' → ∀ b, LiesOnPath b p.1 (plaquetteBoundary p) → b ∈ Bs 0)
    (hfit : ∀ j (c : F.Site (j + 1) × Fin 4), Sum.inr ⟨j, c⟩ ∈ T' → ∀ e ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4), ∀ b, LiesOnPath b (refineSite c.1) (bondContour F.blockSide e π c.2) → b ∈ Bs j)
    (hfar : ∀ j (c : F.Site (j + 1) × Fin 4), Sum.inr ⟨j, c⟩ ∈ T' → c.1 + unitStep (j + 1) c.2 ∈ Ys j)
    (hF : ∑ p ∈ (innerPlaquettes S 0).filter (fun p => Sum.inl p ∈ T'), actionTermSize a W k (Sum.inl p) ^ 2 ≤ κ₀ ^ 2)
    (hM : ∀ j, j < F.top → ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => Sum.inr ⟨j, c⟩ ∈ T'),
      actionTermSize a W k (Sum.inr ⟨j, c⟩) ^ 2 ≤ (κ₀ * ρ ^ (F.top - 1 - j)) ^ 2)
    (hb : ∀ j, j < F.top → levelScale F j * √(∑ b ∈ Bs j, g (slotOfBond j b.1 b.2) ^ 2) ≤ Bd)
    (hl : ∀ j, j < F.top → levelScale F j * √(∑ y ∈ Ys j, g (slotOfLink j y) ^ 2) ≤ Bd) :
    ∑ t ∈ T', farContribution a W k g t ≤ contourSumConstant F.blockSide * κ₀ * Bd := by
  have hnpos : 0 < F.top := Nat.succ_pos _
  have e0 : ∑ t ∈ T', farContribution a W k g t =
      ∑ t ∈ (actionTerms S).filter (fun t => t ∈ T'), farContribution a W k g t := by
    congr 1
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hT h, h⟩, fun h => h.2⟩
  rw [e0, Finset.sum_filter, BlockAverages.PatchLocality.sum_actionTerms]
  have hP : ∑ p ∈ (innerPlaquettes S 0).filter (fun p => (Sum.inl p : F.ActionTerm) ∈ T'),
      farContribution a W k g (Sum.inl p) ≤ 64 * κ₀ * Bd := by
    set P := (innerPlaquettes S 0).filter (fun p => (Sum.inl p : F.ActionTerm) ∈ T') with hPdef
    have h1 := sum_plaquette_bondSum_le P (fun p => actionTermSize a W k (Sum.inl p))
      (fun p => actionTermSize_nonneg ha W k _) (restrictToBonds g 0) (fun _ _ => hg _) (Bs 0)
      (fun p hp b hb' => hplaq p (Finset.mem_filter.1 hp).2 b hb')
    have e1 : ∑ p ∈ P, farContribution a W k g (Sum.inl p) = levelScale F 0 *
        ∑ p ∈ P, actionTermSize a W k (Sum.inl p) * bondSum (restrictToBonds g 0) p.1 (plaquetteBoundary p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [farContribution, actionTermLevel, farWeight]
      ring
    rw [e1]
    have h2 : √(∑ p ∈ P, actionTermSize a W k (Sum.inl p) ^ 2) ≤ κ₀ :=
      (Real.sqrt_le_sqrt hF).trans (by rw [Real.sqrt_sq hκ₀])
    have h3 := hb 0 hnpos
    have hs := levelScale_nonneg F 0
    calc _ ≤ levelScale F 0 * (64 * (√(∑ p ∈ P, actionTermSize a W k (Sum.inl p) ^ 2) *
            √(∑ b ∈ Bs 0, restrictToBonds g 0 b.1 b.2 ^ 2))) := mul_le_mul_of_nonneg_left h1 hs
      _ = 64 * √(∑ p ∈ P, actionTermSize a W k (Sum.inl p) ^ 2) * (levelScale F 0 *
            √(∑ b ∈ Bs 0, g (slotOfBond 0 b.1 b.2) ^ 2)) := by
          simp only [restrictToBonds]
          ring
      _ ≤ 64 * κ₀ * Bd := by
          refine mul_le_mul (by linarith) h3 (mul_nonneg hs (Real.sqrt_nonneg _)) (by positivity)
  have hJ : ∀ j ∈ Finset.range F.top, ∑ c ∈ (innerBonds S (j + 1)).filter
      (fun c => (Sum.inr ⟨j, c⟩ : F.ActionTerm) ∈ T'),
      farContribution a W k g (Sum.inr ⟨j, c⟩) ≤
        (4 + 4 * maxContourLength F.blockSide) * κ₀ * Bd * ρ ^ (F.top - 1 - j) := by
    intro j hj
    have hjn := Finset.mem_range.1 hj
    set C := (innerBonds S (j + 1)).filter (fun c => (Sum.inr ⟨j, c⟩ : F.ActionTerm) ∈ T') with hC
    set κ : F.Site (j + 1) × Fin 4 → ℝ := fun c => actionTermSize a W k (Sum.inr ⟨j, c⟩) with hκ
    have hκ0 : ∀ c, 0 ≤ κ c := fun c => actionTermSize_nonneg ha W k _
    have h1 := sum_far_link_le C κ (fun y => g (slotOfLink j y)) (fun y => hg _) (Ys j)
      (fun c hc => hfar j c (Finset.mem_filter.1 hc).2)
    have h2 := sum_contourBondSum_le hodd (hinj j hjn) C κ hκ0 (restrictToBonds g j) (fun _ _ => hg _) (Bs j)
      (fun c hc e he π b hb' => hfit j c (Finset.mem_filter.1 hc).2 e he π b hb')
    have e1 : ∑ c ∈ C, farContribution a W k g (Sum.inr ⟨j, c⟩) = levelScale F j *
        (∑ c ∈ C, κ c * g (slotOfLink j (c.1 + unitStep (j + 1) c.2)) +
          ∑ c ∈ C, κ c * contourBondSum (restrictToBonds g j) c) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [farContribution, actionTermLevel, farWeight, hκ]
      ring
    rw [e1]
    set K := √(∑ c ∈ C, κ c ^ 2) with hK
    have hKle : K ≤ κ₀ * ρ ^ (F.top - 1 - j) :=
      (Real.sqrt_le_sqrt (hM j hjn)).trans (by
        rw [Real.sqrt_sq (mul_nonneg hκ₀ (pow_nonneg hρ0 _))])
    have hK0 : 0 ≤ K := Real.sqrt_nonneg _
    have hs := levelScale_nonneg F j
    have h3 := hb j hjn
    have h4 := hl j hjn
    have m1 : levelScale F j * (4 * (K * √(∑ y ∈ Ys j, g (slotOfLink j y) ^ 2))) ≤ 4 * K * Bd := by
      calc _ = 4 * K * (levelScale F j * √(∑ y ∈ Ys j, g (slotOfLink j y) ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
    have m2 : levelScale F j * ((4 * maxContourLength F.blockSide) *
        (K * √(∑ b ∈ Bs j, restrictToBonds g j b.1 b.2 ^ 2))) ≤
        (4 * maxContourLength F.blockSide) * K * Bd := by
      calc _ = (4 * maxContourLength F.blockSide) * K * (levelScale F j *
              √(∑ b ∈ Bs j, g (slotOfBond j b.1 b.2) ^ 2)) := by
            simp only [restrictToBonds]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have m3 : levelScale F j * (∑ c ∈ C, κ c * g (slotOfLink j (c.1 + unitStep (j + 1) c.2)) +
        ∑ c ∈ C, κ c * contourBondSum (restrictToBonds g j) c) ≤
          (4 + 4 * maxContourLength F.blockSide) * K * Bd := by
      have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hs
      rw [mul_add] at this
      rw [mul_add] at this
      nlinarith
    refine m3.trans ?_
    have : (4 + 4 * (maxContourLength F.blockSide : ℝ)) * K * Bd ≤
        (4 + 4 * (maxContourLength F.blockSide : ℝ)) * (κ₀ * ρ ^ (F.top - 1 - j)) * Bd := by
      refine mul_le_mul_of_nonneg_right ?_ hBd
      exact mul_le_mul_of_nonneg_left hKle (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  have hsum : ∑ j ∈ Finset.range F.top, ρ ^ (F.top - 1 - j) ≤ 2 := by
    rw [Finset.sum_range_reflect (fun i => ρ ^ i) F.top]
    exact geom_sum_le_two hρ0 hρ1 _
  have hJ2 := Finset.sum_le_sum hJ
  rw [← Finset.mul_sum] at hJ2
  rw [Finset.sum_filter] at hP
  simp only [Finset.sum_filter] at hJ2
  have hc : 0 ≤ (4 + 4 * (maxContourLength F.blockSide : ℝ)) * κ₀ * Bd := by positivity
  have := mul_le_mul_of_nonneg_left hsum hc
  unfold contourSumConstant
  nlinarith
end YangMills.Construction.EvaluationSums
end
