import Mathlib
import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPictureProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Chessboard
abbrev CyclicIndex {d : ℕ} (n : Fin d → ℕ) : Type :=
  ∀ μ : Fin d, ZMod (n μ)
def cyclicHalf {d : ℕ} (n : Fin d → ℕ) (μ : Fin d) (s : ZMod (n μ)) : Set (CyclicIndex n) :=
  {k | ∃ j : ℕ, j < n μ / 2 ∧ k μ = s + (j : ZMod (n μ))}
def planeReflection {d : ℕ} (n : Fin d → ℕ) (μ : Fin d) (s : ZMod (n μ)) (k : CyclicIndex n) :
    CyclicIndex n :=
  Function.update k μ (2 * s - 1 - k μ)
open Classical in
def reflectFamily {d : ℕ} (n : Fin d → ℕ) {F : Type} (μ : Fin d) (s : ZMod (n μ))
    (f : CyclicIndex n → F) : CyclicIndex n → F :=
  fun k => if k ∈ cyclicHalf n μ s then f k else f (planeReflection n μ s k)
def DoublingBound : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : Fin d → ℕ) [∀ μ, NeZero (n μ)], (∀ μ, Even (n μ)) →
    ∀ (F : Type) (Φ : (CyclicIndex n → F) → ℂ),
      (∀ (f : CyclicIndex n → F) (μ : Fin d) (s : ZMod (n μ)),
        (Φ (reflectFamily n μ s f)).im = 0 ∧ 0 ≤ (Φ (reflectFamily n μ s f)).re ∧
          ‖Φ f‖ ^ 2 ≤ (Φ (reflectFamily n μ s f)).re *
            (Φ (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) f)).re) →
      (∀ g : F, (Φ fun _ => g).im = 0 ∧ 0 ≤ (Φ fun _ => g).re) ∧
      ∀ f : CyclicIndex n → F,
        ‖Φ f‖ ≤ ∏ k : CyclicIndex n, (Φ fun _ => f k).re ^ (1 / ((∏ μ, n μ : ℕ) : ℝ))
end YangMills.Construction.Chessboard
end

noncomputable section
namespace YangMills.Construction.Chessboard
theorem cyclic_natCast_inj {m a b : ℕ} (ha : a < m) (hb : b < m)
    (e : (a : ZMod m) = (b : ZMod m)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  exact e
theorem cyclic_half_add_half {m h : ℕ} (hm : m = 2 * h) : (h : ZMod m) + h = 0 := by
  subst hm
  have := ZMod.natCast_self (2 * h)
  push_cast at this
  linear_combination this
theorem cyclicArc_cover {m h : ℕ} [NeZero m] (hm : m = 2 * h) (s x : ZMod m) :
    (∃ j : ℕ, j < h ∧ x = s + j) ∨ (∃ j : ℕ, j < h ∧ x = s + h + j) := by
  have hv : (x - s).val < m := ZMod.val_lt _
  have hx : x = s + ((x - s).val : ZMod m) := by
    rw [ZMod.natCast_zmod_val]; ring
  by_cases hlt : (x - s).val < h
  · exact Or.inl ⟨_, hlt, hx⟩
  · refine Or.inr ⟨(x - s).val - h, by omega, ?_⟩
    have hc : (((x - s).val : ℕ) : ZMod m) = h + (((x - s).val - h : ℕ) : ZMod m) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    linear_combination hx + hc
theorem cyclicArc_disjoint {m h : ℕ} (hm : m = 2 * h) (s : ZMod m) {j j' : ℕ} (hj : j < h)
    (hj' : j' < h) (e : s + j = s + h + j') : False := by
  have e2 : ((j : ℕ) : ZMod m) = ((h + j' : ℕ) : ZMod m) := by
    push_cast
    linear_combination e
  have := cyclic_natCast_inj (by omega) (by omega) e2
  omega
theorem cyclicArc_not_before {m h : ℕ} (hm : m = 2 * h) (t : ZMod m) {b i : ℕ} (hb : 1 ≤ b)
    (hb' : b ≤ h) (hi : i < h) (e : t - b = t + i) : False := by
  have e2 : ((i + b : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m) := by
    push_cast
    linear_combination -e
  have := cyclic_natCast_inj (by omega) (by omega) e2
  omega
theorem reflect_mem_secondArc {m h : ℕ} (hm : m = 2 * h) {s x : ZMod m} {j : ℕ} (hj : j < h)
    (e : x = s + j) : ∃ c : ℕ, c < h ∧ 2 * s - 1 - x = s + h + c := by
  obtain ⟨c, hc⟩ : ∃ c, c + 1 + j = h := ⟨h - 1 - j, by omega⟩
  refine ⟨c, by omega, ?_⟩
  have hh := cyclic_half_add_half hm
  have hc' : (c : ZMod m) + 1 + j = h := by
    have := congrArg (Nat.cast : ℕ → ZMod m) hc
    push_cast at this
    exact this
  rw [e]
  linear_combination (-1 : ZMod m) * hc' - hh
theorem reflect_mem_firstArc {m h : ℕ} (hm : m = 2 * h) {s x : ZMod m} {j : ℕ} (hj : j < h)
    (e : x = s + h + j) : ∃ c : ℕ, c < h ∧ 2 * s - 1 - x = s + c := by
  obtain ⟨c, hc⟩ : ∃ c, c + 1 + j = h := ⟨h - 1 - j, by omega⟩
  refine ⟨c, by omega, ?_⟩
  have hh := cyclic_half_add_half hm
  have hc' : (c : ZMod m) + 1 + j = h := by
    have := congrArg (Nat.cast : ℕ → ZMod m) hc
    push_cast at this
    exact this
  rw [e]
  linear_combination (-1 : ZMod m) * hc' - hh
section Halves
variable {d : ℕ} {n : Fin d → ℕ}
theorem eq_two_mul_div_two_of_even {m : ℕ} (he : Even m) : m = 2 * (m / 2) := by
  obtain ⟨r, hr⟩ := he
  omega
theorem planeReflection_apply_self (μ : Fin d) (s : ZMod (n μ)) (k : CyclicIndex n) :
    planeReflection n μ s k μ = 2 * s - 1 - k μ := by
  simp [planeReflection]
theorem planeReflection_planeReflection (μ : Fin d) (s : ZMod (n μ)) (k : CyclicIndex n) :
    planeReflection n μ s (planeReflection n μ s k) = k := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [planeReflection_apply_self, planeReflection_apply_self]
    ring
  · simp [planeReflection, Function.update_of_ne h]
variable [∀ μ, NeZero (n μ)]
theorem mem_cyclicHalf_add_iff {μ : Fin d} (he : Even (n μ)) (s : ZMod (n μ))
    (k : CyclicIndex n) :
    k ∈ cyclicHalf n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) ↔ k ∉ cyclicHalf n μ s := by
  have hm := eq_two_mul_div_two_of_even he
  constructor
  · rintro ⟨j, hj, e⟩ ⟨j', hj', e'⟩
    exact cyclicArc_disjoint hm s hj' hj (e'.symm.trans e)
  · intro hk
    rcases cyclicArc_cover hm s (k μ) with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
    · exact absurd ⟨j, hj, e⟩ hk
    · exact ⟨j, hj, e⟩
theorem planeReflection_mem_cyclicHalf_iff {μ : Fin d} (he : Even (n μ)) (s : ZMod (n μ))
    (k : CyclicIndex n) :
    planeReflection n μ s k ∈ cyclicHalf n μ s ↔ k ∉ cyclicHalf n μ s := by
  have hm := eq_two_mul_div_two_of_even he
  constructor
  · rintro ⟨i, hi, e⟩ ⟨j, hj, e'⟩
    obtain ⟨c, hc, ec⟩ := reflect_mem_secondArc hm hj e'
    rw [planeReflection_apply_self] at e
    exact cyclicArc_disjoint hm s hi hc (e.symm.trans ec)
  · intro hk
    rcases cyclicArc_cover hm s (k μ) with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
    · exact absurd ⟨j, hj, e⟩ hk
    · obtain ⟨c, hc, ec⟩ := reflect_mem_firstArc hm hj e
      exact ⟨c, hc, by rw [planeReflection_apply_self]; exact ec⟩
open Classical in
theorem prod_reflectFamily {μ : Fin d} (he : Even (n μ)) {F : Type} (w : F → ℝ)
    (s : ZMod (n μ)) (a : CyclicIndex n → F) :
    ∏ k, w (reflectFamily n μ s a k) = (∏ k with k ∈ cyclicHalf n μ s, w (a k)) ^ 2 := by
  have h1 : ∀ k, w (reflectFamily n μ s a k) =
      if k ∈ cyclicHalf n μ s then w (a k) else w (a (planeReflection n μ s k)) := by
    intro k
    unfold reflectFamily
    split_ifs <;> rfl
  simp_rw [h1]
  rw [Finset.prod_ite, sq]
  congr 1
  refine Finset.prod_nbij' (planeReflection n μ s) (planeReflection n μ s) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact (planeReflection_mem_cyclicHalf_iff he s k).2 hk
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    intro hr
    exact (planeReflection_mem_cyclicHalf_iff he s k).1 hr hk
  · intro k _
    exact planeReflection_planeReflection μ s k
  · intro k _
    exact planeReflection_planeReflection μ s k
  · intro k _
    rfl
open Classical in
theorem prod_reflectFamily_mul_prod {μ : Fin d} (he : Even (n μ)) {F : Type} (w : F → ℝ)
    (s : ZMod (n μ)) (a : CyclicIndex n → F) :
    (∏ k, w (reflectFamily n μ s a k)) *
        ∏ k, w (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) a k) =
      (∏ k, w (a k)) ^ 2 := by
  rw [prod_reflectFamily he, prod_reflectFamily he, ← mul_pow]
  congr 1
  simp_rw [mem_cyclicHalf_add_iff he]
  exact Finset.prod_filter_mul_prod_filter_not _ _ _
omit [∀ μ, NeZero (n μ)] in
theorem reflectFamily_doubles_arc {μ : Fin d} (he : Even (n μ)) {F : Type} {g : F}
    {B : CyclicIndex n → Prop} (hB : ∀ k x, B k → B (Function.update k μ x))
    {t : ZMod (n μ)} {j : ℕ} (hj : j ≤ n μ / 2) (a : CyclicIndex n → F)
    (ha : ∀ k, B k → (∃ i : ℕ, i < j ∧ k μ = t + i) → a k = g) :
    ∀ k, B k → (∃ i : ℕ, i < 2 * j ∧ k μ = t - j + i) → reflectFamily n μ t a k = g := by
  rintro k hk ⟨i, hi, e⟩
  have hm := eq_two_mul_div_two_of_even he
  by_cases hij : j ≤ i
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hij
    have e' : k μ = t + c := by
      rw [e]
      push_cast
      ring
    have hmem : k ∈ cyclicHalf n μ t := ⟨c, by omega, e'⟩
    unfold reflectFamily
    rw [if_pos hmem]
    exact ha k hk ⟨c, by omega, e'⟩
  · obtain ⟨b, hb⟩ : ∃ b, i + b + 1 = j := ⟨j - i - 1, by omega⟩
    have hb' : (i : ZMod (n μ)) + b + 1 = j := by
      have := congrArg (Nat.cast : ℕ → ZMod (n μ)) hb
      push_cast at this
      exact this
    have e' : k μ = t - ((b + 1 : ℕ) : ZMod (n μ)) := by
      rw [e]
      push_cast
      linear_combination hb'
    have hnot : k ∉ cyclicHalf n μ t := by
      rintro ⟨c, hc, ec⟩
      exact cyclicArc_not_before hm t (b := b + 1) (by omega) (by omega) hc (e'.symm.trans ec)
    unfold reflectFamily
    rw [if_neg hnot]
    refine ha _ (hB k _ hk) ⟨b, by omega, ?_⟩
    have := planeReflection_apply_self μ t k
    rw [e'] at this
    push_cast at this
    show planeReflection n μ t k μ = t + b
    rw [this]
    ring
theorem spread_value_along {μ : Fin d} (he : Even (n μ)) {F : Type}
    {M : Set (CyclicIndex n → F)}
    (hM : ∀ a ∈ M, ∀ s, reflectFamily n μ s a ∈ M) {g : F}
    {B : CyclicIndex n → Prop} (hB : ∀ k x, B k → B (Function.update k μ x))
    {a : CyclicIndex n → F} (ha : a ∈ M) (t₀ : ZMod (n μ))
    (h₀ : ∀ k, B k → k μ = t₀ → a k = g) : ∃ b ∈ M, ∀ k, B k → b k = g := by
  have hpos : 0 < n μ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm := eq_two_mul_div_two_of_even he
  have cover : ∀ j : ℕ, 1 ≤ j → j ≤ n μ / 2 → ∃ t : ZMod (n μ), ∃ b ∈ M,
      ∀ k, B k → (∃ i : ℕ, i < j ∧ k μ = t + i) → b k = g := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      refine ⟨t₀, a, ha, ?_⟩
      rintro k hk ⟨i, hi, e⟩
      obtain rfl : i = 0 := by omega
      exact h₀ k hk (by simpa using e)
    | succ j hj ih =>
      intro hle
      obtain ⟨t, b, hb, hbg⟩ := ih (by omega)
      refine ⟨t - j, reflectFamily n μ t b, hM b hb t, ?_⟩
      rintro k hk ⟨i, hi, e⟩
      exact reflectFamily_doubles_arc he hB (by omega) b hbg k hk ⟨i, by omega, e⟩
  obtain ⟨t, b, hb, hbg⟩ := cover (n μ / 2) (by omega) le_rfl
  refine ⟨_, hM b hb t, fun k hk => reflectFamily_doubles_arc he hB le_rfl b hbg k hk ?_⟩
  refine ⟨(k μ - (t - ((n μ / 2 : ℕ) : ZMod (n μ)))).val, ?_, ?_⟩
  · have := ZMod.val_lt (k μ - (t - ((n μ / 2 : ℕ) : ZMod (n μ))))
    omega
  · rw [ZMod.natCast_zmod_val]
    ring
theorem spread_value (hEven : ∀ μ, Even (n μ)) {F : Type} {M : Set (CyclicIndex n → F)}
    (hM : ∀ a ∈ M, ∀ μ s, reflectFamily n μ s a ∈ M) {a : CyclicIndex n → F} (ha : a ∈ M)
    (k₀ : CyclicIndex n) (T : Finset (Fin d)) :
    ∃ b ∈ M, ∀ k, (∀ ν, ν ∉ T → k ν = k₀ ν) → b k = a k₀ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨a, ha, fun k hk => ?_⟩
    have : k = k₀ := funext fun ν => hk ν (by simp)
    rw [this]
  | insert μ T hμ ih =>
    obtain ⟨b, hb, hbg⟩ := ih
    obtain ⟨c, hc, hcg⟩ := spread_value_along (hEven μ) (fun a ha s => hM a ha μ s) (g := a k₀)
      (B := fun k => ∀ ν, ν ∉ T → ν ≠ μ → k ν = k₀ ν)
      (fun k x hk ν hν hne => by rw [Function.update_of_ne hne]; exact hk ν hν hne)
      hb (k₀ μ) (fun k hk e => hbg k fun ν hν => by
        by_cases h : ν = μ
        · rw [h]; exact e
        · exact hk ν hν h)
    refine ⟨c, hc, fun k hk => hcg k fun ν hν hne => hk ν ?_⟩
    simp [hν, hne]
theorem le_prod_weight_of_reflection (hEven : ∀ μ, Even (n μ)) {F : Type}
    (N : (CyclicIndex n → F) → ℝ) (hN : ∀ a, 0 ≤ N a)
    (hcs : ∀ (a : CyclicIndex n → F) (μ : Fin d) (s : ZMod (n μ)),
      N a ^ 2 ≤ N (reflectFamily n μ s a) *
        N (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) a))
    (w : F → ℝ) (hw : ∀ g, 0 < w g) (hc : ∀ g, N (fun _ => g) ≤ ∏ _k : CyclicIndex n, w g)
    (f : CyclicIndex n → F) : N f ≤ ∏ k, w (f k) := by
  classical
  let L : (CyclicIndex n → F) → ℝ := fun a => ∏ k, w (a k)
  have hL : ∀ a, 0 < L a := fun a => Finset.prod_pos fun k _ => hw _
  let A : (CyclicIndex n → F) → ℝ := fun a => N a / L a
  have hA : ∀ a, 0 ≤ A a := fun a => div_nonneg (hN a) (hL a).le
  let V : Set (CyclicIndex n → F) := {a | ∀ k, a k ∈ Set.range f}
  have hVfin : V.Finite := Set.Finite.pi' fun _ => Set.finite_range f
  have hVρ : ∀ a ∈ V, ∀ (μ : Fin d) (s : ZMod (n μ)), reflectFamily n μ s a ∈ V := by
    intro a ha μ s k
    unfold reflectFamily
    split_ifs
    · exact ha _
    · exact ha _
  have hfV : f ∈ V := fun k => ⟨k, rfl⟩
  obtain ⟨a₀, ha₀, hmax⟩ := Set.exists_max_image V A hVfin ⟨f, hfV⟩
  have hS : A a₀ ≤ 1 := by
    by_contra hcon
    have hSpos : 0 < A a₀ := by linarith [not_le.1 hcon]
    let M : Set (CyclicIndex n → F) := {a | a ∈ V ∧ A a = A a₀}
    have hM : ∀ a ∈ M, ∀ (μ : Fin d) (s : ZMod (n μ)), reflectFamily n μ s a ∈ M := by
      rintro a ⟨haV, haS⟩ μ s
      have h1 := hVρ a haV μ s
      have h2 := hVρ a haV μ (s + ((n μ / 2 : ℕ) : ZMod (n μ)))
      refine ⟨h1, le_antisymm (hmax _ h1) ?_⟩
      have hprod : L (reflectFamily n μ s a) *
          L (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) a) = L a ^ 2 :=
        prod_reflectFamily_mul_prod (hEven μ) w s a
      have hsq : A a ^ 2 ≤ A (reflectFamily n μ s a) *
          A (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) a) := by
        show (N a / L a) ^ 2 ≤ (N _ / L _) * (N _ / L _)
        rw [div_pow, div_mul_div_comm, hprod]
        exact div_le_div_of_nonneg_right (hcs a μ s) (pow_pos (hL a) 2).le
      rw [haS] at hsq
      have h3 := hsq.trans (mul_le_mul_of_nonneg_left (hmax _ h2) (hA _))
      rw [sq] at h3
      exact le_of_mul_le_mul_right h3 hSpos
    obtain ⟨b, hb, hbg⟩ := spread_value hEven hM ⟨ha₀, rfl⟩ 0 Finset.univ
    have hbc : b = fun _ => a₀ 0 :=
      funext fun k => hbg k fun ν hν => absurd (Finset.mem_univ ν) hν
    have h1 : A b ≤ 1 := by
      rw [hbc]
      exact (div_le_one (hL _)).2 (hc _)
    have h2 : A b = A a₀ := hb.2
    linarith [not_le.1 hcon]
  exact (div_le_one (hL f)).1 ((hmax f hfV).trans hS)
end Halves
theorem complex_norm_eq_re_of_nonneg {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) :
    ‖z‖ = z.re := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetupCellFamilies.norm_eq_re_of_im_eq_zero <;> assumption
theorem reflectFamily_const {d : ℕ} (n : Fin d → ℕ) {F : Type} (μ : Fin d) (s : ZMod (n μ))
    (g : F) : reflectFamily n μ s (fun _ => g) = fun _ => g := by
  funext k
  unfold reflectFamily
  split_ifs <;> rfl
theorem doublingBound_holds : DoublingBound := by
  intro d hd n _ hEven F Φ hΦ
  have hconst : ∀ g : F, (Φ fun _ => g).im = 0 ∧ 0 ≤ (Φ fun _ => g).re := by
    intro g
    have h := hΦ (fun _ => g) ⟨0, hd⟩ 0
    rw [reflectFamily_const] at h
    exact ⟨h.1, h.2.1⟩
  refine ⟨hconst, fun f => ?_⟩
  have hcs : ∀ (a : CyclicIndex n → F) (μ : Fin d) (s : ZMod (n μ)),
      ‖Φ a‖ ^ 2 ≤ ‖Φ (reflectFamily n μ s a)‖ *
        ‖Φ (reflectFamily n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) a)‖ := by
    intro a μ s
    have h1 := hΦ a μ s
    have h2 := hΦ a μ (s + ((n μ / 2 : ℕ) : ZMod (n μ)))
    rw [complex_norm_eq_re_of_nonneg h1.1 h1.2.1, complex_norm_eq_re_of_nonneg h2.1 h2.2.1]
    exact h1.2.2
  have hcard : Fintype.card (CyclicIndex n) = ∏ μ, n μ := by
    simp [CyclicIndex, Fintype.card_pi, ZMod.card]
  have hne : (∏ μ, n μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => NeZero.ne _
  let c : F → ℝ := fun g => (Φ fun _ => g).re ^ (1 / ((∏ μ, n μ : ℕ) : ℝ))
  have hc₀ : ∀ g, 0 ≤ c g := fun g => Real.rpow_nonneg (hconst g).2 _
  have hcpow : ∀ g, c g ^ (∏ μ, n μ) = (Φ fun _ => g).re := by
    intro g
    show ((Φ fun _ => g).re ^ (1 / ((∏ μ, n μ : ℕ) : ℝ))) ^ (∏ μ, n μ) = _
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (hconst g).2 hne
  have hbound : ∀ δ : ℝ, 0 < δ → ‖Φ f‖ ≤ ∏ k, max (c (f k)) δ := by
    intro δ hδ
    refine le_prod_weight_of_reflection hEven (fun a => ‖Φ a‖) (fun _ => norm_nonneg _) hcs
      (fun g => max (c g) δ) (fun g => lt_max_of_lt_right hδ) (fun g => ?_) f
    show ‖Φ fun _ => g‖ ≤ _
    rw [complex_norm_eq_re_of_nonneg (hconst g).1 (hconst g).2, Finset.prod_const,
      Finset.card_univ, hcard, ← hcpow g]
    exact pow_le_pow_left₀ (hc₀ g) (le_max_left _ _) _
  have hcont : Continuous fun δ : ℝ => ∏ k, max (c (f k)) δ :=
    continuous_finsetProd _ fun k _ => continuous_const.max continuous_id
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hfin := ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin hbound)
  have hzero : ∀ k, max (c (f k)) 0 = c (f k) := fun k => max_eq_left (hc₀ _)
  simp only [hzero] at hfin
  exact hfin
end YangMills.Construction.Chessboard
end
