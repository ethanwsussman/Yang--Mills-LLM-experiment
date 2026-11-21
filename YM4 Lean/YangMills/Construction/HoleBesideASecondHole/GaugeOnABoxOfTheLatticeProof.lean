import YangMills.Construction.HoleBesideASecondHole.FlatGaugeOnTheShellOfABoxProof
import YangMills.Construction.HoleBesideASecondHole.GaugeOnABoxOfTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BoxGauge
open LatticeGauge
open BlockAverages (UnitQuaternion)
namespace Fixing
theorem unitVec_apply_self (i : Fin 4) : unitVec i i = 1 := by simp [unitVec]
theorem unitVec_apply_of_ne {i j : Fin 4} (h : j ≠ i) : unitVec i j = 0 := by simp [unitVec, h]
theorem add_smul_unitVec_apply (a : Fin 4 → ℤ) (i l : Fin 4) (r : ℕ) :
    (a + (r : ℤ) • unitVec i) l = a l + if l = i then (r : ℤ) else 0 := by apply _root_.YangMills.Construction.LatticeGauge.BoundaryGauge.add_smul_unitVec_apply <;> assumption
theorem add_unitVec_apply (a : Fin 4 → ℤ) (i l : Fin 4) :
    (a + unitVec i) l = a l + if l = i then 1 else 0 := by
  by_cases h : l = i
  · subst h
    simp [unitVec_apply_self]
  · simp [unitVec_apply_of_ne h, h]
theorem add_succ_smul_unitVec (a : Fin 4 → ℤ) (i : Fin 4) (r : ℕ) :
    a + ((r + 1 : ℕ) : ℤ) • unitVec i = a + (r : ℤ) • unitVec i + unitVec i := by
  push_cast
  rw [add_smul, one_smul, add_assoc]
theorem lineHolonomy_congr (A B : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (a : Fin 4 → ℤ) (i : Fin 4) (n : ℕ)
    (H : ∀ r < n, A (a + (r : ℤ) • unitVec i) i = B (a + (r : ℤ) • unitVec i) i) :
    lineHolonomy A a i n = lineHolonomy B a i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lineHolonomy, lineHolonomy, ih fun r hr => H r (by omega), H n (by omega)]
theorem lineHolonomy_add (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (a : Fin 4 → ℤ) (i : Fin 4) (m n : ℕ) :
    lineHolonomy X a i (m + n) = lineHolonomy X a i m * lineHolonomy X (a + (m : ℤ) • unitVec i) i n := by
  induction n with
  | zero => simp [lineHolonomy]
  | succ n ih =>
    rw [← add_assoc, lineHolonomy, lineHolonomy, ih, mul_assoc]
    congr 3
    push_cast
    rw [add_smul, add_assoc]
theorem quatDist_rectangle_le (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (p : Fin 4 → ℤ) (l m : ℕ) :
    quatDist (lineHolonomy X p 0 l * lineHolonomy X (p + (l : ℤ) • unitVec 0) 1 m)
        (lineHolonomy X p 1 m * lineHolonomy X (p + (m : ℤ) • unitVec 1) 0 l) ≤
      ∑ r ∈ Finset.range m, ∑ c ∈ Finset.range l,
        plaquetteDefect X (p + (r : ℤ) • unitVec 1 + (c : ℤ) • unitVec 0) 0 1 := by
  induction m with
  | zero =>
    simp [lineHolonomy, quatDist_self]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    set pm := p + (m : ℤ) • unitVec 1 with hpm
    have e1 : p + (l : ℤ) • unitVec 0 + (m : ℤ) • unitVec 1 = pm + (l : ℤ) • unitVec 0 := by
      rw [hpm]
      abel
    have e2 : p + ((m + 1 : ℕ) : ℤ) • unitVec 1 = pm + unitVec 1 := add_succ_smul_unitVec p 1 m
    have hs := quatDist_strip_le X pm 0 1 l
    have h2 := quatDist_mul_right (X (pm + (l : ℤ) • unitVec 0) 1)
      (lineHolonomy X p 0 l * lineHolonomy X (p + (l : ℤ) • unitVec 0) 1 m)
      (lineHolonomy X p 1 m * lineHolonomy X pm 0 l)
    have h3 := quatDist_mul_left (lineHolonomy X p 1 m) (lineHolonomy X pm 0 l * X (pm + (l : ℤ) • unitVec 0) 1)
      (X pm 1 * lineHolonomy X (pm + unitVec 1) 0 l)
    have h4 := quatDist_triangle
      (lineHolonomy X p 0 l * lineHolonomy X (p + (l : ℤ) • unitVec 0) 1 m * X (pm + (l : ℤ) • unitVec 0) 1)
      (lineHolonomy X p 1 m * (lineHolonomy X pm 0 l * X (pm + (l : ℤ) • unitVec 0) 1))
      (lineHolonomy X p 1 m * (X pm 1 * lineHolonomy X (pm + unitVec 1) 0 l))
    have e3 : lineHolonomy X p 0 l * lineHolonomy X (p + (l : ℤ) • unitVec 0) 1 (m + 1) =
        lineHolonomy X p 0 l * lineHolonomy X (p + (l : ℤ) • unitVec 0) 1 m * X (pm + (l : ℤ) • unitVec 0) 1 := by
      rw [lineHolonomy, e1, mul_assoc]
    have e4 : lineHolonomy X p 1 (m + 1) * lineHolonomy X (p + ((m + 1 : ℕ) : ℤ) • unitVec 1) 0 l =
        lineHolonomy X p 1 m * (X pm 1 * lineHolonomy X (pm + unitVec 1) 0 l) := by
      rw [e2, lineHolonomy, mul_assoc]
    have e5 : lineHolonomy X p 1 m * lineHolonomy X pm 0 l * X (pm + (l : ℤ) • unitVec 0) 1 =
        lineHolonomy X p 1 m * (lineHolonomy X pm 0 l * X (pm + (l : ℤ) • unitVec 0) 1) := by
      rw [mul_assoc]
    rw [e3, e4]
    rw [e5] at h2
    linarith
theorem quatDist_conj_transport_le (gA gA' gB gB' f u v : UnitQuaternion) (SA SB : ℝ)
    (hA : quatDist u (gA * f * gA'⁻¹) ≤ SA)
    (hB : quatDist v (gB * f * gB'⁻¹) ≤ SB) :
    quatDist (gB * gA⁻¹ * u * (gB' * gA'⁻¹)⁻¹) v ≤ SA + SB := by
  have h1 := quatDist_mul_left (gB * gA⁻¹) u (gA * f * gA'⁻¹)
  have h2 := quatDist_mul_right (gB' * gA'⁻¹)⁻¹ (gB * gA⁻¹ * u) (gB * gA⁻¹ * (gA * f * gA'⁻¹))
  have e : gB * gA⁻¹ * (gA * f * gA'⁻¹) * (gB' * gA'⁻¹)⁻¹ = gB * f * gB'⁻¹ := by group
  rw [e] at h2
  have h3 := quatDist_triangle (gB * gA⁻¹ * u * (gB' * gA'⁻¹)⁻¹) (gB * f * gB'⁻¹) v
  rw [quatDist_comm (gB * f * gB'⁻¹) v] at h3
  linarith
theorem sum_plaquetteDefect_le {α : Type} [DecidableEq α] (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion)
    (kl kh : Fin 4 → ℤ) (M : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hsq : ∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, plaquetteDefect X q.1 0 q.2 ^ 2 ≤ E ^ 2)
    (I : Finset α) (ι : α → (Fin 4 → ℤ) × Fin 4) (hinj : Set.InjOn ι I)
    (hmem : ∀ u ∈ I, ι u ∈ firstAxisPlaquettes kl kh) (hcard : I.card ≤ M ^ 2) :
    ∑ u ∈ I, plaquetteDefect X (ι u).1 0 (ι u).2 ≤ M * E := by
  classical
  have h1 := hsq (I.image ι) (fun q hq => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    exact hmem u hu)
  rw [Finset.sum_image hinj] at h1
  have h2 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun u => plaquetteDefect X (ι u).1 0 (ι u).2)
  have h3 : (I.card : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hcard
  have h4 : (∑ u ∈ I, plaquetteDefect X (ι u).1 0 (ι u).2) ^ 2 ≤ ((M : ℝ) * E) ^ 2 := by
    have h5 : (0 : ℝ) ≤ ∑ u ∈ I, plaquetteDefect X (ι u).1 0 (ι u).2 ^ 2 :=
      Finset.sum_nonneg fun u _ => sq_nonneg _
    calc _ ≤ (I.card : ℝ) * ∑ u ∈ I, plaquetteDefect X (ι u).1 0 (ι u).2 ^ 2 := h2
      _ ≤ (M : ℝ) ^ 2 * E ^ 2 := by
        apply mul_le_mul h3 h1 h5 (by positivity)
      _ = _ := by ring
  exact abs_le_of_sq_le_sq' h4 (by positivity) |>.2
structure Hypotheses (A B : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi w kl kh : Fin 4 → ℤ) (M : ℕ) (E : ℝ) :
    Prop where
  box_bounds : ∀ i, lo i ≤ hi i ∧ hi i - lo i + 3 ≤ M
  bound_nonneg : 0 ≤ E
  cut_zero_ge : lo 0 - 1 ≤ w 0
  cut_zero_le : w 0 ≤ hi 0
  cut_one_ge : lo 1 - 1 ≤ w 1
  cut_one_le : w 1 ≤ hi 1
  outer_zero_hi : hi 0 + 1 ≤ kh 0 ∨ kh 0 ≤ w 0
  outer_zero_lo : kl 0 ≤ lo 0 - 1 ∨ w 0 < kl 0
  outer_one_hi : hi 1 + 1 ≤ kh 1 ∨ kh 1 ≤ w 1
  outer_one_lo : kl 1 ≤ lo 1 - 1 ∨ w 1 < kl 1
  agree : ∀ a i, a ∈ box kl kh → a + unitVec i ∈ box kl kh →
      a ∈ box (lo - 1) (hi + 1) → a + unitVec i ∈ box (lo - 1) (hi + 1) →
      a ∉ box lo hi → a + unitVec i ∉ box lo hi → A a i = B a i
  sq_left : ∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, plaquetteDefect A q.1 0 q.2 ^ 2 ≤ E ^ 2
  sq_right : ∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, plaquetteDefect B q.1 0 q.2 ^ 2 ≤ E ^ 2
def OffBox (lo hi kl kh x : Fin 4 → ℤ) : Prop :=
  x ∈ box kl kh ∧ x ∈ box (lo - 1) (hi + 1) ∧ x ∉ box lo hi
theorem mem_box_widen {lo hi x : Fin 4 → ℤ} :
    x ∈ box (lo - 1) (hi + 1) ↔ ∀ l, lo l - 1 ≤ x l ∧ x l ≤ hi l + 1 := by
  simp [box]
variable {A B : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion} {lo hi w kl kh : Fin 4 → ℤ} {M : ℕ} {E : ℝ}
theorem Hypotheses.agree_of_offBox (S : Hypotheses A B lo hi w kl kh M E) {x : Fin 4 → ℤ} {i : Fin 4}
    (h : OffBox lo hi kl kh x) (h' : OffBox lo hi kl kh (x + unitVec i)) : A x i = B x i :=
  S.agree x i h.1 h'.1 h.2.1 h'.2.1 h.2.2 h'.2.2
theorem Hypotheses.lineHolonomy_eq (S : Hypotheses A B lo hi w kl kh M E) (b : Fin 4 → ℤ) (j : Fin 4) (n : ℕ)
    (H : ∀ r ≤ n, OffBox lo hi kl kh (b + (r : ℤ) • unitVec j)) : lineHolonomy A b j n = lineHolonomy B b j n := by
  refine lineHolonomy_congr A B b j n fun r hr => S.agree_of_offBox (H r hr.le) ?_
  rw [← add_succ_smul_unitVec]
  exact H (r + 1) hr
theorem Hypotheses.sum_strip_le (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (S : Hypotheses A B lo hi w kl kh M E)
    (hsq : ∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, plaquetteDefect X q.1 0 q.2 ^ 2 ≤ E ^ 2)
    (a : Fin 4 → ℤ) (j : Fin 4) (hj : j ≠ 0) (c : ℤ) (n : ℕ) (hc : kl 0 ≤ c) (hcn : c + n ≤ kh 0)
    (ha : a ∈ box kl kh) (ha' : a + unitVec j ∈ box kl kh) (hn : n ≤ M) :
    ∑ r ∈ Finset.range n, plaquetteDefect X (Function.update a 0 c + (r : ℤ) • unitVec 0) 0 j ≤ M * E := by
  have hcard : (Finset.range n).card ≤ M ^ 2 := by
    rw [Finset.card_range]
    nlinarith
  refine sum_plaquetteDefect_le X kl kh M E S.bound_nonneg hsq (Finset.range n)
    (fun r => (Function.update a 0 c + (r : ℤ) • unitVec 0, j)) ?_ ?_ hcard
  · intro r _ r' _ he
    have h1 := congrFun (congrArg Prod.fst he) 0
    simp only [add_smul_unitVec_apply, Function.update_self, if_true] at h1
    omega
  · intro r hr
    have hr' := Finset.mem_range.mp hr
    have coord : ∀ l, l ≠ 0 → (Function.update a 0 c + (r : ℤ) • unitVec 0) l = a l := by
      intro l hl
      rw [add_smul_unitVec_apply, if_neg hl, add_zero, Function.update_of_ne hl]
    have c0 : (Function.update a 0 c + (r : ℤ) • unitVec 0) 0 = c + r := by
      rw [add_smul_unitVec_apply, if_pos rfl, Function.update_self]
    refine ⟨hj, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_⟩
    · dsimp only
      by_cases hl : l = 0
      · subst hl
        rw [c0]
        constructor <;> omega
      · rw [coord l hl]
        exact ha l
    · dsimp only
      by_cases hl : l = 0
      · subst hl
        rw [add_unitVec_apply, c0, if_pos rfl]
        constructor <;> omega
      · rw [add_unitVec_apply, coord l hl, if_neg hl, add_zero]
        exact ha l
    · dsimp only
      by_cases hl : l = 0
      · subst hl
        rw [add_unitVec_apply, c0, if_neg (Ne.symm hj), add_zero]
        constructor <;> omega
      · rw [add_unitVec_apply, coord l hl]
        have := ha' l
        rwa [add_unitVec_apply] at this
    · dsimp only
      by_cases hl : l = 0
      · subst hl
        rw [add_unitVec_apply, add_unitVec_apply, c0, if_pos rfl, if_neg (Ne.symm hj), add_zero]
        constructor <;> omega
      · rw [add_unitVec_apply, add_unitVec_apply, coord l hl, if_neg hl, add_zero]
        have := ha' l
        rwa [add_unitVec_apply] at this
theorem offBox_line (S : Hypotheses A B lo hi w kl kh M E) {x : Fin 4 → ℤ} (hx : x ∉ box lo hi)
    (h0 : lo 0 ≤ x 0 ∧ x 0 ≤ hi 0) (hK : x ∈ box kl kh) (hD : x ∈ box (lo - 1) (hi + 1))
    (c : ℤ) (n : ℕ) (hc₁ : lo 0 - 1 ≤ c) (hc₂ : c + n ≤ hi 0 + 1) (hc₃ : kl 0 ≤ c) (hc₄ : c + n ≤ kh 0) :
    ∀ r ≤ n, OffBox lo hi kl kh (Function.update x 0 c + (r : ℤ) • unitVec 0) := by
  intro r hr
  have coord : ∀ l, l ≠ 0 → (Function.update x 0 c + (r : ℤ) • unitVec 0) l = x l := by
    intro l hl
    rw [add_smul_unitVec_apply, if_neg hl, add_zero, Function.update_of_ne hl]
  have c0 : (Function.update x 0 c + (r : ℤ) • unitVec 0) 0 = c + r := by
    rw [add_smul_unitVec_apply, if_pos rfl, Function.update_self]
  refine ⟨fun l => ?_, mem_box_widen.mpr fun l => ?_, fun hin => hx fun l => ?_⟩
  · by_cases hl : l = 0
    · subst hl
      rw [c0]
      constructor <;> omega
    · rw [coord l hl]
      exact hK l
  · by_cases hl : l = 0
    · subst hl
      rw [c0]
      constructor <;> omega
    · rw [coord l hl]
      exact mem_box_widen.mp hD l
  · by_cases hl : l = 0
    · subst hl
      exact h0
    · have := hin l
      rwa [coord l hl] at this
theorem boxGaugeTransform_of_cut_lt (S : Hypotheses A B lo hi w kl kh M E) {x : Fin 4 → ℤ} (hw : w 0 < x 0)
    (hx₂ : x 0 ≤ hi 0) (hK : x ∈ box kl kh) (hD : x ∈ box (lo - 1) (hi + 1)) :
    boxGaugeTransform A B lo hi w x =
      lineHolonomy B x 0 (hi 0 + 1 - x 0).toNat * (lineHolonomy A x 0 (hi 0 + 1 - x 0).toNat)⁻¹ := by
  have hup : hi 0 + 1 ≤ kh 0 := S.outer_zero_hi.resolve_right (by have := (hK 0).2; omega)
  by_cases hb : x ∈ box lo hi
  · simp only [boxGaugeTransform, if_pos hb, exitHolonomy, if_pos hw]
  · rw [boxGaugeTransform, if_neg hb]
    have hn : (((hi 0 + 1 - x 0).toNat : ℕ) : ℤ) = hi 0 + 1 - x 0 := by omega
    have h1 := offBox_line S hb ⟨by have := S.cut_zero_ge; omega, hx₂⟩ hK hD (x 0) (hi 0 + 1 - x 0).toNat
      (by have := S.cut_zero_ge; omega) (by omega) (hK 0).1 (by omega)
    rw [Function.update_eq_self] at h1
    rw [S.lineHolonomy_eq x 0 _ h1]
    group
theorem boxGaugeTransform_of_le_cut (S : Hypotheses A B lo hi w kl kh M E) {x : Fin 4 → ℤ} (hw : x 0 ≤ w 0)
    (hx₁ : lo 0 ≤ x 0) (hK : x ∈ box kl kh) (hD : x ∈ box (lo - 1) (hi + 1)) :
    boxGaugeTransform A B lo hi w x =
      (lineHolonomy B (Function.update x 0 (lo 0 - 1)) 0 (x 0 - lo 0 + 1).toNat)⁻¹ *
        lineHolonomy A (Function.update x 0 (lo 0 - 1)) 0 (x 0 - lo 0 + 1).toNat := by
  have hdn : kl 0 ≤ lo 0 - 1 := S.outer_zero_lo.resolve_right (by have := (hK 0).1; omega)
  by_cases hb : x ∈ box lo hi
  · simp only [boxGaugeTransform, if_pos hb, exitHolonomy, if_neg (not_lt.mpr hw), inv_inv]
  · rw [boxGaugeTransform, if_neg hb]
    have hn : (((x 0 - lo 0 + 1).toNat : ℕ) : ℤ) = x 0 - lo 0 + 1 := by omega
    have h1 := offBox_line S hb ⟨hx₁, by have := S.cut_zero_le; omega⟩ hK hD (lo 0 - 1) (x 0 - lo 0 + 1).toNat
      le_rfl (by have := S.cut_zero_le; omega) hdn (by have := (hK 0).2; omega)
    rw [S.lineHolonomy_eq _ 0 _ h1]
    group
theorem Hypotheses.le_size (S : Hypotheses A B lo hi w kl kh M E) (i : Fin 4) (n : ℕ)
    (hn : (n : ℤ) ≤ hi i - lo i + 3) : n ≤ M := by
  have := (S.box_bounds i).2
  omega
theorem quatDist_transverse_of_cut_lt (S : Hypotheses A B lo hi w kl kh M E) (a : Fin 4 → ℤ) (i : Fin 4)
    (hi0 : i ≠ 0) (hw : w 0 < a 0) (hx₂ : a 0 ≤ hi 0) (ha : a ∈ box kl kh) (ha' : a + unitVec i ∈ box kl kh)
    (hd : a ∈ box (lo - 1) (hi + 1)) (hd' : a + unitVec i ∈ box (lo - 1) (hi + 1)) :
    quatDist (boxGaugeTransform A B lo hi w a * A a i * (boxGaugeTransform A B lo hi w (a + unitVec i))⁻¹)
      (B a i) ≤ 2 * M * E := by
  have hup : hi 0 + 1 ≤ kh 0 := S.outer_zero_hi.resolve_right (by have := (ha 0).2; omega)
  have e0 : (a + unitVec i) 0 = a 0 := by simp [unitVec_apply_of_ne (Ne.symm hi0)]
  set n := (hi 0 + 1 - a 0).toNat with hn
  have hnz : (n : ℤ) = hi 0 + 1 - a 0 := by omega
  have hnM : n ≤ M := S.le_size 0 n (by have := S.cut_zero_ge; omega)
  have g1 := boxGaugeTransform_of_cut_lt S hw hx₂ ha hd
  have g2 := boxGaugeTransform_of_cut_lt S (x := a + unitVec i) (by rw [e0]; exact hw) (by rw [e0]; exact hx₂)
    ha' hd'
  rw [e0, ← hn] at g2
  rw [← hn] at g1
  have s₁ := S.sum_strip_le A S.sq_left a i hi0 (a 0) n (ha 0).1 (by omega) ha ha' hnM
  have s₂ := S.sum_strip_le B S.sq_right a i hi0 (a 0) n (ha 0).1 (by omega) ha ha' hnM
  rw [Function.update_eq_self] at s₁ s₂
  have t₁ := quatDist_strip_le A a 0 i n
  have t₂ := quatDist_strip_le B a 0 i n
  set e := a + (n : ℤ) • unitVec 0 with he
  have off : ∀ d : ℕ, d ≤ 1 → OffBox lo hi kl kh (e + (d : ℤ) • unitVec i) := by
    intro d hdd
    have hdz : (d : ℤ) ≤ 1 := by exact_mod_cast hdd
    have c0 : (e + (d : ℤ) • unitVec i) 0 = hi 0 + 1 := by
      rw [add_smul_unitVec_apply, if_neg (Ne.symm hi0), he, add_smul_unitVec_apply, if_pos rfl]
      omega
    have coord : ∀ l, l ≠ 0 → (e + (d : ℤ) • unitVec i) l = (a + (d : ℤ) • unitVec i) l := by
      intro l hl
      rw [add_smul_unitVec_apply, add_smul_unitVec_apply, he, add_smul_unitVec_apply, if_neg hl, add_zero]
    have mid : ∀ l, l ≠ 0 → ∀ (lo' hi' : Fin 4 → ℤ), a ∈ box lo' hi' → a + unitVec i ∈ box lo' hi' →
        lo' l ≤ (e + (d : ℤ) • unitVec i) l ∧ (e + (d : ℤ) • unitVec i) l ≤ hi' l := by
      intro l hl lo' hi' h₁ h₂
      rw [coord l hl]
      interval_cases d
      · simpa using h₁ l
      · simpa using h₂ l
    refine ⟨fun l => ?_, fun l => ?_, fun hin => ?_⟩
    · by_cases hl : l = 0
      · subst hl
        rw [c0]
        exact ⟨by have := (ha 0).1; have := S.cut_zero_ge; omega, hup⟩
      · exact mid l hl _ _ ha ha'
    · by_cases hl : l = 0
      · subst hl
        rw [c0]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
        have := (S.box_bounds 0).1
        constructor <;> omega
      · exact mid l hl _ _ hd hd'
    · have := (hin 0).2
      rw [c0] at this
      omega
  have ef : A e i = B e i := by
    have h0 := off 0 (by omega)
    have h1 := off 1 le_rfl
    simp only [Nat.cast_zero, zero_smul, add_zero, Nat.cast_one, one_smul] at h0 h1
    exact S.agree_of_offBox h0 h1
  rw [g1, g2]
  have hA : quatDist (A a i) (lineHolonomy A a 0 n * B e i * (lineHolonomy A (a + unitVec i) 0 n)⁻¹) ≤ M * E := by
    have h1 := quatDist_mul_right (lineHolonomy A (a + unitVec i) 0 n) (A a i)
      (lineHolonomy A a 0 n * B e i * (lineHolonomy A (a + unitVec i) 0 n)⁻¹)
    rw [← h1, inv_mul_cancel_right, quatDist_comm, ← ef]
    linarith
  have hB : quatDist (B a i) (lineHolonomy B a 0 n * B e i * (lineHolonomy B (a + unitVec i) 0 n)⁻¹) ≤ M * E := by
    have h1 := quatDist_mul_right (lineHolonomy B (a + unitVec i) 0 n) (B a i)
      (lineHolonomy B a 0 n * B e i * (lineHolonomy B (a + unitVec i) 0 n)⁻¹)
    rw [← h1, inv_mul_cancel_right, quatDist_comm]
    linarith
  have := quatDist_conj_transport_le _ _ _ _ _ _ _ _ _ hA hB
  linarith
theorem quatDist_transverse_of_le_cut (S : Hypotheses A B lo hi w kl kh M E) (a : Fin 4 → ℤ) (i : Fin 4)
    (hi0 : i ≠ 0) (hw : a 0 ≤ w 0) (hx₁ : lo 0 ≤ a 0) (ha : a ∈ box kl kh) (ha' : a + unitVec i ∈ box kl kh)
    (hd : a ∈ box (lo - 1) (hi + 1)) (hd' : a + unitVec i ∈ box (lo - 1) (hi + 1)) :
    quatDist (boxGaugeTransform A B lo hi w a * A a i * (boxGaugeTransform A B lo hi w (a + unitVec i))⁻¹)
      (B a i) ≤ 2 * M * E := by
  have hdn : kl 0 ≤ lo 0 - 1 := S.outer_zero_lo.resolve_right (by have := (ha 0).1; omega)
  have e0 : (a + unitVec i) 0 = a 0 := by simp [unitVec_apply_of_ne (Ne.symm hi0)]
  set n := (a 0 - lo 0 + 1).toNat with hn
  have hnz : (n : ℤ) = a 0 - lo 0 + 1 := by omega
  have hnM : n ≤ M := S.le_size 0 n (by have := S.cut_zero_le; omega)
  have g1 := boxGaugeTransform_of_le_cut S hw hx₁ ha hd
  have g2 := boxGaugeTransform_of_le_cut S (x := a + unitVec i) (by rw [e0]; exact hw) (by rw [e0]; exact hx₁)
    ha' hd'
  rw [e0, ← hn, update_add_unitVec_of_ne a hi0] at g2
  rw [← hn] at g1
  set e := Function.update a 0 (lo 0 - 1) with he
  have hkn : lo 0 - 1 + n ≤ kh 0 := by have := (ha 0).2; omega
  have s₁ := S.sum_strip_le A S.sq_left a i hi0 (lo 0 - 1) n hdn hkn ha ha' hnM
  have s₂ := S.sum_strip_le B S.sq_right a i hi0 (lo 0 - 1) n hdn hkn ha ha' hnM
  rw [← he] at s₁ s₂
  have t₁ := quatDist_strip_le A e 0 i n
  have t₂ := quatDist_strip_le B e 0 i n
  have ea : e + (n : ℤ) • unitVec 0 = a := by
    have := update_add_smul_unitVec a 0 (lo 0 - 1) (by omega)
    have e2 : (a 0 - (lo 0 - 1)).toNat = n := by omega
    rwa [e2] at this
  rw [ea] at t₁ t₂
  have off : ∀ d : ℕ, d ≤ 1 → OffBox lo hi kl kh (e + (d : ℤ) • unitVec i) := by
    intro d hdd
    have hdz : (d : ℤ) ≤ 1 := by exact_mod_cast hdd
    have c0 : (e + (d : ℤ) • unitVec i) 0 = lo 0 - 1 := by
      rw [add_smul_unitVec_apply, if_neg (Ne.symm hi0), he, Function.update_self]
      omega
    have coord : ∀ l, l ≠ 0 → (e + (d : ℤ) • unitVec i) l = (a + (d : ℤ) • unitVec i) l := by
      intro l hl
      rw [add_smul_unitVec_apply, add_smul_unitVec_apply, he, Function.update_of_ne hl]
    have mid : ∀ l, l ≠ 0 → ∀ (lo' hi' : Fin 4 → ℤ), a ∈ box lo' hi' → a + unitVec i ∈ box lo' hi' →
        lo' l ≤ (e + (d : ℤ) • unitVec i) l ∧ (e + (d : ℤ) • unitVec i) l ≤ hi' l := by
      intro l hl lo' hi' h₁ h₂
      rw [coord l hl]
      interval_cases d
      · simpa using h₁ l
      · simpa using h₂ l
    refine ⟨fun l => ?_, fun l => ?_, fun hin => ?_⟩
    · by_cases hl : l = 0
      · subst hl
        rw [c0]
        exact ⟨hdn, by have := (ha 0).2; omega⟩
      · exact mid l hl _ _ ha ha'
    · by_cases hl : l = 0
      · subst hl
        rw [c0]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
        have := (S.box_bounds 0).1
        constructor <;> omega
      · exact mid l hl _ _ hd hd'
    · have := (hin 0).1
      rw [c0] at this
      omega
  have ef : A e i = B e i := by
    have h0 := off 0 (by omega)
    have h1 := off 1 le_rfl
    simp only [Nat.cast_zero, zero_smul, add_zero, Nat.cast_one, one_smul] at h0 h1
    exact S.agree_of_offBox h0 h1
  rw [g1, g2]
  have hA : quatDist (A a i)
      ((lineHolonomy A e 0 n)⁻¹ * B e i * ((lineHolonomy A (e + unitVec i) 0 n)⁻¹)⁻¹) ≤ M * E := by
    have h1 := quatDist_mul_left (lineHolonomy A e 0 n) (A a i)
      ((lineHolonomy A e 0 n)⁻¹ * B e i * ((lineHolonomy A (e + unitVec i) 0 n)⁻¹)⁻¹)
    have e3 : lineHolonomy A e 0 n * ((lineHolonomy A e 0 n)⁻¹ * B e i * ((lineHolonomy A (e + unitVec i) 0 n)⁻¹)⁻¹) =
        A e i * lineHolonomy A (e + unitVec i) 0 n := by
      rw [ef]
      group
    rw [← h1, e3]
    linarith
  have hB : quatDist (B a i)
      ((lineHolonomy B e 0 n)⁻¹ * B e i * ((lineHolonomy B (e + unitVec i) 0 n)⁻¹)⁻¹) ≤ M * E := by
    have h1 := quatDist_mul_left (lineHolonomy B e 0 n) (B a i)
      ((lineHolonomy B e 0 n)⁻¹ * B e i * ((lineHolonomy B (e + unitVec i) 0 n)⁻¹)⁻¹)
    have e3 : lineHolonomy B e 0 n * ((lineHolonomy B e 0 n)⁻¹ * B e i * ((lineHolonomy B (e + unitVec i) 0 n)⁻¹)⁻¹) =
        B e i * lineHolonomy B (e + unitVec i) 0 n := by
      group
    rw [← h1, e3]
    linarith
  have h9 := quatDist_conj_transport_le ((lineHolonomy A e 0 n)⁻¹) ((lineHolonomy A (e + unitVec i) 0 n)⁻¹)
    ((lineHolonomy B e 0 n)⁻¹) ((lineHolonomy B (e + unitVec i) 0 n)⁻¹) (B e i) (A a i) (B a i) _ _ hA hB
  have e4 : (lineHolonomy B e 0 n)⁻¹ * lineHolonomy A e 0 n * A a i *
      ((lineHolonomy B (e + unitVec i) 0 n)⁻¹ * lineHolonomy A (e + unitVec i) 0 n)⁻¹ =
      (lineHolonomy B e 0 n)⁻¹ * ((lineHolonomy A e 0 n)⁻¹)⁻¹ * A a i *
      ((lineHolonomy B (e + unitVec i) 0 n)⁻¹ * ((lineHolonomy A (e + unitVec i) 0 n)⁻¹)⁻¹)⁻¹ := by
    group
  rw [e4]
  linarith
theorem add_grid_apply (b : Fin 4 → ℤ) (r c : ℕ) (l : Fin 4) :
    (b + (r : ℤ) • unitVec 1 + (c : ℤ) • unitVec 0) l =
      b l + (if l = 1 then (r : ℤ) else 0) + (if l = 0 then (c : ℤ) else 0) := by
  rw [add_smul_unitVec_apply, add_smul_unitVec_apply]
theorem Hypotheses.sum_rectangle_le (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion)
    (S : Hypotheses A B lo hi w kl kh M E)
    (hsq : ∀ Q : Finset ((Fin 4 → ℤ) × Fin 4), (∀ q ∈ Q, q ∈ firstAxisPlaquettes kl kh) →
      ∑ q ∈ Q, plaquetteDefect X q.1 0 q.2 ^ 2 ≤ E ^ 2)
    (b : Fin 4 → ℤ) (l m : ℕ) (hb : ∀ k, k ≠ 0 → k ≠ 1 → kl k ≤ b k ∧ b k ≤ kh k)
    (h0 : kl 0 ≤ b 0) (h0' : b 0 + l ≤ kh 0) (h1 : kl 1 ≤ b 1) (h1' : b 1 + m ≤ kh 1)
    (hl : l ≤ M) (hm : m ≤ M) :
    ∑ r ∈ Finset.range m, ∑ c ∈ Finset.range l,
      plaquetteDefect X (b + (r : ℤ) • unitVec 1 + (c : ℤ) • unitVec 0) 0 1 ≤ M * E := by
  have hcard : (Finset.range m ×ˢ Finset.range l).card ≤ M ^ 2 := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
    nlinarith
  have h := sum_plaquetteDefect_le X kl kh M E S.bound_nonneg hsq (Finset.range m ×ˢ Finset.range l)
    (fun u => (b + (u.1 : ℤ) • unitVec 1 + (u.2 : ℤ) • unitVec 0, (1 : Fin 4))) ?_ ?_ hcard
  · rwa [Finset.sum_product] at h
  · intro u _ u' _ he
    have hq := congrArg Prod.fst he
    have e0 := congrFun hq 0
    have e1 := congrFun hq 1
    dsimp only at e0 e1
    rw [add_grid_apply, add_grid_apply] at e0 e1
    simp at e0 e1
    exact Prod.ext e1 e0
  · intro u hu
    obtain ⟨hr, hc⟩ := Finset.mem_product.mp hu
    have hr' : (u.1 : ℤ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hr
    have hc' : (u.2 : ℤ) + 1 ≤ l := by exact_mod_cast Finset.mem_range.mp hc
    refine ⟨show (1 : Fin 4) ≠ 0 by decide, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩ <;> dsimp only
    all_goals
      simp only [add_unitVec_apply, add_grid_apply]
      by_cases k0 : k = 0
      · subst k0
        simp
        constructor <;> omega
      by_cases k1 : k = 1
      · subst k1
        simp
        constructor <;> omega
      · have := hb k k0 k1
        simp [k0, k1, this]
theorem offBox_of_coords (S : Hypotheses A B lo hi w kl kh M E) {a x : Fin 4 → ℤ} (ha : a ∈ box kl kh)
    (hrow : ∀ l, l ≠ 0 → lo l ≤ a l ∧ a l ≤ hi l) (hother : ∀ l, l ≠ 0 → l ≠ 1 → x l = a l)
    (h0 : lo 0 - 1 ≤ x 0 ∧ x 0 ≤ hi 0 + 1) (h1 : lo 1 - 1 ≤ x 1 ∧ x 1 ≤ hi 1 + 1)
    (k0 : kl 0 ≤ x 0 ∧ x 0 ≤ kh 0) (k1 : kl 1 ≤ x 1 ∧ x 1 ≤ kh 1)
    (hout : x 0 < lo 0 ∨ hi 0 < x 0 ∨ x 1 < lo 1 ∨ hi 1 < x 1) : OffBox lo hi kl kh x := by
  refine ⟨fun l => ?_, mem_box_widen.mpr fun l => ?_, fun hin => ?_⟩
  · by_cases l0 : l = 0
    · subst l0
      exact k0
    by_cases l1 : l = 1
    · subst l1
      exact k1
    · rw [hother l l0 l1]
      exact ha l
  · by_cases l0 : l = 0
    · subst l0
      exact h0
    by_cases l1 : l = 1
    · subst l1
      exact h1
    · rw [hother l l0 l1]
      have := hrow l l0
      constructor <;> omega
  · have a0 := hin 0
    have a1 := hin 1
    omega
theorem quatDist_le_of_coordBounds (S : Hypotheses A B lo hi w kl kh M E) {a : Fin 4 → ℤ}
    (hrow : ∀ l, l ≠ 0 → lo l ≤ a l ∧ a l ≤ hi l)
    (ha : a ∈ box kl kh) (hk0 : kl 0 ≤ lo 0 - 1) (hk0' : hi 0 + 1 ≤ kh 0) (l : ℕ)
    (hl : (l : ℤ) = hi 0 - lo 0 + 2) :
    quatDist (lineHolonomy A (Function.update a 0 (lo 0 - 1)) 0 l)
      (lineHolonomy B (Function.update a 0 (lo 0 - 1)) 0 l) ≤ 2 * M * E := by
  set p := Function.update a 0 (lo 0 - 1) with hp
  have p0 : p 0 = lo 0 - 1 := by simp [p]
  have pl : ∀ k, k ≠ 0 → p k = a k := fun k hk => by simp [p, Function.update_of_ne hk]
  have hr1 := hrow 1 (by decide)
  have ka1 : kl 1 ≤ a 1 ∧ a 1 ≤ kh 1 := ha 1
  have hlo0 := (S.box_bounds 0).1
  have hlM : l ≤ M := S.le_size 0 l (by omega)
  have hbK : ∀ k, k ≠ 0 → k ≠ 1 → kl k ≤ p k ∧ p k ≤ kh k := fun k h₀ _ => by
    rw [pl k h₀]
    exact ha k
  have hother : ∀ (b : Fin 4 → ℤ), (∀ k, k ≠ 0 → k ≠ 1 → b k = p k) → ∀ k, k ≠ 0 → k ≠ 1 → b k = a k :=
    fun b hb k h₀ h₁ => by rw [hb k h₀ h₁, pl k h₀]
  by_cases hw : w 1 < a 1
  · have hup : hi 1 + 1 ≤ kh 1 := S.outer_one_hi.resolve_right (by have := (ha 1).2; omega)
    set m := (hi 1 + 1 - a 1).toNat with hm
    have hmz : (m : ℤ) = hi 1 + 1 - a 1 := by omega
    have hmM : m ≤ M := S.le_size 1 m (by omega)
    have p1 : p 1 = a 1 := pl 1 (by decide)
    have sA := S.sum_rectangle_le A S.sq_left p l m hbK (by omega) (by omega) (by rw [p1]; exact (ha 1).1)
      (by omega) hlM hmM
    have sB := S.sum_rectangle_le B S.sq_right p l m hbK (by omega) (by omega) (by rw [p1]; exact (ha 1).1)
      (by omega) hlM hmM
    have tA := quatDist_rectangle_le A p l m
    have tB := quatDist_rectangle_le B p l m
    have col₁ : lineHolonomy A (p + (l : ℤ) • unitVec 0) 1 m = lineHolonomy B (p + (l : ℤ) • unitVec 0) 1 m := by
      refine S.lineHolonomy_eq _ 1 m fun r hr => ?_
      have hr' : (r : ℤ) ≤ m := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₁, add_zero, add_smul_unitVec_apply, if_neg h₀, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, p0, p1]
        try simp
        try omega
    have col₂ : lineHolonomy A p 1 m = lineHolonomy B p 1 m := by
      refine S.lineHolonomy_eq _ 1 m fun r hr => ?_
      have hr' : (r : ℤ) ≤ m := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₁, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, p0, p1]
        try simp
        try omega
    have top : lineHolonomy A (p + (m : ℤ) • unitVec 1) 0 l = lineHolonomy B (p + (m : ℤ) • unitVec 1) 0 l := by
      refine S.lineHolonomy_eq _ 0 l fun r hr => ?_
      have hr' : (r : ℤ) ≤ l := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₀, add_zero, add_smul_unitVec_apply, if_neg h₁, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, p0, p1]
        try simp
        try omega
    rw [col₁, col₂, top] at tA
    rw [← quatDist_mul_right (lineHolonomy B (p + (l : ℤ) • unitVec 0) 1 m) (lineHolonomy A p 0 l)]
    have h3 := quatDist_triangle (lineHolonomy A p 0 l * lineHolonomy B (p + (l : ℤ) • unitVec 0) 1 m)
      (lineHolonomy B p 1 m * lineHolonomy B (p + (m : ℤ) • unitVec 1) 0 l)
      (lineHolonomy B p 0 l * lineHolonomy B (p + (l : ℤ) • unitVec 0) 1 m)
    rw [quatDist_comm (lineHolonomy B p 1 m * lineHolonomy B (p + (m : ℤ) • unitVec 1) 0 l)] at h3
    linarith
  · have hwz : a 1 ≤ w 1 := not_lt.mp hw
    have hdn : kl 1 ≤ lo 1 - 1 := S.outer_one_lo.resolve_right (by have := (ha 1).1; omega)
    set e := Function.update p 1 (lo 1 - 1) with he
    set m := (a 1 - lo 1 + 1).toNat with hm
    have hmz : (m : ℤ) = a 1 - lo 1 + 1 := by omega
    have hmM : m ≤ M := S.le_size 1 m (by omega)
    have e0 : e 0 = lo 0 - 1 := by
      simp only [e, Function.update_of_ne (show (0 : Fin 4) ≠ 1 by decide)]
      exact p0
    have e1 : e 1 = lo 1 - 1 := by simp [e]
    have el : ∀ k, k ≠ 1 → e k = p k := fun k hk => by simp [e, Function.update_of_ne hk]
    have hbK' : ∀ k, k ≠ 0 → k ≠ 1 → kl k ≤ e k ∧ e k ≤ kh k := fun k h₀ h₁ => by
      rw [el k h₁]
      exact hbK k h₀ h₁
    have hother' : ∀ (b : Fin 4 → ℤ), (∀ k, k ≠ 0 → k ≠ 1 → b k = e k) → ∀ k, k ≠ 0 → k ≠ 1 → b k = a k :=
      fun b hb k h₀ h₁ => by rw [hb k h₀ h₁, el k h₁, pl k h₀]
    have ep : e + (m : ℤ) • unitVec 1 = p := by
      have h1 := update_add_smul_unitVec p 1 (lo 1 - 1) (by
        rw [pl 1 (by decide)]
        omega)
      have h2 : (p 1 - (lo 1 - 1)).toNat = m := by
        rw [pl 1 (by decide)]
        omega
      rwa [h2] at h1
    have sA := S.sum_rectangle_le A S.sq_left e l m hbK' (by omega) (by omega) (by omega)
      (by have := (ha 1).2; omega) hlM hmM
    have sB := S.sum_rectangle_le B S.sq_right e l m hbK' (by omega) (by omega) (by omega)
      (by have := (ha 1).2; omega) hlM hmM
    have tA := quatDist_rectangle_le A e l m
    have tB := quatDist_rectangle_le B e l m
    rw [ep] at tA tB
    have col₁ : lineHolonomy A (e + (l : ℤ) • unitVec 0) 1 m = lineHolonomy B (e + (l : ℤ) • unitVec 0) 1 m := by
      refine S.lineHolonomy_eq _ 1 m fun r hr => ?_
      have hr' : (r : ℤ) ≤ m := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother' _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₁, add_zero, add_smul_unitVec_apply, if_neg h₀, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, e0, e1]
        try simp
        try omega
    have col₂ : lineHolonomy A e 1 m = lineHolonomy B e 1 m := by
      refine S.lineHolonomy_eq _ 1 m fun r hr => ?_
      have hr' : (r : ℤ) ≤ m := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother' _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₁, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, e0, e1]
        try simp
        try omega
    have bot : lineHolonomy A e 0 l = lineHolonomy B e 0 l := by
      refine S.lineHolonomy_eq _ 0 l fun r hr => ?_
      have hr' : (r : ℤ) ≤ l := by exact_mod_cast hr
      refine offBox_of_coords S ha hrow (hother' _ fun k h₀ h₁ => ?_) ?_ ?_ ?_ ?_ ?_
      · rw [add_smul_unitVec_apply, if_neg h₀, add_zero]
      all_goals
        simp only [add_smul_unitVec_apply, e0, e1]
        try simp
        try omega
    rw [col₁, col₂, bot] at tA
    rw [← quatDist_mul_left (lineHolonomy B e 1 m) (lineHolonomy A p 0 l)]
    have h3 := quatDist_triangle (lineHolonomy B e 1 m * lineHolonomy A p 0 l)
      (lineHolonomy B e 0 l * lineHolonomy B (e + (l : ℤ) • unitVec 0) 1 m)
      (lineHolonomy B e 1 m * lineHolonomy B p 0 l)
    rw [quatDist_comm (lineHolonomy B e 1 m * lineHolonomy A p 0 l)
      (lineHolonomy B e 0 l * lineHolonomy B (e + (l : ℤ) • unitVec 0) 1 m)] at h3
    linarith
theorem lineHolonomy_one_add (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (a : Fin 4 → ℤ) (i : Fin 4) (n : ℕ) :
    lineHolonomy X a i (1 + n) = X a i * lineHolonomy X (a + unitVec i) i n := by
  rw [lineHolonomy_add]
  simp [lineHolonomy]
theorem along_of_cut_lt (S : Hypotheses A B lo hi w kl kh M E) (a : Fin 4 → ℤ) (hw : w 0 < a 0)
    (ha : a ∈ box kl kh) (ha' : a + unitVec 0 ∈ box kl kh) (hd : a ∈ box (lo - 1) (hi + 1))
    (hd' : a + unitVec 0 ∈ box (lo - 1) (hi + 1)) :
    boxGaugeTransform A B lo hi w a * A a 0 * (boxGaugeTransform A B lo hi w (a + unitVec 0))⁻¹ = B a 0 := by
  have e0 : (a + unitVec 0) 0 = a 0 + 1 := by simp [unitVec_apply_self]
  have h2 : a 0 ≤ hi 0 := by
    have := (mem_box_widen.mp hd' 0).2
    rw [e0] at this
    omega
  set n := (hi 0 - a 0).toNat with hn
  have hnz : (n : ℤ) = hi 0 - a 0 := by omega
  have hk : (hi 0 + 1 - a 0).toNat = 1 + n := by omega
  have g1 := boxGaugeTransform_of_cut_lt S hw h2 ha hd
  rw [hk, lineHolonomy_one_add, lineHolonomy_one_add] at g1
  have g2 : boxGaugeTransform A B lo hi w (a + unitVec 0) =
      lineHolonomy B (a + unitVec 0) 0 n * (lineHolonomy A (a + unitVec 0) 0 n)⁻¹ := by
    by_cases h3 : a 0 + 1 ≤ hi 0
    · have := boxGaugeTransform_of_cut_lt S (x := a + unitVec 0) (by rw [e0]; omega) (by rw [e0]; omega) ha' hd'
      have e2 : (hi 0 + 1 - (a + unitVec 0) 0).toNat = n := by
        rw [e0]
        omega
      rwa [e2] at this
    · have hz : n = 0 := by omega
      have hb : a + unitVec 0 ∉ box lo hi := fun hin => by
        have := (hin 0).2
        rw [e0] at this
        omega
      rw [boxGaugeTransform, if_neg hb, hz]
      simp [lineHolonomy]
  rw [g1, g2]
  group
theorem along_of_succ_le_cut (S : Hypotheses A B lo hi w kl kh M E) (a : Fin 4 → ℤ) (hw : a 0 + 1 ≤ w 0)
    (ha : a ∈ box kl kh) (ha' : a + unitVec 0 ∈ box kl kh) (hd : a ∈ box (lo - 1) (hi + 1))
    (hd' : a + unitVec 0 ∈ box (lo - 1) (hi + 1)) :
    boxGaugeTransform A B lo hi w a * A a 0 * (boxGaugeTransform A B lo hi w (a + unitVec 0))⁻¹ = B a 0 := by
  have e0 : (a + unitVec 0) 0 = a 0 + 1 := by simp [unitVec_apply_self]
  have h1 : lo 0 - 1 ≤ a 0 := (mem_box_widen.mp hd 0).1
  set n := (a 0 - lo 0 + 1).toNat with hn
  have hnz : (n : ℤ) = a 0 - lo 0 + 1 := by omega
  set e := Function.update a 0 (lo 0 - 1) with he
  have ea : e + (n : ℤ) • unitVec 0 = a := by
    have h3 := update_add_smul_unitVec a 0 (lo 0 - 1) h1
    have h4 : (a 0 - (lo 0 - 1)).toNat = n := by omega
    rwa [h4] at h3
  have g2 := boxGaugeTransform_of_le_cut S (x := a + unitVec 0) (by rw [e0]; exact hw) (by rw [e0]; omega) ha' hd'
  have hk : ((a + unitVec 0) 0 - lo 0 + 1).toNat = n + 1 := by
    rw [e0]
    omega
  rw [hk, update_add_unitVec_self, ← he] at g2
  have line_last : ∀ X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion,
      lineHolonomy X e 0 (n + 1) = lineHolonomy X e 0 n * X a 0 := by
    intro X
    rw [lineHolonomy, ea]
  rw [line_last, line_last] at g2
  have g1 : boxGaugeTransform A B lo hi w a = (lineHolonomy B e 0 n)⁻¹ * lineHolonomy A e 0 n := by
    by_cases h3 : lo 0 ≤ a 0
    · have := boxGaugeTransform_of_le_cut S (x := a) (by omega) h3 ha hd
      rwa [← hn, ← he] at this
    · have hz : n = 0 := by omega
      have hb : a ∉ box lo hi := fun hin => h3 (hin 0).1
      rw [boxGaugeTransform, if_neg hb, hz]
      simp [lineHolonomy]
  rw [g1, g2]
  group
theorem quatDist_across_cut (S : Hypotheses A B lo hi w kl kh M E) (a : Fin 4 → ℤ) (hw : a 0 = w 0)
    (hrow : ∀ l, l ≠ 0 → lo l ≤ a l ∧ a l ≤ hi l) (ha : a ∈ box kl kh)
    (ha' : a + unitVec 0 ∈ box kl kh) (hd : a ∈ box (lo - 1) (hi + 1))
    (hd' : a + unitVec 0 ∈ box (lo - 1) (hi + 1)) :
    quatDist (boxGaugeTransform A B lo hi w a * A a 0 * (boxGaugeTransform A B lo hi w (a + unitVec 0))⁻¹)
      (B a 0) ≤ 2 * M * E := by
  have e0 : (a + unitVec 0) 0 = a 0 + 1 := by simp [unitVec_apply_self]
  have w0a := S.cut_zero_ge
  have w0b := S.cut_zero_le
  have hk0 : kl 0 ≤ lo 0 - 1 := S.outer_zero_lo.resolve_right (by have := (ha 0).1; omega)
  have hk0' : hi 0 + 1 ≤ kh 0 := S.outer_zero_hi.resolve_right (by
    have := (ha' 0).2
    rw [e0] at this
    omega)
  set n₁ := (a 0 - lo 0 + 1).toNat with hn₁
  set n₂ := (hi 0 - a 0).toNat with hn₂
  have hz₁ : (n₁ : ℤ) = a 0 - lo 0 + 1 := by omega
  have hz₂ : (n₂ : ℤ) = hi 0 - a 0 := by omega
  set p := Function.update a 0 (lo 0 - 1) with hp
  have pa : p + (n₁ : ℤ) • unitVec 0 = a := by
    have h3 := update_add_smul_unitVec a 0 (lo 0 - 1) (by omega)
    have h4 : (a 0 - (lo 0 - 1)).toNat = n₁ := by omega
    rwa [h4] at h3
  have g1 : boxGaugeTransform A B lo hi w a = (lineHolonomy B p 0 n₁)⁻¹ * lineHolonomy A p 0 n₁ := by
    by_cases h3 : lo 0 ≤ a 0
    · have := boxGaugeTransform_of_le_cut S (x := a) (by omega) h3 ha hd
      rwa [← hn₁, ← hp] at this
    · have hz : n₁ = 0 := by omega
      have hb : a ∉ box lo hi := fun hin => h3 (hin 0).1
      rw [boxGaugeTransform, if_neg hb, hz]
      simp [lineHolonomy]
  have g2 : boxGaugeTransform A B lo hi w (a + unitVec 0) =
      lineHolonomy B (a + unitVec 0) 0 n₂ * (lineHolonomy A (a + unitVec 0) 0 n₂)⁻¹ := by
    by_cases h3 : a 0 + 1 ≤ hi 0
    · have := boxGaugeTransform_of_cut_lt S (x := a + unitVec 0) (by rw [e0]; omega) (by rw [e0]; omega) ha' hd'
      have e2 : (hi 0 + 1 - (a + unitVec 0) 0).toNat = n₂ := by
        rw [e0]
        omega
      rwa [e2] at this
    · have hz : n₂ = 0 := by omega
      have hb : a + unitVec 0 ∉ box lo hi := fun hin => by
        have := (hin 0).2
        rw [e0] at this
        omega
      rw [boxGaugeTransform, if_neg hb, hz]
      simp [lineHolonomy]
  have row : ∀ X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion, lineHolonomy X p 0 (n₁ + (1 + n₂)) =
      lineHolonomy X p 0 n₁ * (X a 0 * lineHolonomy X (a + unitVec 0) 0 n₂) := by
    intro X
    rw [lineHolonomy_add, pa, lineHolonomy_one_add]
  have hclose := quatDist_le_of_coordBounds S hrow ha hk0 hk0' (n₁ + (1 + n₂)) (by push_cast; omega)
  rw [← hp, row, row] at hclose
  rw [g1, g2]
  have h5 := quatDist_mul_left (lineHolonomy B p 0 n₁)⁻¹
    (lineHolonomy A p 0 n₁ * (A a 0 * lineHolonomy A (a + unitVec 0) 0 n₂))
    (lineHolonomy B p 0 n₁ * (B a 0 * lineHolonomy B (a + unitVec 0) 0 n₂))
  have h6 := quatDist_mul_right (lineHolonomy B (a + unitVec 0) 0 n₂)⁻¹
    ((lineHolonomy B p 0 n₁)⁻¹ * (lineHolonomy A p 0 n₁ * (A a 0 * lineHolonomy A (a + unitVec 0) 0 n₂)))
    ((lineHolonomy B p 0 n₁)⁻¹ * (lineHolonomy B p 0 n₁ * (B a 0 * lineHolonomy B (a + unitVec 0) 0 n₂)))
  have e3 : (lineHolonomy B p 0 n₁)⁻¹ * (lineHolonomy A p 0 n₁ * (A a 0 * lineHolonomy A (a + unitVec 0) 0 n₂)) *
      (lineHolonomy B (a + unitVec 0) 0 n₂)⁻¹ =
      (lineHolonomy B p 0 n₁)⁻¹ * lineHolonomy A p 0 n₁ * A a 0 *
        (lineHolonomy B (a + unitVec 0) 0 n₂ * (lineHolonomy A (a + unitVec 0) 0 n₂)⁻¹)⁻¹ := by
    group
  have e4 : (lineHolonomy B p 0 n₁)⁻¹ * (lineHolonomy B p 0 n₁ * (B a 0 * lineHolonomy B (a + unitVec 0) 0 n₂)) *
      (lineHolonomy B (a + unitVec 0) 0 n₂)⁻¹ = B a 0 := by
    group
  rw [e3, e4] at h6
  linarith
end Fixing
open Fixing in
theorem gaugeFixedNearBox_holds : GaugeFixedNearBox := by
  intro A B lo hi w kl kh M E hbox hE w0a w0b w1a w1b c0h c0l c1h c1l agree hsA hsB a i ha ha' hd hd'
  have S : Hypotheses A B lo hi w kl kh M E :=
    ⟨hbox, hE, w0a, w0b, w1a, w1b, c0h, c0l, c1h, c1l, agree, hsA, hsB⟩
  have hME : (0 : ℝ) ≤ 2 * M * E := by positivity
  have one : ∀ (h : boxGaugeTransform A B lo hi w a = 1) (h' : boxGaugeTransform A B lo hi w (a + unitVec i) = 1)
      (he : A a i = B a i),
      quatDist (boxGaugeTransform A B lo hi w a * A a i * (boxGaugeTransform A B lo hi w (a + unitVec i))⁻¹)
        (B a i) ≤ 2 * M * E := by
    intro h h' he
    rw [h, h', he]
    simp [quatDist_self, hME]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hrow : ∀ l, l ≠ 0 → lo l ≤ a l ∧ a l ≤ hi l
    · rcases lt_trichotomy (a 0) (w 0) with c | c | c
      · rw [along_of_succ_le_cut S a (by omega) ha ha' hd hd', quatDist_self]
        exact hME
      · exact quatDist_across_cut S a c hrow ha ha' hd hd'
      · rw [along_of_cut_lt S a c ha ha' hd hd', quatDist_self]
        exact hME
    · push_neg at hrow
      obtain ⟨l, hl, hout⟩ := hrow
      have el : (a + unitVec 0) l = a l := by simp [unitVec_apply_of_ne hl]
      have b₁ : a ∉ box lo hi := fun hin => by
        have := hin l
        have := hout this.1
        omega
      have b₂ : a + unitVec 0 ∉ box lo hi := fun hin => by
        have h3 := hin l
        rw [el] at h3
        have := hout h3.1
        omega
      exact one (by rw [boxGaugeTransform, if_neg b₁]) (by rw [boxGaugeTransform, if_neg b₂])
        (agree a 0 ha ha' hd hd' b₁ b₂)
  · have e0 : (a + unitVec i) 0 = a 0 := by simp [unitVec_apply_of_ne (Ne.symm hi0)]
    by_cases h0 : lo 0 ≤ a 0 ∧ a 0 ≤ hi 0
    · by_cases hw : w 0 < a 0
      · exact quatDist_transverse_of_cut_lt S a i hi0 hw h0.2 ha ha' hd hd'
      · exact quatDist_transverse_of_le_cut S a i hi0 (not_lt.mp hw) h0.1 ha ha' hd hd'
    · have b₁ : a ∉ box lo hi := fun hin => h0 (hin 0)
      have b₂ : a + unitVec i ∉ box lo hi := fun hin => h0 (by
        have := hin 0
        rwa [e0] at this)
      exact one (by rw [boxGaugeTransform, if_neg b₁]) (by rw [boxGaugeTransform, if_neg b₂])
        (agree a i ha ha' hd hd' b₁ b₂)
end YangMills.Construction.BoxGauge
end
