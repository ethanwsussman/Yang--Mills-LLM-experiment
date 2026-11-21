import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FiniteDifferences
section Group
variable {A W : Type} [AddCommGroup A] [NormedAddCommGroup W]
def FiniteDiffBound (len : A → ℝ) : ℕ → Set A → ℝ → (A → W) → Prop
  | 0, D, B, f => ∀ x ∈ D, ‖f x‖ ≤ B
  | k + 1, D, B, f => (∀ x ∈ D, ‖f x‖ ≤ B) ∧
      ∀ a, FiniteDiffBound len k {x | x ∈ D ∧ x + a ∈ D} (B * len a) (fun x => f (x + a) - f x)
variable {len : A → ℝ}
theorem FiniteDiffBound.norm_le {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len k S C u) : ∀ x ∈ S, ‖u x‖ ≤ C := by
  cases k with
  | zero => exact hu
  | succ k => exact hu.1
theorem FiniteDiffBound.diff {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len (k + 1) S C u) (a : A) :
    FiniteDiffBound len k {x | x ∈ S ∧ x + a ∈ S} (C * len a) (fun x => u (x + a) - u x) := hu.2 a
theorem FiniteDiffBound.of_succ {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len (k + 1) S C u) : FiniteDiffBound len k S C u := by
  induction k generalizing S C u with
  | zero => exact hu.1
  | succ k ih => exact ⟨hu.1, fun a => ih (hu.2 a)⟩
theorem FiniteDiffBound.mono {k : ℕ} {S S' : Set A} {C : ℝ} {u : A → W}
    (hS : S' ⊆ S) (hu : FiniteDiffBound len k S C u) : FiniteDiffBound len k S' C u := by
  induction k generalizing S S' C u with
  | zero => exact fun x hx => hu x (hS hx)
  | succ k ih =>
    refine ⟨fun x hx => hu.1 x (hS hx), fun a => ih ?_ (hu.2 a)⟩
    exact fun x hx => ⟨hS hx.1, hS hx.2⟩
theorem FiniteDiffBound.bound_mono (hl : ∀ a, 0 ≤ len a) {k : ℕ} {S : Set A} {C C' : ℝ} {u : A → W}
    (hC : C ≤ C') (hu : FiniteDiffBound len k S C u) : FiniteDiffBound len k S C' u := by
  induction k generalizing S C C' u with
  | zero => exact fun x hx => (hu x hx).trans hC
  | succ k ih =>
    exact ⟨fun x hx => (hu.1 x hx).trans hC,
      fun a => ih (mul_le_mul_of_nonneg_right hC (hl a)) (hu.2 a)⟩
theorem FiniteDiffBound.congr {k : ℕ} {S : Set A} {C : ℝ} {u v : A → W}
    (huv : ∀ x, u x = v x) (hu : FiniteDiffBound len k S C u) : FiniteDiffBound len k S C v := by
  have : u = v := funext huv
  exact this ▸ hu
theorem FiniteDiffBound.congr_on {k : ℕ} {S : Set A} {C : ℝ} {u v : A → W}
    (huv : ∀ x ∈ S, u x = v x) (hu : FiniteDiffBound len k S C u) :
    FiniteDiffBound len k S C v := by
  induction k generalizing S C u v with
  | zero => exact fun x hx => (huv x hx) ▸ hu x hx
  | succ k ih =>
    refine ⟨fun x hx => (huv x hx) ▸ hu.1 x hx, fun a => ih ?_ (hu.2 a)⟩
    intro x hx
    simp only [huv x hx.1, huv (x + a) hx.2]
theorem FiniteDiffBound.zero {k : ℕ} {S : Set A} {C : ℝ} (hl : ∀ a, 0 ≤ len a) (hC : 0 ≤ C) :
    FiniteDiffBound len k S C (fun _ => (0 : W)) := by
  induction k generalizing S C with
  | zero => exact fun x _ => by simpa using hC
  | succ k ih =>
    refine ⟨fun x _ => by simpa using hC, fun a => ?_⟩
    have := ih (S := {x | x ∈ S ∧ x + a ∈ S}) (C := C * len a) (mul_nonneg hC (hl a))
    simpa using this
theorem FiniteDiffBound.const {k : ℕ} {S : Set A} (hl : ∀ a, 0 ≤ len a) (c : W) :
    FiniteDiffBound len k S ‖c‖ (fun _ => c) := by
  cases k with
  | zero => exact fun _ _ => le_rfl
  | succ k =>
    refine ⟨fun _ _ => le_rfl, fun a => ?_⟩
    have := FiniteDiffBound.zero (W := W) (k := k) (S := {x | x ∈ S ∧ x + a ∈ S}) hl
      (mul_nonneg (norm_nonneg c) (hl a))
    simpa using this
theorem FiniteDiffBound.add {k : ℕ} {S : Set A} {C C' : ℝ} {u v : A → W}
    (hu : FiniteDiffBound len k S C u) (hv : FiniteDiffBound len k S C' v) :
    FiniteDiffBound len k S (C + C') (fun x => u x + v x) := by
  induction k generalizing S C C' u v with
  | zero => exact fun x hx => (norm_add_le _ _).trans (add_le_add (hu x hx) (hv x hx))
  | succ k ih =>
    refine ⟨fun x hx => (norm_add_le _ _).trans (add_le_add (hu.1 x hx) (hv.1 x hx)), fun a => ?_⟩
    have := ih (hu.2 a) (hv.2 a)
    rw [← add_mul] at this
    refine this.congr fun x => ?_
    dsimp only
    abel
theorem FiniteDiffBound.neg {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len k S C u) : FiniteDiffBound len k S C (fun x => - u x) := by
  induction k generalizing S C u with
  | zero => exact fun x hx => by simpa using hu x hx
  | succ k ih =>
    refine ⟨fun x hx => by simpa using hu.1 x hx, fun a => ?_⟩
    refine (ih (hu.2 a)).congr fun x => ?_
    dsimp only
    abel
theorem FiniteDiffBound.sub {k : ℕ} {S : Set A} {C C' : ℝ} {u v : A → W}
    (hu : FiniteDiffBound len k S C u) (hv : FiniteDiffBound len k S C' v) :
    FiniteDiffBound len k S (C + C') (fun x => u x - v x) := by
  refine (hu.add hv.neg).congr fun x => ?_
  abel
theorem FiniteDiffBound.sum {ι : Type} {k : ℕ} {S : Set A} (hl : ∀ a, 0 ≤ len a) (s : Finset ι)
    {C : ι → ℝ} {u : ι → A → W} (hC : ∀ i ∈ s, 0 ≤ C i)
    (hu : ∀ i ∈ s, FiniteDiffBound len k S (C i) (u i)) :
    FiniteDiffBound len k S (∑ i ∈ s, C i) (fun x => ∑ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiniteDiffBound.zero (W := W) (k := k) (S := S) hl le_rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hC j (Finset.mem_insert_of_mem hj))
        fun j hj => hu j (Finset.mem_insert_of_mem hj))
theorem FiniteDiffBound.comp_add_right {k : ℕ} {S : Set A} {C : ℝ} {u : A → W} (a : A)
    (hu : FiniteDiffBound len k S C u) :
    FiniteDiffBound len k {x | x + a ∈ S} C (fun x => u (x + a)) := by
  induction k generalizing S C u with
  | zero => exact fun x hx => hu _ hx
  | succ k ih =>
    refine ⟨fun x hx => hu.1 _ hx, fun b => ?_⟩
    have := ih (hu.2 b)
    refine (this.mono ?_).congr fun x => ?_
    · rintro x ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : x + a + b = x + b + a := by abel
      simpa [this] using h2
    · have : x + a + b = x + b + a := by abel
      simp only [this]
theorem FiniteDiffBound.map {W' : Type} [NormedAddCommGroup W'] {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (T : W →+ W') (hT : ∀ w, ‖T w‖ ≤ ‖w‖) (hu : FiniteDiffBound len k S C u) :
    FiniteDiffBound len k S C (fun x => T (u x)) := by
  induction k generalizing S C u with
  | zero => exact fun x hx => (hT _).trans (hu x hx)
  | succ k ih =>
    refine ⟨fun x hx => (hT _).trans (hu.1 x hx), fun a => ?_⟩
    refine (ih (hu.2 a)).congr fun x => ?_
    simp
theorem FiniteDiffBound.comp {A' : Type} [AddCommGroup A'] {len' : A' → ℝ} (hl : ∀ a, 0 ≤ len a)
    (π : A' →+ A) (hπ : ∀ a, len (π a) ≤ len' a) {k : ℕ} {S : Set A} {C : ℝ} {u : A → W} (hC : 0 ≤ C)
    (hu : FiniteDiffBound len k S C u) :
    FiniteDiffBound len' k (π ⁻¹' S) C (fun x => u (π x)) := by
  induction k generalizing S C u with
  | zero => exact fun x hx => hu _ hx
  | succ k ih =>
    refine ⟨fun x hx => hu.1 _ hx, fun a => ?_⟩
    have h1 := ih (mul_nonneg hC (hl (π a))) (hu.2 (π a))
    have h2 : FiniteDiffBound len' k {x | x ∈ π ⁻¹' S ∧ x + a ∈ π ⁻¹' S} (C * len (π a))
        (fun x => u (π (x + a)) - u (π x)) := by
      refine (h1.mono ?_).congr fun x => ?_
      · rintro x ⟨hx1, hx2⟩
        exact ⟨hx1, by simpa using hx2⟩
      · simp
    exact h2.bound_mono (fun b => (hl _).trans (hπ b)) (mul_le_mul_of_nonneg_left (hπ a) hC)
theorem FiniteDiffBound.of_tendsto {k : ℕ} {S : Set A} {C : ℝ} {u : A → W} {us : ℕ → A → W}
    (hu : ∀ n, FiniteDiffBound len k S C (us n))
    (ht : ∀ x ∈ S, Filter.Tendsto (fun n => us n x) Filter.atTop (nhds (u x))) :
    FiniteDiffBound len k S C u := by
  induction k generalizing S C u us with
  | zero =>
    exact fun x hx => le_of_tendsto (ht x hx).norm (Filter.Eventually.of_forall fun n => hu n x hx)
  | succ k ih =>
    refine ⟨fun x hx => le_of_tendsto (ht x hx).norm (Filter.Eventually.of_forall fun n => (hu n).1 x hx),
      fun a => ih (us := fun n x => us n (x + a) - us n x) (fun n => (hu n).2 a) fun x hx => ?_⟩
    exact (ht _ hx.2).sub (ht _ hx.1)
theorem FiniteDiffBound.norm_sub_le {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len (k + 1) S C u) {x a : A} (h0 : x ∈ S) (h1 : x + a ∈ S) :
    ‖u (x + a) - u x‖ ≤ C * len a := (hu.diff a).norm_le x ⟨h0, h1⟩
theorem FiniteDiffBound.norm_second_diff_le {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len (k + 2) S C u) {x a b : A} (h0 : x ∈ S) (h1 : x + a ∈ S)
    (h2 : x + b ∈ S) (h3 : x + b + a ∈ S) :
    ‖(u (x + b + a) - u (x + b)) - (u (x + a) - u x)‖ ≤ C * len a * len b :=
  (hu.diff a).norm_sub_le ⟨h0, h1⟩ ⟨h2, h3⟩
theorem FiniteDiffBound.norm_third_diff_le {k : ℕ} {S : Set A} {C : ℝ} {u : A → W}
    (hu : FiniteDiffBound len (k + 3) S C u) {x a b c : A} (h0 : x ∈ S) (h1 : x + a ∈ S)
    (h2 : x + b ∈ S) (h3 : x + b + a ∈ S) (h4 : x + c ∈ S) (h5 : x + c + a ∈ S)
    (h6 : x + c + b ∈ S) (h7 : x + c + b + a ∈ S) :
    ‖((u (x + c + b + a) - u (x + c + b)) - (u (x + c + a) - u (x + c))) -
      ((u (x + b + a) - u (x + b)) - (u (x + a) - u x))‖ ≤ C * len a * len b * len c :=
  (hu.diff a).norm_second_diff_le ⟨h0, h1⟩ ⟨h2, h3⟩ ⟨h4, h5⟩ ⟨h6, h7⟩
end Group
section Ring
variable {A R : Type} [AddCommGroup A] [NormedRing R] {len : A → ℝ}
theorem FiniteDiffBound.mul (hl : ∀ a, 0 ≤ len a) {k : ℕ} {S : Set A} {C C' : ℝ} {u v : A → R}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hu : FiniteDiffBound len k S C u)
    (hv : FiniteDiffBound len k S C' v) :
    FiniteDiffBound len k S (2 ^ k * C * C') (fun x => u x * v x) := by
  induction k generalizing S C C' u v with
  | zero =>
    intro x hx
    have := norm_mul_le (u x) (v x)
    have h2 := mul_le_mul (hu x hx) (hv x hx) (norm_nonneg _) hC
    simpa using this.trans h2
  | succ k ih =>
    have hs : ∀ x ∈ S, ‖u x * v x‖ ≤ 2 ^ (k + 1) * C * C' := by
      intro x hx
      have h1 := norm_mul_le (u x) (v x)
      have h2 := mul_le_mul (hu.1 x hx) (hv.1 x hx) (norm_nonneg _) hC
      have h3 : C * C' ≤ 2 ^ (k + 1) * C * C' := by
        have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg hC hC']
      linarith
    refine ⟨hs, fun a => ?_⟩
    have t1 := ih (mul_nonneg hC (hl a)) hC' (hu.2 a)
      ((hv.of_succ.comp_add_right a).mono (fun x hx => hx.2))
    have t2 := ih hC (mul_nonneg hC' (hl a)) (hu.of_succ.mono (fun x hx => hx.1)) (hv.2 a)
    have t3 := t1.add t2
    have e : 2 ^ k * (C * len a) * C' + 2 ^ k * C * (C' * len a) = 2 ^ (k + 1) * C * C' * len a := by
      ring
    rw [e] at t3
    refine t3.congr fun x => ?_
    simp only [sub_mul, mul_sub]
    abel
end Ring
section Division
variable {A R : Type} [AddCommGroup A] [NormedDivisionRing R] {len : A → ℝ}
def invDiffBound (C r : ℝ) : ℕ → ℝ
  | 0 => r
  | k + 1 => max r (4 ^ k * invDiffBound C r k ^ 2 * C)
theorem invDiffBound_nonneg (C r : ℝ) (hr : 0 ≤ r) (k : ℕ) : 0 ≤ invDiffBound C r k := by
  cases k with
  | zero => exact hr
  | succ k => exact hr.trans (le_max_left _ _)
theorem FiniteDiffBound.inv (hl : ∀ a, 0 ≤ len a) {k : ℕ} {S : Set A} {C r : ℝ} {u : A → R}
    (hC : 0 ≤ C) (hr : 0 < r) (hu : FiniteDiffBound len k S C u)
    (hlow : ∀ x ∈ S, r⁻¹ ≤ ‖u x‖) :
    FiniteDiffBound len k S (invDiffBound C r k) (fun x => (u x)⁻¹) := by
  have hsup : ∀ x ∈ S, ‖(u x)⁻¹‖ ≤ r := by
    intro x hx
    rw [norm_inv]
    have h1 : 0 < r⁻¹ := inv_pos.2 hr
    have := inv_anti₀ h1 (hlow x hx)
    simpa using this
  induction k generalizing S u with
  | zero => exact hsup
  | succ k ih =>
    refine ⟨fun x hx => (hsup x hx).trans (le_max_left _ _), fun a => ?_⟩
    have hCk := invDiffBound_nonneg C r hr.le k
    have g0 := ih hu.of_succ hlow hsup
    have gl := g0.mono (S' := {x | x ∈ S ∧ x + a ∈ S}) (fun x hx => hx.1)
    have gr := (g0.comp_add_right a).mono (S' := {x | x ∈ S ∧ x + a ∈ S}) (fun x hx => hx.2)
    have m1 := FiniteDiffBound.mul hl hCk (mul_nonneg hC (hl a)) gl (hu.2 a)
    have m2 := FiniteDiffBound.mul hl
      (mul_nonneg (mul_nonneg (by positivity) hCk) (mul_nonneg hC (hl a))) hCk m1 gr
    have m3 := m2.neg
    have e : 2 ^ k * (2 ^ k * invDiffBound C r k * (C * len a)) * invDiffBound C r k =
        (4 ^ k * invDiffBound C r k ^ 2 * C) * len a := by
      have : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      rw [this]; ring
    rw [e] at m3
    have m4 := m3.bound_mono hl (mul_le_mul_of_nonneg_right (le_max_right r _) (hl a))
    refine m4.congr_on fun x hx => ?_
    have n0 : u x ≠ 0 := by
      have := hlow x hx.1
      intro h0
      rw [h0, norm_zero] at this
      exact absurd this (not_le.2 (inv_pos.2 hr))
    have n1 : u (x + a) ≠ 0 := by
      have := hlow _ hx.2
      intro h0
      rw [h0, norm_zero] at this
      exact absurd this (not_le.2 (inv_pos.2 hr))
    have := inv_sub_inv' n0 n1
    show -((u x)⁻¹ * (u (x + a) - u x) * (u (x + a))⁻¹) = (u (x + a))⁻¹ - (u x)⁻¹
    rw [← this]
    abel
end Division
section Line
def DerivBound : ℕ → ℝ → (ℝ → ℝ) → Prop
  | 0, M, g => ∀ t, |g t| ≤ M
  | k + 1, M, g => (∀ t, |g t| ≤ M) ∧ Differentiable ℝ g ∧ DerivBound k M (deriv g)
theorem DerivBound.abs_le {k : ℕ} {M : ℝ} {g : ℝ → ℝ} (hg : DerivBound k M g) :
    ∀ t, |g t| ≤ M := by
  cases k with
  | zero => exact hg
  | succ k => exact hg.1
theorem DerivBound.sub_shift {k : ℕ} {M : ℝ} {g : ℝ → ℝ} (hg : DerivBound (k + 1) M g) (t : ℝ) :
    DerivBound k (M * |t|) (fun u => g (u + t) - g u) := by
  induction k generalizing g with
  | zero =>
    intro u
    have hd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv g x‖ ≤ M := fun x _ => by simpa using hg.2.2 x
    have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hg.2.1 x) hd convex_univ
      (Set.mem_univ u) (Set.mem_univ (u + t))
    simpa using this
  | succ k ih =>
    have h0 : ∀ u, |g (u + t) - g u| ≤ M * |t| := by
      intro u
      have hd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv g x‖ ≤ M := fun x _ => by
        simpa using hg.2.2.abs_le x
      have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hg.2.1 x) hd convex_univ
        (Set.mem_univ u) (Set.mem_univ (u + t))
      simpa using this
    have hdiff : Differentiable ℝ (fun u => g (u + t) - g u) :=
      (hg.2.1.comp (differentiable_id.add_const t)).sub hg.2.1
    have hder : deriv (fun u => g (u + t) - g u) = fun u => deriv g (u + t) - deriv g u := by
      funext u
      have h1 : HasDerivAt (fun u => g (u + t)) (deriv g (u + t)) u := by
        simpa using ((hg.2.1 (u + t)).hasDerivAt).comp_add_const u t
      exact (h1.sub (hg.2.1 u).hasDerivAt).deriv
    refine ⟨h0, hdiff, ?_⟩
    rw [hder]
    exact ih hg.2.2
theorem DerivBound.finiteDiffBound {A : Type} [AddCommGroup A] {len : A → ℝ}
    (hl : ∀ a, 0 ≤ len a) (l : A →+ ℝ) (hlen : ∀ a, |l a| ≤ len a) (c : ℝ) {k : ℕ} {M : ℝ} {g : ℝ → ℝ}
    {S : Set A} (hg : DerivBound k M g) :
    FiniteDiffBound len k S M (fun x => g (l x + c)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg.abs_le 0)
  induction k generalizing S M g with
  | zero => exact fun x _ => by simpa using hg (l x + c)
  | succ k ih =>
    refine ⟨fun x _ => by simpa using hg.1 (l x + c), fun a => ?_⟩
    have h1 := hg.sub_shift (l a)
    have h2 := ih (S := {x | x ∈ S ∧ x + a ∈ S}) h1 (mul_nonneg hM (abs_nonneg _))
    have h3 := h2.bound_mono hl (mul_le_mul_of_nonneg_left (hlen a) hM)
    refine h3.congr fun x => ?_
    simp only [map_add]
    ring_nf
end Line
end FiniteDifferences
end YangMills.Construction
end
