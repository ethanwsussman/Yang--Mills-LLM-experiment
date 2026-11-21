import YangMills.Construction.ResponseInTheExpansion.TracesOfChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.MatrixTraces
open Finset
section Products
variable {I : Type} [Fintype I] [DecidableEq I]
private def prodUpTo (F : ℕ → Matrix I I ℝ) (r : ℕ) : Matrix I I ℝ := ((List.range r).map F).prod
private theorem prodUpTo_zero (F : ℕ → Matrix I I ℝ) : prodUpTo F 0 = 1 := by simp [prodUpTo]
private theorem prodUpTo_succ (F : ℕ → Matrix I I ℝ) (r : ℕ) : prodUpTo F (r + 1) = prodUpTo F r * F r := by
  simp [prodUpTo, List.range_succ, List.prod_append]
private theorem prodUpTo_congr {F G : ℕ → Matrix I I ℝ} (r : ℕ) (h : ∀ l < r, F l = G l) :
    prodUpTo F r = prodUpTo G r := by
  induction r with
  | zero => simp [prodUpTo_zero]
  | succ r ih =>
    rw [prodUpTo_succ, prodUpTo_succ, ih fun l hl => h l (by omega), h r (by omega)]
private theorem list_ofFn_prod_eq_prodUpTo {q : ℕ} (f : Fin (q + 1) → Matrix I I ℝ) :
    (List.ofFn f).prod = prodUpTo (fun l => f (Fin.ofNat (q + 1) l)) (q + 1) := by
  unfold prodUpTo
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < q + 1 := by simpa using h₁
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    congr 1
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi]
private theorem prodUpTo_apply_eq_zero_of_row (K X : ℕ → Matrix I I ℝ) (a : I) (h : ∀ b, K 0 a b = 0) (r : ℕ)
    (b : I) : prodUpTo (fun l => K l * X l) (r + 1) a b = 0 := by
  induction r generalizing b with
  | zero =>
    rw [prodUpTo_succ, prodUpTo_zero, one_mul]
    simp [Matrix.mul_apply, h]
  | succ r ih =>
    rw [prodUpTo_succ, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [ih c, zero_mul]
private theorem abs_prodUpTo_apply_le (K X : ℕ → Matrix I I ℝ) (Sm : ℕ → I → Prop) (w : ℕ → I → ℝ)
    (c W : ℕ → ℝ)
    (hw : ∀ l a, 0 ≤ w l a) (hc : ∀ l, 0 ≤ c l) (hW0 : ∀ l, 0 ≤ W l)
    (hK : ∀ l a b, K l a b ≠ 0 → Sm l a ∧ Sm l b)
    (hX : ∀ l a b, Sm l a → Sm (l + 1) b → |X l a b| ≤ c l * w l a * w (l + 1) b)
    (hW : ∀ l, ∑ a, ∑ b, |K l a b| * w l a * w l b ≤ W l) (r : ℕ) :
    ∀ a b, Sm (r + 1) b → |prodUpTo (fun l => K l * X l) (r + 1) a b| ≤
      (∏ l ∈ range (r + 1), c l) * (∏ l ∈ range r, W (l + 1)) * (∑ d, |K 0 a d| * w 0 d) * w (r + 1) b := by
  induction r with
  | zero =>
    intro a b hb
    rw [prodUpTo_succ, prodUpTo_zero, one_mul]
    simp only [range_one, prod_singleton, range_zero, prod_empty, mul_one, zero_add]
    rw [Matrix.mul_apply]
    calc |∑ d, K 0 a d * X 0 d b| ≤ ∑ d, |K 0 a d * X 0 d b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, c 0 * (|K 0 a d| * w 0 d) * w 1 b := by
        refine Finset.sum_le_sum fun d _ => ?_
        by_cases hk : K 0 a d = 0
        · simp [hk]
        · have := hX 0 d b (hK 0 a d hk).2 hb
          rw [abs_mul]
          calc |K 0 a d| * |X 0 d b| ≤ |K 0 a d| * (c 0 * w 0 d * w (0 + 1) b) :=
                mul_le_mul_of_nonneg_left this (abs_nonneg _)
            _ = _ := by ring_nf
      _ = c 0 * (∑ d, |K 0 a d| * w 0 d) * w 1 b := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  | succ r ih =>
    intro a b hb
    rw [prodUpTo_succ, Matrix.mul_apply]
    set Pc := ∏ l ∈ range (r + 1), c l with hPc
    set Pw := ∏ l ∈ range r, W (l + 1) with hPw
    set R := ∑ d, |K 0 a d| * w 0 d with hR
    have hPc0 : 0 ≤ Pc := Finset.prod_nonneg fun l _ => hc l
    have hPw0 : 0 ≤ Pw := Finset.prod_nonneg fun l _ => hW0 _
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (hw _ _)
    have hwb := hw (r + 1 + 1) b
    have hcr := hc (r + 1)
    calc |∑ x, prodUpTo (fun l => K l * X l) (r + 1) a x * (K (r + 1) * X (r + 1)) x b|
        ≤ ∑ x, |prodUpTo (fun l => K l * X l) (r + 1) a x * (K (r + 1) * X (r + 1)) x b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, ∑ y, (Pc * Pw * R * c (r + 1) * w (r + 1 + 1) b) *
            (|K (r + 1) x y| * w (r + 1) x * w (r + 1) y) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Matrix.mul_apply, Finset.mul_sum]
        calc _ ≤ ∑ y, |prodUpTo (fun l => K l * X l) (r + 1) a x * (K (r + 1) x y * X (r + 1) y b)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            refine Finset.sum_le_sum fun y _ => ?_
            by_cases hk : K (r + 1) x y = 0
            · simp [hk]
            · obtain ⟨hx, hy⟩ := hK _ x y hk
              have h1 := ih a x hx
              have h2 := hX (r + 1) y b hy hb
              rw [abs_mul, abs_mul]
              calc _ ≤ (Pc * Pw * R * w (r + 1) x) *
                    (|K (r + 1) x y| * (c (r + 1) * w (r + 1) y * w (r + 1 + 1) b)) := by
                    refine mul_le_mul h1 ?_ (by positivity) (by have := hw (r + 1) x; positivity)
                    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
                _ = _ := by ring
      _ = (Pc * Pw * R * c (r + 1) * w (r + 1 + 1) b) *
          ∑ x, ∑ y, |K (r + 1) x y| * w (r + 1) x * w (r + 1) y := by
        simp only [Finset.mul_sum]
      _ ≤ (Pc * Pw * R * c (r + 1) * w (r + 1 + 1) b) * W (r + 1) :=
        mul_le_mul_of_nonneg_left (hW _) (by positivity)
      _ = _ := by
        rw [Finset.prod_range_succ c (r + 1), Finset.prod_range_succ (fun l => W (l + 1)) r, ← hPc, ← hPw]
        ring
private theorem abs_trace_prodUpTo_le (K X : ℕ → Matrix I I ℝ) (Sm : ℕ → I → Prop) (w : ℕ → I → ℝ)
    (c W : ℕ → ℝ)
    (hw : ∀ l a, 0 ≤ w l a) (hc : ∀ l, 0 ≤ c l) (hW0 : ∀ l, 0 ≤ W l)
    (hK : ∀ l a b, K l a b ≠ 0 → Sm l a ∧ Sm l b)
    (hX : ∀ l a b, Sm l a → Sm (l + 1) b → |X l a b| ≤ c l * w l a * w (l + 1) b)
    (hW : ∀ l, ∑ a, ∑ b, |K l a b| * w l a * w l b ≤ W l) (q : ℕ)
    (hSm : ∀ a, Sm (q + 1) a ↔ Sm 0 a) (hwq : ∀ a, w (q + 1) a = w 0 a) :
    |Matrix.trace (prodUpTo (fun l => K l * X l) (q + 1))| ≤
      (∏ l ∈ range (q + 1), c l) * ∏ l ∈ range (q + 1), W l := by
  set Pc := ∏ l ∈ range (q + 1), c l with hPc
  set Pw := ∏ l ∈ range q, W (l + 1) with hPw
  have hPc0 : 0 ≤ Pc := Finset.prod_nonneg fun l _ => hc l
  have hPw0 : 0 ≤ Pw := Finset.prod_nonneg fun l _ => hW0 _
  have hentry : ∀ a, |prodUpTo (fun l => K l * X l) (q + 1) a a| ≤
      Pc * Pw * ∑ b, |K 0 a b| * w 0 a * w 0 b := by
    intro a
    have hrow : 0 ≤ ∑ d, |K 0 a d| * w 0 d :=
      Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (hw _ _)
    have heq : ∑ b, |K 0 a b| * w 0 a * w 0 b = (∑ d, |K 0 a d| * w 0 d) * w 0 a := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [heq]
    by_cases ha : Sm 0 a
    · have := abs_prodUpTo_apply_le K X Sm w c W hw hc hW0 hK hX hW q a a ((hSm a).2 ha)
      rw [hwq] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    · have hz : ∀ b, K 0 a b = 0 := fun b => by
        by_contra hk
        exact ha (hK 0 a b hk).1
      rw [prodUpTo_apply_eq_zero_of_row K X a hz q a, abs_zero]
      have := hw 0 a
      positivity
  calc |Matrix.trace (prodUpTo (fun l => K l * X l) (q + 1))| ≤
        ∑ a, |prodUpTo (fun l => K l * X l) (q + 1) a a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, Pc * Pw * ∑ b, |K 0 a b| * w 0 a * w 0 b := Finset.sum_le_sum fun a _ => hentry a
    _ = Pc * Pw * ∑ a, ∑ b, |K 0 a b| * w 0 a * w 0 b := by rw [Finset.mul_sum]
    _ ≤ Pc * Pw * W 0 := mul_le_mul_of_nonneg_left (hW 0) (by positivity)
    _ = _ := by
      rw [Finset.prod_range_succ' W q]
      ring
private theorem prodUpTo_sub_prodUpTo (F G : ℕ → Matrix I I ℝ) (r : ℕ) :
    prodUpTo F r - prodUpTo G r =
      ∑ j ∈ range r, prodUpTo (fun l => if l < j then F l else if l = j then F j - G j else G l) r := by
  induction r with
  | zero => simp [prodUpTo_zero]
  | succ r ih =>
    have h1 : prodUpTo F (r + 1) - prodUpTo G (r + 1) =
        (prodUpTo F r - prodUpTo G r) * G r + prodUpTo F r * (F r - G r) := by
      rw [prodUpTo_succ, prodUpTo_succ]
      noncomm_ring
    rw [h1, ih, Finset.sum_range_succ, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < r := Finset.mem_range.mp hj
      rw [prodUpTo_succ (fun l => if l < j then F l else if l = j then F j - G j else G l) r]
      congr 1
      simp [show ¬ r < j by omega, show r ≠ j by omega]
    · rw [prodUpTo_succ (fun l => if l < r then F l else if l = r then F r - G r else G l) r]
      congr 1
      · exact (prodUpTo_congr r fun l hl => by simp [hl]).symm
      · simp
end Products
section Swap
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
private theorem prodUpTo_mul_comm_aux (U : Matrix m n ℝ) (C : ℕ → Matrix n m ℝ) (r : ℕ) :
    prodUpTo (fun l => U * C l) r * U = U * prodUpTo (fun l => C l * U) r := by
  induction r with
  | zero => simp [prodUpTo_zero]
  | succ r ih =>
    rw [prodUpTo_succ, prodUpTo_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (prodUpTo _ r) U, ih]
    simp only [Matrix.mul_assoc]
private theorem trace_prodUpTo_swap (U : Matrix m n ℝ) (C : ℕ → Matrix n m ℝ) (r : ℕ) :
    Matrix.trace (prodUpTo (fun l => U * C l) (r + 1)) = Matrix.trace (prodUpTo (fun l => C l * U) (r + 1)) := by
  rw [prodUpTo_succ, prodUpTo_succ, ← Matrix.mul_assoc, prodUpTo_mul_comm_aux, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc]
end Swap
section Paths
variable {n : Type} [Fintype n] [DecidableEq n]
private def pathVertex (a b : n) {r : ℕ} (v : Fin r → n) : ℕ → n
  | 0 => a
  | l + 1 => if h : l < r then v ⟨l, h⟩ else b
private theorem pathVertex_snoc (a b c : n) {r : ℕ} (u : Fin r → n) (l : ℕ) (hl : l ≤ r + 1) :
    pathVertex a b (Fin.snoc (α := fun _ => n) u c) l = pathVertex a c u l := by
  cases l with
  | zero => rfl
  | succ l =>
    simp only [pathVertex]
    by_cases h : l < r
    · rw [dif_pos (by omega : l < r + 1), dif_pos h]
      simp [Fin.snoc, h]
    · have hlr : l = r := by omega
      subst hlr
      rw [dif_pos (by omega : l < l + 1), dif_neg h]
      simp [Fin.snoc]
private theorem prodUpTo_apply_eq_sum_paths (M : ℕ → Matrix n n ℝ) (r : ℕ) (a b : n) :
    prodUpTo M (r + 1) a b =
      ∑ v : Fin r → n, ∏ l ∈ range (r + 1), M l (pathVertex a b v l) (pathVertex a b v (l + 1)) := by
  induction r generalizing b with
  | zero =>
    rw [prodUpTo_succ, prodUpTo_zero, one_mul]
    simp [pathVertex]
  | succ r ih =>
    rw [prodUpTo_succ, Matrix.mul_apply, ← (Fin.snocEquiv (fun _ : Fin (r + 1) => n)).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.prod_range_succ _ (r + 1)]
    have hsn : ∀ l, l ≤ r + 1 →
        pathVertex a b ((Fin.snocEquiv (fun _ : Fin (r + 1) => n)) (c, u)) l = pathVertex a c u l :=
      fun l hl => pathVertex_snoc a b c u l hl
    congr 1
    · refine Finset.prod_congr rfl fun l hl => ?_
      have := Finset.mem_range.mp hl
      rw [hsn l (by omega), hsn (l + 1) (by omega)]
    · rw [hsn (r + 1) le_rfl]
      have h2 : pathVertex a b ((Fin.snocEquiv (fun _ : Fin (r + 1) => n)) (c, u)) (r + 1 + 1) = b := by
        simp [pathVertex]
      have h3 : pathVertex a c u (r + 1) = c := by simp [pathVertex]
      rw [h2, h3]
private theorem trace_prodUpTo_eq_sum_cycles (M : ℕ → Matrix n n ℝ) (q : ℕ) :
    Matrix.trace (prodUpTo M (q + 1)) = ∑ v : Fin (q + 1) → n,
      ∏ l ∈ range (q + 1), M l (v (Fin.ofNat (q + 1) l)) (v (Fin.ofNat (q + 1) (l + 1))) := by
  rw [← (Fin.consEquiv (fun _ : Fin (q + 1) => n)).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [prodUpTo_apply_eq_sum_paths]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hv : ∀ l, l ≤ q + 1 →
      (Fin.consEquiv (fun _ : Fin (q + 1) => n)) (a, u) (Fin.ofNat (q + 1) l) = pathVertex a a u l := by
    intro l hl
    show (Fin.cons a u : Fin (q + 1) → n) (Fin.ofNat (q + 1) l) = pathVertex a a u l
    cases l with
    | zero => simp [pathVertex]
    | succ l =>
      simp only [pathVertex]
      by_cases h : l < q
      · rw [dif_pos h]
        have : Fin.ofNat (q + 1) (l + 1) = Fin.succ ⟨l, h⟩ := by
          ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt (show l + 1 < q + 1 by omega)]
        rw [this, Fin.cons_succ]
      · have hlq : l = q := by omega
        subst hlq
        rw [dif_neg h]
        have : Fin.ofNat (l + 1) (l + 1) = 0 := by
          ext
          simp [Fin.ofNat]
        rw [this, Fin.cons_zero]
  refine Finset.prod_congr rfl fun l hl => ?_
  have := Finset.mem_range.mp hl
  rw [hv l (by omega), hv (l + 1) (by omega)]
end Paths
section Blocks
variable {S X Q : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
private def blockDiag {Y : Type} (A : Finset S) (f : S → Y → Y → ℝ) : Matrix (S × Y) (S × Y) ℝ :=
  fun y y' => if y.1 = y'.1 ∧ y.1 ∈ A then f y.1 y.2 y'.2 else 0
private theorem blockDiag_sub {Y : Type} (A : Finset S) (f f' : S → Y → Y → ℝ) :
    blockDiag A f - blockDiag A f' = blockDiag A fun z a b => f z a b - f' z a b := by
  refine Matrix.ext fun y y' => ?_
  by_cases h : y.1 = y'.1 ∧ y.1 ∈ A
  · simp only [blockDiag, Matrix.sub_apply, if_pos h]
  · simp only [blockDiag, Matrix.sub_apply, if_neg h, sub_zero]
private theorem blockDiag_weighted_mass_le {Y : Type} [Fintype Y] (A : Finset S) (f : S → Y → Y → ℝ)
    (φ : S → Y → ℝ) (Bd Am : ℝ)
    (hBd : 0 ≤ Bd) (hA : (A.card : ℝ) ≤ Am) (h : ∀ z ∈ A, ∑ a, ∑ b, |f z a b| * φ z a * φ z b ≤ Bd) :
    ∑ y, ∑ y', |blockDiag A f y y'| * φ y.1 y.2 * φ y'.1 y'.2 ≤ Am * Bd := by
  have h1 : ∀ z a, ∑ y', |blockDiag A f (z, a) y'| * φ z a * φ y'.1 y'.2 =
      if z ∈ A then ∑ b, |f z a b| * φ z a * φ z b else 0 := by
    intro z a
    rw [Fintype.sum_prod_type, Finset.sum_eq_single z]
    · by_cases hz : z ∈ A <;> simp [blockDiag, hz]
    · intro z' _ hne
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [blockDiag, hne.symm]
    · simp
  rw [Fintype.sum_prod_type]
  calc ∑ z, ∑ a, ∑ y', |blockDiag A f (z, a) y'| * φ (z, a).1 (z, a).2 * φ y'.1 y'.2
      = ∑ z, if z ∈ A then ∑ a, ∑ b, |f z a b| * φ z a * φ z b else 0 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [h1]
        by_cases hz : z ∈ A <;> simp [hz]
    _ = ∑ z ∈ A, ∑ a, ∑ b, |f z a b| * φ z a * φ z b := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ ∑ _z ∈ A, Bd := Finset.sum_le_sum h
    _ = (A.card : ℝ) * Bd := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Am * Bd := mul_le_mul_of_nonneg_right hA hBd
private def planeSum (Pl : X → Q) (k : Matrix X X ℝ) (Q₁ Q₂ : Q) : ℝ :=
  ∑ a, ∑ b, if Pl a = Q₁ ∧ Pl b = Q₂ then k a b else 0
private theorem planeSum_abs_mass_le (Pl : X → Q) (k : Matrix X X ℝ) :
    ∑ Q₁, ∑ Q₂, |planeSum Pl k Q₁ Q₂| ≤ ∑ a, ∑ b, |k a b| := by
  let F : Q → Q → X → X → ℝ := fun Q₁ Q₂ a b => if Pl a = Q₁ ∧ Pl b = Q₂ then |k a b| else 0
  calc ∑ Q₁, ∑ Q₂, |planeSum Pl k Q₁ Q₂| ≤ ∑ Q₁, ∑ Q₂, ∑ a, ∑ b, F Q₁ Q₂ a b := by
        refine Finset.sum_le_sum fun Q₁ _ => Finset.sum_le_sum fun Q₂ _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        by_cases h : Pl a = Q₁ ∧ Pl b = Q₂ <;> simp [F, h]
    _ = ∑ Q₁, ∑ a, ∑ Q₂, ∑ b, F Q₁ Q₂ a b := Finset.sum_congr rfl fun Q₁ _ => Finset.sum_comm
    _ = ∑ a, ∑ Q₁, ∑ Q₂, ∑ b, F Q₁ Q₂ a b := Finset.sum_comm
    _ = ∑ a, ∑ Q₁, ∑ b, ∑ Q₂, F Q₁ Q₂ a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun Q₁ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ Q₁, ∑ Q₂, F Q₁ Q₂ a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, |k a b| := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single (Pl a), Finset.sum_eq_single (Pl b)]
        · simp [F]
        · intro Q₂ _ hne
          simp [F, hne.symm]
        · simp
        · intro Q₁ _ hne
          refine Finset.sum_eq_zero fun Q₂ _ => ?_
          simp [F, hne.symm]
        · simp
private def siteLift : Matrix X (S × X) ℝ := fun a y => if a = y.2 then 1 else 0
private def planeProj (Pl : X → Q) : Matrix (S × X) (S × Q) ℝ :=
  fun y u => if y.1 = u.1 ∧ Pl y.2 = u.2 then 1 else 0
private def planeCouplings (Cc : S → S → Matrix Q Q ℝ) : Matrix (S × Q) (S × Q) ℝ :=
  fun u u' => Cc u.1 u'.1 u.2 u'.2
private theorem blockDiag_support {Y : Type} {A : Finset S} {f : S → Y → Y → ℝ} {y y' : S × Y}
    (h : blockDiag A f y y' ≠ 0) : y.1 ∈ A ∧ y'.1 ∈ A := by
  by_contra hn
  apply h
  have : ¬ (y.1 = y'.1 ∧ y.1 ∈ A) := by
    rintro ⟨h1, h2⟩
    exact hn ⟨h2, h1 ▸ h2⟩
  simp only [blockDiag, if_neg this]
private theorem siteLift_mul_blockDiag (A : Finset S) (K : S → Matrix X X ℝ) :
    (siteLift : Matrix X (S × X) ℝ) * blockDiag A K * (siteLift : Matrix X (S × X) ℝ).transpose =
      ∑ z ∈ A, K z := by
  refine Matrix.ext fun a b => ?_
  have h1 : ∀ y', ((siteLift : Matrix X (S × X) ℝ) * blockDiag A K) a y' = ∑ z, blockDiag A K (z, a) y' := by
    intro y'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [siteLift]
  rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [h1, Matrix.transpose_apply, siteLift]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  have h2 : ∀ z, ∑ z', blockDiag A K (z, a) (z', b) = if z ∈ A then K z a b else 0 := by
    intro z
    rw [Finset.sum_eq_single z]
    · by_cases hz : z ∈ A <;> simp [blockDiag, hz]
    · intro z' _ hne
      simp [blockDiag, hne.symm]
    · simp
  simp only [h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
private theorem siteLift_conj_apply (T : Matrix X X ℝ) (y y' : S × X) :
    ((siteLift : Matrix X (S × X) ℝ).transpose * T * (siteLift : Matrix X (S × X) ℝ)) y y' = T y.2 y'.2 := by
  have h1 : ∀ b, ((siteLift : Matrix X (S × X) ℝ).transpose * T) y b = T y.2 b := by
    intro b
    simp [Matrix.mul_apply, siteLift, Matrix.transpose_apply]
  rw [Matrix.mul_apply]
  simp [h1, siteLift]
private theorem planeProj_conj_apply (Pl : X → Q) (Cc : S → S → Matrix Q Q ℝ) (y y' : S × X) :
    ((planeProj (S := S) Pl) * planeCouplings Cc * (planeProj (S := S) Pl).transpose) y y' =
      Cc y.1 y'.1 (Pl y.2) (Pl y'.2) := by
  have h1 : ∀ u, ((planeProj (S := S) Pl) * planeCouplings Cc) y u = planeCouplings Cc (y.1, Pl y.2) u := by
    intro u
    rw [Matrix.mul_apply, Finset.sum_eq_single (y.1, Pl y.2)]
    · simp [planeProj]
    · rintro ⟨z, Q₁⟩ _ hne
      have : ¬ (y.1 = z ∧ Pl y.2 = Q₁) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp only [planeProj, if_neg this, zero_mul]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (y'.1, Pl y'.2)]
  · simp [h1, planeProj, planeCouplings]
  · rintro ⟨z, Q₁⟩ _ hne
    have : ¬ (y'.1 = z ∧ Pl y'.2 = Q₁) := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    simp only [Matrix.transpose_apply, planeProj, if_neg this, mul_zero]
  · simp
private theorem planeProj_conj_blockDiag (Pl : X → Q) (A : Finset S) (K : S → Matrix X X ℝ) :
    (planeProj (S := S) Pl).transpose * blockDiag A K * (planeProj (S := S) Pl) =
      blockDiag A fun z => planeSum Pl (K z) := by
  refine Matrix.ext fun u u' => ?_
  have h1 : ∀ y', ((planeProj (S := S) Pl).transpose * blockDiag A K) u y' =
      ∑ a, if Pl a = u.2 then blockDiag A K (u.1, a) y' else 0 := by
    intro y'
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single u.1]
    · refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : Pl a = u.2 <;> simp [planeProj, ha]
    · intro z _ hne
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [planeProj, hne.symm, hne]
    · simp
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single u'.1]
  · simp only [h1]
    by_cases hc : u.1 = u'.1 ∧ u.1 ∈ A
    · simp only [blockDiag, if_pos hc, planeSum]
      rw [Finset.sum_congr rfl fun b _ => Finset.sum_mul _ _ _, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases ha : Pl a = u.2 <;> by_cases hb : Pl b = u'.2 <;> simp [ha, hb, planeProj, hc.1, hc.2]
    · have h0 : blockDiag A (fun z => planeSum Pl (K z)) u u' = 0 := by simp only [blockDiag, if_neg hc]
      rw [h0]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : ∀ a, blockDiag A K (u.1, a) (u'.1, b) = 0 := fun a => by simp only [blockDiag, if_neg hc]
      simp [this]
  · intro z _ hne
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [planeProj, hne]
  · simp
end Blocks
section Telescopes
variable {I : Type} [Fintype I] [DecidableEq I]
private theorem prodUpTo_sub_right (K X Y : ℕ → Matrix I I ℝ) (r : ℕ) :
    prodUpTo (fun l => K l * X l) r - prodUpTo (fun l => K l * Y l) r =
      ∑ j ∈ range r, prodUpTo (fun l => K l * (if l < j then X l else if l = j then X j - Y j else Y l)) r := by
  rw [prodUpTo_sub_prodUpTo]
  refine Finset.sum_congr rfl fun j _ => prodUpTo_congr r fun l _ => ?_
  by_cases h1 : l < j
  · simp [h1]
  · by_cases h2 : l = j
    · subst h2
      simp [Matrix.mul_sub]
    · simp [h1, h2]
private theorem prodUpTo_sub_left (K K' X : ℕ → Matrix I I ℝ) (r : ℕ) :
    prodUpTo (fun l => K l * X l) r - prodUpTo (fun l => K' l * X l) r =
      ∑ j ∈ range r, prodUpTo (fun l => (if l < j then K l else if l = j then K j - K' j else K' l) * X l) r := by
  rw [prodUpTo_sub_prodUpTo]
  refine Finset.sum_congr rfl fun j _ => prodUpTo_congr r fun l _ => ?_
  by_cases h1 : l < j
  · simp [h1]
  · by_cases h2 : l = j
    · subst h2
      simp [Matrix.sub_mul]
    · simp [h1, h2]
private theorem prod_range_ite_eq_single (a b : ℝ) (q j : ℕ) (hj : j < q + 1) :
    ∏ l ∈ range (q + 1), (if l = j then a else b) = a * b ^ q := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hj)]
  simp only [if_true]
  congr 1
  rw [Finset.prod_congr rfl (fun l hl => if_neg (Finset.ne_of_mem_erase hl)), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range]
  simp
end Telescopes
private theorem finOfNat_ne_succ (q : ℕ) (hq : 1 ≤ q) (l : ℕ) :
    Fin.ofNat (q + 1) l ≠ Fin.ofNat (q + 1) (l + 1) := by
  intro h
  have h1 : l % (q + 1) = (l + 1) % (q + 1) := congrArg Fin.val h
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < q + 1 by omega)] at h1
  have hlt := Nat.mod_lt l (show 0 < q + 1 by omega)
  set r := l % (q + 1)
  by_cases hr : r + 1 < q + 1
  · rw [Nat.mod_eq_of_lt hr] at h1
    omega
  · have : r + 1 = q + 1 := by omega
    rw [this, Nat.mod_self] at h1
    omega
private theorem finRotate_finOfNat (q l : ℕ) :
    finRotate (q + 1) (Fin.ofNat (q + 1) l) = Fin.ofNat (q + 1) (l + 1) := by
  rw [finRotate_apply]
  ext
  show (l % (q + 1) + ((1 : Fin (q + 1)) : ℕ)) % (q + 1) = (l + 1) % (q + 1)
  rw [Fin.val_one']
  exact (Nat.add_mod _ _ _).symm
private theorem finOfNat_val (q : ℕ) (j : Fin (q + 1)) : Fin.ofNat (q + 1) (j : ℕ) = j := by
  ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt j.2]
theorem traceOfLocalKernelCycle_bound : TraceOfLocalKernelCycle := by
  intro S X Q _ _ _ _ _ _ q A K T Pl Cc w Nr g B δ c η G Am s hq hB hδ hc hη hG hAm hw hcard hnear hmass hT hC hM hg
  set e : ℕ → Fin (q + 1) := fun l => s (Fin.ofNat (q + 1) l) with he
  have hne : ∀ l, e l ≠ e (l + 1) := fun l h => finOfNat_ne_succ q hq l (s.injective h)
  have hper : e (q + 1) = e 0 := by
    have : Fin.ofNat (q + 1) (q + 1) = Fin.ofNat (q + 1) 0 := by
      ext
      simp [Fin.ofNat]
    simp only [he, this]
  set Tt : Matrix (S × X) (S × X) ℝ :=
    (siteLift : Matrix X (S × X) ℝ).transpose * T * (siteLift : Matrix X (S × X) ℝ) with hTtdef
  have hTt : ∀ y y', Tt y y' = T y.2 y'.2 := siteLift_conj_apply T
  set Yt : Matrix (S × X) (S × X) ℝ :=
    (planeProj (S := S) Pl) * planeCouplings Cc * (planeProj (S := S) Pl).transpose with hYtdef
  have hYt : ∀ y y', Yt y y' = Cc y.1 y'.1 (Pl y.2) (Pl y'.2) := planeProj_conj_apply Pl Cc
  let Kk : ℕ → Matrix (S × X) (S × X) ℝ := fun l => blockDiag (A (e l)) (K (e l))
  let Mm : ℕ → Matrix (S × Q) (S × Q) ℝ := fun l => blockDiag (A (e l)) fun z => planeSum Pl (K (e l) z)
  let Gg : ℕ → Matrix (S × Q) (S × Q) ℝ :=
    fun l => blockDiag (A (e l)) fun z Q₁ Q₂ => if Q₁ = Q₂ then g (e l) z else 0
  have h0 : Matrix.trace (List.ofFn fun j : Fin (q + 1) => (∑ z ∈ A (s j), K (s j) z) * T).prod =
      Matrix.trace (prodUpTo (fun l => Kk l * Tt) (q + 1)) := by
    rw [list_ofFn_prod_eq_prodUpTo]
    have := trace_prodUpTo_swap (siteLift : Matrix X (S × X) ℝ)
      (fun l => Kk l * (siteLift : Matrix X (S × X) ℝ).transpose * T) q
    calc _ = Matrix.trace (prodUpTo (fun l => (siteLift : Matrix X (S × X) ℝ) *
          (Kk l * (siteLift : Matrix X (S × X) ℝ).transpose * T)) (q + 1)) := by
          congr 1
          refine prodUpTo_congr _ fun l _ => ?_
          simp only [Kk]
          rw [← siteLift_mul_blockDiag]
          simp only [Matrix.mul_assoc]
          rfl
      _ = _ := by
          rw [this]
          congr 1
          refine prodUpTo_congr _ fun l _ => ?_
          simp only [hTtdef, Matrix.mul_assoc]
  have h1 : Matrix.trace (prodUpTo (fun l => Kk l * Yt) (q + 1)) =
      Matrix.trace (prodUpTo (fun l => Mm l * planeCouplings Cc) (q + 1)) := by
    have := trace_prodUpTo_swap (planeProj (S := S) Pl).transpose
      (fun l => Kk l * (planeProj (S := S) Pl) * planeCouplings Cc) q
    calc _ = Matrix.trace (prodUpTo (fun l => (Kk l * (planeProj (S := S) Pl) * planeCouplings Cc) *
          (planeProj (S := S) Pl).transpose) (q + 1)) := by
          congr 1
          refine prodUpTo_congr _ fun l _ => ?_
          simp only [hYtdef, Matrix.mul_assoc]
      _ = _ := by
          rw [← this]
          congr 1
          refine prodUpTo_congr _ fun l _ => ?_
          simp only [Mm, Kk]
          rw [← planeProj_conj_blockDiag]
          simp only [Matrix.mul_assoc]
  have hstep1 : |Matrix.trace (prodUpTo (fun l => Kk l * Tt) (q + 1)) -
      Matrix.trace (prodUpTo (fun l => Kk l * Yt) (q + 1))| ≤
      ((q : ℝ) + 1) * (δ * (c + δ) ^ q * (Am * B) ^ (q + 1)) := by
    rw [← Matrix.trace_sub, prodUpTo_sub_right Kk (fun _ => Tt) (fun _ => Yt), Matrix.trace_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j ∈ range (q + 1), |Matrix.trace (prodUpTo (fun l => Kk l *
        (if l < j then Tt else if l = j then Tt - Yt else Yt)) (q + 1))| ≤
        δ * (c + δ) ^ q * (Am * B) ^ (q + 1) := by
      intro j hj
      have hjq := Finset.mem_range.mp hj
      have := abs_trace_prodUpTo_le Kk (fun l => if l < j then Tt else if l = j then Tt - Yt else Yt)
        (fun l y => y.1 ∈ A (e l) ∧ Nr y.1 y.2) (fun _ y => w y.1 y.2)
        (fun l => if l = j then δ else c + δ) (fun _ => Am * B)
        (fun _ y => le_trans zero_le_one (hw _ _))
        (fun l => by split_ifs <;> positivity)
        (fun _ => by positivity)
        (fun l y y' hk => by
          have hs := blockDiag_support hk
          have hyy : y.1 = y'.1 := by
            by_contra hn
            exact hk (by simp only [Kk, blockDiag, hn, false_and, if_false])
          have hk' : K (e l) y.1 y.2 y'.2 ≠ 0 := by
            intro h0
            exact hk (by simp only [Kk, blockDiag, hyy, hs.2, and_self, if_true]; rw [← hyy]; exact h0)
          obtain ⟨n1, n2⟩ := hnear (e l) y.1 hs.1 y.2 y'.2 hk'
          exact ⟨⟨hs.1, n1⟩, ⟨hs.2, hyy ▸ n2⟩⟩)
        (fun l y y' hy hy' => by
          have D := hT (e l) (e (l + 1)) (hne l) y.1 hy.1 y'.1 hy'.1 y.2 y'.2 hy.2 hy'.2
          have Cb := hC (e l) (e (l + 1)) (hne l) y.1 hy.1 y'.1 hy'.1 (Pl y.2) (Pl y'.2)
          have w1 := hw y.1 y.2
          have w2 := hw y'.1 y'.2
          have ww : 1 ≤ w y.1 y.2 * w y'.1 y'.2 := by nlinarith
          have hcw : c ≤ c * w y.1 y.2 * w y'.1 y'.2 := by nlinarith
          have hsub : |T y.2 y'.2| ≤ |T y.2 y'.2 - Cc y.1 y'.1 (Pl y.2) (Pl y'.2)| +
              |Cc y.1 y'.1 (Pl y.2) (Pl y'.2)| := by
            have := abs_add_le (T y.2 y'.2 - Cc y.1 y'.1 (Pl y.2) (Pl y'.2)) (Cc y.1 y'.1 (Pl y.2) (Pl y'.2))
            simpa using this
          have hdw : 0 ≤ δ * w y.1 y.2 * w y'.1 y'.2 := by positivity
          by_cases h1 : l < j
          · have h2 : l ≠ j := by omega
            simp only [if_pos h1, if_neg h2, hTt]
            nlinarith
          · by_cases h2 : l = j
            · simp only [if_neg h1, if_pos h2, Matrix.sub_apply, hTt, hYt]
              exact D
            · simp only [if_neg h1, if_neg h2, hYt]
              nlinarith)
        (fun l => blockDiag_weighted_mass_le (A (e l)) (K (e l)) w B Am hB (hcard _) (hmass _)) q
        (fun y => by simp only [hper]) (fun _ => rfl)
      rw [prod_range_ite_eq_single _ _ _ _ hjq, Finset.prod_const, Finset.card_range] at this
      exact this
    calc _ ≤ ∑ _j ∈ range (q + 1), δ * (c + δ) ^ q * (Am * B) ^ (q + 1) := Finset.sum_le_sum hj
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have hstep2 : |Matrix.trace (prodUpTo (fun l => Mm l * planeCouplings Cc) (q + 1)) -
      Matrix.trace (prodUpTo (fun l => Gg l * planeCouplings Cc) (q + 1))| ≤
      ((q : ℝ) + 1) * (c ^ (q + 1) * (Am * (Fintype.card Q : ℝ) ^ 2 * η) *
        (Am * (B + (Fintype.card Q : ℝ) * G)) ^ q) := by
    rw [← Matrix.trace_sub, prodUpTo_sub_left Mm Gg (fun _ => planeCouplings Cc), Matrix.trace_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set Wd : ℝ := Am * ((Fintype.card Q : ℝ) ^ 2 * η) with hWd
    set Wm : ℝ := Am * (B + (Fintype.card Q : ℝ) * G) with hWm
    have hWd0 : 0 ≤ Wd := by positivity
    have hWm0 : 0 ≤ Wm := by positivity
    have hMass : ∀ l, ∑ a, ∑ b, |Mm l a b| * (1 : ℝ) * 1 ≤ Wm := by
      intro l
      refine blockDiag_weighted_mass_le (A (e l)) (fun z => planeSum Pl (K (e l) z)) (fun _ _ => 1) _ Am
        (by positivity) (hcard _) ?_
      intro z hz
      simp only [mul_one]
      have h1 := planeSum_abs_mass_le Pl (K (e l) z)
      have h2 : ∑ a, ∑ b, |K (e l) z a b| ≤ ∑ a, ∑ b, |K (e l) z a b| * w z a * w z b := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        have w1 := hw z a
        have w2 := hw z b
        have ww : 1 ≤ w z a * w z b := by nlinarith
        have := abs_nonneg (K (e l) z a b)
        nlinarith
      have h3 := hmass (e l) z hz
      have : 0 ≤ (Fintype.card Q : ℝ) * G := by positivity
      linarith
    have hGass : ∀ l, ∑ a, ∑ b, |Gg l a b| * (1 : ℝ) * 1 ≤ Wm := by
      intro l
      refine blockDiag_weighted_mass_le (A (e l)) (fun z Q₁ Q₂ => if Q₁ = Q₂ then g (e l) z else 0)
        (fun _ _ => 1) _ Am (by positivity) (hcard _) ?_
      intro z hz
      simp only [mul_one]
      have h1 : ∀ Q₁ : Q, ∑ Q₂, |if Q₁ = Q₂ then g (e l) z else 0| ≤ G := by
        intro Q₁
        rw [Finset.sum_eq_single Q₁]
        · simpa using hg (e l) z hz
        · intro Q₂ _ hne
          simp [hne.symm]
        · simp
      calc _ ≤ ∑ _Q₁ : Q, G := Finset.sum_le_sum fun Q₁ _ => h1 Q₁
        _ = (Fintype.card Q : ℝ) * G := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := by linarith
    have hDiff : ∀ l, ∑ a, ∑ b, |(Mm l - Gg l) a b| * (1 : ℝ) * 1 ≤ Wd := by
      intro l
      simp only [Mm, Gg]
      rw [blockDiag_sub]
      refine blockDiag_weighted_mass_le (A (e l)) _ (fun _ _ => 1) _ Am (by positivity) (hcard _) ?_
      intro z hz
      simp only [mul_one]
      calc _ ≤ ∑ _Q₁ : Q, ∑ _Q₂ : Q, η :=
            Finset.sum_le_sum fun Q₁ _ => Finset.sum_le_sum fun Q₂ _ => hM (e l) z hz Q₁ Q₂
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    have hj : ∀ j ∈ range (q + 1), |Matrix.trace (prodUpTo (fun l =>
        (if l < j then Mm l else if l = j then Mm j - Gg j else Gg l) * (fun _ => planeCouplings Cc) l)
          (q + 1))| ≤ c ^ (q + 1) * (Wd * Wm ^ q) := by
      intro j hj
      have hjq := Finset.mem_range.mp hj
      have := abs_trace_prodUpTo_le (fun l => if l < j then Mm l else if l = j then Mm j - Gg j else Gg l)
        (fun _ => planeCouplings Cc)
        (fun l y => y.1 ∈ A (e l)) (fun _ _ => 1) (fun _ => c) (fun l => if l = j then Wd else Wm)
        (fun _ _ => zero_le_one) (fun _ => hc)
        (fun l => by split_ifs <;> assumption)
        (fun l y y' hk => by
          by_cases h1 : l < j
          · simp only [if_pos h1] at hk
            exact blockDiag_support hk
          · by_cases h2 : l = j
            · subst h2
              simp only [if_neg h1, if_true] at hk
              simp only [Mm, Gg] at hk
              rw [blockDiag_sub] at hk
              exact blockDiag_support hk
            · simp only [if_neg h1, if_neg h2] at hk
              exact blockDiag_support hk)
        (fun l y y' hy hy' => by
          simpa [planeCouplings] using hC (e l) (e (l + 1)) (hne l) y.1 hy y'.1 hy' y.2 y'.2)
        (fun l => by
          by_cases h1 : l < j
          · have h2 : l ≠ j := by omega
            simp only [if_pos h1, if_neg h2]
            exact hMass l
          · by_cases h2 : l = j
            · subst h2
              simp only [if_neg h1, if_true]
              exact hDiff l
            · simp only [if_neg h1, if_neg h2]
              exact hGass l) q
        (fun y => by simp only [hper]) (fun _ => rfl)
      rw [prod_range_ite_eq_single _ _ _ _ hjq, Finset.prod_const, Finset.card_range] at this
      exact this
    calc _ ≤ ∑ _j ∈ range (q + 1), c ^ (q + 1) * (Wd * Wm ^ q) := Finset.sum_le_sum hj
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hWd]
        push_cast
        ring
  have hstep3 : Matrix.trace (prodUpTo (fun l => Gg l * planeCouplings Cc) (q + 1)) =
      ∑ z ∈ Fintype.piFinset A, (∏ i, g i (z i)) *
        Matrix.trace (List.ofFn fun j : Fin (q + 1) => Cc (z (s j)) (z (s (finRotate (q + 1) j)))).prod := by
    have hGC : ∀ l (y y' : S × Q), (Gg l * planeCouplings Cc) y y' =
        (if y.1 ∈ A (e l) then g (e l) y.1 else 0) * Cc y.1 y'.1 y.2 y'.2 := by
      intro l y y'
      rw [Matrix.mul_apply, Finset.sum_eq_single y]
      · by_cases hy : y.1 ∈ A (e l) <;> simp [Gg, blockDiag, hy, planeCouplings]
      · intro b _ hb
        have : Gg l y b = 0 := by
          by_cases h1 : y.1 = b.1 ∧ y.1 ∈ A (e l)
          · have h2 : y.2 ≠ b.2 := fun h => hb (Prod.ext h1.1.symm h.symm)
            simp [Gg, blockDiag, h1.1, h2]
          · simp only [Gg, blockDiag, if_neg h1]
        rw [this, zero_mul]
      · simp
    let ind : ℕ → S → ℝ := fun l z => if z ∈ A (e l) then g (e l) z else 0
    let fo : (Fin (q + 1) → S) → ℕ → S := fun zz l => zz (Fin.ofNat (q + 1) l)
    have hsplit : Matrix.trace (prodUpTo (fun l => Gg l * planeCouplings Cc) (q + 1)) =
        ∑ zz : Fin (q + 1) → S, (∏ l ∈ range (q + 1), ind l (fo zz l)) *
          Matrix.trace (prodUpTo (fun l => Cc (fo zz l) (fo zz (l + 1))) (q + 1)) := by
      rw [trace_prodUpTo_eq_sum_cycles,
        ← (Equiv.arrowProdEquivProdArrow (Fin (q + 1)) (fun _ => S) (fun _ => Q)).symm.sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun zz _ => ?_
      rw [trace_prodUpTo_eq_sum_cycles, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Qs _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [hGC]
      rfl
    rw [hsplit, ← (Equiv.arrowCongr s.symm (Equiv.refl S)).sum_comp]
    rw [← Finset.sum_subset (Finset.subset_univ (Fintype.piFinset A))]
    · refine Finset.sum_congr rfl fun z hz => ?_
      have hzm := Fintype.mem_piFinset.mp hz
      congr 1
      · rw [← Fin.prod_univ_eq_prod_range
          (fun l => ind l (fo ((Equiv.arrowCongr s.symm (Equiv.refl S)) z) l)) (q + 1)]
        rw [← Equiv.prod_comp s (fun i => g i (z i))]
        refine Finset.prod_congr rfl fun j _ => ?_
        have hsj : e (j : ℕ) = s j := by simp only [he, finOfNat_val]
        have hzj : fo ((Equiv.arrowCongr s.symm (Equiv.refl S)) z) (j : ℕ) = z (s j) := by
          simp only [fo, finOfNat_val]
          rfl
        simp only [ind, hsj, hzj]
        rw [if_pos (hzm (s j))]
      · rw [list_ofFn_prod_eq_prodUpTo]
        congr 1
        refine prodUpTo_congr _ fun l _ => ?_
        simp only [finRotate_finOfNat]
        rfl
    · intro z _ hz
      have hz' : ∃ i, z i ∉ A i := by
        by_contra hn
        push_neg at hn
        exact hz (Fintype.mem_piFinset.mpr hn)
      obtain ⟨i, hi⟩ := hz'
      have hprod : ∏ l ∈ range (q + 1), ind l (fo ((Equiv.arrowCongr s.symm (Equiv.refl S)) z) l) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.2 (s.symm i).2) ?_
        have hsj : e ((s.symm i : Fin (q + 1)) : ℕ) = i := by
          simp only [he, finOfNat_val, Equiv.apply_symm_apply]
        have hzj : fo ((Equiv.arrowCongr s.symm (Equiv.refl S)) z) ((s.symm i : Fin (q + 1)) : ℕ) = z i := by
          simp only [fo, finOfNat_val]
          show z (s (s.symm i)) = z i
          rw [Equiv.apply_symm_apply]
        simp only [ind, hsj, hzj]
        rw [if_neg hi]
      rw [hprod, zero_mul]
  rw [h0]
  rw [← hstep3]
  have h4 := abs_sub_le (Matrix.trace (prodUpTo (fun l => Kk l * Tt) (q + 1)))
    (Matrix.trace (prodUpTo (fun l => Kk l * Yt) (q + 1)))
    (Matrix.trace (prodUpTo (fun l => Gg l * planeCouplings Cc) (q + 1)))
  rw [h1] at h4
  rw [h1] at hstep1
  linarith
end YangMills.Construction.MatrixTraces
end
