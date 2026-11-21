import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.TraceInequalityOfContractions
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.TransferOperators
namespace InterleavedTrace
section FiniteDimension
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
def IsNonexpanding (X : Module.End ℂ W) : Prop := ∀ x, ‖X x‖ ≤ ‖x‖
theorem IsNonexpanding.mul {X Y : Module.End ℂ W} (hX : IsNonexpanding X) (hY : IsNonexpanding Y) :
    IsNonexpanding (X * Y) := fun x => (hX (Y x)).trans (hY x)
theorem isNonexpanding_one : IsNonexpanding (1 : Module.End ℂ W) := fun _ => le_rfl
variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ W)
def diagOp (c : ι → ℂ) : Module.End ℂ W :=
  ∑ k, c k • (innerₛₗ ℂ (b k)).smulRight (b k)
theorem diagOp_apply (c : ι → ℂ) (v : W) :
    diagOp b c v = ∑ k, (c k * inner ℂ (b k) v) • b k := by
  simp [diagOp, LinearMap.sum_apply, LinearMap.smulRight_apply, smul_smul]
theorem inner_diagOp (c : ι → ℂ) (k : ι) (v : W) :
    inner ℂ (b k) (diagOp b c v) = c k * inner ℂ (b k) v := by
  classical
  rw [diagOp_apply, inner_sum]
  simp [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal]
theorem diagOp_mul (c d : ι → ℂ) :
    diagOp b c * diagOp b d = diagOp b (fun k => c k * d k) := by
  ext v
  simp only [Module.End.mul_apply]
  rw [diagOp_apply b c, diagOp_apply b (fun k => c k * d k)]
  exact Finset.sum_congr rfl fun k _ => by rw [inner_diagOp, mul_assoc]
theorem diagOp_basisVec (c : ι → ℂ) (k : ι) : diagOp b c (b k) = c k • b k := by
  classical
  rw [diagOp_apply]
  simp [orthonormal_iff_ite.1 b.orthonormal]
theorem trace_diagOp_mul (c : ι → ℂ) (Z : Module.End ℂ W) :
    LinearMap.trace ℂ W (diagOp b c * Z) = ∑ k, c k * inner ℂ (b k) (Z (b k)) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  exact Finset.sum_congr rfl fun k _ => inner_diagOp b c k _
theorem isNonexpanding_diagOp {c : ι → ℂ} (hc : ∀ k, ‖c k‖ ≤ 1) :
    IsNonexpanding (diagOp b c) := by
  intro v
  have h : ‖diagOp b c v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (diagOp b c v), ← b.sum_sq_norm_inner_right v]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [inner_diagOp, norm_mul, mul_pow]
    have h1 : ‖c k‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hc k)
    nlinarith [sq_nonneg ‖(inner ℂ (b k) v : ℂ)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
theorem trace_diagOp_mul_diagOp (c d : ι → ℂ) (X M : Module.End ℂ W) :
    LinearMap.trace ℂ W (diagOp b c * (X * (diagOp b d * M))) =
      ∑ k, ∑ l, c k * d l * (inner ℂ (b k) (X (b l)) * inner ℂ (b l) (M (b k))) := by
  rw [trace_diagOp_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Module.End.mul_apply, diagOp_apply, map_sum, map_smul, inner_sum,
    inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
def realPow (l : ℝ) (z : ℂ) : ℂ := if 0 < l then Complex.exp (z * (Real.log l : ℂ)) else 0
theorem realPow_add (l : ℝ) (z w : ℂ) : realPow l (z + w) = realPow l z * realPow l w := by
  unfold realPow
  split_ifs
  · rw [add_mul, Complex.exp_add]
  · simp
theorem norm_realPow_le (l : ℝ) (z : ℂ) : ‖realPow l z‖ ≤ Real.exp (|z.re| * |Real.log l|) := by
  unfold realPow
  split_ifs
  · rw [Complex.norm_exp, Complex.re_mul_ofReal]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_mul _ _).le)
  · simpa using (Real.exp_pos _).le
theorem norm_realPow_le_one (l : ℝ) {z : ℂ} (hz : z.re = 0) : ‖realPow l z‖ ≤ 1 := by
  simpa [hz] using norm_realPow_le l z
theorem differentiable_realPow (l : ℝ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ fun ζ => realPow l (g ζ) := by
  unfold realPow
  split_ifs
  · exact (hg.mul_const _).cexp
  · exact differentiable_const _
theorem realPow_natCast {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : n ≠ 0) :
    realPow l (n : ℂ) = ((l ^ n : ℝ) : ℂ) := by
  unfold realPow
  split_ifs with h
  · rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm,
      Real.exp_mul, Real.exp_log h, Real.rpow_natCast]
  · have : l = 0 := le_antisymm (not_lt.1 h) hl
    simp [this, hn]
theorem norm_le_of_verticalStrip (lam : ι → ℝ) (T : ℝ) (m : ι → ι → ℂ) (C : ℝ)
    (h0 : ∀ ζ : ℂ, ζ.re = 0 → ‖∑ k, ∑ l, realPow (lam k) (T * ζ) * realPow (lam l) (T * (1 - ζ)) *
      m k l‖ ≤ C)
    (h1 : ∀ ζ : ℂ, ζ.re = 1 → ‖∑ k, ∑ l, realPow (lam k) (T * ζ) * realPow (lam l) (T * (1 - ζ)) *
      m k l‖ ≤ C)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖∑ k, ∑ l, realPow (lam k) (T * (x : ℂ)) * realPow (lam l) (T * (1 - (x : ℂ))) * m k l‖ ≤ C := by
  set F : ℂ → ℂ := fun ζ =>
    ∑ k, ∑ l, realPow (lam k) (T * ζ) * realPow (lam l) (T * (1 - ζ)) * m k l with hF
  have hC : 0 ≤ C := (norm_nonneg _).trans (h0 0 rfl)
  have hdiff : Differentiable ℂ F := by
    refine Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun l _ => ?_
    refine Differentiable.mul_const (Differentiable.mul ?_ ?_) _
    · exact differentiable_realPow _ (by fun_prop)
    · exact differentiable_realPow _ (by fun_prop)
  have hbound : ∀ (l : ℝ) (y : ℂ), 0 ≤ y.re → y.re ≤ 1 →
      ‖realPow l (T * y)‖ ≤ Real.exp (|T| * |Real.log l|) := by
    intro l y hy0 hy1
    refine (norm_realPow_le l _).trans (Real.exp_le_exp.2 ?_)
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Complex.re_ofReal_mul, abs_mul, abs_of_nonneg hy0]
    exact mul_le_of_le_one_right (abs_nonneg _) hy1
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ k, ∑ l, Real.exp (|T| * |Real.log (lam k)|) * Real.exp (|T| * |Real.log (lam l)|) *
      ‖m k l‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : 0 ≤ z.re := hz.1
    have hz1 : z.re ≤ 1 := hz.2
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, norm_mul]
    have e1 := hbound (lam k) z hz0 hz1
    have e2 := hbound (lam l) (1 - z) (by simpa using hz1) (by simpa using hz0)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul e1 e2 (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (x : ℂ)) (a := C) (b := C)
    (by exact ⟨by simpa using hx0, by simpa using hx1⟩) hdiff.diffContOnCl hB
    (fun z hz => h0 z hz) (fun z hz => h1 z hz)
  have hre : ((x : ℂ)).re = x := Complex.ofReal_re x
  rw [hre, ← Real.rpow_add_of_nonneg hC (by linarith) hx0] at key
  simpa using key
variable (lam : ι → ℝ)
def specPow (z : ℂ) : Module.End ℂ W := diagOp b fun k => realPow (lam k) z
theorem specPow_add (z w : ℂ) :
    specPow b lam (z + w) = specPow b lam z * specPow b lam w := by
  unfold specPow
  rw [diagOp_mul]
  simp only [realPow_add]
theorem isNonexpanding_specPow {z : ℂ} (hz : z.re = 0) :
    IsNonexpanding (specPow b lam z) :=
  isNonexpanding_diagOp b fun _ => norm_realPow_le_one _ hz
def interleavedWord : List (ℝ × Module.End ℂ W) → Module.End ℂ W
  | [] => 1
  | p :: l => specPow b lam (p.1 : ℂ) * p.2 * interleavedWord l
theorem norm_trace_specPow_mul_le (t : ℝ) {Z : Module.End ℂ W} (hZ : IsNonexpanding Z) :
    ‖LinearMap.trace ℂ W (specPow b lam (t : ℂ) * Z)‖ ≤
      ∑ k, ‖realPow (lam k) (t : ℂ)‖ := by
  unfold specPow
  rw [trace_diagOp_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have hk : ‖b k‖ = 1 := b.orthonormal.1 k
  calc ‖(inner ℂ (b k) (Z (b k)) : ℂ)‖ ≤ ‖b k‖ * ‖Z (b k)‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by rw [hk, one_mul]; exact (hZ _).trans hk.le
theorem norm_trace_interleavedWord_le (n : ℕ) : ∀ l : List (ℝ × Module.End ℂ W), l.length = n + 1 →
    (∀ p ∈ l, 0 ≤ p.1 ∧ IsNonexpanding p.2) → ∀ Y : Module.End ℂ W, IsNonexpanding Y →
    ‖LinearMap.trace ℂ W (interleavedWord b lam l * Y)‖ ≤
      ∑ k, ‖realPow (lam k) (((l.map Prod.fst).sum : ℝ) : ℂ)‖ := by
  induction n with
  | zero =>
    intro l hl hp Y hY
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    have h := norm_trace_specPow_mul_le b lam p.1 ((hp p (by simp)).2.mul hY)
    simpa [interleavedWord, mul_assoc] using h
  | succ n ih =>
    intro l hl hp Y hY
    obtain ⟨⟨a, X₁⟩, ⟨c, X₂⟩, l', rfl⟩ : ∃ p q l', l = p :: q :: l' := by
      match l, hl with
      | p :: q :: l', _ => exact ⟨p, q, l', rfl⟩
    have hl' : l'.length = n := by simpa using hl
    have ha : 0 ≤ a := (hp (a, X₁) (by simp)).1
    have hc : 0 ≤ c := (hp (c, X₂) (by simp)).1
    have hX₁ : IsNonexpanding X₁ := (hp (a, X₁) (by simp)).2
    have hX₂ : IsNonexpanding X₂ := (hp (c, X₂) (by simp)).2
    have hrest : ∀ p ∈ l', 0 ≤ p.1 ∧ IsNonexpanding p.2 := fun p h => hp p (by simp [h])
    set T : ℝ := a + c with hT
    have hT0 : 0 ≤ T := add_nonneg ha hc
    set R := interleavedWord b lam l' with hR
    set M : Module.End ℂ W := X₂ * (R * Y) with hM
    set S := specPow b lam with hS
    have hF : ∀ ζ : ℂ, LinearMap.trace ℂ W (S (T * ζ) * (X₁ * (S (T * (1 - ζ)) * M))) =
        ∑ k, ∑ l, realPow (lam k) (T * ζ) * realPow (lam l) (T * (1 - ζ)) *
          (inner ℂ (b k) (X₁ (b l)) * inner ℂ (b l) (M (b k))) := fun ζ =>
      trace_diagOp_mul_diagOp b _ _ _ _
    set C : ℝ := ∑ k, ‖realPow (lam k) ((((T + (l'.map Prod.fst).sum : ℝ)) : ℝ) : ℂ)‖ with hC
    have hIH : ∀ (Z : Module.End ℂ W) (Y' : Module.End ℂ W), IsNonexpanding Z → IsNonexpanding Y' →
        ‖LinearMap.trace ℂ W (S (T : ℂ) * Z * R * Y')‖ ≤ C := by
      intro Z Y' hZ hY'
      have h := ih ((T, Z) :: l') (by simpa using hl') (by
        intro p hmem
        rcases List.mem_cons.1 hmem with rfl | h
        · exact ⟨hT0, hZ⟩
        · exact hrest p h) Y' hY'
      have e2 : (((T, Z) :: l').map Prod.fst).sum = T + (l'.map Prod.fst).sum := by simp
      rw [e2] at h
      exact h
    have hzero : ∀ ζ : ℂ, ζ.re = 0 →
        ‖LinearMap.trace ℂ W (S (T * ζ) * (X₁ * (S (T * (1 - ζ)) * M)))‖ ≤ C := by
      intro ζ hζ
      have hre : ((T : ℂ) * ζ).re = 0 := by rw [Complex.re_ofReal_mul, hζ, mul_zero]
      have hre' : (-((T : ℂ) * ζ)).re = 0 := by rw [Complex.neg_re, hre, neg_zero]
      have hU := isNonexpanding_specPow b lam hre
      have hV := isNonexpanding_specPow b lam hre'
      have hsplit : S (T * (1 - ζ)) = S (T : ℂ) * S (-((T : ℂ) * ζ)) := by
        rw [hS, ← specPow_add]
        congr 1
        ring
      have h := hIH (S (-((T : ℂ) * ζ)) * X₂) (Y * (S (T * ζ) * X₁)) (hV.mul hX₂)
        (hY.mul (hU.mul hX₁))
      rw [hsplit]
      have e : S (T * ζ) * (X₁ * (S (T : ℂ) * S (-((T : ℂ) * ζ)) * M)) =
          (S (T * ζ) * X₁) * (S (T : ℂ) * (S (-((T : ℂ) * ζ)) * X₂) * R * Y) := by
        simp only [hM, mul_assoc]
      rw [e, LinearMap.trace_mul_comm]
      simpa only [mul_assoc] using h
    have hone : ∀ ζ : ℂ, ζ.re = 1 →
        ‖LinearMap.trace ℂ W (S (T * ζ) * (X₁ * (S (T * (1 - ζ)) * M)))‖ ≤ C := by
      intro ζ hζ
      have hre : ((T : ℂ) * (ζ - 1)).re = 0 := by
        rw [Complex.re_ofReal_mul, Complex.sub_re, hζ]; simp
      have hre' : ((T : ℂ) * (1 - ζ)).re = 0 := by
        rw [Complex.re_ofReal_mul, Complex.sub_re, hζ]; simp
      have hU := isNonexpanding_specPow b lam hre
      have hV := isNonexpanding_specPow b lam hre'
      have hsplit : S (T * ζ) = S (T : ℂ) * S ((T : ℂ) * (ζ - 1)) := by
        rw [hS, ← specPow_add]
        congr 1
        ring
      have h := hIH (S ((T : ℂ) * (ζ - 1)) * X₁ * (S (T * (1 - ζ)) * X₂)) Y
        ((hU.mul hX₁).mul (hV.mul hX₂)) hY
      rw [hsplit]
      simpa only [hM, mul_assoc] using h
    have hx : ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ (T : ℂ) * (x : ℂ) = (a : ℂ) ∧
        (T : ℂ) * (1 - (x : ℂ)) = (c : ℂ) := by
      rcases hT0.eq_or_lt with h0 | hpos
      · have ha0 : a = 0 := by linarith
        have hc0 : c = 0 := by linarith
        exact ⟨0, le_rfl, zero_le_one, by simp [← h0, ha0], by simp [← h0, hc0]⟩
      · refine ⟨a / T, div_nonneg ha hT0, (div_le_one hpos).2 (by linarith), ?_, ?_⟩
        · rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hpos.ne']
        · have : T * (1 - a / T) = c := by
            field_simp
            linarith
          rw [← this]
          push_cast
          ring
    obtain ⟨x, hx0, hx1, hxa, hxc⟩ := hx
    have hfinal := norm_le_of_verticalStrip lam T
      (fun k l => inner ℂ (b k) (X₁ (b l)) * inner ℂ (b l) (M (b k))) C
      (fun ζ hζ => by rw [← hF]; exact hzero ζ hζ) (fun ζ hζ => by rw [← hF]; exact hone ζ hζ)
      hx0 hx1
    rw [← hF, hxa, hxc] at hfinal
    have hsum : (((a, X₁) :: (c, X₂) :: l').map Prod.fst).sum = T + (l'.map Prod.fst).sum := by
      simp [hT, add_assoc]
    rw [hsum]
    simpa only [interleavedWord, hM, hR, mul_assoc] using hfinal
theorem mul_prod_map_mul_eq_prod_map_mul {M : Type*} [Monoid M] (A : M) (L : List M) :
    A * (L.map (· * A)).prod = (L.map (A * ·)).prod * A := by
  induction L with
  | nil => simp
  | cons X L ih =>
    simp only [List.map_cons, List.prod_cons]
    calc A * (X * A * (L.map (· * A)).prod) = A * X * (A * (L.map (· * A)).prod) := by
          simp only [mul_assoc]
      _ = A * X * ((L.map (A * ·)).prod * A) := by rw [ih]
      _ = A * X * (L.map (A * ·)).prod * A := by simp only [mul_assoc]
theorem interleavedProd_succ {M : Type*} [Monoid M] {n : ℕ} (X : Fin (n + 1) → M) (A : M) :
    interleavedProd X A = X 0 * A * interleavedProd (fun j : Fin n => X j.succ) A := by
  simp [interleavedProd, List.ofFn_succ]
theorem interleavedProd_eq_prod_map {M : Type*} [Monoid M] {n : ℕ} (X : Fin n → M) (A : M) :
    interleavedProd X A = ((List.ofFn X).map (· * A)).prod := by
  simp [interleavedProd, List.map_ofFn, Function.comp_def]
theorem map_interleavedProd {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {n : ℕ}
    (X : Fin n → M) (A : M) :
    f (interleavedProd X A) = interleavedProd (fun j => f (X j)) (f A) := by
  simp [interleavedProd, map_list_prod, List.map_ofFn, Function.comp_def]
theorem interleavedProd_one {M : Type*} [Monoid M] (n : ℕ) (A : M) :
    interleavedProd (fun _ : Fin n => (1 : M)) A = A ^ n := by
  simp [interleavedProd, List.ofFn_const, List.prod_replicate]
theorem sum_fst_map_one_pair (L : List (Module.End ℂ W)) :
    ((L.map fun Z => ((1 : ℝ), Z)).map Prod.fst).sum = L.length := by
  induction L with
  | nil => simp
  | cons Z L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    push_cast
    ring
theorem norm_trace_interleavedProd_le [FiniteDimensional ℂ W] {s : ℕ} (hs : 1 ≤ s)
    (A : Module.End ℂ W) (X : Fin s → Module.End ℂ W) (hA : LinearMap.IsSymmetric A)
    (hpos : ∀ x : W, 0 ≤ (inner ℂ x (A x) : ℂ).re) (hX : ∀ j, IsNonexpanding (X j)) :
    ‖LinearMap.trace ℂ W (interleavedProd X A)‖ ≤ (LinearMap.trace ℂ W (A ^ s)).re ∧
      (LinearMap.trace ℂ W (A ^ s)).im = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  set b := hA.eigenvectorBasis rfl with hb
  set lam := hA.eigenvalues rfl with hlam
  have hAb : ∀ k, A (b k) = (lam k : ℂ) • b k := hA.apply_eigenvectorBasis rfl
  have hnorm : ∀ k, ‖b k‖ = 1 := b.orthonormal.1
  have hself : ∀ k, (inner ℂ (b k) (b k) : ℂ) = 1 := fun k => by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
  have hlam0 : ∀ k, 0 ≤ lam k := by
    intro k
    have h := hpos (b k)
    rw [hAb, inner_smul_right, hself] at h
    simpa using h
  have hS1 : specPow b lam 1 = A := by
    refine b.toBasis.ext fun k => ?_
    simp only [OrthonormalBasis.coe_toBasis]
    rw [specPow, diagOp_basisVec, hAb]
    have h := realPow_natCast (hlam0 k) (n := 1) one_ne_zero
    simp only [Nat.cast_one, pow_one] at h
    rw [h]
  have hSn : ∀ m : ℕ, specPow b lam ((m + 1 : ℕ) : ℂ) = A ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hS1
    | succ m ih =>
      rw [pow_succ, ← ih, ← hS1, ← specPow_add]
      congr 1
      push_cast
      ring
  have htr : LinearMap.trace ℂ W (A ^ (n + 1)) = ((∑ k, lam k ^ (n + 1) : ℝ) : ℂ) := by
    rw [← hSn, ← mul_one (specPow b lam _), specPow, trace_diagOp_mul]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [realPow_natCast (hlam0 k) (Nat.succ_ne_zero n)]
    simp
  have hword : ∀ L : List (Module.End ℂ W),
      interleavedWord b lam (L.map fun Z => ((1 : ℝ), Z)) = (L.map (A * ·)).prod := by
    intro L
    induction L with
    | nil => rfl
    | cons Z L ih =>
      simp only [List.map_cons, interleavedWord, List.prod_cons, ih, Complex.ofReal_one, hS1,
        mul_assoc]
  have hlist : List.ofFn X = X 0 :: List.ofFn fun j : Fin n => X j.succ := List.ofFn_succ
  have hmain := norm_trace_interleavedWord_le b lam n ((List.ofFn X).map fun Z => ((1 : ℝ), Z))
    (by simp) (by
      intro p hp
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hp
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact ⟨zero_le_one, hX j⟩) 1 isNonexpanding_one
  have htrace : LinearMap.trace ℂ W
      (interleavedWord b lam ((List.ofFn X).map fun Z => ((1 : ℝ), Z)) * 1) =
      LinearMap.trace ℂ W (interleavedProd X A) := by
    rw [mul_one, hword, hlist, interleavedProd_eq_prod_map, hlist]
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc (X 0) A, mul_prod_map_mul_eq_prod_map_mul, ← mul_assoc (X 0), mul_assoc A,
      LinearMap.trace_mul_comm]
  rw [htrace, sum_fst_map_one_pair] at hmain
  have hsum : ∑ k, ‖realPow (lam k) ((((List.ofFn X).length : ℝ)) : ℂ)‖ =
      ∑ k, lam k ^ (n + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.length_ofFn, Complex.ofReal_natCast, realPow_natCast (hlam0 k) (Nat.succ_ne_zero n),
      Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (hlam0 k) _)]
  rw [hsum] at hmain
  rw [htr, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨hmain, rfl⟩
end FiniteDimension
section Series
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {I : Type*} (e : I → H)
def matEntry (B : H →L[ℂ] H) (i j : I) : ℂ := inner ℂ (e i) (B (e j))
variable {e}
theorem norm_inner_orthonormal_le (he : Orthonormal ℂ e) (i : I) (v : H) :
    ‖(inner ℂ (e i) v : ℂ)‖ ≤ ‖v‖ :=
  (norm_inner_le_norm _ _).trans (by rw [he.1 i, one_mul])
theorem norm_matEntry_le (he : Orthonormal ℂ e) (B : H →L[ℂ] H) (i j : I) :
    ‖matEntry e B i j‖ ≤ ‖B‖ :=
  (norm_inner_orthonormal_le he i _).trans (by simpa [he.1 j] using B.le_opNorm (e j))
theorem hasSum_matEntry_mul_inner (hexp : ∀ v, HasSum (fun i => (inner ℂ (e i) v : ℂ) • e i) v)
    (B : H →L[ℂ] H) (α : I) (v : H) :
    HasSum (fun γ => matEntry e B α γ * inner ℂ (e γ) v) (inner ℂ (e α) (B v)) := by
  have h := ((innerSL ℂ (e α)).comp B).hasSum (hexp v)
  simpa [matEntry, inner_smul_right, mul_comm] using h
variable (e) (A : H →L[ℂ] H)
def pathTerm : ∀ n : ℕ, (Fin n → H →L[ℂ] H) → I → (Fin n → I × I) → ℂ
  | 0, _, _, _ => 1
  | n + 1, X, α, b => matEntry e (X 0) α (b 0).1 * matEntry e A (b 0).1 (b 0).2 *
      pathTerm n (fun j => X j.succ) (b 0).2 (fun j => b j.succ)
def pathEnd : ∀ n : ℕ, I → (Fin n → I × I) → I
  | 0, α, _ => α
  | n + 1, _, b => pathEnd n (b 0).2 (fun j => b j.succ)
theorem pathEnd_succ (n : ℕ) (α : I) (b : Fin (n + 1) → I × I) :
    pathEnd (n + 1) α b = (b (Fin.last n)).2 := by
  induction n generalizing α with
  | zero => rfl
  | succ n ih =>
    rw [pathEnd, ih]
    simp only [Fin.succ_last]
variable {e A}
theorem norm_pathTerm_le (he : Orthonormal ℂ e) (n : ℕ) (X : Fin n → H →L[ℂ] H)
    (hX : ∀ j, ‖X j‖ ≤ 1) (α : I) (b : Fin n → I × I) :
    ‖pathTerm e A n X α b‖ ≤ ∏ j, ‖matEntry e A (b j).1 (b j).2‖ := by
  induction n generalizing α with
  | zero => simp [pathTerm]
  | succ n ih =>
    rw [pathTerm, Fin.prod_univ_succ, norm_mul, norm_mul]
    have h1 : ‖matEntry e (X 0) α (b 0).1‖ ≤ 1 := (norm_matEntry_le he _ _ _).trans (hX 0)
    exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) h1)
      (ih (fun j => X j.succ) (fun j => hX j.succ) _ (fun j => b j.succ))
      (norm_nonneg _) (norm_nonneg _)
theorem summable_pi_prod {K : Type*} {g : K → ℝ} (hg0 : ∀ p, 0 ≤ g p) (hg : Summable g)
    (n : ℕ) : Summable fun b : Fin n → K => ∏ j, g (b j) := by
  induction n with
  | zero => exact (hasSum_unique _).summable
  | succ n ih =>
    have h := hg.mul_of_nonneg ih (fun p => hg0 p)
      (fun b => Finset.prod_nonneg fun j _ => hg0 _)
    refine ((Fin.consEquiv fun _ => K).summable_iff).1 ?_
    refine h.congr fun x => ?_
    simp [Function.comp, Fin.consEquiv, Fin.prod_univ_succ]
theorem hasSum_pathTerm (he : Orthonormal ℂ e)
    (hexp : ∀ v, HasSum (fun i => (inner ℂ (e i) v : ℂ) • e i) v)
    (hA : Summable fun p : I × I => ‖matEntry e A p.1 p.2‖) (n : ℕ) :
    ∀ (X : Fin n → H →L[ℂ] H), (∀ j, ‖X j‖ ≤ 1) → ∀ (α : I) (v : H),
      HasSum (fun b => pathTerm e A n X α b * inner ℂ (e (pathEnd n α b)) v)
        (inner ℂ (e α) (interleavedProd X A v)) := by
  induction n with
  | zero =>
    intro X _ α v
    have h1 : interleavedProd X A = 1 := by simp [interleavedProd]
    rw [h1]
    simpa [pathTerm, pathEnd] using
      hasSum_unique (fun b : Fin 0 → I × I => pathTerm e A 0 X α b * inner ℂ (e (pathEnd 0 α b)) v)
  | succ n ih =>
    intro X hX α v
    have hX' : ∀ j : Fin n, ‖X j.succ‖ ≤ 1 := fun j => hX j.succ
    set w := interleavedProd (fun j : Fin n => X j.succ) A v with hw
    have hg0 : ∀ p : I × I, 0 ≤ ‖matEntry e A p.1 p.2‖ := fun _ => norm_nonneg _
    have hG := summable_pi_prod hg0 hA n
    have hx0 : ∀ γ, ‖matEntry e (X 0) α γ‖ ≤ 1 := fun γ =>
      (norm_matEntry_le he _ _ _).trans (hX 0)
    let c : I × I → ℂ := fun p =>
      matEntry e (X 0) α p.1 * matEntry e A p.1 p.2 * inner ℂ (e p.2) w
    have hcb : ∀ p, ‖c p‖ ≤ ‖matEntry e A p.1 p.2‖ * ‖w‖ := by
      intro p
      simp only [c, norm_mul]
      exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) (hx0 _))
        (norm_inner_orthonormal_le he _ _) (norm_nonneg _) (norm_nonneg _)
    have hc : Summable c := Summable.of_norm_bounded (hA.mul_right ‖w‖) hcb
    have hcsum : HasSum c (inner ℂ (e α) (X 0 (A w))) := by
      have h1 : ∀ γ, HasSum (fun δ => c (γ, δ))
          (matEntry e (X 0) α γ * inner ℂ (e γ) (A w)) := by
        intro γ
        simpa [c, mul_assoc] using
          (hasSum_matEntry_mul_inner hexp A γ w).mul_left (matEntry e (X 0) α γ)
      have h2 := hc.hasSum.prod_fiberwise h1
      have h3 := hasSum_matEntry_mul_inner hexp (X 0) α (A w)
      rw [← h2.unique h3]
      exact hc.hasSum
    let f : (I × I) × (Fin n → I × I) → ℂ := fun x =>
      (matEntry e (X 0) α x.1.1 * matEntry e A x.1.1 x.1.2) *
        (pathTerm e A n (fun j => X j.succ) x.1.2 x.2 *
          inner ℂ (e (pathEnd n x.1.2 x.2)) v)
    have hfb : ∀ x, ‖f x‖ ≤ ‖matEntry e A x.1.1 x.1.2‖ *
        (∏ j, ‖matEntry e A (x.2 j).1 (x.2 j).2‖) * ‖v‖ := by
      intro x
      simp only [f, norm_mul]
      have h1 := mul_le_of_le_one_left (norm_nonneg (matEntry e A x.1.1 x.1.2)) (hx0 x.1.1)
      have h2 := norm_pathTerm_le he n (fun j => X j.succ) hX' x.1.2 x.2 (A := A)
      have h3 := norm_inner_orthonormal_le he (pathEnd n x.1.2 x.2) v
      calc _ ≤ ‖matEntry e A x.1.1 x.1.2‖ *
            ((∏ j, ‖matEntry e A (x.2 j).1 (x.2 j).2‖) * ‖v‖) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
              (Finset.prod_nonneg fun _ _ => norm_nonneg _)) (by positivity) (norm_nonneg _)
        _ = _ := by ring
    have hf : Summable f := Summable.of_norm_bounded
      ((hA.mul_of_nonneg hG hg0 (fun b => Finset.prod_nonneg fun j _ => hg0 _)).mul_right ‖v‖) hfb
    have hfiber : ∀ p, HasSum (fun b => f (p, b)) (c p) := fun p =>
      (ih (fun j => X j.succ) hX' p.2 v).mul_left
        (matEntry e (X 0) α p.1 * matEntry e A p.1 p.2)
    have hsum := (hf.hasSum.prod_fiberwise hfiber).unique hcsum
    have hfs : HasSum f (inner ℂ (e α) (X 0 (A w))) := hsum ▸ hf.hasSum
    have htarget : interleavedProd X A v = X 0 (A w) := by
      rw [interleavedProd_succ]
      rfl
    rw [htarget]
    refine ((Fin.consEquiv fun _ => I × I).hasSum_iff).1 ?_
    convert hfs using 1
    funext x
    obtain ⟨p, b⟩ := x
    simp only [Function.comp, Fin.consEquiv, Equiv.coe_fn_mk, pathTerm, pathEnd, Fin.cons_zero,
      Fin.cons_succ, f]
    ring
def loopTerm (e : I → H) {s : ℕ} (X : Fin s → H →L[ℂ] H) (A : H →L[ℂ] H)
    (a : Fin s → I × I) : ℂ :=
  ∏ j, matEntry e (X j) (a j).1 (a j).2 * matEntry e A (a j).2 (a (finRotate s j)).1
def loopShift (I : Type*) (s : ℕ) : (Fin s → I × I) ≃ (Fin s → I × I) where
  toFun a j := ((a j).2, (a (finRotate s j)).1)
  invFun b j := ((b ((finRotate s).symm j)).2, (b j).1)
  left_inv a := by
    funext j
    refine Prod.ext ?_ rfl
    change (a (finRotate s ((finRotate s).symm j))).1 = _
    rw [Equiv.apply_symm_apply]
  right_inv b := by
    funext j
    refine Prod.ext rfl ?_
    change (b ((finRotate s).symm (finRotate s j))).2 = _
    rw [Equiv.symm_apply_apply]
theorem pathTerm_eq_prod (n : ℕ) (X : Fin n → H →L[ℂ] H) (c : Fin (n + 1) → I) (b : Fin n → I × I)
    (h : ∀ j, c j.succ = (b j).2) :
    pathTerm e A n X (c 0) b =
      ∏ j, matEntry e (X j) (c j.castSucc) (b j).1 * matEntry e A (b j).1 (b j).2 := by
  induction n with
  | zero => simp [pathTerm]
  | succ n ih =>
    rw [pathTerm, Fin.prod_univ_succ, ← h 0,
      ih (fun j => X j.succ) (fun i => c i.succ) (fun j => b j.succ) (fun j => h j.succ)]
    simp only [Fin.castSucc_zero, Fin.succ_castSucc]
theorem loopTerm_eq_pathTerm {n : ℕ} (X : Fin (n + 1) → H →L[ℂ] H) (a : Fin (n + 1) → I × I) :
    loopTerm e X A a =
      pathTerm e A (n + 1) X ((loopShift I (n + 1) a (Fin.last n)).2) (loopShift I (n + 1) a) := by
  let c : Fin (n + 2) → I := Fin.snoc (α := fun _ => I) (fun j : Fin (n + 1) => (a j).1) (a 0).1
  have hc0 : c 0 = (loopShift I (n + 1) a (Fin.last n)).2 := by
    have h0 : (0 : Fin (n + 2)) = Fin.castSucc 0 := rfl
    have h1 : (loopShift I (n + 1) a (Fin.last n)).2 = (a (finRotate (n + 1) (Fin.last n))).1 := rfl
    rw [h1, finRotate_last, h0]
    simp [c]
  have hcs : ∀ j : Fin (n + 1), c j.castSucc = (a j).1 := fun j => by simp [c]
  have hsucc : ∀ j : Fin (n + 1), c j.succ = (loopShift I (n + 1) a j).2 := by
    intro j
    change c j.succ = (a (finRotate (n + 1) j)).1
    induction j using Fin.lastCases with
    | last => simp [c]
    | cast i =>
      have : finRotate (n + 1) i.castSucc = i.succ := by
        rw [finRotate_apply, Fin.coeSucc_eq_succ]
      rw [this, Fin.succ_castSucc]
      exact hcs _
  rw [← hc0, pathTerm_eq_prod (n + 1) X c _ hsucc]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hcs]
  rfl
theorem hasSum_diag_interleavedProd (he : Orthonormal ℂ e)
    (hexp : ∀ v, HasSum (fun i => (inner ℂ (e i) v : ℂ) • e i) v)
    (hA : Summable fun p : I × I => ‖matEntry e A p.1 p.2‖) {n : ℕ}
    (X : Fin (n + 1) → H →L[ℂ] H) (hX : ∀ j, ‖X j‖ ≤ 1) :
    Summable (fun a => ‖loopTerm e X A a‖) ∧
    Summable (fun α => ‖matEntry e (interleavedProd X A) α α‖) ∧
    HasSum (fun α => matEntry e (interleavedProd X A) α α) (∑' a, loopTerm e X A a) := by
  classical
  let Tc : (Fin (n + 1) → I × I) → ℂ := fun b => pathTerm e A (n + 1) X (b (Fin.last n)).2 b
  have hG := summable_pi_prod (fun p : I × I => norm_nonneg (matEntry e A p.1 p.2)) hA (n + 1)
  have hTn : Summable fun b => ‖Tc b‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun b => norm_pathTerm_le he (n + 1) X hX _ b) hG
  have hTs : Summable Tc := hTn.of_norm
  have hcyc : ∀ a, loopTerm e X A a = Tc (loopShift I (n + 1) a) := fun a =>
    loopTerm_eq_pathTerm X a
  have hnorm : Summable (fun a => ‖loopTerm e X A a‖) := by
    have h := (loopShift I (n + 1)).summable_iff.2 hTn
    exact h.congr fun a => by simp [hcyc]
  have hsumeq : ∑' a, loopTerm e X A a = ∑' b, Tc b := by
    rw [← (loopShift I (n + 1)).tsum_eq Tc]
    exact tsum_congr hcyc
  let D : (Fin (n + 1) → I × I) × I → ℂ := fun x =>
    if (x.1 (Fin.last n)).2 = x.2 then Tc x.1 else 0
  let ψ : (Fin (n + 1) → I × I) → (Fin (n + 1) → I × I) × I := fun b => (b, (b (Fin.last n)).2)
  have hψ : Function.Injective ψ := fun b b' h => congrArg Prod.fst h
  have hoff : ∀ x, x ∉ Set.range ψ → D x = 0 := by
    rintro ⟨b, α⟩ hx
    have hne : (b (Fin.last n)).2 ≠ α := by
      rintro rfl
      exact hx ⟨b, rfl⟩
    simp [D, hne]
  have hDψ : D ∘ ψ = Tc := by
    funext b
    simp [D, ψ]
  have hD : HasSum D (∑' b, Tc b) := by
    refine (hψ.hasSum_iff hoff).1 ?_
    rw [hDψ]
    exact hTs.hasSum
  have hDn : Summable fun x => ‖D x‖ := by
    refine (hψ.summable_iff (f := fun x => ‖D x‖) ?_).1 ?_
    · intro x hx
      simp [hoff x hx]
    · have : (fun x => ‖D x‖) ∘ ψ = fun b => ‖Tc b‖ := by
        funext b
        exact congrArg norm (congrFun hDψ b)
      rw [this]
      exact hTn
  have hD' : HasSum (D ∘ Prod.swap) (∑' b, Tc b) := (Equiv.prodComm I _).hasSum_iff.2 hD
  have hDn' : Summable (fun x : I × (Fin (n + 1) → I × I) => ‖D x.swap‖) :=
    (Equiv.prodComm I _).summable_iff.2 hDn
  have hfib : ∀ α, HasSum (fun b => (D ∘ Prod.swap) (α, b))
      (matEntry e (interleavedProd X A) α α) := by
    intro α
    have h := hasSum_pathTerm he hexp hA (n + 1) X hX α (e α)
    have hterm : (fun b => pathTerm e A (n + 1) X α b * inner ℂ (e (pathEnd (n + 1) α b)) (e α)) =
        fun b => (D ∘ Prod.swap) (α, b) := by
      funext b
      rw [pathEnd_succ, orthonormal_iff_ite.1 he]
      by_cases hb : (b (Fin.last n)).2 = α
      · simp [D, Tc, hb]
      · simp [D, hb]
    rw [hterm] at h
    exact h
  refine ⟨hnorm, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_) hDn'.prod
    rw [← (hfib α).tsum_eq]
    exact norm_tsum_le_tsum_norm (hDn'.prod_factor α)
  · rw [hsumeq]
    exact hD'.prod_fiberwise hfib
end Series
section Compression
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
def compression (L : W →ₗᵢ[ℂ] H) (B : H →L[ℂ] H) : W →L[ℂ] W :=
  (ContinuousLinearMap.adjoint L.toContinuousLinearMap).comp (B.comp L.toContinuousLinearMap)
theorem inner_compression (L : W →ₗᵢ[ℂ] H) (B : H →L[ℂ] H) (x y : W) :
    inner ℂ x (compression L B y) = inner ℂ (L x) (B (L y)) := by
  simp [compression, ContinuousLinearMap.adjoint_inner_right]
theorem norm_compression_le (L : W →ₗᵢ[ℂ] H) (B : H →L[ℂ] H) : ‖compression L B‖ ≤ ‖B‖ := by
  have h1 : ‖L.toContinuousLinearMap‖ ≤ 1 := L.norm_toContinuousLinearMap_le
  have h2 : ‖ContinuousLinearMap.adjoint L.toContinuousLinearMap‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact h1
  calc ‖compression L B‖ ≤ ‖ContinuousLinearMap.adjoint L.toContinuousLinearMap‖ *
        (‖B‖ * ‖L.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖B‖ * 1) := by gcongr
    _ = ‖B‖ := by ring
theorem compression_one (L : W →ₗᵢ[ℂ] H) : compression L 1 = 1 := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [inner_compression]
  simp
theorem isNonexpanding_of_norm_le_one {B : W →L[ℂ] W} (hB : ‖B‖ ≤ 1) :
    IsNonexpanding (B : Module.End ℂ W) := fun x =>
  (B.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
theorem norm_loopTerm_compression_le [FiniteDimensional ℂ W] {ι : Type*} [Fintype ι]
    (d : OrthonormalBasis ι ℂ W) (L : W →ₗᵢ[ℂ] H) (A : H →L[ℂ] H)
    (hsym : ∀ φ ψ : H, inner ℂ φ (A ψ) = inner ℂ (A φ) ψ)
    (hpos : ∀ φ : H, 0 ≤ (inner ℂ φ (A φ) : ℂ).re)
    {n : ℕ} (X : Fin (n + 1) → H →L[ℂ] H) (hX : ∀ j, ‖X j‖ ≤ 1) :
    ‖∑ a, loopTerm d (fun j => compression L (X j)) (compression L A) a‖ ≤
        (∑ a, loopTerm d (fun _ : Fin (n + 1) => 1) (compression L A) a).re ∧
      (∑ a, loopTerm d (fun _ : Fin (n + 1) => 1) (compression L A) a).im = 0 := by
  set A' := compression L A with hA'
  have hexp : ∀ v, HasSum (fun i => (inner ℂ (d i) v : ℂ) • d i) v := by
    intro v
    have h := hasSum_fintype (fun i => (inner ℂ (d i) v : ℂ) • d i)
    rwa [d.sum_repr'] at h
  have hsumm : Summable fun p : ι × ι => ‖matEntry d A' p.1 p.2‖ := (hasSum_fintype _).summable
  have htr : ∀ Y : Fin (n + 1) → W →L[ℂ] W, (∀ j, ‖Y j‖ ≤ 1) →
      LinearMap.trace ℂ W ((interleavedProd Y A' : W →L[ℂ] W) : Module.End ℂ W) =
        ∑ a, loopTerm d Y A' a := by
    intro Y hY
    have h := (hasSum_diag_interleavedProd d.orthonormal hexp hsumm Y hY).2.2
    rw [tsum_fintype] at h
    rw [LinearMap.trace_eq_sum_inner _ d]
    exact (hasSum_fintype _).unique h
  let ρ : (W →L[ℂ] W) →* Module.End ℂ W :=
    (ContinuousLinearMap.toLinearMapRingHom : (W →L[ℂ] W) →+* _).toMonoidHom
  have hρ : ∀ B : W →L[ℂ] W, ρ B = (B : Module.End ℂ W) := fun _ => rfl
  have hX' : ∀ j, ‖compression L (X j)‖ ≤ 1 := fun j => (norm_compression_le L _).trans (hX j)
  have hone : ∀ j : Fin (n + 1), ‖(1 : W →L[ℂ] W)‖ ≤ 1 := fun _ => ContinuousLinearMap.norm_id_le
  have hfin := norm_trace_interleavedProd_le (Nat.succ_pos n) (ρ A')
    (fun j => ρ (compression L (X j)))
    (by
      intro x y
      change inner ℂ (compression L A x) y = inner ℂ x (compression L A y)
      rw [inner_compression, ← inner_conj_symm, inner_compression, ← inner_conj_symm (L x)]
      rw [hsym])
    (fun x => by
      change 0 ≤ (inner ℂ x (compression L A x) : ℂ).re
      rw [inner_compression]
      exact hpos _)
    (fun j => isNonexpanding_of_norm_le_one (hX' j))
  rw [← map_interleavedProd ρ, ← map_pow, ← interleavedProd_one, hρ, hρ, htr _ hX',
    htr _ hone] at hfin
  exact hfin
end Compression
section Truncation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : Type*} {e : I → H}
open Classical in
def finsetIsometry (he : Orthonormal ℂ e) (F : Finset I) : EuclideanSpace ℂ ↥F →ₗᵢ[ℂ] H :=
  ((EuclideanSpace.basisFun ↥F ℂ).toBasis.constr ℂ fun i : ↥F => e i).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun ↥F ℂ).toBasis)
    (by simpa using (EuclideanSpace.basisFun ↥F ℂ).orthonormal)
    (by
      have h : (((EuclideanSpace.basisFun ↥F ℂ).toBasis.constr ℂ fun i : ↥F => e i) ∘
          (EuclideanSpace.basisFun ↥F ℂ).toBasis) = e ∘ Subtype.val := by
        funext i
        simp only [Function.comp, Module.Basis.constr_basis]
      rw [h]
      exact he.comp _ Subtype.val_injective)
open Classical in
theorem finsetIsometry_basisFun (he : Orthonormal ℂ e) (F : Finset I) (i : ↥F) :
    finsetIsometry he F (EuclideanSpace.basisFun ↥F ℂ i) = e i := by
  have h₁ := (EuclideanSpace.basisFun ↥F ℂ).toBasis.constr_basis ℂ (fun i : ↥F => e i) i
  have h₂ : (EuclideanSpace.basisFun ↥F ℂ).toBasis i = EuclideanSpace.basisFun ↥F ℂ i := by
    simp only [OrthonormalBasis.coe_toBasis]
  change ((EuclideanSpace.basisFun ↥F ℂ).toBasis.constr ℂ fun i : ↥F => e i)
    (EuclideanSpace.basisFun ↥F ℂ i) = e i
  rw [← h₂]
  exact h₁
def finsetPairsEmbedding (F : Finset I) (s : ℕ) : (Fin s → ↥F × ↥F) ↪ (Fin s → I × I) where
  toFun a j := ((a j).1.1, (a j).2.1)
  inj' := by
    intro a a' h
    funext j
    have h' := congrFun h j
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
open Classical in
theorem norm_loopTerm_finset_le (he : Orthonormal ℂ e) (A : H →L[ℂ] H)
    (hsym : ∀ φ ψ : H, inner ℂ φ (A ψ) = inner ℂ (A φ) ψ)
    (hpos : ∀ φ : H, 0 ≤ (inner ℂ φ (A φ) : ℂ).re)
    {n : ℕ} (X : Fin (n + 1) → H →L[ℂ] H) (hX : ∀ j, ‖X j‖ ≤ 1) (F : Finset I) :
    ‖∑ a, loopTerm e X A (finsetPairsEmbedding F (n + 1) a)‖ ≤
        (∑ a, loopTerm e (fun _ : Fin (n + 1) => 1) A (finsetPairsEmbedding F (n + 1) a)).re ∧
      (∑ a, loopTerm e (fun _ : Fin (n + 1) => 1) A (finsetPairsEmbedding F (n + 1) a)).im = 0 := by
  set d := EuclideanSpace.basisFun ↥F ℂ with hd
  set L := finsetIsometry he F with hL
  have hmat : ∀ (B : H →L[ℂ] H) (i j : ↥F),
      matEntry d (compression L B) i j = matEntry e B i j := by
    intro B i j
    simp only [matEntry]
    rw [inner_compression, hL, hd, finsetIsometry_basisFun, finsetIsometry_basisFun]
  have hterm : ∀ (Y : Fin (n + 1) → H →L[ℂ] H) (a : Fin (n + 1) → ↥F × ↥F),
      loopTerm d (fun j => compression L (Y j)) (compression L A) a =
        loopTerm e Y A (finsetPairsEmbedding F (n + 1) a) := by
    intro Y a
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hmat, hmat]
    rfl
  have h := norm_loopTerm_compression_le d L A hsym hpos X hX
  have hone : ∀ a : Fin (n + 1) → ↥F × ↥F,
      loopTerm d (fun _ : Fin (n + 1) => (1 : EuclideanSpace ℂ ↥F →L[ℂ] EuclideanSpace ℂ ↥F))
        (compression L A) a = loopTerm e (fun _ => 1) A (finsetPairsEmbedding F (n + 1) a) := by
    intro a
    rw [← hterm]
    simp only [compression_one]
  simp only [hterm, hone] at h
  exact h
theorem tendsto_finsetPairsEmbedding (s : ℕ) :
    Filter.Tendsto (fun F : Finset I => Finset.univ.map (finsetPairsEmbedding F s))
      Filter.atTop Filter.atTop := by
  classical
  refine Filter.tendsto_atTop.2 fun v => ?_
  let F₁ : Finset I := v.biUnion fun a => Finset.univ.biUnion fun j => {(a j).1, (a j).2}
  filter_upwards [Filter.eventually_ge_atTop F₁] with F hF a ha
  have h1 : ∀ j, (a j).1 ∈ F := fun j => hF (by
    simp only [F₁, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨a, ha, j, Or.inl rfl⟩)
  have h2 : ∀ j, (a j).2 ∈ F := fun j => hF (by
    simp only [F₁, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨a, ha, j, Or.inr rfl⟩)
  exact Finset.mem_map.2 ⟨fun j => (⟨(a j).1, h1 j⟩, ⟨(a j).2, h2 j⟩), Finset.mem_univ _, rfl⟩
theorem norm_tsum_loopTerm_le (he : Orthonormal ℂ e) (A : H →L[ℂ] H)
    (hsym : ∀ φ ψ : H, inner ℂ φ (A ψ) = inner ℂ (A φ) ψ)
    (hpos : ∀ φ : H, 0 ≤ (inner ℂ φ (A φ) : ℂ).re)
    {n : ℕ} (X : Fin (n + 1) → H →L[ℂ] H) (hX : ∀ j, ‖X j‖ ≤ 1)
    (hT : Summable (loopTerm e X A))
    (hT₁ : Summable (loopTerm e (fun _ : Fin (n + 1) => 1) A)) :
    ‖∑' a, loopTerm e X A a‖ ≤ (∑' a, loopTerm e (fun _ : Fin (n + 1) => 1) A a).re ∧
      (∑' a, loopTerm e (fun _ : Fin (n + 1) => 1) A a).im = 0 := by
  classical
  have hlim : ∀ {Y : Fin (n + 1) → H →L[ℂ] H}, Summable (loopTerm e Y A) →
      Filter.Tendsto (fun F : Finset I => ∑ a, loopTerm e Y A (finsetPairsEmbedding F (n + 1) a))
        Filter.atTop (nhds (∑' a, loopTerm e Y A a)) := by
    intro Y hY
    have h : Filter.Tendsto (fun w : Finset (Fin (n + 1) → I × I) => ∑ a ∈ w, loopTerm e Y A a)
        Filter.atTop (nhds (∑' a, loopTerm e Y A a)) := by
      simpa [HasSum] using hY.hasSum
    refine (h.comp (tendsto_finsetPairsEmbedding (n + 1))).congr fun F => ?_
    simp [Function.comp, Finset.sum_map]
  have h := hlim hT
  have h₁ := hlim hT₁
  have hb := norm_loopTerm_finset_le he A hsym hpos X hX
  constructor
  · exact le_of_tendsto_of_tendsto' h.norm
      ((Complex.continuous_re.tendsto _).comp h₁) fun F => (hb F).1
  · refine tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp h₁) ?_
    exact tendsto_const_nhds.congr fun F => ((hb F).2).symm
end Truncation
end InterleavedTrace
open SpinHarmonics InterleavedTrace in
theorem contractionTraceBound_holds (hFacts : SpinHarmonics.SeveralVariables.SeveralVariablesFacts) :
    ContractionTraceBound.Statement := by
  intro s hs
  refine ⟨?_, ?_⟩
  · intro W _ _ _ _ A X hA hpos hX
    exact norm_trace_interleavedProd_le hs A X hA (fun x => (hpos x).1)
      (fun j x => ((LinearMap.toContinuousLinearMap (X j)).le_opNorm x).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hX j)))
  · intro J _ _ A X hnn hA hX
    obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
    have hF := hFacts J (fun _ => ⟨0⟩) ⟨0⟩
    have he : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) := hF.1.1
    have hexp : ∀ v : HaarL2 J, HasSum (fun α : PeterWeylIndex J =>
        (inner ℂ (peterWeylVec α) v : ℂ) • peterWeylVec α) v := fun v => (hF.2.1 v).1
    have hser := hasSum_diag_interleavedProd he hexp hA X hX
    have hone : ∀ j : Fin (n + 1), ‖(1 : HaarL2 J →L[ℂ] HaarL2 J)‖ ≤ 1 :=
      fun _ => ContinuousLinearMap.norm_id_le
    have hser₁ := hasSum_diag_interleavedProd he hexp hA
      (fun _ : Fin (n + 1) => (1 : HaarL2 J →L[ℂ] HaarL2 J)) hone
    rw [interleavedProd_one] at hser₁
    have hbound := norm_tsum_loopTerm_le he A hnn.1 (fun φ => (hnn.2 φ).1) X hX
      hser.1.of_norm hser₁.1.of_norm
    have htr : tracePW (interleavedProd X A) = ∑' a, traceExpansionTerm X A a := hser.2.2.tsum_eq
    have htr₁ : tracePW (A ^ (n + 1)) =
        ∑' a, loopTerm peterWeylVec (fun _ : Fin (n + 1) => 1) A a := hser₁.2.2.tsum_eq
    refine ⟨hser.2.1, hser.1, htr, hser₁.2.1, ?_, ?_⟩
    · rw [htr₁, htr]
      exact hbound.1
    · rw [htr₁]
      exact hbound.2
end YangMills.Construction.TransferOperators
