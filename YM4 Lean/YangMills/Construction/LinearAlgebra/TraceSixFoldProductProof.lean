import YangMills.Construction.LinearAlgebra.TraceOfSixFoldProduct
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.TraceBound
open RealPower
section Numbers
theorem rpowPos_eq_rpow {x t : ℝ} (hx : 0 ≤ x) (ht : t ≠ 0) : rpowPos x t = x ^ t := by
  unfold rpowPos
  rcases hx.eq_or_lt with rfl | h
  · simp [Real.zero_rpow ht]
  · rw [if_pos h, Real.rpow_def_of_pos h, mul_comm]
theorem rpowPos_three {x : ℝ} (hx : 0 ≤ x) : rpowPos x 3 = x ^ 3 := by
  rw [rpowPos_eq_rpow hx (by norm_num)]
  exact_mod_cast Real.rpow_natCast x 3
theorem sqrtOf_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : sqrtOf x = √x := by
  unfold sqrtOf
  split_ifs with h
  · simp [h]
  · rw [rpowPos_eq_rpow hx (by norm_num), Real.sqrt_eq_rpow]
theorem cbrtOf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cbrtOf x := by
  unfold cbrtOf
  rw [rpowPos_eq_rpow hx (by norm_num)]
  exact Real.rpow_nonneg hx _
theorem cbrtOf_pow_three {x : ℝ} (hx : 0 ≤ x) : cbrtOf x ^ 3 = x := by
  unfold cbrtOf
  rw [rpowPos_eq_rpow hx (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
theorem mul_mul_le_add_cubes_div_three {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (x ^ 3 + y ^ 3 + z ^ 3) / 3 := by
  have h := mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (z - x)))
  nlinarith [h]
theorem sum_mul_mul_le_of_sum_cubes_eq {ι : Type} [Fintype ι] (x y z : ι → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) (hz : ∀ j, 0 ≤ z j) {a b c : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hxa : ∑ j, x j ^ 3 = a ^ 3) (hyb : ∑ j, y j ^ 3 = b ^ 3)
    (hzc : ∑ j, z j ^ 3 = c ^ 3) : ∑ j, x j * y j * z j ≤ a * b * c := by
  have ha3 : a ^ 3 ≠ 0 := (pow_pos ha 3).ne'
  have hb3 : b ^ 3 ≠ 0 := (pow_pos hb 3).ne'
  have hc3 : c ^ 3 ≠ 0 := (pow_pos hc 3).ne'
  have key : ∀ j, x j * y j * z j ≤
      a * b * c / 3 * (x j ^ 3 / a ^ 3 + y j ^ 3 / b ^ 3 + z j ^ 3 / c ^ 3) := by
    intro j
    have h1 := mul_mul_le_add_cubes_div_three (div_nonneg (hx j) ha.le)
      (div_nonneg (hy j) hb.le) (div_nonneg (hz j) hc.le)
    rw [div_pow, div_pow, div_pow] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_pos (mul_pos ha hb) hc).le
    calc x j * y j * z j = a * b * c * (x j / a * (y j / b) * (z j / c)) := by
          field_simp
      _ ≤ _ := h2
      _ = _ := by ring
  calc ∑ j, x j * y j * z j
      ≤ ∑ j, a * b * c / 3 * (x j ^ 3 / a ^ 3 + y j ^ 3 / b ^ 3 + z j ^ 3 / c ^ 3) :=
        Finset.sum_le_sum fun j _ => key j
    _ = a * b * c / 3 * ((∑ j, x j ^ 3) / a ^ 3 + (∑ j, y j ^ 3) / b ^ 3 +
          (∑ j, z j ^ 3) / c ^ 3) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_div,
          Finset.sum_div, Finset.sum_div]
    _ = a * b * c := by
        rw [hxa, hyb, hzc, div_self ha3, div_self hb3, div_self hc3]
        ring
theorem holder_three_cubes {ι : Type} [Fintype ι] (x y z : ι → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hy : ∀ j, 0 ≤ y j) (hz : ∀ j, 0 ≤ z j) :
    (∑ j, x j * y j * z j) ^ 3 ≤ (∑ j, x j ^ 3) * (∑ j, y j ^ 3) * (∑ j, z j ^ 3) := by
  have eq_zero_of : ∀ f : ι → ℝ, (∀ j, 0 ≤ f j) → ∑ j, f j ^ 3 = 0 → ∀ j, f j = 0 := by
    intro f hf h j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => pow_nonneg (hf j) 3).1 h j
      (Finset.mem_univ j)
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  have sum_nonneg_of : ∀ f : ι → ℝ, (∀ j, 0 ≤ f j) → 0 ≤ ∑ j, f j ^ 3 :=
    fun f hf => Finset.sum_nonneg fun j _ => pow_nonneg (hf j) 3
  by_cases h1 : ∑ j, x j ^ 3 = 0
  · simp [eq_zero_of x hx h1]
  by_cases h2 : ∑ j, y j ^ 3 = 0
  · simp [eq_zero_of y hy h2]
  by_cases h3 : ∑ j, z j ^ 3 = 0
  · simp [eq_zero_of z hz h3]
  have p1 := lt_of_le_of_ne (sum_nonneg_of x hx) (Ne.symm h1)
  have p2 := lt_of_le_of_ne (sum_nonneg_of y hy) (Ne.symm h2)
  have p3 := lt_of_le_of_ne (sum_nonneg_of z hz) (Ne.symm h3)
  have c1 := cbrtOf_pow_three p1.le
  have c2 := cbrtOf_pow_three p2.le
  have c3 := cbrtOf_pow_three p3.le
  have pos_of : ∀ t : ℝ, 0 < t → 0 < cbrtOf t := by
    intro t ht
    unfold cbrtOf
    rw [rpowPos_eq_rpow ht.le (by norm_num)]
    exact Real.rpow_pos_of_pos ht _
  have hle := sum_mul_mul_le_of_sum_cubes_eq x y z hx hy hz (pos_of _ p1) (pos_of _ p2)
    (pos_of _ p3) c1.symm c2.symm c3.symm
  have h0 : 0 ≤ ∑ j, x j * y j * z j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hx j) (hy j)) (hz j)
  calc (∑ j, x j * y j * z j) ^ 3
      ≤ (cbrtOf (∑ j, x j ^ 3) * cbrtOf (∑ j, y j ^ 3) * cbrtOf (∑ j, z j ^ 3)) ^ 3 :=
        pow_le_pow_left₀ h0 hle 3
    _ = _ := by rw [mul_pow, mul_pow, c1, c2, c3]
theorem sum_sqrt_weighted_cube_le {ι : Type} [Fintype ι] (w : ι → ι → ℝ) (σ : ι → ℝ) {b : ℝ}
    (hw : ∀ j l, 0 ≤ w j l) (hσ : ∀ l, 0 ≤ σ l) (hb : 0 ≤ b)
    (hrow : ∀ j, ∑ l, w j l ≤ b ^ 2) (hcol : ∀ l, ∑ j, w j l ≤ b ^ 2) :
    ∑ j, (√(∑ l, w j l * σ l ^ 2)) ^ 3 ≤ b ^ 3 * ∑ l, σ l ^ 3 := by
  have hτ : ∀ j, 0 ≤ ∑ l, w j l * σ l ^ 3 :=
    fun j => Finset.sum_nonneg fun l _ => mul_nonneg (hw j l) (pow_nonneg (hσ l) 3)
  have hS : ∀ j, 0 ≤ ∑ l, w j l * σ l ^ 2 :=
    fun j => Finset.sum_nonneg fun l _ => mul_nonneg (hw j l) (sq_nonneg _)
  have each : ∀ j, (√(∑ l, w j l * σ l ^ 2)) ^ 3 ≤ b * ∑ l, w j l * σ l ^ 3 := by
    intro j
    have c : ∀ l, cbrtOf (w j l) ^ 3 = w j l := fun l => cbrtOf_pow_three (hw j l)
    have c0 : ∀ l, 0 ≤ cbrtOf (w j l) := fun l => cbrtOf_nonneg (hw j l)
    have hol := holder_three_cubes (fun l => cbrtOf (w j l))
      (fun l => cbrtOf (w j l) * σ l) (fun l => cbrtOf (w j l) * σ l) c0
      (fun l => mul_nonneg (c0 l) (hσ l)) (fun l => mul_nonneg (c0 l) (hσ l))
    have e1 : ∀ l, cbrtOf (w j l) * (cbrtOf (w j l) * σ l) * (cbrtOf (w j l) * σ l) =
        w j l * σ l ^ 2 := by
      intro l
      calc _ = cbrtOf (w j l) ^ 3 * σ l ^ 2 := by ring
        _ = _ := by rw [c l]
    have e2 : ∀ l, (cbrtOf (w j l) * σ l) ^ 3 = w j l * σ l ^ 3 := by
      intro l
      rw [mul_pow, c l]
    simp only [e1, e2, c] at hol
    have hsq : ((√(∑ l, w j l * σ l ^ 2)) ^ 3) ^ 2 ≤ (b * ∑ l, w j l * σ l ^ 3) ^ 2 := by
      calc ((√(∑ l, w j l * σ l ^ 2)) ^ 3) ^ 2
          = ((√(∑ l, w j l * σ l ^ 2)) ^ 2) ^ 3 := by ring
        _ = (∑ l, w j l * σ l ^ 2) ^ 3 := by rw [Real.sq_sqrt (hS j)]
        _ ≤ (∑ l, w j l) * (∑ l, w j l * σ l ^ 3) * (∑ l, w j l * σ l ^ 3) := hol
        _ ≤ b ^ 2 * (∑ l, w j l * σ l ^ 3) * (∑ l, w j l * σ l ^ 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hrow j) (hτ j)) (hτ j)
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (pow_nonneg (Real.sqrt_nonneg _) 3) (mul_nonneg hb (hτ j))
      (by norm_num)).1 hsq
  calc ∑ j, (√(∑ l, w j l * σ l ^ 2)) ^ 3
      ≤ ∑ j, b * ∑ l, w j l * σ l ^ 3 := Finset.sum_le_sum fun j _ => each j
    _ = b * ∑ l, σ l ^ 3 * ∑ j, w j l := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum, mul_comm]
    _ ≤ b * ∑ l, σ l ^ 3 * b ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (hcol l) (pow_nonneg (hσ l) 3)) hb
    _ = _ := by
        rw [← Finset.sum_mul]
        ring
end Numbers
section Characteristic
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
theorem charpoly_roots_eq_of_basis_eigen {N : ℕ} (e : Module.Basis (Fin N) ℂ V)
    (X : Module.End ℂ V) (l : Fin N → ℂ) (h : ∀ j, X (e j) = l j • e j) :
    (LinearMap.charpoly X).roots = Finset.univ.val.map l := by
  have hm : LinearMap.toMatrix e e X = Matrix.diagonal l := by
    ext i j
    rw [LinearMap.toMatrix_apply, h j, map_smul, Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [← LinearMap.charpoly_toMatrix X e, hm, Matrix.charpoly_diagonal]
  have hp : (∏ i, (Polynomial.X - Polynomial.C (l i))) =
      ((Finset.univ.val.map l).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]
end Characteristic
section Inner
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
theorem inner_apply_apply_eq (M : Module.End ℂ E) (x y : E) :
    inner ℂ (M x) (M y) = inner ℂ x ((LinearMap.adjoint M * M) y) := by
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
theorem exists_singularValueDecomposition (M : Module.End ℂ E) {N : ℕ}
    (hN : Module.finrank ℂ E = N) :
    ∃ (v u : OrthonormalBasis (Fin N) ℂ E) (r : Fin N → ℝ), (∀ j, 0 ≤ r j) ∧
      (∀ j, M (v j) = (r j : ℂ) • u j) ∧
      (∀ j, (LinearMap.adjoint M * M) (v j) = ((r j ^ 2 : ℝ) : ℂ) • v j) := by
  classical
  have hT : (LinearMap.adjoint M * M).IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  let v := hT.eigenvectorBasis hN
  let μ := hT.eigenvalues hN
  have hv : ∀ j, (LinearMap.adjoint M * M) (v j) = (μ j : ℂ) • v j :=
    fun j => hT.apply_eigenvectorBasis hN j
  have hin : ∀ l j, inner ℂ (M (v l)) (M (v j)) = (μ j : ℂ) * (if l = j then 1 else 0) := by
    intro l j
    rw [inner_apply_apply_eq, hv, inner_smul_right, OrthonormalBasis.inner_eq_ite]
  let r : Fin N → ℝ := fun j => ‖M (v j)‖
  have hμ : ∀ j, μ j = r j ^ 2 := by
    intro j
    have h := congrArg Complex.re (hin j j)
    rw [if_pos rfl, mul_one, Complex.ofReal_re] at h
    rw [← h]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let u₀ : Fin N → E := fun j => (((r j)⁻¹ : ℝ) : ℂ) • M (v j)
  let s : Set (Fin N) := {j | r j ≠ 0}
  have ho : Orthonormal ℂ (s.domRestrict u₀) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : r i ≠ 0 := hi
    show inner ℂ (u₀ i) (u₀ j) = _
    simp only [u₀, inner_smul_left, inner_smul_right, hin, Subtype.mk.injEq, Complex.conj_ofReal]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hμ]
      push_cast
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast hi'
      field_simp
    · simp [hij]
  have hcard : Module.finrank ℂ E = Fintype.card (Fin N) := by simp [hN]
  obtain ⟨u, hu⟩ := ho.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨v, u, r, fun j => norm_nonneg _, ?_, ?_⟩
  · intro j
    by_cases hj : r j = 0
    · have : M (v j) = 0 := norm_eq_zero.1 hj
      simp [this, hj]
    · rw [hu j hj]
      simp only [u₀]
      have : (r j : ℂ) ≠ 0 := by exact_mod_cast hj
      rw [smul_smul]
      push_cast
      rw [mul_inv_cancel₀ this, one_smul]
  · intro j
    rw [hv, hμ]
omit [FiniteDimensional ℂ E] in
theorem inner_apply_of_svd {N : ℕ} (v u : OrthonormalBasis (Fin N) ℂ E) (r : Fin N → ℝ)
    (M : Module.End ℂ E) (h : ∀ j, M (v j) = (r j : ℂ) • u j) (l : Fin N) (y : E) :
    inner ℂ (u l) (M y) = (r l : ℂ) * inner ℂ (v l) y := by
  classical
  conv_lhs => rw [← v.sum_repr' y]
  simp only [map_sum, map_smul, h, inner_sum, inner_smul_right, OrthonormalBasis.inner_eq_ite]
  simp [mul_comm]
theorem norm_adjoint_apply_le (B : Module.End ℂ E) {b : ℝ} (hb : 0 ≤ b)
    (hB : ∀ x, ‖B x‖ ≤ b * ‖x‖) (x : E) : ‖LinearMap.adjoint B x‖ ≤ b * ‖x‖ := by
  set y := LinearMap.adjoint B x with hy
  have h1 : ‖y‖ * ‖y‖ ≤ (b * ‖x‖) * ‖y‖ := by
    have e : ‖inner ℂ y y‖ = ‖inner ℂ x (B y)‖ := by
      rw [hy, LinearMap.adjoint_inner_left]
    calc ‖y‖ * ‖y‖ = ‖inner ℂ y y‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖inner ℂ x (B y)‖ := e
      _ ≤ ‖x‖ * ‖B y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (b * ‖y‖) := mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
      _ = _ := by ring
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hb (norm_nonneg _)
  · exact le_of_mul_le_mul_right h1 h0
theorem sum_norm_cube_le {N : ℕ} (φ ψ ψ' : OrthonormalBasis (Fin N) ℂ E) (r : Fin N → ℝ)
    (hr : ∀ l, 0 ≤ r l) (A B : Module.End ℂ E) {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ l y, inner ℂ (ψ' l) (A y) = (r l : ℂ) * inner ℂ (ψ l) y)
    (hB : ∀ x, ‖B x‖ ≤ b * ‖x‖) :
    ∑ j, ‖A (B (φ j))‖ ^ 3 ≤ b ^ 3 * ∑ l, r l ^ 3 := by
  let w : Fin N → Fin N → ℝ := fun j l => ‖inner ℂ (ψ l) (B (φ j))‖ ^ 2
  have hnorm : ∀ j, ‖A (B (φ j))‖ = √(∑ l, w j l * r l ^ 2) := by
    intro j
    have h := ψ'.sum_sq_norm_inner_right (A (B (φ j)))
    have e : ∑ l, w j l * r l ^ 2 = ‖A (B (φ j))‖ ^ 2 := by
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hA, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_comm]
    rw [e, Real.sqrt_sq (norm_nonneg _)]
  have unit_norm : ∀ (e : OrthonormalBasis (Fin N) ℂ E) j, ‖e j‖ = 1 :=
    fun e j => e.orthonormal.1 j
  have hrow : ∀ j, ∑ l, w j l ≤ b ^ 2 := by
    intro j
    rw [show ∑ l, w j l = ‖B (φ j)‖ ^ 2 from ψ.sum_sq_norm_inner_right _]
    have := hB (φ j)
    rw [unit_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hcol : ∀ l, ∑ j, w j l ≤ b ^ 2 := by
    intro l
    have e : ∑ j, w j l = ‖LinearMap.adjoint B (ψ l)‖ ^ 2 := by
      rw [← φ.sum_sq_norm_inner_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w]
      rw [← LinearMap.adjoint_inner_left, norm_inner_symm]
    rw [e]
    have := norm_adjoint_apply_le B hb hB (ψ l)
    rw [unit_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  simp only [hnorm]
  exact sum_sqrt_weighted_cube_le w r (fun j l => sq_nonneg _) hr hb hrow hcol
theorem norm_trace_six_le {N : ℕ} (A₁ A₂ A₃ B₁ B₂ B₃ : Module.End ℂ E)
    (v₁ u₁ v₂ u₂ v₃ u₃ : OrthonormalBasis (Fin N) ℂ E) (r₁ r₂ r₃ : Fin N → ℝ)
    (hr₁ : ∀ j, 0 ≤ r₁ j) (hr₂ : ∀ j, 0 ≤ r₂ j) (hr₃ : ∀ j, 0 ≤ r₃ j)
    (hA₁ : ∀ j, A₁ (v₁ j) = (r₁ j : ℂ) • u₁ j) (hA₂ : ∀ j, A₂ (v₂ j) = (r₂ j : ℂ) • u₂ j)
    (hA₃ : ∀ j, A₃ (v₃ j) = (r₃ j : ℂ) • u₃ j) {b₁ b₂ b₃ ρ₁ ρ₂ ρ₃ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hB₁ : ∀ x, ‖B₁ x‖ ≤ b₁ * ‖x‖) (hB₂ : ∀ x, ‖B₂ x‖ ≤ b₂ * ‖x‖)
    (hB₃ : ∀ x, ‖B₃ x‖ ≤ b₃ * ‖x‖) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₃ : 0 ≤ ρ₃)
    (hs₁ : ∑ j, r₁ j ^ 3 = ρ₁ ^ 3) (hs₂ : ∑ j, r₂ j ^ 3 = ρ₂ ^ 3)
    (hs₃ : ∑ j, r₃ j ^ 3 = ρ₃ ^ 3) :
    ‖LinearMap.trace ℂ E (A₁ * B₁ * A₂ * B₂ * A₃ * B₃)‖ ≤ ρ₁ * ρ₂ * ρ₃ * b₁ * b₂ * b₃ := by
  let g : Fin N → E := fun j => LinearMap.adjoint A₂ (LinearMap.adjoint B₁ (v₁ j))
  let h : Fin N → E := fun j => A₃ (B₃ (u₁ j))
  have ht : LinearMap.trace ℂ E (A₁ * B₁ * A₂ * B₂ * A₃ * B₃) =
      ∑ j, (r₁ j : ℂ) * inner ℂ (g j) (B₂ (h j)) := by
    have e : A₁ * B₁ * A₂ * B₂ * A₃ * B₃ = A₁ * (B₁ * A₂ * B₂ * A₃ * B₃) := by
      simp only [mul_assoc]
    rw [e, LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ v₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Module.End.mul_apply, g, h, hA₁, map_smul, inner_smul_right,
      LinearMap.adjoint_inner_left]
  have hsum₂ : ∑ j, ‖g j‖ ^ 3 ≤ b₁ ^ 3 * ∑ l, r₂ l ^ 3 := by
    refine sum_norm_cube_le v₁ u₂ v₂ r₂ hr₂ (LinearMap.adjoint A₂) (LinearMap.adjoint B₁) hb₁
      ?_ (norm_adjoint_apply_le B₁ hb₁ hB₁)
    intro l y
    rw [LinearMap.adjoint_inner_right, hA₂, inner_smul_left, Complex.conj_ofReal]
  have hsum₃ : ∑ j, ‖h j‖ ^ 3 ≤ b₃ ^ 3 * ∑ l, r₃ l ^ 3 :=
    sum_norm_cube_le u₁ v₃ u₃ r₃ hr₃ A₃ B₃ hb₃ (inner_apply_of_svd v₃ u₃ r₃ A₃ hA₃) hB₃
  have hterm : ∀ j, ‖(r₁ j : ℂ) * inner ℂ (g j) (B₂ (h j))‖ ≤ b₂ * (r₁ j * ‖g j‖ * ‖h j‖) := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr₁ j)]
    calc r₁ j * ‖inner ℂ (g j) (B₂ (h j))‖ ≤ r₁ j * (‖g j‖ * (b₂ * ‖h j‖)) :=
          mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hB₂ _) (norm_nonneg _))) (hr₁ j)
      _ = _ := by ring
  have hhol := holder_three_cubes r₁ (fun j => ‖g j‖) (fun j => ‖h j‖) hr₁
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hP : 0 ≤ ρ₁ * ρ₂ * ρ₃ * b₁ * b₃ := by positivity
  have hsum0 : 0 ≤ ∑ j, r₁ j * ‖g j‖ * ‖h j‖ := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hr₁ j) (norm_nonneg _)) (norm_nonneg _)
  have hcube : (∑ j, r₁ j * ‖g j‖ * ‖h j‖) ^ 3 ≤ (ρ₁ * ρ₂ * ρ₃ * b₁ * b₃) ^ 3 := by
    calc _ ≤ (∑ j, r₁ j ^ 3) * (∑ j, ‖g j‖ ^ 3) * (∑ j, ‖h j‖ ^ 3) := hhol
      _ ≤ (∑ j, r₁ j ^ 3) * (b₁ ^ 3 * ∑ l, r₂ l ^ 3) * (b₃ ^ 3 * ∑ l, r₃ l ^ 3) := by
          have n₁ : 0 ≤ ∑ j, r₁ j ^ 3 := Finset.sum_nonneg fun j _ => pow_nonneg (hr₁ j) 3
          have n₂ : 0 ≤ ∑ j, ‖g j‖ ^ 3 := Finset.sum_nonneg fun j _ => by positivity
          have n₃ : 0 ≤ b₁ ^ 3 * ∑ l, r₂ l ^ 3 := mul_nonneg (pow_nonneg hb₁ 3)
            (Finset.sum_nonneg fun j _ => pow_nonneg (hr₂ j) 3)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hsum₂ n₁) hsum₃
            (Finset.sum_nonneg fun j _ => by positivity) (mul_nonneg n₁ n₃)
      _ = _ := by
          rw [hs₁, hs₂, hs₃]
          ring
  have hle : ∑ j, r₁ j * ‖g j‖ * ‖h j‖ ≤ ρ₁ * ρ₂ * ρ₃ * b₁ * b₃ :=
    (pow_le_pow_iff_left₀ hsum0 hP (by norm_num)).1 hcube
  rw [ht]
  calc ‖∑ j, (r₁ j : ℂ) * inner ℂ (g j) (B₂ (h j))‖
      ≤ ∑ j, ‖(r₁ j : ℂ) * inner ℂ (g j) (B₂ (h j))‖ := norm_sum_le _ _
    _ ≤ ∑ j, b₂ * (r₁ j * ‖g j‖ * ‖h j‖) := Finset.sum_le_sum fun j _ => hterm j
    _ = b₂ * ∑ j, r₁ j * ‖g j‖ * ‖h j‖ := by rw [Finset.mul_sum]
    _ ≤ b₂ * (ρ₁ * ρ₂ * ρ₃ * b₁ * b₃) := mul_le_mul_of_nonneg_left hle hb₂
    _ = _ := by ring
end Inner
section Spectral
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {K : E → E → ℂ}
theorem formNorm_eq_norm (hK : ∀ v w, K v w = inner ℂ v w) (v : E) : formNorm K v = ‖v‖ := by
  unfold formNorm
  have e : (K v v).re = ‖v‖ ^ 2 := by
    rw [hK]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [e, sqrtOf_eq_sqrt (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
variable [FiniteDimensional ℂ E]
theorem exists_opNormE_bound (hK : ∀ v w, K v w = inner ℂ v w) (M : Module.End ℂ E) :
    ∃ b : ℝ, 0 ≤ b ∧ opNormE K M = b ∧ ∀ x, ‖M x‖ ≤ b * ‖x‖ := by
  let C := LinearMap.toContinuousLinearMap M
  have hC : ∀ x, ‖M x‖ ≤ ‖C‖ * ‖x‖ := fun x => C.le_opNorm x
  have hS : opNormE K M = sSup ((fun v => ((‖M v‖ : ℝ) : EReal)) '' {v | ‖v‖ ≤ 1}) := by
    unfold opNormE
    simp only [formNorm_eq_norm hK]
  set S := sSup ((fun v => ((‖M v‖ : ℝ) : EReal)) '' {v : E | ‖v‖ ≤ 1}) with hSdef
  have hmem : ∀ v : E, ‖v‖ ≤ 1 → ((‖M v‖ : ℝ) : EReal) ≤ S :=
    fun v hv => le_sSup ⟨v, hv, rfl⟩
  have h0 : (0 : EReal) ≤ S := by
    have := hmem 0 (by simp)
    simpa using this
  have hc : S ≤ ((‖C‖ : ℝ) : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨v, hv, rfl⟩
    refine EReal.coe_le_coe_iff.2 ((hC v).trans ?_)
    exact mul_le_of_le_one_right (norm_nonneg _) hv
  have htop : S ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc
  have hbot : S ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  have hcoe : ((S.toReal : ℝ) : EReal) = S := EReal.coe_toReal htop hbot
  refine ⟨S.toReal, ?_, by rw [hS, hcoe], ?_⟩
  · exact EReal.coe_nonneg.1 (hcoe ▸ h0)
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hy : ‖(((‖x‖)⁻¹ : ℝ) : ℂ) • x‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have h1 := hmem _ hy
    rw [← hcoe, EReal.coe_le_coe_iff, map_smul, norm_smul, Complex.norm_real, norm_inv,
      norm_norm] at h1
    calc ‖M x‖ = ‖x‖ * ((‖x‖)⁻¹ * ‖M x‖) := by field_simp
      _ ≤ ‖x‖ * S.toReal := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := mul_comm _ _
theorem isAdjointOf_iff (hK : ∀ v w, K v w = inner ℂ v w) (M M' : Module.End ℂ E) :
    IsAdjointOf K M M' ↔ M' = LinearMap.adjoint M := by
  rw [LinearMap.eq_adjoint_iff]
  simp only [IsAdjointOf, hK]
theorem hasUniqueAdjoint_of_inner (hK : ∀ v w, K v w = inner ℂ v w) (M : Module.End ℂ E) :
    HasUniqueAdjoint K M :=
  ⟨LinearMap.adjoint M, (isAdjointOf_iff hK M _).2 rfl,
    fun _ h => (isAdjointOf_iff hK M _).1 h⟩
theorem adjointOf_eq (hK : ∀ v w, K v w = inner ℂ v w) (M : Module.End ℂ E) :
    adjointOf K M = LinearMap.adjoint M :=
  (isAdjointOf_iff hK M _).1
    (Classical.epsilon_spec (p := IsAdjointOf K M) ⟨_, (isAdjointOf_iff hK M _).2 rfl⟩)
theorem spectral_data_of_basis (hK : ∀ v w, K v w = inner ℂ v w) (M : Module.End ℂ E) {N : ℕ}
    (e : Module.Basis (Fin N) ℂ E) (r : Fin N → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hT : ∀ j, (LinearMap.adjoint M * M) (e j) = ((r j ^ 2 : ℝ) : ℂ) • e j) :
    adjointMulEigenvalues K M = Finset.univ.val.map (fun j => ((r j ^ 2 : ℝ) : ℂ)) ∧
      singularValuesOf K M = Finset.univ.val.map r ∧
      sumCubesSingularValues K M = ∑ j, r j ^ 3 := by
  have h1 : adjointMulEigenvalues K M =
      Finset.univ.val.map (fun j => ((r j ^ 2 : ℝ) : ℂ)) := by
    unfold adjointMulEigenvalues
    rw [adjointOf_eq hK]
    exact charpoly_roots_eq_of_basis_eigen e _ _ hT
  have h2 : singularValuesOf K M = Finset.univ.val.map r := by
    unfold singularValuesOf
    rw [h1, Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp, Complex.ofReal_re]
    rw [sqrtOf_eq_sqrt (sq_nonneg _), Real.sqrt_sq (hr j)]
  refine ⟨h1, h2, ?_⟩
  unfold sumCubesSingularValues
  rw [h2, Multiset.map_map]
  have : ∀ j ∈ (Finset.univ : Finset (Fin N)).val, ((fun x => rpowPos x 3) ∘ r) j = r j ^ 3 :=
    fun j _ => rpowPos_three (hr j)
  rw [Multiset.map_congr rfl this]
  rfl
theorem exists_svd_spectral_data (hK : ∀ v w, K v w = inner ℂ v w) (M : Module.End ℂ E)
    {N : ℕ} (hN : Module.finrank ℂ E = N) :
    ∃ (v u : OrthonormalBasis (Fin N) ℂ E) (r : Fin N → ℝ), (∀ j, 0 ≤ r j) ∧
      (∀ j, M (v j) = (r j : ℂ) • u j) ∧
      adjointMulEigenvalues K M = Finset.univ.val.map (fun j => ((r j ^ 2 : ℝ) : ℂ)) ∧
      singularValuesOf K M = Finset.univ.val.map r ∧
      sumCubesSingularValues K M = ∑ j, r j ^ 3 := by
  obtain ⟨v, u, r, hr, hM, hT⟩ := exists_singularValueDecomposition M hN
  refine ⟨v, u, r, hr, hM, spectral_data_of_basis hK M v.toBasis r hr ?_⟩
  simpa using hT
theorem spectral_quantities_defined (hK : ∀ v w, K v w = inner ℂ v w) {N : ℕ}
    (hN : Module.finrank ℂ E = N) (M : Module.End ℂ E) :
    HasUniqueAdjoint K M ∧
      (∃ r : ℝ, opNormE K M = r) ∧
      (∀ μ ∈ adjointMulEigenvalues K M, μ.im = 0 ∧ 0 ≤ μ.re) ∧
      HasSingularValues K M ∧
      Multiset.card (singularValuesOf K M) = N ∧
      HasSchattenThreeNorm K M := by
  obtain ⟨v, u, r, hr, hM, he, hs, hsum⟩ := exists_svd_spectral_data hK M hN
  obtain ⟨b, -, hb, -⟩ := exists_opNormE_bound hK M
  have heig : ∀ μ ∈ adjointMulEigenvalues K M, μ.im = 0 ∧ 0 ≤ μ.re := by
    intro μ hμ
    rw [he, Multiset.mem_map] at hμ
    obtain ⟨j, -, rfl⟩ := hμ
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact sq_nonneg _⟩
  have hform : HasSingularValues K M := ⟨hasUniqueAdjoint_of_inner hK M, heig⟩
  refine ⟨hasUniqueAdjoint_of_inner hK M, ⟨b, hb⟩, heig, hform, ?_, hform, ?_⟩
  · rw [hs]
    simp
  · rw [hsum]
    exact Finset.sum_nonneg fun j _ => pow_nonneg (hr j) 3
theorem singularValues_of_diagonal (hK : ∀ v w, K v w = inner ℂ v w) {N : ℕ}
    (M : Module.End ℂ E) (φ : Fin N → E) (a : Fin N → ℂ) (hφ : IsOrthonormalBasisOf K φ)
    (hM : ∀ j, M (φ j) = a j • φ j) :
    singularValuesOf K M = Finset.univ.val.map (fun j => ‖a j‖) ∧
      rpowPos (schattenThreeNorm K M) 3 = ∑ j, rpowPos ‖a j‖ 3 := by
  obtain ⟨⟨e, rfl⟩, hone, hzero⟩ := hφ
  simp only [hK] at hone hzero
  have hin : ∀ l j, inner ℂ (e l) (e j) = if l = j then (1 : ℂ) else 0 := by
    intro l j
    by_cases h : l = j
    · subst h
      rw [if_pos rfl]
      exact hone l
    · rw [if_neg h]
      exact hzero l j h
  have hT : ∀ j, (LinearMap.adjoint M * M) (e j) = ((‖a j‖ ^ 2 : ℝ) : ℂ) • e j := by
    intro j
    refine InnerProductSpace.ext_inner_left_basis e fun l => ?_
    rw [← inner_apply_apply_eq, hM, hM, inner_smul_left, inner_smul_right, inner_smul_right, hin]
    by_cases h : l = j
    · subst h
      simp only [if_true, mul_one]
      rw [Complex.conj_mul']
      push_cast
      rfl
    · simp [h]
  obtain ⟨-, hs, hsum⟩ :=
    spectral_data_of_basis hK M e (fun j => ‖a j‖) (fun _ => norm_nonneg _) hT
  have h0 : 0 ≤ sumCubesSingularValues K M := by
    rw [hsum]
    exact Finset.sum_nonneg fun j _ => by positivity
  refine ⟨hs, ?_⟩
  unfold schattenThreeNorm
  rw [rpowPos_three (cbrtOf_nonneg h0), cbrtOf_pow_three h0, hsum]
  exact Finset.sum_congr rfl fun j _ => (rpowPos_three (norm_nonneg _)).symm
theorem norm_trace_six_le_schatten (hK : ∀ v w, K v w = inner ℂ v w) {N : ℕ}
    (hN : Module.finrank ℂ E = N) (A₁ A₂ A₃ B₁ B₂ B₃ : Module.End ℂ E) :
    ((‖LinearMap.trace ℂ E (A₁ * B₁ * A₂ * B₂ * A₃ * B₃)‖ : ℝ) : EReal) ≤
        ((schattenThreeNorm K A₁ * schattenThreeNorm K A₂ * schattenThreeNorm K A₃ : ℝ) :
          EReal) * opNormE K B₁ * opNormE K B₂ * opNormE K B₃ ∧
    ((schattenThreeNorm K A₁ * schattenThreeNorm K A₂ * schattenThreeNorm K A₃ : ℝ) : EReal) *
          opNormE K B₁ * opNormE K B₂ * opNormE K B₃ ≤
        ((1 / 3 * (rpowPos (schattenThreeNorm K A₁) 3 + rpowPos (schattenThreeNorm K A₂) 3 +
            rpowPos (schattenThreeNorm K A₃) 3) : ℝ) : EReal) *
          opNormE K B₁ * opNormE K B₂ * opNormE K B₃ := by
  obtain ⟨v₁, u₁, r₁, hr₁, hA₁, -, -, hs₁⟩ := exists_svd_spectral_data hK A₁ hN
  obtain ⟨v₂, u₂, r₂, hr₂, hA₂, -, -, hs₂⟩ := exists_svd_spectral_data hK A₂ hN
  obtain ⟨v₃, u₃, r₃, hr₃, hA₃, -, -, hs₃⟩ := exists_svd_spectral_data hK A₃ hN
  obtain ⟨b₁, hb₁, ho₁, hB₁⟩ := exists_opNormE_bound hK B₁
  obtain ⟨b₂, hb₂, ho₂, hB₂⟩ := exists_opNormE_bound hK B₂
  obtain ⟨b₃, hb₃, ho₃, hB₃⟩ := exists_opNormE_bound hK B₃
  have norm_data : ∀ (A : Module.End ℂ E) (r : Fin N → ℝ), (∀ j, 0 ≤ r j) →
      sumCubesSingularValues K A = ∑ j, r j ^ 3 →
      0 ≤ schattenThreeNorm K A ∧ ∑ j, r j ^ 3 = schattenThreeNorm K A ^ 3 := by
    intro A r hr hs
    have h0 : 0 ≤ sumCubesSingularValues K A := by
      rw [hs]
      exact Finset.sum_nonneg fun j _ => pow_nonneg (hr j) 3
    exact ⟨cbrtOf_nonneg h0, by rw [← hs]; exact (cbrtOf_pow_three h0).symm⟩
  obtain ⟨hρ₁, hc₁⟩ := norm_data A₁ r₁ hr₁ hs₁
  obtain ⟨hρ₂, hc₂⟩ := norm_data A₂ r₂ hr₂ hs₂
  obtain ⟨hρ₃, hc₃⟩ := norm_data A₃ r₃ hr₃ hs₃
  have hmain := norm_trace_six_le A₁ A₂ A₃ B₁ B₂ B₃ v₁ u₁ v₂ u₂ v₃ u₃ r₁ r₂ r₃ hr₁ hr₂ hr₃
    hA₁ hA₂ hA₃ hb₁ hb₂ hb₃ hB₁ hB₂ hB₃ hρ₁ hρ₂ hρ₃ hc₁ hc₂ hc₃
  rw [ho₁, ho₂, ho₃, rpowPos_three hρ₁, rpowPos_three hρ₂, rpowPos_three hρ₃]
  constructor
  · exact_mod_cast hmain
  · have ham := mul_mul_le_add_cubes_div_three hρ₁ hρ₂ hρ₃
    have hbs : 0 ≤ b₁ * b₂ * b₃ := by positivity
    have hfin : schattenThreeNorm K A₁ * schattenThreeNorm K A₂ * schattenThreeNorm K A₃ *
          b₁ * b₂ * b₃ ≤
        1 / 3 * (schattenThreeNorm K A₁ ^ 3 + schattenThreeNorm K A₂ ^ 3 +
          schattenThreeNorm K A₃ ^ 3) * b₁ * b₂ * b₃ := by
      have := mul_le_mul_of_nonneg_right ham hbs
      linarith
    exact_mod_cast hfin
end Spectral
section Assembly
variable {V : Type} [AddCommGroup V] [Module ℂ V]
@[instance_reducible]
def innerCoreOfForm (K : V → V → ℂ) (h : IsHermitianForm K) :
    InnerProductSpace.Core ℂ V where
  inner := K
  conj_inner_symm x y := (h.conj_symm y x).symm
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · subst hx
      have : K 0 0 = 0 := (h.linear_right 0).mk'.map_zero
      simp [this]
    · exact (Complex.pos_iff.1 (h.pos x hx)).1.le
  add_left x y z := by
    rw [h.conj_symm z (x + y), (h.linear_right z).map_add, map_add,
      ← h.conj_symm z x, ← h.conj_symm z y]
  smul_left x y c := by
    rw [h.conj_symm y (c • x), (h.linear_right y).map_smul, smul_eq_mul, map_mul,
      ← h.conj_symm y x]
  definite x hx := by
    by_contra hne
    have := h.pos x hne
    rw [hx] at this
    exact lt_irrefl _ this
end Assembly
theorem traceSixFoldProductBound_holds : TraceSixFoldProductBound := by
  intro N _ V _ _ _ hN K hK
  let c := innerCoreOfForm K hK
  let _ : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hi : ∀ v w, K v w = inner ℂ v w := fun _ _ => rfl
  exact ⟨fun M => spectral_quantities_defined hi hN M,
    fun M φ a hφ hM => singularValues_of_diagonal hi M φ a hφ hM,
    fun A₁ A₂ A₃ B₁ B₂ B₃ => norm_trace_six_le_schatten hi hN A₁ A₂ A₃ B₁ B₂ B₃⟩
end YangMills.Construction.TraceBound
