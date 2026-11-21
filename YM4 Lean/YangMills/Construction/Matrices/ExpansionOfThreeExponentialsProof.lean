import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Matrices.TripleExponentialExpansion
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Matrix.Norms.L2Operator Topology Nat
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace TripleExp
theorem norm_matExp_sub_quadratic_le (X : ComplexMatrix2) :
    ‖matExp X - 1 - X - (1 / 2 : ℂ) • (X * X)‖ ≤ Real.exp ‖X‖ - 1 - ‖X‖ - ‖X‖ ^ 2 / 2 := by
  have hSer : HasSum (fun n : ℕ => ((n ! : ℂ)⁻¹) • X ^ n) (matExp X) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have hReal : HasSum (fun n : ℕ => ‖X‖ ^ n / (n ! : ℝ)) (Real.exp ‖X‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ‖X‖
  have hSer3 := (hasSum_nat_add_iff' 3).2 hSer
  have hReal3 := (hasSum_nat_add_iff' 3).2 hReal
  have hbd := hSer3.norm_le_of_bounded hReal3 (fun n => by
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by positivity))
  have eqM : matExp X - ∑ i ∈ Finset.range 3, ((i ! : ℂ)⁻¹) • X ^ i =
      matExp X - 1 - X - (1 / 2 : ℂ) • (X * X) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    simp [pow_two]
    abel
  have eqR : Real.exp ‖X‖ - ∑ i ∈ Finset.range 3, ‖X‖ ^ i / (i ! : ℝ) =
      Real.exp ‖X‖ - 1 - ‖X‖ - ‖X‖ ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
    ring
  rwa [eqM, eqR] at hbd
theorem norm_mul_sub_quadratic_le {A₁ A₂ A₃ B₁ B₂ B₃ : ComplexMatrix2} {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (h₁ : ‖A₁‖ ≤ a₁) (h₂ : ‖A₂‖ ≤ a₂) (h₃ : ‖A₃‖ ≤ a₃)
    (k₁ : ‖B₁‖ ≤ b₁) (k₂ : ‖B₂‖ ≤ b₂) (k₃ : ‖B₃‖ ≤ b₃) :
    ‖(1 + A₁ + A₂ + A₃) * (1 + B₁ + B₂ + B₃) - 1 - (A₁ + B₁) - (A₂ + A₁ * B₁ + B₂)‖ ≤
      (1 + a₁ + a₂ + a₃) * (1 + b₁ + b₂ + b₃) - 1 - (a₁ + b₁) - (a₂ + a₁ * b₁ + b₂) := by
  have expand : (1 + A₁ + A₂ + A₃) * (1 + B₁ + B₂ + B₃) - 1 - (A₁ + B₁) - (A₂ + A₁ * B₁ + B₂) =
      A₃ + B₃ + A₃ * B₁ + A₃ * B₂ + A₃ * B₃ + A₁ * B₃ + A₂ * B₃ + A₁ * B₂ + A₂ * B₁ + A₂ * B₂ := by
    noncomm_ring
  have mulBound : ∀ {P Q : ComplexMatrix2} {p q : ℝ}, ‖P‖ ≤ p → ‖Q‖ ≤ q → ‖P * Q‖ ≤ p * q :=
    fun hp hq =>
      (norm_mul_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp))
  rw [expand]
  have m₁ := mulBound h₃ k₁
  have m₂ := mulBound h₃ k₂
  have m₃ := mulBound h₃ k₃
  have m₄ := mulBound h₁ k₃
  have m₅ := mulBound h₂ k₃
  have m₆ := mulBound h₁ k₂
  have m₇ := mulBound h₂ k₁
  have m₈ := mulBound h₂ k₂
  have triangle : ‖A₃ + B₃ + A₃ * B₁ + A₃ * B₂ + A₃ * B₃ + A₁ * B₃ + A₂ * B₃ + A₁ * B₂ + A₂ * B₁ +
      A₂ * B₂‖ ≤ ‖A₃‖ + ‖B₃‖ + ‖A₃ * B₁‖ + ‖A₃ * B₂‖ + ‖A₃ * B₃‖ + ‖A₁ * B₃‖ + ‖A₂ * B₃‖ +
        ‖A₁ * B₂‖ + ‖A₂ * B₁‖ + ‖A₂ * B₂‖ := by
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    exact norm_add_le _ _
  have expandReal : (1 + a₁ + a₂ + a₃) * (1 + b₁ + b₂ + b₃) - 1 - (a₁ + b₁) - (a₂ + a₁ * b₁ + b₂) =
      a₃ + b₃ + a₃ * b₁ + a₃ * b₂ + a₃ * b₃ + a₁ * b₃ + a₂ * b₃ + a₁ * b₂ + a₂ * b₁ + a₂ * b₂ := by
    ring
  rw [expandReal]
  linarith
theorem norm_half_smul_mul_self_le (X : ComplexMatrix2) :
    ‖(1 / 2 : ℂ) • (X * X)‖ ≤ ‖X‖ ^ 2 / 2 := by
  rw [norm_smul]
  have hsq : ‖X * X‖ ≤ ‖X‖ * ‖X‖ := norm_mul_le _ _
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  nlinarith
def linearPart (X Y Z : ComplexMatrix2) : ComplexMatrix2 := X + Y + Z
def quadraticPart (X Y Z : ComplexMatrix2) : ComplexMatrix2 :=
  ((1 / 2 : ℂ) • (X * X) + X * Y + (1 / 2 : ℂ) • (Y * Y)) + (X + Y) * Z + (1 / 2 : ℂ) • (Z * Z)
theorem norm_triple_matExp_sub_quadratic_le (X Y Z : ComplexMatrix2) :
    ‖matExp X * matExp Y * matExp Z - 1 - linearPart X Y Z - quadraticPart X Y Z‖ ≤
      Real.exp (‖X‖ + ‖Y‖ + ‖Z‖) - 1 - (‖X‖ + ‖Y‖ + ‖Z‖) - (‖X‖ + ‖Y‖ + ‖Z‖) ^ 2 / 2 := by
  set RX := matExp X - 1 - X - (1 / 2 : ℂ) • (X * X) with hRX
  set RY := matExp Y - 1 - Y - (1 / 2 : ℂ) • (Y * Y) with hRY
  set RZ := matExp Z - 1 - Z - (1 / 2 : ℂ) • (Z * Z) with hRZ
  have eX : matExp X = 1 + X + (1 / 2 : ℂ) • (X * X) + RX := by rw [hRX]; abel
  have eY : matExp Y = 1 + Y + (1 / 2 : ℂ) • (Y * Y) + RY := by rw [hRY]; abel
  have eZ : matExp Z = 1 + Z + (1 / 2 : ℂ) • (Z * Z) + RZ := by rw [hRZ]; abel
  have first := norm_mul_sub_quadratic_le (le_refl ‖X‖) (norm_half_smul_mul_self_le X)
    (norm_matExp_sub_quadratic_le X) (le_refl ‖Y‖) (norm_half_smul_mul_self_le Y)
    (norm_matExp_sub_quadratic_le Y)
  rw [← hRX, ← hRY, ← eX, ← eY] at first
  set C := matExp X * matExp Y - 1 - (X + Y) -
    ((1 / 2 : ℂ) • (X * X) + X * Y + (1 / 2 : ℂ) • (Y * Y)) with hC
  have ePair : matExp X * matExp Y =
      1 + (X + Y) + ((1 / 2 : ℂ) • (X * X) + X * Y + (1 / 2 : ℂ) • (Y * Y)) + C := by
    rw [hC]; abel
  have nSum : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
  have nQuad : ‖(1 / 2 : ℂ) • (X * X) + X * Y + (1 / 2 : ℂ) • (Y * Y)‖ ≤
      ‖X‖ ^ 2 / 2 + ‖X‖ * ‖Y‖ + ‖Y‖ ^ 2 / 2 :=
    (norm_add₃_le).trans (add_le_add (add_le_add (norm_half_smul_mul_self_le X) (norm_mul_le _ _))
      (norm_half_smul_mul_self_le Y))
  have second := norm_mul_sub_quadratic_le nSum nQuad first (le_refl ‖Z‖)
    (norm_half_smul_mul_self_le Z) (norm_matExp_sub_quadratic_le Z)
  rw [← hRZ, ← eZ, ← ePair] at second
  have hExp : Real.exp (‖X‖ + ‖Y‖ + ‖Z‖) = Real.exp ‖X‖ * Real.exp ‖Y‖ * Real.exp ‖Z‖ := by
    rw [Real.exp_add, Real.exp_add]
  have unfoldLhs : matExp X * matExp Y * matExp Z - 1 - linearPart X Y Z - quadraticPart X Y Z =
      matExp X * matExp Y * matExp Z - 1 - (X + Y + Z) -
        (((1 / 2 : ℂ) • (X * X) + X * Y + (1 / 2 : ℂ) • (Y * Y)) + (X + Y) * Z +
          (1 / 2 : ℂ) • (Z * Z)) := rfl
  rw [unfoldLhs, hExp]
  refine second.trans (le_of_eq ?_)
  ring
theorem norm_logSeries_one_add_sub_quadratic_le {T : ComplexMatrix2} (hT : ‖T‖ ≤ 1 / 2) :
    ‖logSeries (1 + T) - T + (1 / 2 : ℂ) • (T * T)‖ ≤ 2 / 3 * ‖T‖ ^ 3 := by
  set t := ‖T‖ with ht
  have t0 : 0 ≤ t := norm_nonneg _
  have t1 : t < 1 := by linarith
  let term : ℕ → ComplexMatrix2 := fun n => ((n + 1 : ℂ)⁻¹) • (-T) ^ (n + 1)
  have normTerm : ∀ n, ‖term n‖ ≤ ((n : ℝ) + 1)⁻¹ * t ^ (n + 1) := by
    intro n
    have hc : ‖((n + 1 : ℂ)⁻¹)‖ = ((n : ℝ) + 1)⁻¹ := by
      rw [norm_inv]
      congr 1
      exact_mod_cast Complex.norm_natCast (n + 1)
    simp only [term]
    rw [norm_smul, hc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_pow_le _ _).trans (le_of_eq ?_)
    rw [norm_neg]
  have hsum : Summable term := by
    refine Summable.of_norm_bounded (g := fun n => t * t ^ n)
      ((summable_geometric_of_lt_one t0 t1).mul_left t) fun n => ?_
    refine (normTerm n).trans ?_
    rw [pow_succ']
    have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    have hp : 0 ≤ t * t ^ n := by positivity
    nlinarith
  have hlog : logSeries (1 + T) = -∑' n, term n := by
    simp only [logSeries, term]
    congr 1
    refine tsum_congr fun n => ?_
    congr 2
    abel
  have hTail := (hasSum_nat_add_iff' 2).2 hsum.hasSum
  have hGeom : HasSum (fun n : ℕ => t ^ 3 / 3 * t ^ n) (t ^ 3 / 3 * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one t0 t1).mul_left _
  have hbd := hTail.norm_le_of_bounded hGeom (fun n => by
    refine (normTerm (n + 2)).trans ?_
    have : (((n + 2 : ℕ) : ℝ) + 1)⁻¹ ≤ 1 / 3 := by
      rw [one_div]
      refine inv_anti₀ (by norm_num) ?_
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have he : t ^ (n + 2 + 1) = t ^ 3 * t ^ n := by ring
    rw [he]
    have hp : 0 ≤ t ^ 3 * t ^ n := by positivity
    nlinarith)
  have firstTwo : ∑ i ∈ Finset.range 2, term i = -T + (1 / 2 : ℂ) • (T * T) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, term]
    norm_num [pow_two]
  have rewrite : logSeries (1 + T) - T + (1 / 2 : ℂ) • (T * T) =
      -(∑' n, term n - ∑ i ∈ Finset.range 2, term i) := by
    rw [hlog, firstTwo]
    abel
  rw [rewrite, norm_neg]
  refine hbd.trans ?_
  have : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hp : 0 ≤ t ^ 3 := by positivity
  nlinarith
theorem quadraticPart_sub_half_sq (X Y Z : ComplexMatrix2) :
    quadraticPart X Y Z - (1 / 2 : ℂ) • (linearPart X Y Z * linearPart X Y Z) =
      (1 / 2 : ℂ) • (⁅X, Y⁆ + ⁅X, Z⁆ + ⁅Y, Z⁆) := by
  simp only [quadraticPart, linearPart, Ring.lie_def, mul_add, add_mul, smul_add, smul_sub]
  module
theorem log_remainder_decomp (T₁ T₂ T₃ L : ComplexMatrix2) :
    L - T₁ - (T₂ - (1 / 2 : ℂ) • (T₁ * T₁)) =
      T₃ + (L - (T₁ + (T₂ + T₃)) + (1 / 2 : ℂ) • ((T₁ + (T₂ + T₃)) * (T₁ + (T₂ + T₃)))) -
        (1 / 2 : ℂ) • (T₁ * (T₂ + T₃) + (T₂ + T₃) * (T₁ + (T₂ + T₃))) := by
  simp only [mul_add, add_mul, smul_add]
  module
theorem triple_bounds {X Y Z : ComplexMatrix2} (hX : ‖X‖ ≤ 1 / 12) (hY : ‖Y‖ ≤ 1 / 12)
    (hZ : ‖Z‖ ≤ 1 / 12) :
    ‖matExp X * matExp Y * matExp Z - 1‖ ≤ 1 / 2 ∧
    ‖logSeries (matExp X * matExp Y * matExp Z) - (X + Y + Z) -
        (1 / 2 : ℂ) • (⁅X, Y⁆ + ⁅X, Z⁆ + ⁅Y, Z⁆)‖ ≤
      9 * (‖X‖ + ‖Y‖ + ‖Z‖) ^ 3 := by
  set s := ‖X‖ + ‖Y‖ + ‖Z‖ with hs
  have s0 : 0 ≤ s := by positivity
  set T₁ := linearPart X Y Z with hT₁
  set T₂ := quadraticPart X Y Z with hT₂
  set T₃ := matExp X * matExp Y * matExp Z - 1 - T₁ - T₂ with hT₃
  have n₁ : ‖T₁‖ ≤ s := norm_add₃_le
  have n₂ : ‖T₂‖ ≤ s ^ 2 / 2 := by
    have a₁ := norm_half_smul_mul_self_le X
    have a₂ := norm_half_smul_mul_self_le Y
    have a₃ := norm_half_smul_mul_self_le Z
    have a₄ : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le _ _
    have a₅ : ‖(X + Y) * Z‖ ≤ (‖X‖ + ‖Y‖) * ‖Z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _))
    have b₁ : ‖T₂‖ ≤ ‖(1 / 2 : ℂ) • (X * X)‖ + ‖X * Y‖ + ‖(1 / 2 : ℂ) • (Y * Y)‖ +
        ‖(X + Y) * Z‖ + ‖(1 / 2 : ℂ) • (Z * Z)‖ := by
      refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
      exact norm_add₃_le
    rw [hs]
    nlinarith
  have hexp := Real.exp_bound (x := s) (by rw [abs_of_nonneg s0]; linarith) (n := 3) (by norm_num)
  have hexp' : Real.exp s - 1 - s - s ^ 2 / 2 ≤ 2 / 9 * s ^ 3 := by
    have e : ∑ m ∈ Finset.range 3, s ^ m / (m.factorial : ℝ) = 1 + s + s ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    rw [e, abs_of_nonneg s0] at hexp
    have := (abs_le.mp hexp).2
    norm_num [Nat.factorial] at this
    linarith
  have n₃ : ‖T₃‖ ≤ 2 / 9 * s ^ 3 := (norm_triple_matExp_sub_quadratic_le X Y Z).trans hexp'
  have s2 : s ^ 2 ≤ s / 4 := by nlinarith
  have s3 : s ^ 3 ≤ s ^ 2 / 4 := by nlinarith [sq_nonneg s]
  set W := T₂ + T₃ with hW
  have nW : ‖W‖ ≤ s ^ 2 := by
    have := norm_add_le T₂ T₃
    nlinarith
  have eT : matExp X * matExp Y * matExp Z = 1 + (T₁ + W) := by
    rw [hW, hT₃]; abel
  set T := T₁ + W with hT
  have nT : ‖T‖ ≤ 2 * s := by
    have := norm_add_le T₁ W
    nlinarith
  have nT' : ‖T‖ ≤ 1 / 2 := by linarith
  refine ⟨?_, ?_⟩
  · rw [eT]
    simpa using nT'
  · have hL := norm_logSeries_one_add_sub_quadratic_le nT'
    rw [← quadraticPart_sub_half_sq, ← hT₂, ← hT₁, eT]
    have hid := log_remainder_decomp T₁ T₂ T₃ (logSeries (1 + T))
    have hlin : X + Y + Z = T₁ := rfl
    rw [hlin, hid]
    have c₁ : ‖T‖ ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) nT 3
    have m₁ : ‖T₁ * W‖ ≤ s * s ^ 2 :=
      (norm_mul_le _ _).trans (mul_le_mul n₁ nW (norm_nonneg _) s0)
    have m₂ : ‖W * T‖ ≤ s ^ 2 * (2 * s) :=
      (norm_mul_le _ _).trans (mul_le_mul nW nT (norm_nonneg _) (by positivity))
    have m₃ : ‖(1 / 2 : ℂ) • (T₁ * W + W * T)‖ ≤ 1 / 2 * (s * s ^ 2 + s ^ 2 * (2 * s)) := by
      rw [norm_smul]
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [hhalf]
      have := norm_add_le (T₁ * W) (W * T)
      linarith
    have tri := norm_sub_le (T₃ + (logSeries (1 + T) - T + (1 / 2 : ℂ) • (T * T)))
      ((1 / 2 : ℂ) • (T₁ * W + W * T))
    have tri' := norm_add_le T₃ (logSeries (1 + T) - T + (1 / 2 : ℂ) • (T * T))
    have hp : 0 ≤ s ^ 3 := by positivity
    nlinarith
theorem isHolomorphicVia_logSeries_triple (hlog : AnalyticOnNhd ℂ logSeries logBall)
    (hmem : ∀ V : Fin 3 → ComplexMatrix2, (∀ i, operatorNorm (V i) < tripleExpRadius) →
      matExp (V 0) * matExp (V 1) * matExp (V 2) ∈ logBall) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (E := Fin 3 → ComplexMatrix2)
      (Coordinates.ComplexCoordinates.productEquiv
        fun _ : Fin 3 => Coordinates.ComplexCoordinates.Component.matrix)
      Coordinates.ComplexCoordinates.matrixEquiv {V | ∀ i, operatorNorm (V i) < tripleExpRadius}
      fun V => logSeries (matExp (V 0) * matExp (V 1) * matExp (V 2)) := by
  let c : Fin 3 → Coordinates.ComplexCoordinates.Component :=
    fun _ => Coordinates.ComplexCoordinates.Component.matrix
  let e : (Fin 3 → ComplexMatrix2) ≃
      Coordinates.ComplexCoordinates (Coordinates.ComplexCoordinates.productDim c) :=
    Coordinates.ComplexCoordinates.productEquiv c
  let Ls : Coordinates.ComplexCoordinates (Coordinates.ComplexCoordinates.productDim c) →ₗ[ℂ]
      (Fin 3 → ComplexMatrix2) :=
    { toFun := e.symm
      map_add' := fun z w => by funext i; ext a b; rfl
      map_smul' := fun r z => by funext i; ext a b; rfl }
  let Lc : ComplexMatrix2 →ₗ[ℂ] Coordinates.ComplexCoordinates 4 :=
    { toFun := Coordinates.ComplexCoordinates.matrixEquiv
      map_add' := fun A B => by funext k; rfl
      map_smul' := fun r A => by funext k; rfl }
  have cs : Continuous e.symm := Ls.continuous_of_finiteDimensional
  let U : Set (Fin 3 → ComplexMatrix2) := {V | ∀ i, operatorNorm (V i) < tripleExpRadius}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt ((continuous_norm).comp (continuous_apply i)) continuous_const
  have hImg : IsOpen (e '' U) := by
    rw [Equiv.image_eq_preimage_symm]
    exact hU.preimage cs
  let g : (Fin 3 → ComplexMatrix2) → ComplexMatrix2 :=
    fun V => logSeries (matExp (V 0) * matExp (V 1) * matExp (V 2))
  have expDiff : ∀ (i : Fin 3) (V : Fin 3 → ComplexMatrix2),
      DifferentiableAt ℂ (fun V : Fin 3 → ComplexMatrix2 => matExp (V i)) V := fun i V =>
    ((NormedSpace.exp_analytic (𝕂 := ℂ) (V i)).differentiableAt).comp V
      (differentiableAt_apply i V)
  have hg : ∀ V ∈ U, DifferentiableAt ℂ g V := fun V hV => by
    have hProd : DifferentiableAt ℂ
        (fun V : Fin 3 → ComplexMatrix2 => matExp (V 0) * matExp (V 1) * matExp (V 2)) V :=
      ((expDiff 0 V).mul (expDiff 1 V)).mul (expDiff 2 V)
    exact DifferentiableAt.comp (g := logSeries) V (hlog _ (hmem V hV)).differentiableAt hProd
  let F : Coordinates.ComplexCoordinates (Coordinates.ComplexCoordinates.productDim c) →
      Coordinates.ComplexCoordinates 4 :=
    Coordinates.ComplexCoordinates.matrixEquiv ∘ g ∘ e.symm
  have hF : ∀ z ∈ e '' U, DifferentiableAt ℂ F z := by
    intro z hz
    have hz' : e.symm z ∈ U := by
      rw [Equiv.image_eq_preimage_symm] at hz
      exact hz
    have d₁ : DifferentiableAt ℂ e.symm z :=
      (LinearMap.toContinuousLinearMap Ls).differentiableAt
    have d₂ : DifferentiableAt ℂ Coordinates.ComplexCoordinates.matrixEquiv (g (e.symm z)) :=
      (LinearMap.toContinuousLinearMap Lc).differentiableAt
    exact d₂.comp z ((hg _ hz').comp z d₁)
  refine ⟨hImg, fun z hz => (hF z hz).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have line : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have near : ∀ᶠ ζ in 𝓝 (0 : ℂ),
      a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ e '' U := by
    have h0 : (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 ∈
        e '' U := by
      simp only [zero_smul, add_zero]
      exact ha
    exact line.continuousAt.eventually_mem (hImg.mem_nhds h0)
  filter_upwards [near] with ζ hζ
  have d : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := F) ζ (hF _ hζ) d
end TripleExp
open TripleExp in
theorem tripleExpExpansionStatement_holds (hElem : PeriodicLattice.ElementaryStepFacts) :
    TripleExpExpansionStatement := by
  obtain ⟨⟨hSquare, -⟩, -, hSeries, hGroup, -⟩ :=
    hElem 13 1 1 0 ⟨⟨6, rfl⟩, le_rfl⟩ one_pos zero_lt_one
  have hr : tripleExpRadius = 1 / 12 := rfl
  refine ⟨fun X Y Z hX hY hZ => ?_, ?_⟩
  · rw [hr] at hX hY hZ
    obtain ⟨b₁, b₂⟩ := triple_bounds hX hY hZ
    refine ⟨b₁, b₂, ?_⟩
    rintro ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    have hgen : ∀ D ∈ hermitianTraceless, matExp (Complex.I • D) ∈ specialUnitary :=
      fun D hD => (hSquare D hD).2.2.2.2.2.2
    have hu : matExp (Complex.I • A) * matExp (Complex.I • B) * matExp (Complex.I • C) ∈
        specialUnitary :=
      specialUnitary.mul_mem (specialUnitary.mul_mem (hgen A hA) (hgen B hB)) (hgen C hC)
    obtain ⟨c₁, c₂, -⟩ := hGroup.1 _ hu (lt_of_le_of_lt b₁ (by norm_num))
    exact ⟨c₁, c₂⟩
  · refine isHolomorphicVia_logSeries_triple hSeries.1 fun V hV => ?_
    have hb : ∀ i, ‖V i‖ ≤ 1 / 12 := fun i => by
      have := hV i
      rw [hr] at this
      exact this.le
    have := (triple_bounds (hb 0) (hb 1) (hb 2)).1
    show operatorNorm _ < 1
    exact lt_of_le_of_lt this (by norm_num)
end YangMills.Construction.Matrices.ComplexMatrix2
end
