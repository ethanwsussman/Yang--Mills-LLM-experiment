import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPointProof
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace SmallChartBounds
open BlockAverages BlockLines BlockWeights PlaquetteExpansion
variable {F : BlockFrame}
theorem twice_baseDistance_ends_le (hL : 2 ≤ F.blockSide) {j : ℕ} (hj : j < F.top) (x : F.Site j) (i : Fin 4)
    (p : F.Site 0) (h : baseDistance x p ≤ F.blockSide ^ F.top) :
    2 * baseDistance x p ≤ 3 * F.blockSide ^ F.top ∧
      2 * baseDistance (x + unitStep j i) p ≤ 3 * F.blockSide ^ F.top := by
  have h1 := baseDistance_add_unitStep_le hj.le x i p
  have h2 : 2 * F.blockSide ^ j ≤ F.blockSide ^ F.top := by
    have e : F.blockSide ^ F.top = F.blockSide ^ j * F.blockSide ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : F.blockSide ≤ F.blockSide ^ (F.top - j) := by
      have : F.top - j ≠ 0 := by omega
      exact Nat.le_self_pow this _
    rw [e]
    have : 2 ≤ F.blockSide ^ (F.top - j) := by omega
    nlinarith [Nat.zero_le (F.blockSide ^ j)]
  omega
theorem pow_four_le_of_weight {Ω v ρ : ℝ} (hρ : 0 < ρ) (hΩ : ρ ≤ Ω) (hv : 0 ≤ v) :
    v ^ 4 ≤ (ρ⁻¹) ^ 4 * (Ω * v) ^ 4 := by
  have h1 : v ≤ ρ⁻¹ * (Ω * v) := by
    rw [← mul_assoc]
    have : 1 ≤ ρ⁻¹ * Ω := by
      rw [inv_mul_eq_div, one_le_div hρ]
      exact hΩ
    exact le_mul_of_one_le_left hv this
  calc v ^ 4 ≤ (ρ⁻¹ * (Ω * v)) ^ 4 := pow_le_pow_left₀ hv h1 4
    _ = _ := by rw [mul_pow]
theorem sq_le_of_weight {Ω v ρ : ℝ} (hρ : 0 < ρ) (hΩ : ρ ≤ Ω) (hv : 0 ≤ v) :
    v ^ 2 ≤ (ρ⁻¹) ^ 2 * (Ω * v) ^ 2 := by
  have h1 : v ≤ ρ⁻¹ * (Ω * v) := by
    rw [← mul_assoc]
    have : 1 ≤ ρ⁻¹ * Ω := by
      rw [inv_mul_eq_div, one_le_div hρ]
      exact hΩ
    exact le_mul_of_one_le_left hv this
  calc v ^ 2 ≤ (ρ⁻¹ * (Ω * v)) ^ 2 := pow_le_pow_left₀ hv h1 2
    _ = _ := by rw [mul_pow]
theorem inv_rpow_neg_pow {x θ : ℝ} (hx : 0 < x) (n : ℕ) : ((x ^ (-θ))⁻¹) ^ n = x ^ ((n : ℝ) * θ) := by
  rw [Real.rpow_neg hx.le, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  ring
theorem mul_rpow_le_sixteen_mul {θ : ℝ} (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) {x : ℝ} (hx : 0 < x) (a : ℝ) (ha : 1 ≤ a)
    (ha8 : a ≤ 16) (hk : (4 : ℝ) * θ ≤ 1) : (a * x) ^ (((4 : ℕ) : ℝ) * θ) ≤ 16 * x ^ (4 * θ) := by
  have e : (((4 : ℕ) : ℝ)) * θ = 4 * θ := by norm_num
  rw [e, Real.mul_rpow (by linarith) hx.le]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc a ^ (4 * θ) ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha hk
    _ = a := Real.rpow_one a
    _ ≤ 16 := ha8
theorem localQuarticSum_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8)
    (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) {j : ℕ} (hj : j < F.top) {r B : ℝ}
    (hr1 : 1 ≤ r) (hr : r ≤ (F.blockSide : ℝ) ^ (F.top - j)) (hB : 0 ≤ B)
    (hW : ∑ b ∈ innerBonds (cellsNearPoint S p) j,
      (shiftedWeight F θ p j b.1 * ‖levelCoordinate R U j b.1 b.2‖) ^ 4 ≤ B ^ 4) :
    localQuarticSum S R U j p r ≤ (2 * B) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ) := by
  classical
  have hLpos : 0 < F.blockSide := by omega
  have hLj : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  have hN : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ j * (F.blockSide : ℝ) ^ (F.top - j) := by
    rw [← pow_add]
    congr 1
    omega
  set x := r / (F.blockSide : ℝ) ^ (F.top - j) with hx
  have hx0 : 0 < x := by positivity
  set ρ := (5 * x) ^ (-θ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hbig : ((ρ⁻¹) ^ 4) ≤ 16 * x ^ (4 * θ) := by
    rw [hρ, inv_rpow_neg_pow (by positivity) 4]
    exact mul_rpow_le_sixteen_mul hθ hθ8 hx0 5 (by norm_num) (by norm_num) (by linarith)
  have hsub : ∀ b ∈ (innerBonds S j).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j),
      b ∈ innerBonds (cellsNearPoint S p) j ∧ ρ ≤ shiftedWeight F θ p j b.1 := by
    intro b hb
    obtain ⟨hbS, hd⟩ := Finset.mem_filter.1 hb
    refine ⟨?_, ?_⟩
    · have h1 : (baseDistance b.1 p : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by
        rw [hN]
        calc (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j := hd
          _ ≤ (F.blockSide : ℝ) ^ (F.top - j) * (F.blockSide : ℝ) ^ j := mul_le_mul_of_nonneg_right hr hLj.le
          _ = _ := mul_comm _ _
      have h2 : baseDistance b.1 p ≤ F.blockSide ^ F.top := by exact_mod_cast h1
      obtain ⟨a1, a2⟩ := twice_baseDistance_ends_le hL hj b.1 b.2 p h2
      exact mem_innerBonds_cellsNearPoint hodd hj.le hbS p a1 a2
    · have h3 : (baseDistance b.1 p : ℝ) + 4 * (F.blockSide : ℝ) ^ j ≤ 5 * r * (F.blockSide : ℝ) ^ j := by nlinarith
      have := rpow_le_shiftedWeight hLpos hθ.le p b.1 h3
      have e : 5 * r * (F.blockSide : ℝ) ^ j / (F.blockSide : ℝ) ^ F.top = 5 * x := by
        rw [hN, hx]
        field_simp
      rw [e] at this
      exact this
  unfold localQuarticSum
  calc _ ≤ ∑ b ∈ (innerBonds S j).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j),
        (ρ⁻¹) ^ 4 * (shiftedWeight F θ p j b.1 * ‖levelCoordinate R U j b.1 b.2‖) ^ 4 := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h1 := pow_four_le_of_weight hρ0 (hsub b hb).2 (norm_nonneg (levelCoordinate R U j b.1 b.2))
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) ?_ 4) h1
        exact norm_coe_sub_one_le_norm_unitQuaternionLog _
    _ = (ρ⁻¹) ^ 4 * ∑ b ∈ (innerBonds S j).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ j),
        (shiftedWeight F θ p j b.1 * ‖levelCoordinate R U j b.1 b.2‖) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (ρ⁻¹) ^ 4 * B ^ 4 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => (hsub b hb).1)
          fun _ _ _ => by positivity) hW
    _ ≤ (16 * x ^ (4 * θ)) * B ^ 4 := mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = _ := by ring
theorem norm_plaquette_im_le (R : F.FieldChain) (U : ChainChart F) (q : F.Site 0 × Fin 4 × Fin 4)
    (h1 : ‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ≤ 1) (h2 : ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ≤ 1)
    (h3 : ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ≤ 1) (h4 : ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ≤ 1) :
    ‖((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ≤ plaquetteDefect (R 0) q +
      ‖linearizedCurl (R 0) U.fine q‖ + 9 * (‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ^ 2 +
        ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 2 +
        ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 2 + ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ^ 2) := by
  have hp := plaquetteDefect_le_add_curl (chartField R U 0) (R 0) q
  have e : ∀ x i, chartField R U 0 x i * (R 0 x i)⁻¹ = expUnit (U.fine x i) := by
    intro x i
    simp [chartField]
  simp only [e] at hp
  have hc := norm_covariantCurlAt_sub_le (R 0) (fun x i => pureComponent ((expUnit (U.fine x i) : UnitQuaternion) : ℍ[ℝ]))
    (fun x i => (U.fine x i : ℍ[ℝ])) q
  have hd : ∀ x i, ‖(U.fine x i : ℍ[ℝ])‖ ≤ 1 →
      ‖pureComponent ((expUnit (U.fine x i) : UnitQuaternion) : ℍ[ℝ]) - (U.fine x i : ℍ[ℝ])‖ ≤
      ‖(U.fine x i : ℍ[ℝ])‖ ^ 2 := fun x i h => norm_pureComponent_exp_sub_self_le (U.fine x i).2 h
  have hg : ∀ x i, ‖((expUnit (U.fine x i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(U.fine x i : ℍ[ℝ])‖ := fun x i =>
    norm_exp_sub_one_le (U.fine x i).2
  have hcc : ‖covariantCurlAt (R 0) (fun x i => pureComponent ((expUnit (U.fine x i) : UnitQuaternion) : ℍ[ℝ])) q‖ ≤
      ‖linearizedCurl (R 0) U.fine q‖ +
      (‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ^ 2 + ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 2 +
        ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 2 + ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ^ 2) := by
    have e2 : linearizedCurl (R 0) U.fine q = covariantCurlAt (R 0) (fun x i => (U.fine x i : ℍ[ℝ])) q := rfl
    rw [e2]
    have := norm_sub_norm_le
      (covariantCurlAt (R 0) (fun x i => pureComponent ((expUnit (U.fine x i) : UnitQuaternion) : ℍ[ℝ])) q)
      (covariantCurlAt (R 0) (fun x i => (U.fine x i : ℍ[ℝ])) q)
    have a1 := hd _ _ h1
    have a2 := hd _ _ h2
    have a3 := hd _ _ h3
    have a4 := hd _ _ h4
    linarith
  set a := ‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ with ha
  set b := ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ with hb
  set c := ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ with hcdef
  set d := ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ with hddef
  have hsum : ‖((expUnit (U.fine q.1 q.2.1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine (q.1 + unitStep 0 q.2.1) q.2.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine (q.1 + unitStep 0 q.2.2) q.2.1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine q.1 q.2.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      a + b + c + d := add_le_add (add_le_add (add_le_add (hg _ _) (hg _ _)) (hg _ _)) (hg _ _)
  have h0 : 0 ≤ ‖((expUnit (U.fine q.1 q.2.1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine (q.1 + unitStep 0 q.2.1) q.2.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine (q.1 + unitStep 0 q.2.2) q.2.1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((expUnit (U.fine q.1 q.2.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    positivity
  have hsq := pow_le_pow_left₀ h0 hsum 2
  have h4' : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (c - d)]
  have him := norm_coe_im_le (plaquetteHolonomy (chartField R U 0) q)
  have hcv : ‖((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      plaquetteDefect (chartField R U 0) q := rfl
  rw [hcv] at him
  linarith
theorem sq_le_of_le_three_terms (A B D : ℝ) (a b c d : ℝ) (hD : D = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) (x : ℝ)
    (h0 : 0 ≤ x) (h : x ≤ A + B + 9 * D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    x ^ 2 ≤ 3 * A ^ 2 + 3 * B ^ 2 + 972 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have h1 : x ^ 2 ≤ (A + B + 9 * D) ^ 2 := pow_le_pow_left₀ h0 h 2
  have h2 : (A + B + 9 * D) ^ 2 ≤ 3 * A ^ 2 + 3 * B ^ 2 + 243 * D ^ 2 := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - 9 * D), sq_nonneg (B - 9 * D)]
  have h3 : D ^ 2 ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
    rw [hD]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2),
      sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2)]
  linarith
theorem sum_plaquettes_bond_le {P : Finset (F.Site 0 × Fin 4 × Fin 4)} {B : Finset (F.Site 0 × Fin 4)}
    (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (T : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4)
    (hT : ∀ q ∈ P, T q ∈ B) (hinj : ∀ q ∈ P, ∀ q' ∈ P, q.2 = q'.2 → T q = T q' → q.1 = q'.1) :
    ∑ q ∈ P, g (T q) ≤ 16 * ∑ b ∈ B, g b := by apply _root_.YangMills.Construction.CarriedCurl.sum_plaquettes_le_sixteen_mul_sum_bonds <;> assumption
theorem rpow_neg_le_decayWeights (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (del : ℝ) (p : F.Site 0) {j : ℕ}
    (x : F.Site j) {r : ℝ} (h1 : (F.blockSide : ℝ) ^ j ≤ r) (h2 : (baseDistance x p : ℝ) ≤ r) :
    (r / (F.blockSide : ℝ) ^ F.top) ^ (-θ) ≤ decayWeights F del θ p (enclosingCell x) j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  unfold decayWeights
  rw [show cellSupDist (enclosingCell x) (enclosingCell x) = 0 by rw [BlockLines.cellSupDist_self]]
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
  refine rpow_neg_le_rpow_neg (div_pos ?_ hN) (div_le_div_of_nonneg_right ?_ hN.le) hθ
  · unfold scaleRadius
    exact lt_min hN (lt_of_lt_of_le hp (le_max_left _ _))
  · unfold scaleRadius
    exact (min_le_right _ _).trans (max_le h1 h2)
theorem mem_near_bond_filter (hodd : Odd F.blockSide) {S : Finset F.Cell} (p : F.Site 0) {r : ℝ}
    (hr : r ≤ (F.blockSide : ℝ) ^ F.top) (hN4 : 4 ≤ F.blockSide ^ F.top) {b : F.Site 0 × Fin 4}
    (hb : b ∈ innerBonds S 0) (hd : (baseDistance b.1 p : ℝ) ≤ r + 1) :
    b ∈ (innerBonds (cellsNearPoint S p) 0).filter fun b => (baseDistance b.1 p : ℝ) ≤ r + 1 := by
  classical
  have hN4r : (4 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by exact_mod_cast hN4
  have h1 : (2 : ℝ) * (baseDistance b.1 p : ℝ) ≤ 3 * (F.blockSide : ℝ) ^ F.top := by linarith
  have h2 := baseDistance_add_unitStep_le (j := 0) (Nat.zero_le _) b.1 b.2 p
  rw [pow_zero] at h2
  have h2r : (baseDistance (b.1 + unitStep 0 b.2) p : ℝ) ≤ (baseDistance b.1 p : ℝ) + 1 := by exact_mod_cast h2
  have h3 : (2 : ℝ) * (baseDistance (b.1 + unitStep 0 b.2) p : ℝ) ≤ 3 * (F.blockSide : ℝ) ^ F.top := by linarith
  refine Finset.mem_filter.2 ⟨mem_innerBonds_cellsNearPoint hodd (Nat.zero_le _) hb p ?_ ?_, hd⟩
  · exact_mod_cast h1
  · exact_mod_cast h3
theorem sum_fine_pow_four_near_le (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) (S : Finset F.Cell)
    (U : ChainChart F) (p : F.Site 0) {r B : ℝ} (hr1 : 1 ≤ r) (hB : 0 ≤ B)
    (hW : ∑ b ∈ innerBonds (cellsNearPoint S p) 0, (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ B ^ 4) :
    ∑ b ∈ (innerBonds (cellsNearPoint S p) 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r + 1),
      ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 ≤ 16 * (r / (F.blockSide : ℝ) ^ F.top) ^ (4 * θ) * B ^ 4 := by
  classical
  set x := r / (F.blockSide : ℝ) ^ F.top with hx
  have hx0 : 0 < x := by positivity
  set ρ := (6 * x) ^ (-θ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hbig : ((ρ⁻¹) ^ 4) ≤ 16 * x ^ (4 * θ) := by
    rw [hρ, inv_rpow_neg_pow (by positivity) 4]
    exact mul_rpow_le_sixteen_mul hθ hθ8 hx0 6 (by norm_num) (by norm_num) (by linarith)
  have hw : ∀ b ∈ (innerBonds (cellsNearPoint S p) 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r + 1),
      ρ ≤ shiftedWeight F θ p 0 b.1 := by
    intro b hb
    have hd := (Finset.mem_filter.1 hb).2
    have h3 : (baseDistance b.1 p : ℝ) + 4 * (F.blockSide : ℝ) ^ 0 ≤ 6 * r := by
      rw [pow_zero]
      linarith
    have := rpow_le_shiftedWeight hL hθ.le p b.1 h3
    have e : 6 * r / (F.blockSide : ℝ) ^ F.top = 6 * x := by
      rw [hx]
      ring
    rw [e] at this
    exact this
  calc _ ≤ ∑ b ∈ (innerBonds (cellsNearPoint S p) 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r + 1),
        (ρ⁻¹) ^ 4 * (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 :=
        Finset.sum_le_sum fun b hb => pow_four_le_of_weight hρ0 (hw b hb) (norm_nonneg _)
    _ = (ρ⁻¹) ^ 4 * ∑ b ∈ (innerBonds (cellsNearPoint S p) 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r + 1),
        (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (ρ⁻¹) ^ 4 * B ^ 4 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun b _ _ => ?_) hW
        have : 0 ≤ shiftedWeight F θ p 0 b.1 := zero_le_one.trans (one_le_shiftedWeight hL hθ.le p _ _)
        positivity
    _ ≤ _ := mul_le_mul_of_nonneg_right hbig (by positivity)
theorem sum_linearizedCurl_sq_le (hodd : Odd F.blockSide) {θ del : ℝ} (hθ : 0 < θ) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) {r β : ℝ} (hr1 : 1 ≤ r)
    (hr : r ≤ (F.blockSide : ℝ) ^ F.top) (hN4 : 4 ≤ F.blockSide ^ F.top) (hβ : 0 ≤ β)
    (hN : ∀ z ∈ S, localNorm S R U (decayWeights F del θ p z) z ≤ β) :
    ∑ q ∈ (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r), ‖linearizedCurl (R 0) U.fine q‖ ^ 2 ≤
      625 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) * β ^ 2 := by
  classical
  have hL := hodd.pos
  set x := r / (F.blockSide : ℝ) ^ F.top with hx
  have hx0 : 0 < x := by positivity
  set ρ := x ^ (-θ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hx0 _
  have hρ2 : (ρ⁻¹) ^ 2 = x ^ (2 * θ) := by
    rw [hρ, inv_rpow_neg_pow hx0 2]
    norm_num
  set Y := (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r) with hY
  have hmaps : ∀ q ∈ Y, enclosingCell q.1 ∈ cellsNearPoint S p := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
    have hs : q.1 ∈ sitesOfCells S 0 := (NearCellNorms.corners_mem_sitesOfCells h1).1
    have hr3 : (2 : ℝ) * (baseDistance q.1 p : ℝ) ≤ 3 * (F.blockSide : ℝ) ^ F.top := by linarith
    refine Finset.mem_filter.2 ⟨enclosingCell_mem hodd hs, cellSupDist_enclosingCell_le_two hodd (Nat.zero_le _) hs p ?_⟩
    exact_mod_cast hr3
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hcell : ∀ z ∈ cellsNearPoint S p, ∑ q ∈ Y with enclosingCell q.1 = z, ‖linearizedCurl (R 0) U.fine q‖ ^ 2 ≤
      x ^ (2 * θ) * β ^ 2 := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_filter.1 hz).1
    have hparts := (localNorm_parts_le S R U (decayWeights F del θ p z) z hβ (hN z hzS)).2.1
    calc _ ≤ ∑ q ∈ Y with enclosingCell q.1 = z, (ρ⁻¹) ^ 2 *
          (decayWeights F del θ p z 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
          have h3 := (Finset.mem_filter.1 h1).2
          have hw := rpow_neg_le_decayWeights hL hθ.le del p q.1 (r := r) (by simpa using hr1) h3
          rw [h2] at hw
          exact sq_le_of_weight hρ0 hw (norm_nonneg _)
      _ = (ρ⁻¹) ^ 2 * ∑ q ∈ Y with enclosingCell q.1 = z,
          (decayWeights F del θ p z 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (ρ⁻¹) ^ 2 * β ^ 2 := by
          refine mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun _ _ _ => by positivity) hparts) (by positivity)
          intro q hq
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
          have h3 := (Finset.mem_filter.1 h1).1
          exact Finset.mem_filter.2 ⟨h3, by rw [h2]; exact singleton_subset_cellBall hzS (by simp)⟩
      _ = _ := by rw [hρ2]
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((cellsNearPoint S p).card : ℝ) ≤ 625 := by exact_mod_cast card_cellsNearPoint_le S p
  have h0 : 0 ≤ x ^ (2 * θ) * β ^ 2 := by positivity
  nlinarith
theorem sum_plaquetteDefect_sq_le (S : Finset F.Cell) (hL : 0 < F.blockSide) (R : F.FieldChain) (p : F.Site 0)
    {r E : ℝ} (hr1 : 1 ≤ r) (hE : 0 ≤ E)
    (hA : ∀ q ∈ innerPlaquettes S 0, plaquetteDefect (R 0) q ≤ E * levelScale F 0 ^ 2) :
    ∑ q ∈ (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r), plaquetteDefect (R 0) q ^ 2 ≤
      1296 * E ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ 4 := by
  classical
  have hl : levelScale F 0 = 1 / (F.blockSide : ℝ) ^ F.top := by
    unfold levelScale
    rw [one_div, inv_pow, Nat.sub_zero, one_div]
  have h1 : ∀ q ∈ (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r),
      plaquetteDefect (R 0) q ^ 2 ≤ (E * levelScale F 0 ^ 2) ^ 2 := fun q hq =>
    pow_le_pow_left₀ (norm_nonneg _) (hA q (Finset.mem_filter.1 hq).1) 2
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := card_innerPlaquettes_near_le (S := S) p hr1
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg (E * levelScale F 0 ^ 2))
  refine h2.trans (le_of_eq ?_)
  rw [hl]
  field_simp
  ring
theorem rpow_exponent_bounds {x θ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8) :
    x ^ 4 ≤ x ^ (2 * θ) ∧ x ^ (4 * θ) ≤ x ^ (2 * θ) ∧ x ≤ x ^ (2 * θ) := by
  refine ⟨?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (show 2 * θ ≤ (4 : ℝ) by linarith)
    rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  · exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  · have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (show 2 * θ ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at this
theorem sq_norm_plaquette_im_le (R : F.FieldChain) (U : ChainChart F) (q : F.Site 0 × Fin 4 × Fin 4)
    (h1 : ‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ≤ 1) (h2 : ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ≤ 1)
    (h3 : ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ≤ 1) (h4 : ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ≤ 1) :
    ‖((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤
      3 * plaquetteDefect (R 0) q ^ 2 + 3 * ‖linearizedCurl (R 0) U.fine q‖ ^ 2 +
        972 * (‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 4 +
          ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ^ 4) :=
  sq_le_of_le_three_terms (plaquetteDefect (R 0) q) ‖linearizedCurl (R 0) U.fine q‖ _ _ _ _ _ rfl _ (norm_nonneg _)
    (norm_plaquette_im_le R U q h1 h2 h3 h4) (norm_nonneg _) (norm_nonneg _)
theorem curvature_coefficients_le {A Bc a b c d E B β x y z w : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hxy : x ≤ y) (hwy : w ≤ y) (sA : A ≤ 1296 * E ^ 2 * x) (sB : Bc ≤ 625 * y * β ^ 2)
    (s1 : a ≤ 256 * w * B ^ 4) (s2 : b ≤ 256 * w * B ^ 4) (s3 : c ≤ 256 * w * B ^ 4) (s4 : d ≤ 256 * w * B ^ 4) :
    3 * A + 3 * Bc + 972 * (a + b + c + d) ≤ (3888 * E ^ 2 + 1875 * β ^ 2 + 995328 * B ^ 4) * y := by
  have t1 : (1296 * E ^ 2) * x ≤ (1296 * E ^ 2) * y := mul_le_mul_of_nonneg_left hxy (by positivity)
  have t2 : (256 * B ^ 4) * w ≤ (256 * B ^ 4) * y := mul_le_mul_of_nonneg_left hwy (by positivity)
  nlinarith
set_option maxHeartbeats 1000000 in
theorem localCurvatureSum_le (hodd : Odd F.blockSide) (hN4 : 4 ≤ F.blockSide ^ F.top) {θ del : ℝ} (hθ : 0 < θ)
    (hθ8 : θ ≤ 1 / 8) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) {r B β E : ℝ}
    (hr1 : 1 ≤ r) (hr : r ≤ (F.blockSide : ℝ) ^ F.top) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hE : 0 ≤ E)
    (hA : ∀ q ∈ innerPlaquettes S 0, plaquetteDefect (R 0) q ≤ E * levelScale F 0 ^ 2)
    (hW : ∑ b ∈ innerBonds (cellsNearPoint S p) 0, (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ B ^ 4)
    (hN : ∀ z ∈ S, localNorm S R U (decayWeights F del θ p z) z ≤ β)
    (hu : ∀ b ∈ innerBonds S 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1) :
    localCurvatureSum S R U p r ≤
      (3888 * E ^ 2 + 1875 * β ^ 2 + 995328 * B ^ 4) * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := by
  classical
  have hL := hodd.pos
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set x := r / (F.blockSide : ℝ) ^ F.top with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hNp]
    exact hr
  obtain ⟨e1, e2, -⟩ := rpow_exponent_bounds hx0 hx1 hθ hθ8
  set Y := (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r) with hY
  set B' := (innerBonds (cellsNearPoint S p) 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r + 1) with hB'
  have hq4 := sum_fine_pow_four_near_le hL hθ hθ8 S U p hr1 hB hW
  have hstep : ∀ (y : F.Site 0) (i : Fin 4), (baseDistance y p : ℝ) ≤ r →
      (baseDistance (y + unitStep 0 i) p : ℝ) ≤ r + 1 := by
    intro y i hd
    have h2 := baseDistance_add_unitStep_le (j := 0) (Nat.zero_le _) y i p
    rw [pow_zero] at h2
    have h2r : (baseDistance (y + unitStep 0 i) p : ℝ) ≤ (baseDistance y p : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hb1 : ∀ q ∈ Y, (q.1, q.2.1) ∈ innerBonds S 0 ∧ (q.1 + unitStep 0 q.2.1, q.2.2) ∈ innerBonds S 0 ∧
      (q.1 + unitStep 0 q.2.2, q.2.1) ∈ innerBonds S 0 ∧ (q.1, q.2.2) ∈ innerBonds S 0 := by
    intro q hq
    obtain ⟨c1, c2, c3, c4⟩ := NearCellNorms.corners_mem_sitesOfCells (Finset.mem_filter.1 hq).1
    refine ⟨ChartCoordinates.mem_innerBonds c1 c2, ChartCoordinates.mem_innerBonds c2 c4, ChartCoordinates.mem_innerBonds c3 ?_,
      ChartCoordinates.mem_innerBonds c1 c3⟩
    rwa [add_right_comm]
  have hd1 : ∀ q ∈ Y, (baseDistance q.1 p : ℝ) ≤ r := fun q hq => (Finset.mem_filter.1 hq).2
  have hsumT : ∀ T : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4, (∀ q ∈ Y, T q ∈ innerBonds S 0) →
      (∀ q ∈ Y, (baseDistance (T q).1 p : ℝ) ≤ r + 1) →
      (∀ q ∈ Y, ∀ q' ∈ Y, q.2 = q'.2 → T q = T q' → q.1 = q'.1) →
      ∑ q ∈ Y, ‖(U.fine (T q).1 (T q).2 : ℍ[ℝ])‖ ^ 4 ≤ 256 * x ^ (4 * θ) * B ^ 4 := by
    intro T h1 h2 h3
    have := sum_plaquettes_bond_le (P := Y) (B := B') (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4) (fun _ => by positivity) T
      (fun q hq => mem_near_bond_filter hodd p hr hN4 (h1 q hq) (h2 q hq)) h3
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hq4 (by norm_num : (0 : ℝ) ≤ 16)
    refine this.trans (le_of_eq ?_)
    ring
  have s1 := hsumT (fun q => (q.1, q.2.1)) (fun q hq => (hb1 q hq).1)
    (fun q hq => by simpa using (hd1 q hq).trans (by linarith))
    (fun q _ q' _ _ e => (Prod.ext_iff.1 e).1)
  have s2 := hsumT (fun q => (q.1 + unitStep 0 q.2.1, q.2.2)) (fun q hq => (hb1 q hq).2.1)
    (fun q hq => hstep _ _ (hd1 q hq))
    (fun q _ q' _ h e => by
      have e1 := congrArg Prod.fst e
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have s3 := hsumT (fun q => (q.1 + unitStep 0 q.2.2, q.2.1)) (fun q hq => (hb1 q hq).2.2.1)
    (fun q hq => hstep _ _ (hd1 q hq))
    (fun q _ q' _ h e => by
      have e1 := congrArg Prod.fst e
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have s4 := hsumT (fun q => (q.1, q.2.2)) (fun q hq => (hb1 q hq).2.2.2)
    (fun q hq => by simpa using (hd1 q hq).trans (by linarith))
    (fun q _ q' _ _ e => (Prod.ext_iff.1 e).1)
  have sA := sum_plaquetteDefect_sq_le S hL R p hr1 hE hA
  have sB := sum_linearizedCurl_sq_le (del := del) hodd hθ S R U p hr1 hr hN4 hβ hN
  have hone : ∀ q ∈ Y, ‖((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤
      3 * plaquetteDefect (R 0) q ^ 2 + 3 * ‖linearizedCurl (R 0) U.fine q‖ ^ 2 +
        972 * (‖(U.fine q.1 q.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(U.fine (q.1 + unitStep 0 q.2.1) q.2.2 : ℍ[ℝ])‖ ^ 4 +
          ‖(U.fine (q.1 + unitStep 0 q.2.2) q.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(U.fine q.1 q.2.2 : ℍ[ℝ])‖ ^ 4) := by
    intro q hq
    obtain ⟨b1, b2, b3, b4⟩ := hb1 q hq
    exact sq_norm_plaquette_im_le R U q (hu (q.1, q.2.1) b1) (hu (q.1 + unitStep 0 q.2.1, q.2.2) b2)
      (hu (q.1 + unitStep 0 q.2.2, q.2.1) b3) (hu (q.1, q.2.2) b4)
  unfold localCurvatureSum
  refine (Finset.sum_le_sum hone).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hx2 : 0 ≤ x ^ (2 * θ) := by positivity
  exact curvature_coefficients_le hE hB hβ hx2 hx2 e1 e2 sA sB s1 s2 s3 s4
theorem sum_levelScale_le_one (hL : 2 ≤ F.blockSide) : ∑ j ∈ Finset.range F.depth, levelScale F (j + 1) ≤ 1 := by
  have hLr : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  set a : ℝ := 1 / (F.blockSide : ℝ) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hLr
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, a ^ (m - j) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have e : ∑ j ∈ Finset.range m, a ^ (m + 1 - j) = a * ∑ j ∈ Finset.range m, a ^ (m - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : m + 1 - j = (m - j) + 1 := by
          have := Finset.mem_range.1 hj
          omega
        rw [this, pow_succ]
        ring
      rw [e]
      simp only [Nat.add_sub_cancel_left, pow_one]
      nlinarith
  refine le_trans (le_of_eq ?_) (key F.depth)
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold levelScale
  have : F.top - (j + 1) = F.depth - j := by
    have : F.top = F.depth + 1 := rfl
    omega
  rw [this]
theorem chartBondMisfit_of_lt_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) :
    chartBondMisfit R U V j c = expUnit (U.coarse j c.1 c.2) * referenceDefect R j c := by
  unfold chartBondMisfit
  rw [ChartCoordinates.chartChain_of_lt R U V hj, ChartCoordinates.chartChain_of_lt R U V (show j < F.top by omega)]
  simp only [chartField, chartGauge]
  group
theorem sum_misfit_level_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ del : ℝ} (hθ : 0 < θ)
    (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (p : F.Site 0) {r β E : ℝ}
    (hr1 : 1 ≤ r) (hr : r ≤ (F.blockSide : ℝ) ^ F.top) (hE : 0 ≤ E) {j : ℕ} (hj : j + 1 < F.top)
    (hLj : (F.blockSide : ℝ) ^ (j + 1) ≤ r)
    (hmis : ∀ c ∈ innerBonds S (j + 1), normSubOne (referenceDefect R j c) ≤ E * levelScale F (j + 1) ^ 3) :
    ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U V j c) ^ 2 ≤
      2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) * ∑ z ∈ cellsNearPoint S p,
        ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 +
      5000 * E ^ 2 * ((r / (F.blockSide : ℝ) ^ F.top) * levelScale F (j + 1)) := by
  classical
  have hLpos := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set x := r / (F.blockSide : ℝ) ^ F.top with hx
  have hx0 : 0 < x := by positivity
  set ρ := x ^ (-θ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hx0 _
  have hρ2 : (ρ⁻¹) ^ 2 = x ^ (2 * θ) := by
    rw [hρ, inv_rpow_neg_pow hx0 2]
    norm_num
  set l := levelScale F (j + 1) with hl
  have hl0 : 0 ≤ l := by
    rw [hl]
    unfold levelScale
    positivity
  set Y := (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r) with hY
  have hnear : ∀ c ∈ Y, c ∈ innerBonds (cellsNearPoint S p) (j + 1) := by
    intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
    have h3 : baseDistance c.1 p ≤ F.blockSide ^ F.top := by
      have : (baseDistance c.1 p : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := h2.trans hr
      exact_mod_cast this
    obtain ⟨a1, a2⟩ := twice_baseDistance_ends_le hL hj c.1 c.2 p h3
    exact mem_innerBonds_cellsNearPoint hodd (by omega) h1 p a1 a2
  have hone : ∀ c ∈ Y, normSubOne (chartBondMisfit R U V j c) ^ 2 ≤
      2 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 + 2 * (E * l ^ 3) ^ 2 := by
    intro c hc
    obtain ⟨h1, -⟩ := Finset.mem_filter.1 hc
    have e1 : normSubOne (chartBondMisfit R U V j c) ≤ ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + E * l ^ 3 := by
      rw [chartBondMisfit_of_lt_top R U V hj c]
      refine (norm_coe_mul_sub_one_le _ _).trans
        (add_le_add (norm_exp_sub_one_le (U.coarse j c.1 c.2).2) (hmis c h1))
    have e2 : 0 ≤ normSubOne (chartBondMisfit R U V j c) := norm_nonneg _
    have e3 := pow_le_pow_left₀ e2 e1 2
    nlinarith [sq_nonneg (‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ - E * l ^ 3)]
  have hmaps : ∀ c ∈ Y, enclosingCell c.1 ∈ cellsNearPoint S p := by
    intro c hc
    have h1 := hnear c hc
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at h1
    exact enclosingCell_mem hodd h1.1.1
  have hP : ∑ c ∈ Y, ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ x ^ (2 * θ) * ∑ z ∈ cellsNearPoint S p,
      ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have hzS : z ∈ S := (Finset.mem_filter.1 hz).1
    calc _ ≤ ∑ c ∈ Y with enclosingCell c.1 = z, (ρ⁻¹) ^ 2 *
          (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
          refine Finset.sum_le_sum fun c hc => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
          have h3 := (Finset.mem_filter.1 h1).2
          have hw := rpow_neg_le_decayWeights hodd.pos hθ.le del p c.1 hLj h3
          rw [h2] at hw
          exact sq_le_of_weight hρ0 hw (norm_nonneg (U.coarse j c.1 c.2))
      _ = (ρ⁻¹) ^ 2 * ∑ c ∈ Y with enclosingCell c.1 = z,
          (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          rw [hρ2]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun _ _ _ => Even.pow_nonneg (by decide) _) (by positivity)
          intro c hc
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
          have h3 := (Finset.mem_filter.1 h1).1
          exact Finset.mem_filter.2 ⟨h3, by rw [h2]; exact singleton_subset_cellBall hzS (by simp)⟩
  have hM : l * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) = 1 := by
    rw [hl]
    unfold levelScale
    push_cast
    rw [← mul_pow, one_div, inv_mul_cancel₀ hLr.ne', one_pow]
  have hcard : (Y.card : ℝ) ≤ 2500 * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) ^ 4 := by
    have h1 : Y.card ≤ (innerBonds (cellsNearPoint S p) (j + 1)).card := Finset.card_le_card hnear
    have h2 := card_innerBonds_le hodd (cellsNearPoint S p) (j + 1)
    have h3 : (cellsNearPoint S p).card * (F.blockSide ^ (F.top - (j + 1))) ^ 4 ≤
        625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4 :=
      Nat.mul_le_mul_right _ (card_cellsNearPoint_le S p)
    have h4 : Y.card ≤ 4 * (625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) :=
      h1.trans (h2.trans (Nat.mul_le_mul_left 4 h3))
    have h5 : (Y.card : ℝ) ≤ ((4 * (625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) : ℕ) : ℝ) := by exact_mod_cast h4
    refine h5.trans (le_of_eq ?_)
    push_cast
    ring
  have hlx : l ≤ x := by
    have hNe : (F.blockSide : ℝ) ^ F.top =
        (F.blockSide : ℝ) ^ (j + 1) * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    have e : l = (F.blockSide : ℝ) ^ (j + 1) / (F.blockSide : ℝ) ^ F.top := by
      rw [hNe, eq_div_iff (by positivity)]
      calc l * ((F.blockSide : ℝ) ^ (j + 1) * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ))
          = (l * ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ)) * (F.blockSide : ℝ) ^ (j + 1) := by ring
        _ = _ := by rw [hM, one_mul]
    rw [e, hx]
    exact div_le_div_of_nonneg_right hLj hNp.le
  have hQ : ∑ c ∈ Y, (E * l ^ 3) ^ 2 ≤ 2500 * E ^ 2 * (x * l) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    set M : ℝ := ((F.blockSide ^ (F.top - (j + 1)) : ℕ) : ℝ) with hMdef
    have h1 := mul_le_mul_of_nonneg_right hcard (sq_nonneg (E * l ^ 3))
    refine h1.trans ?_
    have e : 2500 * M ^ 4 * (E * l ^ 3) ^ 2 = 2500 * E ^ 2 * l ^ 2 * (l * M) ^ 4 := by ring
    rw [e, hM, one_pow, mul_one]
    have h2 : l ^ 2 ≤ x * l := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2500 * E ^ 2)
    linarith
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have a1 := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)
  have a2 := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 2)
  linarith
theorem localMisfitSum_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ del : ℝ} (hθ : 0 < θ)
    (hθ8 : θ ≤ 1 / 8) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (p : F.Site 0) {r β E T : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ (F.blockSide : ℝ) ^ F.top) (hβ : 0 ≤ β) (hE : 0 ≤ E)
    (hT : 0 ≤ T)
    (hmis : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      normSubOne (referenceDefect R j c) ≤ E * levelScale F (j + 1) ^ 3)
    (hN : ∀ z ∈ S, localNorm S R U (decayWeights F del θ p z) z ≤ β)
    (htop : ∀ c ∈ innerBonds S F.top, normSubOne (chartBondMisfit R U V F.depth c) ≤ T) :
    localMisfitSum S R U V p r ≤
      (1250 * β ^ 2 + 5000 * E ^ 2 + 2500 * T ^ 2) * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := by
  classical
  have hLpos := hodd.pos
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set x := r / (F.blockSide : ℝ) ^ F.top with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hNp]
    exact hr
  obtain ⟨-, -, e3⟩ := rpow_exponent_bounds hx0 hx1 hθ hθ8
  set y := x ^ (2 * θ) with hy
  set W : ℕ → ℝ := fun j => ∑ z ∈ cellsNearPoint S p, ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
    (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 with hW
  have hW0 : ∀ j, 0 ≤ W j := fun j => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Even.pow_nonneg (by decide) _
  have hWs : ∑ j ∈ Finset.range F.depth, W j ≤ 625 * β ^ 2 := by
    simp only [hW]
    rw [Finset.sum_comm]
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (decayWeights F del θ p z (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ β ^ 2 := by
      intro z hz
      have := sum_coarse_sq_le_of_localNorm_le S R U (decayWeights F del θ p z) z
        (hN z (Finset.mem_filter.1 hz).1) hβ
      simpa [BlockFrame.top] using this
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((cellsNearPoint S p).card : ℝ) ≤ 625 := by exact_mod_cast card_cellsNearPoint_le S p
    have h0 : 0 ≤ β ^ 2 := by positivity
    nlinarith
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hs := sum_levelScale_le_one (F := F) hL
  unfold localMisfitSum
  rw [Finset.sum_filter]
  change ∑ j ∈ Finset.range (F.depth + 1), _ ≤ _
  rw [Finset.sum_range_succ]
  have hbelow : ∑ j ∈ Finset.range F.depth, (if (F.blockSide : ℝ) ^ (j + 1) ≤ r then
      ∑ c ∈ (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U V j c) ^ 2 else 0) ≤
      ∑ j ∈ Finset.range F.depth, (2 * y * W j + 5000 * E ^ 2 * (x * levelScale F (j + 1))) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjt : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      have e : F.top = F.depth + 1 := rfl
      omega
    split_ifs with hc
    · exact sum_misfit_level_le (β := β) hodd hL hθ S R U V p hr1 hr hE hjt hc (hmis j hjt)
    · have := hW0 j
      have h2 := hl0 (j + 1)
      positivity
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hbelow
  have htop' : (if (F.blockSide : ℝ) ^ (F.depth + 1) ≤ r then
      ∑ c ∈ (innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
        normSubOne (chartBondMisfit R U V F.depth c) ^ 2 else 0) ≤
      2500 * T ^ 2 * y := by
    split_ifs with hc
    · have hrN : r = (F.blockSide : ℝ) ^ F.top := le_antisymm hr hc
      have hx1' : x = 1 := by
        rw [hx, hrN, div_self hNp.ne']
      have hy1 : y = 1 := by
        rw [hy, hx1', Real.one_rpow]
      rw [hy1, mul_one]
      have h1 : ∀ c ∈ (innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r),
          normSubOne (chartBondMisfit R U V F.depth c) ^ 2 ≤ T ^ 2 := fun c hc' =>
        pow_le_pow_left₀ (norm_nonneg _) (htop c (Finset.mem_filter.1 hc').1) 2
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)).card ≤ 2500 := by
        have h2 : ((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)) ⊆
            sitesOfCells (cellsNearPoint S p) F.top ×ˢ (Finset.univ : Finset (Fin 4)) := by
          intro c hc'
          obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hc'
          have h5 : c.1 ∈ sitesOfCells S F.top := (ChartCoordinates.innerBonds_ends h3).1
          have h6 : (2 : ℝ) * (baseDistance c.1 p : ℝ) ≤ 3 * (F.blockSide : ℝ) ^ F.top := by linarith
          have h7 : 2 * baseDistance c.1 p ≤ 3 * F.blockSide ^ F.top := by exact_mod_cast h6
          refine Finset.mem_product.2 ⟨mem_sitesOfCells_of_enclosingCell_mem hodd h5 ?_, Finset.mem_univ _⟩
          exact Finset.mem_filter.2 ⟨enclosingCell_mem hodd h5, cellSupDist_enclosingCell_le_two hodd le_rfl h5 p h7⟩
        refine (Finset.card_le_card h2).trans ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        have h8 := card_sitesOfCells_le hodd (cellsNearPoint S p) F.top
        simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at h8
        have h9 := card_cellsNearPoint_le S p
        omega
      have hcr : (((innerBonds S (F.depth + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)).card : ℝ) ≤ 2500 := by
        exact_mod_cast hcard
      have h0 : 0 ≤ T ^ 2 := by positivity
      nlinarith
    · positivity
  have t1 : 2 * y * ∑ j ∈ Finset.range F.depth, W j ≤ 2 * y * (625 * β ^ 2) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have t2 : x * ∑ j ∈ Finset.range F.depth, levelScale F (j + 1) ≤ y := by
    have := mul_le_mul_of_nonneg_left hs hx0.le
    linarith
  have t3 := mul_le_mul_of_nonneg_left t2 (by positivity : (0 : ℝ) ≤ 5000 * E ^ 2)
  nlinarith
theorem localNorm_unit_le_two_mul (hL : 0 < F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (hdel : 0 ≤ del)
    (hdel8 : del ≤ 1 / 8) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z ≤ 2 * localNorm S R U (decayWeights F del θ p z) z := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.localNorm_unit_le_two_mul <;> assumption
theorem norm_fine_le (hL : 0 < F.blockSide) (hodd : Odd F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) {β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ z ∈ S, localNorm S R U (decayWeights F del θ p z) z ≤ β) :
    ∀ b ∈ innerBonds S 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ≤ β := by
  classical
  intro b hb
  have hz : enclosingCell b.1 ∈ S := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
    exact enclosingCell_mem hodd hb.1.1
  have hb' : b ∈ bondsOver S {enclosingCell b.1} 0 := Finset.mem_filter.2 ⟨hb, by simp⟩
  have h1 := Finset.single_le_sum (f := fun b' : F.Site 0 × Fin 4 =>
    (decayWeights F del θ p (enclosingCell b.1) 0 b'.1 * ‖U.fine b'.1 b'.2‖) ^ 4)
    (fun _ _ => Even.pow_nonneg (by decide) _) (bondsOver_singleton_subset hz 0 hb')
  have h2 := h1.trans (localNorm_parts_le S R U _ _ hβ (hN _ hz)).1
  have h4 := one_le_decayWeights_self hL hθ del p 0 b.1
  have h5 : (0 : ℝ) ≤ ‖U.fine b.1 b.2‖ := norm_nonneg _
  have h3 : decayWeights F del θ p (enclosingCell b.1) 0 b.1 * ‖U.fine b.1 b.2‖ ≤ β :=
    le_of_not_gt fun hlt => absurd h2 (not_le.2 (pow_lt_pow_left₀ hlt hβ (by norm_num)))
  calc ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ = ‖U.fine b.1 b.2‖ := rfl
    _ ≤ _ := le_mul_of_one_le_left h5 h4
    _ ≤ β := h3
theorem curvature_coefficient_le {K Db Cw β s y : ℝ} (hK : 3888 * Db ^ 2 + 1875 + 995328 * Cw ^ 4 ≤ K)
    (hK1 : 1 ≤ K) (h0 : 0 ≤ s) (hsβ : s ≤ β) (hβ1 : β ≤ 1) (hy : 0 ≤ y) :
    (3888 * (Db * s) ^ 2 + 1875 * β ^ 2 + 995328 * (Cw * β) ^ 4) * y ≤ (K * β) ^ 2 * y := by
  refine mul_le_mul_of_nonneg_right ?_ hy
  have hβ0 : 0 ≤ β := h0.trans hsβ
  have h1 : s ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ h0 hsβ 2
  have h2 : β ^ 4 ≤ β ^ 2 := pow_le_pow_of_le_one hβ0 hβ1 (by norm_num)
  have h3 : (Db * s) ^ 2 ≤ Db ^ 2 * β ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (Cw * β) ^ 4 ≤ Cw ^ 4 * β ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : K ≤ K ^ 2 := by nlinarith
  have h6 : K * β ^ 2 ≤ K ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_right h5 (by positivity)
  have h7 : (3888 * Db ^ 2 + 1875 + 995328 * Cw ^ 4) * β ^ 2 ≤ K * β ^ 2 :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  rw [mul_pow]
  nlinarith
theorem misfit_coefficient_le {K Db Cm β s y : ℝ} (hK : 1250 + 5000 * Db ^ 2 + 22500 * Cm ^ 2 ≤ K) (hK1 : 1 ≤ K)
    (h0 : 0 ≤ s) (hsβ : s ≤ β) (hy : 0 ≤ y) :
    (1250 * β ^ 2 + 5000 * (Db * s) ^ 2 + 2500 * (Cm * (s + 2 * β)) ^ 2) * y ≤ (K * β) ^ 2 * y := by
  refine mul_le_mul_of_nonneg_right ?_ hy
  have hβ0 : 0 ≤ β := h0.trans hsβ
  have h1 : s ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ h0 hsβ 2
  have h3 : (Db * s) ^ 2 ≤ Db ^ 2 * β ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (Cm * (s + 2 * β)) ^ 2 ≤ Cm ^ 2 * (9 * β ^ 2) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : s + 2 * β ≤ 3 * β := by linarith
    have := pow_le_pow_left₀ (by positivity) this 2
    nlinarith
  have h5 : K ≤ K ^ 2 := by nlinarith
  have h6 : K * β ^ 2 ≤ K ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_right h5 (by positivity)
  have h7 : (1250 + 5000 * Db ^ 2 + 22500 * Cm ^ 2) * β ^ 2 ≤ K * β ^ 2 :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  rw [mul_pow]
  nlinarith
end SmallChartBounds
open SmallChartBounds BlockAverages BlockLines BlockWeights PlaquetteExpansion
theorem BlockAverages.smallChartLocalBounds (hWG : weightedLevelGapsStatement) (hB : referenceBoundsStatement)
    (hLM : topMisfitNearCellStatement) : smallChartLocalBoundsStatement := by
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  obtain ⟨Cm, hCm, Lm, hLM⟩ := hLM
  intro θ del hθ hθ8 hdel hdel8
  obtain ⟨Lw, hWG⟩ := hWG θ del hθ hθ8 hdel hdel8
  refine ⟨max (max Lw L1) (max Lm 5), fun L hL hge => ?_⟩
  have hLw : Lw ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL1 : L1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hLm : Lm ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hge)
  have hL5 : 5 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hge)
  obtain ⟨cw, Cw, hcw, hCw, hWGL⟩ := hWG L hL hLw
  obtain ⟨cm, hcm, hLML⟩ := hLM L hL hLm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ : ∃ K : ℝ, 1 ≤ K ∧ 2 * Cw ≤ K ∧ 3888 * Db ^ 2 + 1875 + 995328 * Cw ^ 4 ≤ K ∧
      1250 + 5000 * Db ^ 2 + 22500 * Cm ^ 2 ≤ K := by
    refine ⟨1 + 2 * Cw + (3888 * Db ^ 2 + 1875 + 995328 * Cw ^ 4) + (1250 + 5000 * Db ^ 2 + 22500 * Cm ^ 2),
      ?_, ?_, ?_, ?_⟩
    · have h1 : 0 ≤ Db ^ 2 := sq_nonneg _
      have h2 : 0 ≤ Cw ^ 4 := by positivity
      have h3 : 0 ≤ Cm ^ 2 := sq_nonneg _
      linarith
    · have h1 : 0 ≤ Db ^ 2 := sq_nonneg _
      have h2 : 0 ≤ Cw ^ 4 := by positivity
      have h3 : 0 ≤ Cm ^ 2 := sq_nonneg _
      linarith
    · have h3 : 0 ≤ Cm ^ 2 := sq_nonneg _
      have h1 : 0 ≤ Db ^ 2 := sq_nonneg _
      linarith
    · have h1 : 0 ≤ Db ^ 2 := sq_nonneg _
      have h2 : 0 ≤ Cw ^ 4 := by positivity
      linarith
  have hmin0 : 0 < min (min cw cb) (min cm (1 / 8)) := lt_min (lt_min hcw hcb) (lt_min hcm (by norm_num))
  obtain ⟨c, hc0, hcc⟩ : ∃ c : ℝ, 0 < c ∧ 2 * c ≤ min (min cw cb) (min cm (1 / 8)) :=
    ⟨min (min cw cb) (min cm (1 / 8)) / 2, by positivity, by linarith⟩
  have hc1 : 2 * c ≤ cw := hcc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hc2 : 2 * c ≤ cb := hcc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc3 : 2 * c ≤ cm := hcc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc4 : 2 * c ≤ 1 / 8 := hcc.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, K, hc0, by linarith, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold U β hsβ hβc hN
  subst hFL
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hL2 : 2 ≤ F.blockSide := by omega
  have hN4 : 4 ≤ F.blockSide ^ F.top := by
    have : F.blockSide ≤ F.blockSide ^ F.top := Nat.le_self_pow (by simp [BlockFrame.top]) _
    omega
  obtain ⟨-, b2, b3, -, -, -⟩ := hBd F m S hodd hL1 hamb hm hreg s V hs0 (by linarith) hcold
  have hβ0 : 0 ≤ β := hs0.le.trans hsβ
  have hNz : ∀ (p : F.Site 0), ∀ z ∈ S,
      localNorm S (referenceFieldChain S V) U (decayWeights F del θ p z) z ≤ β :=
    fun p z hz => (localNorm_le_weightedNorm S _ U _ hz).trans (hN p z)
  have hW := fun (p : F.Site 0) j hj => hWGL F m S rfl hamb hm hreg s V hs0 (by linarith) hcold U p β hβ0
    (by linarith) (fun y0 => hN p y0) j hj
  have hCwβ : 0 ≤ Cw * β := by positivity
  refine ⟨fun j p r hj hr1 hr => ?_, fun p r hr1 hr => ⟨?_, ?_⟩⟩
  · refine (localQuarticSum_le hodd hL2 hθ hθ8 S _ U p hj hr1 hr hCwβ (hW p j hj)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    nlinarith
  · have hu := norm_fine_le hLpos hodd hθ.le S (referenceFieldChain S V) U p hβ0 (hNz p)
    have hW0 : ∑ b ∈ innerBonds (cellsNearPoint S p) 0, (shiftedWeight F θ p 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
        (Cw * β) ^ 4 := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b hb => ?_)) (hW p 0 (Nat.succ_pos _))
      have hbS : b ∈ innerBonds S 0 := innerBonds_mono (Finset.filter_subset _ _) 0 hb
      have h1 := hu b hbS
      have e : levelCoordinate (referenceFieldChain S V) U 0 b.1 b.2 = (U.fine b.1 b.2 : ℍ[ℝ]) := by
        unfold levelCoordinate chartGap
        simp only [chartField, mul_inv_cancel_right]
        exact unitQuaternionLog_expUnit (by linarith)
      rw [e]
      rfl
    have h := localCurvatureSum_le (del := del) (E := Db * s) hodd hN4 hθ hθ8 S (referenceFieldChain S V) U p hr1 hr
      hCwβ hβ0 (by positivity) (fun q hq => b2 0 (Nat.succ_pos _) q hq) hW0 (hNz p)
      (fun b hb => (hu b hb).trans (by linarith))
    exact h.trans (curvature_coefficient_le hK3 hK1 hs0.le hsβ (by linarith) (Real.rpow_nonneg (by positivity) _))
  · have htop : ∀ c ∈ innerBonds S F.top,
        normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth c) ≤ Cm * (s + 2 * β) := by
      intro c hc
      have hz : enclosingCell c.1 ∈ S := enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hc).1
      have h1 := localNorm_unit_le_two_mul hLpos hθ.le hdel.le hdel8 S (referenceFieldChain S V) U p (enclosingCell c.1)
      have h2 := hNz p _ hz
      exact hLML F m S rfl hamb hm hreg s V hs0 (by linarith) hcold U (enclosingCell c.1) (2 * β) hz (by positivity)
        (by linarith) (by linarith) c (Finset.mem_filter.2 ⟨hc, by simp⟩)
    have h := localMisfitSum_le (E := Db * s) (T := Cm * (s + 2 * β)) hodd hL2 hθ hθ8 S (referenceFieldChain S V) U V p
      hr1 hr hβ0 (by positivity) (by positivity) (fun j hj c hc => b3 j hj c hc) (hNz p) htop
    exact h.trans (misfit_coefficient_le hK4 hK1 hs0.le hsβ (Real.rpow_nonneg (by positivity) _))
end YangMills.Construction
end
