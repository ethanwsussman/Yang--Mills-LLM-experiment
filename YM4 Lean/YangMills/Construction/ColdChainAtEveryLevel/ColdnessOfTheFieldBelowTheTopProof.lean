import YangMills.Construction.ColdChainAtEveryLevel.ColdnessOfTheFieldBelowTheTop
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedForm
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.WeightedGapsAboutAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open BlockLines BlockWeights PlaquetteExpansion LatticePaths LatticeFractionalIntegration FlatPairing
namespace ColdBelowTop
variable {F : BlockFrame}
theorem natAbs_le_of_mem_centredCube (hL : 1 ≤ F.blockSide) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide)
    (i : Fin 4) : (h i).natAbs ≤ F.blockSide := by
  have := (mem_centredCube_iff _ _).1 hh i
  omega
theorem shiftedWeight_refine_le (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ} (hj : j < F.top)
    (y : F.Site (j + 1)) (x : F.Site j) (v : Fin 4 → ℤ) (hv : ∀ i, (v i).natAbs ≤ 2 * F.blockSide)
    (e : x = refineSite y + siteOfCoords j v) : shiftedWeight F θ p (j + 1) y ≤ shiftedWeight F θ p j x := by
  rw [e]
  exact shiftedWeight_succ_le hL hθ p hj y v hv
theorem natAbs_add_smul_basisVector_le (hL : 1 ≤ F.blockSide) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide)
    (k : Fin 4) {r : ℕ} (hr : r < F.blockSide) (i : Fin 4) :
    ((h + (r : ℤ) • basisVector k) i).natAbs ≤ 2 * F.blockSide := by
  refine (Int.natAbs_add_le _ _).trans ?_
  have h1 := natAbs_le_of_mem_centredCube hL hh i
  have h2 : (((r : ℤ) • basisVector k) i).natAbs ≤ F.blockSide := by
    by_cases hi : i = k
    · subst hi
      simp [basisVector]
      omega
    · simp [basisVector, Pi.single_eq_of_ne hi]
  omega
theorem natAbs_smul_basisVector_add_le (hL : 1 ≤ F.blockSide) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide)
    (k : Fin 4) (i : Fin 4) :
    (((F.blockSide : ℤ) • basisVector k + h) i).natAbs ≤ 2 * F.blockSide := by
  refine (Int.natAbs_add_le _ _).trans ?_
  have h1 := natAbs_le_of_mem_centredCube hL hh i
  have h2 : (((F.blockSide : ℤ) • basisVector k) i).natAbs ≤ F.blockSide := by
    by_cases hi : i = k
    · subst hi
      simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne hi]
  omega
theorem shiftedWeight_mul_norm_parallelAverage_le (hodd : Odd F.blockSide) (hL2 : 2 ≤ F.blockSide) {θ : ℝ}
    (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ} (hj : j < F.top)
    (Rj : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ]) (c' : F.Site (j + 1) × Fin 4) :
    shiftedWeight F θ p (j + 1) c'.1 * ‖parallelAverage Rj f c'‖ ≤
      lineBlockAverage (fun x i => shiftedWeight F θ p j x * ‖f x i‖) c' := by
  have hL1 : 1 ≤ F.blockSide := by omega
  have hΩ0 : 0 ≤ shiftedWeight F θ p (j + 1) c'.1 := zero_le_one.trans (one_le_shiftedWeight (by omega) hθ p _ _)
  have h1 := norm_parallelAverage_le hodd Rj f c'
  have h2 := mul_le_mul_of_nonneg_left h1 hΩ0
  refine h2.trans ?_
  unfold lineBlockAverage
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h hh => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact shiftedWeight_refine_le hL2 hθ p hj c'.1 _ (h + (r : ℤ) • basisVector c'.2)
    (natAbs_add_smul_basisVector_le hL1 hh c'.2 (Finset.mem_range.1 hr)) (lineBond_fst c' h r)
theorem parallelAverage_sub {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i - g x i) c = parallelAverage R f c - parallelAverage R g c := by
  unfold parallelAverage
  simp only [BlockLines.adjointAction_sub, Finset.sum_sub_distrib, smul_sub]
def coordinateRemainder (R : F.FieldChain) (U : ChainChart F) (f0 : F.Site 0 → Fin 4 → ℍ[ℝ]) (j : ℕ) :
    F.Site j → Fin 4 → ℍ[ℝ] := fun x i => levelCoordinate R U j x i - transportedForm R f0 j x i
def stepRemainder (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  levelCoordinate R U (j + 1) c.1 c.2 - (U.coarse j c.1 c.2 : ℍ[ℝ]) - parallelAverage (R j) (levelCoordinate R U j) c
theorem sq_le_three_mul_sum_sq {a b c x : ℝ} (h0 : 0 ≤ x) (h : x ≤ a + b + c) :
    x ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  have h1 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
theorem sum_weighted_coordinateRemainder_sq_le (hodd : Odd F.blockSide) (hL : 3 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) (D : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (f0 : F.Site 0 → Fin 4 → ℍ[ℝ]) {Q M : ℝ}
    (h0 : ∀ b ∈ innerBonds D 0, coordinateRemainder R U f0 0 b.1 b.2 = 0)
    (hq : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds D (j + 1),
      (shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 ≤ Q ^ 2)
    (hm : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds D (j + 1),
      (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ M ^ 2) :
    ∀ j, j < F.top → ∑ b ∈ innerBonds D j,
      (shiftedWeight F θ p j b.1 * ‖coordinateRemainder R U f0 j b.1 b.2‖) ^ 2 ≤ 5 * (Q ^ 2 + M ^ 2) := by
  have hLpos : 0 < F.blockSide := by omega
  have hLr : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hΩ0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hLpos hθ p _ x)
  intro j
  induction j with
  | zero =>
    intro _
    have : ∀ b ∈ innerBonds D 0, (shiftedWeight F θ p 0 b.1 * ‖coordinateRemainder R U f0 0 b.1 b.2‖) ^ 2 = 0 := by
      intro b hb
      rw [h0 b hb]
      simp
    rw [Finset.sum_eq_zero this]
    positivity
  | succ j ih =>
    intro hj
    have hjn : j < F.top := by omega
    have ih' := ih hjn
    set A : F.Site j → Fin 4 → ℝ := fun x i => shiftedWeight F θ p j x * ‖coordinateRemainder R U f0 j x i‖ with hA
    have hA0 : ∀ x i, 0 ≤ A x i := fun x i => mul_nonneg (hΩ0 x) (norm_nonneg _)
    have hone : ∀ c ∈ innerBonds D (j + 1),
        (shiftedWeight F θ p (j + 1) c.1 * ‖coordinateRemainder R U f0 (j + 1) c.1 c.2‖) ^ 2 ≤
        3 * (shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 +
        3 * (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 + 3 * lineBlockAverage A c ^ 2 := by
      intro c _
      have e : coordinateRemainder R U f0 (j + 1) c.1 c.2 = stepRemainder R U j c + (U.coarse j c.1 c.2 : ℍ[ℝ]) +
          parallelAverage (R j) (coordinateRemainder R U f0 j) c := by
        have e1 : transportedForm R f0 (j + 1) c.1 c.2 = parallelAverage (R j) (transportedForm R f0 j) c := rfl
        have e2 : parallelAverage (R j) (coordinateRemainder R U f0 j) c =
            parallelAverage (R j) (levelCoordinate R U j) c -
            parallelAverage (R j) (transportedForm R f0 j) c := parallelAverage_sub _ _ _ _
        rw [e2]
        simp only [coordinateRemainder, stepRemainder, e1]
        abel
      have h1 : shiftedWeight F θ p (j + 1) c.1 * ‖coordinateRemainder R U f0 (j + 1) c.1 c.2‖ ≤
          shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖ +
            shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ +
            lineBlockAverage A c := by
        rw [e]
        have h2 := norm_add_le (stepRemainder R U j c + (U.coarse j c.1 c.2 : ℍ[ℝ]))
          (parallelAverage (R j) (coordinateRemainder R U f0 j) c)
        have h3 := norm_add_le (stepRemainder R U j c) (U.coarse j c.1 c.2 : ℍ[ℝ])
        have h4 := shiftedWeight_mul_norm_parallelAverage_le hodd (by omega) hθ p hjn (R j)
          (coordinateRemainder R U f0 j) c
        have h5 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add_left h3 _)) (hΩ0 c.1)
        rw [mul_add, mul_add] at h5
        linarith
      exact sq_le_three_mul_sum_sq (mul_nonneg (hΩ0 _) (norm_nonneg _)) h1
    refine (Finset.sum_le_sum hone).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have t1 := hq j hj
    have t2 := hm j hj
    have t3 := sum_lineBlockAverage_sq_le hjn hodd (innerBonds D (j + 1)) subset_rfl A hA0
    have hL9 : 1 / (F.blockSide : ℝ) ^ 2 ≤ 1 / 9 := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      nlinarith
    have t4 : ∑ b ∈ innerBonds D j, A b.1 b.2 ^ 2 ≤ 5 * (Q ^ 2 + M ^ 2) := ih'
    have hs0 : 0 ≤ ∑ b ∈ innerBonds D j, A b.1 b.2 ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have t5 : (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds D j, A b.1 b.2 ^ 2 ≤ (1 / 9) * (5 * (Q ^ 2 + M ^ 2)) :=
      mul_le_mul hL9 t4 hs0 (by norm_num)
    linarith
theorem le_of_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 ≤ b ^ 4) : a ≤ b :=
  le_of_not_gt fun hlt => absurd h (not_le.2 (pow_lt_pow_left₀ hlt hb (by norm_num)))
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  le_of_not_gt fun hlt => absurd h (not_le.2 (pow_lt_pow_left₀ hlt hb (by norm_num)))
theorem boundedOnAdjacentBlocks_div_shiftedWeight (hL2 : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0)
    (R : F.FieldChain) (U : ChainChart F) {j : ℕ}
    (hjn : j < F.top) (c' : F.Site (j + 1) × Fin 4) {t : ℝ}
    (hBB : BoundedOnAdjacentBlocks (fun x i => shiftedWeight F θ p j x * ‖levelCoordinate R U j x i‖) c' t) :
    BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) c' (t / shiftedWeight F θ p (j + 1) c'.1) := by
  have hL1 : 1 ≤ F.blockSide := by omega
  have hΩpos : 0 < shiftedWeight F θ p (j + 1) c'.1 :=
    lt_of_lt_of_le one_pos (one_le_shiftedWeight (by omega) hθ p _ _)
  have hhull : ∀ (x : F.Site j) (i : Fin 4) (v : Fin 4 → ℤ), (∀ i, (v i).natAbs ≤ 2 * F.blockSide) →
      x = refineSite c'.1 + siteOfCoords j v → shiftedWeight F θ p j x * ‖levelCoordinate R U j x i‖ ≤ t →
      ‖levelCoordinate R U j x i‖ ≤ t / shiftedWeight F θ p (j + 1) c'.1 := by
    intro x i v hv e hx
    rw [le_div_iff₀ hΩpos, mul_comm]
    exact (mul_le_mul_of_nonneg_right (shiftedWeight_refine_le hL2 hθ p hjn c'.1 x v hv e) (norm_nonneg _)).trans hx
  refine ⟨fun h hh k hk => ⟨?_, ?_⟩, fun h hh r hr => ?_⟩
  · exact hhull _ k h (fun i => (natAbs_le_of_mem_centredCube hL1 hh i).trans (by omega)) rfl (hBB.1 h hh k hk).1
  · refine hhull _ k ((F.blockSide : ℤ) • basisVector c'.2 + h) (natAbs_smul_basisVector_add_le hL1 hh c'.2) ?_
      (hBB.1 h hh k hk).2
    rw [refineSite_add_unitStep hjn, add_assoc, ← siteOfCoords_add]
  · exact hhull _ c'.2 (h + (r : ℤ) • basisVector c'.2)
      (natAbs_add_smul_basisVector_le hL1 hh c'.2 (Finset.mem_range.1 hr)) (lineBond_fst c' h r)
      (hBB.2 h hh r hr)
theorem stepBound_weighted_le {Ω Cs Db K t tA x2 x3 μ mis mm : ℝ} (hK : K = Cs * (1 + Db)) (hCs : 0 ≤ Cs)
    (hDb : 0 ≤ Db) (hΩt : Ω * tA = t) (htA0 : 0 ≤ tA) (htAt : tA ≤ t) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3) (hμ0 : 0 ≤ μ)
    (hmu : μ ≤ mm) (hmis : mis ≤ Db * x3) :
    Ω * (Cs * (tA ^ 2 + (x2 + μ + mis) * tA)) ≤ K * (t ^ 2 + (x2 + mm + x3) * t) := by
  have ht0 : 0 ≤ t := htA0.trans htAt
  have e : Ω * (Cs * (tA ^ 2 + (x2 + μ + mis) * tA)) = Cs * ((Ω * tA) * tA + (x2 + μ + mis) * (Ω * tA)) := by ring
  rw [e, hΩt]
  have h1 : t * tA ≤ t ^ 2 := by nlinarith
  have h2 : (x2 + μ + mis) * t ≤ (x2 + mm + Db * x3) * t := by
    refine mul_le_mul_of_nonneg_right ?_ ht0
    linarith
  have hm0 : 0 ≤ mm := hμ0.trans hmu
  have h3 : (x2 + mm + Db * x3) * t ≤ (1 + Db) * ((x2 + mm + x3) * t) := by
    have a1 : 0 ≤ Db * (x2 * t) := by positivity
    have a2 : 0 ≤ Db * (mm * t) := by positivity
    have a3 : 0 ≤ x3 * t := by positivity
    nlinarith
  have h4 : t ^ 2 ≤ (1 + Db) * t ^ 2 := by nlinarith [sq_nonneg t]
  calc Cs * (t * tA + (x2 + μ + mis) * t)
      ≤ Cs * ((1 + Db) * t ^ 2 + (1 + Db) * ((x2 + mm + x3) * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCs
        linarith
    _ = _ := by rw [hK]; ring
theorem mem_twoBlockHull_of_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    h ∈ twoBlockHull L i := by
  intro k
  have := (mem_centredCube_iff _ _).1 hh k
  have h2 : (0 : ℤ) ≤ if k = i then (L : ℤ) else 0 := by split_ifs <;> positivity
  constructor <;> omega
theorem smul_basisVector_add_mem_twoBlockHull {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    (L : ℤ) • basisVector i + h ∈ twoBlockHull L i := by
  intro k
  have := (mem_centredCube_iff _ _).1 hh k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
    have : (0 : ℤ) ≤ L := by positivity
    omega
  · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hk, smul_eq_mul, mul_zero, zero_add,
      if_neg hk, add_zero]
    omega
theorem boundedOnAdjacentBlocks_hullSum (hL : 1 ≤ F.blockSide) {j : ℕ} (a : F.Site j → Fin 4 → ℝ)
    (ha : ∀ x i, 0 ≤ a x i) (c : F.Site (j + 1) × Fin 4) (hj : j < F.top) :
    BoundedOnAdjacentBlocks a c (Real.sqrt (Real.sqrt (hullSum (fun b => a b.1 b.2 ^ 4) c))) := by
  have hs : ∀ (v : Lattice4) (k : Fin 4), v ∈ twoBlockHull F.blockSide c.2 →
      v + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      a (refineSite c.1 + siteOfCoords j v) k ≤ Real.sqrt (Real.sqrt (hullSum (fun b => a b.1 b.2 ^ 4) c)) := by
    intro v k h1 h2
    have h3 := le_hullSum hL (fun b : F.Site j × Fin 4 => a b.1 b.2 ^ 4)
      (fun b => by have := ha b.1 b.2; positivity) c k h1 h2
    simp only at h3
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
    refine le_trans (le_of_eq ?_) h3
    ring
  refine ⟨fun h hh k hk => ⟨?_, ?_⟩, fun h hh r hr => ?_⟩
  · have h1 : h + basisVector k ∈ centredCube F.blockSide := by
      have e : h + basisVector k = h + Pi.single k 1 := rfl
      rw [e]
      exact hk
    exact hs h k (mem_twoBlockHull_of_mem_centredCube hh c.2) (mem_twoBlockHull_of_mem_centredCube h1 c.2)
  · have h1 : h + basisVector k ∈ centredCube F.blockSide := hk
    have e : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
        refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector c.2 + h) := by
      rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
    rw [e]
    refine hs _ k (smul_basisVector_add_mem_twoBlockHull hh c.2) ?_
    rw [add_assoc]
    exact smul_basisVector_add_mem_twoBlockHull h1 c.2
  · have hr' := Finset.mem_range.1 hr
    have e : refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 =
        refineSite c.1 + siteOfCoords j (h + (r : ℤ) • basisVector c.2) := lineBond_fst c h r
    rw [e]
    refine hs _ c.2 (add_smul_basisVector_mem_twoBlockHull hh c.2 hr'.le) ?_
    have e2 : h + (r : ℤ) • basisVector c.2 + basisVector c.2 = h + ((r + 1 : ℕ) : ℤ) • basisVector c.2 := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e2]
    exact add_smul_basisVector_mem_twoBlockHull hh c.2 hr'
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem sq_le_of_le_quadratic {a K τ x2 x3 mm T : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx : x3 ≤ x2) (hm : 0 ≤ mm) (hτT : τ ≤ T) (h : a ≤ K * (τ ^ 2 + (x2 + mm + x3) * τ)) :
    a ^ 2 ≤ 3 * K ^ 2 * (τ ^ 4 + 4 * x2 ^ 2 * τ ^ 2 + T ^ 2 * mm ^ 2) := by
  have h1 := pow_le_pow_left₀ ha h 2
  refine h1.trans ?_
  rw [mul_pow, mul_assoc 3]
  have e : τ ^ 2 + (x2 + mm + x3) * τ = τ ^ 2 + (x2 + x3) * τ + mm * τ := by ring
  rw [e]
  have h2 : (τ ^ 2 + (x2 + x3) * τ + mm * τ) ^ 2 ≤ 3 * (τ ^ 4 + ((x2 + x3) * τ) ^ 2 + (mm * τ) ^ 2) := by
    nlinarith [sq_nonneg (τ ^ 2 - (x2 + x3) * τ), sq_nonneg (τ ^ 2 - mm * τ), sq_nonneg ((x2 + x3) * τ - mm * τ)]
  have h3 : ((x2 + x3) * τ) ^ 2 ≤ 4 * x2 ^ 2 * τ ^ 2 := by
    rw [mul_pow]
    have : (x2 + x3) ^ 2 ≤ (2 * x2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h4 := mul_le_mul_of_nonneg_right this (sq_nonneg τ)
    nlinarith
  have h5 : (mm * τ) ^ 2 ≤ T ^ 2 * mm ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ hτT 2) (sq_nonneg _)
  have h6 : (τ ^ 2 + (x2 + x3) * τ + mm * τ) ^ 2 ≤ 3 * (τ ^ 4 + 4 * x2 ^ 2 * τ ^ 2 + T ^ 2 * mm ^ 2) := by linarith
  have h7 := mul_le_mul_of_nonneg_left h6 (sq_nonneg K)
  linarith
theorem sum_weighted_stepRemainder_sq_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) {D : Finset F.Cell} {R : F.FieldChain}
    {U : ChainChart F} {j : ℕ} (hjn : j + 1 < F.top) {Cs cs Db s B Mb T H : ℝ} (hCs : 0 ≤ Cs) (hDb : 0 ≤ Db)
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hMb : 0 ≤ Mb) (hT0 : 0 ≤ T) (hH : 16 * ((hullBox F.blockSide).card : ℝ) ≤ H)
    (hT : H * B ^ 4 ≤ T ^ 4) (hTc : T ≤ cs) (hMc : Mb ≤ cs)
    (hstep : ∀ b ∈ innerBonds D (j + 1), ∀ t : ℝ, 0 ≤ t → t ≤ cs → ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ ≤ cs →
      BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) b t →
      ‖stepRemainder R U j b‖ ≤ Cs * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 +
        ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ + ‖((referenceDefect R j b : UnitQuaternion) : ℍ[ℝ]) - 1‖) * t))
    (hmis : ∀ b ∈ innerBonds D (j + 1), ‖((referenceDefect R j b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      Db * (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3))
    (hW : ∑ b ∈ innerBonds D j, (shiftedWeight F θ p j b.1 * ‖levelCoordinate R U j b.1 b.2‖) ^ 4 ≤ B ^ 4)
    (hM : ∑ c ∈ innerBonds D (j + 1),
      (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ Mb ^ 2)
    (hcard : ((innerBonds D (j + 1)).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4) :
    ∑ c ∈ innerBonds D (j + 1), (shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 ≤
      3 * (Cs * (1 + Db)) ^ 2 * (H * B ^ 4 + 200 * s ^ 2 * (1 + H) * B ^ 2 + T ^ 2 * Mb ^ 2) := by
  classical
  have hLpos : 0 < F.blockSide := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hL1r : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  have hjn' : j < F.top := by omega
  have hΩ1 : ∀ {j : ℕ} (x : F.Site j), 1 ≤ shiftedWeight F θ p j x := fun x => one_le_shiftedWeight hLpos hθ p _ x
  have hΩ0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x => zero_le_one.trans (hΩ1 x)
  set l : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := pow_le_one₀ (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1r)
  set M : ℝ := (F.blockSide : ℝ) ^ (F.top - (j + 1)) with hMdef
  have hlM : l * M = 1 := by
    rw [hl, hMdef, ← mul_pow, one_div, inv_mul_cancel₀ hLr.ne', one_pow]
  set a : F.Site j → Fin 4 → ℝ := fun x i => shiftedWeight F θ p j x * ‖levelCoordinate R U j x i‖ with ha
  have ha0 : ∀ x i, 0 ≤ a x i := fun x i => mul_nonneg (hΩ0 x) (norm_nonneg _)
  set g : F.Site j × Fin 4 → ℝ := fun b => a b.1 b.2 ^ 4 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => by
    have := ha0 b.1 b.2
    positivity
  set τ : F.Site (j + 1) × Fin 4 → ℝ := fun c => Real.sqrt (Real.sqrt (hullSum g c)) with hτ
  have hτ0 : ∀ c, 0 ≤ τ c := fun c => Real.sqrt_nonneg _
  have hh0 : ∀ c, 0 ≤ hullSum g c := fun c => by
    unfold hullSum
    refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
    split_ifs
    · exact hg0 _
    · exact le_rfl
  have hτ4 : ∀ c, τ c ^ 4 = hullSum g c := fun c => sqrt_sqrt_pow_four (hh0 c)
  have hsum4 : ∑ c ∈ innerBonds D (j + 1), τ c ^ 4 ≤ H * B ^ 4 := by
    simp only [hτ4]
    refine (sum_hullSum_le hjn' hodd (innerBonds D (j + 1)) subset_rfl g hg0).trans ?_
    exact mul_le_mul hH hW (Finset.sum_nonneg fun _ _ => hg0 _)
      ((by positivity : (0 : ℝ) ≤ 16 * ((hullBox F.blockSide).card : ℝ)).trans hH)
  have hτT : ∀ c ∈ innerBonds D (j + 1), τ c ≤ T := by
    intro c hc
    have h1 := Finset.single_le_sum (f := fun c => τ c ^ 4) (fun c _ => by have := hτ0 c; positivity) hc
    exact le_of_pow_four_le (hτ0 c) hT0 (h1.trans (hsum4.trans hT))
  set mm : F.Site (j + 1) × Fin 4 → ℝ := fun c => shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖
    with hmm
  have hmm0 : ∀ c, 0 ≤ mm c := fun c => mul_nonneg (hΩ0 _) (norm_nonneg _)
  have hmmM : ∀ c ∈ innerBonds D (j + 1), mm c ≤ Mb := by
    intro c hc
    have h1 := Finset.single_le_sum (f := fun c => mm c ^ 2) (fun c _ => by positivity) hc
    exact le_of_sq_le_sq_of_nonneg (hmm0 c) hMb (h1.trans hM)
  have hone : ∀ c ∈ innerBonds D (j + 1), (shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 ≤
      3 * (Cs * (1 + Db)) ^ 2 * (τ c ^ 4 + 4 * (s * l ^ 2) ^ 2 * τ c ^ 2 + T ^ 2 * mm c ^ 2) := by
    intro c hc
    have hΩp : 0 < shiftedWeight F θ p (j + 1) c.1 := lt_of_lt_of_le one_pos (hΩ1 _)
    have hBB := boundedOnAdjacentBlocks_div_shiftedWeight hL (hθ) p R U hjn' c
      (boundedOnAdjacentBlocks_hullSum (by omega) a ha0 c hjn')
    have hτc : τ c / shiftedWeight F θ p (j + 1) c.1 ≤ τ c := div_le_self (hτ0 c) (hΩ1 _)
    have htA0 : 0 ≤ τ c / shiftedWeight F θ p (j + 1) c.1 := div_nonneg (hτ0 c) hΩp.le
    have hμmm : ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ mm c := le_mul_of_one_le_left (norm_nonneg _) (hΩ1 _)
    have h1 := hstep c hc _ htA0 (hτc.trans ((hτT c hc).trans hTc)) (hμmm.trans ((hmmM c hc).trans hMc)) hBB
    have h2 := mul_le_mul_of_nonneg_left h1 hΩp.le
    have hΩt : shiftedWeight F θ p (j + 1) c.1 * (τ c / shiftedWeight F θ p (j + 1) c.1) = τ c := by
      field_simp
    have h3 := stepBound_weighted_le (Cs := Cs) (Db := Db) (K := Cs * (1 + Db)) rfl hCs hDb hΩt htA0 hτc
      (x2 := s * l ^ 2) (x3 := s * l ^ 3) (by positivity) (by positivity) (norm_nonneg _) hμmm (hmis c hc)
    have hx : s * l ^ 3 ≤ s * l ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hl0 hl1 (by norm_num)) hs
    exact sq_le_of_le_quadratic (mul_nonneg hΩp.le (norm_nonneg _)) (by positivity) (hτ0 c) (by positivity)
      (by positivity) hx (hmm0 c) (hτT c hc) (h2.trans h3)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hH0 : 0 ≤ H := (by positivity : (0 : ℝ) ≤ 16 * ((hullBox F.blockSide).card : ℝ)).trans hH
  have hsq : (∑ c ∈ innerBonds D (j + 1), τ c ^ 2) ^ 2 ≤ (50 * M ^ 2 * (1 + H) * B ^ 2) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := innerBonds D (j + 1)) (f := fun c => τ c ^ 2)
    have h2 : ∑ c ∈ innerBonds D (j + 1), (τ c ^ 2) ^ 2 ≤ H * B ^ 4 := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) hsum4
      ring
    have h3 := mul_le_mul hcard h2 (Finset.sum_nonneg fun c _ => by positivity) (by positivity)
    refine h1.trans (h3.trans ?_)
    have h4 : H ≤ (1 + H) ^ 2 := by nlinarith
    have h5 : 0 ≤ 2500 * M ^ 4 * B ^ 4 := by positivity
    have h6 := mul_le_mul_of_nonneg_right h4 h5
    nlinarith
  have hS2 : ∑ c ∈ innerBonds D (j + 1), τ c ^ 2 ≤ 50 * M ^ 2 * (1 + H) * B ^ 2 :=
    le_of_sq_le_sq_of_nonneg (Finset.sum_nonneg fun c _ => by positivity) (by positivity) hsq
  have hx2 : 4 * (s * l ^ 2) ^ 2 * ∑ c ∈ innerBonds D (j + 1), τ c ^ 2 ≤ 200 * s ^ 2 * (1 + H) * B ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hS2 (by positivity : (0 : ℝ) ≤ 4 * (s * l ^ 2) ^ 2)
    refine h1.trans ?_
    have e : 4 * (s * l ^ 2) ^ 2 * (50 * M ^ 2 * (1 + H) * B ^ 2) =
        200 * s ^ 2 * (1 + H) * B ^ 2 * (l ^ 2 * (l * M) ^ 2) := by
      ring
    rw [e, hlM, one_pow, mul_one]
    have h2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
    exact mul_le_of_le_one_right (by positivity) h2
  have hx3 : T ^ 2 * ∑ c ∈ innerBonds D (j + 1), mm c ^ 2 ≤ T ^ 2 * Mb ^ 2 :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  linarith
theorem nearPoint_input_bounds (hodd : Odd F.blockSide) {θ del : ℝ} (hθ : 0 ≤ θ) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (p : F.Site 0) {β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ y0 : F.Cell, weightedNorm S R U (decayWeights F del θ p y0) ≤ β) :
    (∑ b ∈ innerBonds (cellsNearPoint S p) 0,
        (shiftedWeight F θ p 0 b.1 * ‖(U.fine b.1 b.2 : ℍ[ℝ])‖) ^ 4 ≤ (25 * β) ^ 4) ∧
      (∀ j, j + 1 < F.top → ∑ c ∈ innerBonds (cellsNearPoint S p) (j + 1),
        (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ (25 * β) ^ 2) ∧
      (∑ q ∈ innerPlaquettes (cellsNearPoint S p) 0,
        (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt (R 0) (fun x i => (U.fine x i : ℍ[ℝ])) q‖) ^ 2 ≤
          (25 * β) ^ 2) ∧
      ∀ b ∈ innerBonds S 0, ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ≤ β := by
  classical
  have hL := hodd.pos
  have hsub : cellsNearPoint S p ⊆ S := Finset.filter_subset _ _
  have hcard : ((cellsNearPoint S p).card : ℝ) ≤ 625 := by exact_mod_cast card_cellsNearPoint_le S p
  have hparts : ∀ z ∈ S, _ := fun z hz => localNorm_parts_le S R U (decayWeights F del θ p z) z hβ
    ((localNorm_le_weightedNorm S R U _ hz).trans (hN z))
  have hw : ∀ (z : F.Cell) {j : ℕ} (x : F.Site j), enclosingCell x = z →
      shiftedWeight F θ p j x ≤ decayWeights F del θ p z j x := by
    intro z j x hc
    have := shiftedWeight_le_exp_mul_decayWeights hL hθ del p z j x
    rw [hc, BlockLines.cellSupDist_self] at this
    simpa using this
  have hw0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hL hθ p _ x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (sum_innerBonds_le_sum_cells hodd hsub 0 _ fun _ => by positivity).trans ?_
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ b ∈ bondsOver S {z} 0,
        (shiftedWeight F θ p 0 b.1 * ‖(U.fine b.1 b.2 : ℍ[ℝ])‖) ^ 4 ≤ β ^ 4 := by
      intro z hz
      have hzS := hsub hz
      refine le_trans ?_ (hparts z hzS).1
      refine le_trans (Finset.sum_le_sum fun b hb => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset hzS 0)
          fun _ _ _ => Even.pow_nonneg (by decide) _)
      have hc : enclosingCell b.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hb).2
      exact pow_le_pow_left₀ (mul_nonneg (hw0 b.1) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hw z b.1 hc) (norm_nonneg _)) 4
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb4 : 0 ≤ β ^ 4 := by positivity
    nlinarith
  · intro j hj
    refine (sum_innerBonds_le_sum_cells hodd hsub (j + 1) _ fun _ => by positivity).trans ?_
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ c ∈ bondsOver S {z} (j + 1),
        (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ β ^ 2 := by
      intro z hz
      have hzS := hsub hz
      refine le_trans ?_ ((hparts z hzS).2.2 j hj)
      refine le_trans (Finset.sum_le_sum fun b hb => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (bondsOver_singleton_subset hzS (j + 1))
          fun _ _ _ => Even.pow_nonneg (by decide) _)
      have hc : enclosingCell b.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hb).2
      exact pow_le_pow_left₀ (mul_nonneg (hw0 b.1) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hw z b.1 hc) (norm_nonneg _)) 2
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb2 : 0 ≤ β ^ 2 := by positivity
    nlinarith
  · have hmaps : ∀ q ∈ innerPlaquettes (cellsNearPoint S p) 0, enclosingCell q.1 ∈ cellsNearPoint S p := fun q hq =>
      enclosingCell_mem hodd ((Finset.mem_filter.1 hq).2.2 (by simp [plaquetteCorners]))
    have ecurl : ∀ q, covariantCurlAt (R 0) (fun x i => (U.fine x i : ℍ[ℝ])) q = linearizedCurl (R 0) U.fine q :=
      fun q => rfl
    simp only [ecurl]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have h1 : ∀ z ∈ cellsNearPoint S p, ∑ q ∈ innerPlaquettes (cellsNearPoint S p) 0 with enclosingCell q.1 = z,
        (shiftedWeight F θ p 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤ β ^ 2 := by
      intro z hz
      have hzS := hsub hz
      have hp2 := (hparts z hzS).2.1
      have hss : (innerPlaquettes (cellsNearPoint S p) 0).filter (fun q => enclosingCell q.1 = z) ⊆
          plaquettesOver S (cellBall S z 3) 0 := by
        intro q hq
        obtain ⟨h2, h3⟩ := Finset.mem_filter.1 hq
        obtain ⟨h4, h5, h6⟩ := Finset.mem_filter.1 h2
        refine Finset.mem_filter.2 ⟨?_, by rw [h3]; exact singleton_subset_cellBall hzS (by simp)⟩
        refine Finset.mem_filter.2 ⟨?_, h5, h6.trans (sitesOfCells_mono hsub 0)⟩
        obtain ⟨h7, h8⟩ := Finset.mem_product.1 h4
        exact Finset.mem_product.2 ⟨sitesOfCells_mono hsub 0 h7, h8⟩
      have hs1 : ∑ q ∈ innerPlaquettes (cellsNearPoint S p) 0 with enclosingCell q.1 = z,
          (decayWeights F del θ p z 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
          ∑ q ∈ plaquettesOver S (cellBall S z 3) 0,
            (decayWeights F del θ p z 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hss fun _ _ _ => Even.pow_nonneg (by decide) _
      refine le_trans (Finset.sum_le_sum fun q hq => ?_) (hs1.trans hp2)
      have hc : enclosingCell q.1 = z := (Finset.mem_filter.1 hq).2
      exact pow_le_pow_left₀ (mul_nonneg (hw0 q.1) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hw z q.1 hc) (norm_nonneg _)) 2
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb2 : 0 ≤ β ^ 2 := by positivity
    nlinarith
  · intro b hb
    have hz : enclosingCell b.1 ∈ S := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
      exact enclosingCell_mem hodd hb.1.1
    have hb' : b ∈ bondsOver S {enclosingCell b.1} 0 := Finset.mem_filter.2 ⟨hb, by simp⟩
    have h1 := Finset.single_le_sum (f := fun b' : F.Site 0 × Fin 4 =>
      (decayWeights F del θ p (enclosingCell b.1) 0 b'.1 * ‖U.fine b'.1 b'.2‖) ^ 4)
      (fun _ _ => Even.pow_nonneg (by decide) _) (bondsOver_singleton_subset hz 0 hb')
    have h2 := h1.trans (hparts _ hz).1
    have h4 := one_le_decayWeights_self hL hθ del p 0 b.1
    have h5 : (0 : ℝ) ≤ ‖U.fine b.1 b.2‖ := norm_nonneg _
    have h3 : decayWeights F del θ p (enclosingCell b.1) 0 b.1 * ‖U.fine b.1 b.2‖ ≤ β :=
      le_of_pow_four_le (mul_nonneg (by linarith) h5) hβ h2
    calc ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ = ‖U.fine b.1 b.2‖ := rfl
      _ ≤ _ := le_mul_of_one_le_left h5 h4
      _ ≤ β := h3
theorem plaquette_mem_near_baseSite (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {S : Finset F.Cell}
    {q : F.Site F.depth × Fin 4 × Fin 4}
    (hq : q ∈ innerPlaquettes S F.depth) : q ∈ innerPlaquettes (cellsNearPoint S (baseSite q.1)) F.depth ∧
      baseDistance q.1 (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth ∧
      baseDistance (q.1 + unitStep F.depth q.2.1) (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth ∧
      baseDistance (q.1 + unitStep F.depth q.2.2) (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth := by
  classical
  obtain ⟨h1, hlt, hc⟩ := Finset.mem_filter.1 hq
  have hN : 2 * (2 * F.blockSide ^ F.depth) ≤ 3 * F.blockSide ^ F.top := by
    have e : F.blockSide ^ F.top = F.blockSide ^ F.depth * F.blockSide := pow_succ _ _
    rw [e]
    nlinarith [Nat.zero_le (F.blockSide ^ F.depth)]
  have h0 : baseDistance q.1 (baseSite q.1) = 0 := by
    simp [baseDistance]
  have htn : F.depth ≤ F.top := Nat.le_succ _
  have hd : ∀ x ∈ plaquetteCorners q, baseDistance x (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth := by
    intro x hx
    have s1 := baseDistance_add_unitStep_le htn q.1 q.2.1 (baseSite q.1)
    have s2 := baseDistance_add_unitStep_le htn q.1 q.2.2 (baseSite q.1)
    have s3 := baseDistance_add_unitStep_le htn (q.1 + unitStep F.depth q.2.1) q.2.2 (baseSite q.1)
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  have hs : ∀ x ∈ plaquetteCorners q, x ∈ sitesOfCells (cellsNearPoint S (baseSite q.1)) F.depth := by
    intro x hx
    have hxS := hc hx
    refine mem_sitesOfCells_of_enclosingCell_mem hodd hxS (Finset.mem_filter.2 ⟨enclosingCell_mem hodd hxS, ?_⟩)
    refine cellSupDist_enclosingCell_le_two hodd htn hxS _ ?_
    have := hd x hx
    omega
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs _ (by simp [plaquetteCorners]),
      (Finset.mem_product.1 h1).2⟩, hlt, hs⟩,
    hd _ (by simp [plaquetteCorners]), hd _ (by simp [plaquetteCorners]), hd _ (by simp [plaquetteCorners])⟩
theorem inv_shiftedWeight_le_of_baseDistance_le (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (hθ8 : θ ≤ 1 / 8)
    (p : F.Site 0) (x : F.Site F.depth) (hd : baseDistance x p ≤ 2 * F.blockSide ^ F.depth) :
    (shiftedWeight F θ p F.depth x)⁻¹ ≤ 3 * (1 / (F.blockSide : ℝ)) ^ θ := by
  have hd' : (baseDistance x p : ℝ) ≤ 2 * (F.blockSide : ℝ) ^ F.depth := by exact_mod_cast hd
  have h1 := rpow_le_shiftedWeight hL hθ p x (r := 6 * (F.blockSide : ℝ) ^ F.depth) (by linarith)
  have e : 6 * (F.blockSide : ℝ) ^ F.depth / (F.blockSide : ℝ) ^ F.top = 6 * (1 / (F.blockSide : ℝ)) := by
    have : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ F.depth * F.blockSide := pow_succ _ _
    rw [this]
    field_simp
  rw [e] at h1
  have hp : 0 < (6 * (1 / (F.blockSide : ℝ))) ^ (-θ) := Real.rpow_pos_of_pos (by positivity) _
  have h2 := inv_anti₀ hp h1
  refine h2.trans ?_
  rw [Real.rpow_neg (by positivity), inv_inv, Real.mul_rpow (by norm_num) (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (6 : ℝ) ^ θ ≤ 6 ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ8
    _ ≤ 3 := by
      have h3 : ((6 : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = 6 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      by_contra hc
      have h4 : (3 : ℝ) ^ 8 < ((6 : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℕ) :=
        pow_lt_pow_left₀ (not_le.1 hc) (by norm_num) (by norm_num)
      rw [h3] at h4
      norm_num at h4
theorem plaquette_edges_mem_innerBonds {D : Finset F.Cell} {j : ℕ} {q : F.Site j × Fin 4 × Fin 4}
    (hq : q ∈ innerPlaquettes D j) :
    (q.1, q.2.1) ∈ innerBonds D j ∧ (q.1 + unitStep j q.2.1, q.2.2) ∈ innerBonds D j ∧
      (q.1 + unitStep j q.2.2, q.2.1) ∈ innerBonds D j ∧ (q.1, q.2.2) ∈ innerBonds D j := by
  have hc := (Finset.mem_filter.1 hq).2.2
  have c1 : q.1 ∈ sitesOfCells D j := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep j q.2.1 ∈ sitesOfCells D j := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep j q.2.2 ∈ sitesOfCells D j := hc (by simp [plaquetteCorners])
  have c4 : q.1 + unitStep j q.2.1 + unitStep j q.2.2 ∈ sitesOfCells D j := hc (by simp [plaquetteCorners])
  refine ⟨ChartCoordinates.mem_innerBonds c1 c2, ChartCoordinates.mem_innerBonds c2 c4,
    ChartCoordinates.mem_innerBonds c3 ?_, ChartCoordinates.mem_innerBonds c1 c3⟩
  rwa [add_right_comm]
theorem plaquetteDefect_chartField_le (R : F.FieldChain) (U : ChainChart F) (q : F.Site F.depth × Fin 4 × Fin 4)
    (h1 : ‖levelCoordinate R U F.depth q.1 q.2.1‖ ≤ 1)
    (h2 : ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ ≤ 1)
    (h3 : ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ ≤ 1)
    (h4 : ‖levelCoordinate R U F.depth q.1 q.2.2‖ ≤ 1) :
    plaquetteDefect (chartField R U F.depth) q ≤ plaquetteDefect (R F.depth) q +
      ‖covariantCurlAt (R F.depth) (levelCoordinate R U F.depth) q‖ +
      9 * (‖levelCoordinate R U F.depth q.1 q.2.1‖ ^ 2 +
        ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ ^ 2 +
        ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ ^ 2 +
        ‖levelCoordinate R U F.depth q.1 q.2.2‖ ^ 2) := by
  have hp := plaquetteDefect_le_add_curl (chartField R U F.depth) (R F.depth) q
  have hc := norm_covariantCurlAt_sub_le (R F.depth)
    (fun x i => pureComponent ((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ])) (levelCoordinate R U F.depth) q
  have hd : ∀ x i, ‖levelCoordinate R U F.depth x i‖ ≤ 1 →
      ‖pureComponent ((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ]) - levelCoordinate R U F.depth x i‖ ≤
      ‖levelCoordinate R U F.depth x i‖ ^ 2 := by
    intro x i h
    have := norm_pureComponent_exp_sub_self_le (re_unitQuaternionLog (chartGap R U F.depth x i)) h
    rwa [exp_unitQuaternionLog] at this
  have hg : ∀ x i, ‖((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖levelCoordinate R U F.depth x i‖ :=
    fun x i => norm_coe_sub_one_le_norm_unitQuaternionLog _
  have hcc : ‖covariantCurlAt (R F.depth)
      (fun x i => pureComponent ((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ])) q‖ ≤
      ‖covariantCurlAt (R F.depth) (levelCoordinate R U F.depth) q‖ + (‖levelCoordinate R U F.depth q.1 q.2.1‖ ^ 2 +
        ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ ^ 2 +
        ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ ^ 2 +
        ‖levelCoordinate R U F.depth q.1 q.2.2‖ ^ 2) := by
    have := norm_sub_norm_le (covariantCurlAt (R F.depth)
      (fun x i => pureComponent ((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ])) q)
      (covariantCurlAt (R F.depth) (levelCoordinate R U F.depth) q)
    have a1 := hd _ _ h1
    have a2 := hd _ _ h2
    have a3 := hd _ _ h3
    have a4 := hd _ _ h4
    linarith
  set a := ‖levelCoordinate R U F.depth q.1 q.2.1‖ with ha
  set b := ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ with hb
  set c := ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ with hcdef
  set d := ‖levelCoordinate R U F.depth q.1 q.2.2‖ with hddef
  have hsum : ‖((chartGap R U F.depth q.1 q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth q.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a + b + c + d :=
    add_le_add (add_le_add (add_le_add (hg _ _) (hg _ _)) (hg _ _)) (hg _ _)
  have h0 : 0 ≤ ‖((chartGap R U F.depth q.1 q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
      ‖((chartGap R U F.depth q.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by positivity
  have hsq := pow_le_pow_left₀ h0 hsum 2
  have h4' : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (c - d)]
  have hp' : plaquetteDefect (chartField R U F.depth) q ≤ plaquetteDefect (R F.depth) q +
      ‖covariantCurlAt (R F.depth)
        (fun x i => pureComponent ((chartGap R U F.depth x i : UnitQuaternion) : ℍ[ℝ])) q‖ +
      2 * (‖((chartGap R U F.depth q.1 q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((chartGap R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((chartGap R U F.depth q.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖) ^ 2 := hp
  linarith
theorem plaquetteDefect_final_arith {cv cR cf cC r1 r2 r3 r4 f4 Ωi lam s β Q M Cc Kq Cw Db L2 : ℝ} (hs0 : 0 ≤ s)
    (hsβ : s ≤ β) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hCc : 0 ≤ Cc) (hKq : 0 ≤ Kq) (hDb : 0 ≤ Db) (hL2 : 0 < L2)
    (hv : cv ≤ cR + cf + 9 * f4) (hcR : cR ≤ Db * s / L2) (hcf : cf ≤ cC + (r1 + r2 + r3 + r4))
    (hcC : cC ≤ Ωi * (2 * (25 * β)) + Cc * s * (25 * β)) (hΩi : Ωi ≤ 3 * lam)
    (h1 : r1 ≤ 9 * lam * (Q + M)) (h2 : r2 ≤ 9 * lam * (Q + M)) (h3 : r3 ≤ 9 * lam * (Q + M))
    (h4 : r4 ≤ 9 * lam * (Q + M))
    (hf4 : f4 ≤ 4 * (Cw * β) ^ 2) (hQ : Q = Kq * β ^ 2) (hM : M = 25 * β) :
    cv ≤ (Db + 1050) * s / L2 + (Db + 1050) * lam * β + (25 * Cc + 36 * Kq + 36 * Cw ^ 2) * β ^ 2 := by
  have hβ0 : 0 ≤ β := hs0.trans hsβ
  have a0 : Ωi * (2 * (25 * β)) ≤ 3 * lam * (2 * (25 * β)) := mul_le_mul_of_nonneg_right hΩi (by positivity)
  have a1 : Cc * s * (25 * β) ≤ Cc * β * (25 * β) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsβ hCc) (by positivity)
  have a2 : lam * (Kq * β ^ 2) ≤ 1 * (Kq * β ^ 2) := mul_le_mul_of_nonneg_right hlam1 (by positivity)
  have a3 : Db * s / L2 ≤ (Db + 1050) * s / L2 := by
    refine div_le_div_of_nonneg_right ?_ hL2.le
    have : 0 ≤ 1050 * s := by positivity
    nlinarith
  have a4 : 0 ≤ Db * lam * β := by positivity
  rw [hQ, hM] at h1 h2 h3 h4
  nlinarith
theorem sum_weighted_stepRemainder_sq_le_all (hodd : Odd F.blockSide) (hL2 : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) {S : Finset F.Cell} {R : F.FieldChain}
    {U : ChainChart F} {Cs cs Db s β Cw T0 H Kq : ℝ} (hCs : 0 ≤ Cs) (hDb : 0 ≤ Db) (hs : 0 ≤ s) (hsβ : s ≤ β)
    (hCw : 0 ≤ Cw) (hT0 : 0 ≤ T0) (hT0def : T0 = (1 + H) * Cw) (hH0 : 0 ≤ H)
    (hHdef : 16 * ((hullBox F.blockSide).card : ℝ) ≤ H) (hTc : T0 * β ≤ cs) (hMc : 25 * β ≤ cs)
    (hKq : 3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) ≤ Kq ^ 2)
    (hstep : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ∀ t : ℝ, 0 ≤ t → t ≤ cs →
      ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ ≤ cs →
      BoundedOnAdjacentBlocks (fun x i => ‖levelCoordinate R U j x i‖) b t →
      ‖stepRemainder R U j b‖ ≤ Cs * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 +
        ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ + ‖((referenceDefect R j b : UnitQuaternion) : ℍ[ℝ]) - 1‖) * t))
    (hmis : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      ‖((referenceDefect R j b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      Db * (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3))
    (hW : ∀ j, j < F.top → ∑ b ∈ innerBonds (cellsNearPoint S p) j,
      (shiftedWeight F θ p j b.1 * ‖levelCoordinate R U j b.1 b.2‖) ^ 4 ≤ (Cw * β) ^ 4)
    (hM : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds (cellsNearPoint S p) (j + 1),
      (shiftedWeight F θ p (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ (25 * β) ^ 2) :
    ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds (cellsNearPoint S p) (j + 1),
      (shiftedWeight F θ p (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 ≤ (Kq * β ^ 2) ^ 2 := by
  intro j hj
  have hβ0 : 0 ≤ β := hs.trans hsβ
  have hDS : cellsNearPoint S p ⊆ S := Finset.filter_subset _ _
  have hcard : ((innerBonds (cellsNearPoint S p) (j + 1)).card : ℝ) ≤
      2500 * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4 := by
    have h2 := card_innerBonds_le hodd (cellsNearPoint S p) (j + 1)
    have h3 : (cellsNearPoint S p).card * (F.blockSide ^ (F.top - (j + 1))) ^ 4 ≤
        625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4 :=
      Nat.mul_le_mul_right _ (card_cellsNearPoint_le S _)
    have h4 : (innerBonds (cellsNearPoint S p) (j + 1)).card ≤ 4 * (625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) :=
      h2.trans (Nat.mul_le_mul_left 4 h3)
    have h5 : ((innerBonds (cellsNearPoint S p) (j + 1)).card : ℝ) ≤
        ((4 * (625 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast h4
    refine h5.trans (le_of_eq ?_)
    push_cast
    ring
  have hT : H * (Cw * β) ^ 4 ≤ (T0 * β) ^ 4 := by
    rw [hT0def]
    have h1 : H ≤ (1 + H) ^ 4 := by nlinarith [sq_nonneg ((1 + H) ^ 2 - 1), sq_nonneg H]
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (Cw * β) ^ 4)
    refine h2.trans (le_of_eq ?_)
    ring
  have hst := sum_weighted_stepRemainder_sq_le (Cs := Cs) (cs := cs) (Db := Db) (s := s) (B := Cw * β)
    (Mb := 25 * β) (T := T0 * β) (H := H)
    (R := R) (U := U) (D := cellsNearPoint S p) hodd hL2 hθ p hj hCs hDb hs
    (by positivity) (by positivity) (by positivity) hHdef hT hTc hMc
    (fun b hb t ht0 htc hmu hBB => hstep j hj b (innerBonds_mono hDS _ hb) t ht0 htc hmu hBB)
    (fun b hb => hmis j hj b (innerBonds_mono hDS _ hb)) (hW j (by omega)) (hM j hj) hcard
  refine hst.trans ?_
  have e : 3 * (Cs * (1 + Db)) ^ 2 * (H * (Cw * β) ^ 4 + 200 * s ^ 2 * (1 + H) * (Cw * β) ^ 2 +
      (T0 * β) ^ 2 * (25 * β) ^ 2) ≤
      3 * (Cs * (1 + Db)) ^ 2 * ((H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) * β ^ 4) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : s ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hs hsβ 2
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 200 * (1 + H) * (Cw * β) ^ 2)
    nlinarith
  refine e.trans ?_
  have h2 := mul_le_mul_of_nonneg_right hKq (by positivity : (0 : ℝ) ≤ β ^ 4)
  calc _ = 3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) * β ^ 4 := by ring
    _ ≤ Kq ^ 2 * β ^ 4 := h2
    _ = _ := by ring
theorem norm_le_of_sum_pow_four_le (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) {D : Finset F.Cell} {j : ℕ}
    (p : F.Site 0) (g : F.Site j → Fin 4 → ℍ[ℝ]) {B : ℝ} (hB : 0 ≤ B)
    (hW : ∑ b ∈ innerBonds D j, (shiftedWeight F θ p j b.1 * ‖g b.1 b.2‖) ^ 4 ≤ B ^ 4) :
    ∀ b ∈ innerBonds D j, ‖g b.1 b.2‖ ≤ B := by
  intro b hb
  have hΩ1 : ∀ x : F.Site j, 1 ≤ shiftedWeight F θ p j x := fun x => one_le_shiftedWeight hL hθ _ _ x
  have h1 := Finset.single_le_sum
    (f := fun b : F.Site j × Fin 4 => (shiftedWeight F θ p j b.1 * ‖g b.1 b.2‖) ^ 4)
    (fun _ _ => Even.pow_nonneg (by decide) _) hb
  have h2 := h1.trans hW
  have h3 := le_of_pow_four_le (mul_nonneg (zero_le_one.trans (hΩ1 _)) (norm_nonneg _)) hB h2
  exact (le_mul_of_one_le_left (norm_nonneg _) (hΩ1 _)).trans h3
theorem norm_le_of_sum_sq_le (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) {D : Finset F.Cell} {j : ℕ}
    (p : F.Site 0) (g : F.Site j → Fin 4 → ℍ[ℝ]) {Q M w : ℝ} (hQ0 : 0 ≤ Q) (hM0 : 0 ≤ M) (hw0 : 0 ≤ w)
    (hsum : ∑ b ∈ innerBonds D j, (shiftedWeight F θ p j b.1 * ‖g b.1 b.2‖) ^ 2 ≤ 5 * (Q ^ 2 + M ^ 2))
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds D j) (hw : (shiftedWeight F θ p j b.1)⁻¹ ≤ w) :
    ‖g b.1 b.2‖ ≤ w * (3 * (Q + M)) := by
  have hΩ1 : ∀ x : F.Site j, 1 ≤ shiftedWeight F θ p j x := fun x => one_le_shiftedWeight hL hθ _ _ x
  have h1 := Finset.single_le_sum
    (f := fun b : F.Site j × Fin 4 => (shiftedWeight F θ p j b.1 * ‖g b.1 b.2‖) ^ 2)
    (fun _ _ => Even.pow_nonneg (by decide) _) hb
  have h2 := h1.trans hsum
  have h3 : 5 * (Q ^ 2 + M ^ 2) ≤ (3 * (Q + M)) ^ 2 := by nlinarith [mul_nonneg hQ0 hM0]
  have h4 := le_of_sq_le_sq_of_nonneg (mul_nonneg (zero_le_one.trans (hΩ1 _)) (norm_nonneg _)) (by positivity)
    (h2.trans h3)
  have hΩp : 0 < shiftedWeight F θ p j b.1 := lt_of_lt_of_le one_pos (hΩ1 _)
  have h6 : ‖g b.1 b.2‖ = (shiftedWeight F θ p j b.1)⁻¹ * (shiftedWeight F θ p j b.1 * ‖g b.1 b.2‖) := by
    field_simp
  rw [h6]
  exact mul_le_mul hw h4 (mul_nonneg (zero_le_one.trans (hΩ1 _)) (norm_nonneg _)) hw0
theorem plaquetteDefect_chartField_bound (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) {θ : ℝ} (hθ : 0 < θ)
    (hθ8 : θ ≤ 1 / 8) {D : Finset F.Cell}
    {R : F.FieldChain} {U : ChainChart F} {q : F.Site F.depth × Fin 4 × Fin 4}
    (hqD : q ∈ innerPlaquettes D F.depth)
    (hc1' : baseDistance q.1 (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth)
    (hc2' : baseDistance (q.1 + unitStep F.depth q.2.1) (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth)
    (hc3' : baseDistance (q.1 + unitStep F.depth q.2.2) (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth)
    {Cc Kq Cw Db s β : ℝ}
    (hCc : 0 ≤ Cc) (hKq : 0 ≤ Kq) (hCw : 0 ≤ Cw) (hDb : 0 ≤ Db) (hs : 0 ≤ s) (hsβ : s ≤ β) (hCb : Cw * β ≤ 1)
    (h0 : ∀ b ∈ innerBonds D 0, coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) 0 b.1 b.2 = 0)
    (hQ : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds D (j + 1),
      (shiftedWeight F θ (baseSite q.1) (j + 1) c.1 * ‖stepRemainder R U j c‖) ^ 2 ≤ (Kq * β ^ 2) ^ 2)
    (hM : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds D (j + 1),
      (shiftedWeight F θ (baseSite q.1) (j + 1) c.1 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ^ 2 ≤ (25 * β) ^ 2)
    (hW : ∑ b ∈ innerBonds D F.depth,
      (shiftedWeight F θ (baseSite q.1) F.depth b.1 * ‖levelCoordinate R U F.depth b.1 b.2‖) ^ 4 ≤ (Cw * β) ^ 4)
    (hcurl : ‖covariantCurlAt (R F.depth) (transportedForm R (fun x i => (U.fine x i : ℍ[ℝ])) F.depth) q‖ ≤
      (shiftedWeight F θ (baseSite q.1) F.depth q.1)⁻¹ * (2 * (25 * β)) + Cc * s * (25 * β))
    (hR0 : plaquetteDefect (R F.depth) q ≤ Db * s / ((F.blockSide : ℝ)) ^ 2) :
    plaquetteDefect (chartField R U F.depth) q ≤ (Db + 1050) * s / ((F.blockSide : ℝ)) ^ 2 +
      (Db + 1050) * (1 / (F.blockSide : ℝ)) ^ θ * β + (25 * Cc + 36 * Kq + 36 * Cw ^ 2) * β ^ 2 := by
  have hLpos : 0 < F.blockSide := by omega
  have hL1r : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  have hβ0 : 0 ≤ β := hs.trans hsβ
  have htn : F.depth < F.top := Nat.lt_succ_self _
  have hrest := sum_weighted_coordinateRemainder_sq_le hodd hL3 hθ.le (baseSite q.1) D R U
    (fun x i => (U.fine x i : ℍ[ℝ])) h0 hQ hM F.depth htn
  obtain ⟨e1, e2, e3, e4⟩ := plaquette_edges_mem_innerBonds hqD
  have hfb := norm_le_of_sum_pow_four_le hLpos hθ.le (baseSite q.1) (levelCoordinate R U F.depth)
    (by positivity : 0 ≤ Cw * β) hW
  have hlam0 : 0 ≤ (1 / (F.blockSide : ℝ)) ^ θ := by positivity
  have hlam1 : (1 / (F.blockSide : ℝ)) ^ θ ≤ 1 :=
    Real.rpow_le_one (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1r) hθ.le
  have hQ0 : 0 ≤ Kq * β ^ 2 := by positivity
  have hM0 : 0 ≤ 25 * β := by positivity
  have hrb : ∀ b ∈ innerBonds D F.depth, baseDistance b.1 (baseSite q.1) ≤ 2 * F.blockSide ^ F.depth →
      ‖coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth b.1 b.2‖ ≤
        9 * (1 / (F.blockSide : ℝ)) ^ θ * (Kq * β ^ 2 + 25 * β) := by
    intro b hb hd
    have h5 := inv_shiftedWeight_le_of_baseDistance_le hLpos hθ.le hθ8 (baseSite q.1) b.1 hd
    have h7 := norm_le_of_sum_sq_le hLpos hθ.le (baseSite q.1)
      (coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth) hQ0 hM0
      (by positivity) hrest hb h5
    refine h7.trans (le_of_eq ?_)
    ring
  have f1 : ‖levelCoordinate R U F.depth q.1 q.2.1‖ ≤ Cw * β := hfb (q.1, q.2.1) e1
  have f2 : ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ ≤ Cw * β :=
    hfb (q.1 + unitStep F.depth q.2.1, q.2.2) e2
  have f3 : ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ ≤ Cw * β :=
    hfb (q.1 + unitStep F.depth q.2.2, q.2.1) e3
  have f4 : ‖levelCoordinate R U F.depth q.1 q.2.2‖ ≤ Cw * β := hfb (q.1, q.2.2) e4
  have hv := plaquetteDefect_chartField_le R U q (f1.trans hCb) (f2.trans hCb) (f3.trans hCb) (f4.trans hCb)
  have hcf := norm_covariantCurlAt_sub_le (R F.depth) (levelCoordinate R U F.depth)
    (transportedForm R (fun x i => (U.fine x i : ℍ[ℝ])) F.depth) q
  have hcf' := (norm_sub_norm_le (covariantCurlAt (R F.depth) (levelCoordinate R U F.depth) q)
    (covariantCurlAt (R F.depth) (transportedForm R (fun x i => (U.fine x i : ℍ[ℝ])) F.depth) q)).trans hcf
  have hf4 : ‖levelCoordinate R U F.depth q.1 q.2.1‖ ^ 2 +
      ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ ^ 2 +
      ‖levelCoordinate R U F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ ^ 2 +
      ‖levelCoordinate R U F.depth q.1 q.2.2‖ ^ 2 ≤ 4 * (Cw * β) ^ 2 := by
    have g1 := pow_le_pow_left₀ (norm_nonneg _) f1 2
    have g2 := pow_le_pow_left₀ (norm_nonneg _) f2 2
    have g3 := pow_le_pow_left₀ (norm_nonneg _) f3 2
    have g4 := pow_le_pow_left₀ (norm_nonneg _) f4 2
    linarith
  have r1 := hrb (q.1, q.2.1) e1 hc1'
  have r2 := hrb (q.1 + unitStep F.depth q.2.1, q.2.2) e2 hc2'
  have r3 := hrb (q.1 + unitStep F.depth q.2.2, q.2.1) e3 hc3'
  have r4 := hrb (q.1, q.2.2) e4 hc1'
  have hcf2 : ‖covariantCurlAt (R F.depth) (levelCoordinate R U F.depth) q‖ ≤
      ‖covariantCurlAt (R F.depth) (transportedForm R (fun x i => (U.fine x i : ℍ[ℝ])) F.depth) q‖ +
      (‖coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth q.1 q.2.1‖ +
        ‖coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth (q.1 + unitStep F.depth q.2.1) q.2.2‖ +
        ‖coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth (q.1 + unitStep F.depth q.2.2) q.2.1‖ +
        ‖coordinateRemainder R U (fun x i => (U.fine x i : ℍ[ℝ])) F.depth q.1 q.2.2‖) := by
    simp only [coordinateRemainder]
    linarith
  exact plaquetteDefect_final_arith (Kq := Kq) (Cw := Cw) (Db := Db) (Cc := Cc) (s := s) (β := β)
    (lam := (1 / (F.blockSide : ℝ)) ^ θ) (L2 := ((F.blockSide : ℝ)) ^ 2)
    (Q := Kq * β ^ 2) (M := 25 * β) hs hsβ hlam0 hlam1 hCc hKq hDb (by positivity) hv hR0
    hcf2 hcurl (inv_shiftedWeight_le_of_baseDistance_le hLpos hθ.le hθ8 _ _ hc1') r1 r2 r3 r4 hf4 rfl rfl
end ColdBelowTop
open ColdBelowTop
set_option maxHeartbeats 1600000 in
theorem coldFieldBelowTop_of_statements (hWG : weightedLevelGapsStatement)
    (hCC : transportedCurlBoundStatement) (hOne : levelCoordinateStepStatement) (hB : referenceBoundsStatement) :
    coldFieldBelowTopStatement := by
  obtain ⟨L0, hOne⟩ := hOne
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  intro θ del hθ hθ8 hdel hdel8
  obtain ⟨Cc, cc, Lc, hCc, hcc, hCurl⟩ := hCC θ hθ hθ8
  obtain ⟨Lw, hWG⟩ := hWG θ del hθ hθ8 hdel hdel8
  refine ⟨Db + 1050, by positivity, max (max L0 L1) (max (max Lc Lw) 5), fun L hL hge => ?_⟩
  have hL0 : L0 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL1 : L1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hLc : Lc ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hge))
  have hLw : Lw ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hge))
  have hL5 : 5 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hge)
  obtain ⟨Cs, cs, hCs, hcs, hStep⟩ := hOne L hL hL0
  obtain ⟨cw, Cw, hcw, hCw, hWGL⟩ := hWG L hL hLw
  obtain ⟨H, hH0, hHdef⟩ : ∃ H : ℝ, 0 ≤ H ∧ 16 * ((hullBox L).card : ℝ) ≤ H :=
    ⟨16 * ((hullBox L).card : ℝ), by positivity, le_rfl⟩
  obtain ⟨T0, hT0, hT0def⟩ : ∃ T0 : ℝ, 0 ≤ T0 ∧ T0 = (1 + H) * Cw := ⟨(1 + H) * Cw, by positivity, rfl⟩
  obtain ⟨Kq, hKq1, hKq⟩ : ∃ Kq : ℝ, 1 ≤ Kq ∧
      3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) ≤ Kq ^ 2 := by
    refine ⟨1 + 3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2), ?_, ?_⟩
    · have : 0 ≤ 3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) := by positivity
      linarith
    · set X := 3 * (Cs * (1 + Db)) ^ 2 * (H * Cw ^ 4 + 200 * (1 + H) * Cw ^ 2 + 625 * T0 ^ 2) with hX
      have : 0 ≤ X := by positivity
      nlinarith
  obtain ⟨c, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cw ∧ c ≤ cb ∧ c ≤ cc ∧ c ≤ 1 / 8 ∧
      25 * c ≤ cs ∧ T0 * c ≤ cs ∧ Cw * c ≤ 1 := by
    have hp1 : 0 < cs / (T0 + 1) := by positivity
    have hp2 : 0 < 1 / (Cw + 1) := by positivity
    have hp3 : 0 < cs / 25 := by positivity
    refine ⟨min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1)))),
      lt_min (lt_min (lt_min hcw hcb) (lt_min hcc (by norm_num))) (lt_min hp3 (lt_min hp1 hp2)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    · have : min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1)))) ≤
          cs / 25 :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have h1 : min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1)))) ≤
          cs / (T0 + 1) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      set z := min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1))))
      have hz0 : 0 < z :=
        lt_min (lt_min (lt_min hcw hcb) (lt_min hcc (by norm_num))) (lt_min hp3 (lt_min hp1 hp2))
      have h2 : z * (T0 + 1) ≤ cs := (le_div_iff₀ (by positivity)).1 h1
      nlinarith
    · have h1 : min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1)))) ≤
          1 / (Cw + 1) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      set z := min (min (min cw cb) (min cc (1 / 8))) (min (cs / 25) (min (cs / (T0 + 1)) (1 / (Cw + 1))))
      have hz0 : 0 < z :=
        lt_min (lt_min (lt_min hcw hcb) (lt_min hcc (by norm_num))) (lt_min hp3 (lt_min hp1 hp2))
      have h2 : z * (Cw + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 h1
      nlinarith
  refine ⟨c, 25 * Cc + 36 * Kq + 36 * Cw ^ 2, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold U β hsβ hβc hN q hq
  subst hFL
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hL2 : 2 ≤ F.blockSide := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  obtain ⟨-, b2, b3, -, -, -⟩ := hBd F m S hodd hL1 hamb hm hreg s V hs0 (hsc.trans hc2) hcold
  have hβ0 : 0 ≤ β := hs0.le.trans hsβ
  have hsc5 : s ≤ cs := by linarith
  obtain ⟨hqD, hd1, hd2, hd3⟩ := plaquette_mem_near_baseSite hodd hL2 hq
  have hDS : cellsNearPoint S (baseSite q.1) ⊆ S := Finset.filter_subset _ _
  obtain ⟨i1, i2, i3, i4⟩ := nearPoint_input_bounds hodd hθ.le S (referenceFieldChain S V) U (baseSite q.1) hβ0
    (hN (baseSite q.1))
  have hW := fun j hj => hWGL F m S rfl hamb hm hreg s V hs0 (hsc.trans hc1) hcold U (baseSite q.1) β hβ0
    (hβc.trans hc1) (hN (baseSite q.1)) j hj
  have htn : F.depth < F.top := Nat.lt_succ_self _
  have h0 : ∀ b ∈ innerBonds (cellsNearPoint S (baseSite q.1)) 0,
      coordinateRemainder (referenceFieldChain S V) U (fun x i => (U.fine x i : ℍ[ℝ])) 0 b.1 b.2 = 0 := by
    intro b hb
    have hu := i4 b (innerBonds_mono hDS 0 hb)
    have e1 : levelCoordinate (referenceFieldChain S V) U 0 b.1 b.2 = (U.fine b.1 b.2 : ℍ[ℝ]) := by
      unfold levelCoordinate chartGap
      simp only [chartField, mul_inv_cancel_right]
      exact unitQuaternionLog_expUnit (by linarith)
    simp only [coordinateRemainder, transportedForm, e1, sub_self]
  have hQ := sum_weighted_stepRemainder_sq_le_all hodd hL2 hθ.le (baseSite q.1) hCs.le hDb.le hs0.le hsβ hCw.le
    hT0 hT0def hH0 hHdef
    ((mul_le_mul_of_nonneg_left hβc hT0).trans hc6) (by linarith) hKq
    (fun j hj b hb t ht0 htc hmu hBB =>
      hStep F m S rfl hamb hm hreg s V hs0 hsc5 hcold U j b hj hb t ht0 htc hmu hBB)
    (fun j hj b hb => (b3 j hj b hb).trans (le_of_eq (by simp only [levelScale]; ring))) hW i2
  have hcurl := hCurl F m S hodd hLc hamb hm hreg s V hs0 (hsc.trans hc3) hcold (fun x i => (U.fine x i : ℍ[ℝ]))
    (baseSite q.1) (25 * β) (25 * β) (by positivity) (by positivity) i3 i1 q hqD
  have hR0 : plaquetteDefect (referenceFieldChain S V F.depth) q ≤ Db * s / ((F.blockSide : ℝ)) ^ 2 := by
    refine (b2 F.depth htn q hq).trans (le_of_eq ?_)
    have : F.top - F.depth = 1 := by simp [BlockFrame.top]
    simp only [levelScale, this]
    field_simp
  exact plaquetteDefect_chartField_bound hodd (by omega) hθ hθ8 hqD hd1 hd2 hd3 hCc.le (by linarith) hCw.le hDb.le
    hs0.le hsβ ((mul_le_mul_of_nonneg_left hβc hCw.le).trans hc7) h0 hQ i2 (hW F.depth htn) hcurl hR0
end BlockAverages
end YangMills.Construction
end
