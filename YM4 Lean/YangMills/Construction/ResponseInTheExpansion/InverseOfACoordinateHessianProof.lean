import YangMills.Construction.ColdStepAtMirrorFrames.EntryBoundOfASymmetricSystem
import YangMills.Construction.ResponseInTheExpansion.InverseOfACoordinateHessian
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.LinearResponse.HessianInverse
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem secondDerivAlong_eq_fderiv_fderiv {A : BondField ι → ℝ} (hA : ContDiffAt ℝ 3 A 0) (u v : BondField ι) :
    secondDerivAlong A 0 u v = fderiv ℝ (fderiv ℝ A) 0 v u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ A) 0 := hA.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ A) 0 := h2.differentiableAt (by norm_num)
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const u (0 : BondField ι))
  unfold secondDerivAlong
  rw [h.fderiv]
  simp
theorem secondDerivAlong_symm {A : BondField ι → ℝ} (hA : ContDiffAt ℝ 3 A 0) (u v : BondField ι) :
    secondDerivAlong A 0 u v = secondDerivAlong A 0 v u := by
  rw [secondDerivAlong_eq_fderiv_fderiv hA, secondDerivAlong_eq_fderiv_fderiv hA]
  exact (hA.isSymmSndFDerivAt (by simp; norm_num)).eq v u
def bondFieldOfCoords (x : ι × Fin 3 → ℝ) : BondField ι :=
  fun b => WithLp.toLp 2 fun i => x (b, i)
theorem bondFieldOfCoords_eq_sum (x : ι × Fin 3 → ℝ) :
    bondFieldOfCoords x = ∑ p, x p • bondCoordinateVector p := by
  funext b
  have hb : (∑ p, x p • bondCoordinateVector p) b =
      ∑ j, x (b, j) • (EuclideanSpace.single j (1 : ℝ) : BondVector) := by
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [bondCoordinateVector, bondVariation]
    · intro b' _ hb'
      simp [bondCoordinateVector, bondVariation, Pi.single_eq_of_ne hb'.symm]
    · intro h
      exact absurd (Finset.mem_univ b) h
  rw [hb]
  ext i
  simp [bondFieldOfCoords, Finset.sum_apply, Pi.single_apply]
theorem sum_norm_sq_bondFieldOfCoords (x : ι × Fin 3 → ℝ) :
    ∑ b, ‖bondFieldOfCoords x b‖ ^ 2 = ∑ p, x p ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [bondFieldOfCoords]
theorem quadForm_bondCoordinateHessian {A : BondField ι → ℝ} (hA : ContDiffAt ℝ 3 A 0) (x : ι × Fin 3 → ℝ) :
    ∑ p, x p * (bondCoordinateHessian A).mulVec x p =
      secondDerivAlong A 0 (bondFieldOfCoords x) (bondFieldOfCoords x) := by
  set Bf := fderiv ℝ (fderiv ℝ A) (0 : BondField ι) with hBf
  set U : BondField ι := ∑ p, x p • bondCoordinateVector p with hU
  have e1 : ∀ v : BondField ι, Bf v U = ∑ p, x p * Bf v (bondCoordinateVector p) := by
    intro v
    rw [hU, map_sum]
    simp
  have e2 : ∀ w : BondField ι, Bf U w = ∑ q, x q * Bf (bondCoordinateVector q) w := by
    intro w
    rw [hU, map_sum, ContinuousLinearMap.sum_apply]
    simp
  rw [secondDerivAlong_eq_fderiv_fderiv hA, bondFieldOfCoords_eq_sum, ← hU, ← hBf, e1]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [e2]
  simp only [Matrix.mulVec, dotProduct, bondCoordinateHessian]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [secondDerivAlong_eq_fderiv_fderiv hA, ← hBf]
  ring
theorem coordinateHessianInverseBound_holds (hE : SymmetricSystemGreenDecay) :
    CoordinateHessianInverseBound := by
  intro ι _ _ A K d lam κ W hlam hκ hd hA hfl hK hrow hW
  set H := bondCoordinateHessian A with hH
  have hsymm : H.IsSymm := by
    ext p q
    simp only [Matrix.transpose_apply, hH, bondCoordinateHessian]
    exact secondDerivAlong_symm hA _ _
  have hfloor : ∀ x : ι × Fin 3 → ℝ, lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * H.mulVec x p := by
    intro x
    rw [hH, quadForm_bondCoordinateHessian hA, ← sum_norm_sq_bondFieldOfCoords]
    exact hfl _
  have hdet : IsUnit H.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := hfloor v
    rw [hHv] at h1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    have h2 : ∑ p, v p ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hlam hc
      linarith
    have h3 : ∑ p, v p ^ 2 = 0 := le_antisymm h2 (Finset.sum_nonneg fun p _ => sq_nonneg _)
    apply hv
    funext p
    have := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => sq_nonneg (v p)).1 h3 p (Finset.mem_univ p)
    simpa using this
  have hunit : ∀ i : Fin 3, ‖(EuclideanSpace.single i (1 : ℝ) : BondVector)‖ = 1 := fun i => by simp
  have hentry : ∀ p q : ι × Fin 3, |H p q| ≤ K p.1 q.1 := by
    intro p q
    have := hK p.1 q.1 (EuclideanSpace.single p.2 1) (EuclideanSpace.single q.2 1)
    rw [hunit, hunit, mul_one, mul_one] at this
    exact this
  have hd0 : ∀ b b', 0 ≤ d b b' := by
    intro b b'
    have h1 := hd.triangle b b' b
    rw [hd.self, hd.symm b' b] at h1
    linarith
  set d' : ι × Fin 3 → ι × Fin 3 → ℝ := fun p q => d p.1 q.1 with hd'
  have hrows : ∀ p, ∑ q, |H p q| * (Real.exp (2 * κ * d' p q) - 1) ≤ lam / 2 := by
    intro p
    have hw : ∀ b', 0 ≤ Real.exp (2 * κ * d p.1 b') - 1 := by
      intro b'
      have : 1 ≤ Real.exp (2 * κ * d p.1 b') := Real.one_le_exp (by have := hd0 p.1 b'; positivity)
      linarith
    calc ∑ q, |H p q| * (Real.exp (2 * κ * d' p q) - 1)
        ≤ ∑ q : ι × Fin 3, K p.1 q.1 * (Real.exp (2 * κ * d p.1 q.1) - 1) :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hentry p q) (hw q.1)
      _ = 3 * ∑ b', K p.1 b' * (Real.exp (2 * κ * d p.1 b') - 1) := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b' _ => ?_
          simp
      _ ≤ 3 * (lam / 16) := by
          have := hrow p.1
          linarith
      _ ≤ lam / 2 := by linarith
  have hinv : ∀ (p q : ι × Fin 3), |H⁻¹ p q| ≤ 2 / lam * Real.exp (-(2 * κ * d' p q)) := by
    intro p q
    have hx : H.mulVec (H⁻¹.mulVec (Pi.single q 1)) = Pi.single q 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
    have := hE (ι × Fin 3) d' H lam κ hlam hκ (fun i => hd.self _) (fun i j => hd.symm _ _)
      (fun i j k => hd.triangle _ _ _) hsymm hfloor hrows _ q hx p
    have e : H⁻¹.mulVec (Pi.single q 1) p = H⁻¹ p q := by
      rw [Matrix.mulVec_single_one]
      rfl
    rwa [e] at this
  refine ⟨hsymm, hdet, fun l => ?_⟩
  have hW0 : ∀ q : ι × Fin 3, ∑ p : ι × Fin 3, Real.exp (-(2 * κ * d' p q)) ≤ 3 * W := by
    intro q
    calc ∑ p : ι × Fin 3, Real.exp (-(2 * κ * d' p q))
        = 3 * ∑ b, Real.exp (-(2 * κ * d b q.1)) := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp [hd']
      _ ≤ 3 * W := by
          have := hW q.1
          linarith
  calc ∑ p, |H⁻¹.mulVec l p| ≤ ∑ p, ∑ q, |H⁻¹ p q| * |l q| := by
        refine Finset.sum_le_sum fun p _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp only [abs_mul, le_refl]
    _ = ∑ q, ∑ p, |H⁻¹ p q| * |l q| := Finset.sum_comm
    _ ≤ ∑ q, 6 * W / lam * |l q| := by
        refine Finset.sum_le_sum fun q _ => ?_
        calc ∑ p, |H⁻¹ p q| * |l q| ≤ ∑ p, 2 / lam * Real.exp (-(2 * κ * d' p q)) * |l q| :=
              Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hinv p q) (abs_nonneg _)
          _ = 2 / lam * (∑ p, Real.exp (-(2 * κ * d' p q))) * |l q| := by
              rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ 2 / lam * (3 * W) * |l q| := by
              have h2 : 0 ≤ 2 / lam := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hW0 q) h2) (abs_nonneg _)
          _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]
end YangMills.Construction.LinearResponse.HessianInverse
end
