import YangMills.Construction.EuclideanAnalysis.RotationsOfCoordinatePlanesGenerateTheSpecialOrthogonalGroup
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.GivensGeneration
open YangMills.Construction.EuclideanAnalysis YangMills.Construction.EuclideanAnalysis.PlaneRotations
variable {n : ℕ}
def givensMatrix (i k : Fin n) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + (a - 1) • (single i i (1 : ℝ) + single k k 1) + b • (single i k (1 : ℝ) - single k i 1)
theorem single_one_mul_apply (i j p q : Fin n) (M : Matrix (Fin n) (Fin n) ℝ) :
    (single i j (1 : ℝ) * M) p q = if p = i then M j q else 0 := by
  by_cases h : p = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · simp [Matrix.single_mul_apply_of_ne _ _ _ _ _ h, h]
theorem givensMatrix_mul_apply (i k : Fin n) (a b : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) :
    (givensMatrix i k a b * M) p q =
      M p q + (a - 1) * ((if p = i then M i q else 0) + (if p = k then M k q else 0)) +
        b * ((if p = i then M k q else 0) - (if p = k then M i q else 0)) := by
  simp only [givensMatrix, add_mul, sub_mul, one_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, single_one_mul_apply, smul_eq_mul]
theorem givensMatrix_apply (i k : Fin n) (a b : ℝ) (p q : Fin n) :
    givensMatrix i k a b p q =
      (1 : Matrix (Fin n) (Fin n) ℝ) p q +
        (a - 1) * ((if p = i then (1 : Matrix (Fin n) (Fin n) ℝ) i q else 0) +
          (if p = k then (1 : Matrix (Fin n) (Fin n) ℝ) k q else 0)) +
        b * ((if p = i then (1 : Matrix (Fin n) (Fin n) ℝ) k q else 0) -
          (if p = k then (1 : Matrix (Fin n) (Fin n) ℝ) i q else 0)) := by
  have := givensMatrix_mul_apply i k a b 1 p q
  rwa [mul_one] at this
theorem givensMatrix_mul_givensMatrix {i k : Fin n} (hik : i ≠ k) (a b c d : ℝ) :
    givensMatrix i k a b * givensMatrix i k c d =
      givensMatrix i k (a * c - b * d) (a * d + b * c) := by
  ext p q
  rw [givensMatrix_mul_apply]
  simp only [givensMatrix_apply]
  by_cases hpi : p = i
  · subst hpi
    by_cases hqp : q = p
    · subst hqp
      simp [hik, hik.symm, Matrix.one_apply]
      ring
    · by_cases hqk : q = k
      · subst hqk
        simp [hik, hik.symm, Matrix.one_apply]
        ring
      · simp [hik, Ne.symm hqp, Ne.symm hqk, hqp, hqk, Matrix.one_apply]
  · by_cases hpk : p = k
    · subst hpk
      by_cases hqi : q = i
      · subst hqi
        simp [hik, hik.symm, hpi, Matrix.one_apply]
        ring
      · by_cases hqp : q = p
        · subst hqp
          simp [hik, hik.symm, hpi, Matrix.one_apply]
          ring
        · simp [hpi, hqi, hqp, Ne.symm hqi, Ne.symm hqp, Matrix.one_apply]
    · simp [hpi, hpk, Matrix.one_apply]
theorem givensMatrix_one_zero (i k : Fin n) : givensMatrix i k 1 0 = 1 := by
  simp [givensMatrix]
theorem transpose_givensMatrix (i k : Fin n) (a b : ℝ) :
    (givensMatrix i k a b)ᵀ = givensMatrix i k a (-b) := by
  simp only [givensMatrix, transpose_add, transpose_smul, transpose_one, transpose_sub,
    transpose_single]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring
theorem givensMatrix_mul_transpose {i k : Fin n} (hik : i ≠ k) {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    givensMatrix i k a b * (givensMatrix i k a b)ᵀ = 1 := by
  rw [transpose_givensMatrix, givensMatrix_mul_givensMatrix hik]
  have h1 : a * a - b * -b = 1 := by linarith
  have h2 : a * -b + b * a = 0 := by ring
  rw [h1, h2, givensMatrix_one_zero]
theorem exists_half_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * c - s * s = a ∧ c * s + s * c = b := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hz]
      nlinarith
    have h2 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp at hnorm
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hnorm]
    simp [hz]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hnorm]
    simp [hz]
  set θ := Complex.arg z
  refine ⟨Real.cos (θ / 2), Real.sin (θ / 2), Real.cos_sq_add_sin_sq _, ?_, ?_⟩
  · rw [← hcos]
    have : θ = 2 * (θ / 2) := by ring
    conv_rhs => rw [this, Real.cos_two_mul]
    have := Real.cos_sq_add_sin_sq (θ / 2)
    nlinarith
  · rw [← hsin]
    have : θ = 2 * (θ / 2) := by ring
    conv_rhs => rw [this, Real.sin_two_mul]
    ring
theorem det_givensMatrix {i k : Fin n} (hik : i ≠ k) {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (givensMatrix i k a b).det = 1 := by
  obtain ⟨c, s, hcs, rfl, rfl⟩ := exists_half_angle h
  rw [← givensMatrix_mul_givensMatrix hik, det_mul]
  have := congrArg Matrix.det (givensMatrix_mul_transpose hik hcs)
  rwa [det_mul, det_transpose, det_one] at this
theorem givensMatrix_mem_specialOrthogonalGroup {i k : Fin n} (hik : i ≠ k) {a b : ℝ}
    (h : a ^ 2 + b ^ 2 = 1) :
    givensMatrix i k a b ∈ specialOrthogonalGroup (Fin n) ℝ :=
  mem_specialOrthogonalGroup_iff.2
    ⟨(mem_orthogonalGroup_iff (Fin n) ℝ).2 (givensMatrix_mul_transpose hik h),
      det_givensMatrix hik h⟩
theorem toEuclideanLin_stdBasisVector_apply (A : Matrix (Fin n) (Fin n) ℝ) (j p : Fin n) :
    (toEuclideanLin A (stdBasisVector j)) p = A p j := by
  simp [Matrix.toLpLin_apply, stdBasisVector, Matrix.mulVec_single_one]
theorem toEuclideanLin_comp_apply (A B : Matrix (Fin n) (Fin n) ℝ) (x : RealSpace n) :
    toEuclideanLin A (toEuclideanLin B x) = toEuclideanLin (A * B) x := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
theorem toEuclideanLin_givensMatrix_fst {i k : Fin n} (hik : i ≠ k) (a b : ℝ) :
    toEuclideanLin (givensMatrix i k a b) (stdBasisVector i) =
      a • stdBasisVector i + (-b) • stdBasisVector k := by
  ext p
  rw [toEuclideanLin_stdBasisVector_apply, givensMatrix_apply]
  by_cases hpi : p = i
  · subst hpi
    simp [stdBasisVector, hik, hik.symm, Matrix.one_apply]
  · by_cases hpk : p = k
    · subst hpk
      simp [stdBasisVector, hik, hik.symm, hpi, Matrix.one_apply]
    · simp [stdBasisVector, hpi, hpk, Matrix.one_apply]
theorem toEuclideanLin_givensMatrix_snd {i k : Fin n} (hik : i ≠ k) (a b : ℝ) :
    toEuclideanLin (givensMatrix i k a b) (stdBasisVector k) =
      b • stdBasisVector i + a • stdBasisVector k := by
  ext p
  rw [toEuclideanLin_stdBasisVector_apply, givensMatrix_apply]
  by_cases hpi : p = i
  · subst hpi
    simp [stdBasisVector, hik, hik.symm, Matrix.one_apply]
  · by_cases hpk : p = k
    · subst hpk
      simp [stdBasisVector, hik, hik.symm, hpi, Matrix.one_apply]
    · simp [stdBasisVector, hpi, hpk, Matrix.one_apply]
theorem map_coordPlane_givensMatrix_le {i k : Fin n} (hik : i ≠ k) (a b : ℝ) :
    (coordPlane i k).map (toEuclideanLin (givensMatrix i k a b)) ≤ coordPlane i k := by
  have hi : stdBasisVector i ∈ coordPlane i k :=
    Submodule.subset_span (by simp)
  have hk : stdBasisVector k ∈ coordPlane i k :=
    Submodule.subset_span (by simp)
  rw [coordPlane, Submodule.map_span, Set.image_pair, Submodule.span_le]
  rintro _ (rfl | rfl)
  · rw [toEuclideanLin_givensMatrix_fst hik]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hi) (Submodule.smul_mem _ _ hk)
  · rw [toEuclideanLin_givensMatrix_snd hik]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hi) (Submodule.smul_mem _ _ hk)
theorem isPlaneRotation_givensMatrix {i k : Fin n} (hik : i ≠ k) {a b : ℝ}
    (h : a ^ 2 + b ^ 2 = 1) :
    IsPlaneRotation
      (⟨givensMatrix i k a b, givensMatrix_mem_specialOrthogonalGroup hik h⟩ :
        specialOrthogonalGroup (Fin n) ℝ) := by
  refine ⟨i, k, hik, le_antisymm (map_coordPlane_givensMatrix_le hik a b) ?_, ?_⟩
  · intro x hx
    refine ⟨toEuclideanLin (givensMatrix i k a (-b)) x, ?_, ?_⟩
    · exact map_coordPlane_givensMatrix_le hik a (-b) ⟨x, hx, rfl⟩
    · have hone := givensMatrix_mul_transpose hik h
      rw [transpose_givensMatrix] at hone
      change toEuclideanLin (givensMatrix i k a b) (toEuclideanLin (givensMatrix i k a (-b)) x) = x
      rw [toEuclideanLin_comp_apply, hone]
      simp [Matrix.toLpLin_apply]
  · intro q hqi hqk
    ext p
    change (toEuclideanLin (givensMatrix i k a b) (stdBasisVector q)) p = _
    rw [toEuclideanLin_stdBasisVector_apply, givensMatrix_apply]
    by_cases hpi : p = i
    · subst hpi
      simp [stdBasisVector, Matrix.one_apply, Ne.symm hqi, Ne.symm hqk, hqi, hqk]
    · by_cases hpk : p = k
      · subst hpk
        simp [stdBasisVector, Matrix.one_apply, Ne.symm hqi, Ne.symm hqk, hqi, hqk, hpi]
      · simp [stdBasisVector, Matrix.one_apply, hpi, hpk]
def givensSet (n : ℕ) : Set (specialOrthogonalGroup (Fin n) ℝ) :=
  {Q | ∃ (i k : Fin n) (a b : ℝ), i ≠ k ∧ a ^ 2 + b ^ 2 = 1 ∧
    (Q : Matrix (Fin n) (Fin n) ℝ) = givensMatrix i k a b}
theorem isPlaneRotation_of_mem_givensSet {Q : specialOrthogonalGroup (Fin n) ℝ}
    (hQ : Q ∈ givensSet n) : IsPlaneRotation Q := by
  obtain ⟨i, k, a, b, hik, h, hQ⟩ := hQ
  have : Q = ⟨givensMatrix i k a b, givensMatrix_mem_specialOrthogonalGroup hik h⟩ :=
    Subtype.ext hQ
  rw [this]
  exact isPlaneRotation_givensMatrix hik h
theorem inv_mem_givensSet {Q : specialOrthogonalGroup (Fin n) ℝ}
    (hQ : Q ∈ givensSet n) : Q⁻¹ ∈ givensSet n := by
  obtain ⟨i, k, a, b, hik, h, hQ⟩ := hQ
  refine ⟨i, k, a, -b, hik, by simpa using h, ?_⟩
  rw [← transpose_givensMatrix, ← hQ, ← star_eq_inv]
  simp [Matrix.star_eq_conjTranspose]
def ColumnsStdFrom (k : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ j : Fin n, k ≤ j.val → ∀ p, M p j = (1 : Matrix (Fin n) (Fin n) ℝ) p j
theorem coe_transpose_mul_coe (M : specialOrthogonalGroup (Fin n) ℝ) :
    (M : Matrix (Fin n) (Fin n) ℝ)ᵀ * (M : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  (mem_orthogonalGroup_iff' (Fin n) ℝ).1 (mem_specialOrthogonalGroup_iff.1 M.2).1
theorem row_eq_of_column {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ * M = 1) {j : Fin n}
    (hj : ∀ p, M p j = (1 : Matrix (Fin n) (Fin n) ℝ) p j) (q : Fin n) :
    M j q = (1 : Matrix (Fin n) (Fin n) ℝ) q j := by
  have h := congrFun (congrFun hM q) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hj] at h
  simpa [Matrix.one_apply] using h
theorem sum_sq_column {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ * M = 1) (k : Fin n) :
    ∑ p, M p k ^ 2 = 1 := by
  have h := congrFun (congrFun hM k) k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  simpa [pow_two] using h
theorem eq_one_of_columnsStdFrom_one (M : specialOrthogonalGroup (Fin n) ℝ)
    (h : ColumnsStdFrom 1 (M : Matrix (Fin n) (Fin n) ℝ)) : M = 1 := by
  cases n with
  | zero =>
    apply Subtype.ext
    ext p
    exact p.elim0
  | succ n =>
    have hM := coe_transpose_mul_coe M
    have hcol : ∀ q : Fin (n + 1), q ≠ 0 → ∀ p, (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q := fun q hq =>
      h q (Nat.one_le_iff_ne_zero.2 (fun h0 => hq (Fin.ext h0)))
    have hdiag : (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
        diagonal (fun p => if p = 0 then (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0 else 1) := by
      ext p q
      by_cases hq : q = 0
      · subst hq
        by_cases hp : p = 0
        · subst hp
          simp
        · rw [row_eq_of_column hM (hcol p hp)]
          simp [Matrix.one_apply, hp, Ne.symm hp]
      · rw [hcol q hq]
        by_cases hpq : p = q
        · subst hpq
          simp [hq]
        · simp [Matrix.one_apply, hpq]
    have hdet : (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = 1 :=
      (mem_specialOrthogonalGroup_iff.1 M.2).2
    have h00 : (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0 = 1 := by
      rw [hdiag, det_diagonal, Fin.prod_univ_succ] at hdet
      simpa [Fin.succ_ne_zero] using hdet
    apply Subtype.ext
    rw [hdiag]
    ext p q
    simp [h00, Matrix.one_apply, Matrix.diagonal_apply]
theorem mem_closure_of_clear_entry (K i : Fin n) (t : ℕ) (hiK : i.val < K.val) (hit : i.val = t)
    (M : specialOrthogonalGroup (Fin n) ℝ)
    (hF : ColumnsStdFrom (K.val + 1) (M : Matrix (Fin n) (Fin n) ℝ))
    (hz : ∀ p : Fin n, p.val < t → (M : Matrix (Fin n) (Fin n) ℝ) p K = 0)
    (IH : ∀ M' : specialOrthogonalGroup (Fin n) ℝ,
      ColumnsStdFrom (K.val + 1) (M' : Matrix (Fin n) (Fin n) ℝ) →
      (∀ p : Fin n, p.val < t + 1 → (M' : Matrix (Fin n) (Fin n) ℝ) p K = 0) →
      0 ≤ (M' : Matrix (Fin n) (Fin n) ℝ) K K → M' ∈ Subgroup.closure (givensSet n)) :
    M ∈ Subgroup.closure (givensSet n) := by
  have hik : i ≠ K := fun h => by rw [h] at hiK; exact lt_irrefl _ hiK
  set A : Matrix (Fin n) (Fin n) ℝ := (M : Matrix (Fin n) (Fin n) ℝ) with hA
  set α := A i K with hα
  set β := A K K with hβ
  have hlt : ∀ p : Fin n, p.val < t + 1 → p ≠ i → p.val < t := by
    intro p hp hpi
    have : p.val ≠ t := fun h => hpi (Fin.ext (h.trans hit.symm))
    omega
  by_cases h0 : α ^ 2 + β ^ 2 = 0
  · have hα0 : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have hβ0 : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    refine IH M hF ?_ hβ0.ge
    intro p hp
    by_cases hpi : p = i
    · rw [hpi]; exact hα0
    · exact hz p (hlt p hp hpi)
  · have hpos : 0 < α ^ 2 + β ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set ϱ := Real.sqrt (α ^ 2 + β ^ 2) with hϱ
    have hϱpos : 0 < ϱ := Real.sqrt_pos.2 hpos
    have hϱsq : ϱ ^ 2 = α ^ 2 + β ^ 2 := Real.sq_sqrt hpos.le
    have hab : (β / ϱ) ^ 2 + (-α / ϱ) ^ 2 = 1 := by
      field_simp
      nlinarith
    set G : specialOrthogonalGroup (Fin n) ℝ :=
      ⟨givensMatrix i K (β / ϱ) (-α / ϱ), givensMatrix_mem_specialOrthogonalGroup hik hab⟩ with hG
    have hGmem : G ∈ Subgroup.closure (givensSet n) :=
      Subgroup.subset_closure ⟨i, K, _, _, hik, hab, rfl⟩
    have hGM : ((G * M : specialOrthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        givensMatrix i K (β / ϱ) (-α / ϱ) * A := rfl
    have hGMmem : G * M ∈ Subgroup.closure (givensSet n) := by
      refine IH (G * M) ?_ ?_ ?_
      · intro j hj p
        have hjK : K ≠ j := fun h => by rw [← h] at hj; omega
        have hji : i ≠ j := fun h => by rw [← h] at hj; omega
        have h1 : A i j = 0 := by
          rw [hF j hj]; simp [Matrix.one_apply, hji]
        have h2 : A K j = 0 := by
          rw [hF j hj]; simp [Matrix.one_apply, hjK]
        rw [hGM, givensMatrix_mul_apply, h1, h2]
        simp [hF j hj p]
      · intro p hp
        rw [hGM, givensMatrix_mul_apply]
        by_cases hpi : p = i
        · subst hpi
          simp only [if_true, if_neg hik, ← hα, ← hβ]
          field_simp
          ring
        · have hpK : p ≠ K := fun h => by
            have := hlt p hp hpi
            rw [h] at this
            omega
          simp [hpi, hpK, hz p (hlt p hp hpi)]
      · rw [hGM, givensMatrix_mul_apply]
        simp only [if_true, if_neg hik.symm, ← hα, ← hβ]
        have : β + (β / ϱ - 1) * (0 + β) + -α / ϱ * (0 - α) = ϱ := by
          field_simp
          nlinarith
        rw [this]
        exact hϱpos.le
    have : M = G⁻¹ * (G * M) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hGmem) hGMmem
theorem mem_closure_of_clear_column (K : Fin n) (hK : 1 ≤ K.val)
    (outer : ∀ M : specialOrthogonalGroup (Fin n) ℝ,
      ColumnsStdFrom K.val (M : Matrix (Fin n) (Fin n) ℝ) → M ∈ Subgroup.closure (givensSet n))
    (d : ℕ) : ∀ t : ℕ, t + d = K.val → ∀ M : specialOrthogonalGroup (Fin n) ℝ,
      ColumnsStdFrom (K.val + 1) (M : Matrix (Fin n) (Fin n) ℝ) →
      (∀ p : Fin n, p.val < t → (M : Matrix (Fin n) (Fin n) ℝ) p K = 0) →
      (1 ≤ t → 0 ≤ (M : Matrix (Fin n) (Fin n) ℝ) K K) →
      M ∈ Subgroup.closure (givensSet n) := by
  induction d with
  | zero =>
    intro t ht M hF hz hs
    have htK : t = K.val := by omega
    subst htK
    have hM := coe_transpose_mul_coe M
    have hbelow : ∀ p : Fin n, K.val < p.val → (M : Matrix (Fin n) (Fin n) ℝ) p K = 0 := by
      intro p hp
      rw [row_eq_of_column hM (hF p hp)]
      have : K ≠ p := fun h => by rw [h] at hp; exact lt_irrefl _ hp
      simp [Matrix.one_apply, this]
    have hoff : ∀ p : Fin n, p ≠ K → (M : Matrix (Fin n) (Fin n) ℝ) p K = 0 := by
      intro p hp
      rcases lt_or_gt_of_ne (fun h : p.val = K.val => hp (Fin.ext h)) with h | h
      · exact hz p h
      · exact hbelow p h
    have hKK : (M : Matrix (Fin n) (Fin n) ℝ) K K = 1 := by
      have hsum := sum_sq_column hM K
      rw [Finset.sum_eq_single K (fun p _ hp => by rw [hoff p hp]; simp) (by simp)] at hsum
      nlinarith [hs hK, sq_nonneg ((M : Matrix (Fin n) (Fin n) ℝ) K K - 1)]
    refine outer M ?_
    intro j hj p
    by_cases hjK : j = K
    · subst hjK
      by_cases hp : p = j
      · subst hp
        simp [hKK]
      · rw [hoff p hp]
        simp [Matrix.one_apply, hp]
    · exact hF j (by
        have : j.val ≠ K.val := fun h => hjK (Fin.ext h)
        omega) p
  | succ d ih =>
    intro t ht M hF hz _
    have htK : t < K.val := by omega
    refine mem_closure_of_clear_entry K ⟨t, htK.trans K.isLt⟩ t htK rfl M hF hz ?_
    intro M' hF' hz' hs'
    exact ih (t + 1) (by omega) M' hF' hz' (fun _ => hs')
theorem mem_closure_of_columnsStdFrom (k : ℕ) : ∀ M : specialOrthogonalGroup (Fin n) ℝ,
    ColumnsStdFrom (k + 1) (M : Matrix (Fin n) (Fin n) ℝ) →
    M ∈ Subgroup.closure (givensSet n) := by
  induction k with
  | zero =>
    intro M hM
    rw [eq_one_of_columnsStdFrom_one M hM]
    exact Subgroup.one_mem _
  | succ k ih =>
    intro M hM
    by_cases hk : k + 1 < n
    · exact mem_closure_of_clear_column ⟨k + 1, hk⟩ (by simp) ih (k + 1) 0 (by simp) M hM
        (fun p hp => absurd hp (Nat.not_lt_zero _)) (fun h => absurd h (by omega))
    · exact ih M (fun j hj => absurd j.isLt (by omega))
theorem exists_list_prod_eq (R : specialOrthogonalGroup (Fin n) ℝ) :
    ∃ l : List (specialOrthogonalGroup (Fin n) ℝ),
      (∀ Q ∈ l, IsPlaneRotation Q) ∧ l.prod = R := by
  have hR : R ∈ Subgroup.closure (givensSet n) :=
    mem_closure_of_columnsStdFrom n R (fun j hj => absurd j.isLt (by omega))
  have hR' : R ∈ Submonoid.closure (givensSet n ∪ (givensSet n)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hR
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hR'
  refine ⟨l, fun Q hQ => ?_, hprod⟩
  rcases hl Q hQ with h | h
  · exact isPlaneRotation_of_mem_givensSet h
  · have := inv_mem_givensSet (Set.mem_inv.1 h)
    rw [inv_inv] at this
    exact isPlaneRotation_of_mem_givensSet this
theorem reflect_mul_reflect : lastCoordReflection * lastCoordReflection = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [lastCoordReflection, Matrix.diagonal_apply]
theorem transpose_reflect : lastCoordReflectionᵀ = lastCoordReflection := by
  simp [lastCoordReflection]
theorem det_reflect : lastCoordReflection.det = -1 := by
  simp [lastCoordReflection, det_diagonal, Fin.prod_univ_succ]
theorem reflect_mem_orthogonalGroup : lastCoordReflection ∈ orthogonalGroup (Fin 4) ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_reflect, reflect_mul_reflect]
theorem orthogonalGroup_eq_union :
    (orthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) =
      (specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) ∪
        (fun R => R * lastCoordReflection) ''
          (specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) := by
  ext R
  simp only [Set.mem_union, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hR
    have hdet : R.det * R.det = 1 := by
      have := congrArg Matrix.det ((mem_orthogonalGroup_iff (Fin 4) ℝ).1 hR)
      rwa [det_mul, det_transpose, det_one] at this
    have hcases : R.det = 1 ∨ R.det = -1 := mul_self_eq_one_iff.1 hdet
    rcases hcases with h | h
    · exact Or.inl (mem_specialOrthogonalGroup_iff.2 ⟨hR, h⟩)
    · refine Or.inr ⟨R * lastCoordReflection, mem_specialOrthogonalGroup_iff.2
        ⟨Submonoid.mul_mem _ hR reflect_mem_orthogonalGroup, ?_⟩, ?_⟩
      · rw [det_mul, h, det_reflect]
        norm_num
      · rw [mul_assoc, reflect_mul_reflect, mul_one]
  · rintro (h | ⟨S, hS, rfl⟩)
    · exact (mem_specialOrthogonalGroup_iff.1 h).1
    · exact Submonoid.mul_mem _ (mem_specialOrthogonalGroup_iff.1 hS).1 reflect_mem_orthogonalGroup
theorem reflect_induced_by_hyperoctahedral (L m : ℕ) :
    ∃ σ ∈ PeriodicLattice.hyperoctahedralGroup L m, ∀ x : Fin 4 → ℝ,
      σ (fun μ => (x μ : AddCircle (PeriodicLattice.torusSide L m))) =
        fun μ => ((lastCoordReflection *ᵥ x) μ : AddCircle (PeriodicLattice.torusSide L m)) := by
  refine ⟨PeriodicLattice.signedCoordinatePerm L m 1 ![1, 1, 1, -1], ⟨1, _, rfl⟩, fun x => ?_⟩
  funext μ
  rw [lastCoordReflection_mulVec]
  fin_cases μ <;> simp [PeriodicLattice.signedCoordinatePerm]
theorem planeRotationsGenerate_holds : PlaneRotationsGenerate :=
  ⟨fun _ _ R => exists_list_prod_eq R, orthogonalGroup_eq_union, reflect_induced_by_hyperoctahedral⟩
end YangMills.Construction.EuclideanAnalysis.GivensGeneration
