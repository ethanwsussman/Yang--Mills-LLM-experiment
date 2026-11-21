import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.LogarithmsOfThePlainIterates
import YangMills.Construction.RunningCouplingSlope.NoiseAndStepKernelsAtARadius
import YangMills.Construction.RunningCouplingSlope.NoiseFamilyReadsNearCells
import YangMills.Construction.RunningCouplingSlope.PlainExpansionsDetermineTheBlocks
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreNearOne
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsAreBounded
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsReadTheDoubleBlock
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NoiseCovarianceLocality
open Tower PeriodicOperators
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
variable {L n k : ℕ}
private def meshRatio (L k m : ℕ) : ℂ :=
  ((Tower.meshAt L k (m + 1) ^ 4 / Tower.meshAt L k m ^ 4 : ℝ) : ℂ)
private theorem noiseCovariance_zero (a : ℝ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    noiseCovariance a L n k U 0 = 0 := rfl
private theorem noiseCovariance_succ_apply (a : ℝ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (m : ℕ)
    [Fintype (Fin 3 × Tower.PositiveEdge L n k m)] (i' i : Fin 3 × Tower.PositiveEdge L n k (m + 1)) :
    noiseCovariance a L n k U (m + 1) i' i =
      ((a⁻¹ : ℝ) : ℂ) * invRadiusDiag U m i' i +
        (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) *
          ∑ x, (∑ y, meanStepKernel L n k U m i' y * noiseCovariance a L n k U m y x) *
            (meshRatio L k m * meanStepKernel L n k U m i x) := by
  simp only [noiseCovariance, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    PeriodicOperators.compKernel, tsum_fintype, Tower.meshTranspose, PeriodicOperators.wTranspose,
    Tower.meshWeight, meshRatio]
private abbrev fineEdgesBelow {m : ℕ} (c : Tower.Edge L n k m) : Set (Tower.Edge L n k 0) :=
  PeriodicLattice.bondsInside (cubesOfEdge c)
private theorem fineEdgesBelow_mono {m m' : ℕ} {b : Tower.Edge L n k m} {c : Tower.Edge L n k m'}
    (h : cubesOfEdge b ⊆ cubesOfEdge c) : fineEdgesBelow b ⊆ fineEdgesBelow c :=
  fun _ hw => ⟨h hw.1, h hw.2⟩
private structure LocalityData (L n k : ℕ) (ρ : ℝ) : Prop where
  finite : ∀ m, Finite (Tower.PositiveEdge L n k m)
  mem_own : ∀ m ≤ k, ∀ y : Tower.Vertex L n k m,
    (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock m y
  support_sub : ∀ m < k, ∀ (i' : Fin 3 × Tower.PositiveEdge L n k (m + 1)) (i : Fin 3 × Tower.PositiveEdge L n k m),
    ∀ v ∈ smallFormBall L n k ρ, meanStepKernel L n k (Tower.remainderGaugeField v) m i' i ≠ 0 →
      cubesOfEdge i.2.1 ⊆ cubesOfEdge i'.2.1
  step_eq : ∀ m < k, ∀ (i' : Fin 3 × Tower.PositiveEdge L n k (m + 1)) (i : Fin 3 × Tower.PositiveEdge L n k m),
    ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ, EqOn v v' (fineEdgesBelow i'.2.1) →
      meanStepKernel L n k (Tower.remainderGaugeField v) m i' i =
        meanStepKernel L n k (Tower.remainderGaugeField v') m i' i
  radius_eq : ∀ m < k, ∀ c : Tower.Edge L n k (m + 1), ∀ v ∈ smallFormBall L n k ρ,
    ∀ v' ∈ smallFormBall L n k ρ, EqOn v v' (fineEdgesBelow c) →
      meanRadius (meanIterate (Tower.remainderGaugeField v) m) c =
        meanRadius (meanIterate (Tower.remainderGaugeField v') m) c
private theorem noiseCovariance_eq_zero_of_disjoint {ρ : ℝ} (H : LocalityData L n k ρ) (a : ℝ) :
    ∀ m ≤ k, ∀ i' i : Fin 3 × Tower.PositiveEdge L n k m, ∀ v ∈ smallFormBall L n k ρ,
      cubesOfEdge i'.2.1 ∩ cubesOfEdge i.2.1 = ∅ →
        noiseCovariance a L n k (Tower.remainderGaugeField v) m i' i = 0 := by
  intro m
  induction m with
  | zero =>
    intro _ i' i v _ _
    rw [noiseCovariance_zero]
    rfl
  | succ m ih =>
    intro hm i' i v hv hD
    have hmk : m < k := hm
    have := H.finite m
    let _ : Fintype (Tower.PositiveEdge L n k m) := Fintype.ofFinite _
    have hne : i' ≠ i := by
      rintro rfl
      have hp : (i'.2.1.source : PeriodicLattice.FourTorus L n) ∈
          cubesOfEdge i'.2.1 ∩ cubesOfEdge i'.2.1 :=
        ⟨Or.inl (H.mem_own _ hm _), Or.inl (H.mem_own _ hm _)⟩
      rw [hD] at hp
      exact hp
    have h₁ : invRadiusDiag (Tower.remainderGaugeField v) m i' i = 0 := by
      simp only [invRadiusDiag]
      exact if_neg hne
    rw [noiseCovariance_succ_apply, h₁, Finset.sum_eq_zero, mul_zero, mul_zero, add_zero]
    intro x _
    by_cases hx : meanStepKernel L n k (Tower.remainderGaugeField v) m i x = 0
    · rw [hx, mul_zero, mul_zero]
    · rw [Finset.sum_eq_zero, zero_mul]
      intro y _
      by_cases hy : meanStepKernel L n k (Tower.remainderGaugeField v) m i' y = 0
      · rw [hy, zero_mul]
      · rw [ih hmk.le y x v hv ?_, mul_zero]
        refine eq_empty_of_forall_notMem fun p hp => ?_
        have hq : p ∈ cubesOfEdge i'.2.1 ∩ cubesOfEdge i.2.1 :=
          ⟨H.support_sub m hmk i' y v hv hy hp.1, H.support_sub m hmk i x v hv hx hp.2⟩
        rw [hD] at hq
        exact hq
private theorem noiseCovariance_congr {ρ : ℝ} (H : LocalityData L n k ρ) (a : ℝ) :
    ∀ m ≤ k, ∀ i' i : Fin 3 × Tower.PositiveEdge L n k m, ∀ v ∈ smallFormBall L n k ρ,
      ∀ v' ∈ smallFormBall L n k ρ, EqOn v v' (fineEdgesBelow i'.2.1 ∪ fineEdgesBelow i.2.1) →
        noiseCovariance a L n k (Tower.remainderGaugeField v) m i' i =
          noiseCovariance a L n k (Tower.remainderGaugeField v') m i' i := by
  intro m
  induction m with
  | zero =>
    intro _ i' i v _ v' _ _
    rw [noiseCovariance_zero, noiseCovariance_zero]
  | succ m ih =>
    intro hm i' i v hv v' hv' h
    have hmk : m < k := hm
    have := H.finite m
    let _ : Fintype (Tower.PositiveEdge L n k m) := Fintype.ofFinite _
    have h' : EqOn v v' (fineEdgesBelow i'.2.1) := h.mono subset_union_left
    have hi : EqOn v v' (fineEdgesBelow i.2.1) := h.mono subset_union_right
    have h₁ : invRadiusDiag (Tower.remainderGaugeField v) m i' i =
        invRadiusDiag (Tower.remainderGaugeField v') m i' i := by
      simp only [invRadiusDiag]
      by_cases e : i' = i
      · rw [if_pos e, if_pos e, H.radius_eq m hmk i.2.1 v hv v' hv' hi]
      · rw [if_neg e, if_neg e]
    have h₂ : ∀ x, ∀ hx : meanStepKernel L n k (Tower.remainderGaugeField v) m i x ≠ 0,
        (∑ y, meanStepKernel L n k (Tower.remainderGaugeField v) m i' y *
            noiseCovariance a L n k (Tower.remainderGaugeField v) m y x) =
          ∑ y, meanStepKernel L n k (Tower.remainderGaugeField v') m i' y *
            noiseCovariance a L n k (Tower.remainderGaugeField v') m y x := by
      intro x hx
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← H.step_eq m hmk i' y v hv v' hv' h']
      by_cases hy : meanStepKernel L n k (Tower.remainderGaugeField v) m i' y = 0
      · rw [hy, zero_mul, zero_mul]
      · rw [ih hmk.le y x v hv v' hv' (h.mono (union_subset_union
          (fineEdgesBelow_mono (H.support_sub m hmk i' y v hv hy))
          (fineEdgesBelow_mono (H.support_sub m hmk i x v hv hx))))]
    have h₃ : (∑ x, (∑ y, meanStepKernel L n k (Tower.remainderGaugeField v) m i' y *
            noiseCovariance a L n k (Tower.remainderGaugeField v) m y x) *
          (meshRatio L k m * meanStepKernel L n k (Tower.remainderGaugeField v) m i x)) =
        ∑ x, (∑ y, meanStepKernel L n k (Tower.remainderGaugeField v') m i' y *
            noiseCovariance a L n k (Tower.remainderGaugeField v') m y x) *
          (meshRatio L k m * meanStepKernel L n k (Tower.remainderGaugeField v') m i x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← H.step_eq m hmk i x v hv v' hv' hi]
      by_cases hx : meanStepKernel L n k (Tower.remainderGaugeField v) m i x = 0
      · rw [hx, mul_zero, mul_zero, mul_zero]
      · rw [h₂ x hx]
    rw [noiseCovariance_succ_apply, noiseCovariance_succ_apply, h₁, h₃]
private theorem matrix_norm_transpose_le {I I' : Type} [Fintype I] [Fintype I'] [DecidableEq I]
    [DecidableEq I'] (A : Matrix I' I ℂ) : ‖A.transpose‖ ≤ ‖A‖ := by
  have nrm : ∀ {J : Type} [Fintype J] (f : J → ℂ),
      ‖(WithLp.toLp 2 (star f) : EuclideanSpace ℂ J)‖ = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ J)‖ := by
    intro J _ f
    simp [EuclideanSpace.norm_eq]
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  show ‖Matrix.toEuclideanLin A.transpose x‖ ≤ _
  have h := Matrix.l2_opNorm_mulVec A.conjTranspose (WithLp.toLp 2 (star (WithLp.ofLp x)))
  rw [Matrix.l2_opNorm_conjTranspose, nrm] at h
  have e : Matrix.toEuclideanLin A.transpose x =
      WithLp.toLp 2 (star (A.conjTranspose.mulVec (star (WithLp.ofLp x)))) := by
    show WithLp.toLp 2 (A.transpose.mulVec (WithLp.ofLp x)) = _
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [e, nrm]
  exact h
private theorem noiseCovariance_norm_le {a : ℝ} (ha : 0 < a) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (hfin : ∀ m, Finite (Tower.PositiveEdge L n k m))
    (hS : ∀ m < k, ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k m)]
        [Fintype (Fin 3 × Tower.PositiveEdge L n k (m + 1))]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k m)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k (m + 1))],
        ‖(Matrix.of (meanStepKernel L n k U m) :
          Matrix (Fin 3 × Tower.PositiveEdge L n k (m + 1)) (Fin 3 × Tower.PositiveEdge L n k m) ℂ)‖ ≤
          2 * ((L : ℝ) ^ 2)⁻¹)
    (hlen : ∀ m < k, ∀ c : Tower.Edge L n k (m + 1), ‖(meanRadius (meanIterate U m) c)⁻¹‖ ≤ 2) :
    ∀ m ≤ k, ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k m)]
      [DecidableEq (Fin 3 × Tower.PositiveEdge L n k m)],
      ‖(Matrix.of (noiseCovariance a L n k U m) :
        Matrix (Fin 3 × Tower.PositiveEdge L n k m) (Fin 3 × Tower.PositiveEdge L n k m) ℂ)‖ ≤ 4 / a := by
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hL0 : (0 : ℝ) < L := by linarith
  intro m
  induction m with
  | zero =>
    intro _ _ _
    have e : (Matrix.of (noiseCovariance a L n k U 0) :
        Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ) = 0 := rfl
    rw [e, norm_zero]
    positivity
  | succ m ih =>
    intro hm _ _
    have hmk : m < k := hm
    classical
    have := hfin m
    let _ : Fintype (Fin 3 × Tower.PositiveEdge L n k m) := Fintype.ofFinite _
    obtain ⟨S, hSd⟩ : ∃ S : Matrix (Fin 3 × Tower.PositiveEdge L n k (m + 1))
        (Fin 3 × Tower.PositiveEdge L n k m) ℂ, S = Matrix.of (meanStepKernel L n k U m) := ⟨_, rfl⟩
    obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin 3 × Tower.PositiveEdge L n k m)
        (Fin 3 × Tower.PositiveEdge L n k m) ℂ, G = Matrix.of (noiseCovariance a L n k U m) := ⟨_, rfl⟩
    have hSn : ‖S‖ ≤ 2 * ((L : ℝ) ^ 2)⁻¹ := by
      rw [hSd]
      exact hS m hmk
    have hGn : ‖G‖ ≤ 4 / a := by
      rw [hGd]
      exact ih hmk.le
    obtain ⟨d, hd⟩ : ∃ d : Fin 3 × Tower.PositiveEdge L n k (m + 1) → ℂ,
        d = fun i => (meanRadius (meanIterate U m) i.2.1)⁻¹ := ⟨_, rfl⟩
    have e : (Matrix.of (noiseCovariance a L n k U (m + 1)) : Matrix _ _ ℂ) =
        ((a⁻¹ : ℝ) : ℂ) • Matrix.diagonal d +
          (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) • ((S * G) * (meshRatio L k m • S.transpose)) := by
      ext i' i
      have hdiag : invRadiusDiag U m i' i = Matrix.diagonal d i' i := by
        by_cases h : i' = i
        · subst h
          rw [Matrix.diagonal_apply_eq, hd]
          simp [invRadiusDiag]
        · rw [Matrix.diagonal_apply_ne _ h]
          simp [invRadiusDiag, h]
      rw [Matrix.of_apply, noiseCovariance_succ_apply, hdiag]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.transpose_apply, hSd, hGd, Matrix.of_apply]
    have hdn : ‖(Matrix.diagonal d : Matrix _ _ ℂ)‖ ≤ 2 := by
      rw [Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      rw [hd]
      exact hlen m hmk i.2.1
    have hl1 : Tower.meshAt L k (m + 1) = L * Tower.meshAt L k m := by
      unfold Tower.meshAt
      rw [← zpow_one_add₀ hL0.ne']
      congr 1
      push_cast
      ring
    have hl0 : 0 < Tower.meshAt L k m := zpow_pos hL0 _
    have hw : ‖meshRatio L k m‖ = (L : ℝ) ^ 4 := by
      unfold meshRatio
      rw [Complex.norm_real, hl1, mul_pow, mul_div_assoc, div_self (by positivity), mul_one,
        Real.norm_of_nonneg (by positivity)]
    have hT := matrix_norm_transpose_le S
    have hs0 := norm_nonneg S
    have hg0 := norm_nonneg G
    have h₁ : ‖((a⁻¹ : ℝ) : ℂ) • (Matrix.diagonal d : Matrix _ _ ℂ)‖ ≤ 2 / a := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc a⁻¹ * _ ≤ a⁻¹ * 2 := mul_le_mul_of_nonneg_left hdn (by positivity)
        _ = 2 / a := by ring
    have hprod : ‖(S * G) * (meshRatio L k m • S.transpose)‖ ≤
        ‖S‖ * ‖G‖ * ((L : ℝ) ^ 4 * ‖S‖) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [norm_smul, hw]
      exact mul_le_mul (Matrix.l2_opNorm_mul _ _)
        (mul_le_mul_of_nonneg_left hT (by positivity)) (by positivity) (by positivity)
    have hLsq : (169 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 169 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hLsq
    have hs1 : ‖S‖ ≤ 2 / 169 := by linarith
    have ht : (L : ℝ) ^ 2 * ‖S‖ ≤ 2 := by
      have h := mul_le_mul_of_nonneg_left hSn (show 0 ≤ (L : ℝ) ^ 2 by positivity)
      have e₂ : (L : ℝ) ^ 2 * (2 * ((L : ℝ) ^ 2)⁻¹) = 2 := by
        field_simp
      linarith
    have h₂ : ‖(((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) • ((S * G) * (meshRatio L k m • S.transpose))‖ ≤
        2 / a := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have e₃ : (L : ℝ) ^ (-2 : ℤ) * (‖S‖ * ‖G‖ * ((L : ℝ) ^ 4 * ‖S‖)) =
          ((L : ℝ) ^ 2 * ‖S‖) * ‖S‖ * ‖G‖ := by
        rw [zpow_neg, zpow_ofNat]
        field_simp
      calc (L : ℝ) ^ (-2 : ℤ) * _ ≤ (L : ℝ) ^ (-2 : ℤ) * (‖S‖ * ‖G‖ * ((L : ℝ) ^ 4 * ‖S‖)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = ((L : ℝ) ^ 2 * ‖S‖) * ‖S‖ * ‖G‖ := e₃
        _ ≤ 2 * (2 / 169) * (4 / a) := by
            refine mul_le_mul (mul_le_mul ht hs1 hs0 (by norm_num)) hGn hg0 (by norm_num)
        _ ≤ 2 / a := by
            rw [show 2 * (2 / 169 : ℝ) * (4 / a) = (16 / 169) * (1 / a) * 1 by ring,
              show 2 / a = 2 * (1 / a) * 1 by ring]
            have : 0 < 1 / a := by positivity
            nlinarith
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 2 / a + 2 / a := add_le_add h₁ h₂
      _ = 4 / a := by ring
theorem noiseCovarianceIsLocalNearCells_of (hK : StepAndNoiseKernelsNearIdentity)
    (hR : StepKernelLocality)
    (hB : StepKernelNormBound)
    (hN : MeanIteratesNearIdentity.Claim)
    (hRows : MeanExpansionsLocal.Claim)
    (hLog : MeanIterateLogarithms)
    (hC : NeighbouringFineVertexCells)
    (hT : TopEdgesAndCubes) : NoiseCovarianceIsLocalNearCells := by
  intro a ha L hL
  obtain ⟨r₁, hr₁, HK⟩ := hK L hL
  obtain ⟨ρ₂, hρ₂, HR⟩ := hR L hL
  obtain ⟨ρ₃, hρ₃, HB⟩ := hB L hL
  obtain ⟨ρ₄, hρ₄, HL⟩ := hLog L hL
  obtain ⟨ρ₅, hρ₅, HW⟩ := hRows L hL
  obtain ⟨ρ₆, hρ₆, HN⟩ := hN L hL (min r₁ ρ₃) (lt_min hr₁ hρ₃)
  obtain ⟨ρ, hρ, h₂, h₄, h₅, h₆⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₂ ∧ ρ ≤ ρ₄ ∧ ρ ≤ ρ₅ ∧ ρ ≤ ρ₆ :=
    ⟨min (min ρ₂ ρ₄) (min ρ₅ ρ₆), lt_min (lt_min hρ₂ hρ₄) (lt_min hρ₅ hρ₆),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨ρ, 4 / a, 6, hρ, by positivity, by norm_num, fun k hk => ⟨0, fun n _ hn => ?_⟩⟩
  intro _ _ _ _ _ _ _ _
  have hsmall : ∀ {ρ' : ℝ}, ρ ≤ ρ' → ∀ {v}, v ∈ smallFormBall L n k ρ → v ∈ smallFormBall L n k ρ' :=
    fun h v hv => ⟨hv.1, hv.2.trans (ENNReal.ofReal_le_ofReal h)⟩
  have hLpos : 0 < L := by have := hL.2; omega
  have hfin : ∀ m, Finite (Tower.PositiveEdge L n k m) := fun m =>
    have : Finite (Tower.Vertex L n k m) := SeparatedSequences.BaseParameters.site_finite hLpos n _
    have : Finite (Tower.Edge L n k m) :=
      Finite.of_injective (fun b : Tower.Edge L n k m => (b.source, b.target)) fun b b' hb =>
        PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    Subtype.finite
  obtain ⟨hself, hstep⟩ := HR n k hn hk
  obtain ⟨-, -, hrow⟩ := HW n k hn hk
  have H : LocalityData L n k ρ :=
    { finite := hfin
      mem_own := hself
      support_sub := fun m hm i' i v hv => (hstep m hm i' i v (hsmall h₂ hv)).1
      step_eq := fun m hm i' i v hv v' hv' =>
        (hstep m hm i' i v (hsmall h₂ hv)).2 v' (hsmall h₂ hv')
      radius_eq := fun m hm c v hv v' hv' => hrow m hm c v (hsmall h₅ hv) v' (hsmall h₅ hv') }
  obtain ⟨hzero, hends, huniq⟩ := hT L hL n k hn hk
  obtain ⟨hsymm, htri, hcell, -⟩ := hC L hL n k
  have hcellOf : ∀ {x : Tower.Vertex L n k 0} {e : Tower.Vertex L n k k},
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k e → fineVertexCell x = e :=
    fun {x} {e} h => huniq _ _ _ (hcell x) h
  have hEnd : ∀ (c : Tower.Edge L n k k) (e : Tower.Vertex L n k k), (e = c.source ∨ e = c.target) →
      cellDist e c.source ≤ 2 := by
    intro c e he
    rcases he with rfl | rfl
    · rw [hzero]
      norm_num
    · rw [hsymm]
      exact hends c
  have hShare : ∀ (c c' : Tower.Edge L n k k), (cubesOfEdge c ∩ cubesOfEdge c').Nonempty →
      ∃ s : Tower.Vertex L n k k, (s = c.source ∨ s = c.target) ∧ (s = c'.source ∨ s = c'.target) := by
    rintro c c' ⟨p, h₁ | h₁, h₂ | h₂⟩
    · exact ⟨_, Or.inl rfl, Or.inl (huniq _ _ p h₁ h₂)⟩
    · exact ⟨_, Or.inl rfl, Or.inr (huniq _ _ p h₁ h₂)⟩
    · exact ⟨_, Or.inr rfl, Or.inl (huniq _ _ p h₁ h₂)⟩
    · exact ⟨_, Or.inr rfl, Or.inr (huniq _ _ p h₁ h₂)⟩
  have hNear : ∀ (c c' : Tower.Edge L n k k), (cubesOfEdge c ∩ cubesOfEdge c').Nonempty →
      cellDist c.source c'.source ≤ 4 := by
    intro c c' h
    obtain ⟨s, hs, hs'⟩ := hShare c c' h
    have h₁ := hEnd c s hs
    have h₂ := hEnd c' s hs'
    rw [hsymm] at h₁
    linarith [htri c.source s c'.source]
  have hPoint : ∀ (c c' : Tower.Edge L n k k), (cubesOfEdge c ∩ cubesOfEdge c').Nonempty →
      ∀ x : Tower.Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ cubesOfEdge c ∪ cubesOfEdge c' →
        cellDist (fineVertexCell x) c.source ≤ 6 := by
    intro c c' h x hx
    have far : ∀ e : Tower.Vertex L n k k, (e = c'.source ∨ e = c'.target) → cellDist e c.source ≤ 6 := by
      intro e he
      have h₁ := hEnd c' e he
      have h₂ := hNear c c' h
      rw [hsymm c.source] at h₂
      linarith [htri e c'.source c.source]
    rcases hx with (hx | hx) | (hx | hx)
    · rw [hcellOf hx]
      linarith [hEnd c c.source (Or.inl rfl)]
    · rw [hcellOf hx]
      linarith [hEnd c c.target (Or.inr rfl)]
    · rw [hcellOf hx]
      exact far _ (Or.inl rfl)
    · rw [hcellOf hx]
      exact far _ (Or.inr rfl)
  refine ⟨fun p q => ?_, fun v hv => ?_, fun p q v hv v' hv' h => ?_, fun v hv p q hr => ?_⟩
  · refine (HK n k hn hk).2 ρ hρ (fun v hv hs m hm => ?_) a k le_rfl p q
    obtain ⟨e₁, e₂⟩ := HN n k hn hk v (hsmall h₆ ⟨hv, hs.le⟩) m hm
    exact ⟨e₁, fun b => (e₂ b).trans_le (min_le_left _ _)⟩
  · have hU := fun m hm => HN n k hn hk v (hsmall h₆ hv) m hm
    refine noiseCovariance_norm_le ha hL _ hfin
      (HB n k hn hk _ fun m hm => ⟨(hU m hm).1, fun b => ((hU m hm).2 b).le.trans (min_le_right _ _)⟩)
      (fun m hm c => ((HL n k hn hk v (hsmall h₄ hv)).2.2 m hm c).2) k le_rfl
  · by_cases hD : cubesOfEdge p.2.1 ∩ cubesOfEdge q.2.1 = ∅
    · exact (noiseCovariance_eq_zero_of_disjoint H a k le_rfl p q v hv hD).trans
        (noiseCovariance_eq_zero_of_disjoint H a k le_rfl p q v' hv' hD).symm
    · have hne := nonempty_iff_ne_empty.2 hD
      refine noiseCovariance_congr H a k le_rfl p q v hv v' hv' (h.mono ?_)
      have hc := hPoint p.2.1 q.2.1 hne
      rintro w (hw | hw)
      · exact ⟨hc _ (Or.inl hw.1), hc _ (Or.inl hw.2)⟩
      · exact ⟨hc _ (Or.inr hw.1), hc _ (Or.inr hw.2)⟩
  · refine noiseCovariance_eq_zero_of_disjoint H a k le_rfl p q v hv ?_
    by_contra hD
    have h₁ := hNear p.2.1 q.2.1 (nonempty_iff_ne_empty.2 hD)
    have h₂ : cellDist (edgeCell p) (edgeCell q) ≤ 4 := h₁
    linarith
end YangMills.Construction.RunningCouplingSlope.NoiseCovarianceLocality
end
