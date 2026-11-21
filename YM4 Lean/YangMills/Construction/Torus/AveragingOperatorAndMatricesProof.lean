import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedDataProof
import YangMills.Construction.Weighted.GivenChainGeneral
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.AvgMatrix
section Matrices
def expWeightedNorm {ι : Type*} (ρ : ι → ι → ℝ) (δ : ℝ) (M : ι → ι → ℝ) : ℝ :=
  max (⨆ i, ∑ᶠ j, |M i j| * Real.exp (δ * ρ i j))
    (⨆ j, ∑ᶠ i, |M i j| * Real.exp (δ * ρ i j))
set_option linter.unusedSectionVars false
variable {ι : Type*} [Fintype ι] (ρ : ι → ι → ℝ)
theorem rowSum_le_expWeightedNorm (δ : ℝ) (M : ι → ι → ℝ) (i : ι) :
    ∑ j, |M i j| * Real.exp (δ * ρ i j) ≤ expWeightedNorm ρ δ M := by
  rw [← finsum_eq_sum_of_fintype]
  exact le_max_of_le_left (le_ciSup (f := fun i => ∑ᶠ j, |M i j| * Real.exp (δ * ρ i j))
    (Set.finite_range _).bddAbove i)
theorem colSum_le_expWeightedNorm (δ : ℝ) (M : ι → ι → ℝ) (j : ι) :
    ∑ i, |M i j| * Real.exp (δ * ρ i j) ≤ expWeightedNorm ρ δ M := by
  rw [← finsum_eq_sum_of_fintype]
  exact le_max_of_le_right (le_ciSup (f := fun j => ∑ᶠ i, |M i j| * Real.exp (δ * ρ i j))
    (Set.finite_range _).bddAbove j)
theorem expWeightedNorm_nonneg (δ : ℝ) (M : ι → ι → ℝ) : 0 ≤ expWeightedNorm ρ δ M :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => finsum_nonneg fun _ =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
theorem expWeightedNorm_le_of {δ C : ℝ} {M : ι → ι → ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, |M i j| * Real.exp (δ * ρ i j) ≤ C)
    (hcol : ∀ j, ∑ i, |M i j| * Real.exp (δ * ρ i j) ≤ C) : expWeightedNorm ρ δ M ≤ C := by
  refine max_le (Real.iSup_le (fun i => ?_) hC) (Real.iSup_le (fun j => ?_) hC)
  · rw [finsum_eq_sum_of_fintype]
    exact hrow i
  · rw [finsum_eq_sum_of_fintype]
    exact hcol j
theorem expWeightedNorm_matProd_le (hρ : ∀ a b c, ρ a c ≤ ρ a b + ρ b c) {δ : ℝ} (hδ : 0 ≤ δ)
    (M M' : ι → ι → ℝ) :
    expWeightedNorm ρ δ (matProd M M') ≤ expWeightedNorm ρ δ M * expWeightedNorm ρ δ M' := by
  set P : ι → ι → ℝ := fun a b => |M a b| * Real.exp (δ * ρ a b) with hP
  set Q : ι → ι → ℝ := fun a b => |M' a b| * Real.exp (δ * ρ a b) with hQ
  have hP0 : ∀ a b, 0 ≤ P a b := fun a b => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hQ0 : ∀ a b, 0 ≤ Q a b := fun a b => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hN := expWeightedNorm_nonneg ρ δ M
  have hN' := expWeightedNorm_nonneg ρ δ M'
  have hexp : ∀ a b c, Real.exp (δ * ρ a c) ≤ Real.exp (δ * ρ a b) * Real.exp (δ * ρ b c) := by
    intro a b c
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hρ a b c) hδ)
  have hterm : ∀ a c, |matProd M M' a c| * Real.exp (δ * ρ a c) ≤ ∑ b, P a b * Q b c := by
    intro a c
    have h1 : |matProd M M' a c| ≤ ∑ b, |M a b| * |M' b c| := by
      simp only [matProd, finsum_eq_sum_of_fintype]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      simp [abs_mul]
    calc |matProd M M' a c| * Real.exp (δ * ρ a c)
        ≤ (∑ b, |M a b| * |M' b c|) * Real.exp (δ * ρ a c) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = ∑ b, |M a b| * |M' b c| * Real.exp (δ * ρ a c) := Finset.sum_mul _ _ _
      _ ≤ ∑ b, P a b * Q b c := Finset.sum_le_sum fun b _ => by
          have h0 : 0 ≤ |M a b| * |M' b c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          calc |M a b| * |M' b c| * Real.exp (δ * ρ a c)
              ≤ |M a b| * |M' b c| * (Real.exp (δ * ρ a b) * Real.exp (δ * ρ b c)) :=
                mul_le_mul_of_nonneg_left (hexp a b c) h0
            _ = P a b * Q b c := by simp only [hP, hQ]; ring
  refine expWeightedNorm_le_of ρ (mul_nonneg hN hN') (fun a => ?_) (fun c => ?_)
  · calc ∑ c, |matProd M M' a c| * Real.exp (δ * ρ a c)
        ≤ ∑ c, ∑ b, P a b * Q b c := Finset.sum_le_sum fun c _ => hterm a c
      _ = ∑ b, P a b * ∑ c, Q b c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ b, P a b * expWeightedNorm ρ δ M' :=
          Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_left (rowSum_le_expWeightedNorm ρ δ M' b) (hP0 a b)
      _ = (∑ b, P a b) * expWeightedNorm ρ δ M' := (Finset.sum_mul _ _ _).symm
      _ ≤ expWeightedNorm ρ δ M * expWeightedNorm ρ δ M' :=
          mul_le_mul_of_nonneg_right (rowSum_le_expWeightedNorm ρ δ M a) hN'
  · calc ∑ a, |matProd M M' a c| * Real.exp (δ * ρ a c)
        ≤ ∑ a, ∑ b, P a b * Q b c := Finset.sum_le_sum fun a _ => hterm a c
      _ = ∑ b, (∑ a, P a b) * Q b c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ b, expWeightedNorm ρ δ M * Q b c :=
          Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_right (colSum_le_expWeightedNorm ρ δ M b) (hQ0 b c)
      _ = expWeightedNorm ρ δ M * ∑ b, Q b c := (Finset.mul_sum _ _ _).symm
      _ ≤ expWeightedNorm ρ δ M * expWeightedNorm ρ δ M' :=
          mul_le_mul_of_nonneg_left (colSum_le_expWeightedNorm ρ δ M' c) hN
theorem abs_entry_le (δ : ℝ) (M : ι → ι → ℝ) (i j : ι) :
    |M i j| ≤ expWeightedNorm ρ δ M * Real.exp (-δ * ρ i j) := by
  have h1 : |M i j| * Real.exp (δ * ρ i j) ≤ expWeightedNorm ρ δ M :=
    (Finset.single_le_sum (f := fun b => |M i b| * Real.exp (δ * ρ i b))
      (fun _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ j)).trans
      (rowSum_le_expWeightedNorm ρ δ M i)
  have h2 : Real.exp (δ * ρ i j) * Real.exp (-δ * ρ i j) = 1 := by
    rw [← Real.exp_add]
    simp
  calc |M i j| = |M i j| * Real.exp (δ * ρ i j) * Real.exp (-δ * ρ i j) := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ expWeightedNorm ρ δ M * Real.exp (-δ * ρ i j) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
theorem expWeightedNorm_zero_le (hρ : ∀ a b, 0 ≤ ρ a b) {δ : ℝ} (hδ : 0 ≤ δ) (M : ι → ι → ℝ) :
    expWeightedNorm ρ 0 M ≤ expWeightedNorm ρ δ M := by
  have hexp : ∀ a b, Real.exp (0 * ρ a b) ≤ Real.exp (δ * ρ a b) := fun a b =>
    Real.exp_le_exp.2 (by rw [zero_mul]; exact mul_nonneg hδ (hρ a b))
  refine expWeightedNorm_le_of ρ (expWeightedNorm_nonneg ρ δ M) (fun i => ?_) (fun j => ?_)
  · exact (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hexp i b)
      (abs_nonneg _)).trans (rowSum_le_expWeightedNorm ρ δ M i)
  · exact (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hexp b j)
      (abs_nonneg _)).trans (colSum_le_expWeightedNorm ρ δ M j)
theorem l2OpNorm_le_of_schur {C : ℝ} (hC : 0 ≤ C) (M : ι → ι → ℝ)
    (hrow : ∀ i, ∑ j, |M i j| ≤ C) (hcol : ∀ j, ∑ i, |M i j| ≤ C) :
    l2OpNorm M ≤ C := by
  refine csInf_le ⟨0, fun c hc' => hc'.1⟩ ⟨hC, fun u => ?_⟩
  simp only [finsum_eq_sum_of_fintype]
  have h1 : ∀ i, (∑ j, M i j * u j) ^ 2 ≤ C * ∑ j, |M i j| * u j ^ 2 := by
    intro i
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => M i j * u j) (f := fun j => |M i j|)
      (g := fun j => |M i j| * u j ^ 2) (fun _ _ => abs_nonneg _)
      (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun j _ => le_of_eq (by
        rw [mul_pow, ← mul_assoc, abs_mul_abs_self, sq (M i j)]))
    exact h.trans (mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  have key : ∑ i, (∑ j, M i j * u j) ^ 2 ≤ C ^ 2 * ∑ i, u i ^ 2 := by
    calc ∑ i, (∑ j, M i j * u j) ^ 2 ≤ ∑ i, C * ∑ j, |M i j| * u j ^ 2 :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = C * ∑ j, (∑ i, |M i j|) * u j ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          exact congrArg _ (Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm)
      _ ≤ C * ∑ j, C * u j ^ 2 := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hcol b) (sq_nonneg _)) hC
      _ = C ^ 2 * ∑ i, u i ^ 2 := by rw [← Finset.mul_sum]; ring
  calc Real.sqrt (∑ i, (∑ j, M i j * u j) ^ 2) ≤ Real.sqrt (C ^ 2 * ∑ i, u i ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = C * Real.sqrt (∑ i, u i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
theorem l2OpNorm_le_expWeightedNorm_zero (M : ι → ι → ℝ) :
    l2OpNorm M ≤ expWeightedNorm ρ 0 M := by
  refine l2OpNorm_le_of_schur (expWeightedNorm_nonneg ρ 0 M) M (fun i => ?_) (fun j => ?_)
  · simpa using rowSum_le_expWeightedNorm ρ 0 M i
  · simpa using colSum_le_expWeightedNorm ρ 0 M j
open Classical in
def zeroExtend (X : Set ι) (M : ↥X → ↥X → ℝ) : ι → ι → ℝ :=
  fun i j => if h : i ∈ X ∧ j ∈ X then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
theorem zeroExtend_coe (X : Set ι) (M : ↥X → ↥X → ℝ) (i j : ↥X) :
    zeroExtend X M i j = M i j := by
  simp [zeroExtend]
theorem zeroExtend_of_not_mem_left (X : Set ι) (M : ↥X → ↥X → ℝ) {i : ι} (hi : i ∉ X) (j : ι) :
    zeroExtend X M i j = 0 := by
  simp [zeroExtend, hi]
theorem zeroExtend_of_not_mem_right (X : Set ι) (M : ↥X → ↥X → ℝ) (i : ι) {j : ι} (hj : j ∉ X) :
    zeroExtend X M i j = 0 := by
  simp [zeroExtend, hj]
theorem finsum_eq_finsum_subtype_of_vanish (X : Set ι) {g : ι → ℝ} (hg : ∀ i, i ∉ X → g i = 0) :
    ∑ᶠ i, g i = ∑ᶠ i : ↥X, g i := by
  rw [finsum_set_coe_eq_finsum_mem]
  exact (finsum_mem_univ g).symm.trans (finsum_mem_inter_support_eq' g univ X fun i hi =>
    ⟨fun _ => by_contra fun h => hi (hg i h), fun _ => trivial⟩)
theorem zeroExtend_matProd (X : Set ι) (M M' : ↥X → ↥X → ℝ) :
    zeroExtend X (matProd M M') = matProd (zeroExtend X M) (zeroExtend X M') := by
  funext i k
  by_cases hi : i ∈ X
  · by_cases hk : k ∈ X
    · lift i to ↥X using hi
      lift k to ↥X using hk
      rw [zeroExtend_coe]
      simp only [matProd]
      rw [finsum_eq_finsum_subtype_of_vanish X
        (g := fun b => zeroExtend X M i b * zeroExtend X M' b k)
        (fun b hb => by simp [zeroExtend_of_not_mem_right X M _ hb])]
      exact finsum_congr fun b => by rw [zeroExtend_coe, zeroExtend_coe]
    · rw [zeroExtend_of_not_mem_right _ _ _ hk]
      simp [matProd, zeroExtend_of_not_mem_right X M' _ hk]
  · rw [zeroExtend_of_not_mem_left _ _ hi]
    simp [matProd, zeroExtend_of_not_mem_left X M hi]
theorem rowSum_le_zeroExtend (X : Set ι) [Fintype ↥X] (M : ↥X → ↥X → ℝ) (i : ↥X) :
    ∑ j, |M i j| ≤ expWeightedNorm ρ 0 (zeroExtend X M) := by
  refine le_trans (le_of_eq ?_) (rowSum_le_expWeightedNorm ρ 0 (zeroExtend X M) i)
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype,
    finsum_eq_finsum_subtype_of_vanish X (g := fun b => |zeroExtend X M i b|)
      (fun b hb => by simp [zeroExtend_of_not_mem_right X M _ hb])]
  exact finsum_congr fun b => by rw [zeroExtend_coe]
theorem colSum_le_zeroExtend (X : Set ι) [Fintype ↥X] (M : ↥X → ↥X → ℝ) (j : ↥X) :
    ∑ i, |M i j| ≤ expWeightedNorm ρ 0 (zeroExtend X M) := by
  refine le_trans (le_of_eq ?_) (colSum_le_expWeightedNorm ρ 0 (zeroExtend X M) j)
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype,
    finsum_eq_finsum_subtype_of_vanish X (g := fun b => |zeroExtend X M b j|)
      (fun b hb => by simp [zeroExtend_of_not_mem_left X M hb])]
  exact finsum_congr fun b => by rw [zeroExtend_coe]
theorem l2OpNorm_le_zeroExtend (X : Set ι) (M : ↥X → ↥X → ℝ) :
    l2OpNorm M ≤ expWeightedNorm ρ 0 (zeroExtend X M) := by
  classical
  exact l2OpNorm_le_of_schur (expWeightedNorm_nonneg ρ 0 _) M
    (rowSum_le_zeroExtend ρ X M) (colSum_le_zeroExtend ρ X M)
end Matrices
section Basis
variable {D : TorusData} (B : SeparatedChain D)
theorem chainScale_pos (n : ℕ) : 0 < D.scale n := by
  have hL : 0 < (D.L : ℝ) := by
    have := D.blocking.three_le_factor
    exact_mod_cast (by omega : 0 < D.L)
  exact mul_pos (pow_pos hL n) D.bareSpacing_pos
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := chainScale_pos _
theorem siteScale_eq_pow (y : D.Space) :
    B.siteScale y = (D.L : ℝ) ^ B.level y * D.scale 0 := by
  simp [SeparatedChain.siteScale, SeparatedChain.level, TorusData.scale]
theorem zpow_neg_two_eq (x : ℝ) : x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := by
  rw [zpow_neg]
  norm_cast
theorem allSites_finite : Finite ↥B.allSites := by
  have := D.bareSite_finite
  have hsub : B.allSites ⊆ Subtype.val '' (univ : Set D.BareSite) := by
    intro y hy
    simp only [SeparatedChain.allSites, mem_iUnion] at hy
    obtain ⟨n, _, hy⟩ := hy
    obtain ⟨k, hk⟩ := hy.1
    refine ⟨⟨y, ⟨fun μ => (D.L : ℤ) ^ n * k μ, ?_⟩⟩, trivial, rfl⟩
    rw [hk]
    congr 1
    funext μ
    simp only [TorusData.scale]
    push_cast
    ring
  exact ((toFinite _).subset hsub).to_subtype
theorem basisVec_self (y : ↥B.allSites) :
    B.basisVec y y = (B.siteScale y ^ 2)⁻¹ := by
  simp [SeparatedChain.basisVec]
theorem basisVec_of_ne {y y' : ↥B.allSites} (h : y' ≠ y) : B.basisVec y y' = 0 := by
  simp [SeparatedChain.basisVec, h]
theorem layerInner_basisVec (y : ↥B.allSites) (v : B.LayerFn) :
    B.layerInner (B.basisVec y) v = B.siteScale y ^ 2 * v y := by
  unfold SeparatedChain.layerInner
  rw [finsum_eq_single _ y (fun y' h => by rw [basisVec_of_ne B h]; simp), basisVec_self]
  have := (siteScale_pos B y).ne'
  field_simp
theorem matrixOf_apply (K : B.LayerOp) (y y' : ↥B.allSites) :
    B.matrixOf K y y' = B.siteScale y ^ 2 * K (B.basisVec y') y :=
  layerInner_basisVec B y _
def weightedCoords (u : ↥B.allSites → ℝ) : B.LayerFn := fun y => (B.siteScale y ^ 2)⁻¹ * u y
theorem weightedCoords_eq_sum [Fintype ↥B.allSites] (u : ↥B.allSites → ℝ) :
    weightedCoords B u = ∑ y', u y' • B.basisVec y' := by
  funext y
  rw [Finset.sum_apply, Finset.sum_eq_single y (fun y' _ h => by simp [basisVec_of_ne B h.symm])
    (fun h => absurd (Finset.mem_univ y) h)]
  simp [weightedCoords, basisVec_self, mul_comm]
theorem weightedCoords_scaled (v : B.LayerFn) :
    weightedCoords B (fun y : ↥B.allSites => B.siteScale y ^ 2 * v y) = v := by
  funext y
  have := (siteScale_pos B y).ne'
  simp only [weightedCoords]
  field_simp
theorem matrixOf_mulVec [Fintype ↥B.allSites] (K : B.LayerOp) (u : ↥B.allSites → ℝ)
    (y : ↥B.allSites) :
    ∑ y', B.matrixOf K y y' * u y' = B.siteScale y ^ 2 * K (weightedCoords B u) y := by
  rw [weightedCoords_eq_sum, map_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [matrixOf_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  ring
theorem matrixOf_comp (K K' : B.LayerOp) :
    B.matrixOf (K ∘ₗ K') = matProd (B.matrixOf K) (B.matrixOf K') := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  funext y y''
  simp only [matProd, finsum_eq_sum_of_fintype]
  rw [matrixOf_mulVec, matrixOf_apply]
  have hu : (fun b => B.matrixOf K' b y'') =
      fun b : ↥B.allSites => B.siteScale b ^ 2 * K' (B.basisVec y'') b := by
    funext b
    exact matrixOf_apply B K' b y''
  rw [hu, weightedCoords_scaled]
  rfl
theorem layerSpaceNorm_eq [Fintype ↥B.allSites] (v : B.LayerFn) :
    B.layerSpaceNorm v = Real.sqrt (∑ y : ↥B.allSites, (B.siteScale y ^ 2 * v y) ^ 2) := by
  unfold SeparatedChain.layerSpaceNorm SeparatedChain.layerInner
  rw [finsum_eq_sum_of_fintype]
  exact congrArg _ (Finset.sum_congr rfl fun y _ => by ring)
theorem layerSpaceNorm_weightedCoords [Fintype ↥B.allSites] (u : ↥B.allSites → ℝ) :
    B.layerSpaceNorm (weightedCoords B u) = Real.sqrt (∑ y, u y ^ 2) := by
  rw [layerSpaceNorm_eq]
  refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
  have := (siteScale_pos B y).ne'
  simp only [weightedCoords]
  field_simp
theorem l2OpNorm_matrixOf (K : B.LayerOp) :
    l2OpNorm (B.matrixOf K) = B.layerOpNorm K := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  have hu : ∀ u : ↥B.allSites → ℝ,
      Real.sqrt (∑ᶠ y, (∑ᶠ y', B.matrixOf K y y' * u y') ^ 2) =
        B.layerSpaceNorm (K (weightedCoords B u)) := by
    intro u
    rw [layerSpaceNorm_eq]
    simp only [finsum_eq_sum_of_fintype, matrixOf_mulVec]
  have hv : ∀ u : ↥B.allSites → ℝ,
      Real.sqrt (∑ᶠ y, u y ^ 2) = B.layerSpaceNorm (weightedCoords B u) := by
    intro u
    rw [layerSpaceNorm_weightedCoords, finsum_eq_sum_of_fintype]
  unfold l2OpNorm SeparatedChain.layerOpNorm
  congr 1
  ext C
  simp only [mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨fun h w => ?_, fun h u => ?_⟩
  · have h1 := h fun y : ↥B.allSites => B.siteScale y ^ 2 * w y
    rwa [hu, hv, weightedCoords_scaled] at h1
  · rw [hu, hv]
    exact h _
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨Γ, -, -, -, rfl⟩
  have hlen : ∀ (A : Set D.Space), 0 ≤ TorusMetric.pathLengthIn D.side Γ A := by
    intro A
    unfold TorusMetric.pathLengthIn
    refine List.sum_nonneg ?_
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ENNReal.toReal_nonneg
  unfold SeparatedChain.weightedLength
  exact add_nonneg (Finset.sum_nonneg fun n _ =>
    mul_nonneg (inv_nonneg.2 (chainScale_pos n).le) (hlen _))
    (mul_nonneg (inv_nonneg.2 (chainScale_pos 0).le) (hlen _))
end Basis
section Blocks
variable {D : TorusData} (B : SeparatedChain D)
  (hb : GivenChainGeneral.BlockPartition B)
  (hc : ∀ y ∈ B.allSites, ((B.block y).ncard : ℝ) = (D.L : ℝ) ^ (B.level y * 4))
theorem layerEval_coe (w : B.LayerFn) (y : ↥B.allSites) : B.layerEval w y = w y := by
  simp [SeparatedChain.layerEval]
theorem avgOp_apply (f : ↥B.bareSpace) (y : ↥B.allSites) :
    B.avgOp f y = ((D.L : ℝ) ^ (B.level y * 4))⁻¹ *
      ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x := rfl
theorem siteScale_pow_four_mul_inv (y : D.Space) :
    B.siteScale y ^ 4 * ((D.L : ℝ) ^ (B.level y * 4))⁻¹ = D.scale 0 ^ 4 := by
  have hL : (D.L : ℝ) ^ (B.level y * 4) ≠ 0 := by
    have := D.blocking.three_le_factor
    have hL : (D.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.L ≠ 0)
    exact pow_ne_zero _ hL
  rw [siteScale_eq_pow, mul_pow, ← pow_mul]
  field_simp
include hb
theorem block_subset_bareSites {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by
  rw [← hb.iUnion_block]
  exact subset_biUnion_of_mem (u := B.block) hy
theorem blockCenter_spec {x : D.BareSite} (hx : x ∈ D.bareSites (B.stage 0)) :
    B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
  rw [← hb.iUnion_block] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact Classical.epsilon_spec (p := fun y => y ∈ B.allSites ∧ x ∈ B.block y) ⟨y, hy, hxy⟩
theorem blockCenter_eq {y : D.Space} (hy : y ∈ B.allSites) {x : D.BareSite} (hx : x ∈ B.block y) :
    B.blockCenter x = y := by
  obtain ⟨h1, h2⟩ := blockCenter_spec B hb (block_subset_bareSites B hb hy hx)
  by_contra hne
  exact Set.disjoint_left.1 (hb.block_pairwise_disjoint _ h1 _ hy hne) h2 hx
theorem finsum_bareSites_eq_sum_blocks (g : D.BareSite → ℝ) :
    ∑ᶠ x ∈ D.bareSites (B.stage 0), g x = ∑ᶠ y : ↥B.allSites, ∑ᶠ x ∈ B.block y, g x := by
  have := D.bareSite_finite
  have := allSites_finite B
  rw [← hb.iUnion_block, finsum_mem_biUnion
    (fun y hy y' hy' hne => hb.block_pairwise_disjoint y hy y' hy' hne)
    (toFinite _) (fun _ _ => toFinite _)]
  exact (finsum_set_coe_eq_finsum_mem (f := fun y => ∑ᶠ x ∈ B.block y, g x) B.allSites).symm
theorem avgOpAdjoint_on_block (w : B.LayerFn) (y : ↥B.allSites) {x : D.BareSite}
    (hx : x ∈ B.block y) : (B.avgOpAdjoint w : D.BareSite → ℝ) x = w y := by
  have h0 := block_subset_bareSites B hb y.2 hx
  show (D.bareSites (B.stage 0)).indicator
    (fun x => B.layerEval w (B.blockCenter x)) x = w y
  rw [indicator_of_mem h0, blockCenter_eq B hb y.2 hx, layerEval_coe]
theorem layerInner_avgOp (f : ↥B.bareSpace) (w : B.LayerFn) :
    B.layerInner (B.avgOp f) w = B.bareInner f (B.avgOpAdjoint w) := by
  have := D.bareSite_finite
  have := allSites_finite B
  unfold SeparatedChain.layerInner SeparatedChain.bareInner
  rw [finsum_bareSites_eq_sum_blocks B hb, mul_finsum]
  refine finsum_congr fun y => ?_
  have hin : ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x *
      (B.avgOpAdjoint w : D.BareSite → ℝ) x =
      (∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x) * w y := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (toFinite _), Finset.sum_mul]
    exact Finset.sum_congr rfl fun x hx => by
      rw [avgOpAdjoint_on_block B hb w y ((Set.Finite.mem_toFinset _).1 hx)]
  rw [hin, avgOp_apply, ← siteScale_pow_four_mul_inv B y]
  ring
omit hb in
theorem finsum_const_block (y : D.Space) (c : ℝ) :
    ∑ᶠ _x ∈ B.block y, c = ((B.block y).ncard : ℝ) * c := by
  have := D.bareSite_finite
  rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite _), Finset.sum_const, nsmul_eq_mul,
    Set.ncard_eq_toFinset_card _ (toFinite _)]
include hc
theorem avgOp_avgOpAdjoint (w : B.LayerFn) :
    B.avgOp (B.avgOpAdjoint w) = w := by
  have := D.bareSite_finite
  funext y
  have hL : (D.L : ℝ) ^ (B.level y * 4) ≠ 0 := by
    have h3 := D.blocking.three_le_factor
    have hL : (D.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.L ≠ 0)
    exact pow_ne_zero _ hL
  rw [avgOp_apply, finsum_mem_congr rfl
    (fun x hx => avgOpAdjoint_on_block B hb w y hx), finsum_const_block B, hc y y.2]
  field_simp
theorem bareSpaceNorm_blockIndicator_sq (y : ↥B.allSites) :
    B.bareSpaceNorm (B.blockIndicator y) ^ 2 = B.siteScale y ^ 4 := by
  have := D.bareSite_finite
  have hprod : B.bareInner (B.blockIndicator y) (B.blockIndicator y) =
      B.siteScale y ^ 4 := by
    unfold SeparatedChain.bareInner
    rw [finsum_bareSites_eq_sum_blocks B hb, finsum_eq_single _ y ?_]
    · have h1 : ∑ᶠ x ∈ B.block y, B.blockIndicator y x * B.blockIndicator y x =
          ∑ᶠ _x ∈ B.block y, (1 : ℝ) := finsum_mem_congr rfl fun x hx => by
        simp [SeparatedChain.blockIndicator, hx]
      rw [h1, finsum_const_block B, hc y y.2, ← siteScale_pow_four_mul_inv B y]
      have hL : (D.L : ℝ) ^ (B.level y * 4) ≠ 0 := by
        have h3 := D.blocking.three_le_factor
        have hL : (D.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.L ≠ 0)
        exact pow_ne_zero _ hL
      field_simp
    · intro y' hne
      refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
      have hx' : x ∉ B.block y := fun h =>
        Set.disjoint_left.1 (hb.block_pairwise_disjoint _ y'.2 _ y.2
          (fun e => hne (Subtype.ext e))) hx h
      simp [SeparatedChain.blockIndicator, hx']
  have hnn : 0 ≤ B.bareInner (B.blockIndicator y) (B.blockIndicator y) := by
    rw [hprod]
    positivity
  rw [SeparatedChain.bareSpaceNorm, Real.sq_sqrt hnn, hprod]
end Blocks
section Relations
variable {D : TorusData} (B : SeparatedChain D)
  (hb : GivenChainGeneral.BlockPartition B)
  (hc : ∀ y ∈ B.allSites, ((B.block y).ncard : ℝ) = (D.L : ℝ) ^ (B.level y * 4))
theorem siteNorm_sq_eq (E : Set D.BareSite) (g : D.BareSite → ℝ) :
    TorusData.siteNorm E g ^ 2 = D.scale 0 ^ 4 * ∑ᶠ x ∈ E, g x ^ 2 := by
  unfold TorusData.siteNorm
  have h0 := chainScale_pos (D := D) 0
  exact Real.sq_sqrt (mul_nonneg (by positivity)
    (finsum_nonneg fun x => finsum_nonneg fun _ => sq_nonneg _))
theorem bareInner_comm (f g : D.BareSite → ℝ) : B.bareInner f g = B.bareInner g f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
include hb in
theorem weightedAvg_eq (f : ↥B.bareSpace) :
    B.weightedAvg f = B.avgOpAdjoint (fun y : ↥B.allSites =>
      avgWeight D.L (B.level y) * (B.siteScale y ^ 2)⁻¹ * B.avgOp f y) := by
  apply Subtype.ext
  funext x
  show (D.bareSites (B.stage 0)).indicator (fun x =>
      avgWeight D.L (B.bareLevel x) * (B.bareScale x ^ 2)⁻¹ *
        B.layerEval (B.avgOp f) (B.blockCenter x)) x =
    (D.bareSites (B.stage 0)).indicator (fun x => B.layerEval (fun y : ↥B.allSites =>
      avgWeight D.L (B.level y) * (B.siteScale y ^ 2)⁻¹ * B.avgOp f y)
        (B.blockCenter x)) x
  by_cases hx : x ∈ D.bareSites (B.stage 0)
  · obtain ⟨h1, -⟩ := blockCenter_spec B hb hx
    rw [indicator_of_mem hx, indicator_of_mem hx]
    have hv := layerEval_coe B (B.avgOp f) ⟨_, h1⟩
    have hw := layerEval_coe B (fun y : ↥B.allSites =>
      avgWeight D.L (B.level y) * (B.siteScale y ^ 2)⁻¹ * B.avgOp f y) ⟨_, h1⟩
    simp only at hv hw
    rw [hv, hw]
    rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]
include hb in
theorem bareInner_weightedAvg (f f' : ↥B.bareSpace) :
    B.bareInner f' (B.weightedAvg f) =
      ∑ᶠ y : ↥B.allSites, avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.avgOp f' y * B.avgOp f y) := by
  rw [weightedAvg_eq B hb, ← layerInner_avgOp B hb]
  unfold SeparatedChain.layerInner
  refine finsum_congr fun y => ?_
  have := (siteScale_pos B y).ne'
  field_simp
include hb in
theorem weightedAvg_symm (f g : ↥B.bareSpace) :
    B.bareInner (B.weightedAvg f) g = B.bareInner f (B.weightedAvg g) := by
  rw [bareInner_comm, bareInner_weightedAvg B hb, bareInner_weightedAvg B hb]
  exact finsum_congr fun y => by ring
include hb in
theorem avgOpAdjoint_basisVec (y : ↥B.allSites) :
    (B.avgOpAdjoint (B.basisVec y) : D.BareSite → ℝ) =
      B.siteScale y ^ (-2 : ℤ) • B.blockIndicator y := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hxb : x ∈ B.block y
  · rw [avgOpAdjoint_on_block B hb _ y hxb, basisVec_self, zpow_neg_two_eq]
    simp [SeparatedChain.blockIndicator, hxb]
  · have h0 : B.blockIndicator y x = 0 := by simp [SeparatedChain.blockIndicator, hxb]
    rw [h0, mul_zero]
    by_cases hx : x ∈ D.bareSites (B.stage 0)
    · obtain ⟨h1, h2⟩ := blockCenter_spec B hb hx
      have hne : (⟨_, h1⟩ : ↥B.allSites) ≠ y := fun e => hxb (by rw [← e]; exact h2)
      rw [avgOpAdjoint_on_block B hb _ ⟨_, h1⟩ h2]
      exact basisVec_of_ne B hne
    · exact (B.avgOpAdjoint _).2 x hx
include hb hc
omit hb in
theorem siteNorm_block_sq_split (f : ↥B.bareSpace) (y : ↥B.allSites) :
    TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2 =
      TorusData.siteNorm (B.block y) (fun x => (f : D.BareSite → ℝ) x - B.avgOp f y) ^ 2 +
        B.siteScale y ^ 4 * B.avgOp f y ^ 2 := by
  have := D.bareSite_finite
  have hL : (D.L : ℝ) ^ (B.level y * 4) ≠ 0 := by
    have h3 := D.blocking.three_le_factor
    have hL : (D.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.L ≠ 0)
    exact pow_ne_zero _ hL
  have hN := hc y y.2
  have hcard : ((toFinite (B.block y)).toFinset.card : ℝ) = ((B.block y).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (toFinite _)]
  have hmean : ∑ x ∈ (toFinite (B.block y)).toFinset, (f : D.BareSite → ℝ) x =
      ((B.block y).ncard : ℝ) * B.avgOp f y := by
    rw [avgOp_apply, hN, finsum_mem_eq_finite_toFinset_sum _ (toFinite _)]
    field_simp
  have hsplit : ∑ x ∈ (toFinite (B.block y)).toFinset,
      ((f : D.BareSite → ℝ) x - B.avgOp f y) ^ 2 =
      ∑ x ∈ (toFinite (B.block y)).toFinset, (f : D.BareSite → ℝ) x ^ 2 -
        2 * B.avgOp f y * (((B.block y).ncard : ℝ) * B.avgOp f y) +
        ((B.block y).ncard : ℝ) * B.avgOp f y ^ 2 := by
    have hx : ∀ x, ((f : D.BareSite → ℝ) x - B.avgOp f y) ^ 2 =
        (f : D.BareSite → ℝ) x ^ 2 - 2 * B.avgOp f y * (f : D.BareSite → ℝ) x +
          B.avgOp f y ^ 2 := fun x => by ring
    simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, hmean, hcard]
  have h4 : B.siteScale y ^ 4 = D.scale 0 ^ 4 * ((B.block y).ncard : ℝ) := by
    rw [hN, ← siteScale_pow_four_mul_inv B y]
    field_simp
  rw [siteNorm_sq_eq, siteNorm_sq_eq, finsum_mem_eq_finite_toFinset_sum _ (toFinite _),
    finsum_mem_eq_finite_toFinset_sum _ (toFinite _), hsplit, h4]
  ring
omit hb in
theorem abs_avgOp_le (f : ↥B.bareSpace) (y : ↥B.allSites) :
    |B.avgOp f y| ≤
      B.siteScale y ^ (-2 : ℤ) * TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) := by
  have hs := siteNorm_block_sq_split B hc f y
  have hT0 : 0 ≤ TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) := Real.sqrt_nonneg _
  have hξ := siteScale_pos B y
  have h1 : (B.siteScale y ^ 2 * |B.avgOp f y|) ^ 2 ≤
      TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) ^ 2 := by
    rw [mul_pow, sq_abs, hs]
    have h2 := sq_nonneg
      (TorusData.siteNorm (B.block y) (fun x => (f : D.BareSite → ℝ) x - B.avgOp f y))
    nlinarith
  have h2 : B.siteScale y ^ 2 * |B.avgOp f y| ≤
      TorusData.siteNorm (B.block y) (f : D.BareSite → ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) hT0 two_ne_zero).1 h1
  rw [zpow_neg_two_eq, inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
  exact h2
theorem avgRelations : B.AvgRelations :=
  ⟨layerInner_avgOp B hb, fun w x hx => by
      show (D.bareSites (B.stage 0)).indicator
        (fun x => B.layerEval w (B.blockCenter x)) x = _
      exact indicator_of_mem hx _,
    LinearMap.ext (avgOp_avgOpAdjoint B hb hc), bareSpaceNorm_blockIndicator_sq B hb hc,
    abs_avgOp_le B hc, siteNorm_block_sq_split B hc⟩
end Relations
section Conclusions
variable {D : TorusData} (B : SeparatedChain D)
theorem basisRelations (hb : GivenChainGeneral.BlockPartition B) :
    B.BasisRelations := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  refine ⟨fun y => ?_, fun y y' h => ?_, ?_, fun K y y' => ?_, avgOpAdjoint_basisVec B hb⟩
  · rw [layerInner_basisVec, basisVec_self]
    have := (siteScale_pos B y).ne'
    field_simp
  · rw [layerInner_basisVec, basisVec_of_ne B h, mul_zero]
  · rw [eq_top_iff]
    intro w _
    have hw := weightedCoords_eq_sum B fun y : ↥B.allSites => B.siteScale y ^ 2 * w y
    rw [weightedCoords_scaled] at hw
    rw [hw]
    exact Submodule.sum_mem _ fun y _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  · have he : B.basisVec y' =
        B.siteScale y' ^ (-2 : ℤ) • ({y'} : Set ↥B.allSites).indicator 1 := by
      funext b
      by_cases hby : b = y'
      · subst hby
        simp [SeparatedChain.basisVec]
      · simp [SeparatedChain.basisVec, hby]
    rw [matrixOf_apply, he, map_smul, Pi.smul_apply, smul_eq_mul]
    unfold SeparatedChain.kernel
    ring
theorem mulOpRelations : B.MulOpRelations := by
  intro m
  refine ⟨fun y y' h => ?_, ?_⟩
  · rw [matrixOf_apply]
    show B.siteScale y ^ 2 * (m y * B.basisVec y' y) = 0
    rw [basisVec_of_ne B h]
    simp
  · refine LinearMap.ext fun w => ?_
    funext y
    show m y * (B.siteScale y * w y) = B.siteScale y * (m y * w y)
    ring
variable (htri : ∀ x x' x'' : D.Space, B.weightedDistance x x'' ≤
  B.weightedDistance x x' + B.weightedDistance x' x'')
include htri
theorem opNormBounds : B.OpNormBounds := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  intro K K' δ hδ
  set ρ : ↥B.allSites → ↥B.allSites → ℝ := fun y y' => B.weightedDistance y y' with hρ
  refine ⟨?_, fun y y' => abs_entry_le ρ δ _ y y', l2OpNorm_matrixOf B K,
    l2OpNorm_le_expWeightedNorm_zero ρ _,
    expWeightedNorm_zero_le ρ (fun a b => weightedDistance_nonneg B a b) hδ _⟩
  show expWeightedNorm ρ δ (B.matrixOf (K ∘ₗ K')) ≤
    expWeightedNorm ρ δ (B.matrixOf K) * expWeightedNorm ρ δ (B.matrixOf K')
  rw [matrixOf_comp]
  exact expWeightedNorm_matProd_le ρ (fun a b c => htri a b c) hδ _ _
theorem matNormBounds : B.MatNormBounds := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  intro M M' δ hδ
  set ρ : ↥B.allSites → ↥B.allSites → ℝ := fun y y' => B.weightedDistance y y' with hρ
  exact ⟨expWeightedNorm_matProd_le ρ (fun a b c => htri a b c) hδ M M',
    fun y y' => abs_entry_le ρ δ M y y', l2OpNorm_le_expWeightedNorm_zero ρ M,
    expWeightedNorm_zero_le ρ (fun a b => weightedDistance_nonneg B a b) hδ M⟩
theorem subsetMatNormBounds : B.SubsetMatNormBounds := by
  have := allSites_finite B
  cases nonempty_fintype ↥B.allSites
  intro X M M' δ hδ
  set ρ : ↥B.allSites → ↥B.allSites → ℝ := fun y y' => B.weightedDistance y y' with hρ
  refine ⟨?_, fun y y' => ?_, l2OpNorm_le_zeroExtend ρ X M,
    expWeightedNorm_zero_le ρ (fun a b => weightedDistance_nonneg B a b) hδ _⟩
  · show expWeightedNorm ρ δ (zeroExtend X (matProd M M')) ≤
      expWeightedNorm ρ δ (zeroExtend X M) * expWeightedNorm ρ δ (zeroExtend X M')
    rw [zeroExtend_matProd]
    exact expWeightedNorm_matProd_le ρ (fun a b c => htri a b c) hδ _ _
  · have h := abs_entry_le ρ δ (zeroExtend X M) y y'
    rwa [zeroExtend_coe] at h
end Conclusions
theorem block_ncard (G : GivenChain)
    (hgrid : ∀ n, ∀ y ∈ G.chain.layerSites n, ∀ z : Fin 4 → ℝ,
      Torus.torusProj 4 G.data.side z = y →
        GivenChainGeneral.SiteBlockGrid G.chain n y z) :
    ∀ y ∈ G.chain.allSites, ((G.chain.block y).ncard : ℝ) =
      (G.data.L : ℝ) ^ (G.chain.level y * 4) := by
  intro y hy
  have hn : y ∈ G.chain.layerSites (G.chain.level y) := by
    simp only [SeparatedChain.allSites, mem_iUnion] at hy
    obtain ⟨n, _, hn⟩ := hy
    exact Nat.sInf_mem (s := {n | y ∈ G.chain.layerSites n}) ⟨n, hn⟩
  obtain ⟨k, hk⟩ := hn.1
  have g := (hgrid _ y hn _ hk.symm).isGrid
  calc ((G.chain.block y).ncard : ℝ)
      = ((Subtype.val '' G.chain.block y).ncard : ℝ) := by
        rw [ncard_image_of_injective _ Subtype.val_injective]
    _ = ((Torus.centredIntVectors 4
          ((G.data.L : ℝ) ^ G.chain.level y)).ncard : ℝ) := by
        rw [← g.image_eq, g.injOn.ncard_image]
    _ = ((G.data.L : ℝ) ^ G.chain.level y) ^ 4 := g.ncard_eq
    _ = (G.data.L : ℝ) ^ (G.chain.level y * 4) := by rw [pow_mul]
theorem avgAndMatrixFacts_of (h : GivenChainGeneralFacts) :
    AvgAndMatrixFacts := by
  intro G
  obtain ⟨-, -, -, hgrid, hb, htri⟩ := h G
  have hc := block_ncard G hgrid
  exact ⟨avgRelations G.chain hb hc,
    ⟨fun f f' => bareInner_weightedAvg G.chain hb f f', weightedAvg_symm G.chain hb⟩,
    basisRelations G.chain hb, opNormBounds G.chain htri,
    matNormBounds G.chain htri, subsetMatNormBounds G.chain htri,
    mulOpRelations G.chain⟩
end YangMills.Construction.Weighted.AvgMatrix
