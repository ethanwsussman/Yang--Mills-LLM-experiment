import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfFunctionsWithContinuousPartialsProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.IsometriesLiftToOrthogonalMotions
import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfFunctionsWithContinuousPartials
import YangMills.Construction.TorusOrFourSpace.MapsOfFourKindsOnTuplesTestFunctionsAndDistributions
import YangMills.Construction.TorusOrFourSpace.ThreeKindsOfMapsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal Kronecker
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.ExtendedTupleMapProof
section Calculus
open Coords
variable {p : ℕ+}
def listPartials (l : List (Fin (4 * (p : ℕ)))) (G : Coords p → ℂ) : Coords p → ℂ :=
  l.foldr partialAlong G
def indexList (α : CoordIndex p) : List (Fin (4 * (p : ℕ))) :=
  (List.finRange _).flatMap fun j => List.replicate (α j) j
theorem iterPartial_eq_listPartials (α : CoordIndex p) (G : Coords p → ℂ) :
    iterPartial α G = listPartials (indexList α) G := by apply _root_.YangMills.Construction.PeriodicSpace.IteratedPartials.iterPartial_eq_partialWord <;> assumption
theorem length_indexList (α : CoordIndex p) :
    (indexList α).length = α.degree := by apply _root_.YangMills.Construction.PeriodicSpace.IteratedPartials.length_multiIndexToList <;> assumption
theorem iterPartial_single (k : Fin (4 * (p : ℕ))) (G : Coords p → ℂ) :
    iterPartial (Pi.single k 1 : CoordIndex p) G = partialAlong k G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_single <;> assumption
theorem iterPartial_zero (G : Coords p → ℂ) :
    iterPartial (0 : CoordIndex p) G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
theorem degree_add (α β : CoordIndex p) : (α + β).degree = α.degree + β.degree := by
  simp [CoordIndex.degree, Finset.sum_add_distrib]
theorem degree_single (k : Fin (4 * (p : ℕ))) :
    CoordIndex.degree (Pi.single k 1 : CoordIndex p) = 1 := by
  simp [CoordIndex.degree]
def multiplicities (l : List (Fin (4 * (p : ℕ)))) : CoordIndex p := fun j => l.count j
theorem multiplicities_cons (k : Fin (4 * (p : ℕ))) (l : List (Fin (4 * (p : ℕ)))) :
    multiplicities (k :: l) = multiplicities l + Pi.single k 1 := by
  funext j
  by_cases h : j = k
  · subst h
    simp [multiplicities]
  · have h' : k ≠ j := fun e => h e.symm
    simp [multiplicities, h, h']
theorem degree_multiplicities (l : List (Fin (4 * (p : ℕ)))) :
    (multiplicities l).degree = l.length := by
  induction l with
  | nil => simp [multiplicities, CoordIndex.degree]
  | cons k l ih => rw [multiplicities_cons, degree_add, degree_single, ih, List.length_cons]
theorem listPartials_eq_iterPartial
    (hIt : PartialDerivatives.IteratedPartialsCompose) {ν : ℕ}
    {G : Coords p → ℂ} (hG : ContPartialsUpTo ν G)
    (l : List (Fin (4 * (p : ℕ)))) (hl : l.length ≤ ν) :
    listPartials l G = iterPartial (multiplicities l) G := by
  induction l with
  | nil =>
    have : multiplicities ([] : List (Fin (4 * (p : ℕ)))) = 0 := by
      funext j
      simp [multiplicities]
    rw [this, iterPartial_zero]
    rfl
  | cons k l ih =>
    have hl' : l.length + 1 ≤ ν := by simpa using hl
    have h1 := ih (by omega)
    have hα : (multiplicities l).degree ≤ ν := by rw [degree_multiplicities]; omega
    have h2 := (hIt p ν G hG (multiplicities l) hα).2 (Pi.single k 1)
      (by rw [degree_single, degree_multiplicities]; omega)
    rw [multiplicities_cons, ← h2, iterPartial_single, ← h1]
    rfl
theorem listPartials_ofFn {G : Coords p → ℂ} {n : ℕ} (hG : ContDiff ℝ n G) :
    ∀ (κ : ℕ), κ ≤ n → ∀ r : Fin κ → Fin (4 * (p : ℕ)), listPartials (List.ofFn r) G =
      fun x => iteratedFDeriv ℝ κ G x fun i => Pi.single (r i) (1 : ℝ) := by
  intro κ
  induction κ with
  | zero =>
    intro _ r
    funext x
    simp [listPartials]
  | succ κ ih =>
    intro hκ r
    funext x
    have hr := ih (by omega) (fun i => r i.succ)
    rw [List.ofFn_succ]
    change partialAlong (r 0) (listPartials (List.ofFn fun i => r i.succ) G) x = _
    rw [hr]
    have hlt : ((κ : ℕ) : WithTop ℕ∞) < (n : WithTop ℕ∞) := by exact_mod_cast (by omega : κ < n)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ κ G) x :=
      (hG.differentiable_iteratedFDeriv hlt).differentiableAt
    set v : Fin κ → Coords p := fun i => Pi.single (r i.succ) (1 : ℝ) with hv
    have hf : HasFDerivAt (fun y => iteratedFDeriv ℝ κ G y v)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin κ => Coords p) ℂ v).comp
          (fderiv ℝ (iteratedFDeriv ℝ κ G) x)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin κ => Coords p) ℂ v).hasFDerivAt.comp x
        hd.hasFDerivAt
    have hl := (hf.hasLineDerivAt (Pi.single (r 0) (1 : ℝ))).lineDeriv
    rw [partialAlong, hl, iteratedFDeriv_succ_apply_left]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
    rfl
theorem norm_iterPartial_comp_affine_le
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose) {ν : ℕ}
    {G : Coords p → ℂ} (hG : ContPartialsUpTo ν G)
    (A : Matrix (Fin (4 * (p : ℕ))) (Fin (4 * (p : ℕ))) ℝ) (b : Coords p) {c B : ℝ}
    (hc : 1 ≤ c) (hcol : ∀ j, ∑ k, |A k j| ≤ c)
    (hB : ∀ β : CoordIndex p, β.degree ≤ ν → ∀ x, ‖iterPartial β G x‖ ≤ B)
    (α : CoordIndex p) (hα : α.degree ≤ ν) (x : Coords p) :
    ‖iterPartial α (fun x => G (A.mulVec x + b)) x‖ ≤ c ^ ν * B := by
  have cd : ContDiff ℝ ν G := (hCD p ν G).1 hG
  let Al : Coords p →L[ℝ] Coords p := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  have hAl : ∀ y, Al y = A.mulVec y := fun y => by simp [Al]
  have cdb : ContDiff ℝ ν (fun y => G (y + b)) := cd.comp (contDiff_id.add contDiff_const)
  have hcomp : (fun x => G (A.mulVec x + b)) = (fun y => G (y + b)) ∘ Al := by
    funext y
    simp [hAl]
  have cdH : ContDiff ℝ ν (fun x => G (A.mulVec x + b)) := by
    rw [hcomp]
    exact cdb.comp Al.contDiff
  have hB0 : 0 ≤ B :=
    (norm_nonneg _).trans (hB 0 (by simp [CoordIndex.degree]) 0)
  obtain ⟨κ, r, hofFn, hlen⟩ : ∃ (κ : ℕ) (r : Fin κ → Fin (4 * (p : ℕ))),
      List.ofFn r = indexList α ∧ κ ≤ ν :=
    ⟨_, (indexList α).get, List.ofFn_get _, by rw [length_indexList]; exact hα⟩
  have h1 : iterPartial α (fun x => G (A.mulVec x + b)) x =
      iteratedFDeriv ℝ κ (fun x => G (A.mulVec x + b)) x fun i => Pi.single (r i) (1 : ℝ) := by
    rw [iterPartial_eq_listPartials, ← hofFn, listPartials_ofFn cdH κ hlen r]
  set y := A.mulVec x + b with hy
  set m := iteratedFDeriv ℝ κ G y with hm
  have h2 : iteratedFDeriv ℝ κ (fun x => G (A.mulVec x + b)) x =
      m.compContinuousLinearMap fun _ => Al := by
    rw [hcomp, Al.iteratedFDeriv_comp_right cdb x (by exact_mod_cast hlen),
      iteratedFDeriv_comp_add_right]
    simp [hm, hy, hAl]
  have hcolumn : ∀ j, Al (Pi.single j (1 : ℝ)) = ∑ k, A k j • (Pi.single k (1 : ℝ) : Coords p) := by
    intro j
    funext i
    simp [hAl, Matrix.mulVec_single, Finset.sum_apply, Pi.single_apply]
  have h3 : m (fun i => Al (Pi.single (r i) (1 : ℝ))) =
      ∑ s : Fin κ → Fin (4 * (p : ℕ)), (∏ i, (A (s i) (r i) : ℝ)) •
        m fun i => Pi.single (s i) (1 : ℝ) := by
    simp only [hcolumn]
    rw [m.map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [m.map_smul_univ (fun i => A (s i) (r i)) fun i => Pi.single (s i) (1 : ℝ)]
  have h4 : ∀ s : Fin κ → Fin (4 * (p : ℕ)), ‖m fun i => Pi.single (s i) (1 : ℝ)‖ ≤ B := by
    intro s
    have hs := congrFun (listPartials_ofFn cd κ hlen s) y
    rw [listPartials_eq_iterPartial hIt hG (List.ofFn s) (by simpa using hlen)] at hs
    change _ = m _ at hs
    rw [← hs]
    exact hB _ (by rw [degree_multiplicities]; simpa using hlen) y
  have h5 : ∑ s : Fin κ → Fin (4 * (p : ℕ)), ∏ i, |A (s i) (r i)| = ∏ i, ∑ k, |A k (r i)| := by
    rw [Finset.prod_univ_sum (fun _ : Fin κ => Finset.univ) fun i k => |A k (r i)|,
      Fintype.piFinset_univ]
  have h6 : ∏ i, ∑ k, |A k (r i)| ≤ c ^ κ := by
    calc ∏ i, ∑ k, |A k (r i)| ≤ ∏ _i : Fin κ, c :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
            fun i _ => hcol (r i)
      _ = c ^ κ := by simp
  calc ‖iterPartial α (fun x => G (A.mulVec x + b)) x‖
      = ‖m fun i => Al (Pi.single (r i) (1 : ℝ))‖ := by rw [h1, h2]; rfl
    _ = ‖∑ s : Fin κ → Fin (4 * (p : ℕ)), (∏ i, (A (s i) (r i) : ℝ)) •
        m fun i => Pi.single (s i) (1 : ℝ)‖ := by rw [h3]
    _ ≤ ∑ s : Fin κ → Fin (4 * (p : ℕ)), ‖(∏ i, (A (s i) (r i) : ℝ)) •
        m fun i => Pi.single (s i) (1 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Fin κ → Fin (4 * (p : ℕ)), (∏ i, |A (s i) (r i)|) * B := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
        exact mul_le_mul_of_nonneg_left (h4 s) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = (∏ i, ∑ k, |A k (r i)|) * B := by rw [← Finset.sum_mul, h5]
    _ ≤ c ^ κ * B := mul_le_mul_of_nonneg_right h6 hB0
    _ ≤ c ^ ν * B := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hlen) hB0
end Calculus
section Matrices
variable {p : ℕ+}
theorem sum_abs_column_le_two {A : Matrix (Fin (4 * (p : ℕ))) (Fin (4 * (p : ℕ))) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin (4 * (p : ℕ))) ℝ)
    (h4 : ∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ 4) (j : Fin (4 * (p : ℕ))) :
    ∑ k, |A k j| ≤ 2 := by
  have h1 : ∑ k, A k j ^ 2 = 1 := by
    have := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff' _ _).1 hA) j) j
    simpa [Matrix.mul_apply, sq] using this
  have h2 : ∑ k, |A k j| = ∑ k ∈ Finset.univ.filter (fun i => A i j ≠ 0), |A k j| := by
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    intro h0
    exact hk (by simp [h0])
  have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter fun i => A i j ≠ 0)
    (f := fun k => |A k j|)
  have h5 : ∑ k ∈ Finset.univ.filter (fun i => A i j ≠ 0), |A k j| ^ 2 ≤ 1 := by
    calc ∑ k ∈ Finset.univ.filter (fun i => A i j ≠ 0), |A k j| ^ 2
        = ∑ k ∈ Finset.univ.filter (fun i => A i j ≠ 0), A k j ^ 2 := by simp only [sq_abs]
      _ ≤ ∑ k, A k j ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _
      _ = 1 := h1
  have hc : (((Finset.univ.filter fun i => A i j ≠ 0).card : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast h4 j
  have h6 : (∑ k ∈ Finset.univ.filter (fun i => A i j ≠ 0), |A k j|) ^ 2 ≤ 4 := by
    calc _ ≤ _ := h3
      _ ≤ 4 * 1 := mul_le_mul hc h5 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  rw [h2]
  nlinarith [Finset.sum_nonneg (s := Finset.univ.filter fun i => A i j ≠ 0)
    (f := fun k => |A k j|) fun _ _ => abs_nonneg _]
theorem sum_abs_column_le_one {A : Matrix (Fin (4 * (p : ℕ))) (Fin (4 * (p : ℕ))) ℝ}
    (h : ∀ j, ∃ i, (A i j = 1 ∨ A i j = -1) ∧ ∀ i', i' ≠ i → A i' j = 0)
    (j : Fin (4 * (p : ℕ))) : ∑ k, |A k j| ≤ 1 := by
  obtain ⟨i, hi, h0⟩ := h j
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [h0 k hk]) (by simp)]
  rcases hi with hi | hi <;> simp [hi]
def pairIndexEquiv (n : ℕ+) : Fin (n : ℕ) × Fin 4 ≃ Fin (4 * (n : ℕ)) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _))
theorem block_apply {n : ℕ+} (x : Coords n) (i : Fin (n : ℕ)) (μ : Fin 4) :
    x.block i μ = x (pairIndexEquiv n (i, μ)) := by
  unfold Coords.block
  congr 1
  apply Fin.ext
  simp [pairIndexEquiv, finProdFinEquiv]
  omega
def blockDiagonal (n : ℕ+) (S : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (4 * (n : ℕ))) (Fin (4 * (n : ℕ))) ℝ :=
  Matrix.reindex (pairIndexEquiv n) (pairIndexEquiv n)
    ((1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) ⊗ₖ S)
theorem blockDiagonal_apply (n : ℕ+) (S : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin (n : ℕ))
    (μ ν : Fin 4) :
    blockDiagonal n S (pairIndexEquiv n (i, μ)) (pairIndexEquiv n (j, ν)) =
      if i = j then S μ ν else 0 := by
  simp [blockDiagonal, Matrix.one_apply]
theorem blockDiagonal_mem_orthogonalGroup (n : ℕ+) {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    blockDiagonal n S ∈ Matrix.orthogonalGroup (Fin (4 * (n : ℕ))) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff] at hS ⊢
  simp only [blockDiagonal, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv]
  have : ((1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) ⊗ₖ S) *
      ((1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) ⊗ₖ S).transpose = 1 := by
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one, ← Matrix.mul_kronecker_mul, hS,
      Matrix.mul_one, Matrix.one_kronecker_one]
  rw [this, Matrix.submatrix_one_equiv]
theorem block_blockDiagonal_mulVec {n : ℕ+} (S : Matrix (Fin 4) (Fin 4) ℝ) (x : Coords n)
    (i : Fin (n : ℕ)) :
    Coords.block ((blockDiagonal n S).mulVec x) i = S.mulVec (x.block i) := by
  funext μ
  rw [block_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (pairIndexEquiv n), Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [blockDiagonal_apply, if_pos rfl, block_apply]
  · intro j _ hj
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [blockDiagonal_apply, if_neg (Ne.symm hj), zero_mul]
  · simp
def repeatedBlock (n : ℕ+) (v : Fin 4 → ℝ) : Coords n :=
  fun k => v ((pairIndexEquiv n).symm k).2
theorem block_repeatedBlock {n : ℕ+} (v : Fin 4 → ℝ) (i : Fin (n : ℕ)) :
    Coords.block (repeatedBlock n v) i = v := by
  funext μ
  rw [block_apply]
  simp [repeatedBlock]
theorem block_add {n : ℕ+} (x y : Coords n) (i : Fin (n : ℕ)) :
    Coords.block (x + y) i = x.block i + y.block i := rfl
theorem blockDiagonal_column_card_le (n : ℕ+) (S : Matrix (Fin 4) (Fin 4) ℝ)
    (l : Fin (4 * (n : ℕ))) :
    (Finset.univ.filter fun k => blockDiagonal n S k l ≠ 0).card ≤ 4 := by
  obtain ⟨⟨j, ν⟩, rfl⟩ := (pairIndexEquiv n).surjective l
  have hsub : (Finset.univ.filter fun k => blockDiagonal n S k (pairIndexEquiv n (j, ν)) ≠ 0) ⊆
      Finset.univ.image fun μ : Fin 4 => pairIndexEquiv n (j, μ) := by
    intro k hk
    obtain ⟨⟨i, μ⟩, rfl⟩ := (pairIndexEquiv n).surjective k
    have hk' := (Finset.mem_filter.1 hk).2
    rw [blockDiagonal_apply] at hk'
    have hij : i = j := by
      by_contra h
      exact hk' (if_neg h)
    subst hij
    exact Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp
theorem blockDiagonal_signed_column (n : ℕ+) {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : ∀ ν, ∃ μ, (S μ ν = 1 ∨ S μ ν = -1) ∧ ∀ μ', μ' ≠ μ → S μ' ν = 0)
    (l : Fin (4 * (n : ℕ))) :
    ∃ k, (blockDiagonal n S k l = 1 ∨ blockDiagonal n S k l = -1) ∧
      ∀ k', k' ≠ k → blockDiagonal n S k' l = 0 := by
  obtain ⟨⟨j, ν⟩, rfl⟩ := (pairIndexEquiv n).surjective l
  obtain ⟨μ, hμ, h0⟩ := hS ν
  refine ⟨pairIndexEquiv n (j, μ), ?_, fun k' hk' => ?_⟩
  · rw [blockDiagonal_apply, if_pos rfl]
    exact hμ
  · obtain ⟨⟨i, μ'⟩, rfl⟩ := (pairIndexEquiv n).surjective k'
    rw [blockDiagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact h0 μ' fun e => hk' (by rw [e])
    · rw [if_neg hij]
theorem int_orthogonal_column {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : ∀ μ ν, ∃ m : ℤ, S μ ν = m) (ν : Fin 4) :
    ∃ μ, (S μ ν = 1 ∨ S μ ν = -1) ∧ ∀ μ', μ' ≠ μ → S μ' ν = 0 := by
  have h1 : ∑ k, S k ν ^ 2 = 1 := by
    have := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff' _ _).1 hS) ν) ν
    simpa [Matrix.mul_apply, sq] using this
  choose m hm using fun μ => hZ μ ν
  have h2 : ∑ k, m k ^ 2 = 1 := by
    have : ((∑ k, m k ^ 2 : ℤ) : ℝ) = 1 := by
      push_cast
      simpa [hm] using h1
    exact_mod_cast this
  obtain ⟨μ, hμ⟩ : ∃ μ, m μ ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at h2
  have h3 : m μ ^ 2 + ∑ k ∈ Finset.univ.erase μ, m k ^ 2 = ∑ k, m k ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun k => m k ^ 2) (Finset.mem_univ μ)
  have h4 : 0 ≤ ∑ k ∈ Finset.univ.erase μ, m k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h5 : 1 ≤ m μ ^ 2 := by
    have : 0 < m μ ^ 2 := by positivity
    linarith
  have h6 : m μ ^ 2 = 1 := by linarith
  have h7 : ∑ k ∈ Finset.univ.erase μ, m k ^ 2 = 0 := by linarith
  refine ⟨μ, ?_, fun μ' hμ' => ?_⟩
  · rw [sq] at h6
    rcases mul_self_eq_one_iff.1 h6 with h | h
    · left
      rw [hm, h]
      simp
    · right
      rw [hm, h]
      simp
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h7 μ'
      (Finset.mem_erase.2 ⟨hμ', Finset.mem_univ _⟩)
    have h0 : m μ' = 0 := by simpa using this
    rw [hm, h0]
    simp
theorem exists_signed_matrix {σ : Equiv.Perm (Fin (4 * (p : ℕ)))}
    {ε : Fin (4 * (p : ℕ)) → ℤˣ} {A : Coords p →ₗ[ℝ] Coords p}
    (hA : ∀ j, A (Pi.single j 1) = (((ε j : ℤˣ) : ℤ) : ℝ) • Pi.single (σ j) (1 : ℝ)) :
    ∃ M ∈ Matrix.orthogonalGroup (Fin (4 * (p : ℕ))) ℝ,
      (∀ j, ∃ i, (M i j = 1 ∨ M i j = -1) ∧ ∀ i', i' ≠ i → M i' j = 0) ∧
        ∀ x, M.mulVec x = A x := by
  have hM : ∀ i j, LinearMap.toMatrix' A i j = if i = σ j then (((ε j : ℤˣ) : ℤ) : ℝ) else 0 := by
    intro i j
    rw [LinearMap.toMatrix'_apply, hA]
    simp [Pi.single_apply]
  refine ⟨LinearMap.toMatrix' A, ?_, fun j => ⟨σ j, ?_, fun i' hi' => ?_⟩,
    fun x => LinearMap.toMatrix'_mulVec A x⟩
  · rw [Matrix.mem_orthogonalGroup_iff']
    ext j j'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hM]
    by_cases h : j = j'
    · subst h
      have hs : (((ε j : ℤˣ) : ℤ) : ℝ) * (((ε j : ℤˣ) : ℤ) : ℝ) = 1 := by
        exact_mod_cast Int.units_coe_mul_self (ε j)
      simp [hs]
    · have h' : σ j ≠ σ j' := fun e => h (σ.injective e)
      simp [h, h'.symm, Matrix.one_apply]
  · rw [hM, if_pos rfl]
    rcases Int.units_eq_one_or (ε j) with h | h <;> simp [h]
  · rw [hM, if_neg hi']
end Matrices
section Distances
variable {X : Type*} {d : X → X → ℝ} {g h : X → X}
theorem isCompactWrt_preimage (hl : Function.LeftInverse h g) (hr : Function.RightInverse h g)
    (hg : ∀ x y, d (g x) (g y) = d x y) {K : Set X} (hK : MetricNotions.IsCompactWrt d K) :
    MetricNotions.IsCompactWrt d (g ⁻¹' K) := by
  intro U hU hcov
  have hopen : ∀ V ∈ (fun W : Set X => h ⁻¹' W) '' U, MetricNotions.IsOpenWrt d V := by
    rintro _ ⟨W, hW, rfl⟩ x hx
    obtain ⟨r, hr0, hball⟩ := hU W hW (h x) hx
    refine ⟨r, hr0, fun y hy => hball (h y) ?_⟩
    rw [← hg (h x) (h y), hr x, hr y]
    exact hy
  have hcov' : K ⊆ ⋃₀ ((fun W : Set X => h ⁻¹' W) '' U) := by
    intro x hx
    have hx' : h x ∈ g ⁻¹' K := by
      change g (h x) ∈ K
      rw [hr x]
      exact hx
    obtain ⟨W, hW, hxW⟩ := hcov hx'
    exact ⟨h ⁻¹' W, ⟨W, hW, rfl⟩, hxW⟩
  obtain ⟨U', hU', hfin, hsub⟩ := Set.exists_subset_image_finite_and.1 (hK _ hopen hcov')
  refine ⟨U', hU', hfin, fun x hx => ?_⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW⟩ := hsub hx
  refine ⟨W, hW, ?_⟩
  have : h (g x) ∈ W := hxW
  rwa [hl x] at this
theorem closureWrt_preimage (hr : Function.RightInverse h g) (hg : ∀ x y, d (g x) (g y) = d x y)
    (Z : Set X) : MetricNotions.closureWrt d (g ⁻¹' Z) = g ⁻¹' MetricNotions.closureWrt d Z := by
  ext x
  constructor
  · intro hx r hr0
    obtain ⟨y, hy, hxy⟩ := hx r hr0
    exact ⟨g y, hy, by rwa [hg]⟩
  · intro hx r hr0
    obtain ⟨z, hz, hxz⟩ := hx r hr0
    refine ⟨h z, ?_, ?_⟩
    · change g (h z) ∈ Z
      rwa [hr z]
    · rw [← hg x (h z), hr z]
      exact hxz
end Distances
section Points
variable {D : Params} {E : Kind}
theorem exists_isLift (hQ : QuotientCompactC1.Claim)
    (y : E.Pt D) : ∃ x, IsLift D E y x := by
  obtain ⟨x, hx, -⟩ := (hQ D E).1.2.2.2.2.2 (E.quotMap D 0) y 0 rfl
  exact ⟨x, hx⟩
theorem quotMap_pickLift (hQ : QuotientCompactC1.Claim)
    (y : E.Pt D) : E.quotMap D (pickLift D E y) = y :=
  Classical.epsilon_spec (exists_isLift hQ y)
theorem one_mem_motionMatrices (hIso : IsometryOrthogonalLiftTheorem) :
    (1 : Euclidean.RealMatrix4) ∈ motionMatrices E := by
  cases E with
  | euclidean =>
    change (1 : Euclidean.RealMatrix4) ∈ Euclidean.O4
    exact one_mem _
  | torus =>
    refine (hIso.1 1).2 ⟨one_mem _, fun μ ν => ?_⟩
    by_cases h : μ = ν
    · refine ⟨1, ?_⟩
      change (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν = _
      subst h
      simp
    · refine ⟨0, ?_⟩
      change (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν = _
      simp [h]
theorem quotMap_add (hIso : IsometryOrthogonalLiftTheorem)
    (x v : Fin 4 → ℝ) :
    E.quotMap D x + E.quotMap D v = E.quotMap D (x + v) := by
  obtain ⟨-, -, hMot, -, hTrans, -⟩ := hIso.2 D E
  have h1 := (hTrans (E.quotMap D v) v rfl).1
  have h2 := (hMot v 1 (one_mem_motionMatrices hIso)).2.1 x
  rw [h1] at h2
  simpa using h2
theorem quotMap_zero (hIso : IsometryOrthogonalLiftTheorem) :
    E.quotMap D 0 = 0 := by
  have h := quotMap_add (D := D) (E := E) hIso 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h.symm |>.symm ▸ rfl
theorem quotMap_neg (hIso : IsometryOrthogonalLiftTheorem) (v : Fin 4 → ℝ) :
    E.quotMap D (-v) = -E.quotMap D v := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [quotMap_add hIso, neg_add_cancel, quotMap_zero hIso]
theorem addPt_eq (hQ : QuotientCompactC1.Claim)
    (hIso : IsometryOrthogonalLiftTheorem) (y a : E.Pt D) :
    addPt D E y a = y + a := by
  rw [addPt, ← quotMap_add hIso, quotMap_pickLift hQ, quotMap_pickLift hQ]
theorem subPt_eq (hQ : QuotientCompactC1.Claim)
    (hIso : IsometryOrthogonalLiftTheorem) (y a : E.Pt D) :
    subPt D E y a = y - a := by
  rw [subPt, sub_eq_add_neg (pickLift D E y), ← quotMap_add hIso, quotMap_neg hIso,
    quotMap_pickLift hQ, quotMap_pickLift hQ, sub_eq_add_neg]
structure IsometryPair (s t : E.Pt D → E.Pt D) : Prop where
  isom : IsIsometry D E s
  isomInv : IsIsometry D E t
  leftInv : Function.LeftInverse t s
  rightInv : Function.RightInverse t s
theorem isometryInv_eq {s t : E.Pt D → E.Pt D} (hl : Function.LeftInverse t s)
    (hr : Function.RightInverse t s) : isometryInverse D E s = t := by
  funext y
  have hinj : Function.Injective s := hl.injective
  have h := Function.leftInverse_invFun hinj (t y)
  rw [hr y] at h
  exact h
theorem tupleDist_const_one (hQ : QuotientCompactC1.Claim)
    (a b : E.Pt D) :
    Tuple.tupleDist D E (p := 1) (fun _ => a) (fun _ => b) = quotDist D E a b := by
  change Real.sqrt (∑ _i : Fin 1, quotDist D E a b ^ 2) = _
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul]
  exact Real.sqrt_sq ((hQ D E).1.1 a b)
theorem frameAct_isometryPair (hQ : QuotientCompactC1.Claim)
    (hThree : TupleMapFacts.Claim) (w : PeriodicLattice.SignedFrame) :
    IsometryPair (frameAct D E w) (frameAct D E (frameInv w)) := by
  obtain ⟨-, -, ⟨-, hd, hl, hr, -⟩, -, -⟩ := hThree D E 1 (.frameDiag w)
  obtain ⟨-, -, ⟨-, hd', -, -, -⟩, -, -⟩ := hThree D E 1 (.frameDiag (frameInv w))
  refine ⟨fun y y' => ?_, fun y y' => ?_, fun y => ?_, fun y => ?_⟩
  · have h : Tuple.tupleDist D E (p := 1) (fun _ => frameAct D E w y)
        (fun _ => frameAct D E w y') = Tuple.tupleDist D E (p := 1) (fun _ => y)
          (fun _ => y') := hd _ _
    rwa [tupleDist_const_one hQ, tupleDist_const_one hQ] at h
  · have h : Tuple.tupleDist D E (p := 1) (fun _ => frameAct D E (frameInv w) y)
        (fun _ => frameAct D E (frameInv w) y') =
          Tuple.tupleDist D E (p := 1) (fun _ => y) (fun _ => y') := hd' _ _
    rwa [tupleDist_const_one hQ, tupleDist_const_one hQ] at h
  · have := congrFun (hl fun _ => y) ⟨0, by simp⟩
    exact this
  · have := congrFun (hr fun _ => y) ⟨0, by simp⟩
    exact this
theorem translate_isometryPair (hQ : QuotientCompactC1.Claim)
    (hIso : IsometryOrthogonalLiftTheorem) (a : E.Pt D) :
    IsometryPair (fun y : E.Pt D => y + a) (fun y => y - a) := by
  obtain ⟨-, -, -, -, hTrans, -⟩ := hIso.2 D E
  have h1 : ∀ b : E.Pt D, IsIsometry D E fun y => y + b :=
    fun b => (hTrans b _ (quotMap_pickLift hQ b)).2
  refine ⟨h1 a, ?_, fun y => by simp, fun y => by simp⟩
  simpa [sub_eq_add_neg] using h1 (-a)
theorem isometryPair_isometryInv (hIso : IsometryOrthogonalLiftTheorem)
    {s : E.Pt D → E.Pt D} (hs : IsIsometry D E s) :
    IsometryPair s (isometryInverse D E s) := by
  obtain ⟨-, hLift, -, -, -, hBij, hInv, -⟩ := hIso.2 D E
  obtain ⟨S, hS, v, hv, -⟩ := hLift s hs
  obtain ⟨-, hl, hr⟩ := hBij s hs
  exact ⟨hs, (hInv s hs S hS v hv).1, hl, hr⟩
theorem frameInv_frameInv (w : PeriodicLattice.SignedFrame) : frameInv (frameInv w) = w := by
  refine Prod.ext (by simp [frameInv]) ?_
  funext ν
  change w.2 (w.1.symm (w.1 ν)) = _
  simp
end Points
section Maps
variable {D : Params} {E : Kind} {n : ℕ+}
open ExtendedTupleMap
structure GoodAction (ψ φ : ExtendedTupleMap D E n) : Prop where
  leftInv : Function.LeftInverse φ.actPts ψ.actPts
  rightInv : Function.RightInverse φ.actPts ψ.actPts
  dist_eq : ∀ y y', Tuple.tupleDist D E (ψ.actPts y) (ψ.actPts y') =
    Tuple.tupleDist D E y y'
  supDist_eq : ∀ y y', Tuple.supDist D E (ψ.actPts y) (ψ.actPts y') =
    Tuple.supDist D E y y'
  distinct_iff : ∀ y, ψ.actPts y ∈ pairwiseDistinct D E n ↔ y ∈ pairwiseDistinct D E n
  tensorProd_eq : ∀ f : Fin (n : ℕ) → E.Pt D → ℂ, Tuple.tensorProd D E (ψ.actFns f) =
    Tuple.tensorProd D E f ∘ φ.actPts
  undo : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z), φ.actFns (ψ.actFns f) = f
  redo : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z), ψ.actFns (φ.actFns f) = f
  classes : ψ.PreservesTupleClasses
theorem goodAction_of_pointwise (hIso : IsometryOrthogonalLiftTheorem)
    {ψ φ : ExtendedTupleMap D E n} {s t : E.Pt D → E.Pt D} (h : IsometryPair s t)
    (hp : ψ.actPts = fun y i => s (y i)) (hq : φ.actPts = fun y i => t (y i))
    (hf : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z),
      ψ.actFns f = fun i y => f i (t y))
    (hg : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z),
      φ.actFns f = fun i y => f i (s y)) : GoodAction ψ φ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hClass, hSep⟩ := hIso.2 D E
  refine ⟨fun y => ?_, fun y => ?_, fun y y' => ?_, fun y y' => ?_, fun y => ?_, fun f => ?_,
    fun Z f => ?_, fun Z f => ?_, ?_⟩
  · rw [hp, hq]
    funext i
    exact h.leftInv _
  · rw [hp, hq]
    funext i
    exact h.rightInv _
  · rw [hp]
    simp only [Tuple.tupleDist, h.isom _ _]
  · rw [hp]
    simp only [Tuple.supDist]
    exact iSup_congr fun i => h.isom _ _
  · rw [hp]
    exact h.leftInv.injective.of_comp_iff y
  · rw [hf, hq]
    rfl
  · rw [hg, hf]
    funext i y
    change f i (t (s y)) = _
    rw [h.leftInv y]
  · rw [hf, hg]
    funext i y
    change f i (s (t y)) = _
    rw [h.rightInv y]
  · unfold PreservesTupleClasses
    refine ⟨fun f hf' => ?_, fun f hf' i => ?_⟩
    · rw [hf]
      exact hSep t h.isomInv n n.pos f hf'
    · rw [hf]
      exact (hClass t h.isomInv (f i)).2 (hf' i)
theorem goodAction_of_perm {ψ φ : ExtendedTupleMap D E n} (ς : Equiv.Perm (Fin (n : ℕ)))
    (hp : ψ.actPts = fun y i => y (ς.symm i)) (hq : φ.actPts = fun y i => y (ς i))
    (hf : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z),
      ψ.actFns f = fun i => f (ς.symm i))
    (hg : ∀ (Z : Type) (f : Fin (n : ℕ) → E.Pt D → Z),
      φ.actFns f = fun i => f (ς i)) : GoodAction ψ φ := by
  refine ⟨fun y => ?_, fun y => ?_, fun y y' => ?_, fun y y' => ?_, fun y => ?_, fun f => ?_,
    fun Z f => ?_, fun Z f => ?_, ?_⟩
  · rw [hp, hq]
    funext i
    simp
  · rw [hp, hq]
    funext i
    simp
  · rw [hp]
    simp only [Tuple.tupleDist]
    rw [Equiv.sum_comp ς.symm fun i => E.quotDist D (y i) (y' i) ^ 2]
  · rw [hp]
    simp only [Tuple.supDist]
    exact Equiv.iSup_comp (g := fun i => E.quotDist D (y i) (y' i)) ς.symm
  · rw [hp]
    exact Equiv.injective_comp ς.symm y
  · rw [hf, hq]
    funext y
    simp only [Tuple.tensorProd, Function.comp_apply]
    rw [← Equiv.prod_comp ς fun i => f (ς.symm i) (y i)]
    simp
  · rw [hg, hf]
    funext i
    simp
  · rw [hf, hg]
    funext i
    simp
  · unfold PreservesTupleClasses
    refine ⟨fun f hf' => ?_, fun f hf' i => ?_⟩
    · rw [hf]
      exact ⟨fun i => hf'.1 _, fun i => hf'.2.1 _,
        fun i k hik => hf'.2.2 _ _ (ς.symm.injective.ne hik)⟩
    · rw [hf]
      exact hf' _
theorem sameKindInv_spec {ψ : ExtendedTupleMap D E n} (h : ∃ φ, ψ.IsSameKindInverse φ) :
    ψ.IsSameKindInverse ψ.sameKindInv :=
  Classical.epsilon_spec h
theorem goodAction_sameKindInv (hQ : QuotientCompactC1.Claim)
    (hIso : IsometryOrthogonalLiftTheorem) (hThree : TupleMapFacts.Claim)
    (ψ : ExtendedTupleMap D E n) :
    ψ.IsSameKindInverse ψ.sameKindInv ∧ GoodAction ψ ψ.sameKindInv := by
  cases ψ with
  | ofTupleMap ψ₀ =>
    cases ψ₀ with
    | permute ς =>
      have h : (ofTupleMap (.permute ς) : ExtendedTupleMap D E n).IsSameKindInverse _ :=
        sameKindInv_spec ⟨_, rfl⟩
      refine ⟨h, ?_⟩
      have e : (ofTupleMap (.permute ς) : ExtendedTupleMap D E n).sameKindInv =
        ofTupleMap (.permute ς⁻¹) := h
      rw [e]
      exact goodAction_of_perm ς rfl rfl (fun _ _ => rfl) fun _ _ => rfl
    | frameDiag w =>
      have h : (ofTupleMap (.frameDiag w) : ExtendedTupleMap D E n).IsSameKindInverse _ :=
        sameKindInv_spec ⟨_, rfl⟩
      refine ⟨h, ?_⟩
      have e : (ofTupleMap (.frameDiag w) : ExtendedTupleMap D E n).sameKindInv =
        ofTupleMap (.frameDiag (frameInv w)) := h
      rw [e]
      refine goodAction_of_pointwise hIso (frameAct_isometryPair hQ hThree w) rfl rfl
        (fun _ _ => rfl) fun Z f => ?_
      funext i y
      change f i (frameAct D E (frameInv (frameInv w)) y) = _
      rw [frameInv_frameInv]
    | translate a =>
      have h : (ofTupleMap (.translate a) : ExtendedTupleMap D E n).IsSameKindInverse _ :=
        sameKindInv_spec ⟨_, rfl⟩
      refine ⟨h, ?_⟩
      have e : (ofTupleMap (.translate a) : ExtendedTupleMap D E n).sameKindInv =
        ofTupleMap (.translate (-a)) := h
      rw [e]
      refine goodAction_of_pointwise hIso (translate_isometryPair hQ hIso a) ?_ ?_
        (fun Z f => ?_) fun Z f => ?_
      · funext y i
        exact addPt_eq hQ hIso _ _
      · funext y i
        change addPt D E (y i) (-a) = _
        rw [addPt_eq hQ hIso, sub_eq_add_neg]
      · funext i y
        change f i (subPt D E y a) = _
        rw [subPt_eq hQ hIso]
      · funext i y
        change f i (subPt D E y (-a)) = _
        rw [subPt_eq hQ hIso, sub_neg_eq_add]
  | ofIsometry s hs =>
    have hp := isometryPair_isometryInv hIso hs
    have h : (ofIsometry s hs : ExtendedTupleMap D E n).IsSameKindInverse _ :=
      sameKindInv_spec ⟨_, hp.isomInv, rfl⟩
    refine ⟨h, ?_⟩
    obtain ⟨hs', e⟩ := h
    rw [e]
    have e' : isometryInverse D E (isometryInverse D E s) = s :=
      isometryInv_eq hp.rightInv hp.leftInv
    refine goodAction_of_pointwise hIso hp rfl rfl (fun _ _ => rfl) fun Z f => ?_
    change compEach f (isometryInverse D E (isometryInverse D E s)) = _
    rw [e']
    rfl
end Maps
section Composition
variable {D : Params} {E : Kind} {n : ℕ+}
open ExtendedTupleMap
theorem comp_affine_cNorm_le
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose)
    (hDist : TupleFacts.AllFacts)
    {Ψ : E.Tuple D n → E.Tuple D n}
    {A : Matrix (Fin (4 * (n : ℕ))) (Fin (4 * (n : ℕ))) ℝ} {b : Coords n}
    (hlift : ∀ x, Ψ (Tuple.proj D E x) =
      Tuple.proj D E (A.mulVec x + b))
    {c : ℝ} (hc : 1 ≤ c) (hcol : ∀ j, ∑ k, |A k j| ≤ c) (ν : ℕ)
    (F : E.Tuple D n → ℂ) (hF : Tuple.IsClassC D E ν F) :
    Tuple.IsClassC D E ν (F ∘ Ψ) ∧
      Tuple.cNorm D E ν (F ∘ Ψ) ≤
        ENNReal.ofReal (c ^ ν) * Tuple.cNorm D E ν F := by
  obtain ⟨hq, -, -, -, -, -, -, -, -, -, -, -, -, -, hder, -⟩ := hDist D E n
  have hcomp : (F ∘ Ψ) ∘ Tuple.proj D E =
      fun x => (F ∘ Tuple.proj D E) (A.mulVec x + b) := by
    funext x
    simp [hlift]
  have hclass : Tuple.IsClassC D E ν (F ∘ Ψ) := by
    unfold Tuple.IsClassC
    rw [hcomp]
    refine (hCD n ν _).2 (((hCD n ν _).1 hF).comp ?_)
    exact (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).contDiff.add contDiff_const
  refine ⟨hclass, ?_⟩
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hq.1 y
  have e1 := congrFun (hder ν _ hclass α hα).2.1 x
  rw [Function.comp_apply] at e1
  rw [e1, hcomp]
  by_cases hN : Tuple.cNorm D E ν F = ⊤
  · rw [hN, ENNReal.mul_top]
    · exact le_top
    · have : 0 < c ^ ν := by positivity
      simpa using this
  · have hB : ∀ β : CoordIndex n, β.degree ≤ ν → ∀ z,
        ‖Coords.iterPartial β (F ∘ Tuple.proj D E) z‖ ≤
          (Tuple.cNorm D E ν F).toReal := by
      intro β hβ z
      have e2 := congrFun (hder ν F hF β hβ).2.1 z
      rw [Function.comp_apply] at e2
      rw [← e2, ← ENNReal.ofReal_le_iff_le_toReal hN]
      unfold Tuple.cNorm
      exact le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le _ le_rfl))
    have hb := norm_iterPartial_comp_affine_le hCD hIt hF A b hc hcol hB α hα x
    calc ENNReal.ofReal ‖Coords.iterPartial α
            (fun x => (F ∘ Tuple.proj D E) (A.mulVec x + b)) x‖
        ≤ ENNReal.ofReal (c ^ ν * (Tuple.cNorm D E ν F).toReal) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (c ^ ν) * Tuple.cNorm D E ν F := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hN]
theorem signed_lift_of_tupleMap (hThree : TupleMapFacts.Claim) (ψ₀ : TupleMap D E n) :
    ∃ A ∈ Matrix.orthogonalGroup (Fin (4 * (n : ℕ))) ℝ,
      (∀ j, ∃ i, (A i j = 1 ∨ A i j = -1) ∧ ∀ i', i' ≠ i → A i' j = 0) ∧
      ∃ b, ∀ x : Coords n, ψ₀.actPts (Tuple.proj D E x) =
        Tuple.proj D E (A.mulVec x + b) := by
  obtain ⟨-, ⟨σ, ε, b, A, hA, hlift, -, -⟩, -⟩ := hThree D E n ψ₀
  obtain ⟨M, hM, hcol, hx⟩ := exists_signed_matrix hA
  exact ⟨M, hM, hcol, b, fun x => by rw [hx]; exact hlift x⟩
theorem ofIsometry_lift {s : E.Pt D → E.Pt D} (hs : IsIsometry D E s)
    {S : Euclidean.RealMatrix4} {v : Fin 4 → ℝ} (hl : LiftsVia D E s S v)
    (x : Coords n) :
    (ofIsometry s hs : ExtendedTupleMap D E n).actPts (Tuple.proj D E x) =
      Tuple.proj D E ((blockDiagonal n S).mulVec x + repeatedBlock n v) := by
  funext i
  change s (E.quotMap D (x.block i)) =
    E.quotMap D (Coords.block ((blockDiagonal n S).mulVec x + repeatedBlock n v) i)
  rw [hl, block_add, block_blockDiagonal_mulVec, block_repeatedBlock]
theorem hasOrthogonalLift_all (hIso : IsometryOrthogonalLiftTheorem)
    (hThree : TupleMapFacts.Claim) (ψ : ExtendedTupleMap D E n) : ψ.HasOrthogonalLift := by
  cases ψ with
  | ofTupleMap ψ₀ =>
    obtain ⟨A, hA, hcol, b, hb⟩ := signed_lift_of_tupleMap hThree ψ₀
    refine ⟨A, hA, fun j => ?_, b, hb⟩
    obtain ⟨i, -, h0⟩ := hcol j
    have hsub : (Finset.univ.filter fun k => A k j ≠ 0) ⊆ {i} := by
      intro k hk
      by_contra hki
      exact (Finset.mem_filter.1 hk).2 (h0 k (by simpa using hki))
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ 4 := by simp
  | ofIsometry s hs =>
    obtain ⟨-, hLift, -⟩ := hIso.2 D E
    obtain ⟨S, hS, v, hv, -⟩ := hLift s hs
    exact ⟨blockDiagonal n S, blockDiagonal_mem_orthogonalGroup n hS,
      blockDiagonal_column_card_le n S, repeatedBlock n v, ofIsometry_lift hs hv⟩
theorem hasSignedPermLift_of (hIso : IsometryOrthogonalLiftTheorem)
    (hThree : TupleMapFacts.Claim) (ψ : ExtendedTupleMap D E n)
    (h : ψ.IsTupleMapKind ∨ E = torus) : ψ.HasSignedPermLift := by
  rcases h with ⟨ψ₀, h0⟩ | rfl
  · obtain ⟨A, hA, hcol, b, hb⟩ := signed_lift_of_tupleMap hThree ψ₀
    exact ⟨A, hA, hcol, b, fun x => by rw [h0]; exact hb x⟩
  · cases ψ with
    | ofTupleMap ψ₀ =>
      obtain ⟨A, hA, hcol, b, hb⟩ := signed_lift_of_tupleMap hThree ψ₀
      exact ⟨A, hA, hcol, b, hb⟩
    | ofIsometry s hs =>
      obtain ⟨-, hLift, -⟩ := hIso.2 D torus
      obtain ⟨S, hS, v, hv, hW⟩ := hLift s hs
      obtain ⟨hO, hZ⟩ := (hIso.1 S).1 (hW rfl)
      exact ⟨blockDiagonal n S, blockDiagonal_mem_orthogonalGroup n hS,
        blockDiagonal_signed_column n (int_orthogonal_column hS hZ), repeatedBlock n v,
        ofIsometry_lift hs hv⟩
theorem supportT_comp {ψ φ : ExtendedTupleMap D E n} (W : GoodAction ψ φ)
    (F : E.Tuple D n → ℂ) :
    Tuple.supportT D E (F ∘ ψ.actPts) =
      ψ.actPts ⁻¹' Tuple.supportT D E F :=
  closureWrt_preimage W.rightInv W.dist_eq {y | F y ≠ 0}
theorem compNormLE_of
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose)
    (hDist : TupleFacts.AllFacts)
    (hIso : IsometryOrthogonalLiftTheorem)
    (hThree : TupleMapFacts.Claim) {ψ φ : ExtendedTupleMap D E n} (W : GoodAction ψ φ) :
    ψ.CompNormLE := by
  intro ν F hF
  obtain ⟨A, hA, h4, b, hb⟩ := hasOrthogonalLift_all hIso hThree ψ
  have h := comp_affine_cNorm_le hCD hIt hDist hb (c := 2) one_le_two
    (sum_abs_column_le_two hA h4) ν F hF
  refine ⟨h.1, ?_, supportT_comp W F⟩
  have e : ENNReal.ofReal ((2 : ℝ) ^ ν) = (2 : ℝ≥0∞) ^ ν := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [← e]
  exact h.2
theorem cNorm_comp_le_of_signed
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose)
    (hDist : TupleFacts.AllFacts)
    {ψ : ExtendedTupleMap D E n} (hs : ψ.HasSignedPermLift) (ν : ℕ)
    (F : E.Tuple D n → ℂ) (hF : Tuple.IsClassC D E ν F) :
    Tuple.IsClassC D E ν (F ∘ ψ.actPts) ∧
      Tuple.cNorm D E ν (F ∘ ψ.actPts) ≤ Tuple.cNorm D E ν F := by
  obtain ⟨A, -, hcol, b, hb⟩ := hs
  have h := comp_affine_cNorm_le hCD hIt hDist hb (c := 1) le_rfl
    (sum_abs_column_le_one hcol) ν F hF
  simpa using h
theorem compNormEq_of
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose)
    (hDist : TupleFacts.AllFacts)
    (hIso : IsometryOrthogonalLiftTheorem)
    (hThree : TupleMapFacts.Claim) {ψ φ : ExtendedTupleMap D E n} (W : GoodAction ψ φ)
    (h : ψ.IsTupleMapKind ∨ E = torus) : ψ.CompNormEq := by
  intro ν F hF
  refine ⟨?_, supportT_comp W F⟩
  rcases h with ⟨ψ₀, h0⟩ | hE
  · obtain ⟨-, -, -, ⟨-, hK, -⟩, -⟩ := hThree D E n ψ₀
    rw [h0]
    exact (hK ν F hF).2
  · have h1 := cNorm_comp_le_of_signed hCD hIt hDist
      (hasSignedPermLift_of hIso hThree ψ (Or.inr hE)) ν F hF
    have h2 := cNorm_comp_le_of_signed hCD hIt hDist
      (hasSignedPermLift_of hIso hThree φ (Or.inr hE)) ν _ h1.1
    have e : (F ∘ ψ.actPts) ∘ φ.actPts = F := by
      funext y
      exact congrArg F (W.rightInv y)
    rw [e] at h2
    exact le_antisymm h1.2 h2.2
end Composition
section TestFunctions
variable {D : Params} {E : Kind} {n : ℕ+}
open ExtendedTupleMap Tuple
theorem actsOnTestFnsAndDistribs_of {ψ φ : ExtendedTupleMap D E n} (W : GoodAction ψ φ)
    (hc : ψ.CompNormLE) : ψ.ActsOnTestFnsAndDistribs := by
  have hK : ∀ K, Tuple.IsCompactT D E K → K ⊆ pairwiseDistinct D E n →
      Tuple.IsCompactT D E (ψ.actPts ⁻¹' K) ∧ ψ.actPts ⁻¹' K ⊆ pairwiseDistinct D E n :=
    fun K hKc hKs => ⟨isCompactWrt_preimage W.leftInv W.rightInv W.dist_eq hKc,
      fun y hy => (W.distinct_iff y).1 (hKs hy)⟩
  have hmem : ∀ F : testFns D E (pairwiseDistinct D E n),
      F.1 ∘ ψ.actPts ∈ testFns D E (pairwiseDistinct D E n) := by
    rintro ⟨F, hsm, hcomp, hsub⟩
    refine ⟨fun ν => (hc ν F (hsm ν)).1, ?_, ?_⟩
    · change Tuple.IsCompactT D E (Tuple.supportT D E (F ∘ ψ.actPts))
      rw [supportT_comp W]
      exact (hK _ hcomp hsub).1
    · change Tuple.supportT D E (F ∘ ψ.actPts) ⊆ _
      rw [supportT_comp W]
      exact (hK _ hcomp hsub).2
  refine ⟨hmem, fun F G => rfl, fun c F => rfl, fun T => ?_⟩
  have hserve : ∀ K ν, HasOrderBoundOn T (ψ.actPts ⁻¹' K) ν →
      HasOrderBoundOn (fun F => T ⟨_, hmem F⟩) K ν := by
    rintro K ν ⟨C, hC⟩
    refine ⟨C * 2 ^ ν, fun F hF => ?_⟩
    have hsup : Tuple.supportT D E (F.1 ∘ ψ.actPts) ⊆ ψ.actPts ⁻¹' K := by
      rw [supportT_comp W]
      exact Set.preimage_mono hF
    calc ENNReal.ofReal ‖T ⟨_, hmem F⟩‖
        ≤ (C : ℝ≥0∞) * cNorm D E ν (F.1 ∘ ψ.actPts) := hC ⟨_, hmem F⟩ hsup
      _ ≤ (C : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ ν * cNorm D E ν F.1) := by
          gcongr
          exact (hc ν F.1 (F.2.1 ν)).2.1
      _ = ((C * 2 ^ ν : NNReal) : ℝ≥0∞) * cNorm D E ν F.1 := by
          push_cast
          ring
  have hlin : IsComplexLinearForm T → IsComplexLinearForm fun F => T ⟨_, hmem F⟩ := by
    rintro ⟨ha, hm⟩
    refine ⟨fun F G H hH => ha _ _ _ ?_, fun c F H hH => hm c _ _ ?_⟩
    · change H.1 ∘ ψ.actPts = _
      rw [hH]
      rfl
    · change H.1 ∘ ψ.actPts = _
      rw [hH]
      rfl
  refine ⟨fun hT => ⟨hlin hT.1, fun K hKc hKs => ?_⟩, fun ν₀ hT =>
    ⟨⟨hlin hT.1.1, fun K hKc hKs => ?_⟩, fun K hKc hKs => ?_⟩⟩
  · obtain ⟨ν, hν⟩ := hT.2 _ (hK K hKc hKs).1 (hK K hKc hKs).2
    exact ⟨ν, hserve K ν hν⟩
  · obtain ⟨ν, hν⟩ := hT.1.2 _ (hK K hKc hKs).1 (hK K hKc hKs).2
    exact ⟨ν, hserve K ν hν⟩
  · exact hserve K ν₀ (hT.2 _ (hK K hKc hKs).1 (hK K hKc hKs).2)
theorem invariantFunctional_of {ψ φ : ExtendedTupleMap D E n}
    (hr : ∀ f : Fin (n : ℕ) → E.Pt D → ℝ, ψ.actFns (φ.actFns f) = f)
    {Z : Type} {Φ : sepC1Tuples D E (n : ℕ) → Z} (hΦ : ψ.InvariantFunctional Φ) :
    φ.InvariantFunctional Φ := by
  intro f h
  have e := hr f.1
  have h' : ψ.actFns (φ.actFns f.1) ∈ sepC1Tuples D E (n : ℕ) := by
    rw [e]
    exact f.2
  rw [← hΦ ⟨_, h⟩ h']
  exact congrArg Φ (Subtype.ext e)
theorem invariantDistrib_of {ψ φ : ExtendedTupleMap D E n}
    (hl : Function.LeftInverse φ.actPts ψ.actPts)
    {T : testFns D E (pairwiseDistinct D E n) → ℂ} (hT : ψ.InvariantDistrib T) :
    φ.InvariantDistrib T := by
  intro F h
  have e : (F.1 ∘ φ.actPts) ∘ ψ.actPts = F.1 := by
    funext y
    exact congrArg F.1 (hl y)
  have h' : (F.1 ∘ φ.actPts) ∘ ψ.actPts ∈ testFns D E (pairwiseDistinct D E n) := by
    rw [e]
    exact F.2
  rw [← hT ⟨_, h⟩ h']
  exact congrArg T (Subtype.ext e)
end TestFunctions
open ExtendedTupleMap in
theorem mainProperties_holds (hIso : IsometryOrthogonalLiftTheorem)
    (hThree : TupleMapFacts.Claim)
    (hDist : TupleFacts.AllFacts)
    (hCD : ContPartialsIffContDiff)
    (hIt : PartialDerivatives.IteratedPartialsCompose)
    (hQ : QuotientCompactC1.Claim) : ExtendedTupleMapFacts.MainProperties := by
  intro D E n _
  refine ⟨⟨fun w => ?_, fun a => ?_⟩, fun ψ => ?_⟩
  · have hp := frameAct_isometryPair (D := D) (E := E) hQ hThree w
    refine ⟨hp.isom, rfl, fun Z f => ?_⟩
    change _ = compEach f (isometryInverse D E (frameAct D E w))
    rw [isometryInv_eq hp.leftInv hp.rightInv]
    rfl
  · have e1 : (fun y => addPt D E y a) = fun y => y + a :=
      funext fun y => addPt_eq hQ hIso y a
    have e2 : (fun y => subPt D E y a) = fun y => y - a :=
      funext fun y => subPt_eq hQ hIso y a
    have hp : IsometryPair (fun y => addPt D E y a)
        (fun y => subPt D E y a) := by
      rw [e1, e2]
      exact translate_isometryPair hQ hIso a
    refine ⟨hp.isom, rfl, fun Z f => ?_⟩
    change _ = compEach f (isometryInverse D E fun y => addPt D E y a)
    rw [isometryInv_eq hp.leftInv hp.rightInv]
    rfl
  · obtain ⟨hk, W⟩ := goodAction_sameKindInv hQ hIso hThree ψ
    have hc := compNormLE_of hCD hIt hDist hIso hThree W
    refine ⟨⟨Function.bijective_iff_has_inverse.2 ⟨_, W.leftInv, W.rightInv⟩, W.supDist_eq⟩,
      ⟨hk, W.leftInv, W.rightInv⟩, ?_, ⟨W.tensorProd_eq, W.undo⟩, hasOrthogonalLift_all hIso hThree ψ,
      hasSignedPermLift_of hIso hThree ψ, hc,
      compNormEq_of hCD hIt hDist hIso hThree W, W.classes,
      actsOnTestFnsAndDistribs_of W hc,
      fun Z Φ => ⟨invariantFunctional_of (W.redo ℝ), invariantFunctional_of (W.undo ℝ)⟩,
      fun T _ => ⟨invariantDistrib_of W.leftInv, invariantDistrib_of W.rightInv⟩⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (W.distinct_iff x).2 hx
    · intro hy
      refine ⟨ψ.sameKindInv.actPts y, (W.distinct_iff _).1 ?_, W.rightInv y⟩
      rw [W.rightInv y]
      exact hy
end YangMills.Construction.PeriodicSpace.Kind.ExtendedTupleMapProof
