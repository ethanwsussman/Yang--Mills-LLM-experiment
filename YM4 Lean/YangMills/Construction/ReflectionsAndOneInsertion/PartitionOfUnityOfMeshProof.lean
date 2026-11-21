import YangMills.Construction.LawInAState.PairOfTheLawIsNearAPointProof
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.ReflectionsAndOneInsertion.PartitionOfUnityOfMesh
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MeshPartition
open YangMills.Construction.CosineSquaredBump YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric Filter Topology Set
def cosSqFormula (s : ℝ) : ℝ := Real.cos (Real.pi / 2 * s) ^ 2
def cosSqBumpDeriv (s : ℝ) : ℝ :=
  if |s| ≤ 1 then -(Real.pi / 2) * Real.sin (Real.pi * s) else 0
theorem hasDerivAt_cosSqFormula (s : ℝ) :
    HasDerivAt cosSqFormula (-(Real.pi / 2) * Real.sin (Real.pi * s)) s := by
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi s := by
    simpa using (hasDerivAt_id s).const_mul Real.pi
  have hhalf : HasDerivAt (fun y : ℝ => 1 / 2 + Real.cos (Real.pi * y) / 2)
      (-Real.sin (Real.pi * s) * Real.pi / 2) s :=
    ((Real.hasDerivAt_cos (Real.pi * s)).comp s hlin).div_const 2 |>.const_add (1 / 2)
  have heq : cosSqFormula = fun y : ℝ => 1 / 2 + Real.cos (Real.pi * y) / 2 := by
    funext y
    have : 2 * (Real.pi / 2 * y) = Real.pi * y := by ring
    rw [cosSqFormula, Real.cos_sq, this]
  rw [heq]
  convert hhalf using 1
  ring
theorem cosSqFormula_one : cosSqFormula 1 = 0 := by simp [cosSqFormula]
theorem cosSqFormula_neg_one : cosSqFormula (-1) = 0 := by simp [cosSqFormula]
theorem cosSqBump_eq_of_abs_le {s : ℝ} (h : |s| ≤ 1) : cosSqBump s = cosSqFormula s := by
  simp [cosSqBump, cosSqFormula, h]
theorem cosSqBump_eq_zero_of_one_lt_abs {s : ℝ} (h : 1 < |s|) : cosSqBump s = 0 := by
  simp [cosSqBump, not_le.2 h]
theorem cosSqBump_eq_zero_of_one_le_abs {s : ℝ} (h : 1 ≤ |s|) : cosSqBump s = 0 := by
  rcases h.lt_or_eq with h | h
  · exact cosSqBump_eq_zero_of_one_lt_abs h
  · rw [cosSqBump_eq_of_abs_le h.ge]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h.symm with rfl | rfl
    · exact cosSqFormula_one
    · exact cosSqFormula_neg_one
theorem cosSqBump_ne_zero_iff (s : ℝ) : cosSqBump s ≠ 0 ↔ |s| < 1 := by
  constructor
  · intro h
    by_contra hs
    exact h (cosSqBump_eq_zero_of_one_le_abs (not_lt.1 hs))
  · intro h
    rw [cosSqBump_eq_of_abs_le h.le]
    have hs := abs_lt.1 h
    have hpi := Real.pi_pos
    have : 0 < Real.cos (Real.pi / 2 * s) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith
    exact pow_ne_zero 2 this.ne'
theorem cosSqBumpDeriv_one : cosSqBumpDeriv 1 = 0 := by simp [cosSqBumpDeriv]
theorem cosSqBumpDeriv_neg_one : cosSqBumpDeriv (-1) = 0 := by simp [cosSqBumpDeriv]
theorem hasDerivAt_cosSqBump_one : HasDerivAt cosSqBump 0 1 := by
  have hc : HasDerivAt cosSqFormula 0 1 := by
    simpa using hasDerivAt_cosSqFormula 1
  have hleft : HasDerivWithinAt cosSqBump 0 (Iic 1) 1 := by
    refine hc.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with t ht hu
      exact cosSqBump_eq_of_abs_le (abs_le.2 ⟨le_of_lt hu, ht⟩)
    · exact cosSqBump_eq_of_abs_le (by simp)
  have hright : HasDerivWithinAt cosSqBump 0 (Ici 1) 1 := by
    refine (hasDerivWithinAt_const (1 : ℝ) (Ici 1) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact cosSqBump_eq_zero_of_one_le_abs (le_trans ht (le_abs_self t))
    · exact cosSqBump_eq_zero_of_one_le_abs (by simp)
  have := hleft.union hright
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
theorem hasDerivAt_cosSqBump_neg_one : HasDerivAt cosSqBump 0 (-1) := by
  have hc : HasDerivAt cosSqFormula 0 (-1) := by
    simpa using hasDerivAt_cosSqFormula (-1)
  have hright : HasDerivWithinAt cosSqBump 0 (Ici (-1)) (-1) := by
    refine hc.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with t ht hu
      exact cosSqBump_eq_of_abs_le (abs_le.2 ⟨ht, le_of_lt hu⟩)
    · exact cosSqBump_eq_of_abs_le (by simp)
  have hleft : HasDerivWithinAt cosSqBump 0 (Iic (-1)) (-1) := by
    refine (hasDerivWithinAt_const (-1 : ℝ) (Iic (-1)) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine cosSqBump_eq_zero_of_one_le_abs ?_
      have : -t ≤ |t| := neg_le_abs t
      have ht' : t ≤ -1 := ht
      linarith
    · exact cosSqBump_eq_zero_of_one_le_abs (by simp)
  have := hleft.union hright
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
theorem hasDerivAt_cosSqBump (s : ℝ) : HasDerivAt cosSqBump (cosSqBumpDeriv s) s := by
  rcases lt_trichotomy |s| 1 with h | h | h
  · have hs : cosSqBumpDeriv s = -(Real.pi / 2) * Real.sin (Real.pi * s) := by
      simp [cosSqBumpDeriv, h.le]
    rw [hs]
    refine (hasDerivAt_cosSqFormula s).congr_of_eventuallyEq ?_
    have ho : IsOpen {t : ℝ | |t| < 1} := isOpen_lt continuous_abs continuous_const
    filter_upwards [ho.mem_nhds h] with t ht
    exact cosSqBump_eq_of_abs_le (le_of_lt ht)
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h with rfl | rfl
    · rw [cosSqBumpDeriv_one]
      exact hasDerivAt_cosSqBump_one
    · rw [cosSqBumpDeriv_neg_one]
      exact hasDerivAt_cosSqBump_neg_one
  · have hs : cosSqBumpDeriv s = 0 := by simp [cosSqBumpDeriv, not_le.2 h]
    rw [hs]
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    have ho : IsOpen {t : ℝ | 1 < |t|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [ho.mem_nhds h] with t ht
    exact cosSqBump_eq_zero_of_one_lt_abs ht
theorem continuous_cosSqBumpDeriv : Continuous cosSqBumpDeriv := by
  refine Continuous.if_le (by fun_prop) continuous_const continuous_abs continuous_const ?_
  intro s h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h with rfl | rfl <;> simp
theorem contDiff_cosSqBump : ContDiff ℝ 1 cosSqBump := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_cosSqBump s).differentiableAt, ?_⟩
  have : deriv cosSqBump = cosSqBumpDeriv := funext fun s => (hasDerivAt_cosSqBump s).deriv
  rw [this]
  exact continuous_cosSqBumpDeriv
theorem abs_cosSqBumpDeriv_le (s : ℝ) : |cosSqBumpDeriv s| ≤ Real.pi / 2 := by
  have hpi := Real.pi_pos
  unfold cosSqBumpDeriv
  split_ifs
  · rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < Real.pi / 2)]
    have := Real.abs_sin_le_one (Real.pi * s)
    nlinarith
  · simp only [abs_zero]
    positivity
theorem abs_cosSqBump_sub_le (s t : ℝ) :
    |cosSqBump s - cosSqBump t| ≤ Real.pi / 2 * |s - t| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := cosSqBump) (C := Real.pi / 2)
    (s := univ) (x := t) (y := s) (fun x _ => (hasDerivAt_cosSqBump x).differentiableAt)
    (fun x _ => by rw [(hasDerivAt_cosSqBump x).deriv]; exact abs_cosSqBumpDeriv_le x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using this
theorem abs_cosSqBump_le_one (s : ℝ) : |cosSqBump s| ≤ 1 := by
  have := cosSqBump_mem_Icc s
  rw [abs_of_nonneg this.1]
  exact this.2
theorem cosSqBump_floor_add (s : ℝ) :
    cosSqBump (s - ⌊s⌋) + cosSqBump (s - (⌊s⌋ + 1)) = 1 := by
  set u := s - ⌊s⌋ with hu
  have h0 : 0 ≤ u := Int.fract_nonneg s
  have h1 : u < 1 := Int.fract_lt_one s
  have e : s - ((⌊s⌋ : ℝ) + 1) = u - 1 := by rw [hu]; ring
  rw [e, cosSqBump_eq_of_abs_le (abs_le.2 ⟨by linarith, h1.le⟩),
    cosSqBump_eq_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)]
  have : Real.pi / 2 * (u - 1) = Real.pi / 2 * u - Real.pi / 2 := by ring
  rw [cosSqFormula, cosSqFormula, this, Real.cos_sub_pi_div_two]
  exact Real.cos_sq_add_sin_sq _ |>.symm ▸ by ring
theorem abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (hb : ∀ i, |b i| ≤ 1) : |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hQ : |∏ j ∈ s, b j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hb j)
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| ≤ ∑ j ∈ s, |a j - b j| :=
      (mul_le_of_le_one_left (abs_nonneg _) (ha i)).trans ih
    have h2 : |a i - b i| * |∏ j ∈ s, b j| ≤ |a i - b i| :=
      mul_le_of_le_one_right (abs_nonneg _) hQ
    linarith
theorem abs_productBump_sub_le {ε : ℝ} (hε : 0 < ε) (α x y : Fin 4 → ℝ) :
    |productBump ε α x - productBump ε α y| ≤ Real.pi / (2 * ε) * ∑ μ, |x μ - y μ| := by
  refine (abs_prod_sub_prod_le_sum Finset.univ _ _ (fun _ => abs_cosSqBump_le_one _)
    (fun _ => abs_cosSqBump_le_one _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => (abs_cosSqBump_sub_le _ _).trans (le_of_eq ?_)
  have e : (x μ - α μ) / ε - (y μ - α μ) / ε = (x μ - y μ) / ε := by ring
  rw [e, abs_div, abs_of_pos hε]
  field_simp
theorem sum_abs_le_two_mul_euclidNormVec (v : Fin 4 → ℝ) :
    ∑ μ, |v μ| ≤ 2 * euclidNormVec v := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem abs_productBump_sub_le_dist {ε : ℝ} (hε : 0 < ε) (α x y : Fin 4 → ℝ) :
    |productBump ε α x - productBump ε α y| ≤ Real.pi / ε * euclidDistR4 x y := by
  refine (abs_productBump_sub_le hε α x y).trans ?_
  have h := sum_abs_le_two_mul_euclidNormVec (x - y)
  simp only [Pi.sub_apply] at h
  have hc : 0 ≤ Real.pi / (2 * ε) := by have := Real.pi_pos; positivity
  calc Real.pi / (2 * ε) * ∑ μ, |x μ - y μ|
        ≤ Real.pi / (2 * ε) * (2 * euclidNormVec (x - y)) :=
        mul_le_mul_of_nonneg_left h hc
    _ = Real.pi / ε * euclidDistR4 x y := by
        unfold euclidDistR4
        field_simp
theorem contDiff_productBump (ε : ℝ) (α : Fin 4 → ℝ) : ContDiff ℝ 1 (productBump ε α) := by
  unfold productBump
  refine contDiff_prod fun μ _ => contDiff_cosSqBump.comp ?_
  exact ((contDiff_apply ℝ ℝ μ).sub contDiff_const).div_const ε
theorem norm_fderiv_productBump_le {ε : ℝ} (hε : 0 < ε) (α x : Fin 4 → ℝ) (μ : Fin 4) :
    ‖fderiv ℝ (productBump ε α) x (Pi.single μ 1)‖ ≤ Real.pi / (2 * ε) := by
  have hd : DifferentiableAt ℝ (productBump ε α) x :=
    ((contDiff_productBump ε α).differentiable (by norm_num)) x
  have hl : HasDerivAt (fun t : ℝ => productBump ε α (x + t • Pi.single μ (1 : ℝ)))
      (fderiv ℝ (productBump ε α) x (Pi.single μ 1)) 0 := hd.hasFDerivAt.hasLineDerivAt _
  refine hl.le_of_lip' (by have := Real.pi_pos; positivity) (Eventually.of_forall fun t => ?_)
  have h := abs_productBump_sub_le hε α (x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
    (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
  have hs : ∑ ν, |(x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) ν -
      (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) ν| = |t| := by
    simp [Pi.single_apply, abs_ite]
  rw [hs] at h
  simpa [Real.norm_eq_abs] using h
theorem gradNorm_productBump_le {ε : ℝ} (hε : 0 < ε) (α x : Fin 4 → ℝ) :
    YangMills.Construction.ReflectionsAndOneInsertion.gradNorm (productBump ε α) x ≤
      Real.pi / ε := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ μ : Fin 4, ‖fderiv ℝ (productBump ε α) x (Pi.single μ 1)‖ ^ 2
      ≤ ∑ _μ : Fin 4, (Real.pi / (2 * ε)) ^ 2 :=
        Finset.sum_le_sum fun μ _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_productBump_le hε α x μ) 2
    _ = (Real.pi / ε) ^ 2 := by
        simp
        field_simp
        norm_num
theorem productBump_nonneg (ε : ℝ) (α x : Fin 4 → ℝ) : 0 ≤ productBump ε α x :=
  Finset.prod_nonneg fun _ _ => (cosSqBump_mem_Icc _).1
theorem productBump_le_one (ε : ℝ) (α x : Fin 4 → ℝ) : productBump ε α x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => (cosSqBump_mem_Icc _).1) (fun _ _ => (cosSqBump_mem_Icc _).2)
theorem productBump_ne_zero_iff {ε : ℝ} (hε : 0 < ε) (α x : Fin 4 → ℝ) :
    productBump ε α x ≠ 0 ↔ ∀ μ, |x μ - α μ| < ε := by
  unfold productBump
  rw [Finset.prod_ne_zero_iff]
  refine forall_congr' fun μ => ?_
  simp only [Finset.mem_univ, true_implies]
  rw [cosSqBump_ne_zero_iff, abs_div, abs_of_pos hε, div_lt_one hε]
theorem cubeAround_eq_pi (ε : ℝ) (α : Fin 4 → ℝ) :
    cubeAround ε α = Set.pi univ fun μ => Icc (α μ - ε) (α μ + ε) := by
  ext x
  constructor
  · intro h μ _
    have h1 := (h μ).1
    have h2 := (h μ).2
    exact ⟨by linarith, by linarith⟩
  · intro h μ
    have h1 := (h μ (mem_univ μ)).1
    have h2 := (h μ (mem_univ μ)).2
    exact ⟨by linarith, by linarith⟩
theorem tsupport_productBump {ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) :
    tsupport (productBump ε α) = cubeAround ε α := by
  have hs : Function.support (productBump ε α) =
      Set.pi univ fun μ => Ioo (α μ - ε) (α μ + ε) := by
    ext x
    rw [Function.mem_support, productBump_ne_zero_iff hε]
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Ioo]
    refine forall_congr' fun μ => ?_
    rw [abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [tsupport, hs, closure_pi_set, cubeAround_eq_pi]
  refine Set.pi_congr rfl fun μ _ => closure_Ioo ?_
  exact (by linarith : α μ - ε < α μ + ε).ne
theorem isCompact_cubeAround (ε : ℝ) (α : Fin 4 → ℝ) : IsCompact (cubeAround ε α) := by
  rw [cubeAround_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc
theorem cubeAround_subset_closedBallR4 {ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) :
    cubeAround ε α ⊆ closedBallR4 α (2 * ε) := by
  intro y hy
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ μ, (y - α) μ ^ 2 ≤ ∑ _μ : Fin 4, ε ^ 2 := by
        refine Finset.sum_le_sum fun μ _ => ?_
        have h := hy μ
        exact sq_le_sq' h.1 h.2
    _ = (2 * ε) ^ 2 := by simp; ring
theorem bumpProperties {ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) : BumpProperties ε α := by
  refine ⟨⟨contDiff_productBump ε α, ?_⟩,
    fun x => ⟨productBump_nonneg ε α x, productBump_le_one ε α x⟩,
    tsupport_productBump hε α, cubeAround_subset_closedBallR4 hε α, gradNorm_productBump_le hε α⟩
  change IsCompact (tsupport (productBump ε α))
  rw [tsupport_productBump hε]
  exact isCompact_cubeAround ε α
def latticePoint (ε : ℝ) (n : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => ε * (n μ : ℝ)
theorem latticePoint_injective {ε : ℝ} (hε : 0 < ε) : Function.Injective (latticePoint ε) := by apply _root_.YangMills.DeltaSharedProofs.p4422 <;> assumption
def adjacentIndices (ε : ℝ) (x : Fin 4 → ℝ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun μ => {⌊x μ / ε⌋, ⌊x μ / ε⌋ + 1}
theorem productBump_latticePoint {ε : ℝ} (hε : 0 < ε) (n : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    productBump ε (latticePoint ε n) x = ∏ μ, cosSqBump (x μ / ε - n μ) := by
  refine Finset.prod_congr rfl fun μ _ => ?_
  congr 1
  simp only [latticePoint]
  field_simp
theorem mem_adjacentIndices {ε : ℝ} (hε : 0 < ε) {n : Fin 4 → ℤ} {x : Fin 4 → ℝ}
    (h : productBump ε (latticePoint ε n) x ≠ 0) : n ∈ adjacentIndices ε x := by
  rw [productBump_latticePoint hε, Finset.prod_ne_zero_iff] at h
  refine Fintype.mem_piFinset.2 fun μ => ?_
  have h1 := abs_lt.1 ((cosSqBump_ne_zero_iff _).1 (h μ (Finset.mem_univ μ)))
  set s := x μ / ε
  have hf := Int.floor_le s
  have hl := Int.lt_floor_add_one s
  have a1 : ((⌊s⌋ - 1 : ℤ) : ℝ) < n μ := by push_cast; linarith [h1.2]
  have a2 : (n μ : ℝ) < ((⌊s⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith [h1.1]
  have b1 : ⌊s⌋ - 1 < n μ := by exact_mod_cast a1
  have b2 : n μ < ⌊s⌋ + 2 := by exact_mod_cast a2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega
theorem sum_adjacentIndices {ε : ℝ} (hε : 0 < ε) (x : Fin 4 → ℝ) :
    ∑ n ∈ adjacentIndices ε x, productBump ε (latticePoint ε n) x = 1 := by
  simp only [productBump_latticePoint hε]
  rw [adjacentIndices, ← Finset.prod_univ_sum (f := fun μ (k : ℤ) => cosSqBump (x μ / ε - k))]
  refine Finset.prod_eq_one fun μ _ => ?_
  rw [Finset.sum_pair (by omega)]
  have := cosSqBump_floor_add (x μ / ε)
  push_cast
  exact this
theorem card_adjacentIndices (ε : ℝ) (x : Fin 4 → ℝ) : (adjacentIndices ε x).card = 16 := by
  rw [adjacentIndices, Fintype.card_piFinset]
  simp
def latticeIndex (ε : ℝ) (n : Fin 4 → ℤ) : latticeOfSpacing ε :=
  ⟨latticePoint ε n, n, fun _ => rfl⟩
theorem latticeIndex_bijective {ε : ℝ} (hε : 0 < ε) : Function.Bijective (latticeIndex ε) := by
  refine ⟨fun n k h => latticePoint_injective hε (congrArg Subtype.val h), ?_⟩
  rintro ⟨α, n, hn⟩
  exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
theorem finsum_productBump {ε : ℝ} (hε : 0 < ε) (x : Fin 4 → ℝ) :
    ∑ᶠ α : latticeOfSpacing ε, productBump ε α x = 1 := by
  rw [← finsum_comp (g := fun α : latticeOfSpacing ε => productBump ε α x) (latticeIndex ε)
    (latticeIndex_bijective hε)]
  rw [finsum_eq_sum_of_support_subset (s := adjacentIndices ε x)]
  · exact sum_adjacentIndices hε x
  · intro n hn
    exact mem_adjacentIndices hε hn
theorem sumsToOneAtPoint {ε : ℝ} (hε : 0 < ε) (x : Fin 4 → ℝ) : SumsToOneAtPoint ε x := by
  refine ⟨finsum_productBump hε x, ?_⟩
  have hs : {α | α ∈ latticeOfSpacing ε ∧ productBump ε α x ≠ 0} ⊆
      latticePoint ε '' (adjacentIndices ε x : Set (Fin 4 → ℤ)) := by
    rintro α ⟨⟨n, hn⟩, hα⟩
    have he : α = latticePoint ε n := funext hn
    subst he
    exact ⟨n, mem_adjacentIndices hε hα, rfl⟩
  calc {α | α ∈ latticeOfSpacing ε ∧ productBump ε α x ≠ 0}.encard
      ≤ (latticePoint ε '' (adjacentIndices ε x : Set (Fin 4 → ℤ))).encard :=
        encard_le_encard hs
    _ ≤ (adjacentIndices ε x : Set (Fin 4 → ℤ)).encard := encard_image_le _ _
    _ = 16 := by
        rw [encard_coe_eq_coe_finsetCard, card_adjacentIndices]
        rfl
section Decomposition
variable {f : (Fin 4 → ℝ) → ℝ}
theorem continuous_of_isLipschitzFor (hf : IsLipschitzFor euclidDistR4 f) : Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem isCompact_boxFrom (b lam : Fin 4 → ℝ) : IsCompact (boxFrom b lam) := by
  have : boxFrom b lam = Set.pi univ fun μ => Icc (b μ) (b μ + lam μ) := by
    ext x
    exact ⟨fun h μ _ => h μ, fun h μ => h μ (mem_univ μ)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_Icc
theorem bddAbove_range_norm {b lam : Fin 4 → ℝ} (hf : IsLipschitzFor euclidDistR4 f)
    (hs : tsupport f ⊆ boxFrom b lam) : BddAbove (range fun x => ‖f x‖) := by
  have hc : HasCompactSupport f := (isCompact_boxFrom b lam).of_isClosed_subset
    (isClosed_tsupport f) hs
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous (continuous_of_isLipschitzFor hf)
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
theorem uniformNorm_nonneg : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
theorem lipConstR4_nonneg (hf : IsLipschitzFor euclidDistR4 f) : 0 ≤ lipConstR4 f := by
  obtain ⟨C, hC⟩ := hf
  exact le_csInf ⟨C, hC⟩ fun _ h => h.1
theorem norm_sub_le_lipConstR4 (hf : IsLipschitzFor euclidDistR4 f) (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ lipConstR4 f * euclidDistR4 x y := by apply _root_.YangMills.DeltaSharedProofs.p501590 <;> assumption
theorem pieceProperties {ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) {b lam : Fin 4 → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) (hs : tsupport f ⊆ boxFrom b lam) :
    PieceProperties ε α f := by
  have hb := bddAbove_range_norm hf hs
  have hle : ∀ x, ‖f x‖ ≤ uniformNorm f := fun x => le_ciSup hb x
  have habs : ∀ x, |productBump ε α x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (productBump_nonneg ε α x)]
    exact productBump_le_one ε α x
  have hp : localizedPiece ε α f = productBump ε α * f := rfl
  have hK : 0 ≤ lipConstR4 f + Real.pi / ε * uniformNorm f :=
    add_nonneg (lipConstR4_nonneg hf) (mul_nonneg (by positivity) uniformNorm_nonneg)
  have hL : ∀ x y, ‖localizedPiece ε α f x - localizedPiece ε α f y‖ ≤
      (lipConstR4 f + Real.pi / ε * uniformNorm f) * euclidDistR4 x y := by
    intro x y
    have e : localizedPiece ε α f x - localizedPiece ε α f y =
        productBump ε α x * (f x - f y) + (productBump ε α x - productBump ε α y) * f y := by
      simp only [localizedPiece]
      ring
    rw [e, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hd : 0 ≤ euclidDistR4 x y := euclidNormVec_nonneg _
    have h1 : |productBump ε α x| * |f x - f y| ≤ lipConstR4 f * euclidDistR4 x y :=
      (mul_le_of_le_one_left (abs_nonneg _) (habs x)).trans (norm_sub_le_lipConstR4 hf x y)
    have h2 : |productBump ε α x - productBump ε α y| * |f y| ≤
        Real.pi / ε * euclidDistR4 x y * uniformNorm f :=
      mul_le_mul (abs_productBump_sub_le_dist hε α x y) (hle y) (abs_nonneg _)
        (mul_nonneg (by positivity) hd)
    nlinarith
  refine ⟨?_, ?_, ⟨_, hK, hL⟩, ?_, ?_⟩
  · refine subset_inter ?_ ?_
    · rw [hp]
      exact tsupport_mul_subset_right
    · rw [hp]
      refine tsupport_mul_subset_left.trans ?_
      rw [tsupport_productBump hε]
      exact cubeAround_subset_closedBallR4 hε α
  · refine ciSup_le fun x => ?_
    simp only [localizedPiece, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (habs x)).trans (hle x)
  · exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨hK, hL⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(contDiff_productBump ε α).mul h1, ?_⟩
    rw [hp]
    exact h2.mul_left
def sideRange (ε b l : ℝ) : Finset ℤ := Finset.Icc ⌈(b - ε) / ε⌉ ⌊(b + l + ε) / ε⌋
theorem card_sideRange_le {ε : ℝ} (hε : 0 < ε) (b : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    ((sideRange ε b l).card : ℝ) ≤ l / ε + 3 := by
  have hpos : 0 ≤ l / ε + 3 := by positivity
  rw [sideRange, Int.card_Icc]
  rcases le_total (⌊(b + l + ε) / ε⌋ + 1 - ⌈(b - ε) / ε⌉) 0 with h | h
  · rw [Int.toNat_of_nonpos h]
    simpa using hpos
  · have e : (((⌊(b + l + ε) / ε⌋ + 1 - ⌈(b - ε) / ε⌉).toNat : ℕ) : ℝ) =
        ((⌊(b + l + ε) / ε⌋ + 1 - ⌈(b - ε) / ε⌉ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h)
    rw [e]
    push_cast
    have h1 := Int.floor_le ((b + l + ε) / ε)
    have h2 := Int.le_ceil ((b - ε) / ε)
    have e2 : (b + l + ε) / ε - (b - ε) / ε = l / ε + 2 := by
      field_simp
      ring
    linarith
theorem mem_sideRange {ε : ℝ} (hε : 0 < ε) {b l : ℝ} {n : ℤ}
    (h1 : b - ε ≤ ε * n) (h2 : ε * n ≤ b + l + ε) : n ∈ sideRange ε b l := by
  refine Finset.mem_Icc.2 ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩
  · rw [div_le_iff₀ hε]
    linarith
  · rw [le_div_iff₀ hε]
    linarith
def boxRange (ε : ℝ) (b lam : Fin 4 → ℝ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun μ => sideRange ε (b μ) (lam μ)
theorem nonzeroPieces_subset {ε : ℝ} (hε : 0 < ε) {b lam : Fin 4 → ℝ}
    (hs : tsupport f ⊆ boxFrom b lam) :
    {α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0} ⊆
      latticePoint ε '' (boxRange ε b lam : Set (Fin 4 → ℤ)) := by
  rintro α ⟨⟨n, hn⟩, hα⟩
  have he : α = latticePoint ε n := funext hn
  subst he
  refine ⟨n, ?_, rfl⟩
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hα
  simp only [localizedPiece, Pi.zero_apply, mul_ne_zero_iff] at hx
  have hbox := hs (subset_tsupport f hx.2)
  have hχ := (productBump_ne_zero_iff hε _ _).1 hx.1
  refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun μ => ?_)
  have h1 := abs_lt.1 (hχ μ)
  have h2 := hbox μ
  simp only [latticePoint] at h1
  exact mem_sideRange hε (by linarith [h1.2, h2.1]) (by linarith [h1.1, h2.2])
theorem decomposesFunction {ε : ℝ} (hε : 0 < ε) {b lam : Fin 4 → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) (hl : ∀ μ, 0 ≤ lam μ)
    (hs : tsupport f ⊆ boxFrom b lam) : DecomposesFunction ε f lam := by
  have hsub := nonzeroPieces_subset hε hs
  have hfin : {α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.Finite :=
    ((boxRange ε b lam).finite_toSet.image _).subset hsub
  refine ⟨hfin, ?_, ?_, fun α _ => pieceProperties hε α hf hs⟩
  · have h1 : {α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.ncard ≤
        (boxRange ε b lam).card :=
      calc {α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.ncard
          ≤ (latticePoint ε '' (boxRange ε b lam : Set (Fin 4 → ℤ))).ncard :=
            ncard_le_ncard hsub ((boxRange ε b lam).finite_toSet.image _)
        _ ≤ (boxRange ε b lam : Set (Fin 4 → ℤ)).ncard :=
            ncard_image_le (boxRange ε b lam).finite_toSet
        _ = (boxRange ε b lam).card := ncard_coe_finset _
    calc (({α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.ncard : ℕ) : ℝ)
        ≤ ((boxRange ε b lam).card : ℝ) := by exact_mod_cast h1
      _ = ∏ μ, ((sideRange ε (b μ) (lam μ)).card : ℝ) := by
          rw [boxRange, Fintype.card_piFinset]
          push_cast
          rfl
      _ ≤ ∏ μ : Fin 4, (lam μ / ε + 3) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
            fun μ _ => card_sideRange_le hε (b μ) (hl μ)
  · have hT : {α : latticeOfSpacing ε | localizedPiece ε α f ≠ 0}.Finite :=
      (hfin.preimage Subtype.val_injective.injOn).subset fun α hα => ⟨α.2, hα⟩
    have hsum : ∑ᶠ α : latticeOfSpacing ε, localizedPiece ε α f =
        ∑ α ∈ hT.toFinset, localizedPiece ε α f :=
      finsum_eq_sum_of_support_subset _ fun α hα => Finset.mem_coe.2 (hT.mem_toFinset.2 hα)
    rw [hsum]
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · simp [localizedPiece, hx]
    · simp only [localizedPiece]
      rw [← Finset.sum_mul]
      have h2 : ∑ᶠ α : latticeOfSpacing ε, productBump ε α x =
          ∑ α ∈ hT.toFinset, productBump ε α x :=
        finsum_eq_sum_of_support_subset _ fun α hα =>
          Finset.mem_coe.2 (hT.mem_toFinset.2 fun h0 => mul_ne_zero hα hx (congrFun h0 x))
      rw [← h2, finsum_productBump hε x, one_mul]
end Decomposition
theorem meshPartitionStatement_holds : MeshPartitionStatement := fun _ε hε =>
  ⟨fun α _ => bumpProperties hε α, fun x => sumsToOneAtPoint hε x,
    fun _f _b _lam hf hl hs => decomposesFunction hε hf hl hs⟩
end YangMills.Construction.MeshPartition
