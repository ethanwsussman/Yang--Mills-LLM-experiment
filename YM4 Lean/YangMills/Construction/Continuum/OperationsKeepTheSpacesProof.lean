import YangMills.Construction.Continuum.OperationsKeepTheSpaces
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace SchwartzOps
variable {n : ℕ}
def unitVec (a : Fin n × Fin 4) : Config n := Pi.single a.1 (Pi.single a.2 1)
def dirPartial (a : Fin n × Fin 4) (g : Config n → ℂ) : Config n → ℂ :=
  coordPartial a.1 a.2 g
theorem differentiable_of_contDiff_top {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ g :=
  hg.differentiable (by simp)
theorem dirPartial_eq_fderiv {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4)
    (x : Config n) :
    dirPartial a g x = fderiv ℝ g x (unitVec a) :=
  (differentiable_of_contDiff_top hg x).lineDeriv_eq_fderiv
theorem contDiff_dirPartial {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4) :
    ContDiff ℝ ∞ (dirPartial a g) := by
  have h : dirPartial a g = fun x => fderiv ℝ g x (unitVec a) :=
    funext (dirPartial_eq_fderiv hg a)
  rw [h]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem dirPartial_comm {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a b : Fin n × Fin 4) :
    dirPartial a (dirPartial b g) = dirPartial b (dirPartial a g) := by
  funext x
  rw [dirPartial_eq_fderiv (contDiff_dirPartial hg b), dirPartial_eq_fderiv (contDiff_dirPartial hg a)]
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have key : ∀ (c : Fin n × Fin 4) (d : Config n),
      fderiv ℝ (dirPartial c g) x d = fderiv ℝ (fderiv ℝ g) x d (unitVec c) := by
    intro c d
    have h : dirPartial c g = fun y => fderiv ℝ g y (unitVec c) :=
      funext (dirPartial_eq_fderiv hg c)
    rw [h, fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)) _ _
def listPartial (w : List (Fin n × Fin 4)) (g : Config n → ℂ) : Config n → ℂ :=
  w.foldl (fun h a => dirPartial a h) g
theorem listPartial_nil (g : Config n → ℂ) : listPartial [] g = g := rfl
theorem listPartial_cons (a : Fin n × Fin 4) (w : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    listPartial (a :: w) g = listPartial w (dirPartial a g) := rfl
theorem listPartial_perm {w w' : List (Fin n × Fin 4)} (h : w.Perm w') {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) : listPartial w g = listPartial w' g := by
  induction h generalizing g with
  | nil => rfl
  | cons a _ ih => exact ih (contDiff_dirPartial hg a)
  | swap a b l =>
    simp only [listPartial_cons]
    rw [dirPartial_comm hg]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hg).trans (ih₂ hg)
def indexList (α : MultiIndex n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem foldr_flatMap {A B C : Type*} (f : B → C → C) (l : List A) (t : A → List B) (c : C) :
    (l.flatMap t).foldr f c = l.foldr (fun a h => (t a).foldr f h) c := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.foldr_append, ih]
theorem foldr_replicate_iterate {B C : Type*} (f : B → C → C) (k : ℕ) (b : B) (c : C) :
    (List.replicate k b).foldr f c = (f b)^[k] c := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, Function.iterate_succ_apply', ih]
theorem iteratedPartial_eq_listPartial (α : MultiIndex n) (g : Config n → ℂ) :
    iteratedPartial α g = listPartial (indexList α).reverse g := by
  have h : (indexList α).foldr dirPartial g = iteratedPartial α g := by
    simp only [indexList, foldr_flatMap, foldr_replicate_iterate]
    rfl
  rw [← h, listPartial, List.foldl_reverse]
theorem sum_map_finRange {m : ℕ} (f : Fin m → ℕ) :
    ((List.finRange m).map f).sum = ∑ i, f i := (Fin.sum_univ_def f).symm
theorem length_indexList (α : MultiIndex n) : (indexList α).length = α.order := by
  simp only [indexList, List.length_flatMap, List.length_replicate, sum_map_finRange,
    MultiIndex.order]
theorem count_indexList (α : MultiIndex n) (a : Fin n × Fin 4) :
    (indexList α).count a = α a.1 a.2 := by
  obtain ⟨i, μ⟩ := a
  simp only [indexList, List.count_flatMap, Function.comp_def, sum_map_finRange,
    List.count_replicate]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [hν]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
theorem perm_indexList (w : List (Fin n × Fin 4)) :
    w.Perm (indexList fun i μ => w.count (i, μ)) :=
  List.perm_iff_count.2 fun a => by rw [count_indexList]
theorem exists_multiIndex_listPartial (w : List (Fin n × Fin 4)) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    ∃ γ : MultiIndex n, γ.order = w.length ∧ listPartial w g = iteratedPartial γ g := by
  refine ⟨fun i μ => w.count (i, μ), ?_, ?_⟩
  · rw [← length_indexList, (perm_indexList w).length_eq]
  · rw [iteratedPartial_eq_listPartial]
    exact listPartial_perm ((perm_indexList w).trans (List.reverse_perm _).symm) hg
theorem dirPartial_sum_smul {ι : Type*} [Fintype ι] (d : ι → ℝ) (h : ι → Config n → ℂ)
    (hh : ∀ b, ContDiff ℝ ∞ (h b)) (a : Fin n × Fin 4) :
    dirPartial a (fun x => ∑ b, d b • h b x) = fun x => ∑ b, d b • dirPartial a (h b) x := by
  have hs : ContDiff ℝ ∞ (fun x => ∑ b, d b • h b x) :=
    ContDiff.sum fun b _ => (hh b).const_smul (d b)
  funext x
  rw [dirPartial_eq_fderiv hs]
  have hf : HasFDerivAt (fun x => ∑ b, d b • h b x) (∑ b, d b • fderiv ℝ (h b) x) x :=
    HasFDerivAt.fun_sum fun b _ =>
      ((differentiable_of_contDiff_top (hh b) x).hasFDerivAt).const_smul (d b)
  rw [hf.fderiv]
  simp [dirPartial_eq_fderiv (hh _)]
theorem listPartial_sum_smul {ι : Type*} [Fintype ι] (d : ι → ℝ) (w : List (Fin n × Fin 4))
    (h : ι → Config n → ℂ) (hh : ∀ b, ContDiff ℝ ∞ (h b)) :
    listPartial w (fun x => ∑ b, d b • h b x) = fun x => ∑ b, d b • listPartial w (h b) x := by
  induction w generalizing h with
  | nil => rfl
  | cons a w ih =>
    rw [listPartial_cons, dirPartial_sum_smul d h hh a]
    exact ih _ fun b => contDiff_dirPartial (hh b) a
theorem sum_coord_smul_unitVec (y : Config n) :
    ∑ b : Fin n × Fin 4, y b.1 b.2 • unitVec b = y := by
  funext i μ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec]
  rw [Finset.sum_eq_single (i, μ)]
  · simp
  · rintro ⟨j, ν⟩ _ hb
    by_cases hj : j = i
    · subst hj
      have hν : ν ≠ μ := fun e => hb (by rw [e])
      simp [hν.symm]
    · simp [Ne.symm hj]
  · simp
def affineOf (L : Config n →L[ℝ] Config n) (c : Config n) : Config n → Config n := fun x => L x + c
variable (L : Config n →L[ℝ] Config n) (c : Config n)
theorem contDiff_affineOf : ContDiff ℝ ∞ (affineOf L c) :=
  L.contDiff.add contDiff_const
theorem dirPartial_comp_affineOf {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4) :
    dirPartial a (g ∘ affineOf L c) = fun x =>
      ∑ b : Fin n × Fin 4, (L (unitVec a)) b.1 b.2 • (dirPartial b g ∘ affineOf L c) x := by
  funext x
  have hA : HasFDerivAt (affineOf L c) L x := L.hasFDerivAt.add_const c
  have hc := ((differentiable_of_contDiff_top hg (affineOf L c x)).hasFDerivAt).comp x hA
  rw [dirPartial_eq_fderiv (hg.comp (contDiff_affineOf L c)), hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
  conv_lhs => rw [← sum_coord_smul_unitVec (L (unitVec a))]
  simp only [map_sum, map_smul, dirPartial_eq_fderiv hg]
theorem norm_listPartial_comp_le {K : ℝ}
    (hK : ∀ a : Fin n × Fin 4, ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2| ≤ K)
    (w : List (Fin n × Fin 4)) {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (x : Config n) (bd : ℝ)
    (h : ∀ v : List (Fin n × Fin 4), v.length = w.length → ‖listPartial v g (affineOf L c x)‖ ≤ bd) :
    ‖listPartial w (g ∘ affineOf L c) x‖ ≤ K ^ w.length * bd := by
  induction w generalizing g with
  | nil =>
    have h0 := h [] rfl
    simp only [listPartial_nil, List.length_nil, pow_zero, one_mul, Function.comp_apply] at h0 ⊢
    exact h0
  | cons a w ih =>
    have hb : 0 ≤ bd := (norm_nonneg _).trans (h (a :: w) rfl)
    have hK0 : 0 ≤ K := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hK a)
    have hsm : ∀ b : Fin n × Fin 4, ContDiff ℝ ∞ (dirPartial b g ∘ affineOf L c) :=
      fun b => (contDiff_dirPartial hg b).comp (contDiff_affineOf L c)
    rw [listPartial_cons, dirPartial_comp_affineOf L c hg a,
      listPartial_sum_smul (fun b : Fin n × Fin 4 => (L (unitVec a)) b.1 b.2) w
        (fun b => dirPartial b g ∘ affineOf L c) hsm]
    have hterm : ∀ b : Fin n × Fin 4,
        ‖listPartial w (dirPartial b g ∘ affineOf L c) x‖ ≤ K ^ w.length * bd := fun b =>
      ih (contDiff_dirPartial hg b) fun v hv => h (b :: v) (by simp [hv])
    calc ‖∑ b : Fin n × Fin 4, (L (unitVec a)) b.1 b.2 •
            listPartial w (dirPartial b g ∘ affineOf L c) x‖
        ≤ ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2| * (K ^ w.length * bd) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hterm b) (abs_nonneg _)
      _ = (∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2|) * (K ^ w.length * bd) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ K * (K ^ w.length * bd) :=
          mul_le_mul_of_nonneg_right (hK a) (mul_nonneg (pow_nonneg hK0 _) hb)
      _ = K ^ (a :: w).length * bd := by
          simp only [List.length_cons, pow_succ]
          ring
theorem schwartzSeminorm_comp_le {K C : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ a : Fin n × Fin 4, ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2| ≤ K)
    (hC : 0 < C)
    (hCx : ∀ x, 1 + euclidNorm x ^ 2 ≤ C * (1 + euclidNorm (affineOf L c x) ^ 2))
    {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (hW : schwartzSeminorm k g < ⊤) :
    schwartzSeminorm k (g ∘ affineOf L c) ≤
      ENNReal.ofReal (C ^ ((k : ℝ) / 2) * K ^ k) * schwartzSeminorm k g := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  set y := affineOf L c x with hy
  set Wr := (schwartzSeminorm k g).toReal with hWr
  have hWr0 : 0 ≤ Wr := ENNReal.toReal_nonneg
  have hbase : (0 : ℝ) < 1 + euclidNorm y ^ 2 := by positivity
  have hwt : 0 < (1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hbase _
  have hbound : ∀ v : List (Fin n × Fin 4), v.length = (indexList α).reverse.length →
      ‖listPartial v g y‖ ≤ Wr / (1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2) := by
    intro v hv
    obtain ⟨γ, hγ, e⟩ := exists_multiIndex_listPartial v hg
    have hsize : γ.order ≤ k := by
      rw [hγ, hv, List.length_reverse, length_indexList]
      exact hα
    have hle : ENNReal.ofReal ((1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2) *
        ‖iteratedPartial γ g y‖) ≤ schwartzSeminorm k g :=
      le_iSup_of_le y (le_iSup_of_le γ (le_iSup_of_le hsize le_rfl))
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hW.ne).1 hle
    rw [e, le_div_iff₀ hwt, mul_comm]
    exact hreal
  have hmain := norm_listPartial_comp_le L c hK (indexList α).reverse hg x _ hbound
  rw [← iteratedPartial_eq_listPartial, List.length_reverse, length_indexList] at hmain
  have hCp : 0 ≤ C ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hC _).le
  have hKp : K ^ α.order ≤ K ^ k := pow_le_pow_right₀ hK1 hα
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hfirst : (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) ≤
      C ^ ((k : ℝ) / 2) * (1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2) := by
    rw [← Real.mul_rpow hC.le hbase.le]
    exact Real.rpow_le_rpow (by positivity) (hCx x) (by positivity)
  have hreal : (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α (g ∘ affineOf L c) x‖ ≤
      C ^ ((k : ℝ) / 2) * K ^ k * Wr := by
    calc (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α (g ∘ affineOf L c) x‖
        ≤ (C ^ ((k : ℝ) / 2) * (1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2)) *
            (K ^ α.order * (Wr / (1 + euclidNorm y ^ 2) ^ ((k : ℝ) / 2))) :=
          mul_le_mul hfirst hmain (norm_nonneg _) (by positivity)
      _ = C ^ ((k : ℝ) / 2) * K ^ α.order * Wr := by
          field_simp
      _ ≤ C ^ ((k : ℝ) / 2) * K ^ k * Wr :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hCp) hWr0
  calc ENNReal.ofReal ((1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) *
        ‖iteratedPartial α (g ∘ affineOf L c) x‖)
      ≤ ENNReal.ofReal (C ^ ((k : ℝ) / 2) * K ^ k * Wr) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (C ^ ((k : ℝ) / 2) * K ^ k) * schwartzSeminorm k g := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCp (pow_nonneg hK0 _)), hWr,
          ENNReal.ofReal_toReal hW.ne]
def colBound : ℝ :=
  1 + ∑ a : Fin n × Fin 4, ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2|
theorem one_le_colBound : 1 ≤ colBound L :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
theorem sum_le_colBound (a : Fin n × Fin 4) :
    ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2| ≤ colBound L := by
  have h := Finset.single_le_sum
    (f := fun a : Fin n × Fin 4 => ∑ b : Fin n × Fin 4, |(L (unitVec a)) b.1 b.2|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  exact h.trans (le_add_of_nonneg_left zero_le_one)
theorem isSchwartz_comp_affineOf {C : ℝ} (hC : 0 < C)
    (hCx : ∀ x, 1 + euclidNorm x ^ 2 ≤ C * (1 + euclidNorm (affineOf L c x) ^ 2))
    {g : Config n → ℂ} (hg : IsSchwartz g) : IsSchwartz (g ∘ affineOf L c) :=
  ⟨hg.1.comp (contDiff_affineOf L c), fun k hk =>
    (schwartzSeminorm_comp_le L c (one_le_colBound L) (sum_le_colBound L) hC hCx hg.1 k
      (hg.2 k hk)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg.2 k hk))⟩
theorem flatAt_comp_affineOf {g : Config n → ℂ} {x : Config n} (h : FlatAt g (affineOf L c x)) :
    FlatAt (g ∘ affineOf L c) x := by
  refine ⟨h.1.comp (contDiff_affineOf L c), fun α => ?_⟩
  have hb := norm_listPartial_comp_le L c (sum_le_colBound L) (indexList α).reverse h.1 x 0
    fun v _ => by
      obtain ⟨γ, -, e⟩ := exists_multiIndex_listPartial v h.1
      rw [e, h.2 γ, norm_zero]
  rw [mul_zero] at hb
  rw [iteratedPartial_eq_listPartial]
  exact norm_le_zero_iff.1 hb
theorem flatOff_comp_affineOf {C : ℝ} (hC : 0 < C)
    (hCx : ∀ x, 1 + euclidNorm x ^ 2 ≤ C * (1 + euclidNorm (affineOf L c x) ^ 2))
    {V V' : Set (Config n)} (hV' : IsOpen V') (hVV : ∀ x, x ∉ V' → affineOf L c x ∉ V)
    {g : Config n → ℂ} (hg : IsSchwartz g ∧ FlatOff g V) :
    IsSchwartz (g ∘ affineOf L c) ∧ FlatOff (g ∘ affineOf L c) V' :=
  ⟨isSchwartz_comp_affineOf L c hC hCx hg.1, hg.1.1.comp (contDiff_affineOf L c), hV',
    fun x hx => flatAt_comp_affineOf L c (hg.2.2.2 _ (hVV x hx))⟩
def clmOfAdditive (f : Config n → Config n) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (t : ℝ) x, f (t • x) = t • f x) : Config n →L[ℝ] Config n :=
  LinearMap.toContinuousLinearMap { toFun := f, map_add' := hadd, map_smul' := hsmul }
theorem euclidNormVec_add_sq_le (a b : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (a + b) ^ 2 ≤
      2 * TorusMetric.euclidNormVec a ^ 2 + 2 * TorusMetric.euclidNormVec b ^ 2 := by
  unfold TorusMetric.euclidNormVec
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_four, Pi.add_apply]
  nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2),
    sq_nonneg (a 3 - b 3)]
theorem exists_affineOf_motion (r : EuclidMotion) :
    ∃ (L : Config n →L[ℝ] Config n) (c : Config n) (C : ℝ), 0 < C ∧
      (∀ x, affineOf L c x = fun i => r.invMap (x i)) ∧
      ∀ x, 1 + euclidNorm x ^ 2 ≤ C * (1 + euclidNorm (affineOf L c x) ^ 2) := by
  obtain ⟨R, hR, v, h⟩ := r.2
  let L : Config n →L[ℝ] Config n := clmOfAdditive (fun x i => R⁻¹.mulVec (x i))
    (fun x y => by funext i; simp [Matrix.mulVec_add])
    (fun t x => by funext i; simp [Matrix.mulVec_smul])
  have hinv : ∀ x, affineOf L (fun _ => -(R⁻¹.mulVec v)) x = fun i => r.invMap (x i) := by
    intro x
    funext i
    rw [r.invMap_eq hR h]
    show R⁻¹.mulVec (x i) + -(R⁻¹.mulVec v) = _
    rw [Matrix.mulVec_sub, sub_eq_add_neg]
  refine ⟨L, fun _ => -(R⁻¹.mulVec v), 2 + 2 * n * TorusMetric.euclidNormVec v ^ 2,
    by positivity, hinv, fun x => ?_⟩
  rw [hinv]
  have hx : ∀ i, x i = R.mulVec (r.invMap (x i)) + v := fun i => by
    rw [← h]
    exact (r.apply_invMap (x i)).symm
  have hs : euclidNorm x ^ 2 ≤ 2 * euclidNorm (fun i => r.invMap (x i)) ^ 2 +
      2 * n * TorusMetric.euclidNormVec v ^ 2 := by
    rw [euclidNorm_sq_eq_sum_sq, euclidNorm_sq_eq_sum_sq]
    calc ∑ i, TorusMetric.euclidNormVec (x i) ^ 2
        ≤ ∑ i, (2 * TorusMetric.euclidNormVec (r.invMap (x i)) ^ 2 +
            2 * TorusMetric.euclidNormVec v ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hadd := euclidNormVec_add_sq_le (R.mulVec (r.invMap (x i))) v
          rw [euclidNormVec_orth_mulVec hR, ← hx i] at hadd
          exact hadd
      _ = 2 * ∑ i, TorusMetric.euclidNormVec (r.invMap (x i)) ^ 2 +
            2 * n * TorusMetric.euclidNormVec v ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hy : 0 ≤ euclidNorm (fun i => r.invMap (x i)) ^ 2 := by positivity
  have hv : 0 ≤ 2 * (n : ℝ) * TorusMetric.euclidNormVec v ^ 2 := by positivity
  nlinarith [mul_nonneg hv hy]
theorem flatOff_motionAct (r : EuclidMotion) {V V' : Set (Config n)} (hV' : IsOpen V')
    (hVV : ∀ x, x ∉ V' → (fun i => r.invMap (x i)) ∉ V) {φ : Config n → ℂ}
    (hφ : IsSchwartz φ ∧ FlatOff φ V) :
    IsSchwartz (motionAct r φ) ∧ FlatOff (motionAct r φ) V' := by
  obtain ⟨L, c, C, hC, hinv, hCx⟩ := exists_affineOf_motion (n := n) r
  have e : motionAct r φ = φ ∘ affineOf L c := by
    funext x
    simp only [motionAct, Function.comp_apply, hinv x]
  rw [e]
  exact flatOff_comp_affineOf L c hC hCx hV' (fun x hx => by rw [hinv]; exact hVV x hx) hφ
theorem flatOff_permAct (ς : Equiv.Perm (Fin n)) {V V' : Set (Config n)} (hV' : IsOpen V')
    (hVV : ∀ x : Config n, x ∉ V' → (fun i => x (ς i)) ∉ V) {φ : Config n → ℂ}
    (hφ : IsSchwartz φ ∧ FlatOff φ V) :
    IsSchwartz (permAct ς φ) ∧ FlatOff (permAct ς φ) V' := by
  let L : Config n →L[ℝ] Config n :=
    clmOfAdditive (fun x i => x (ς i)) (fun _ _ => rfl) (fun _ _ => rfl)
  have hinv : ∀ x, affineOf L 0 x = fun i => x (ς i) := fun x => add_zero _
  have hnorm : ∀ x : Config n, euclidNorm (fun i => x (ς i)) = euclidNorm x := fun x => by
    unfold euclidNorm
    rw [Equiv.sum_comp ς fun i => ∑ μ, x i μ ^ 2]
  have e : permAct ς φ = φ ∘ affineOf L 0 := by
    funext x
    simp only [permAct, Function.comp_apply, hinv x]
  rw [e]
  exact flatOff_comp_affineOf L 0 one_pos (fun x => by rw [hinv, hnorm, one_mul])
    hV' (fun x hx => by rw [hinv]; exact hVV x hx) hφ
theorem unitVec_apply (a b : Fin n × Fin 4) :
    unitVec a b.1 b.2 = if b = a then 1 else 0 := by
  obtain ⟨i, μ⟩ := a
  obtain ⟨j, ν⟩ := b
  by_cases hj : j = i
  · subst hj
    by_cases hν : ν = μ
    · subst hν
      simp [unitVec]
    · simp [unitVec, hν]
  · simp [unitVec, hj]
def flipLinear : Config n →L[ℝ] Config n :=
  clmOfAdditive (fun x i => timeFlip (x i))
    (fun x y => by
      funext i μ
      fin_cases μ <;> simp [timeFlip]
      ring)
    (fun t x => by
      funext i μ
      fin_cases μ <;> simp [timeFlip])
theorem affineOf_flipLinear (x : Config n) :
    affineOf flipLinear 0 x = fun i => timeFlip (x i) := add_zero _
theorem euclidNorm_timeFlip (x : Config n) :
    euclidNorm (fun i => timeFlip (x i)) = euclidNorm x := by
  unfold euclidNorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Fin.sum_univ_four, timeFlip]
theorem flip_weight_le (x : Config n) :
    1 + euclidNorm x ^ 2 ≤ 1 * (1 + euclidNorm (affineOf flipLinear 0 x) ^ 2) := by
  rw [affineOf_flipLinear, euclidNorm_timeFlip, one_mul]
theorem sum_flipLinear_le_one (a : Fin n × Fin 4) :
    ∑ b : Fin n × Fin 4, |(flipLinear (unitVec a)) b.1 b.2| ≤ 1 := by
  have hcoord : ∀ b : Fin n × Fin 4, |(flipLinear (unitVec a)) b.1 b.2| =
      if b = a then 1 else 0 := by
    rintro ⟨j, ν⟩
    have h : |timeFlip (unitVec a j) ν| = |unitVec a j ν| := by
      fin_cases ν <;> simp [timeFlip]
    have h' := unitVec_apply a (j, ν)
    simp only at h'
    show |timeFlip (unitVec a j) ν| = _
    rw [h, h']
    split_ifs <;> simp
  simp [hcoord]
theorem dirPartial_conj {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4) :
    dirPartial a (fun x => conj (g x)) = fun x => conj (dirPartial a g x) := by
  have hs : ContDiff ℝ ∞ (fun x => conj (g x)) := Complex.conjCLE.contDiff.comp hg
  funext x
  have hf := (Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    (x := g x)).comp x (differentiable_of_contDiff_top hg x).hasFDerivAt
  have e : fderiv ℝ (fun x => conj (g x)) x =
      (Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap).comp (fderiv ℝ g x) :=
    hf.fderiv
  rw [dirPartial_eq_fderiv hs, e, dirPartial_eq_fderiv hg]
  rfl
theorem listPartial_conj (w : List (Fin n × Fin 4)) {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) :
    listPartial w (fun x => conj (g x)) = fun x => conj (listPartial w g x) := by
  induction w generalizing g with
  | nil => rfl
  | cons a w ih =>
    rw [listPartial_cons, dirPartial_conj hg a]
    exact ih (contDiff_dirPartial hg a)
theorem schwartzSeminorm_conj {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    schwartzSeminorm k (fun x => conj (g x)) = schwartzSeminorm k g := by
  have h : ∀ α : MultiIndex n, iteratedPartial α (fun x => conj (g x)) =
      fun x => conj (iteratedPartial α g x) := fun α => by
    simp only [iteratedPartial_eq_listPartial, listPartial_conj _ hg]
  simp only [schwartzSeminorm, h, RCLike.norm_conj]
theorem flipConj_eq_comp (φ : Config n → ℂ) :
    flipConj φ = fun x => conj ((φ ∘ affineOf flipLinear 0) x) := by
  funext x
  simp only [flipConj, Function.comp_apply, affineOf_flipLinear]
theorem isSchwartz_flipConj {φ : Config n → ℂ} (hφ : IsSchwartz φ) :
    IsSchwartz (flipConj φ) := by
  have h := isSchwartz_comp_affineOf flipLinear 0 one_pos flip_weight_le hφ
  rw [flipConj_eq_comp]
  refine ⟨Complex.conjCLE.contDiff.comp h.1, fun k hk => ?_⟩
  rw [schwartzSeminorm_conj h.1]
  exact h.2 k hk
theorem flipConj_flipConj (φ : Config n → ℂ) :
    flipConj (flipConj φ) = φ := by
  funext x
  simp [flipConj, timeFlip_timeFlip]
theorem schwartzSeminorm_flipConj_le {φ : Config n → ℂ} (hφ : IsSchwartz φ) (k : ℕ) :
    schwartzSeminorm k (flipConj φ) ≤ schwartzSeminorm k φ := by
  have h := isSchwartz_comp_affineOf flipLinear 0 one_pos flip_weight_le hφ
  rw [flipConj_eq_comp, schwartzSeminorm_conj h.1]
  have hle := schwartzSeminorm_comp_le flipLinear 0 le_rfl sum_flipLinear_le_one one_pos
    flip_weight_le hφ.1 k ((isSchwartz_iff_mem_schwartzSpace.1 hφ).2 k)
  simpa using hle
theorem schwartzSeminorm_flipConj {φ : Config n → ℂ} (hφ : IsSchwartz φ) (k : ℕ) :
    schwartzSeminorm k (flipConj φ) = schwartzSeminorm k φ := by
  refine le_antisymm (schwartzSeminorm_flipConj_le hφ k) ?_
  have h := schwartzSeminorm_flipConj_le (isSchwartz_flipConj hφ) k
  rwa [flipConj_flipConj] at h
theorem flatOff_flipConj {V V' : Set (Config n)} (hV' : IsOpen V')
    (hVV : ∀ x : Config n, x ∉ V' → (fun i => timeFlip (x i)) ∉ V) {φ : Config n → ℂ}
    (hφ : IsSchwartz φ ∧ FlatOff φ V) :
    IsSchwartz (flipConj φ) ∧ FlatOff (flipConj φ) V' := by
  have hS := isSchwartz_flipConj hφ.1
  refine ⟨hS, hS.1, hV', fun x hx => ?_⟩
  have hf : FlatAt (φ ∘ affineOf flipLinear 0) x :=
    flatAt_comp_affineOf _ _ (hφ.2.2.2 _ (by rw [affineOf_flipLinear]; exact hVV x hx))
  refine ⟨hS.1, fun α => ?_⟩
  have h0 := hf.2 α
  rw [iteratedPartial_eq_listPartial] at h0
  rw [iteratedPartial_eq_listPartial, flipConj_eq_comp, listPartial_conj _ hf.1]
  show conj (listPartial (indexList α).reverse (φ ∘ affineOf flipLinear 0) x) = 0
  rw [h0, map_zero]
theorem not_mem_distinctArgs_map (f : (Fin 4 → ℝ) → Fin 4 → ℝ) {x : Config n}
    (hx : x ∉ distinctArgs n) : (fun i => f (x i)) ∉ distinctArgs n :=
  fun h => hx fun _ _ e => h (congrArg f e)
theorem not_mem_distinctArgs_perm (ς : Equiv.Perm (Fin n)) {x : Config n}
    (hx : x ∉ distinctArgs n) : (fun i => x (ς i)) ∉ distinctArgs n :=
  fun h => hx ((Equiv.injective_comp ς x).1 h)
theorem argTime_shiftMotion_invMap {w : Fin 4 → ℝ} (hw : w ∈ zeroTimeHyperplane) (x : Config n)
    (i : Fin n) :
    argTime (fun i => (shiftMotion w).invMap (x i)) i = argTime x i := by
  have h : w 3 = 0 := hw
  simp only [argTime, lastCoord, shiftMotion_invMap, Pi.sub_apply, h, sub_zero]
theorem mem_injectiveTuples_of_map (f : (Fin 4 → ℝ) → Fin 4 → ℝ) {x : Config n}
    (h : (fun i => f (x i)) ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n) :
    x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n :=
  fun _ _ e => h (congrArg f e)
theorem argTime_timeFlip (x : Config n) (i : Fin n) :
    argTime (fun i => timeFlip (x i)) i = -argTime x i := by
  simp [argTime, lastCoord, timeFlip]
end SchwartzOps
open SchwartzOps in
theorem operationsPreserveSchwartzSpaces_of_suprema (hbridge : SchwartzSupremaStatement) :
    OperationsPreserveSchwartzSpaces := by
  intro n hn
  refine ⟨fun φ hφ r ς => ⟨?_, ?_⟩, fun w hw => ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩, fun φ => ?_, ?_,
    ?_⟩
  · exact flatOff_motionAct r isOpen_distinctArgs (fun x hx => not_mem_distinctArgs_map _ hx) hφ
  · exact flatOff_permAct ς isOpen_distinctArgs (fun x hx => not_mem_distinctArgs_perm ς hx) hφ
  · refine flatOff_motionAct (shiftMotion w) isOpen_posTimeSet (fun x hx h => hx ?_) hφ
    refine ⟨mem_injectiveTuples_of_map _ h.1, fun i => ?_⟩
    have := h.2 i
    rwa [argTime_shiftMotion_invMap hw] at this
  · refine flatOff_motionAct (shiftMotion w) isOpen_negTimeSet (fun x hx h => hx ?_) hφ
    refine ⟨mem_injectiveTuples_of_map _ h.1, fun i => ?_⟩
    have := h.2 i
    rwa [argTime_shiftMotion_invMap hw] at this
  · refine ⟨isSchwartz_flipConj φ.2, flipConj_flipConj φ.1, fun k => ?_⟩
    simp only [bracketNorm]
    rw [schwartzSeminorm_flipConj φ.2 k]
  · obtain ⟨-, -, -, -, -, S, hS, -⟩ := hbridge n hn
    have mem : ∀ φ : S, flipConj φ.1 ∈ S := fun φ => by
      have hφ : φ.1 ∈ (S : Set (Config n → ℂ)) := φ.2
      rw [hS] at hφ
      exact show flipConj φ.1 ∈ (S : Set (Config n → ℂ)) from by
        rw [hS]
        exact isSchwartz_flipConj hφ
    refine ⟨S, hS, fun φ => ⟨flipConj φ.1, mem φ⟩, fun φ => rfl, ?_⟩
    intro c c' x x'
    apply Subtype.ext
    funext y
    simp [flipConj]
  · have hneg : ∀ x : Config n, x ∉ negTimeSet n →
        (fun i => timeFlip (x i)) ∉ posTimeSet n := fun x hx h => hx
      ⟨mem_injectiveTuples_of_map _ h.1, fun i => by
        have := h.2 i
        rwa [argTime_timeFlip] at this⟩
    have hpos : ∀ x : Config n, x ∉ posTimeSet n →
        (fun i => timeFlip (x i)) ∉ negTimeSet n := fun x hx h => hx
      ⟨mem_injectiveTuples_of_map _ h.1, fun i => by
        have := h.2 i
        rw [argTime_timeFlip, neg_neg] at this
        exact this⟩
    ext ψ
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact flatOff_flipConj isOpen_negTimeSet hneg hφ
    · intro hψ
      exact ⟨flipConj ψ, flatOff_flipConj isOpen_posTimeSet hpos hψ,
        flipConj_flipConj ψ⟩
end YangMills.Construction.ConfigSpace
end
