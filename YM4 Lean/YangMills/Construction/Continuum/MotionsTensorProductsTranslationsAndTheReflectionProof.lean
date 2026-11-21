import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpacesProof
import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import YangMills.Construction.Continuum.OperationsOnTestFunctionsProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff ComplexConjugate
noncomputable section
namespace YangMills.Construction.MotionsTranslations
open TestSpaces Motions WightmanReconstruction HyperplaneReflection UpperHalfTensors
variable {n : ℕ}
def iterDerivAlong (l : List (CoordIdx n)) (g : PointTuple n → ℂ) : PointTuple n → ℂ :=
  l.foldr (fun c h => coordDeriv c.1 c.2 h) g
theorem coordDeriv_eq_fderiv {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (i : Fin n) (μ : Fin 4)
    (x : PointTuple n) :
    coordDeriv i μ g x = fderiv ℝ g x (Pi.single i (Pi.single μ 1)) :=
  ((hg.differentiable (by simp)) x).lineDeriv_eq_fderiv
theorem contDiff_coordDeriv {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (i : Fin n) (μ : Fin 4) :
    ContDiff ℝ ∞ (coordDeriv i μ g) := by
  have h : coordDeriv i μ g = fun x => fderiv ℝ g x (Pi.single i (Pi.single μ 1)) :=
    funext fun x => coordDeriv_eq_fderiv hg i μ x
  rw [h]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem coordDeriv_comm {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (c d : CoordIdx n)
    (x : PointTuple n) :
    coordDeriv c.1 c.2 (coordDeriv d.1 d.2 g) x =
      coordDeriv d.1 d.2 (coordDeriv c.1 c.2 g) x := by
  have h : ∀ b : CoordIdx n, coordDeriv b.1 b.2 g =
      fun y => fderiv ℝ g y (Pi.single b.1 (Pi.single b.2 1)) :=
    fun b => funext fun y => coordDeriv_eq_fderiv hg b.1 b.2 y
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have key : ∀ v : PointTuple n, ∀ b : CoordIdx n,
      coordDeriv b.1 b.2 (fun y => fderiv ℝ g y v) x =
        fderiv ℝ (fderiv ℝ g) x (Pi.single b.1 (Pi.single b.2 1)) v := by
    intro v b
    have := (HasFDerivAt.hasLineDerivAt
      ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt)
      (Pi.single b.1 (Pi.single b.2 1) : PointTuple n)).lineDeriv
    simpa [Function.comp_def, coordDeriv] using this
  rw [h d, h c, key, key]
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simpa using h2)) _ _
theorem contDiff_iterDerivAlong {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (l : List (CoordIdx n)) : ContDiff ℝ ∞ (iterDerivAlong l g) := by
  induction l with
  | nil => exact hg
  | cons c l ih => exact contDiff_coordDeriv ih c.1 c.2
theorem iterDerivAlong_perm {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    {l l' : List (CoordIdx n)} (h : l.Perm l') : iterDerivAlong l g = iterDerivAlong l' g := by
  induction h with
  | nil => rfl
  | cons c _ ih =>
    show coordDeriv c.1 c.2 (iterDerivAlong _ g) =
      coordDeriv c.1 c.2 (iterDerivAlong _ g)
    rw [ih]
  | swap c d l =>
    funext x
    exact coordDeriv_comm (contDiff_iterDerivAlong hg l) d c x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
def idxList (α : MultiIdx4 n) : List (CoordIdx n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem foldr_flatMap {α β γ : Type*} (f : β → γ → γ) (init : γ) (l : List α)
    (t : α → List β) :
    (l.flatMap t).foldr f init = l.foldr (fun a acc => (t a).foldr f acc) init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_flatMap <;> assumption
theorem foldr_replicate_iterate {β γ : Type*} (f : β → γ → γ) (init : γ) (m : ℕ) (a : β) :
    (List.replicate m a).foldr f init = (f a)^[m] init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_replicate <;> assumption
theorem multiDeriv_eq_iterDerivAlong (α : MultiIdx4 n) (g : PointTuple n → ℂ) :
    multiDeriv α g = iterDerivAlong (idxList α) g := by
  unfold iterDerivAlong idxList multiDeriv
  rw [foldr_flatMap]
  simp only [foldr_flatMap, foldr_replicate_iterate]
theorem count_idxList (α : MultiIdx4 n) (c : CoordIdx n) :
    (idxList α).count c = α c.1 c.2 := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.count_indexList <;> assumption
theorem length_idxList (α : MultiIdx4 n) : (idxList α).length = idxOrder α := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.length_indexList <;> assumption
theorem exists_multiIdx_perm (d : List (CoordIdx n)) :
    ∃ γ : MultiIdx4 n, idxOrder γ = d.length ∧ d.Perm (idxList γ) := by apply _root_.YangMills.Construction.TestFunctionOps.exists_idx_perm <;> assumption
theorem tupleNorm_sq (x : PointTuple n) :
    tupleNorm x ^ 2 = ∑ c : CoordIdx n, x c.1 c.2 ^ 2 := by
  unfold tupleNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _),
    Fintype.sum_prod_type]
theorem invFrobeniusNorm_sq (M : CoordMatrix n) :
    invFrobeniusNorm M ^ 2 = ∑ a, ∑ b, M⁻¹ a b ^ 2 := by
  unfold invFrobeniusNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
theorem one_add_tupleNorm_sq_le {M : CoordMatrix n} (hM : IsUnit M) (w x : PointTuple n) :
    1 + tupleNorm x ^ 2 ≤
      affineWeightConst M w * (1 + tupleNorm (affineApply M w x) ^ 2) := by
  set y := affineApply M w x with hy
  let z : CoordIdx n → ℝ := fun c => y c.1 c.2 - w c.1 c.2
  let X : CoordIdx n → ℝ := fun c => x c.1 c.2
  have hz : z = M.mulVec X := by
    funext c
    simp [z, X, hy, affineApply, Matrix.mulVec, dotProduct]
  have hX : X = M⁻¹.mulVec z := by
    rw [hz, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).1 hM), Matrix.one_mulVec]
  have hc : ∀ c, X c ^ 2 ≤ (∑ b, M⁻¹ c b ^ 2) * ∑ b, z b ^ 2 := by
    intro c
    rw [hX]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : tupleNorm x ^ 2 ≤ invFrobeniusNorm M ^ 2 * ∑ b, z b ^ 2 := by
    rw [tupleNorm_sq, invFrobeniusNorm_sq, Finset.sum_mul]
    exact Finset.sum_le_sum fun c _ => hc c
  have hzs : ∑ b, z b ^ 2 ≤ 2 * (tupleNorm y ^ 2 + tupleNorm w ^ 2) := by
    rw [tupleNorm_sq, tupleNorm_sq, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    nlinarith [sq_nonneg (y c.1 c.2 + w c.1 c.2)]
  have ha : 0 ≤ invFrobeniusNorm M ^ 2 := sq_nonneg _
  have hY : 0 ≤ tupleNorm y ^ 2 := sq_nonneg _
  have hW : 0 ≤ tupleNorm w ^ 2 := sq_nonneg _
  have h₁ : tupleNorm x ^ 2 ≤
      invFrobeniusNorm M ^ 2 * (2 * (tupleNorm y ^ 2 + tupleNorm w ^ 2)) :=
    hsum.trans (mul_le_mul_of_nonneg_left hzs ha)
  unfold affineWeightConst
  have h₂ := mul_nonneg (mul_nonneg ha hW) hY
  nlinarith
theorem affineWeightConst_pos (M : CoordMatrix n) (w : PointTuple n) :
    0 < affineWeightConst M w := by
  unfold affineWeightConst
  have : 0 ≤ invFrobeniusNorm M ^ 2 * (1 + tupleNorm w ^ 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith
def affineLinPart (M : CoordMatrix n) : PointTuple n →L[ℝ] PointTuple n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i μ => ∑ c : CoordIdx n, M (i, μ) c * x c.1 c.2
      map_add' := fun x y => by
        funext i μ
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        funext i μ
        simp [Finset.mul_sum, mul_left_comm] }
theorem affineLinPart_apply (M : CoordMatrix n) (x : PointTuple n) (i : Fin n) (μ : Fin 4) :
    affineLinPart M x i μ = ∑ c : CoordIdx n, M (i, μ) c * x c.1 c.2 :=
  rfl
theorem affineApply_eq (M : CoordMatrix n) (w : PointTuple n) :
    affineApply M w = fun x => affineLinPart M x + w :=
  rfl
theorem hasFDerivAt_affineApply (M : CoordMatrix n) (w x : PointTuple n) :
    HasFDerivAt (affineApply M w) (affineLinPart M) x := by
  rw [affineApply_eq]
  exact (affineLinPart M).hasFDerivAt.add_const w
theorem contDiff_affineApply (M : CoordMatrix n) (w : PointTuple n) :
    ContDiff ℝ ∞ (affineApply M w) := by
  rw [affineApply_eq]
  exact (affineLinPart M).contDiff.add contDiff_const
theorem contDiff_affineComp {f : PointTuple n → ℂ} (hf : ContDiff ℝ ∞ f)
    (M : CoordMatrix n) (w : PointTuple n) : ContDiff ℝ ∞ (affineComp M w f) :=
  hf.comp (contDiff_affineApply M w)
theorem affineLinPart_single (M : CoordMatrix n) (c : CoordIdx n) :
    affineLinPart M (Pi.single c.1 (Pi.single c.2 1)) =
      ∑ b : CoordIdx n, M b c • (Pi.single b.1 (Pi.single b.2 1) : PointTuple n) := by
  funext i μ
  rw [affineLinPart_apply, Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single c, Finset.sum_eq_single (i, μ)]
  · simp
  · rintro ⟨j, ν⟩ _ hb
    by_cases hj : i = j
    · subst hj
      have hν : μ ≠ ν := fun h => hb (by rw [h])
      simp [Pi.single_apply, hν]
    · simp [Pi.single_apply, hj]
  · simp
  · rintro ⟨j, ν⟩ _ hb
    obtain ⟨i₀, μ₀⟩ := c
    by_cases hj : j = i₀
    · subst hj
      have hν : ν ≠ μ₀ := fun h => hb (by rw [h])
      simp [Pi.single_apply, hν]
    · simp [Pi.single_apply, hj]
  · simp
theorem coordDeriv_affineComp {f : PointTuple n → ℂ} (hf : ContDiff ℝ ∞ f)
    (M : CoordMatrix n) (w : PointTuple n) (c : CoordIdx n) (x : PointTuple n) :
    coordDeriv c.1 c.2 (affineComp M w f) x =
      ∑ b : CoordIdx n, ((M b c : ℝ) : ℂ) *
        affineComp M w (coordDeriv b.1 b.2 f) x := by
  have hfd : HasFDerivAt f (fderiv ℝ f (affineApply M w x)) (affineApply M w x) :=
    ((hf.differentiable (by simp)) _).hasFDerivAt
  have hc : HasFDerivAt (affineComp M w f)
      ((fderiv ℝ f (affineApply M w x)).comp (affineLinPart M)) x :=
    hfd.comp x (hasFDerivAt_affineApply M w x)
  have hl := (hc.hasLineDerivAt (Pi.single c.1 (Pi.single c.2 1) : PointTuple n)).lineDeriv
  show lineDeriv ℝ _ x _ = _
  rw [hl, ContinuousLinearMap.comp_apply, affineLinPart_single, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, Complex.real_smul]
  congr 1
  exact (coordDeriv_eq_fderiv hf b.1 b.2 _).symm
theorem coordDeriv_sum {T : Type} [Fintype T] (a : T → ℂ) {g : T → PointTuple n → ℂ}
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (c : CoordIdx n) (x : PointTuple n) :
    coordDeriv c.1 c.2 (fun y => ∑ t, a t * g t y) x =
      ∑ t, a t * coordDeriv c.1 c.2 (g t) x := by
  have hd : ∀ t, HasFDerivAt (fun y => a t * g t y) (a t • fderiv ℝ (g t) x) x := fun t =>
    (((hg t).differentiable (by simp)) x).hasFDerivAt.const_mul (a t)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun t _ => hd t
  have hl := (hs.hasLineDerivAt (Pi.single c.1 (Pi.single c.2 1) : PointTuple n)).lineDeriv
  show lineDeriv ℝ _ x _ = _
  rw [hl, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, coordDeriv_eq_fderiv (hg t)]
theorem iterDerivAlong_affineComp {f : PointTuple n → ℂ} (hf : ContDiff ℝ ∞ f)
    (M : CoordMatrix n) (w : PointTuple n) (l : List (CoordIdx n)) :
    ∀ p, l.length = p →
    ∃ (T : Type) (_ : Fintype T) (entries : T → Fin p → CoordIdx n × CoordIdx n)
      (d : T → List (CoordIdx n)),
      Fintype.card T = (4 * n) ^ p ∧ (∀ t, (d t).length = p) ∧
      ∀ x, iterDerivAlong l (affineComp M w f) x =
        ∑ t, ((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
          affineComp M w (iterDerivAlong (d t) f) x := by
  induction l with
  | nil =>
    intro p hp
    have hp0 : p = 0 := by simpa using hp.symm
    subst hp0
    refine ⟨Unit, inferInstance, fun _ s => s.elim0, fun _ => [], by simp, fun _ => rfl, ?_⟩
    intro x
    simp [iterDerivAlong]
  | cons c l ih =>
    intro p hp
    cases p with
    | zero => simp at hp
    | succ p =>
      obtain ⟨T, _, entries, d, hcard, hd, hsum⟩ := ih p (by simpa using hp)
      refine ⟨CoordIdx n × T, inferInstance,
        fun u => Fin.cons (u.1, c) (entries u.2), fun u => u.1 :: d u.2, ?_, ?_, ?_⟩
      · simp [Fintype.card_prod, hcard, pow_succ, CoordIdx]
        ring
      · intro u
        simp [hd]
      · intro x
        have hfun : iterDerivAlong l (affineComp M w f) = fun y =>
            ∑ t, ((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
              affineComp M w (iterDerivAlong (d t) f) y := funext hsum
        have hstep : iterDerivAlong (c :: l) (affineComp M w f) x =
            coordDeriv c.1 c.2 (iterDerivAlong l (affineComp M w f)) x := rfl
        rw [hstep, hfun, coordDeriv_sum _
          (fun t => contDiff_affineComp (contDiff_iterDerivAlong hf (d t)) M w) c x,
          Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [coordDeriv_affineComp (contDiff_iterDerivAlong hf (d t)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        push_cast
        have : iterDerivAlong (b :: d t) f =
            coordDeriv b.1 b.2 (iterDerivAlong (d t) f) := rfl
        rw [this]
        ring
theorem derivExpansion_of_contDiff {f : PointTuple n → ℂ} (hf : ContDiff ℝ ∞ f)
    (M : CoordMatrix n) (w : PointTuple n) (p : ℕ) (α : MultiIdx4 n) (hα : idxOrder α = p) :
    DerivExpansion M w f p α := by
  obtain ⟨T, _, entries, d, hcard, hd, hsum⟩ := iterDerivAlong_affineComp hf M w
    (idxList α) p (by rw [length_idxList, hα])
  let e : Fin ((4 * n) ^ p) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  have hγ := fun t => exists_multiIdx_perm (d t)
  choose γ hγo hγp using hγ
  refine ⟨fun t => entries (e t), fun t => γ (e t), fun t => by rw [hγo, hd], fun x => ?_⟩
  rw [multiDeriv_eq_iterDerivAlong, hsum x, ← e.sum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [multiDeriv_eq_iterDerivAlong, iterDerivAlong_perm hf (hγp (e t))]
theorem norm_multiDeriv_affineComp_le {M : CoordMatrix n} {w : PointTuple n}
    {φ : PointTuple n → ℂ} {p : ℕ}
    {α : MultiIdx4 n} {c B : ℝ} (hs : DerivExpansion M w φ p α) (hc : EntryBound M c)
    (hB0 : 0 ≤ B) (x : PointTuple n)
    (hB : ∀ γ : MultiIdx4 n, idxOrder γ = p →
      ‖multiDeriv γ φ (affineApply M w x)‖ ≤ B) :
    ‖multiDeriv α (affineComp M w φ) x‖ ≤ (4 * (n : ℝ) * c) ^ p * B := by
  obtain ⟨entries, γ, hγ, h⟩ := hs
  have hc0 : 0 ≤ c := zero_le_one.trans hc.1
  have term : ∀ t, ‖((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
      affineComp M w (multiDeriv (γ t) φ) x‖ ≤ c ^ p * B := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    have h1 : ∏ s, |M (entries t s).1 (entries t s).2| ≤ c ^ p := by
      calc ∏ s, |M (entries t s).1 (entries t s).2| ≤ ∏ _s : Fin p, c :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun s _ => hc.2 _ _)
        _ = c ^ p := by simp
    exact mul_le_mul h1 (hB _ (hγ t)) (norm_nonneg _) (pow_nonneg hc0 _)
  rw [h x]
  calc ‖∑ t, ((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
          affineComp M w (multiDeriv (γ t) φ) x‖
      ≤ ∑ t, ‖((∏ s, M (entries t s).1 (entries t s).2 : ℝ) : ℂ) *
          affineComp M w (multiDeriv (γ t) φ) x‖ := norm_sum_le _ _
    _ ≤ ∑ _t : Fin ((4 * n) ^ p), c ^ p * B := Finset.sum_le_sum fun t _ => term t
    _ = (4 * (n : ℝ) * c) ^ p * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [mul_pow]
        ring
theorem term_le_weightedSeminorm (k : ℕ) (φ : PointTuple n → ℂ) (x : PointTuple n)
    (α : MultiIdx4 n) (h : idxOrder α ≤ k) :
    ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α φ x‖) ≤
      weightedSeminorm k φ := by apply _root_.YangMills.Construction.TestSpaces.Elementary.weightedTerm_le_seminorm <;> assumption
theorem weightedSeminorm_affineComp_le {φ : PointTuple n → ℂ} (hn : 0 < n)
    (hφ : ContDiff ℝ ∞ φ) {k : ℕ} (hfin : weightedSeminorm k φ ≠ ⊤) {M : CoordMatrix n}
    (w : PointTuple n) {c : ℝ} (hM : IsUnit M) (hc : EntryBound M c) :
    weightedSeminorm k (affineComp M w φ) ≤
      ENNReal.ofReal ((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
        weightedSeminorm k φ := by
  have hW : ENNReal.ofReal (weightedSeminorm k φ).toReal = weightedSeminorm k φ :=
    ENNReal.ofReal_toReal hfin
  have hW0 : 0 ≤ (weightedSeminorm k φ).toReal := ENNReal.toReal_nonneg
  have each : ∀ (y : PointTuple n) (γ : MultiIdx4 n), idxOrder γ ≤ k →
      (1 + tupleNorm y ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv γ φ y‖ ≤
        (weightedSeminorm k φ).toReal := fun y γ h =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (term_le_weightedSeminorm k φ y γ h)
  have hC := affineWeightConst_pos M w
  have hCk : 0 < affineWeightConst M w ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hC _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : 1 ≤ 4 * (n : ℝ) * c := by nlinarith [hc.1]
  have h4k : 0 ≤ (4 * (n : ℝ) * c) ^ k := pow_nonneg (by linarith) _
  conv_lhs => unfold weightedSeminorm
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  have hpos : ∀ u : PointTuple n, 0 < 1 + tupleNorm u ^ 2 := fun u => by positivity
  have hD : 0 < (1 + tupleNorm (affineApply M w x) ^ 2) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos (hpos _) _
  have hnorm := norm_multiDeriv_affineComp_le
    (derivExpansion_of_contDiff hφ M w (idxOrder α) α rfl) hc
    (div_nonneg hW0 hD.le) x (fun γ hγ => by
      rw [le_div_iff₀ hD, mul_comm]
      exact each _ γ (hγ ▸ hα))
  have hx : (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) ≤ affineWeightConst M w ^ ((k : ℝ) / 2) *
      (1 + tupleNorm (affineApply M w x) ^ 2) ^ ((k : ℝ) / 2) := by
    rw [← Real.mul_rpow hC.le (hpos _).le]
    exact Real.rpow_le_rpow (hpos x).le (one_add_tupleNorm_sq_le hM w x) (by positivity)
  have hp : (4 * (n : ℝ) * c) ^ idxOrder α ≤ (4 * (n : ℝ) * c) ^ k := pow_le_pow_right₀ h4 hα
  have hreal : (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) *
      ‖multiDeriv α (affineComp M w φ) x‖ ≤
      ((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
        (weightedSeminorm k φ).toReal := by
    calc (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) *
          ‖multiDeriv α (affineComp M w φ) x‖
        ≤ (affineWeightConst M w ^ ((k : ℝ) / 2) *
            (1 + tupleNorm (affineApply M w x) ^ 2) ^ ((k : ℝ) / 2)) *
          ((4 * (n : ℝ) * c) ^ k * ((weightedSeminorm k φ).toReal /
            (1 + tupleNorm (affineApply M w x) ^ 2) ^ ((k : ℝ) / 2))) :=
          mul_le_mul hx (hnorm.trans (mul_le_mul_of_nonneg_right hp (div_nonneg hW0 hD.le)))
            (norm_nonneg _) (mul_pos hCk hD).le
      _ = ((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
            (weightedSeminorm k φ).toReal := by
          field_simp
  calc ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) *
        ‖multiDeriv α (affineComp M w φ) x‖)
      ≤ ENNReal.ofReal (((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
          (weightedSeminorm k φ).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (mul_nonneg h4k hCk.le), hW]
theorem affineCompBounds : AffineCompBounds := by
  intro n hn φ hφ M w c hM hc
  have hb : ∀ k : ℕ, 0 < k → weightedSeminorm k (affineComp M w φ) ≤
      ENNReal.ofReal ((4 * (n : ℝ) * c) ^ k * affineWeightConst M w ^ ((k : ℝ) / 2)) *
        weightedSeminorm k φ := fun k hk =>
    weightedSeminorm_affineComp_le hn hφ.1 (hφ.2 k hk).ne w hM hc
  refine ⟨one_add_tupleNorm_sq_le hM w, ⟨contDiff_affineComp hφ.1 M w, fun k hk => ?_⟩,
    fun p α hα => derivExpansion_of_contDiff hφ.1 M w p α hα, hb⟩
  exact lt_of_le_of_lt (hb k hk) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφ.2 k hk))
theorem multiDeriv_multiDeriv {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (α β : MultiIdx4 n) :
    multiDeriv α (multiDeriv β φ) = multiDeriv (α + β) φ := by
  rw [multiDeriv_eq_iterDerivAlong α, multiDeriv_eq_iterDerivAlong β,
    multiDeriv_eq_iterDerivAlong (α + β)]
  have h : iterDerivAlong (idxList α) (iterDerivAlong (idxList β) φ) =
      iterDerivAlong (idxList α ++ idxList β) φ := by
    unfold iterDerivAlong
    rw [List.foldr_append]
  rw [h]
  exact iterDerivAlong_perm hφ (List.perm_iff_count.2 fun c => by
    rw [List.count_append, count_idxList, count_idxList, count_idxList]
    rfl)
theorem idxOrder_add (α β : MultiIdx4 n) : idxOrder (α + β) = idxOrder α + idxOrder β := by
  simp [idxOrder, Finset.sum_add_distrib]
theorem derivSchwartzBounds : DerivSchwartzBounds := by
  intro n hn φ hφ β
  have hb : ∀ k : ℕ, weightedSeminorm k (multiDeriv β φ) ≤
      weightedSeminorm (k + idxOrder β) φ := by
    intro k
    conv_lhs => unfold weightedSeminorm
    refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
    rw [multiDeriv_multiDeriv hφ.1]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (term_le_weightedSeminorm (k + idxOrder β) φ x (α + β) (by rw [idxOrder_add]; omega))
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _)) ?_
    have : (0 : ℝ) ≤ idxOrder β := Nat.cast_nonneg _
    push_cast
    linarith
  refine ⟨⟨?_, fun k hk => lt_of_le_of_lt (hb k) (hφ.2 _ (by omega))⟩, fun k _ => hb k⟩
  rw [multiDeriv_eq_iterDerivAlong]
  exact contDiff_iterDerivAlong hφ.1 _
theorem valToFun_actOfOrder (r : RigidMotion) {q : ℕ} (F : TensorVal ℂ q) :
    valToFun (actOfOrder r F) = actOnFun r (valToFun F) := by
  cases q <;> rfl
theorem valToFun_injective {q : ℕ} :
    Function.Injective (valToFun (q := q)) := by apply _root_.YangMills.Construction.TestFunctionOps.valToFun_injective <;> assumption
theorem motionTensorProd : MotionTensorProd := by
  intro q q' r φ ψ _ _
  apply valToFun_injective
  rw [valToFun_actOfOrder, tensorVal, tensorVal,
    valToFun_funToVal, valToFun_funToVal,
    valToFun_actOfOrder, valToFun_actOfOrder]
  rfl
def shiftPoint (v : Fin 4 → ℝ) (x : PointTuple n) : PointTuple n := fun i => x i - v
theorem coordDeriv_comp_shiftPoint (v : Fin 4 → ℝ) (g : PointTuple n → ℂ) (i : Fin n)
    (μ : Fin 4) (x : PointTuple n) :
    coordDeriv i μ (fun y => g (shiftPoint v y)) x =
      coordDeriv i μ g (shiftPoint v x) := by
  unfold coordDeriv lineDeriv
  congr 1
  funext t
  show g (shiftPoint v _) = g _
  congr 1
  funext j ν
  simp only [shiftPoint, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring
theorem iterDerivAlong_comp_shiftPoint (v : Fin 4 → ℝ) (g : PointTuple n → ℂ)
    (l : List (CoordIdx n)) :
    iterDerivAlong l (fun y => g (shiftPoint v y)) =
      fun x => iterDerivAlong l g (shiftPoint v x) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    funext x
    show coordDeriv c.1 c.2 (iterDerivAlong l _) x =
      coordDeriv c.1 c.2 (iterDerivAlong l g) (shiftPoint v x)
    rw [ih]
    exact coordDeriv_comp_shiftPoint v _ c.1 c.2 x
theorem actOnFun_translate_eq (v : Fin 4 → ℝ) (φ : PointTuple n → ℂ) :
    actOnFun (translateMotion v) φ = fun y => φ (shiftPoint v y) :=
  funext fun x => actOnFun_translateMotion v φ x
theorem translatePreservesPlus (hOps : TestFunctionOps.OperationsStatement) :
    TranslatePreservesPlus := by
  intro n hn φ hφ v hv
  obtain ⟨hS, _, hopen, hflat⟩ := hφ
  have hmem : actOnFun (translateMotion v) φ ∈ schwartzSet n :=
    (((hOps.1 n 1 hn one_pos (Equiv.refl _) (translateMotion v)).2.1 φ hS).1).2.1
  refine ⟨hmem, hmem.1, hopen, fun x hx => ?_⟩
  have hout : shiftPoint v x ∈ (positiveTimeLocus n)ᶜ := by
    intro hin
    apply hx
    refine ⟨fun i j hij => hin.1 ?_, fun i => ?_⟩
    · show shiftPoint v x i = shiftPoint v x j
      simp [shiftPoint, hij]
    · have h := hin.2 i
      simp only [timeCoord, shiftPoint, Pi.sub_apply] at h ⊢
      linarith
  obtain ⟨_, h0, hd⟩ := hflat _ hout
  refine ⟨hmem.1, ?_, fun α => ?_⟩
  · rw [actOnFun_translate_eq]
    exact h0
  · rw [actOnFun_translate_eq, multiDeriv_eq_iterDerivAlong, iterDerivAlong_comp_shiftPoint]
    show iterDerivAlong _ φ (shiftPoint v x) = 0
    rw [← multiDeriv_eq_iterDerivAlong]
    exact hd α
theorem timeReflect_sub_timeReflect (u v : Fin 4 → ℝ) :
    timeReflect (u - timeReflect v) = timeReflect u - v := by
  funext μ
  fin_cases μ <;> simp [timeReflect] <;> ring
theorem reflectConj_translate (φ : PointTuple n → ℂ) (v : Fin 4 → ℝ) :
    reflectConj (actOnFun (translateMotion v) φ) =
      actOnFun (translateMotion (timeReflect v)) (reflectConj φ) := by
  funext x
  rw [actOnFun_translateMotion]
  simp only [reflectConj]
  rw [actOnFun_translateMotion]
  congr 2
  funext i
  exact (timeReflect_sub_timeReflect (x i) v).symm
theorem reflectTranslate : ReflectTranslate := by
  intro q φ _
  have main : ∀ v : Fin 4 → ℝ, reflectConjVal (translateOfOrder v φ) =
      translateOfOrder (timeReflect v) (reflectConjVal φ) := by
    intro v
    cases q with
    | zero => rfl
    | succ m => exact reflectConj_translate φ v
  refine ⟨main, fun t => ?_, fun v hv => ?_⟩
  · have h : timeReflect (t • PeriodicLattice.coordVec 3) =
        (-t) • PeriodicLattice.coordVec 3 := by
      funext μ
      fin_cases μ <;> simp [timeReflect, PeriodicLattice.coordVec]
    rw [main, h]
  · have h : timeReflect v = v := by
      have hv3 : v 3 = 0 := hv
      funext μ
      fin_cases μ <;> simp [timeReflect, hv3]
    rw [main, h]
theorem statement_holds (hOps : TestFunctionOps.OperationsStatement) : Statement :=
  ⟨motionTensorProd, translatePreservesPlus hOps, reflectTranslate,
    affineCompBounds, derivSchwartzBounds⟩
end YangMills.Construction.MotionsTranslations
