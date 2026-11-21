import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.OperationsOnTestFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ComplexConjugate
noncomputable section
namespace YangMills.Construction.TestFunctionOps
open TestSpaces Motions Motions.RigidMotion HyperplaneReflection
variable {n : ℕ}
def iteratedLineDeriv (l : List (PointTuple n)) (g : PointTuple n → ℂ) : PointTuple n → ℂ :=
  l.foldr (fun e h x => lineDeriv ℝ h x e) g
theorem lineDeriv_eq_fderiv_of_smooth {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (x e : PointTuple n) :
    lineDeriv ℝ g x e = fderiv ℝ g x e :=
  ((hg.differentiable (by simp)) x).lineDeriv_eq_fderiv
theorem contDiff_lineDeriv_apply {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (e : PointTuple n) :
    ContDiff ℝ ∞ fun x => lineDeriv ℝ g x e := by
  have h : (fun x => lineDeriv ℝ g x e) = fun x => fderiv ℝ g x e :=
    funext fun x => lineDeriv_eq_fderiv_of_smooth hg x e
  rw [h]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem lineDeriv_lineDeriv_comm {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (e f x : PointTuple n) :
    lineDeriv ℝ (fun y => lineDeriv ℝ g y f) x e =
      lineDeriv ℝ (fun y => lineDeriv ℝ g y e) x f := by
  have h : ∀ v : PointTuple n, (fun y => lineDeriv ℝ g y v) = fun y => fderiv ℝ g y v :=
    fun v => funext fun y => lineDeriv_eq_fderiv_of_smooth hg y v
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have key : ∀ v w : PointTuple n,
      lineDeriv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
    intro v w
    have := (HasFDerivAt.hasLineDerivAt
      ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt) w).lineDeriv
    simpa [Function.comp_def] using this
  rw [h f, h e, key, key]
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simpa using h2)) e f
theorem contDiff_iteratedLineDeriv {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (l : List (PointTuple n)) :
    ContDiff ℝ ∞ (iteratedLineDeriv l g) := by
  induction l with
  | nil => exact hg
  | cons e l ih => exact contDiff_lineDeriv_apply ih e
theorem iteratedLineDeriv_perm {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    {l l' : List (PointTuple n)}
    (h : l.Perm l') : iteratedLineDeriv l g = iteratedLineDeriv l' g := by
  induction h with
  | nil => rfl
  | cons e _ ih =>
    show (fun x => lineDeriv ℝ (iteratedLineDeriv _ g) x e) =
      fun x => lineDeriv ℝ (iteratedLineDeriv _ g) x e
    rw [ih]
  | swap e f l =>
    funext x
    exact lineDeriv_lineDeriv_comm (contDiff_iteratedLineDeriv hg l) f e x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
def basisDir (c : Fin n × Fin 4) : PointTuple n := Pi.single c.1 (Pi.single c.2 1)
theorem pi_single_eq_sum_basisDir (i : Fin n) (u : Fin 4 → ℝ) :
    (Pi.single i u : PointTuple n) = ∑ ν, u ν • basisDir (i, ν) := by
  funext j μ
  by_cases hj : j = i
  · subst hj
    simp [basisDir, Finset.sum_apply, Pi.single_apply]
  · simp [basisDir, Finset.sum_apply, hj]
theorem norm_iteratedLineDeriv_le {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (x : PointTuple n) (l : List (PointTuple n)) :
    ∀ c : List (Fin n × Fin 4),
      (∀ w ∈ l, ∃ (i : Fin n) (u : Fin 4 → ℝ), w = Pi.single i u ∧ ∑ ν, |u ν| ≤ C) →
      (∀ d : List (Fin n × Fin 4), d.length = l.length + c.length →
        ‖iteratedLineDeriv (d.map basisDir) g x‖ ≤ M) →
      ‖iteratedLineDeriv (l ++ c.map basisDir) g x‖ ≤ C ^ l.length * M := by
  induction l with
  | nil =>
    intro c _ h
    simpa using h c (by simp)
  | cons w l ih =>
    intro c hl h
    obtain ⟨i, u, rfl, hu⟩ := hl w (by simp)
    have hl' : ∀ w ∈ l, ∃ (i : Fin n) (u : Fin 4 → ℝ), w = Pi.single i u ∧ ∑ ν, |u ν| ≤ C :=
      fun w hw => hl w (by simp [hw])
    have hH := contDiff_iteratedLineDeriv hg (l ++ c.map basisDir)
    have key : iteratedLineDeriv ((Pi.single i u :: l) ++ c.map basisDir) g x =
        ∑ ν, u ν • iteratedLineDeriv (l ++ ((i, ν) :: c).map basisDir) g x := by
      show lineDeriv ℝ (iteratedLineDeriv (l ++ c.map basisDir) g) x (Pi.single i u) = _
      rw [lineDeriv_eq_fderiv_of_smooth hH, pi_single_eq_sum_basisDir, map_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [map_smul, ← lineDeriv_eq_fderiv_of_smooth hH]
      have hp : iteratedLineDeriv (l ++ ((i, ν) :: c).map basisDir) g =
          iteratedLineDeriv (basisDir (i, ν) :: (l ++ c.map basisDir)) g :=
        iteratedLineDeriv_perm hg List.perm_middle
      rw [hp]
      rfl
    have hb : ∀ ν, ‖iteratedLineDeriv (l ++ ((i, ν) :: c).map basisDir) g x‖ ≤
        C ^ l.length * M := fun ν =>
      ih _ hl' fun d hd => h d (by simp at hd ⊢; omega)
    rw [key]
    calc ‖∑ ν, u ν • iteratedLineDeriv (l ++ ((i, ν) :: c).map basisDir) g x‖
        ≤ ∑ ν, ‖u ν • iteratedLineDeriv (l ++ ((i, ν) :: c).map basisDir) g x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ν, |u ν| * (C ^ l.length * M) := by
          refine Finset.sum_le_sum fun ν _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb ν) (abs_nonneg _)
      _ = (∑ ν, |u ν|) * (C ^ l.length * M) := (Finset.sum_mul _ _ _).symm
      _ ≤ C * (C ^ l.length * M) :=
          mul_le_mul_of_nonneg_right hu (mul_nonneg (pow_nonneg hC _) hM)
      _ = C ^ (Pi.single i u :: l).length * M := by
          rw [List.length_cons, pow_succ]
          ring
def idxList (α : MultiIdx4 n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem list_foldr_flatMap {α β γ : Type*} (f : β → γ → γ) (init : γ) (l : List α)
    (t : α → List β) :
    (l.flatMap t).foldr f init = l.foldr (fun a acc => (t a).foldr f acc) init := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.foldr_append, ih]
theorem list_foldr_replicate {β γ : Type*} (f : β → γ → γ) (init : γ) (m : ℕ) (a : β) :
    (List.replicate m a).foldr f init = (f a)^[m] init := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, Function.iterate_succ_apply', ih]
theorem multiDeriv_eq_iteratedLineDeriv (α : MultiIdx4 n) (g : PointTuple n → ℂ) :
    multiDeriv α g = iteratedLineDeriv ((idxList α).map basisDir) g := by
  unfold iteratedLineDeriv idxList multiDeriv
  rw [List.foldr_map, list_foldr_flatMap]
  simp only [list_foldr_flatMap, list_foldr_replicate]
  rfl
theorem count_idxList (α : MultiIdx4 n) (c : Fin n × Fin 4) :
    (idxList α).count c = α c.1 c.2 := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.count_indexList <;> assumption
theorem length_idxList (α : MultiIdx4 n) : (idxList α).length = idxOrder α := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.length_indexList <;> assumption
theorem exists_idx_perm (d : List (Fin n × Fin 4)) :
    ∃ γ : MultiIdx4 n, idxOrder γ = d.length ∧ d.Perm (idxList γ) := by
  refine ⟨fun i μ => d.count (i, μ), ?_, ?_⟩ <;> [skip; skip]
  all_goals
    have hp : d.Perm (idxList fun i μ => d.count (i, μ)) :=
      List.perm_iff_count.2 fun c => by rw [count_idxList]
  · rw [← length_idxList, hp.length_eq]
  · exact hp
def affineArgs (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) (σ : Equiv.Perm (Fin n))
    (x : PointTuple n) : PointTuple n :=
  fun i => A.mulVec (x (σ i)) + w
def linearArgs (A : Matrix (Fin 4) (Fin 4) ℝ) (σ : Equiv.Perm (Fin n)) :
    PointTuple n →L[ℝ] PointTuple n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => A.mulVec (x (σ i))
      map_add' := fun x y => by
        funext i
        simp [Matrix.mulVec_add]
      map_smul' := fun c x => by
        funext i
        simp [Matrix.mulVec_smul] }
theorem affineArgs_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) (σ : Equiv.Perm (Fin n))
    (x : PointTuple n) (i : Fin n) : affineArgs A w σ x i = A.mulVec (x (σ i)) + w :=
  rfl
theorem linearArgs_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (σ : Equiv.Perm (Fin n))
    (x : PointTuple n) (i : Fin n) : linearArgs A σ x i = A.mulVec (x (σ i)) :=
  rfl
theorem hasFDerivAt_affineArgs (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : PointTuple n) :
    HasFDerivAt (affineArgs A w σ) (linearArgs A σ) x :=
  (linearArgs A σ).hasFDerivAt.add_const (fun _ => w)
theorem contDiff_affineArgs (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (affineArgs A w σ) :=
  (linearArgs A σ).contDiff.add contDiff_const
theorem linearArgs_basisDir (A : Matrix (Fin 4) (Fin 4) ℝ) (σ : Equiv.Perm (Fin n))
    (c : Fin n × Fin 4) :
    linearArgs A σ (basisDir c) = Pi.single (σ.symm c.1) fun ν => A ν c.2 := by
  funext j
  rw [linearArgs_apply]
  by_cases hj : j = σ.symm c.1
  · subst hj
    funext ν
    simp [basisDir]
  · have h : σ j ≠ c.1 := fun h => hj (by rw [← h]; simp)
    simp [basisDir, hj, h]
theorem iteratedLineDeriv_comp {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (T : ℂ →L[ℝ] ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) (σ : Equiv.Perm (Fin n))
    (l : List (PointTuple n)) :
    iteratedLineDeriv l (fun x => T (g (affineArgs A w σ x))) = fun x =>
      T (iteratedLineDeriv (l.map (linearArgs A σ)) g (affineArgs A w σ x)) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    funext x
    show lineDeriv ℝ (iteratedLineDeriv l (fun x => T (g (affineArgs A w σ x)))) x e =
      T (lineDeriv ℝ (iteratedLineDeriv (l.map (linearArgs A σ)) g) (affineArgs A w σ x)
        (linearArgs A σ e))
    have hH := contDiff_iteratedLineDeriv hg (l.map (linearArgs A σ))
    have hd : HasFDerivAt (iteratedLineDeriv (l.map (linearArgs A σ)) g)
        (fderiv ℝ (iteratedLineDeriv (l.map (linearArgs A σ)) g) (affineArgs A w σ x))
        (affineArgs A w σ x) := ((hH.differentiable (by simp)) _).hasFDerivAt
    have h := (HasFDerivAt.hasLineDerivAt
      (T.hasFDerivAt.comp x (hd.comp x (hasFDerivAt_affineArgs A w σ x))) e).lineDeriv
    rw [ih, lineDeriv_eq_fderiv_of_smooth hH]
    simpa [Function.comp_def] using h
theorem norm_multiDeriv_comp_le {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (T : ℂ →L[ℝ] ℂ)
    (hT : ∀ z, ‖T z‖ = ‖z‖) (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin n)) {C M : ℝ} (hA : ∀ μ, ∑ ν, |A ν μ| ≤ C) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (α : MultiIdx4 n) (x : PointTuple n)
    (h : ∀ γ : MultiIdx4 n, idxOrder γ = idxOrder α →
      ‖multiDeriv γ g (affineArgs A w σ x)‖ ≤ M) :
    ‖multiDeriv α (fun x => T (g (affineArgs A w σ x))) x‖ ≤ C ^ idxOrder α * M := by
  rw [multiDeriv_eq_iteratedLineDeriv, iteratedLineDeriv_comp hg]
  have hb := norm_iteratedLineDeriv_le hg hC hM (affineArgs A w σ x)
    (((idxList α).map basisDir).map (linearArgs A σ)) [] ?_ ?_
  · simpa [hT, length_idxList] using hb
  · intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨_, ⟨c, -, rfl⟩, rfl⟩ := hv
    exact ⟨_, _, linearArgs_basisDir A σ c, hA c.2⟩
  · intro d hd
    obtain ⟨γ, hγ, hp⟩ := exists_idx_perm d
    rw [iteratedLineDeriv_perm hg (hp.map basisDir), ← multiDeriv_eq_iteratedLineDeriv]
    refine h γ ?_
    rw [hγ, hd]
    simp [length_idxList]
structure AffineControl (T : ℂ →L[ℝ] ℂ) (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin n)) (C κ : ℝ) : Prop where
  norm_T : ∀ z, ‖T z‖ = ‖z‖
  entries : ∀ μ, ∑ ν, |A ν μ| ≤ C
  one_le : 1 ≤ C
  pos : 0 < κ
  weight : ∀ x : PointTuple n,
    1 + tupleNorm x ^ 2 ≤ κ * (1 + tupleNorm (affineArgs A w σ x) ^ 2)
theorem contDiff_comp_affineArgs {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g) (T : ℂ →L[ℝ] ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ fun x => T (g (affineArgs A w σ x)) :=
  T.contDiff.comp (hg.comp (contDiff_affineArgs A w σ))
section Control
variable {T : ℂ →L[ℝ] ℂ} {A : Matrix (Fin 4) (Fin 4) ℝ} {w : Fin 4 → ℝ}
  {σ : Equiv.Perm (Fin n)} {C κ : ℝ}
theorem weightedSeminorm_comp_le {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (h : AffineControl T A w σ C κ) (k : ℕ) :
    weightedSeminorm k (fun x => T (g (affineArgs A w σ x))) ≤
      ENNReal.ofReal (C ^ k * κ ^ ((k : ℝ) / 2)) * weightedSeminorm k g := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos h.one_le
  have hκk : 0 < κ ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos h.pos _
  have hc : 0 < C ^ k * κ ^ ((k : ℝ) / 2) := mul_pos (pow_pos hC0 k) hκk
  by_cases htop : weightedSeminorm k g = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using hc)]
    exact le_top
  have hW0 : 0 ≤ (weightedSeminorm k g).toReal := ENNReal.toReal_nonneg
  have each : ∀ (y : PointTuple n) (γ : MultiIdx4 n), idxOrder γ ≤ k →
      (1 + tupleNorm y ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv γ g y‖ ≤
        (weightedSeminorm k g).toReal := by
    intro y γ hγ
    have hle : ENNReal.ofReal ((1 + tupleNorm y ^ 2) ^ ((k : ℝ) / 2) *
        ‖multiDeriv γ g y‖) ≤ weightedSeminorm k g := by
      conv_rhs => unfold weightedSeminorm
      exact le_iSup_of_le y (le_iSup_of_le γ (le_iSup_of_le hγ le_rfl))
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 hle
  have hfin : ENNReal.ofReal (weightedSeminorm k g).toReal = weightedSeminorm k g :=
    ENNReal.ofReal_toReal htop
  generalize hW : (weightedSeminorm k g).toReal = W at hW0 each hfin
  rw [← hfin, ← ENNReal.ofReal_mul hc.le]
  conv_lhs => unfold weightedSeminorm
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
  set P := (1 + tupleNorm (affineArgs A w σ x) ^ 2) ^ ((k : ℝ) / 2) with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos (by positivity) _
  have hw : (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) ≤ κ ^ ((k : ℝ) / 2) * P := by
    rw [hPdef, ← Real.mul_rpow h.pos.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (h.weight x) (by positivity)
  have hb := norm_multiDeriv_comp_le hg T h.norm_T A w σ h.entries hC0.le
    (div_nonneg hW0 hP.le) α x fun γ hγ => (le_div_iff₀' hP).2 (each _ γ (hγ.le.trans hα))
  have hpow : C ^ idxOrder α ≤ C ^ k := pow_le_pow_right₀ h.one_le hα
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hpow (div_nonneg hW0 hP.le))
  calc _ ≤ (κ ^ ((k : ℝ) / 2) * P) * (C ^ k * (W / P)) :=
        mul_le_mul hw hb' (norm_nonneg _) (mul_nonneg hκk.le hP.le)
    _ = C ^ k * κ ^ ((k : ℝ) / 2) * W := by field_simp
theorem multiDeriv_comp_eq_zero {g : PointTuple n → ℂ} (hg : ContDiff ℝ ∞ g)
    (h : AffineControl T A w σ C κ) (α : MultiIdx4 n) (x : PointTuple n)
    (hz : ∀ γ : MultiIdx4 n, multiDeriv γ g (affineArgs A w σ x) = 0) :
    multiDeriv α (fun x => T (g (affineArgs A w σ x))) x = 0 := by
  have hb := norm_multiDeriv_comp_le hg T h.norm_T A w σ h.entries
    (zero_le_one.trans h.one_le) le_rfl α x fun γ _ => by simp [hz γ]
  simpa using hb
theorem affineArgs_mem_diagonalLocus (A : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin n)) {x : PointTuple n} (hx : x ∈ diagonalLocus n) :
    affineArgs A w σ x ∈ diagonalLocus n := by
  have hx' : ¬ Function.Injective x := hx
  show ¬ Function.Injective (affineArgs A w σ x)
  intro hinj
  refine hx' fun a b hab => ?_
  have h := @hinj (σ.symm a) (σ.symm b) (by simp [affineArgs, hab])
  simpa using h
theorem comp_mem_schwartzSet {φ : PointTuple n → ℂ} (hφ : φ ∈ schwartzSet n)
    (h : AffineControl T A w σ C κ) :
    (fun x => T (φ (affineArgs A w σ x))) ∈ schwartzSet n :=
  ⟨contDiff_comp_affineArgs hφ.1 T A w σ, fun k hk => lt_of_le_of_lt
    (weightedSeminorm_comp_le hφ.1 h k)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφ.2 k hk))⟩
theorem comp_mem_flatSchwartzSet {φ : PointTuple n → ℂ} (hφ : φ ∈ flatSchwartzSet n)
    (h : AffineControl T A w σ C κ) :
    (fun x => T (φ (affineArgs A w σ x))) ∈ flatSchwartzSet n :=
  ⟨comp_mem_schwartzSet hφ.1 h, fun α x hx => multiDeriv_comp_eq_zero hφ.1.1 h α x
    fun γ => hφ.2 γ _ (affineArgs_mem_diagonalLocus A w σ hx)⟩
end Control
theorem permuteArgs_eq_comp (ς : Equiv.Perm (Fin n)) (φ : PointTuple n → ℂ) :
    permuteArgs ς φ =
      fun x => ContinuousLinearMap.id ℝ ℂ (φ (affineArgs 1 0 ς x)) := by
  funext x
  have h : affineArgs 1 0 ς x = fun i => x (ς i) := by
    funext i
    simp [affineArgs_apply]
  simp [permuteArgs, h]
theorem affineArgs_rigid (r : RigidMotion) (x : PointTuple n) :
    affineArgs r.mat⁻¹ (-(r.mat⁻¹.mulVec r.shift)) 1 x = fun i => r.invFun (x i) := by
  funext i
  show r.mat⁻¹.mulVec (x i) + -(r.mat⁻¹.mulVec r.shift) = r.mat⁻¹.mulVec (x i - r.shift)
  rw [Matrix.mulVec_sub, sub_eq_add_neg]
theorem actOnFun_eq_comp (r : RigidMotion) (φ : PointTuple n → ℂ) :
    actOnFun r φ = fun x =>
      ContinuousLinearMap.id ℝ ℂ (φ (affineArgs r.mat⁻¹ (-(r.mat⁻¹.mulVec r.shift)) 1 x)) := by
  funext x
  simp [actOnFun, affineArgs_rigid]
theorem affineArgs_timeReflection (x : PointTuple n) :
    affineArgs timeReflection.mat 0 1 x = timeReflectTuple x := by
  funext i
  show timeReflection.toFun (x i) = timeReflect (x i)
  rw [timeReflection_toFun]
theorem reflectConj_eq_comp (φ : PointTuple n → ℂ) :
    reflectConj φ = fun x =>
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (φ (affineArgs timeReflection.mat 0 1 x)) := by
  funext x
  rw [affineArgs_timeReflection]
  simp [reflectConj]
theorem tupleNorm_affineArgs_perm (ς : Equiv.Perm (Fin n)) (x : PointTuple n) :
    tupleNorm (affineArgs 1 0 ς x) = tupleNorm x := by
  have h : ∀ i μ, affineArgs 1 0 ς x i μ = x (ς i) μ := fun i μ => by simp [affineArgs_apply]
  simp only [tupleNorm, h]
  rw [Equiv.sum_comp ς fun i => ∑ μ, x i μ ^ 2]
theorem tupleNorm_timeReflectTuple (x : PointTuple n) :
    tupleNorm (timeReflectTuple x) = tupleNorm x := by
  simp [tupleNorm, timeReflectTuple, timeReflect, Fin.sum_univ_four]
theorem affineControl_perm (ς : Equiv.Perm (Fin n)) :
    AffineControl (ContinuousLinearMap.id ℝ ℂ) 1 0 ς 1 1 where
  norm_T := fun _ => rfl
  entries := fun μ => by
    rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [hν]) (by simp)]
    simp
  one_le := le_rfl
  pos := one_pos
  weight := fun x => by rw [tupleNorm_affineArgs_perm, one_mul]
theorem affineControl_timeReflection :
    AffineControl (Complex.conjCLE : ℂ →L[ℝ] ℂ) timeReflection.mat 0
      (1 : Equiv.Perm (Fin n)) 1 1 where
  norm_T := fun z => by simp
  entries := fun μ => by
    fin_cases μ <;> simp [timeReflection, Matrix.diagonal_apply, Fin.sum_univ_four]
  one_le := le_rfl
  pos := one_pos
  weight := fun x => by rw [affineArgs_timeReflection, tupleNorm_timeReflectTuple, one_mul]
theorem euclidNormVec_sq (u : Fin 4 → ℝ) : TorusMetric.euclidNormVec u ^ 2 = ∑ μ, u μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem sum_sq_mat_mulVec (r : RigidMotion) (u : Fin 4 → ℝ) :
    ∑ μ, r.mat.mulVec u μ ^ 2 = ∑ μ, u μ ^ 2 := by
  have h₁ : r.mat * r.mat.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 r.mat_mem
  have h₂ : r.mat.transpose * r.mat = 1 := mul_eq_one_comm.1 h₁
  have h : r.mat.mulVec u ⬝ᵥ r.mat.mulVec u = u ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h₂,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h
theorem sum_abs_mat_inv_le (r : RigidMotion) (μ : Fin 4) : ∑ ν, |r.mat⁻¹ ν μ| ≤ 4 := by
  have h₁ : r.mat * r.mat.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 r.mat_mem
  have hinv : r.mat⁻¹ = r.mat.transpose := Matrix.inv_eq_right_inv h₁
  have hrow : ∑ ν, r.mat μ ν ^ 2 = 1 := by
    have := congrFun (congrFun h₁ μ) μ
    simpa [Matrix.mul_apply, sq] using this
  have hone : ∀ ν, |r.mat⁻¹ ν μ| ≤ 1 := by
    intro ν
    rw [hinv, Matrix.transpose_apply, ← sq_le_one_iff_abs_le_one]
    exact hrow ▸ Finset.single_le_sum (f := fun ν => r.mat μ ν ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ ν)
  calc ∑ ν, |r.mat⁻¹ ν μ| ≤ ∑ _ν : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun ν _ => hone ν
    _ = 4 := by simp
theorem affineControl_rigid (r : RigidMotion) :
    AffineControl (ContinuousLinearMap.id ℝ ℂ) r.mat⁻¹ (-(r.mat⁻¹.mulVec r.shift))
      (1 : Equiv.Perm (Fin n)) 4
      (2 * (1 + (n : ℝ) * TorusMetric.euclidNormVec r.shift ^ 2)) where
  norm_T := fun _ => rfl
  entries := sum_abs_mat_inv_le r
  one_le := by norm_num
  pos := by positivity
  weight := fun x => by
    have hi : ∀ i, x i =
        r.mat.mulVec (affineArgs r.mat⁻¹ (-(r.mat⁻¹.mulVec r.shift)) 1 x i) + r.shift := by
      intro i
      rw [affineArgs_rigid]
      exact (r.toFun_invFun (x i)).symm
    generalize affineArgs r.mat⁻¹ (-(r.mat⁻¹.mulVec r.shift)) 1 x = y at hi ⊢
    have hb : ∀ i, TorusMetric.euclidNormVec (x i) ^ 2 ≤
        2 * TorusMetric.euclidNormVec (y i) ^ 2 + 2 * TorusMetric.euclidNormVec r.shift ^ 2 := by
      intro i
      simp only [euclidNormVec_sq]
      rw [hi i]
      calc ∑ μ, (r.mat.mulVec (y i) + r.shift) μ ^ 2
          ≤ ∑ μ, (2 * r.mat.mulVec (y i) μ ^ 2 + 2 * r.shift μ ^ 2) := by
            refine Finset.sum_le_sum fun μ _ => ?_
            simp only [Pi.add_apply]
            nlinarith [sq_nonneg (r.mat.mulVec (y i) μ - r.shift μ)]
        _ = 2 * ∑ μ, y i μ ^ 2 + 2 * ∑ μ, r.shift μ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sq_mat_mulVec]
    have hs : tupleNorm x ^ 2 ≤
        2 * tupleNorm y ^ 2 + 2 * ((n : ℝ) * TorusMetric.euclidNormVec r.shift ^ 2) := by
      rw [tupleNorm_sq, tupleNorm_sq]
      calc ∑ i, TorusMetric.euclidNormVec (x i) ^ 2
          ≤ ∑ i, (2 * TorusMetric.euclidNormVec (y i) ^ 2 +
              2 * TorusMetric.euclidNormVec r.shift ^ 2) := Finset.sum_le_sum fun i _ => hb i
        _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp
            ring
    have h0 : 0 ≤ (n : ℝ) * TorusMetric.euclidNormVec r.shift ^ 2 * tupleNorm y ^ 2 := by
      positivity
    nlinarith
theorem contDiff_permuteArgs {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (ς : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (permuteArgs ς φ) := by
  rw [permuteArgs_eq_comp]
  exact contDiff_comp_affineArgs hφ _ _ _ _
theorem contDiff_reflectConj {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (reflectConj φ) := by
  rw [reflectConj_eq_comp]
  exact contDiff_comp_affineArgs hφ _ _ _ _
theorem weightedSeminorm_permuteArgs_le {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (ς : Equiv.Perm (Fin n)) (k : ℕ) :
    weightedSeminorm k (permuteArgs ς φ) ≤ weightedSeminorm k φ := by
  rw [permuteArgs_eq_comp]
  simpa using weightedSeminorm_comp_le hφ (affineControl_perm ς) k
theorem weightedSeminorm_reflectConj_le {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    weightedSeminorm k (reflectConj φ) ≤ weightedSeminorm k φ := by
  rw [reflectConj_eq_comp]
  simpa using weightedSeminorm_comp_le hφ affineControl_timeReflection k
theorem permuteArgs_symm (ς : Equiv.Perm (Fin n)) (φ : PointTuple n → ℂ) :
    permuteArgs ς.symm (permuteArgs ς φ) = φ := by
  funext x
  simp [permuteArgs]
theorem timeReflectTuple_timeReflectTuple (x : PointTuple n) :
    timeReflectTuple (timeReflectTuple x) = x :=
  funext fun i => timeReflect_timeReflect (x i)
theorem reflectConj_reflectConj (φ : PointTuple n → ℂ) : reflectConj (reflectConj φ) = φ := by
  funext x
  simp [reflectConj, timeReflectTuple_timeReflectTuple]
theorem seminormBounds (k : ℕ) (ς : Equiv.Perm (Fin n)) (r : RigidMotion) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : SeminormBounds n k ς r φ := by
  refine ⟨le_antisymm (weightedSeminorm_permuteArgs_le hφ ς k) ?_,
    le_antisymm (weightedSeminorm_reflectConj_le hφ k) ?_, ?_⟩
  · have h := weightedSeminorm_permuteArgs_le (contDiff_permuteArgs hφ ς) ς.symm k
    rwa [permuteArgs_symm] at h
  · have h := weightedSeminorm_reflectConj_le (contDiff_reflectConj hφ) k
    rwa [reflectConj_reflectConj] at h
  · rw [actOnFun_eq_comp]
    exact weightedSeminorm_comp_le hφ (affineControl_rigid r) k
theorem preservesClasses (ς : Equiv.Perm (Fin n)) (r : RigidMotion) {φ : PointTuple n → ℂ}
    (hφ : φ ∈ schwartzSet n) : PreservesClasses n ς r φ := by
  refine ⟨?_, ?_, ?_, fun hf => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [permuteArgs_eq_comp]
    exact comp_mem_schwartzSet hφ (affineControl_perm ς)
  · rw [actOnFun_eq_comp]
    exact comp_mem_schwartzSet hφ (affineControl_rigid r)
  · rw [reflectConj_eq_comp]
    exact comp_mem_schwartzSet hφ affineControl_timeReflection
  · rw [permuteArgs_eq_comp]
    exact comp_mem_flatSchwartzSet hf (affineControl_perm ς)
  · rw [actOnFun_eq_comp]
    exact comp_mem_flatSchwartzSet hf (affineControl_rigid r)
  · rw [reflectConj_eq_comp]
    exact comp_mem_flatSchwartzSet hf affineControl_timeReflection
  · funext x
    show conj (φ (timeReflectTuple x)) = conj (φ fun i => timeReflection.invFun (x i))
    rw [timeReflection_invFun]
    rfl
theorem isLinearOnSchwartz (ς : Equiv.Perm (Fin n)) (r : RigidMotion) :
    IsLinearOnSchwartz n ς r := by
  intro φ _ φ' _ c c'
  refine ⟨rfl, rfl, ?_⟩
  funext x
  simp [reflectConj]
theorem vanishesAt_reflectConj {ψ : PointTuple n → ℂ} (hψ : ContDiff ℝ ∞ ψ) {x : PointTuple n}
    (h : VanishesToInfiniteOrderAt ψ (timeReflectTuple x)) :
    VanishesToInfiniteOrderAt (reflectConj ψ) x := by
  refine ⟨contDiff_reflectConj hψ, ?_, fun α => ?_⟩
  · simp [reflectConj, h.2.1]
  · rw [reflectConj_eq_comp]
    refine multiDeriv_comp_eq_zero hψ affineControl_timeReflection α x fun γ => ?_
    rw [affineArgs_timeReflection]
    exact h.2.2 γ
theorem injective_of_timeReflectTuple {x : PointTuple n}
    (h : Function.Injective (timeReflectTuple x)) : Function.Injective x :=
  fun a b hab => h (by simp [timeReflectTuple, hab])
theorem vanishesOff_iff_reflectConj (hn : 0 < n) (hFirst : TestSpaces.Elementary.BasicProperties)
    {φ : PointTuple n → ℂ} (hφ : φ ∈ schwartzSet n) :
    VanishesToInfiniteOrderOff φ (positiveTimeLocus n) ↔
      VanishesToInfiniteOrderOff (reflectConj φ) (negativeTimeLocus n) := by
  have hp : IsOpen (positiveTimeLocus n) := (hFirst n hn).2.1.2.1
  have hm : IsOpen (negativeTimeLocus n) := (hFirst n hn).2.1.2.2.1
  have mem₁ : ∀ x, x ∉ negativeTimeLocus n → timeReflectTuple x ∉ positiveTimeLocus n :=
    fun x hx h => hx ⟨injective_of_timeReflectTuple h.1, fun i => by
      simpa [timeCoord, timeReflectTuple, timeReflect] using h.2 i⟩
  have mem₂ : ∀ x, x ∉ positiveTimeLocus n → timeReflectTuple x ∉ negativeTimeLocus n :=
    fun x hx h => hx ⟨injective_of_timeReflectTuple h.1, fun i => by
      simpa [timeCoord, timeReflectTuple, timeReflect] using h.2 i⟩
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨contDiff_reflectConj hφ.1, hm, fun x hx =>
      vanishesAt_reflectConj hφ.1 (h _ (mem₁ x hx))⟩
  · rintro ⟨hs, _, h⟩
    refine ⟨hφ.1, hp, fun x hx => ?_⟩
    have := vanishesAt_reflectConj hs (h _ (mem₂ x hx))
    rwa [reflectConj_reflectConj] at this
theorem contDiff_invFun (r : RigidMotion) {m : WithTop ℕ∞} : ContDiff ℝ m r.invFun :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin r.mat⁻¹)).contDiff.comp
    (contDiff_id.sub contDiff_const)
theorem continuous_toFun (r : RigidMotion) : Continuous r.toFun :=
  ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin r.mat)).continuous).add continuous_const
def invHomeomorph (r : RigidMotion) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := r.invFun
  invFun := r.toFun
  left_inv := r.toFun_invFun
  right_inv := r.invFun_toFun
  continuous_toFun := (contDiff_invFun r (m := 0)).continuous
  continuous_invFun := continuous_toFun r
theorem tsupport_actOnPointFun (r : RigidMotion) (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (actOnPointFun r f) = r.invFun ⁻¹' tsupport f := by
  have h := (invHomeomorph r).preimage_closure (Function.support f)
  have hs : Function.support (actOnPointFun r f) =
      (invHomeomorph r) ⁻¹' Function.support f := rfl
  unfold tsupport
  rw [hs, ← h]
  rfl
theorem actOnPointFun_mem_c1 (r : RigidMotion) {O : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ (c1CompactSupp O : Set ((Fin 4 → ℝ) → ℝ))) :
    actOnPointFun r f ∈ (c1CompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)) :=
  ⟨hf.1.comp (contDiff_invFun r), hf.2.1.comp_homeomorph (invHomeomorph r),
    Set.subset_univ _⟩
theorem actOnPointFun_mem_smooth (r : RigidMotion) {O : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ (smoothCompactSupp O : Set ((Fin 4 → ℝ) → ℝ))) :
    actOnPointFun r f ∈ (smoothCompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)) :=
  ⟨hf.1.comp (contDiff_invFun r), hf.2.1.comp_homeomorph (invHomeomorph r),
    Set.subset_univ _⟩
theorem actOnTuple_mem (r : RigidMotion) {O : Set (Fin 4 → ℝ)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples O n) :
    actOnTuple r f ∈ disjointSupportTuples Set.univ n := by
  refine ⟨fun i => actOnPointFun_mem_c1 r (hf.1 i), fun i j hij => ?_⟩
  show Disjoint (tsupport (actOnPointFun r (f i))) (tsupport (actOnPointFun r (f j)))
  rw [tsupport_actOnPointFun, tsupport_actOnPointFun]
  exact (hf.2 hij).preimage _
theorem permuted_mem_disjointSupportTuples (ς : Equiv.Perm (Fin n)) {O : Set (Fin 4 → ℝ)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples O n) :
    (fun j => f (ς.symm j)) ∈ disjointSupportTuples O n :=
  ⟨fun _ => hf.1 _, fun _ _ hij => hf.2 fun h => hij (ς.symm.injective h)⟩
theorem reflectConj_tensorProd (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    reflectConj (tensorProd (complexify f)) = tensorProd (complexify (reflectTuple f)) := by
  funext x
  simp [reflectConj, tensorProd, complexify, map_prod, reflectTuple, reflectFun_eq,
    timeReflectTuple]
theorem actsOnTensorProd (ς : Equiv.Perm (Fin n)) (r : RigidMotion)
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples Set.univ n)
    (hs : HasSmoothComponents Set.univ f) : ActsOnTensorProd n ς r f := by
  refine ⟨rfl, ?_, reflectConj_tensorProd f, actOnTuple_mem r hf,
    fun i => actOnPointFun_mem_smooth r (hs i), permuted_mem_disjointSupportTuples ς hf,
    fun _ => hs _, actOnTuple_mem timeReflection hf,
    fun i => actOnPointFun_mem_smooth timeReflection (hs i)⟩
  funext x
  show ∏ i, complexify f i (x (ς i)) = ∏ j, complexify (fun j => f (ς.symm j)) j (x j)
  rw [← Equiv.prod_comp ς fun j => complexify (fun j => f (ς.symm j)) j (x j)]
  simp [complexify]
variable {q q' : ℕ}
theorem valToFun_tupleTensor (f : Fin q → (Fin 4 → ℝ) → ℂ) :
    valToFun (tupleTensor f) = tensorProd f := by
  cases q with
  | zero =>
    funext x
    simp [valToFun, tupleTensor, tensorProd]
  | succ q => rfl
theorem valToFun_reflectConjVal (F : TensorVal ℂ q) :
    valToFun (reflectConjVal F) = reflectConj (valToFun F) := by
  cases q <;> rfl
theorem valToFun_injective : Function.Injective (valToFun (q := q)) := by
  cases q with
  | zero => exact fun a b h => congrFun h default
  | succ q => exact fun a b h => h
theorem complexify_concatTuple (X : Fin q → (Fin 4 → ℝ) → ℝ)
    (Y : Fin q' → (Fin 4 → ℝ) → ℝ) :
    complexify (concatTuple X Y) = concatTuple (complexify X) (complexify Y) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · funext u
    simp [complexify, concatTuple_castAdd]
  · funext u
    simp [complexify, concatTuple_natAdd]
theorem tensorProd_concatTuple (X : Fin q → (Fin 4 → ℝ) → ℂ) (Y : Fin q' → (Fin 4 → ℝ) → ℂ)
    (z : PointTuple (q + q')) :
    tensorProd (concatTuple X Y) z = tensorProd X (leftPart z) * tensorProd Y (rightPart z) := by
  simp [tensorProd, Fin.prod_univ_add, concatTuple, leftPart, rightPart]
theorem tupleTensor_across (X : Fin q → (Fin 4 → ℝ) → ℝ) (Y : Fin q' → (Fin 4 → ℝ) → ℝ) :
    tupleTensor (complexify (concatTuple (reflectTuple X) Y)) =
      tensorVal (reflectConjVal (tupleTensor (complexify X))) (tupleTensor (complexify Y)) := by
  apply valToFun_injective
  rw [tensorVal, valToFun_funToVal, valToFun_reflectConjVal,
    valToFun_tupleTensor, valToFun_tupleTensor, valToFun_tupleTensor,
    reflectConj_tensorProd, complexify_concatTuple]
  funext z
  exact tensorProd_concatTuple _ _ z
theorem disjoint_tsupport_reflectFun {f h : (Fin 4 → ℝ) → ℝ} (hf : tsupport f ⊆ upperHalfSpace)
    (hh : tsupport h ⊆ upperHalfSpace) :
    Disjoint (tsupport (reflectFun f)) (tsupport h) := by
  rw [Set.disjoint_left]
  intro u hu hv
  have h₁ : timeReflection.invFun u ∈ tsupport f := by
    have e := tsupport_actOnPointFun timeReflection f
    have hu' : u ∈ tsupport (actOnPointFun timeReflection f) := hu
    rw [e] at hu'
    exact hu'
  have h₂ := hf h₁
  rw [timeReflection_invFun] at h₂
  have h₃ := hh hv
  simp only [upperHalfSpace, Set.mem_ofPred_eq] at h₂ h₃
  simp [timeReflect] at h₂
  linarith
theorem concatTuple_mem {X : Fin q → (Fin 4 → ℝ) → ℝ} {Y : Fin q' → (Fin 4 → ℝ) → ℝ}
    (hX : X ∈ disjointSupportTuples upperHalfSpace q)
    (hY : Y ∈ disjointSupportTuples upperHalfSpace q') :
    concatTuple (reflectTuple X) Y ∈ disjointSupportTuples Set.univ (q + q') := by
  have hX' : reflectTuple X ∈ disjointSupportTuples Set.univ q := actOnTuple_mem timeReflection hX
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · rw [concatTuple_castAdd]
      exact hX'.1 i
    · rw [concatTuple_natAdd]
      exact ⟨(hY.1 j).1, (hY.1 j).2.1, Set.subset_univ _⟩
  · induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left i' =>
        rw [concatTuple_castAdd, concatTuple_castAdd]
        exact hX'.2 fun h => hab (by rw [h])
      | right j =>
        rw [concatTuple_castAdd, concatTuple_natAdd]
        exact disjoint_tsupport_reflectFun (hX.1 i).2.2 (hY.1 j).2.2
    | right j =>
      induction b using Fin.addCases with
      | left i =>
        rw [concatTuple_castAdd, concatTuple_natAdd]
        exact (disjoint_tsupport_reflectFun (hX.1 i).2.2 (hY.1 j).2.2).symm
      | right j' =>
        rw [concatTuple_natAdd, concatTuple_natAdd]
        exact hY.2 fun h => hab (by rw [h])
theorem concatTuple_smooth {X : Fin q → (Fin 4 → ℝ) → ℝ} {Y : Fin q' → (Fin 4 → ℝ) → ℝ}
    (hX : HasSmoothComponents upperHalfSpace X) (hY : HasSmoothComponents upperHalfSpace Y) :
    HasSmoothComponents Set.univ (concatTuple (reflectTuple X) Y) := by
  intro a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · rw [concatTuple_castAdd]
    exact actOnPointFun_mem_smooth timeReflection (hX i)
  · rw [concatTuple_natAdd]
    exact ⟨(hY j).1, (hY j).2.1, Set.subset_univ _⟩
theorem operationsStatement_holds (hFirst : TestSpaces.Elementary.BasicProperties) :
    OperationsStatement := by
  refine ⟨fun n k hn _ ς r => ⟨isLinearOnSchwartz ς r, fun φ hφ =>
    ⟨preservesClasses ς r hφ, seminormBounds k ς r hφ.1, vanishesOff_iff_reflectConj hn hFirst hφ⟩,
    fun r' hr => ?_, fun f hf hs => actsOnTensorProd ς r hf hs⟩,
    fun q q' X Y hX hXs hY hYs =>
      ⟨concatTuple_mem hX hY, concatTuple_smooth hXs hYs, tupleTensor_across X Y⟩⟩
  simp [motionBound, hr]
end YangMills.Construction.TestFunctionOps
