import YangMills.Construction.ConfigurationSpace.IterDirDerivLeibniz
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
namespace DirDerivLeibniz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem dirDeriv_eq_fderiv (v : V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    dirDeriv v f = fun x => fderiv ℝ f x v :=
  funext fun x => ((hf.differentiable (by simp)) x).lineDeriv_eq_fderiv
theorem dirDeriv_of_hasFDerivAt (v : V) {f : V → ℂ} {L : V →L[ℝ] ℂ} {x : V}
    (h : HasFDerivAt f L x) : dirDeriv v f x = L v :=
  (h.hasLineDerivAt v).lineDeriv
theorem contDiff_dirDeriv (v : V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirDeriv v f) := by
  rw [dirDeriv_eq_fderiv v hf]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_iterate_dirDeriv (v : V) (k : ℕ) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ ((dirDeriv v)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ n hn =>
    rw [Function.iterate_succ_apply']
    exact contDiff_dirDeriv v hn
theorem dirDeriv_mul (v : V) {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    dirDeriv v (fun y => f y * g y) =
      fun x => dirDeriv v f x * g x + f x * dirDeriv v g x := by
  funext x
  show dirDeriv v (fun y => f y * g y) x = dirDeriv v f x * g x + f x * dirDeriv v g x
  have Df := (hf.differentiable (by simp) x).hasFDerivAt
  have Dg := (hg.differentiable (by simp) x).hasFDerivAt
  have Dfg : dirDeriv v (fun y => f y * g y) x = _ := dirDeriv_of_hasFDerivAt v (Df.mul Dg)
  rw [Dfg, dirDeriv_of_hasFDerivAt v Df, dirDeriv_of_hasFDerivAt v Dg, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply, smul_eq_mul, smul_eq_mul]
  ring
theorem dirDeriv_sum (v : V) {J : Type} (s : Finset J) (c : J → ℂ) {F : J → V → ℂ}
    (hF : ∀ j ∈ s, ContDiff ℝ ∞ (F j)) :
    dirDeriv v (fun y => ∑ j ∈ s, c j * F j y) =
      fun x => ∑ j ∈ s, c j * dirDeriv v (F j) x := by
  funext x
  show dirDeriv v (fun y => ∑ j ∈ s, c j * F j y) x = ∑ j ∈ s, c j * dirDeriv v (F j) x
  have DF : ∀ j ∈ s, HasFDerivAt (F j) (fderiv ℝ (F j) x) x := fun j hj =>
    ((hF j hj).differentiable (by simp) x).hasFDerivAt
  have Dsum : HasFDerivAt (fun y => ∑ j ∈ s, c j * F j y)
      (∑ j ∈ s, c j • fderiv ℝ (F j) x) x :=
    HasFDerivAt.fun_sum fun j hj => (DF j hj).const_mul (c j)
  rw [dirDeriv_of_hasFDerivAt v Dsum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [_root_.smul_apply, smul_eq_mul, dirDeriv_of_hasFDerivAt v (DF j hj)]
theorem iterate_dirDeriv_sum (v : V) {J : Type} (s : Finset J) (c : J → ℂ) (k : ℕ)
    {F : J → V → ℂ} (hF : ∀ j ∈ s, ContDiff ℝ ∞ (F j)) :
    (dirDeriv v)^[k] (fun y => ∑ j ∈ s, c j * F j y) =
      fun x => ∑ j ∈ s, c j * (dirDeriv v)^[k] (F j) x := by
  induction k generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, dirDeriv_sum v s c hF]
    exact ih fun j hj => contDiff_dirDeriv v (hF j hj)
theorem iterate_dirDeriv_mul_antidiagonal (v : V) (k : ℕ) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (dirDeriv v)^[k] (fun y => f y * g y) =
      fun x => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (k.choose p.1 : ℂ) *
        ((dirDeriv v)^[p.1] f x * (dirDeriv v)^[p.2] g x) := by
  induction k with
  | zero =>
    funext x
    simp
  | succ n ih =>
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, ContDiff ℝ ∞
        (fun x => (dirDeriv v)^[p.1] f x * (dirDeriv v)^[p.2] g x) := fun p _ =>
      (contDiff_iterate_dirDeriv v p.1 hf).mul (contDiff_iterate_dirDeriv v p.2 hg)
    rw [Function.iterate_succ_apply', ih,
      dirDeriv_sum v _ (fun p => (n.choose p.1 : ℂ)) hterm]
    funext x
    rw [Finset.sum_antidiagonal_choose_succ_mul
      (fun a b => (dirDeriv v)^[a] f x * (dirDeriv v)^[b] g x) n, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hp).symm,
      dirDeriv_mul v (contDiff_iterate_dirDeriv v p.1 hf) (contDiff_iterate_dirDeriv v p.2 hg)]
    simp only [Function.iterate_succ_apply']
    ring
theorem iterate_dirDeriv_mul (v : V) (k : ℕ) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : V) :
    (dirDeriv v)^[k] (fun y => f y * g y) x =
      ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) *
        ((dirDeriv v)^[m] f x * (dirDeriv v)^[k - m] g x) := by
  have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun p : ℕ × ℕ => (k.choose p.1 : ℂ) * ((dirDeriv v)^[p.1] f x * (dirDeriv v)^[p.2] g x)) k
  rw [iterate_dirDeriv_mul_antidiagonal v k hf hg]
  exact h
variable {I : Type} [Fintype I] [LinearOrder I]
def listDirDeriv (e : I → V) (l : List I) (α : MultiIdx I) (f : V → ℂ) : V → ℂ :=
  l.foldr (fun ι g => (dirDeriv (e ι))^[α ι] g) f
omit [Fintype I] [LinearOrder I] in
theorem listDirDeriv_cons (e : I → V) (a : I) (l : List I) (α : MultiIdx I) (f : V → ℂ) :
    listDirDeriv e (a :: l) α f = (dirDeriv (e a))^[α a] (listDirDeriv e l α f) := rfl
omit [Fintype I] [LinearOrder I] in
theorem listDirDeriv_congr (e : I → V) (l : List I) {α β : MultiIdx I} (f : V → ℂ)
    (h : ∀ ι ∈ l, α ι = β ι) : listDirDeriv e l α f = listDirDeriv e l β f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [listDirDeriv_cons, listDirDeriv_cons, h a (by simp),
      ih fun ι hι => h ι (List.mem_cons_of_mem a hι)]
omit [Fintype I] [LinearOrder I] in
theorem contDiff_listDirDeriv (e : I → V) (l : List I) (α : MultiIdx I) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (listDirDeriv e l α f) := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact contDiff_iterate_dirDeriv (e a) (α a) ih
def listMultiIdxBox (l : List I) (α : MultiIdx I) : Finset (MultiIdx I) :=
  Fintype.piFinset fun ι => if ι ∈ l then Finset.range (α ι + 1) else {0}
theorem mem_listMultiIdxBox {l : List I} {α γ : MultiIdx I} :
    γ ∈ listMultiIdxBox l α ↔ ∀ ι, (ι ∈ l → γ ι ≤ α ι) ∧ (ι ∉ l → γ ι = 0) := by
  rw [listMultiIdxBox, Fintype.mem_piFinset]
  apply forall_congr'
  intro ι
  split_ifs with hι
  · simp [hι]
  · simp [hι]
theorem update_mem_listMultiIdxBox_cons {a : I} {l : List I} {α γ : MultiIdx I} {m : ℕ}
    (hγ : γ ∈ listMultiIdxBox l α) (hm : m ≤ α a) :
    Function.update γ a m ∈ listMultiIdxBox (a :: l) α := by
  rw [mem_listMultiIdxBox] at hγ ⊢
  intro ι
  rcases eq_or_ne ι a with rfl | hne
  · simp [hm]
  · rw [Function.update_of_ne hne]
    simp only [List.mem_cons, hne, false_or]
    exact hγ ι
theorem update_zero_mem_listMultiIdxBox {a : I} {l : List I} (ha : a ∉ l) {α δ : MultiIdx I}
    (hδ : δ ∈ listMultiIdxBox (a :: l) α) :
    Function.update δ a 0 ∈ listMultiIdxBox l α := by
  rw [mem_listMultiIdxBox] at hδ ⊢
  intro ι
  rcases eq_or_ne ι a with rfl | hne
  · simp [ha]
  · rw [Function.update_of_ne hne]
    have hι := hδ ι
    simp only [List.mem_cons, hne, false_or] at hι
    exact hι
theorem le_of_mem_listMultiIdxBox_cons {a : I} {l : List I} {α δ : MultiIdx I}
    (hδ : δ ∈ listMultiIdxBox (a :: l) α) : δ a ≤ α a :=
  (mem_listMultiIdxBox.mp hδ a).1 List.mem_cons_self
theorem choose_update (α γ : MultiIdx I) (a : I) (m : ℕ) (h : γ a = 0) :
    MultiIdx.choose α (Function.update γ a m) =
      (α a).choose m * MultiIdx.choose α γ := by
  unfold MultiIdx.choose
  have hrest : ∏ ι ∈ Finset.univ.erase a, (α ι).choose (Function.update γ a m ι) =
      ∏ ι ∈ Finset.univ.erase a, (α ι).choose (γ ι) :=
    Finset.prod_congr rfl fun ι hι => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hι)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), hrest, Function.update_self,
    ← Finset.prod_erase_mul _ (fun ι => (α ι).choose (γ ι)) (Finset.mem_univ a), h,
    Nat.choose_zero_right, mul_one, mul_comm]
theorem listDirDeriv_mul (e : I → V) (l : List I) (hl : l.Nodup) (α : MultiIdx I)
    {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    listDirDeriv e l α (fun y => f y * g y) =
      fun x => ∑ γ ∈ listMultiIdxBox l α, (MultiIdx.choose α γ : ℂ) *
        (listDirDeriv e l γ f x * listDirDeriv e l (α - γ) g x) := by
  induction l with
  | nil =>
    have h0 : listMultiIdxBox ([] : List I) α = {0} := by
      ext γ
      simp [mem_listMultiIdxBox, funext_iff]
    funext x
    simp [h0, listDirDeriv, MultiIdx.choose]
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have hsm : ∀ γ ∈ listMultiIdxBox l α, ContDiff ℝ ∞
        (fun x => listDirDeriv e l γ f x * listDirDeriv e l (α - γ) g x) := fun γ _ =>
      (contDiff_listDirDeriv e l γ hf).mul (contDiff_listDirDeriv e l (α - γ) hg)
    rw [listDirDeriv_cons, ih hl',
      iterate_dirDeriv_sum (e a) _ (fun γ => (MultiIdx.choose α γ : ℂ)) _ hsm]
    funext x
    simp only [iterate_dirDeriv_mul (e a) (α a) (contDiff_listDirDeriv e l _ hf)
      (contDiff_listDirDeriv e l _ hg) x, Finset.mul_sum]
    rw [← Finset.sum_product', eq_comm]
    refine Finset.sum_nbij' (fun δ => (Function.update δ a 0, δ a))
      (fun p => Function.update p.1 a p.2) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      exact Finset.mem_product.mpr ⟨update_zero_mem_listMultiIdxBox ha hδ,
        Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_mem_listMultiIdxBox_cons hδ))⟩
    · rintro ⟨γ, m⟩ hp
      obtain ⟨hγ, hm⟩ := Finset.mem_product.mp hp
      exact update_mem_listMultiIdxBox_cons hγ (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
    · intro δ _
      simp
    · rintro ⟨γ, m⟩ hp
      have h0 : γ a = 0 := (mem_listMultiIdxBox.mp (Finset.mem_product.mp hp).1 a).2 ha
      refine Prod.ext ?_ ?_
      · simp only [Function.update_idem]
        rw [← h0, Function.update_eq_self]
      · simp
    · intro δ _
      have hd : Function.update (Function.update δ a 0) a (δ a) = δ := by simp
      have hc := choose_update α (Function.update δ a 0) a (δ a) (Function.update_self a 0 δ)
      rw [hd] at hc
      have hf' : listDirDeriv e l δ f = listDirDeriv e l (Function.update δ a 0) f :=
        listDirDeriv_congr e l f fun ι hι =>
          (Function.update_of_ne (fun h : ι = a => ha (h ▸ hι)) 0 δ).symm
      have hg' : listDirDeriv e l (α - δ) g =
          listDirDeriv e l (α - Function.update δ a 0) g :=
        listDirDeriv_congr e l g fun ι hι => by
          simp [Function.update_of_ne (fun h : ι = a => ha (h ▸ hι))]
      simp only [listDirDeriv_cons, Pi.sub_apply, hc, hf', hg']
      push_cast
      ring
end DirDerivLeibniz
open DirDerivLeibniz in
theorem iterDirDerivLeibniz_holds : IterDirDerivLeibniz := by
  intro V _ _ I _ _ e γ f hf g hg x
  have hbox : listMultiIdxBox ((Finset.univ : Finset I).sort (· ≤ ·)) γ =
      Fintype.piFinset fun ι => Finset.range (γ ι + 1) := by
    simp [listMultiIdxBox]
  have key := congrFun (listDirDeriv_mul e ((Finset.univ : Finset I).sort (· ≤ ·))
    (Finset.sort_nodup _ _) γ hf hg) x
  rw [hbox] at key
  refine key.trans (Finset.sum_congr rfl fun δ _ => ?_)
  exact (mul_assoc _ _ _).symm
end YangMills.Construction.ConfigurationSpace
end
