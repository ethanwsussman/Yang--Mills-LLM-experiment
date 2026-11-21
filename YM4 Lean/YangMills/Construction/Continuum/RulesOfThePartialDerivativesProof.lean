import YangMills.Construction.Continuum.FirstFactsOnTheTestSpacesProof
import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.TestSpaces.DerivRules
variable {n : ℕ}
section Coordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
def unitCoordVec (a : Fin n × Fin 4) : PointTuple n := Pi.single a.1 (Pi.single a.2 1)
def pdAt (a : Fin n × Fin 4) (g : PointTuple n → E) : PointTuple n → E :=
  coordDeriv a.1 a.2 g
theorem differentiable_of_contDiff_top {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ g :=
  hg.differentiable (by simp)
theorem pdAt_eq_fderiv {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4)
    (x : PointTuple n) : pdAt a g x = fderiv ℝ g x (unitCoordVec a) :=
  (differentiable_of_contDiff_top hg x).lineDeriv_eq_fderiv
theorem contDiff_pdAt {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) (a : Fin n × Fin 4) :
    ContDiff ℝ ∞ (pdAt a g) := by
  have hfun : pdAt a g = fun x => fderiv ℝ g x (unitCoordVec a) :=
    funext (pdAt_eq_fderiv hg a)
  rw [hfun]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem pdAt_comm {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) (a b : Fin n × Fin 4) :
    pdAt a (pdAt b g) = pdAt b (pdAt a g) := by
  funext x
  rw [pdAt_eq_fderiv (contDiff_pdAt hg b), pdAt_eq_fderiv (contDiff_pdAt hg a)]
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have key : ∀ (c : Fin n × Fin 4) (d : PointTuple n),
      fderiv ℝ (pdAt c g) x d = fderiv ℝ (fderiv ℝ g) x d (unitCoordVec c) := by
    intro c d
    have hfun : pdAt c g = fun y => fderiv ℝ g y (unitCoordVec c) :=
      funext (pdAt_eq_fderiv hg c)
    rw [hfun, fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)) _ _
theorem pdAt_add {g h : PointTuple n → E} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin n × Fin 4) : pdAt a (g + h) = pdAt a g + pdAt a h := by
  funext x
  have hs : ContDiff ℝ ∞ (g + h) := hg.add hh
  rw [Pi.add_apply, pdAt_eq_fderiv hs, pdAt_eq_fderiv hg, pdAt_eq_fderiv hh,
    fderiv_add (differentiable_of_contDiff_top hg x) (differentiable_of_contDiff_top hh x)]
  rfl
theorem pdAt_comp_clm (T : E →L[ℝ] E') {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g)
    (a : Fin n × Fin 4) : pdAt a (T ∘ g) = T ∘ pdAt a g := by
  funext x
  rw [pdAt_eq_fderiv (T.contDiff.comp hg), Function.comp_apply, pdAt_eq_fderiv hg,
    T.hasFDerivAt.comp x (differentiable_of_contDiff_top hg x).hasFDerivAt |>.fderiv]
  rfl
theorem pdAt_eq_zero_on {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) {U : Set (PointTuple n)}
    (hU : IsOpen U) (h0 : ∀ x ∈ U, g x = 0) (a : Fin n × Fin 4) :
    ∀ x ∈ U, pdAt a g x = 0 := by
  intro x hx
  have hev : g =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy using h0 y hy
  rw [pdAt_eq_fderiv hg, hev.fderiv_eq]
  simp
theorem pdAt_finset_sum {ι : Type*} (s : Finset ι) (h : ι → PointTuple n → E)
    (hh : ∀ b ∈ s, ContDiff ℝ ∞ (h b)) (a : Fin n × Fin 4) :
    pdAt a (fun x => ∑ b ∈ s, h b x) = fun x => ∑ b ∈ s, pdAt a (h b) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext x
    simpa using pdAt_eq_zero_on (g := fun _ : PointTuple n => (0 : E)) contDiff_const isOpen_univ
      (fun _ _ => rfl) a x (Set.mem_univ x)
  | insert b s hb ih =>
    have hs : ContDiff ℝ ∞ (fun x => ∑ c ∈ s, h c x) :=
      ContDiff.sum fun c hc => hh c (Finset.mem_insert_of_mem hc)
    have hb' := hh b (Finset.mem_insert_self b s)
    have e : (fun x => ∑ c ∈ insert b s, h c x) = h b + fun x => ∑ c ∈ s, h c x := by
      funext x
      simp [Finset.sum_insert hb]
    rw [e, pdAt_add hb' hs, ih fun c hc => hh c (Finset.mem_insert_of_mem hc)]
    funext x
    simp [Finset.sum_insert hb]
def derivAlong (w : List (Fin n × Fin 4)) (g : PointTuple n → E) : PointTuple n → E :=
  w.foldl (fun h a => pdAt a h) g
theorem derivAlong_cons (a : Fin n × Fin 4) (w : List (Fin n × Fin 4)) (g : PointTuple n → E) :
    derivAlong (a :: w) g = derivAlong w (pdAt a g) := rfl
theorem derivAlong_append (v w : List (Fin n × Fin 4)) (g : PointTuple n → E) :
    derivAlong (v ++ w) g = derivAlong w (derivAlong v g) := by
  simp [derivAlong, List.foldl_append]
theorem derivAlong_perm {w w' : List (Fin n × Fin 4)} (h : w.Perm w') {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) : derivAlong w g = derivAlong w' g := by
  induction h generalizing g with
  | nil => rfl
  | cons a _ ih => exact ih (contDiff_pdAt hg a)
  | swap a b l =>
    simp only [derivAlong_cons]
    rw [pdAt_comm hg]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hg).trans (ih₂ hg)
theorem derivAlong_add (w : List (Fin n × Fin 4)) {g h : PointTuple n → E} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) : derivAlong w (g + h) = derivAlong w g + derivAlong w h := by
  induction w generalizing g h with
  | nil => rfl
  | cons a w ih =>
    rw [derivAlong_cons, pdAt_add hg hh]
    exact ih (contDiff_pdAt hg a) (contDiff_pdAt hh a)
theorem derivAlong_comp_clm (T : E →L[ℝ] E') (w : List (Fin n × Fin 4)) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) : derivAlong w (T ∘ g) = T ∘ derivAlong w g := by
  induction w generalizing g with
  | nil => rfl
  | cons a w ih =>
    rw [derivAlong_cons, pdAt_comp_clm T hg]
    exact ih (contDiff_pdAt hg a)
theorem derivAlong_eq_zero_on (w : List (Fin n × Fin 4)) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) {U : Set (PointTuple n)} (hU : IsOpen U) (h0 : ∀ x ∈ U, g x = 0) :
    ∀ x ∈ U, derivAlong w g x = 0 := by
  induction w generalizing g with
  | nil => exact h0
  | cons a w ih => exact ih (contDiff_pdAt hg a) (pdAt_eq_zero_on hg hU h0 a)
def idxWord (α : MultiIdx4 n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem foldr_flatMap' {A B C : Type*} (f : B → C → C) (l : List A) (t : A → List B) (c : C) :
    (l.flatMap t).foldr f c = l.foldr (fun a h => (t a).foldr f h) c := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.foldr_flatMap <;> assumption
theorem foldr_replicate_iterate {B C : Type*} (f : B → C → C) (k : ℕ) (b : B) (c : C) :
    (List.replicate k b).foldr f c = (f b)^[k] c := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.foldr_replicate_iterate <;> assumption
theorem multiDeriv_eq_derivAlong (α : MultiIdx4 n) (g : PointTuple n → E) :
    multiDeriv α g = derivAlong (idxWord α).reverse g := by
  have h : (idxWord α).foldr pdAt g = multiDeriv α g := by
    simp only [idxWord, foldr_flatMap', foldr_replicate_iterate]
    rfl
  rw [← h, derivAlong, List.foldl_reverse]
def wordCount (w : List (Fin n × Fin 4)) : MultiIdx4 n := fun i μ => w.count (i, μ)
theorem sum_map_finRange {m : ℕ} (f : Fin m → ℕ) :
    ((List.finRange m).map f).sum = ∑ i, f i := (Fin.sum_univ_def f).symm
theorem count_idxWord (α : MultiIdx4 n) (a : Fin n × Fin 4) :
    (idxWord α).count a = α a.1 a.2 := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.count_indexList <;> assumption
theorem wordCount_idxWord (α : MultiIdx4 n) : wordCount (idxWord α) = α := by
  funext i μ
  exact count_idxWord α (i, μ)
theorem wordCount_append (v w : List (Fin n × Fin 4)) :
    wordCount (v ++ w) = wordCount v + wordCount w := by
  funext i μ
  simp [wordCount, List.count_append]
theorem perm_idxWord_wordCount (w : List (Fin n × Fin 4)) : w.Perm (idxWord (wordCount w)) := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.perm_indexList <;> assumption
theorem multiDeriv_wordCount (w : List (Fin n × Fin 4)) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) : multiDeriv (wordCount w) g = derivAlong w g := by
  rw [multiDeriv_eq_derivAlong]
  exact (derivAlong_perm ((perm_idxWord_wordCount w).trans (List.reverse_perm _).symm) hg).symm
theorem contDiff_multiDeriv (α : MultiIdx4 n) {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (multiDeriv α g) := by apply _root_.YangMills.Construction.TestSpaces.Elementary.contDiff_multiDeriv <;> assumption
theorem multiDeriv_multiDeriv (α γ : MultiIdx4 n) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) :
    multiDeriv α (multiDeriv γ g) = multiDeriv (α + γ) g := by
  have e : α + γ = wordCount ((idxWord γ).reverse ++ (idxWord α).reverse) := by
    rw [add_comm]
    funext i μ
    simp [wordCount, List.count_append, List.count_reverse, count_idxWord]
  rw [e, multiDeriv_wordCount _ hg, derivAlong_append, multiDeriv_eq_derivAlong α,
    multiDeriv_eq_derivAlong γ]
theorem multiDeriv_add (α : MultiIdx4 n) {g h : PointTuple n → E} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) :
    multiDeriv α (g + h) = multiDeriv α g + multiDeriv α h := by
  simp only [multiDeriv_eq_derivAlong]
  exact derivAlong_add _ hg hh
theorem multiDeriv_comp_clm (T : E →L[ℝ] E') (α : MultiIdx4 n) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) : multiDeriv α (T ∘ g) = T ∘ multiDeriv α g := by
  simp only [multiDeriv_eq_derivAlong]
  exact derivAlong_comp_clm T _ hg
theorem multiDeriv_eq_zero_on (α : MultiIdx4 n) {g : PointTuple n → E} (hg : ContDiff ℝ ∞ g)
    {U : Set (PointTuple n)} (hU : IsOpen U) (h0 : ∀ x ∈ U, g x = 0) :
    ∀ x ∈ U, multiDeriv α g x = 0 := by
  rw [multiDeriv_eq_derivAlong]
  exact derivAlong_eq_zero_on _ hg hU h0
theorem pdAt_multiDeriv (a : Fin n × Fin 4) (β : MultiIdx4 n) {g : PointTuple n → E}
    (hg : ContDiff ℝ ∞ g) :
    pdAt a (multiDeriv β g) = multiDeriv (wordCount [a] + β) g := by
  rw [← multiDeriv_multiDeriv _ _ hg,
    multiDeriv_wordCount [a] (contDiff_multiDeriv β hg)]
  rfl
end Coordinates
section Binomials
theorem idxChoose_eq_mul_prod_erase (α γ : MultiIdx4 n) (a : Fin n × Fin 4) :
    idxChoose α γ = (α a.1 a.2).choose (γ a.1 a.2) *
      ∏ b ∈ Finset.univ.erase a, (α b.1 b.2).choose (γ b.1 b.2) := by
  rw [Finset.mul_prod_erase _ (fun b : Fin n × Fin 4 => (α b.1 b.2).choose (γ b.1 b.2))
    (Finset.mem_univ a)]
  exact (Fintype.prod_prod_type' fun i μ => (α i μ).choose (γ i μ)).symm
theorem wordCount_singleton_self (a : Fin n × Fin 4) : wordCount [a] a.1 a.2 = 1 := by
  simp [wordCount]
theorem wordCount_singleton_of_ne {a b : Fin n × Fin 4} (h : b ≠ a) :
    wordCount [a] b.1 b.2 = 0 := by
  simp [wordCount, Ne.symm h]
theorem idxChoose_pascal (a : Fin n × Fin 4) (β γ : MultiIdx4 n) :
    idxChoose (wordCount [a] + β) (wordCount [a] + γ) =
      idxChoose β (wordCount [a] + γ) + idxChoose β γ := by
  have e₁ : ∏ b ∈ Finset.univ.erase a, ((wordCount [a] + β) b.1 b.2).choose
      ((wordCount [a] + γ) b.1 b.2) = ∏ b ∈ Finset.univ.erase a, (β b.1 b.2).choose (γ b.1 b.2) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    have h := wordCount_singleton_of_ne (Finset.ne_of_mem_erase hb)
    simp [h]
  have e₂ : ∏ b ∈ Finset.univ.erase a, (β b.1 b.2).choose ((wordCount [a] + γ) b.1 b.2) =
      ∏ b ∈ Finset.univ.erase a, (β b.1 b.2).choose (γ b.1 b.2) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    have h := wordCount_singleton_of_ne (Finset.ne_of_mem_erase hb)
    simp [h]
  rw [idxChoose_eq_mul_prod_erase _ _ a, idxChoose_eq_mul_prod_erase β _ a,
    idxChoose_eq_mul_prod_erase β γ a, e₁, e₂, ← add_mul]
  congr 1
  simp only [Pi.add_apply, wordCount_singleton_self]
  rw [add_comm 1, add_comm 1, Nat.choose_succ_succ', add_comm]
theorem idxChoose_add_single_of_eq_zero (a : Fin n × Fin 4) (β γ : MultiIdx4 n)
    (h0 : γ a.1 a.2 = 0) : idxChoose (wordCount [a] + β) γ = idxChoose β γ := by
  have e : ∏ b ∈ Finset.univ.erase a, ((wordCount [a] + β) b.1 b.2).choose (γ b.1 b.2) =
      ∏ b ∈ Finset.univ.erase a, (β b.1 b.2).choose (γ b.1 b.2) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    have h := wordCount_singleton_of_ne (Finset.ne_of_mem_erase hb)
    simp [h]
  rw [idxChoose_eq_mul_prod_erase _ _ a, idxChoose_eq_mul_prod_erase β _ a, e, h0]
  simp
theorem idxChoose_eq_zero_of_not_le {β γ : MultiIdx4 n} (h : ¬γ ≤ β) : idxChoose β γ = 0 := by
  simp only [Pi.le_def, not_forall, not_le] at h
  obtain ⟨i, μ, hlt⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (Finset.prod_eq_zero (Finset.mem_univ μ) (Nat.choose_eq_zero_of_lt hlt))
theorem sum_leibniz_step {R : Type*} [CommRing R] (a : Fin n × Fin 4) (β : MultiIdx4 n)
    (A B : MultiIdx4 n → R) :
    ∑ γ ∈ Finset.Icc 0 (wordCount [a] + β), (idxChoose (wordCount [a] + β) γ : R) * A γ *
        B (wordCount [a] + β - γ) =
      ∑ γ ∈ Finset.Icc 0 β, (idxChoose β γ : R) * A (wordCount [a] + γ) * B (β - γ) +
      ∑ γ ∈ Finset.Icc 0 β, (idxChoose β γ : R) * A γ * B (wordCount [a] + (β - γ)) := by
  classical
  have hδa := wordCount_singleton_self a
  have hδ : ∀ (i : Fin n) (μ : Fin 4), (i, μ) ≠ a → wordCount [a] i μ = 0 :=
    fun i μ h => wordCount_singleton_of_ne h
  generalize hδdef : wordCount [a] = δ at *
  have hadd : ∀ γ ∈ Finset.Icc 0 β, δ + (β - γ) = δ + β - γ := by
    intro γ hγ
    funext i μ
    have : γ i μ ≤ β i μ := (Finset.mem_Icc.1 hγ).2 i μ
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have hsub : Finset.Icc 0 β ⊆ Finset.Icc 0 (δ + β) :=
    Finset.Icc_subset_Icc le_rfl fun i μ => Nat.le_add_left _ _
  have h2 : ∑ γ ∈ Finset.Icc 0 β, (idxChoose β γ : R) * A γ * B (δ + (β - γ)) =
      ∑ γ ∈ Finset.Icc 0 (δ + β), (idxChoose β γ : R) * A γ * B (δ + β - γ) := by
    rw [Finset.sum_congr rfl fun γ hγ => by rw [hadd γ hγ]]
    refine Finset.sum_subset hsub fun γ _ hγ => ?_
    have hn : ¬γ ≤ β := fun h => hγ (Finset.mem_Icc.2 ⟨fun i μ => Nat.zero_le _, h⟩)
    simp [idxChoose_eq_zero_of_not_le hn]
  have h1 : ∑ γ ∈ Finset.Icc 0 β, (idxChoose β γ : R) * A (δ + γ) * B (β - γ) =
      ∑ γ ∈ (Finset.Icc 0 (δ + β)).filter (fun γ => 0 < γ a.1 a.2),
        (idxChoose β (γ - δ) : R) * A γ * B (δ + β - γ) := by
    refine Finset.sum_nbij' (fun γ => δ + γ) (fun γ => γ - δ) ?_ ?_ ?_ ?_ ?_
    · intro γ hγ
      have hle := (Finset.mem_Icc.1 hγ).2
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨fun i μ => Nat.zero_le _, fun i μ => ?_⟩, ?_⟩
      · have : γ i μ ≤ β i μ := hle i μ
        simp only [Pi.add_apply]
        omega
      · simp only [Pi.add_apply, hδa]
        omega
    · intro γ hγ
      have hm := Finset.mem_filter.1 hγ
      have hle := (Finset.mem_Icc.1 hm.1).2
      refine Finset.mem_Icc.2 ⟨fun i μ => Nat.zero_le _, fun i μ => ?_⟩
      have : γ i μ ≤ (δ + β) i μ := hle i μ
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    · intro γ _
      funext i μ
      simp
    · intro γ hγ
      have hpos := (Finset.mem_filter.1 hγ).2
      funext i μ
      simp only [Pi.add_apply, Pi.sub_apply]
      by_cases h : (i, μ) = a
      · subst h
        simp only at hδa hpos
        omega
      · have := hδ i μ h
        omega
    · intro γ _
      have e₁ : δ + γ - δ = γ := by
        funext i μ
        simp
      have e₂ : δ + β - (δ + γ) = β - γ := by
        funext i μ
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      rw [e₁, e₂]
  rw [h1, h2,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 (δ + β)) (fun γ => 0 < γ a.1 a.2)
      (fun γ => (idxChoose (δ + β) γ : R) * A γ * B (δ + β - γ)),
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 (δ + β)) (fun γ => 0 < γ a.1 a.2)
      (fun γ => (idxChoose β γ : R) * A γ * B (δ + β - γ)),
    ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hpos := (Finset.mem_filter.1 hγ).2
    have hγδ : δ + (γ - δ) = γ := by
      funext i μ
      simp only [Pi.add_apply, Pi.sub_apply]
      by_cases h : (i, μ) = a
      · subst h
        simp only at hδa hpos
        omega
      · have := hδ i μ h
        omega
    have hp := idxChoose_pascal a β (γ - δ)
    rw [hδdef, hγδ] at hp
    rw [hp]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have h0 : γ a.1 a.2 = 0 := by
      have := (Finset.mem_filter.1 hγ).2
      omega
    have hp := idxChoose_add_single_of_eq_zero a β γ h0
    rw [hδdef] at hp
    rw [hp]
theorem sum_idxChoose (α : MultiIdx4 n) :
    ∑ γ ∈ Finset.Icc 0 α, idxChoose α γ = 2 ^ idxOrder α := by
  have hentry : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, m.choose k = 2 ^ m := by
    intro m
    rw [← Nat.sum_range_choose]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp
  have hrow : ∀ i : Fin n, ∑ y ∈ Finset.Icc (0 : Fin 4 → ℕ) (α i), ∏ μ, (α i μ).choose (y μ) =
      ∏ μ, 2 ^ α i μ := by
    intro i
    have h := Finset.prod_univ_sum (fun μ => Finset.Icc 0 (α i μ))
      (fun μ k => (α i μ).choose k)
    rw [Finset.prod_congr rfl fun μ _ => hentry (α i μ)] at h
    rw [h, Pi.Icc_eq]
    rfl
  have h := Finset.prod_univ_sum (fun i => Finset.Icc (0 : Fin 4 → ℕ) (α i))
    (fun i y => ∏ μ, (α i μ).choose (y μ))
  rw [Finset.prod_congr rfl fun i _ => hrow i] at h
  rw [idxOrder, Pi.Icc_eq]
  simp only [idxChoose]
  have e : (2 : ℕ) ^ ∑ i, ∑ μ, α i μ = ∏ i, ∏ μ, 2 ^ α i μ := by
    simp only [Finset.prod_pow_eq_pow_sum]
  rw [e, h]
  rfl
end Binomials
section Products
variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]
theorem pdAt_mul {u v : PointTuple n → F} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (a : Fin n × Fin 4) :
    pdAt a (fun y => u y * v y) = fun y => pdAt a u y * v y + u y * pdAt a v y := by
  funext x
  rw [pdAt_eq_fderiv (hu.mul hv), pdAt_eq_fderiv hu, pdAt_eq_fderiv hv]
  change fderiv ℝ (u * v) x _ = _
  rw [((differentiable_of_contDiff_top hu x).hasFDerivAt.mul
      (differentiable_of_contDiff_top hv x).hasFDerivAt).fderiv]
  simp [mul_comm, add_comm]
theorem pdAt_const_mul (c : F) {u : PointTuple n → F} (hu : ContDiff ℝ ∞ u) (a : Fin n × Fin 4) :
    pdAt a (fun y => c * u y) = fun y => c * pdAt a u y :=
  pdAt_comp_clm (ContinuousLinearMap.mul ℝ F c) hu a
theorem leibniz_wordCount {u v : PointTuple n → F} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin n × Fin 4)) :
    multiDeriv (wordCount w) (fun y => u y * v y) = fun x =>
      ∑ γ ∈ Finset.Icc 0 (wordCount w), (idxChoose (wordCount w) γ : F) *
        multiDeriv γ u x * multiDeriv (wordCount w - γ) v x := by
  induction w with
  | nil =>
    have h0 : wordCount ([] : List (Fin n × Fin 4)) = 0 := rfl
    have hz : ∀ {g : PointTuple n → F}, ContDiff ℝ ∞ g → multiDeriv 0 g = g := fun hg => by
      rw [← h0, multiDeriv_wordCount [] hg]
      rfl
    funext x
    rw [h0, Finset.Icc_self, Finset.sum_singleton, hz (hu.mul hv), tsub_zero, hz hu, hz hv]
    simp [idxChoose]
  | cons a w ih =>
    have hc : wordCount (a :: w) = wordCount [a] + wordCount w := wordCount_append [a] w
    rw [hc, ← pdAt_multiDeriv a _ (hu.mul hv), ih,
      pdAt_finset_sum _ _ fun γ _ =>
        (contDiff_const.mul (contDiff_multiDeriv γ hu)).mul
          (contDiff_multiDeriv _ hv)]
    funext x
    rw [sum_leibniz_step a (wordCount w) (fun γ => multiDeriv γ u x)
      (fun γ => multiDeriv γ v x), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hp := contDiff_multiDeriv γ hu
    have hq := contDiff_multiDeriv (wordCount w - γ) hv
    rw [pdAt_mul (contDiff_const.mul hp) hq, pdAt_const_mul _ hp,
      pdAt_multiDeriv a γ hu, pdAt_multiDeriv a _ hv]
end Products
theorem rulesOver_normedField (F : Type) [NormedField F] [NormedAlgebra ℝ F] :
    RulesOver F := fun _ _ hg =>
  ⟨fun i μ x => pdAt_eq_fderiv hg (i, μ) x,
    fun i μ => contDiff_pdAt hg (i, μ),
    fun α => contDiff_multiDeriv α hg,
    fun i j μ ν => pdAt_comm hg (i, μ) (j, ν),
    fun α γ => multiDeriv_multiDeriv α γ hg,
    fun _ hh α => multiDeriv_add α hg hh,
    fun c α => multiDeriv_comp_clm (ContinuousLinearMap.mul ℝ F c) α hg,
    fun _ hU h0 α => multiDeriv_eq_zero_on α hg hU h0⟩
theorem leibnizProp_holds : LeibnizProp := by
  intro n χ φ hχ hφ α x
  have hu : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ) := Complex.ofRealCLM.contDiff.comp hχ
  have h := congrFun (leibniz_wordCount hu hφ (idxWord α)) x
  rw [wordCount_idxWord] at h
  refine h.trans (Finset.sum_congr rfl fun γ _ => ?_)
  rw [multiDeriv_comp_clm Complex.ofRealCLM γ hχ]
  rfl
theorem combined_holds : Combined :=
  ⟨rulesOver_normedField ℝ, rulesOver_normedField ℂ, leibnizProp_holds, fun _ α => sum_idxChoose α⟩
end YangMills.Construction.TestSpaces.DerivRules
