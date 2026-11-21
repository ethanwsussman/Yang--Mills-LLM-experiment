import YangMills.Construction.LinearAlgebra.BoundedMultilinearForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Multilinear.Seminormed
variable {q : ℕ} {V : Fin q → Type} [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
theorem abs_sub_le_telescoping (n : ∀ l, Seminorm ℝ (V l)) (Ψ : MultilinearMap ℝ V ℝ) (c : ℝ)
    (hbound : ∀ x : ∀ l, V l, |Ψ x| ≤ c * ∏ l, n l (x l)) (f g : ∀ l, V l) :
    |Ψ f - Ψ g| ≤ c * ∑ l, n l (f l - g l) * (∏ j ∈ Finset.Iio l, n j (g j)) *
      ∏ j ∈ Finset.Ioi l, n j (f j) := by
  let mix : ℕ → ∀ l, V l := fun m i => if i.val < m then g i else f i
  have hzero : mix 0 = f := by
    funext i
    simp [mix]
  have hfull : mix q = g := by
    funext i
    simp [mix, i.isLt]
  have hstep : ∀ l : Fin q,
      Ψ (mix l) - Ψ (mix (l + 1)) = Ψ (Function.update (mix l) l (f l - g l)) := by
    intro l
    rw [MultilinearMap.map_update_sub]
    have ef : Function.update (mix l) l (f l) = mix l := by
      funext i
      by_cases hi : i = l
      · subst hi
        simp [mix]
      · rw [Function.update_of_ne hi]
    have eg : Function.update (mix l) l (g l) = mix (l + 1) := by
      funext i
      by_cases hi : i = l
      · subst hi
        simp [mix]
      · have hne : i.val ≠ l.val := fun h => hi (Fin.ext h)
        have hiff : i.val < l.val + 1 ↔ i.val < l.val := by omega
        rw [Function.update_of_ne hi]
        simp only [mix, hiff]
    rw [ef, eg]
  have hsum : Ψ f - Ψ g = ∑ l : Fin q, Ψ (Function.update (mix l) l (f l - g l)) := by
    have htel : ∑ l : Fin q, (Ψ (mix l) - Ψ (mix (l + 1))) = Ψ f - Ψ g := by
      rw [Fin.sum_univ_eq_sum_range (fun m => Ψ (mix m) - Ψ (mix (m + 1))) q,
        Finset.sum_range_sub', hzero, hfull]
    rw [← htel]
    exact Finset.sum_congr rfl fun l _ => hstep l
  rw [hsum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  refine (hbound _).trans (le_of_eq ?_)
  have hsplit : Finset.univ.erase l = Finset.Iio l ∪ Finset.Ioi l := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact ne_iff_lt_or_gt
  have hdisj : Disjoint (Finset.Iio l) (Finset.Ioi l) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact lt_asymm (Finset.mem_Iio.mp h1) (Finset.mem_Ioi.mp h2)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hsplit,
    Finset.prod_union hdisj]
  have hat : n l (Function.update (mix l) l (f l - g l) l) = n l (f l - g l) := by
    rw [Function.update_self]
  have hbelow : ∏ j ∈ Finset.Iio l, n j (Function.update (mix l) l (f l - g l) j) =
      ∏ j ∈ Finset.Iio l, n j (g j) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hlt : i < l := Finset.mem_Iio.mp hi
    rw [Function.update_of_ne hlt.ne]
    simp only [mix, Fin.lt_def.mp hlt, if_true]
  have habove : ∏ j ∈ Finset.Ioi l, n j (Function.update (mix l) l (f l - g l) j) =
      ∏ j ∈ Finset.Ioi l, n j (f j) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hlt : l < i := Finset.mem_Ioi.mp hi
    rw [Function.update_of_ne hlt.ne']
    have hnot : ¬ i.val < l.val := not_lt.mpr (Fin.lt_def.mp hlt).le
    simp only [mix, hnot, if_false]
  rw [hat, hbelow, habove]
  ring
theorem telescoping_le_sum_prod_add (n : ∀ l, Seminorm ℝ (V l)) (c : ℝ) (hc : 0 ≤ c)
    (f g : ∀ l, V l) :
    c * ∑ l, n l (f l - g l) * (∏ j ∈ Finset.Iio l, n j (g j)) *
        ∏ j ∈ Finset.Ioi l, n j (f j) ≤
      c * ∑ l, n l (f l - g l) * ∏ j ∈ Finset.univ.erase l, (n j (f j) + n j (g j)) := by
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hc
  have hsplit : Finset.univ.erase l = Finset.Iio l ∪ Finset.Ioi l := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact ne_iff_lt_or_gt
  have hdisj : Disjoint (Finset.Iio l) (Finset.Ioi l) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact lt_asymm (Finset.mem_Iio.mp h1) (Finset.mem_Ioi.mp h2)
  rw [hsplit, Finset.prod_union hdisj, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Finset.prod_le_prod (fun i _ => apply_nonneg _ _)
      fun i _ => le_add_of_nonneg_left (apply_nonneg _ _)
  · exact Finset.prod_le_prod (fun i _ => apply_nonneg _ _)
      fun i _ => le_add_of_nonneg_right (apply_nonneg _ _)
  · exact Finset.prod_nonneg fun i _ => apply_nonneg _ _
  · exact Finset.prod_nonneg fun i _ =>
      add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
omit [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)] in
theorem restrictOrdered_update_of_notMem {J : Finset (Fin q)} {l : Fin q}
    (hl : l ∉ J) (x : ∀ l, V l) (v : V l) :
    restrictOrdered (Function.update x l v) J = restrictOrdered x J := by
  funext i
  have hne : J.orderEmbOfFin rfl i ≠ l := fun e =>
    hl (e ▸ Finset.orderEmbOfFin_mem J rfl i)
  simp only [restrictOrdered]
  rw [Function.update_of_ne hne]
omit [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)] in
theorem restrictOrdered_update (J : Finset (Fin q)) (i : Fin J.card)
    (x : ∀ l, V l) (v : V (J.orderEmbOfFin rfl i)) :
    restrictOrdered (Function.update x (J.orderEmbOfFin rfl i) v) J =
      Function.update (restrictOrdered x J) i v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [restrictOrdered]
  · have hne : J.orderEmbOfFin rfl j ≠ J.orderEmbOfFin rfl i := fun e =>
      hj ((J.orderEmbOfFin rfl).injective e)
    simp only [restrictOrdered]
    rw [Function.update_of_ne hne, Function.update_of_ne hj]
    rfl
def blockEval (Ψ : BlockForms V) (J : Finset (Fin q)) (x : ∀ l, V l) : ℝ :=
  if hJ : 2 ≤ J.card then Ψ J hJ (restrictOrdered x J) else 0
theorem blockEval_update_of_notMem (Ψ : BlockForms V)
    {J : Finset (Fin q)} {l : Fin q} (hl : l ∉ J) (x : ∀ l, V l) (v : V l) :
    blockEval Ψ J (Function.update x l v) = blockEval Ψ J x := by
  simp only [blockEval, restrictOrdered_update_of_notMem hl]
theorem exists_orderEmbOfFin_eq {J : Finset (Fin q)} {l : Fin q} (hl : l ∈ J) :
    ∃ i : Fin J.card, J.orderEmbOfFin rfl i = l := by
  exact show l ∈ Set.range (J.orderEmbOfFin rfl) from by
    rw [Finset.range_orderEmbOfFin]
    exact hl
theorem blockEval_update_add (Ψ : BlockForms V)
    {J : Finset (Fin q)} {l : Fin q} (hl : l ∈ J) (x : ∀ l, V l) (u v : V l) :
    blockEval Ψ J (Function.update x l (u + v)) =
      blockEval Ψ J (Function.update x l u) + blockEval Ψ J (Function.update x l v) := by
  obtain ⟨i, rfl⟩ := exists_orderEmbOfFin_eq hl
  by_cases hJ : 2 ≤ J.card
  · simp only [blockEval, dif_pos hJ, restrictOrdered_update]
    exact (Ψ J hJ).map_update_add _ i u v
  · simp [blockEval, hJ]
theorem blockEval_update_smul (Ψ : BlockForms V)
    {J : Finset (Fin q)} {l : Fin q} (hl : l ∈ J) (x : ∀ l, V l) (a : ℝ) (v : V l) :
    blockEval Ψ J (Function.update x l (a • v)) =
      a * blockEval Ψ J (Function.update x l v) := by
  obtain ⟨i, rfl⟩ := exists_orderEmbOfFin_eq hl
  by_cases hJ : 2 ≤ J.card
  · simp only [blockEval, dif_pos hJ, restrictOrdered_update]
    exact (Ψ J hJ).map_update_smul _ i a v
  · simp [blockEval, hJ]
theorem prod_blockEval_update (Ψ : BlockForms V)
    (π : Finpartition (Finset.univ : Finset (Fin q))) {J₀ : Finset (Fin q)}
    (hJ₀ : J₀ ∈ π.parts) {l : Fin q} (hl : l ∈ J₀) (x : ∀ l, V l) (v : V l) :
    ∏ J ∈ π.parts, blockEval Ψ J (Function.update x l v) =
      blockEval Ψ J₀ (Function.update x l v) *
        ∏ J ∈ π.parts.erase J₀, blockEval Ψ J x := by
  rw [← Finset.mul_prod_erase π.parts _ hJ₀]
  congr 1
  refine Finset.prod_congr rfl fun J hJ => ?_
  have hJπ : J ∈ π.parts := Finset.mem_of_mem_erase hJ
  have hne : J ≠ J₀ := Finset.ne_of_mem_erase hJ
  have hdisj : Disjoint J J₀ := π.disjoint hJπ hJ₀ hne
  exact blockEval_update_of_notMem Ψ (Finset.disjoint_right.mp hdisj hl) x v
theorem exists_part_mem (π : Finpartition (Finset.univ : Finset (Fin q))) (l : Fin q) :
    ∃ J ∈ π.parts, l ∈ J :=
  π.exists_mem (Finset.mem_univ l)
def partitionMultilinear (Ψ : BlockForms V) (π : Finpartition (Finset.univ : Finset (Fin q))) :
    MultilinearMap ℝ V ℝ where
  toFun x := ∏ J ∈ π.parts, blockEval Ψ J x
  map_update_add' := by
    intro inst x l u v
    obtain rfl : inst = instDecidableEqFin q := Subsingleton.elim _ _
    obtain ⟨J₀, hJ₀, hl⟩ := exists_part_mem π l
    rw [prod_blockEval_update Ψ π hJ₀ hl, prod_blockEval_update Ψ π hJ₀ hl,
      prod_blockEval_update Ψ π hJ₀ hl, blockEval_update_add Ψ hl, add_mul]
  map_update_smul' := by
    intro inst x l a v
    obtain rfl : inst = instDecidableEqFin q := Subsingleton.elim _ _
    obtain ⟨J₀, hJ₀, hl⟩ := exists_part_mem π l
    rw [prod_blockEval_update Ψ π hJ₀ hl, prod_blockEval_update Ψ π hJ₀ hl,
      blockEval_update_smul Ψ hl, smul_eq_mul, mul_assoc]
theorem partitionSum_eq_sum_prod (Ψ : BlockForms V) (x : ∀ l, V l) :
    partitionSum Ψ x =
      ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, blockEval Ψ J x := by
  rw [partitionSum, ← Finset.sum_attach (SetPartition.nonSingletonPartitions q)]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach π.1.parts]
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [blockEval, dif_pos ((Finset.mem_filter.mp π.2).2 J.1 J.2)]
theorem abs_partitionSum_le (n : ∀ l, Seminorm ℝ (V l)) (Ψ : BlockForms V) (C : ℕ → ℝ)
    (hbound : ∀ (J : Finset (Fin q)) (hJ : 2 ≤ J.card) (x : ∀ l, V l),
      |Ψ J hJ (restrictOrdered x J)| ≤ C J.card * ∏ l ∈ J, n l (x l)) (x : ∀ l, V l) :
    |partitionSum Ψ x| ≤ partitionBound q C * ∏ l, n l (x l) := by
  rw [partitionSum_eq_sum_prod, partitionBound, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π hπ => ?_)
  have hcard : ∀ J ∈ π.parts, 2 ≤ J.card := (Finset.mem_filter.mp hπ).2
  have hprod : ∏ J ∈ π.parts, ∏ l ∈ J, n l (x l) = ∏ l, n l (x l) := by
    calc ∏ J ∈ π.parts, ∏ l ∈ J, n l (x l)
        = ∏ l ∈ π.parts.biUnion id, n l (x l) := (Finset.prod_biUnion π.disjoint).symm
      _ = ∏ l, n l (x l) := by rw [π.biUnion_parts]
  rw [Finset.abs_prod, ← hprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun J _ => abs_nonneg _) fun J hJ => ?_
  rw [blockEval, dif_pos (hcard J hJ)]
  exact hbound J (hcard J hJ) x
theorem boundedMultilinearEstimates : BoundedMultilinearEstimates := by
  intro q _ V _ _ n
  refine ⟨fun Ψ c hc hbound f g =>
      ⟨abs_sub_le_telescoping n Ψ c hbound f g, telescoping_le_sum_prod_add n c hc f g⟩,
    fun Ψ => ⟨⟨∑ π ∈ SetPartition.nonSingletonPartitions q, partitionMultilinear Ψ π,
      fun x => ?_⟩, fun C _ hbound x => abs_partitionSum_le n Ψ C hbound x⟩⟩
  rw [_root_.sum_apply, partitionSum_eq_sum_prod]
  rfl
end YangMills.Construction.Multilinear.Seminormed
end
