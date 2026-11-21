import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion.QuadraticFormCumulants
open MvPolynomial
section Partitions
variable {α : Type} [DecidableEq α]
private theorem sum_finpartition_eq_sum_block_containing (S : Finset α) (u : α) (hu : u ∈ S)
    (F : Finset (Finset α) → ℝ) :
    ∑ π : Finpartition S, F π.parts =
      ∑ B ∈ S.powerset.filter (u ∈ ·), ∑ ρ : Finpartition (S \ B), F (insert B ρ.parts) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x hx => (x.2.extend (b := x.1) (c := S) ?_ ?_ ?_)) ?_ ?_ ?_ ?_
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, and_true] at hx
    exact Finset.ne_empty_of_mem hx.2
  · exact Finset.sdiff_disjoint
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, and_true] at hx
    simpa using hx.1
  · intro _ _
    exact Finset.mem_univ _
  · rintro ⟨B, ρ⟩ h1 ⟨B', ρ'⟩ h2 h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, and_true] at h1 h2
    have hp : insert B ρ.parts = insert B' ρ'.parts := congrArg Finpartition.parts h
    have notin : ∀ (C : Finset α) (τ : Finpartition (S \ C)), u ∈ C → ∀ D ∈ τ.parts, u ∉ D := by
      intro C τ hC D hD huD
      have := τ.le hD huD
      simp [hC] at this
    have hBB : B = B' := by
      have : B ∈ insert B' ρ'.parts := hp ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 this with h' | h'
      · exact h'
      · exact absurd h1.2 (notin B' ρ' h2.2 B h')
    subst hBB
    have hρ : ρ.parts = ρ'.parts := by
      have nB : ∀ τ : Finpartition (S \ B), B ∉ τ.parts := fun τ hB => notin B τ h1.2 B hB h1.2
      rw [← Finset.erase_insert (nB ρ), hp, Finset.erase_insert (nB ρ')]
    have : ρ = ρ' := Finpartition.ext hρ
    subst this
    rfl
  · intro π _
    have hbu : ∃ B ∈ π.parts, u ∈ B := by
      have : u ∈ π.parts.biUnion id := by rw [π.biUnion_parts]; exact hu
      simpa using this
    obtain ⟨B, hB, huB⟩ := hbu
    refine ⟨⟨B, π.avoid B⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, and_true]
      exact ⟨π.le hB, huB⟩
    · apply Finpartition.ext
      show insert B (π.avoid B).parts = π.parts
      ext D
      simp only [Finset.mem_insert, Finpartition.mem_avoid]
      constructor
      · rintro (rfl | ⟨E, hE, hEB, rfl⟩)
        · exact hB
        · have hne : E ≠ B := fun h => hEB (h ▸ le_rfl)
          have hdis : Disjoint E B := π.disjoint hE hB hne
          rw [Finset.sdiff_eq_self_of_disjoint hdis]
          exact hE
      · intro hD
        by_cases hDB : D = B
        · exact Or.inl hDB
        · refine Or.inr ⟨D, hD, ?_, Finset.sdiff_eq_self_of_disjoint (π.disjoint hD hB hDB)⟩
          intro hle
          obtain ⟨y, hy⟩ := π.nonempty_of_mem_parts hD
          have hdis := π.disjoint hD hB hDB
          exact Finset.disjoint_left.1 hdis hy (hle hy)
  · intro x hx
    rfl
end Partitions
section Stein
variable {V : Type} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
private def covDeriv (c : V → V → ℝ) (u : V) : Derivation ℝ (MvPolynomial V ℝ) (MvPolynomial V ℝ) :=
  ∑ v, c u v • pderiv v
private def covLaplacian (c : V → V → ℝ) : MvPolynomial V ℝ →ₗ[ℝ] MvPolynomial V ℝ :=
  ∑ u, (pderiv u).toLinearMap ∘ₗ (covDeriv c u).toLinearMap
private theorem derivation_sum_apply {ι : Type} (s : Finset ι)
    (D : ι → Derivation ℝ (MvPolynomial V ℝ) (MvPolynomial V ℝ)) (f : MvPolynomial V ℝ) :
    (∑ i ∈ s, D i) f = ∑ i ∈ s, D i f := by
  show Derivation.coeFnAddMonoidHom (∑ i ∈ s, D i) f = _
  rw [map_sum, Finset.sum_apply]
  rfl
private theorem covDeriv_apply (c : V → V → ℝ) (u : V) (f : MvPolynomial V ℝ) :
    covDeriv c u f = ∑ v, c u v • pderiv v f := by
  rw [covDeriv, derivation_sum_apply]
  rfl
private theorem covLaplacian_apply (c : V → V → ℝ) (f : MvPolynomial V ℝ) :
    covLaplacian c f = ∑ u, pderiv u (covDeriv c u f) := by
  simp [covLaplacian, LinearMap.sum_apply]
private theorem covDeriv_X (c : V → V → ℝ) (u v : V) :
    covDeriv c u (X v) = MvPolynomial.C (c u v) := by
  rw [covDeriv_apply]
  simp [pderiv_X, Pi.single_apply, MvPolynomial.smul_eq_C_mul]
private theorem pderiv_pderiv_comm (a b : V) (f : MvPolynomial V ℝ) :
    pderiv a (pderiv b f) = pderiv b (pderiv a f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, Pi.single_apply]
    split_ifs <;> simp [hp] <;> ring
private theorem covDeriv_pderiv (c : V → V → ℝ) (u w : V) (f : MvPolynomial V ℝ) :
    covDeriv c u (pderiv w f) = pderiv w (covDeriv c u f) := by
  simp only [covDeriv_apply, map_sum, Derivation.map_smul, pderiv_pderiv_comm w]
private theorem covDeriv_covDeriv (c : V → V → ℝ) (u w : V) (f : MvPolynomial V ℝ) :
    covDeriv c u (covDeriv c w f) = covDeriv c w (covDeriv c u f) := by
  simp only [covDeriv_apply, map_sum, Derivation.map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z _ => ?_
  rw [pderiv_pderiv_comm, smul_comm]
private theorem covDeriv_covLaplacian (c : V → V → ℝ) (u : V) (f : MvPolynomial V ℝ) :
    covDeriv c u (covLaplacian c f) = covLaplacian c (covDeriv c u f) := by
  simp only [covLaplacian_apply, map_sum, covDeriv_pderiv, covDeriv_covDeriv c u]
private theorem covLaplacian_X_mul (c : V → V → ℝ) (hc : ∀ u v, c u v = c v u) (u : V)
    (g : MvPolynomial V ℝ) :
    covLaplacian c (X u * g) = X u * covLaplacian c g + (2 : ℝ) • covDeriv c u g := by
  have h1 : ∀ a, pderiv a (covDeriv c a (X u * g)) =
      X u * pderiv a (covDeriv c a g) + (if u = a then (1 : MvPolynomial V ℝ) else 0) * covDeriv c a g +
        MvPolynomial.C (c a u) * pderiv a g := by
    intro a
    simp only [Derivation.leibniz, covDeriv_X, pderiv_X, smul_eq_mul, map_add, pderiv_C, mul_zero,
      Pi.single_apply]
    ring
  simp only [covLaplacian_apply, h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ a, (if u = a then (1 : MvPolynomial V ℝ) else 0) * covDeriv c a g = covDeriv c u g := by
    simp
  have h3 : ∑ a, MvPolynomial.C (c a u) * pderiv a g = covDeriv c u g := by
    rw [covDeriv_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hc a u, MvPolynomial.smul_eq_C_mul]
  rw [h2, h3, two_smul]
  ring
private def evalZero : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval (fun _ : V => (0 : ℝ))).toLinearMap
private theorem evalZero_X_mul (u : V) (f : MvPolynomial V ℝ) : evalZero (X u * f) = 0 := by
  simp [evalZero]
private theorem evalZero_one : evalZero (1 : MvPolynomial V ℝ) = 1 := by
  simp [evalZero]
private def gaussianMoment (c : V → V → ℝ) : ℕ → (MvPolynomial V ℝ →ₗ[ℝ] ℝ)
  | 0 => evalZero
  | n + 1 => (1 / (2 * ((n : ℝ) + 1))) • (gaussianMoment c n ∘ₗ covLaplacian c)
private theorem gaussianMoment_succ (c : V → V → ℝ) (n : ℕ) (f : MvPolynomial V ℝ) :
    gaussianMoment c (n + 1) f = (1 / (2 * ((n : ℝ) + 1))) * gaussianMoment c n (covLaplacian c f) := rfl
private theorem gaussianMoment_X_mul (c : V → V → ℝ) (hc : ∀ u v, c u v = c v u) (n : ℕ) (u : V)
    (f : MvPolynomial V ℝ) :
    gaussianMoment c (n + 1) (X u * f) = gaussianMoment c n (covDeriv c u f) := by
  induction n generalizing f with
  | zero =>
    rw [gaussianMoment_succ, covLaplacian_X_mul c hc, map_add, map_smul]
    simp only [gaussianMoment, evalZero_X_mul, smul_eq_mul]
    norm_num
    ring
  | succ n ih =>
    have h : gaussianMoment c n (covLaplacian c (covDeriv c u f)) = (2 * ((n : ℝ) + 1)) * gaussianMoment c (n + 1) (covDeriv c u f) := by
      rw [gaussianMoment_succ]
      have : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
      field_simp
    rw [gaussianMoment_succ, covLaplacian_X_mul c hc, map_add, map_smul, ih, covDeriv_covLaplacian, h, smul_eq_mul]
    push_cast
    have : (2 * ((n : ℝ) + 1 + 1)) ≠ 0 := by positivity
    field_simp
private theorem covDeriv_prod_X {α : Type} [DecidableEq α] (c : V → V → ℝ) (u : V) (w : α → V)
    (S : Finset α) :
    covDeriv c u (∏ i ∈ S, X (w i)) =
      ∑ t ∈ S, c u (w t) • ∏ i ∈ S.erase t, (X (w i) : MvPolynomial V ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, covDeriv_X, Finset.sum_insert ha,
      Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, MvPolynomial.smul_eq_C_mul, Finset.mul_sum,
      add_comm]
    congr 1
    · exact mul_comm _ _
    refine Finset.sum_congr rfl fun t ht => ?_
    have hne : a ≠ t := fun h => ha (h ▸ ht)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (by simp [ha]), mul_smul_comm]
end Stein
section Matching
variable {α : Type} [LinearOrder α]
private def pairWeight (g : α → α → ℝ) (B : Finset α) : ℝ :=
  if h : B.Nonempty then g (B.min' h) (B.max' h) else 1
open Classical in
private def pairingSumOn (g : α → α → ℝ) (S : Finset α) : ℝ :=
  ∑ π : Finpartition S, if ∀ B ∈ π.parts, B.card = 2 then ∏ B ∈ π.parts, pairWeight g B else 0
private theorem pairWeight_pair (g : α → α → ℝ) (hg : ∀ a b, g a b = g b a) {u v : α} (h : u ≠ v) :
    pairWeight g {u, v} = g u v := by
  have hn : ({u, v} : Finset α).Nonempty := ⟨u, by simp⟩
  rw [pairWeight, dif_pos hn]
  rcases lt_or_gt_of_ne h with h' | h'
  · have h1 : ({u, v} : Finset α).min' hn = u :=
      le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp [h'.le]))
    have h2 : ({u, v} : Finset α).max' hn = v :=
      le_antisymm (Finset.max'_le _ _ _ (by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp [h'.le])) (Finset.le_max' _ _ (by simp))
    rw [h1, h2]
  · have h1 : ({u, v} : Finset α).min' hn = v :=
      le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp [h'.le]))
    have h2 : ({u, v} : Finset α).max' hn = u :=
      le_antisymm (Finset.max'_le _ _ _ (by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp [h'.le])) (Finset.le_max' _ _ (by simp))
    rw [h1, h2, hg]
private theorem pairingSumOn_expand (g : α → α → ℝ) (hg : ∀ a b, g a b = g b a) (S : Finset α) (u : α)
    (hu : u ∈ S) :
    pairingSumOn g S = ∑ v ∈ S.erase u, g u v * pairingSumOn g (S \ {u, v}) := by
  classical
  let F : Finset (Finset α) → ℝ := fun P => if ∀ B ∈ P, B.card = 2 then ∏ B ∈ P, pairWeight g B else 0
  have h0 : pairingSumOn g S = ∑ π : Finpartition S, F π.parts := rfl
  rw [h0, sum_finpartition_eq_sum_block_containing S u hu F]
  have hsub : (S.erase u).image (fun v => ({u, v} : Finset α)) ⊆ S.powerset.filter (u ∈ ·) := by
    intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hB
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, by simp⟩
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hu
    · exact Finset.mem_of_mem_erase hv
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image ?_]
  · refine Finset.sum_congr rfl fun v hv => ?_
    have huv : u ≠ v := (Finset.ne_of_mem_erase hv).symm
    have hm : pairingSumOn g (S \ {u, v}) =
        ∑ ρ : Finpartition (S \ {u, v}), F ρ.parts := rfl
    rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hnot : ({u, v} : Finset α) ∉ ρ.parts := by
      intro hB
      have := ρ.le hB (show u ∈ ({u, v} : Finset α) by simp)
      simp at this
    simp only [F]
    by_cases hall : ∀ B ∈ ρ.parts, B.card = 2
    · have hall' : ∀ B ∈ insert ({u, v} : Finset α) ρ.parts, B.card = 2 := by
        intro B hB
        rcases Finset.mem_insert.1 hB with rfl | hB
        · exact Finset.card_pair huv
        · exact hall B hB
      rw [if_pos hall, if_pos hall', Finset.prod_insert hnot, pairWeight_pair g hg huv]
    · have hall' : ¬ ∀ B ∈ insert ({u, v} : Finset α) ρ.parts, B.card = 2 :=
        fun h => hall fun B hB => h B (Finset.mem_insert_of_mem hB)
      rw [if_neg hall, if_neg hall', mul_zero]
  · intro a ha b hb hab
    have ha' : a ≠ u := Finset.ne_of_mem_erase ha
    have hb' : b ≠ u := Finset.ne_of_mem_erase hb
    have : a ∈ ({u, b} : Finset α) := by
      have h2 : a ∈ ({u, a} : Finset α) := by simp
      have h3 : ({u, a} : Finset α) = {u, b} := hab
      rwa [h3] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h ha'
    · exact h
  · intro B hB hnot
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    refine Finset.sum_eq_zero fun ρ _ => ?_
    have hcard : B.card ≠ 2 := by
      intro h2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
      apply hnot
      rcases (by simpa using hB.2 : u = a ∨ u = b) with rfl | rfl
      · refine Finset.mem_image.2 ⟨b, Finset.mem_erase.2 ⟨hab.symm, hB.1 (by simp)⟩, rfl⟩
      · refine Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨hab, hB.1 (by simp)⟩, ?_⟩
        exact Finset.pair_comm _ _
    simp only [F]
    rw [if_neg]
    intro h
    exact hcard (h B (Finset.mem_insert_self _ _))
private theorem pairingSumOn_empty (g : α → α → ℝ) : pairingSumOn g ∅ = 1 := by
  classical
  have hp : ∀ π : Finpartition (∅ : Finset α), π.parts = ∅ := by
    intro π
    apply Finset.eq_empty_of_forall_notMem
    intro J hJ
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hJ
    simpa using π.le hJ hx
  have hone : ∀ π π' : Finpartition (∅ : Finset α), π = π' := fun π π' =>
    Finpartition.ext (by rw [hp, hp])
  have : Unique (Finpartition (∅ : Finset α)) := ⟨⟨Finpartition.empty _⟩, fun π => hone _ _⟩
  rw [pairingSumOn, Fintype.sum_unique]
  simp [hp]
private theorem gaussianMoment_prod_X {V : Type} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : ∀ u v, c u v = c v u) (w : α → V) (m : ℕ) (S : Finset α) (hS : S.card = 2 * m) :
    gaussianMoment c m (∏ i ∈ S, (X (w i) : MvPolynomial V ℝ)) = pairingSumOn (fun i j => c (w i) (w j)) S := by
  induction m generalizing S with
  | zero =>
    have : S = ∅ := by simpa using hS
    subst this
    simp [pairingSumOn_empty, gaussianMoment, evalZero_one]
  | succ m ih =>
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨u, hu⟩ := hne
    rw [pairingSumOn_expand _ (fun a b => hc _ _) S u hu, ← Finset.mul_prod_erase S _ hu, gaussianMoment_X_mul c hc,
      covDeriv_prod_X, map_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [map_smul, smul_eq_mul]
    have hcard : ((S.erase u).erase v).card = 2 * m := by
      rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]; omega
    rw [ih _ hcard]
    have : (S.erase u).erase v = S \ {u, v} := by
      ext y; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [this]
end Matching
section Forms
variable {I : Type} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false
private def colourCov (T : Matrix I I ℝ) (v v' : I × Fin 3) : ℝ := if v.2 = v'.2 then T v.1 v'.1 else 0
private theorem colourCov_symm {T : Matrix I I ℝ} (hT : T.IsSymm) (u v : I × Fin 3) :
    colourCov T u v = colourCov T v u := by
  unfold colourCov
  by_cases h : u.2 = v.2
  · rw [if_pos h, if_pos h.symm]
    exact congrFun (congrFun hT _) _ |>.symm
  · rw [if_neg h, if_neg (Ne.symm h)]
private def quadPoly (K : Matrix I I ℝ) : MvPolynomial (I × Fin 3) ℝ :=
  ∑ a, ∑ b, (K a b / 2) • ∑ e, X (a, e) * X (b, e)
private def quadMean (T M : Matrix I I ℝ) : ℝ := (3 / 2) * ∑ a, ∑ b, M a b * T a b
private def contractDeriv (T M : Matrix I I ℝ) :
    Derivation ℝ (MvPolynomial (I × Fin 3) ℝ) (MvPolynomial (I × Fin 3) ℝ) :=
  ∑ a, ∑ b, (M a b / 2) • ∑ e, (X (b, e) : MvPolynomial (I × Fin 3) ℝ) • covDeriv (colourCov T) (a, e)
private theorem contractDeriv_apply (T M : Matrix I I ℝ) (f : MvPolynomial (I × Fin 3) ℝ) :
    contractDeriv T M f = ∑ a, ∑ b, (M a b / 2) • ∑ e, X (b, e) * covDeriv (colourCov T) (a, e) f := by
  rw [contractDeriv, derivation_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [derivation_sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Derivation.smul_apply, derivation_sum_apply]
  rfl
private theorem gaussianMoment_quadPoly_mul {T : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ) (n : ℕ)
    (F : MvPolynomial (I × Fin 3) ℝ) :
    gaussianMoment (colourCov T) (n + 1) (quadPoly M * F) =
      quadMean T M * gaussianMoment (colourCov T) n F + gaussianMoment (colourCov T) n (contractDeriv T M F) := by
  have key : ∀ a b, gaussianMoment (colourCov T) (n + 1) ((∑ e, X (a, e) * X (b, e)) * F) =
      3 * T a b * gaussianMoment (colourCov T) n F +
        gaussianMoment (colourCov T) n (∑ e, X (b, e) * covDeriv (colourCov T) (a, e) F) := by
    intro a b
    have h1 : ∀ e : Fin 3, gaussianMoment (colourCov T) (n + 1) (X (a, e) * X (b, e) * F) =
        T a b * gaussianMoment (colourCov T) n F + gaussianMoment (colourCov T) n (X (b, e) * covDeriv (colourCov T) (a, e) F) := by
      intro e
      rw [mul_assoc, gaussianMoment_X_mul _ (colourCov_symm hT), Derivation.leibniz, covDeriv_X, smul_eq_mul,
        smul_eq_mul, map_add, mul_comm F, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      simp only [colourCov, if_true]
      ring
    rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_congr rfl fun e _ => h1 e,
      Finset.sum_add_distrib]
    simp
    ring
  have e1 : quadMean T M * gaussianMoment (colourCov T) n F =
      ∑ a, ∑ b, (3 / 2 * (M a b * T a b)) * gaussianMoment (colourCov T) n F := by
    simp only [quadMean, Finset.mul_sum, Finset.sum_mul]
  rw [quadPoly, contractDeriv_apply, e1, Finset.sum_mul, map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_assoc, map_smul, map_smul, key, smul_eq_mul, smul_eq_mul]
  ring
private theorem pderiv_quadPoly {L : Matrix I I ℝ} (hL : L.IsSymm) (c : I) (e : Fin 3) :
    pderiv (c, e) (quadPoly L) = ∑ d, L c d • (X (d, e) : MvPolynomial (I × Fin 3) ℝ) := by
  have h1 : ∀ a b, pderiv (c, e) (∑ f, (X (a, f) * X (b, f) : MvPolynomial (I × Fin 3) ℝ)) =
      (if c = b then X (a, e) else 0) + (if c = a then X (b, e) else 0) := by
    intro a b
    simp only [map_sum, Derivation.leibniz, pderiv_X, smul_eq_mul, Pi.single_apply, Prod.mk.injEq,
      Finset.sum_add_distrib]
    congr 1
    · by_cases h : c = b <;> simp [h, eq_comm]
    · by_cases h : c = a <;> simp [h, eq_comm]
  simp only [quadPoly, map_sum, Derivation.map_smul, h1, smul_add, Finset.sum_add_distrib, smul_ite,
    smul_zero]
  have hA : ∑ a, ∑ b, (if c = b then (L a b / 2) • (X (a, e) : MvPolynomial (I × Fin 3) ℝ) else 0) =
      ∑ a, (L a c / 2) • (X (a, e) : MvPolynomial (I × Fin 3) ℝ) := by
    simp
  have hB : ∑ a, ∑ b, (if c = a then (L a b / 2) • (X (b, e) : MvPolynomial (I × Fin 3) ℝ) else 0) =
      ∑ b, (L c b / 2) • (X (b, e) : MvPolynomial (I × Fin 3) ℝ) := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ h
      simp [Ne.symm h]
    · simp
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← add_smul]
  congr 1
  have : L d c = L c d := congrFun (congrFun hL c) d
  rw [this]
  ring
private theorem covDeriv_quadPoly {T L : Matrix I I ℝ} (hL : L.IsSymm) (a : I) (e : Fin 3) :
    covDeriv (colourCov T) (a, e) (quadPoly L) =
      ∑ c, T a c • ∑ d, L c d • (X (d, e) : MvPolynomial (I × Fin 3) ℝ) := by
  rw [covDeriv_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [pderiv_quadPoly hL, colourCov, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
private theorem sum_four_reorder {R : Type} [AddCommMonoid R] (f : I → I → I → I → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ d, ∑ c, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
  rw [Finset.sum_comm]
private theorem contractDeriv_quadPoly {T L : Matrix I I ℝ} (M : Matrix I I ℝ) (hL : L.IsSymm) :
    contractDeriv T M (quadPoly L) = quadPoly (M.transpose * T * L) := by
  obtain ⟨P, hP⟩ : ∃ P : I → I → MvPolynomial (I × Fin 3) ℝ,
      P = fun b d => ∑ e, (X (b, e) * X (d, e) : MvPolynomial (I × Fin 3) ℝ) := ⟨_, rfl⟩
  have h : ∀ a b, ∑ e : Fin 3, (X (b, e) : MvPolynomial (I × Fin 3) ℝ) *
      ∑ c, T a c • ∑ d, L c d • (X (d, e) : MvPolynomial (I × Fin 3) ℝ) =
      ∑ c, ∑ d, (T a c * L c d) • P b d := by
    intro a b
    simp only [hP, Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
  have hc : ∀ b d, (M.transpose * T * L) b d / 2 = ∑ c, ∑ a, (M a b / 2) * (T a c * L c d) := by
    intro b d
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hq : quadPoly (M.transpose * T * L) = ∑ b, ∑ d, ((M.transpose * T * L) b d / 2) • P b d := by
    rw [hP]
    rfl
  rw [contractDeriv_apply, hq]
  simp only [covDeriv_quadPoly hL]
  simp only [h]
  simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact sum_four_reorder fun a b c d => ((M a b / 2) * (T a c * L c d)) • P b d
private theorem gaussianMoment_one_form {T : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ) :
    gaussianMoment (colourCov T) 1 (quadPoly M) = quadMean T M := by
  have := gaussianMoment_quadPoly_mul hT M 0 1
  simpa [gaussianMoment, evalZero_one] using this
private theorem gaussianMoment_two_forms {T L : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ) (hL : L.IsSymm) :
    gaussianMoment (colourCov T) 2 (quadPoly M * quadPoly L) = quadMean T M * quadMean T L + quadMean T (M.transpose * T * L) := by
  rw [gaussianMoment_quadPoly_mul hT M 1 (quadPoly L), contractDeriv_quadPoly M hL, gaussianMoment_one_form hT, gaussianMoment_one_form hT]
private theorem gaussianMoment_three_forms {T L₁ L₂ : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ)
    (h₁ : L₁.IsSymm) (h₂ : L₂.IsSymm) :
    gaussianMoment (colourCov T) 3 (quadPoly M * (quadPoly L₁ * quadPoly L₂)) =
      quadMean T M * gaussianMoment (colourCov T) 2 (quadPoly L₁ * quadPoly L₂) +
        gaussianMoment (colourCov T) 2 (quadPoly (M.transpose * T * L₁) * quadPoly L₂) +
          gaussianMoment (colourCov T) 2 (quadPoly (M.transpose * T * L₂) * quadPoly L₁) := by
  have h : contractDeriv T M (quadPoly L₁ * quadPoly L₂) =
      quadPoly (M.transpose * T * L₁) * quadPoly L₂ + quadPoly (M.transpose * T * L₂) * quadPoly L₁ := by
    simp only [Derivation.leibniz, contractDeriv_quadPoly M h₁, contractDeriv_quadPoly M h₂, smul_eq_mul]
    ring
  rw [gaussianMoment_quadPoly_mul hT M 2, h, map_add, add_assoc]
private theorem gaussianMoment_four_forms {T L₁ L₂ L₃ : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ)
    (h₁ : L₁.IsSymm) (h₂ : L₂.IsSymm) (h₃ : L₃.IsSymm) :
    gaussianMoment (colourCov T) 4 (quadPoly M * (quadPoly L₁ * (quadPoly L₂ * quadPoly L₃))) =
      quadMean T M * gaussianMoment (colourCov T) 3 (quadPoly L₁ * (quadPoly L₂ * quadPoly L₃)) +
        gaussianMoment (colourCov T) 3 (quadPoly (M.transpose * T * L₁) * (quadPoly L₂ * quadPoly L₃)) +
          gaussianMoment (colourCov T) 3 (quadPoly (M.transpose * T * L₂) * (quadPoly L₁ * quadPoly L₃)) +
            gaussianMoment (colourCov T) 3 (quadPoly (M.transpose * T * L₃) * (quadPoly L₁ * quadPoly L₂)) := by
  have h : contractDeriv T M (quadPoly L₁ * (quadPoly L₂ * quadPoly L₃)) =
      quadPoly (M.transpose * T * L₁) * (quadPoly L₂ * quadPoly L₃) + quadPoly (M.transpose * T * L₂) * (quadPoly L₁ * quadPoly L₃) +
        quadPoly (M.transpose * T * L₃) * (quadPoly L₁ * quadPoly L₂) := by
    simp only [Derivation.leibniz, contractDeriv_quadPoly M h₁, contractDeriv_quadPoly M h₂, contractDeriv_quadPoly M h₃, smul_eq_mul]
    ring
  rw [gaussianMoment_quadPoly_mul hT M 3, h, map_add, map_add]
  ring
private theorem quadMean_eq_trace {T : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ) :
    quadMean T M = 3 / 2 * Matrix.trace (M * T) := by
  simp only [quadMean, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show T a b = T b a from congrFun (congrFun hT b) a]
private theorem quadMean_chain_two {T K₀ K₁ : Matrix I I ℝ} (hT : T.IsSymm) (h₀ : K₀.IsSymm) :
    quadMean T (K₀.transpose * T * K₁) = 3 / 2 * Matrix.trace (K₀ * T * (K₁ * T)) := by
  rw [quadMean_eq_trace hT, h₀.eq]
  simp only [Matrix.mul_assoc]
private theorem quadMean_chain_three {T K₀ K₁ K₂ : Matrix I I ℝ} (hT : T.IsSymm) (h₀ : K₀.IsSymm)
    (h₁ : K₁.IsSymm) :
    quadMean T ((K₀.transpose * T * K₁).transpose * T * K₂) =
      3 / 2 * Matrix.trace (K₀ * T * (K₂ * T) * (K₁ * T)) := by
  rw [quadMean_eq_trace hT]
  simp only [Matrix.transpose_mul, h₀.eq, h₁.eq, hT.eq]
  rw [show K₁ * (T * K₀) * T * K₂ * T = (K₁ * T) * (K₀ * T * (K₂ * T)) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
private theorem quadMean_chain_four {T K₀ K₁ K₂ K₃ : Matrix I I ℝ} (hT : T.IsSymm) (h₀ : K₀.IsSymm)
    (h₁ : K₁.IsSymm) (h₂ : K₂.IsSymm) :
    quadMean T (((K₀.transpose * T * K₁).transpose * T * K₂).transpose * T * K₃) =
      3 / 2 * Matrix.trace (K₀ * T * (K₁ * T) * (K₃ * T) * (K₂ * T)) := by
  rw [quadMean_eq_trace hT]
  simp only [Matrix.transpose_mul, h₀.eq, h₁.eq, h₂.eq, hT.eq]
  rw [show K₂ * (T * (K₀ * T * K₁)) * T * K₃ * T = (K₂ * T) * (K₀ * T * (K₁ * T) * (K₃ * T)) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
end Forms
section Enumeration
variable {α : Type} [DecidableEq α]
private def partitionSum (S : Finset α) (F : Finset (Finset α) → ℝ) : ℝ :=
  ∑ π : Finpartition S, F π.parts
private theorem partitionSum_first (S : Finset α) (u : α) (hu : u ∈ S) (L : Finset (Finset α))
    (hL : S.powerset.filter (u ∈ ·) = L) (F : Finset (Finset α) → ℝ) :
    partitionSum S F = ∑ B ∈ L, partitionSum (S \ B) fun P => F (insert B P) := by
  rw [partitionSum, sum_finpartition_eq_sum_block_containing S u hu F, hL]
  rfl
private theorem partitionSum_empty (F : Finset (Finset α) → ℝ) : partitionSum ∅ F = F ∅ := by
  have hp : ∀ π : Finpartition (∅ : Finset α), π.parts = ∅ := by
    intro π
    apply Finset.eq_empty_of_forall_notMem
    intro J hJ
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hJ
    simpa using π.le hJ hx
  have hone : ∀ π π' : Finpartition (∅ : Finset α), π = π' := fun π π' =>
    Finpartition.ext (by rw [hp, hp])
  have : Unique (Finpartition (∅ : Finset α)) := ⟨⟨Finpartition.empty _⟩, fun π => hone _ _⟩
  rw [partitionSum, Fintype.sum_unique]
  simp [hp]
private theorem partitionSum_singleton (a : α) (F : Finset (Finset α) → ℝ) : partitionSum {a} F = F {{a}} := by
  rw [partitionSum_first {a} a (by simp) {{a}} (by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Finset.subset_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · simp at h
      · rfl
    · rintro rfl
      simp), Finset.sum_singleton, Finset.sdiff_self]
  rw [partitionSum_empty]
  simp
private theorem partitionSum_pair {a b : α} (h : a ≠ b) (F : Finset (Finset α) → ℝ) :
    partitionSum {a, b} F = F {{a}, {b}} + F {{a, b}} := by
  have hL : ({a, b} : Finset α).powerset.filter (a ∈ ·) = {{a}, {a, b}} := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, ha⟩
      by_cases hb : b ∈ B
      · right
        apply Finset.Subset.antisymm hs
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      · left
        ext y
        simp only [Finset.mem_singleton]
        constructor
        · intro hy
          rcases (by simpa using hs hy : y = a ∨ y = b) with rfl | rfl
          · rfl
          · exact absurd hy hb
        · rintro rfl
          exact ha
    · rintro (rfl | rfl)
      · simp
      · simp
  have hne : ({a} : Finset α) ≠ {a, b} := by
    intro he
    have : b ∈ ({a} : Finset α) := by rw [he]; simp
    have hba : b = a := by simpa using this
    exact h hba.symm
  rw [partitionSum_first {a, b} a (by simp) _ hL, Finset.sum_pair hne]
  have e1 : ({a, b} : Finset α) \ {a} = {b} := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h2⟩
      · exact absurd rfl h2
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, fun h' => h h'.symm⟩
  rw [e1, Finset.sdiff_self, partitionSum_singleton, partitionSum_empty]
  simp
end Enumeration
section Counts
private def cumulantWeight {n : ℕ} (m : Finset (Fin n) → ℝ) (P : Finset (Finset (Fin n))) : ℝ :=
  (-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) * ∏ J ∈ P, m J
private theorem cumulantWeight_sum_two (m : Finset (Fin 2) → ℝ) :
    partitionSum Finset.univ (cumulantWeight m) = m {0, 1} - m {0} * m {1} := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    partitionSum_pair (show (0 : Fin 2) ≠ 1 by decide)]
  simp (disch := decide) only [cumulantWeight, Finset.card_insert_of_notMem, Finset.card_singleton,
    Finset.prod_insert, Finset.prod_singleton]
  norm_num
  ring
private theorem cumulantWeight_sum_three (m : Finset (Fin 3) → ℝ) :
    partitionSum Finset.univ (cumulantWeight m) = m {0, 1, 2} - m {0} * m {1, 2} - m {1} * m {0, 2} - m {2} * m {0, 1}
      + 2 * (m {0} * m {1} * m {2}) := by
  rw [partitionSum_first Finset.univ 0 (by decide) {{0}, {0, 1}, {0, 2}, {0, 1, 2}} (by decide)]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  rw [show (Finset.univ : Finset (Fin 3)) \ {0} = {1, 2} by decide,
    show (Finset.univ : Finset (Fin 3)) \ {0, 1} = {2} by decide,
    show (Finset.univ : Finset (Fin 3)) \ {0, 2} = {1} by decide,
    show (Finset.univ : Finset (Fin 3)) \ {0, 1, 2} = ∅ by decide,
    partitionSum_pair (show (1 : Fin 3) ≠ 2 by decide), partitionSum_singleton, partitionSum_singleton, partitionSum_empty]
  simp (disch := decide) only [cumulantWeight, Finset.card_insert_of_notMem, Finset.card_singleton,
    Finset.card_empty, Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]
  norm_num
  ring
private theorem cumulantWeight_sum_four (m : Finset (Fin 4) → ℝ) :
    partitionSum Finset.univ (cumulantWeight m) = m {0, 1, 2, 3}
      - (m {0} * m {1, 2, 3} + m {1} * m {0, 2, 3} + m {2} * m {0, 1, 3} + m {3} * m {0, 1, 2})
      - (m {0, 1} * m {2, 3} + m {0, 2} * m {1, 3} + m {0, 3} * m {1, 2})
      + 2 * (m {0} * m {1} * m {2, 3} + m {0} * m {2} * m {1, 3} + m {0} * m {3} * m {1, 2}
        + m {1} * m {2} * m {0, 3} + m {1} * m {3} * m {0, 2} + m {2} * m {3} * m {0, 1})
      - 6 * (m {0} * m {1} * m {2} * m {3}) := by
  have h3 : ∀ F : Finset (Finset (Fin 4)) → ℝ, partitionSum {1, 2, 3} F =
      F {{1}, {2}, {3}} + F {{1}, {2, 3}} + F {{1, 2}, {3}} + F {{1, 3}, {2}} + F {{1, 2, 3}} := by
    intro F
    rw [partitionSum_first {1, 2, 3} 1 (by decide) {{1}, {1, 2}, {1, 3}, {1, 2, 3}} (by decide)]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    rw [show ({1, 2, 3} : Finset (Fin 4)) \ {1} = {2, 3} by decide,
      show ({1, 2, 3} : Finset (Fin 4)) \ {1, 2} = {3} by decide,
      show ({1, 2, 3} : Finset (Fin 4)) \ {1, 3} = {2} by decide,
      show ({1, 2, 3} : Finset (Fin 4)) \ {1, 2, 3} = ∅ by decide,
      partitionSum_pair (show (2 : Fin 4) ≠ 3 by decide), partitionSum_singleton, partitionSum_singleton, partitionSum_empty]
    simp only [insert_empty_eq]
    ring
  rw [partitionSum_first Finset.univ 0 (by decide)
    {{0}, {0, 1}, {0, 2}, {0, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 1, 2, 3}} (by decide)]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  rw [show (Finset.univ : Finset (Fin 4)) \ {0} = {1, 2, 3} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 1} = {2, 3} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 2} = {1, 3} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 3} = {1, 2} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 1, 2} = {3} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 1, 3} = {2} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 2, 3} = {1} by decide,
    show (Finset.univ : Finset (Fin 4)) \ {0, 1, 2, 3} = ∅ by decide,
    h3, partitionSum_pair (show (2 : Fin 4) ≠ 3 by decide), partitionSum_pair (show (1 : Fin 4) ≠ 3 by decide),
    partitionSum_pair (show (1 : Fin 4) ≠ 2 by decide), partitionSum_singleton, partitionSum_singleton, partitionSum_singleton, partitionSum_empty]
  simp (disch := decide) only [cumulantWeight, insert_empty_eq, Finset.card_insert_of_notMem, Finset.card_singleton,
    Finset.prod_insert, Finset.prod_singleton]
  norm_num
  ring
end Counts
section Exact
variable {I : Type} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false
private def formMoment (T : Matrix I I ℝ) {n : ℕ} (K : Fin n → Matrix I I ℝ) (J : Finset (Fin n)) : ℝ :=
  gaussianMoment (colourCov T) J.card (∏ l ∈ J, quadPoly (K l))
private theorem formMoment_singleton (T : Matrix I I ℝ) (hT : T.IsSymm) {n : ℕ} (K : Fin n → Matrix I I ℝ)
    (i : Fin n) : formMoment T K {i} = quadMean T (K i) := by
  simp [formMoment, gaussianMoment_one_form hT]
private theorem formMoment_pair (T : Matrix I I ℝ) (hT : T.IsSymm) {n : ℕ} (K : Fin n → Matrix I I ℝ)
    (hK : ∀ i, (K i).IsSymm) {i j : Fin n} (h : i ≠ j) :
    formMoment T K {i, j} = quadMean T (K i) * quadMean T (K j) + quadMean T ((K i).transpose * T * K j) := by
  rw [formMoment, Finset.card_pair h, Finset.prod_pair h, gaussianMoment_two_forms hT _ (hK j)]
private theorem gaussianMoment_three_forms_expanded {T L₁ L₂ : Matrix I I ℝ} (hT : T.IsSymm) (M : Matrix I I ℝ)
    (h₁ : L₁.IsSymm) (h₂ : L₂.IsSymm) :
    gaussianMoment (colourCov T) 3 (quadPoly M * (quadPoly L₁ * quadPoly L₂)) =
      quadMean T M * (quadMean T L₁ * quadMean T L₂ + quadMean T (L₁.transpose * T * L₂)) +
        (quadMean T (M.transpose * T * L₁) * quadMean T L₂ +
          quadMean T ((M.transpose * T * L₁).transpose * T * L₂)) +
        (quadMean T (M.transpose * T * L₂) * quadMean T L₁ +
          quadMean T ((M.transpose * T * L₂).transpose * T * L₁)) := by
  rw [gaussianMoment_three_forms hT M h₁ h₂, gaussianMoment_two_forms hT _ h₂, gaussianMoment_two_forms hT _ h₂, gaussianMoment_two_forms hT _ h₁]
private theorem formMoment_triple (T : Matrix I I ℝ) (hT : T.IsSymm) {n : ℕ} (K : Fin n → Matrix I I ℝ)
    (hK : ∀ i, (K i).IsSymm) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    formMoment T K {i, j, k} =
      quadMean T (K i) * (quadMean T (K j) * quadMean T (K k) + quadMean T ((K j).transpose * T * K k)) +
        (quadMean T ((K i).transpose * T * K j) * quadMean T (K k) +
          quadMean T (((K i).transpose * T * K j).transpose * T * K k)) +
        (quadMean T ((K i).transpose * T * K k) * quadMean T (K j) +
          quadMean T (((K i).transpose * T * K k).transpose * T * K j)) := by
  have hn : i ∉ ({j, k} : Finset (Fin n)) := by simp [hij, hik]
  rw [formMoment, Finset.card_insert_of_notMem hn, Finset.card_pair hjk, Finset.prod_insert hn,
    Finset.prod_pair hjk, gaussianMoment_three_forms_expanded hT _ (hK j) (hK k)]
private theorem kernelCycleTrace_two (K : Fin 2 → Matrix I I ℝ) (T : Matrix I I ℝ)
    (s : Equiv.Perm (Fin 2)) (h0 : s 0 = 0) (h1 : s 1 = 1) :
    kernelCycleTrace K T s = Matrix.trace (K 0 * T * (K 1 * T)) := by
  simp only [kernelCycleTrace, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  simp [h0, h1]
end Exact
section ExactCycles
variable {I : Type} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false
private theorem permsFixingZero_two : (Finset.univ.filter fun s : Equiv.Perm (Fin 2) => s 0 = 0) = {1} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h0
    have h1 : s 1 ≠ 0 := by
      rw [← h0]
      exact fun h => absurd (s.injective h) (by decide)
    have h1' : s 1 = 1 := by
      revert h1
      generalize s 1 = a
      revert a
      decide
    ext i
    fin_cases i
    · simp [h0]
    · simp [h1']
  · rintro rfl
    rfl
private theorem permsFixingZero_three_aux : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ t ∈ ([1, Equiv.swap 1 2] : List (Equiv.Perm (Fin 3))), t 1 = a ∧ t 2 = b := by
  decide
private theorem permsFixingZero_three : (Finset.univ.filter fun s : Equiv.Perm (Fin 3) => s 0 = 0) =
    ({1, Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 3))) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h0
    have hne : ∀ i j : Fin 3, i ≠ j → s i ≠ s j := fun i j hij h => hij (s.injective h)
    obtain ⟨t, ht, h1, h2⟩ := permsFixingZero_three_aux (s 1) (s 2)
      (by rw [← h0]; exact hne _ _ (by decide)) (by rw [← h0]; exact hne _ _ (by decide))
      (hne _ _ (by decide))
    have ht0 : ∀ t ∈ ([1, Equiv.swap 1 2] : List (Equiv.Perm (Fin 3))), t 0 = 0 := by decide
    have : s = t := by
      ext i
      fin_cases i
      · simp [h0, ht0 t ht]
      · simp [h1]
      · simp [h2]
    subst this
    simpa using ht
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> decide
private theorem permsFixingZero_four_aux : ∀ a b c : Fin 4, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
    ∃ t ∈ ([1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3, Equiv.swap 1 2 * Equiv.swap 2 3,
      Equiv.swap 2 3 * Equiv.swap 1 2] : List (Equiv.Perm (Fin 4))), t 1 = a ∧ t 2 = b ∧ t 3 = c := by
  decide
private theorem permsFixingZero_four : (Finset.univ.filter fun s : Equiv.Perm (Fin 4) => s 0 = 0) =
    ({1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3, Equiv.swap 1 2 * Equiv.swap 2 3,
      Equiv.swap 2 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h0
    have hne : ∀ i j : Fin 4, i ≠ j → s i ≠ s j := fun i j hij h => hij (s.injective h)
    obtain ⟨t, ht, h1, h2, h3⟩ := permsFixingZero_four_aux (s 1) (s 2) (s 3)
      (by rw [← h0]; exact hne _ _ (by decide)) (by rw [← h0]; exact hne _ _ (by decide))
      (by rw [← h0]; exact hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))
    have ht0 : ∀ t ∈ ([1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3,
      Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.swap 2 3 * Equiv.swap 1 2] :
        List (Equiv.Perm (Fin 4))), t 0 = 0 := by decide
    have : s = t := by
      ext i
      fin_cases i
      · simp [h0, ht0 t ht]
      · simp [h1]
      · simp [h2]
      · simp [h3]
    subst this
    simpa using ht
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem kernelCycleTrace_three (K : Fin 3 → Matrix I I ℝ) (T : Matrix I I ℝ)
    (s : Equiv.Perm (Fin 3)) (a b : Fin 3) (h0 : s 0 = 0) (h1 : s 1 = a) (h2 : s 2 = b) :
    kernelCycleTrace K T s = Matrix.trace (K 0 * T * (K a * T) * (K b * T)) := by
  simp only [kernelCycleTrace, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  simp [h0, h1, h2, Matrix.mul_assoc]
private theorem kernelCycleTrace_four (K : Fin 4 → Matrix I I ℝ) (T : Matrix I I ℝ)
    (s : Equiv.Perm (Fin 4)) (a b c : Fin 4) (h0 : s 0 = 0) (h1 : s 1 = a) (h2 : s 2 = b)
    (h3 : s 3 = c) :
    kernelCycleTrace K T s = Matrix.trace (K 0 * T * (K a * T) * (K b * T) * (K c * T)) := by
  simp only [kernelCycleTrace, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  simp [h0, h1, h2, h3, Matrix.mul_assoc]
private theorem cumulant_eq_cyclicTraceSum_two (T : Matrix I I ℝ) (hT : T.IsSymm) (K : Fin 2 → Matrix I I ℝ)
    (hK : ∀ i, (K i).IsSymm) : partitionSum Finset.univ (cumulantWeight (formMoment T K)) = cyclicTraceSum K T := by
  have hs : cyclicTraceSum K T = quadMean T ((K 0).transpose * T * K 1) := by
    rw [quadMean_chain_two hT (hK 0), cyclicTraceSum, permsFixingZero_two, Finset.sum_singleton]
    rw [kernelCycleTrace_two K T 1 rfl rfl]
  rw [cumulantWeight_sum_two, formMoment_pair T hT K hK (show (0 : Fin 2) ≠ 1 by decide), formMoment_singleton T hT, formMoment_singleton T hT, hs]
  ring
private theorem cumulant_eq_cyclicTraceSum_three (T : Matrix I I ℝ) (hT : T.IsSymm) (K : Fin 3 → Matrix I I ℝ)
    (hK : ∀ i, (K i).IsSymm) : partitionSum Finset.univ (cumulantWeight (formMoment T K)) = cyclicTraceSum K T := by
  have hs : cyclicTraceSum K T = quadMean T (((K 0).transpose * T * K 1).transpose * T * K 2) +
      quadMean T (((K 0).transpose * T * K 2).transpose * T * K 1) := by
    rw [quadMean_chain_three hT (hK 0) (hK 1), quadMean_chain_three hT (hK 0) (hK 2), cyclicTraceSum, permsFixingZero_three,
      Finset.sum_pair (by decide), kernelCycleTrace_three K T 1 1 2 rfl rfl rfl,
      kernelCycleTrace_three K T (Equiv.swap 1 2) 2 1 (by decide) (by decide) (by decide)]
    ring
  rw [cumulantWeight_sum_three,
    formMoment_triple T hT K hK (show (0 : Fin 3) ≠ 1 by decide) (by decide) (by decide),
    formMoment_pair T hT K hK (show (1 : Fin 3) ≠ 2 by decide),
    formMoment_pair T hT K hK (show (0 : Fin 3) ≠ 2 by decide),
    formMoment_pair T hT K hK (show (0 : Fin 3) ≠ 1 by decide),
    formMoment_singleton T hT, formMoment_singleton T hT, formMoment_singleton T hT, hs]
  ring
private theorem cumulant_eq_cyclicTraceSum_four (T : Matrix I I ℝ) (hT : T.IsSymm) (K : Fin 4 → Matrix I I ℝ)
    (hK : ∀ i, (K i).IsSymm) : partitionSum Finset.univ (cumulantWeight (formMoment T K)) = cyclicTraceSum K T := by
  have hs : cyclicTraceSum K T =
      quadMean T ((((K 0).transpose * T * K 1).transpose * T * K 2).transpose * T * K 3) +
      quadMean T ((((K 0).transpose * T * K 1).transpose * T * K 3).transpose * T * K 2) +
      quadMean T ((((K 0).transpose * T * K 2).transpose * T * K 1).transpose * T * K 3) +
      quadMean T ((((K 0).transpose * T * K 2).transpose * T * K 3).transpose * T * K 1) +
      quadMean T ((((K 0).transpose * T * K 3).transpose * T * K 1).transpose * T * K 2) +
      quadMean T ((((K 0).transpose * T * K 3).transpose * T * K 2).transpose * T * K 1) := by
    rw [quadMean_chain_four hT (hK 0) (hK 1) (hK 2), quadMean_chain_four hT (hK 0) (hK 1) (hK 3),
      quadMean_chain_four hT (hK 0) (hK 2) (hK 1), quadMean_chain_four hT (hK 0) (hK 2) (hK 3),
      quadMean_chain_four hT (hK 0) (hK 3) (hK 1), quadMean_chain_four hT (hK 0) (hK 3) (hK 2), cyclicTraceSum, permsFixingZero_four]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    rw [kernelCycleTrace_four K T 1 1 2 3 rfl rfl rfl rfl,
      kernelCycleTrace_four K T (Equiv.swap 1 2) 2 1 3 (by decide) (by decide) (by decide) (by decide),
      kernelCycleTrace_four K T (Equiv.swap 1 3) 3 2 1 (by decide) (by decide) (by decide) (by decide),
      kernelCycleTrace_four K T (Equiv.swap 2 3) 1 3 2 (by decide) (by decide) (by decide) (by decide),
      kernelCycleTrace_four K T (Equiv.swap 1 2 * Equiv.swap 2 3) 2 3 1 (by decide) (by decide)
        (by decide) (by decide),
      kernelCycleTrace_four K T (Equiv.swap 2 3 * Equiv.swap 1 2) 3 1 2 (by decide) (by decide)
        (by decide) (by decide)]
    ring
  have e4 : formMoment T K {0, 1, 2, 3} =
      gaussianMoment (colourCov T) 4 (quadPoly (K 0) * (quadPoly (K 1) * (quadPoly (K 2) * quadPoly (K 3)))) := by
    rw [formMoment, show ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 by decide]
    simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton]
  rw [cumulantWeight_sum_four, e4, gaussianMoment_four_forms hT (K 0) (hK 1) (hK 2) (hK 3), gaussianMoment_three_forms_expanded hT (K 1) (hK 2) (hK 3),
    gaussianMoment_three_forms_expanded hT ((K 0).transpose * T * K 1) (hK 2) (hK 3),
    gaussianMoment_three_forms_expanded hT ((K 0).transpose * T * K 2) (hK 1) (hK 3),
    gaussianMoment_three_forms_expanded hT ((K 0).transpose * T * K 3) (hK 1) (hK 2),
    formMoment_triple T hT K hK (show (1 : Fin 4) ≠ 2 by decide) (by decide) (by decide),
    formMoment_triple T hT K hK (show (0 : Fin 4) ≠ 2 by decide) (by decide) (by decide),
    formMoment_triple T hT K hK (show (0 : Fin 4) ≠ 1 by decide) (show (0 : Fin 4) ≠ 3 by decide) (by decide),
    formMoment_triple T hT K hK (show (0 : Fin 4) ≠ 1 by decide) (show (0 : Fin 4) ≠ 2 by decide) (by decide),
    formMoment_pair T hT K hK (show (0 : Fin 4) ≠ 1 by decide),
    formMoment_pair T hT K hK (show (0 : Fin 4) ≠ 2 by decide),
    formMoment_pair T hT K hK (show (0 : Fin 4) ≠ 3 by decide),
    formMoment_pair T hT K hK (show (1 : Fin 4) ≠ 2 by decide),
    formMoment_pair T hT K hK (show (1 : Fin 4) ≠ 3 by decide),
    formMoment_pair T hT K hK (show (2 : Fin 4) ≠ 3 by decide),
    formMoment_singleton T hT, formMoment_singleton T hT, formMoment_singleton T hT, formMoment_singleton T hT, hs]
  ring
end ExactCycles
section Analysis
open MeasureTheory
set_option linter.unusedSectionVars false
variable {Ω : Type} [MeasurableSpace Ω] {V : Type}
private theorem aeval_measurable_bounded (p : Ω → V → ℝ) (hm : ∀ v, Measurable fun ω => p ω v)
    (hb : ∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C) (f : MvPolynomial V ℝ) :
    Measurable (fun ω => aeval (p ω) f) ∧ ∃ C : ℝ, ∀ ω, |aeval (p ω) f| ≤ C := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    refine ⟨?_, |r|, fun ω => ?_⟩
    · simp
    · simp
  | add f g hf hg =>
    obtain ⟨mf, Cf, hCf⟩ := hf
    obtain ⟨mg, Cg, hCg⟩ := hg
    refine ⟨?_, Cf + Cg, fun ω => ?_⟩
    · simp only [map_add]
      exact mf.add mg
    · rw [map_add]
      exact (abs_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))
  | mul_X f v hf =>
    obtain ⟨mf, Cf, hCf⟩ := hf
    obtain ⟨Cv, hCv⟩ := hb v
    refine ⟨?_, |Cf| * |Cv|, fun ω => ?_⟩
    · simp only [map_mul, aeval_X]
      exact mf.mul (hm v)
    · rw [map_mul, aeval_X, abs_mul]
      exact mul_le_mul ((hCf ω).trans (le_abs_self _)) ((hCv ω).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
private theorem integrable_indicator_aeval (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (p : Ω → V → ℝ) (hm : ∀ v, Measurable fun ω => p ω v)
    (hb : ∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C) (f : MvPolynomial V ℝ) :
    Integrable (A.indicator fun ω => aeval (p ω) f) μ := by
  obtain ⟨m, C, hC⟩ := aeval_measurable_bounded p hm hb f
  exact (Integrable.of_bound m.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC ω)).indicator hA
private def eventMean (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (p : Ω → V → ℝ) (hm : ∀ v, Measurable fun ω => p ω v)
    (hb : ∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C) : MvPolynomial V ℝ →ₗ[ℝ] ℝ where
  toFun f := ∫ ω, A.indicator (fun ω => aeval (p ω) f) ω ∂μ
  map_add' f g := by
    rw [← integral_add (integrable_indicator_aeval μ hA p hm hb f) (integrable_indicator_aeval μ hA p hm hb g)]
    congr 1
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
private theorem eventMean_apply (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (p : Ω → V → ℝ) (hm : ∀ v, Measurable fun ω => p ω v)
    (hb : ∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C) (f : MvPolynomial V ℝ) :
    eventMean μ hA p hm hb f = ∫ ω, A.indicator (fun ω => aeval (p ω) f) ω ∂μ := rfl
variable {I : Type} [Fintype I] [DecidableEq I]
private def kernelSize (K : Matrix I I ℝ) : ℝ := (3 / 2) * ∑ a, ∑ b, |K a b|
private theorem kernelSize_nonneg (K : Matrix I I ℝ) : 0 ≤ kernelSize K := by
  unfold kernelSize
  positivity
private theorem abs_apply_quadPoly_word_le (Λ : MvPolynomial (I × Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ) (ε : ℝ)
    (h : ∀ w : List (I × Fin 3), w.length = N →
      |Λ (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod| ≤ ε) :
    ∀ (ℓ : List (Matrix I I ℝ)) (u : List (I × Fin 3)), u.length + 2 * ℓ.length = N →
      |Λ ((ℓ.map quadPoly).prod * (u.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod)| ≤
        (ℓ.map kernelSize).prod * ε := by
  intro ℓ
  induction ℓ with
  | nil =>
    intro u hu
    simpa using h u (by simpa using hu)
  | cons K ℓ ih =>
    intro u hu
    obtain ⟨P, hP⟩ : ∃ P, P = (ℓ.map quadPoly).prod := ⟨_, rfl⟩
    have e : ((K :: ℓ).map quadPoly).prod * (u.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod =
        ∑ a, ∑ b, (K a b / 2) • ∑ e : Fin 3, P *
          (((a, e) :: (b, e) :: u).map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod := by
      simp only [List.map_cons, List.prod_cons, quadPoly, Finset.sum_mul, smul_mul_assoc, ← hP]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    obtain ⟨β, hβ⟩ : ∃ β, β = (ℓ.map kernelSize).prod * ε := ⟨_, rfl⟩
    have hb : ∀ a b e, |Λ (P *
        (((a, e) :: (b, e) :: u).map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod)| ≤ β := by
      intro a b e
      rw [hP, hβ]
      refine ih _ ?_
      simp only [List.length_cons] at hu ⊢
      omega
    have hterm : ∀ a b, |Λ ((K a b / 2) • ∑ e : Fin 3, P *
        (((a, e) :: (b, e) :: u).map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod)| ≤
        (3 / 2) * |K a b| * β := by
      intro a b
      rw [map_smul, smul_eq_mul, abs_mul, map_sum, abs_div, abs_two]
      have h3 : |∑ e : Fin 3, Λ (P *
          (((a, e) :: (b, e) :: u).map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod)| ≤
          3 * β := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun e _ => hb a b e).trans ?_
        simp
      calc |K a b| / 2 * _ ≤ |K a b| / 2 * (3 * β) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    rw [e, map_sum]
    have hfin : ((K :: ℓ).map kernelSize).prod * ε = kernelSize K * β := by
      rw [hβ, List.map_cons, List.prod_cons, mul_assoc]
    rw [hfin]
    calc _ ≤ ∑ a, |Λ (∑ b, (K a b / 2) • ∑ e : Fin 3, P *
          (((a, e) :: (b, e) :: u).map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, (3 / 2) * |K a b| * β := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [map_sum]
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hterm a b)
      _ = kernelSize K * β := by
          simp only [kernelSize, Finset.mul_sum, Finset.sum_mul]
private theorem abs_apply_prod_quadPoly_le (Λ : MvPolynomial (I × Fin 3) ℝ →ₗ[ℝ] ℝ) {n : ℕ}
    (K : Fin n → Matrix I I ℝ) (J : Finset (Fin n)) (ε : ℝ)
    (h : ∀ w : List (I × Fin 3), w.length = 2 * J.card →
      |Λ (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod| ≤ ε) :
    |Λ (∏ l ∈ J, quadPoly (K l))| ≤ (∏ l ∈ J, kernelSize (K l)) * ε := by
  have := abs_apply_quadPoly_word_le Λ (2 * J.card) ε h (J.toList.map K) [] (by simp)
  simpa [List.map_map, Finset.prod_map_toList] using this
open Classical in
private def pairingBound (D : ℝ) (r : ℕ) : ℝ :=
  ∑ _π : Finpartition (Finset.univ : Finset (Fin r)), D ^ r
private theorem pairingBound_nonneg {D : ℝ} (hD : 1 ≤ D) (r : ℕ) : 0 ≤ pairingBound D r := by
  unfold pairingBound
  have : 0 ≤ D := by linarith
  positivity
private theorem abs_wickPairingSum_le {r : ℕ} (G : Fin r → Fin r → ℝ) (D : ℝ) (hD : 1 ≤ D)
    (hG : ∀ i j, |G i j| ≤ D) : |wickPairingSum G| ≤ pairingBound D r := by
  rw [wickPairingSum, pairingBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  split_ifs with h
  · rw [Finset.abs_prod]
    calc _ ≤ ∏ _B ∈ π.parts, D := by
          refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun B _ => ?_
          split_ifs
          · exact hG _ _
          · simpa using hD
      _ = D ^ π.parts.card := by simp
      _ ≤ D ^ r := pow_le_pow_right₀ hD (by simpa using π.card_parts_le_card)
  · simp only [abs_zero]
    have : 0 ≤ D := by linarith
    positivity
abbrev _root_.YangMills.DeltaSharedProofs.p500570 := @abs_wickPairingSum_le
private theorem gaussianMoment_word {W : Type} [Fintype W] [DecidableEq W] (c : W → W → ℝ)
    (hc : ∀ u v, c u v = c v u) {r : ℕ} (w : Fin r → W) (m : ℕ) (hr : r = 2 * m) :
    gaussianMoment c m (∏ i, (X (w i) : MvPolynomial W ℝ)) = wickPairingSum fun i j => c (w i) (w j) := by
  rw [gaussianMoment_prod_X c hc w m Finset.univ (by simp [hr])]
  simp only [pairingSumOn, wickPairingSum, pairWeight]
private theorem list_prod_X_eq {W : Type} (w : List W) :
    (w.map (X : W → MvPolynomial W ℝ)).prod = ∏ i : Fin w.length, (X (w.get i) : MvPolynomial W ℝ) :=
  (Fin.prod_univ_fun_getElem w X).symm
private theorem abs_prod_le_pow_mul {ι : Type} (P : Finset ι) (a s : ι → ℝ) (c : ℝ)
    (h : ∀ j ∈ P, |a j| ≤ c * s j) : |∏ j ∈ P, a j| ≤ c ^ P.card * ∏ j ∈ P, s j := by
  rw [Finset.abs_prod]
  calc _ ≤ ∏ j ∈ P, (c * s j) := Finset.prod_le_prod (fun _ _ => abs_nonneg _) h
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
private theorem abs_prod_sub_prod_le {ι : Type} [DecidableEq ι] (P : Finset ι) (a b s : ι → ℝ) (c ε : ℝ)
    (hc : 1 ≤ c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : ∀ j ∈ P, 0 ≤ s j)
    (h1 : ∀ j ∈ P, |a j - b j| ≤ s j * ε) (h2 : ∀ j ∈ P, |b j| ≤ c * s j) :
    |∏ j ∈ P, a j - ∏ j ∈ P, b j| ≤ P.card * (2 * c) ^ P.card * (∏ j ∈ P, s j) * ε := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert j P hj ih =>
    have hs' : ∀ i ∈ P, 0 ≤ s i := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have ih' := ih hs' (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h2 i (Finset.mem_insert_of_mem hi))
    have hA : |∏ i ∈ P, a i| ≤ (2 * c) ^ P.card * ∏ i ∈ P, s i := by
      refine abs_prod_le_pow_mul P a s (2 * c) fun i hi => ?_
      have e1 := h1 i (Finset.mem_insert_of_mem hi)
      have e2 := h2 i (Finset.mem_insert_of_mem hi)
      have e3 := hs' i hi
      have e4 : |a i| ≤ |a i - b i| + |b i| := by
        simpa using abs_add_le (a i - b i) (b i)
      have e5 : s i * ε ≤ s i * c := mul_le_mul_of_nonneg_left (hε1.trans hc) e3
      nlinarith
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj,
      Finset.card_insert_of_notMem hj]
    have hsj := hs j (Finset.mem_insert_self _ _)
    have hj1 := h1 j (Finset.mem_insert_self _ _)
    have hj2 := h2 j (Finset.mem_insert_self _ _)
    obtain ⟨A, hAd⟩ : ∃ A, A = ∏ i ∈ P, a i := ⟨_, rfl⟩
    obtain ⟨B', hBd⟩ : ∃ B', B' = ∏ i ∈ P, b i := ⟨_, rfl⟩
    obtain ⟨S, hSd⟩ : ∃ S, S = ∏ i ∈ P, s i := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hSd ▸ Finset.prod_nonneg hs'
    rw [← hAd, ← hSd] at hA
    rw [← hAd, ← hBd, ← hSd] at ih'
    rw [← hAd, ← hBd, ← hSd]
    obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (P.card : ℝ) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (2 * c) ^ P.card := ⟨_, rfl⟩
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    rw [← hQ] at hA ih'
    rw [← hn] at ih'
    have step : |a j * A - b j * B'| ≤ |a j - b j| * |A| + |b j| * |A - B'| := by
      have : a j * A - b j * B' = (a j - b j) * A + b j * (A - B') := by ring
      rw [this, ← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    have t1 : |a j - b j| * |A| ≤ (s j * ε) * (Q * S) :=
      mul_le_mul hj1 hA (abs_nonneg _) (by positivity)
    have t2 : |b j| * |A - B'| ≤ (c * s j) * (n * Q * S * ε) :=
      mul_le_mul hj2 ih' (abs_nonneg _) (by positivity)
    have hE : 0 ≤ Q * S * s j * ε := by positivity
    have fin : (s j * ε) * (Q * S) + (c * s j) * (n * Q * S * ε) ≤
        (n + 1) * (2 * c * Q) * (s j * S) * ε := by
      have : (n + 1) * (2 * c * Q) * (s j * S) * ε - ((s j * ε) * (Q * S) + (c * s j) * (n * Q * S * ε)) =
          (Q * S * s j * ε) * (2 * c * (n + 1) - 1 - c * n) := by ring
      have h3 : 0 ≤ 2 * c * (n + 1) - 1 - c * n := by nlinarith
      have := mul_nonneg hE h3
      linarith
    calc _ ≤ _ := step
      _ ≤ _ := add_le_add t1 t2
      _ ≤ _ := fin
      _ = _ := by rw [hn, hQ]; push_cast; ring
private theorem quadPoly_smul (c : ℝ) (K : Matrix I I ℝ) : quadPoly (c • K) = c • quadPoly K := by
  simp only [quadPoly, Finset.smul_sum, smul_smul, Matrix.smul_apply, smul_eq_mul, mul_div_assoc]
private theorem list_prod_ofFn_smul (c : ℝ) : ∀ (n : ℕ) (f : Fin n → Matrix I I ℝ),
    (List.ofFn fun i => c • f i).prod = c ^ n • (List.ofFn f).prod := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro f
    simp only [List.ofFn_succ, List.prod_cons, ih, smul_mul_smul_comm, pow_succ']
private theorem cyclicTraceSum_smul {q : ℕ} (c : ℝ) (κ : Fin (q + 1) → Matrix I I ℝ)
    (T : Matrix I I ℝ) :
    cyclicTraceSum (fun i => c • κ i) T = c ^ (q + 1) * cyclicTraceSum κ T := by
  have h : ∀ s, kernelCycleTrace (fun i => c • κ i) T s = c ^ (q + 1) * kernelCycleTrace κ T s := by
    intro s
    simp only [kernelCycleTrace, Matrix.smul_mul]
    rw [@list_prod_ofFn_smul I _ (fun a b => Classical.propDecidable (a = b)), Matrix.trace_smul,
      smul_eq_mul]
  simp only [cyclicTraceSum, h, ← Finset.mul_sum]
  ring
private theorem cumulant_eq_cyclicTraceSum (q : ℕ) (h1 : 1 ≤ q) (h3 : q ≤ 3) (T : Matrix I I ℝ) (hT : T.IsSymm)
    (K : Fin (q + 1) → Matrix I I ℝ) (hK : ∀ i, (K i).IsSymm) :
    partitionSum Finset.univ (cumulantWeight (formMoment T K)) = cyclicTraceSum K T := by
  interval_cases q
  · exact cumulant_eq_cyclicTraceSum_two T hT K hK
  · exact cumulant_eq_cyclicTraceSum_three T hT K hK
  · exact cumulant_eq_cyclicTraceSum_four T hT K hK
end Analysis
section Main
open MeasureTheory
set_option linter.unusedSectionVars false
private theorem cumulant_sub_gaussian_le (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (B : ℝ) : ∃ C : ℝ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
      (I : Type) [Fintype I] [DecidableEq I] (p : Ω → I × Fin 3 → ℝ) (T : Matrix I I ℝ) (x ε : ℝ)
      (κ : Fin (q + 1) → Matrix I I ℝ),
      MeasurableSet A → (∀ i, (κ i).IsSymm) → (∀ v, Measurable fun ω => p ω v) →
      (∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C) → 1 ≤ x → T.IsSymm → (∀ a b, |T a b| ≤ B) → 0 ≤ ε → ε ≤ 1 →
      (∀ (r : ℕ) (w : Fin r → I × Fin 3), r ≤ 2 * (q + 1) →
        |∫ ω, A.indicator (fun ω => ∏ i, p ω (w i)) ω ∂μ -
          x ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' => colourCov T (w i) (w i')| ≤ ε) →
      |(∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
          (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
            ∏ J ∈ π.parts, ∫ ω, ∏ l ∈ J, A.indicator (fun ω => aeval (p ω) (quadPoly (κ l))) ω ∂μ) -
        x ^ (-((q : ℝ) + 1)) * cyclicTraceSum κ T| ≤
        C * (∏ i, ∑ a, ∑ b, |κ i a b|) * ε := by
  obtain ⟨D, hDd⟩ : ∃ D, D = |B| + 1 := ⟨_, rfl⟩
  have hD : 1 ≤ D := by rw [hDd]; linarith [abs_nonneg B]
  obtain ⟨Dq, hDq⟩ : ∃ Dq, Dq = 1 + ∑ m ∈ Finset.range (q + 2), pairingBound D (2 * m) := ⟨_, rfl⟩
  have hDq1 : 1 ≤ Dq := by
    rw [hDq]
    have := Finset.sum_nonneg fun m (_ : m ∈ Finset.range (q + 2)) =>
      pairingBound_nonneg hD (2 * m)
    linarith
  have hDqw : ∀ m, m ≤ q + 1 → pairingBound D (2 * m) ≤ Dq := by
    intro m hm
    have := Finset.single_le_sum (f := fun m => pairingBound D (2 * m))
      (fun m (_ : m ∈ Finset.range (q + 2)) => pairingBound_nonneg hD (2 * m))
      (Finset.mem_range.2 (by omega : m < q + 2))
    rw [hDq]
    linarith
  refine ⟨(∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
    ((π.parts.card - 1).factorial : ℝ) * (π.parts.card * (2 * Dq) ^ π.parts.card)) *
      (3 / 2) ^ (q + 1), ?_⟩
  intro Ω _ μ _ A I _ _ p T x ε κ hA hκ hm hb hx hT hTB hε0 hε1 hmom
  have hx0 : 0 < x := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = eventMean μ hA p hm hb := ⟨_, rfl⟩
  have hLa : ∀ f, L f = ∫ ω, A.indicator (fun ω => aeval (p ω) f) ω ∂μ := by
    intro f
    rw [hL, eventMean_apply]
  obtain ⟨mA, hmA⟩ : ∃ mA : Finset (Fin (q + 1)) → ℝ, mA = fun J =>
    ∫ ω, ∏ l ∈ J, A.indicator (fun ω => aeval (p ω) (quadPoly (κ l))) ω ∂μ := ⟨_, rfl⟩
  obtain ⟨mG, hmG⟩ : ∃ mG : Finset (Fin (q + 1)) → ℝ, mG = fun J =>
    (x⁻¹) ^ J.card * gaussianMoment (colourCov T) J.card (∏ l ∈ J, quadPoly (κ l)) := ⟨_, rfl⟩
  have hAL : ∀ J : Finset (Fin (q + 1)), J.Nonempty → mA J = L (∏ l ∈ J, quadPoly (κ l)) := by
    intro J hJ
    rw [hLa, hmA]
    simp only
    congr 1
    funext ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω, map_prod]
    · simp only [Set.indicator_of_notMem hω]
      obtain ⟨l, hl⟩ := hJ
      exact Finset.prod_eq_zero hl rfl
  have hpair : ∀ (m : ℕ) (w : List (I × Fin 3)), w.length = 2 * m →
      wickPairingSum (fun i i' => colourCov T (w.get i) (w.get i')) =
        gaussianMoment (colourCov T) m (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod := by
    intro m w hw
    rw [list_prod_X_eq, gaussianMoment_word (colourCov T) (colourCov_symm hT) w.get m hw]
  have hword : ∀ m, m ≤ q + 1 → ∀ w : List (I × Fin 3), w.length = 2 * m →
      |L (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod -
        (x⁻¹) ^ m * gaussianMoment (colourCov T) m (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod| ≤ ε := by
    intro m hmq w hw
    have h := hmom w.length w.get (by omega)
    have e1 : ∫ ω, A.indicator (fun ω => ∏ i, p ω (w.get i)) ω ∂μ =
        L (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod := by
      rw [hLa]
      congr 1
      funext ω
      congr 1
      funext ω'
      rw [list_prod_X_eq, map_prod]
      simp only [aeval_X]
    have e2 : x ^ (-(w.length : ℝ) / 2) = (x⁻¹) ^ m := by
      have : -(w.length : ℝ) / 2 = -(m : ℝ) := by
        rw [hw]
        push_cast
        ring
      rw [this, Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
    rw [e1, e2, hpair m w hw] at h
    exact h
  have hxm : ∀ m : ℕ, (x⁻¹) ^ m ≤ 1 := fun m =>
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hx)
  have hxm0 : ∀ m : ℕ, 0 ≤ (x⁻¹) ^ m := fun m => by positivity
  have hgword : ∀ m (w : List (I × Fin 3)), w.length = 2 * m →
      |(x⁻¹) ^ m * gaussianMoment (colourCov T) m (w.map (X : I × Fin 3 → MvPolynomial (I × Fin 3) ℝ)).prod| ≤
        pairingBound D (2 * m) := by
    intro m w hw
    rw [← hpair m w hw, abs_mul, abs_of_nonneg (hxm0 m)]
    have hb' : |wickPairingSum fun i i' => colourCov T (w.get i) (w.get i')| ≤ pairingBound D w.length := by
      refine abs_wickPairingSum_le _ D hD fun i j => ?_
      unfold colourCov
      split_ifs
      · have := hTB (w.get i).1 (w.get j).1
        rw [hDd]
        linarith [le_abs_self B]
      · simpa using (zero_le_one.trans hD)
    have hwb : pairingBound D w.length = pairingBound D (2 * m) := by rw [hw]
    rw [hwb] at hb'
    calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (hxm m) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb'
  have hcard : ∀ J : Finset (Fin (q + 1)), J.card ≤ q + 1 := fun J => by
    simpa using J.card_le_univ
  have main1 : ∀ J : Finset (Fin (q + 1)), J.Nonempty →
      |mA J - mG J| ≤ (∏ l ∈ J, kernelSize (κ l)) * ε := by
    intro J hJ
    have h := abs_apply_prod_quadPoly_le (L - (x⁻¹) ^ J.card • gaussianMoment (colourCov T) J.card) κ J ε
      (fun w hw => by simpa using hword J.card (hcard J) w hw)
    rw [hAL J hJ, hmG]
    simpa using h
  have main2 : ∀ J : Finset (Fin (q + 1)), |mG J| ≤ Dq * ∏ l ∈ J, kernelSize (κ l) := by
    intro J
    have h := abs_apply_prod_quadPoly_le ((x⁻¹) ^ J.card • gaussianMoment (colourCov T) J.card) κ J (pairingBound D (2 * J.card))
      (fun w hw => by simpa using hgword J.card w hw)
    have hs : 0 ≤ ∏ l ∈ J, kernelSize (κ l) := Finset.prod_nonneg fun l _ => kernelSize_nonneg _
    rw [hmG]
    calc _ ≤ (∏ l ∈ J, kernelSize (κ l)) * pairingBound D (2 * J.card) := by simpa using h
      _ ≤ (∏ l ∈ J, kernelSize (κ l)) * Dq := mul_le_mul_of_nonneg_left (hDqw _ (hcard J)) hs
      _ = _ := mul_comm _ _
  have ex : (∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, mG J) =
      x ^ (-((q : ℝ) + 1)) * cyclicTraceSum κ T := by
    have hK' : ∀ i, (x⁻¹ • κ i).IsSymm := fun i => (hκ i).smul _
    have e := cumulant_eq_cyclicTraceSum q hq1 hq3 T hT (fun i => x⁻¹ • κ i) hK'
    have e1 : mG = formMoment T fun i => x⁻¹ • κ i := by
      rw [hmG]
      funext J
      simp only [formMoment, quadPoly_smul]
      rw [Finset.prod_smul, Finset.prod_const, map_smul, smul_eq_mul]
    have e2 : x ^ (-((q : ℝ) + 1)) = (x⁻¹) ^ (q + 1) := by
      have : -((q : ℝ) + 1) = -((q + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
    rw [e2, ← cyclicTraceSum_smul, ← e, e1]
    rfl
  have hprod : ∀ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
      ∏ J ∈ π.parts, ∏ l ∈ J, kernelSize (κ l) = (3 / 2) ^ (q + 1) * ∏ i, ∑ a, ∑ b, |κ i a b| := by
    intro π
    have hb' : ∏ l ∈ π.parts.biUnion id, kernelSize (κ l) = ∏ J ∈ π.parts, ∏ l ∈ id J, kernelSize (κ l) :=
      Finset.prod_biUnion π.disjoint
    rw [show ∏ J ∈ π.parts, ∏ l ∈ J, kernelSize (κ l) = ∏ J ∈ π.parts, ∏ l ∈ id J, kernelSize (κ l) from rfl, ← hb',
      π.biUnion_parts]
    simp only [kernelSize, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hper : ∀ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
      |(-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, mA J -
        (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, mG J| ≤
      ((π.parts.card - 1).factorial : ℝ) * (π.parts.card * (2 * Dq) ^ π.parts.card) *
        ((3 / 2) ^ (q + 1) * ∏ i, ∑ a, ∑ b, |κ i a b|) * ε := by
    intro π
    have hd := abs_prod_sub_prod_le π.parts mA mG (fun J => ∏ l ∈ J, kernelSize (κ l)) Dq ε hDq1 hε0 hε1
      (fun J _ => Finset.prod_nonneg fun l _ => kernelSize_nonneg _)
      (fun J hJ => main1 J (π.nonempty_of_mem_parts hJ)) (fun J _ => main2 J)
    rw [hprod π] at hd
    rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    calc _ ≤ ((π.parts.card - 1).factorial : ℝ) * _ :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  have hA0 : (∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        ∏ J ∈ π.parts, ∫ ω, ∏ l ∈ J, A.indicator (fun ω => aeval (p ω) (quadPoly (κ l))) ω ∂μ) =
      ∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
        (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, mA J := by
    rw [hmA]
  rw [hA0, ← ex, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun π _ => hper π).trans ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine le_of_eq (Finset.sum_congr rfl fun π _ => ?_)
  ring
end Main
open MeasureTheory in
theorem quadraticFormCumulants_holds (hJ : Cumulants.MixedCumulantMomentExpansion) :
    quadraticFormCumulantsStatement := by
  intro q B h1 h3
  obtain ⟨C, hC⟩ := cumulant_sub_gaussian_le q h1 h3 B
  refine ⟨C, ?_⟩
  intro Ω _ μ _ A I _ G Tc x ε Bg κ hA hκ hmeas hbd hx hT hTB hε0 hε1 hmom
  classical
  let p : Ω → I × Fin 3 → ℝ := fun ω v => BlockAverages.imaginaryComponent v.2 (G ω v.1)
  have hp : ∀ ω K, aeval (p ω) (quadPoly K) = quadraticForm K (G ω) := by
    intro ω K
    simp only [quadPoly, quadraticForm, map_sum, map_smul, map_mul, aeval_X, smul_eq_mul, p]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hpm : ∀ v, Measurable fun ω => p ω v := fun v => hmeas v.1 v.2
  have hpb : ∀ v, ∃ C : ℝ, ∀ ω, |p ω v| ≤ C := fun v => ⟨Bg, fun ω => hbd ω v.1 v.2⟩
  have main := hC Ω μ A I p Tc x ε κ hA hκ hpm hpb hx hT hTB hε0 hε1
    (fun r w hr => hmom r (fun i => (w i).1) (fun i => (w i).2) hr)
  simp only [hp] at main
  have hY : ∀ i, Probability.IsBoundedRealRV
      (A.indicator fun ω => quadraticForm (κ i) (G ω)) := by
    intro i
    obtain ⟨m, Cb, hCb⟩ := aeval_measurable_bounded p hpm hpb (quadPoly (κ i))
    simp only [hp] at m hCb
    refine ⟨m.indicator hA, |Cb|, fun ω => ?_⟩
    by_cases h : ω ∈ A
    · simpa [h] using (hCb ω).trans (le_abs_self _)
    · simp [h]
  have hc := hJ Ω μ (q + 1) (fun i => A.indicator fun ω => quadraticForm (κ i) (G ω)) (by omega) hY
  refine le_trans (le_of_eq ?_) main
  rw [hc]
  have e : (∑ π : SetPartition.PartitionsFin (q + 1),
      (-1 : ℂ) ^ (SetPartition.blockCount π - 1) *
        ((SetPartition.blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ ω, ∏ l ∈ J, A.indicator (fun ω => quadraticForm (κ l) (G ω)) ω ∂μ : ℝ) : ℂ)) =
      ((∑ π : Finpartition (Finset.univ : Finset (Fin (q + 1))),
        (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
          ∏ J ∈ π.parts, ∫ ω, ∏ l ∈ J, A.indicator (fun ω => quadraticForm (κ l) (G ω)) ω ∂μ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
end YangMills.Construction.ResponseInTheExpansion.QuadraticFormCumulants
end
