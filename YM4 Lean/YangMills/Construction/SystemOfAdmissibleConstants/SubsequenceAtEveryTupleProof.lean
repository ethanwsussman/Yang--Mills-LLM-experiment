import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABoundProof
import YangMills.Construction.SystemOfAdmissibleConstants.SubsequenceAtEveryTuple
import Mathlib
set_option autoImplicit false
open Filter Set TopologicalSpace
open scoped Topology
noncomputable section
namespace YangMills.Construction.AdmissibleConstants.DiagonalSubsequence
variable {P : Type} [MetricSpace P]
def ballUnion [ProperSpace P] [Nonempty P] (T : Finset (ℕ × ℕ)) : Set P :=
  ⋃ p ∈ T, Metric.closedBall (denseSeq P p.1) (1 / ((p.2 : ℝ) + 1))
theorem isCompact_ballUnion [ProperSpace P] [Nonempty P] (T : Finset (ℕ × ℕ)) :
    IsCompact (ballUnion (P := P) T) :=
  T.isCompact_biUnion fun _ _ => isCompact_closedBall _ _
theorem exists_ballUnion_cover [ProperSpace P] [Nonempty P] {K : Set P} (hK : IsCompact K) {δ : ℝ}
    (hδ : 0 < δ) : ∃ T, K ⊆ ballUnion T ∧ ∀ y ∈ ballUnion T, ∃ x ∈ K, dist y x < δ := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hδ)
  have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hx : ∀ x : P, ∃ a : ℕ, dist x (denseSeq P a) < 1 / ((m : ℝ) + 1) := fun x =>
    (denseRange_denseSeq P).exists_dist_lt x hr
  choose a ha using hx
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover
    (fun x => Metric.ball (denseSeq P (a x)) (1 / ((m : ℝ) + 1)))
    fun x _ => Metric.isOpen_ball.mem_nhds (ha x)
  classical
  refine ⟨t.image fun x => (a x, m), fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcov hy)
    refine mem_iUnion₂.2 ⟨(a x, m), Finset.mem_image_of_mem _ hxt, ?_⟩
    exact Metric.ball_subset_closedBall hyx
  · obtain ⟨p, hp, hy'⟩ := mem_iUnion₂.1 hy
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.1 hp
    refine ⟨x, htK x hxt, ?_⟩
    have h₁ : dist y (denseSeq P (a x)) ≤ 1 / ((m : ℝ) + 1) := hy'
    have h₂ := ha x
    rw [dist_comm] at h₂
    have h₃ := dist_triangle y (denseSeq P (a x)) x
    linarith
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ g i := by apply _root_.YangMills.Construction.BoundsOnEverySide.SubsequentialLimits.exists_pos_lower_bound <;> assumption
theorem exists_pos_le_dist_of_pairwise_disjoint {n : ℕ} {A : Fin n → Set P} (hA : ∀ i, IsCompact (A i))
    (hdis : Pairwise fun i k => Disjoint (A i) (A k)) :
    ∃ d : ℝ, 0 < d ∧ ∀ i k, i ≠ k → ∀ x ∈ A i, ∀ y ∈ A k, d ≤ dist x y := by
  have hpair : ∀ p : Fin n × Fin n, ∃ e : ℝ, 0 < e ∧
      (p.1 ≠ p.2 → ∀ x ∈ A p.1, ∀ y ∈ A p.2, e ≤ dist x y) := by
    rintro ⟨i, k⟩
    by_cases hik : i = k
    · exact ⟨1, one_pos, fun h => (h hik).elim⟩
    · obtain ⟨e, he, hxy⟩ := Metric.exists_pos_forall_lt_edist (hA i) (hA k).isClosed (hdis hik)
      refine ⟨e, by exact_mod_cast he, fun _ x hx y hy => ?_⟩
      have h := hxy x hx y hy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        e.coe_nonneg] at h
      exact h.le
  choose e he hxy using hpair
  obtain ⟨d, hd, hde⟩ := exists_pos_le_of_finite e he
  exact ⟨d, hd, fun i k hik x hx y hy => (hde (i, k)).trans (hxy (i, k) hik x hx y hy)⟩
theorem norm_sub_le_of_sizeLE_sub (C : NormedFunctionClass P) {n : ℕ} {A : Fin n → Set P}
    (hA : ∀ i, IsClosed (A i)) {Ψ : (Fin n → P → ℝ) → ℂ} {c : ℝ}
    (hΨ : C.IsMultiadditiveBounded A Ψ c) {u v : Fin n → P → ℝ}
    (hu : ∀ i, u i ∈ C.supportedIn (A i)) (hv : ∀ i, v i ∈ C.supportedIn (A i)) {B ε : ℝ}
    (huB : ∀ i, C.SizeLE (u i) B) (hvB : ∀ i, C.SizeLE (v i) B)
    (huv : ∀ i, C.SizeLE (u i - v i) ε) :
    ‖Ψ u - Ψ v‖ ≤ n * (c * (ε * B ^ (n - 1))) := by
  classical
  set w : ℕ → Fin n → P → ℝ := fun k i => if (i : ℕ) < k then v i else u i with hw
  have hwm : ∀ k i, w k i ∈ C.supportedIn (A i) := fun k i => by
    simp only [hw]
    split_ifs
    exacts [hv i, hu i]
  have hwB : ∀ k i, C.SizeLE (w k i) B := fun k i => by
    simp only [hw]
    split_ifs
    exacts [hvB i, huB i]
  have hstep : ∀ k, k < n → ‖Ψ (w k) - Ψ (w (k + 1))‖ ≤ c * (ε * B ^ (n - 1)) := by
    intro k hk
    have hwi : w k ⟨k, hk⟩ = u ⟨k, hk⟩ := by simp [hw]
    have hupd : w (k + 1) = Function.update (w k) ⟨k, hk⟩ (v ⟨k, hk⟩) := by
      funext l
      by_cases hl : l = ⟨k, hk⟩
      · subst hl
        simp [hw]
      · have hl' : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
        rw [Function.update_of_ne hl]
        simp only [hw]
        by_cases h : (l : ℕ) < k
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
    have he : Ψ (w k) - Ψ (w (k + 1)) =
        Ψ (Function.update (w k) ⟨k, hk⟩ (u ⟨k, hk⟩ - v ⟨k, hk⟩)) := by
      rw [hupd, hΨ.update_sub (w k) (fun l => hwm k l) ⟨k, hk⟩ (v ⟨k, hk⟩) (hv _), hwi]
    rw [he]
    have hZ : ∀ l, Function.update (w k) ⟨k, hk⟩ (u ⟨k, hk⟩ - v ⟨k, hk⟩) l ∈ C.supportedIn (A l) := by
      intro l
      by_cases hl : l = ⟨k, hk⟩
      · subst hl
        simpa using C.sub_mem (hA _) (hu _) (hv _)
      · simpa [Function.update_of_ne hl] using hwm k l
    refine (hΨ.norm_le _ hZ (fun l => if l = ⟨k, hk⟩ then ε else B) fun l => ?_).trans (le_of_eq ?_)
    · by_cases hl : l = ⟨k, hk⟩
      · subst hl
        simpa using huv _
      · simpa [Function.update_of_ne hl, if_neg hl] using hwB k l
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)), if_pos rfl]
      congr 2
      rw [Finset.prod_congr rfl (g := fun _ => B) fun l hl => by
        rw [if_neg (Finset.ne_of_mem_erase hl)]]
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
  have hsum : ∀ k, k ≤ n → ‖Ψ (w 0) - Ψ (w k)‖ ≤ k * (c * (ε * B ^ (n - 1))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h₁ := ih (by omega)
      have h₂ := hstep k (by omega)
      have h₃ : Ψ (w 0) - Ψ (w (k + 1)) = (Ψ (w 0) - Ψ (w k)) + (Ψ (w k) - Ψ (w (k + 1))) := by
        ring
      rw [h₃]
      refine (norm_add_le _ _).trans ?_
      push_cast
      linarith
  have h0 : w 0 = u := by
    funext i
    simp [hw]
  have hn : w n = v := by
    funext i
    simp [hw]
  have := hsum n le_rfl
  rwa [h0, hn] at this
theorem diagonalSubsequenceExists_holds : DiagonalSubsequenceExists := by
  intro P _ _ _ C Tup Φ hT hΦ
  classical
  choose D hDc hDs hDa using fun T : Finset (ℕ × ℕ) =>
    C.exists_countable_dense (isCompact_ballUnion (P := P) T)
  have hGc : (⋃ T, D T).Countable := countable_iUnion hDc
  have := hGc.to_subtype
  let I : Type := Σ n : ℕ, Fin n → (⋃ T, D T : Set (P → ℝ))
  let tupleOf : (ι : I) → Fin ι.1 → P → ℝ := fun ι i => (ι.2 i).1
  let Good : I → Prop := fun ι => 2 ≤ ι.1 ∧ ∃ T : Fin ι.1 → Finset (ℕ × ℕ),
    (∀ i, tupleOf ι i ∈ C.supportedIn (ballUnion (T i))) ∧
      ∃ d : ℝ, 0 < d ∧ ∀ i k, i ≠ k → ∀ x ∈ ballUnion (P := P) (T i),
        ∀ y ∈ ballUnion (P := P) (T k), d ≤ dist x y
  let w : I → ℕ → ℂ := fun ι j => if Good ι then Φ j ι.1 (tupleOf ι) else 0
  have hbd : ∀ ι, ∃ b, ∀ j, ‖w ι j‖ ≤ b := by
    intro ι
    by_cases h : Good ι
    · obtain ⟨h2, T, hm, d, hd, hsp⟩ := id h
      obtain ⟨c, N, hc, hN⟩ := hΦ ι.1 h2 _ (fun i => isCompact_ballUnion (T i)) d hd hsp
      choose b hb using fun i => C.exists_sizeLE (isCompact_ballUnion (T i)) (hm i)
      refine ⟨|c * ∏ i, b i| + ∑ j ∈ Finset.range N, ‖w ι j‖, fun j => ?_⟩
      have hs : 0 ≤ ∑ j ∈ Finset.range N, ‖w ι j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      by_cases hj : N ≤ j
      · have h₁ : ‖w ι j‖ ≤ c * ∏ i, b i := by
          simp only [w, if_pos h]
          exact (hN j hj).norm_le _ hm b hb
        linarith [le_abs_self (c * ∏ i, b i)]
      · have h₁ : ‖w ι j‖ ≤ ∑ j ∈ Finset.range N, ‖w ι j‖ :=
          Finset.single_le_sum (f := fun j => ‖w ι j‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_range.2 (by omega))
        linarith [abs_nonneg (c * ∏ i, b i)]
    · exact ⟨0, fun j => by simp [w, if_neg h]⟩
  choose b hb using hbd
  have hK : IsCompact (Set.pi univ fun ι => Metric.closedBall (0 : ℂ) (b ι)) :=
    isCompact_univ_pi fun ι => isCompact_closedBall _ _
  obtain ⟨a, -, φ, hφ, ht⟩ := hK.tendsto_subseq (x := fun j ι => w ι j)
    fun j ι _ => mem_closedBall_zero_iff.2 (hb ι j)
  refine ⟨φ, hφ, fun n hn X hX => ?_⟩
  suffices hc : CauchySeq fun i => Φ (φ i) n X from cauchySeq_tendsto_of_complete hc
  rw [Metric.cauchySeq_iff]
  intro η hη
  obtain ⟨hXc, hXm, hXd⟩ := hT n X hX
  obtain ⟨e, he, hsep⟩ := exists_pos_le_dist_of_pairwise_disjoint hXc hXd
  have hcov := fun i => exists_ballUnion_cover (hXc i) (δ := e / 4) (by positivity)
  choose T hKT hTK using hcov
  let A : Fin n → Set P := fun i => ballUnion (T i)
  have hAc : ∀ i, IsCompact (A i) := fun i => isCompact_ballUnion _
  have hdis : ∀ i k, i ≠ k → ∀ y ∈ A i, ∀ y' ∈ A k, e / 2 ≤ dist y y' := by
    intro i k hik y hy y' hy'
    obtain ⟨x, hx, hxy⟩ := hTK i y hy
    obtain ⟨x', hx', hxy'⟩ := hTK k y' hy'
    have h₁ := hsep i k hik x hx x' hx'
    have h₂ := dist_triangle4 x y y' x'
    rw [dist_comm x y] at h₂
    linarith
  obtain ⟨c, N, hc0, hN⟩ := hΦ n hn A hAc (e / 2) (by positivity) hdis
  have hXA : ∀ i, X i ∈ C.supportedIn (A i) := fun i => C.supportedIn_mono (hKT i) (hXm i)
  choose bX hbX using fun i => C.exists_sizeLE (hAc i) (hXA i)
  set B₀ : ℝ := ∑ i, |bX i| with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hXB : ∀ i, C.SizeLE (X i) B₀ := fun i => C.sizeLE_mono (hbX i)
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |bX i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  set W : ℝ := n * (c * (B₀ + 1) ^ (n - 1)) with hW
  have hW0 : 0 ≤ W := by positivity
  set ε : ℝ := min 1 (η / (3 * (W + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hWε : W * ε < η / 3 := by
    have h₁ : ε ≤ η / (3 * (W + 1)) := min_le_right _ _
    have h₂ : W * ε ≤ W * (η / (3 * (W + 1))) := mul_le_mul_of_nonneg_left h₁ hW0
    have h₃ : W * (η / (3 * (W + 1))) < η / 3 := by
      rw [show W * (η / (3 * (W + 1))) = (η / 3) * (W / (W + 1)) by field_simp]
      have : W / (W + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      nlinarith
    linarith
  have happ := fun i => hDa (T i) (X i) (hXA i) ε hε0
  choose H hHD hHn using happ
  have hHc : ∀ i, H i ∈ C.supportedIn (A i) := fun i => hDs _ (hHD i)
  have hHB : ∀ i, C.SizeLE (H i) (B₀ + 1) := fun i =>
    C.sizeLE_mono (C.sizeLE_of_sub (hXA i) (hHc i) (hXB i) (hHn i)) (by linarith)
  let ι₀ : I := ⟨n, fun i => ⟨H i, mem_iUnion.2 ⟨T i, hHD i⟩⟩⟩
  have hgood : Good ι₀ := ⟨hn, T, hHc, e / 2, by positivity, hdis⟩
  have hw : ∀ j, w ι₀ j = Φ j n H := fun j => if_pos hgood
  have hclose : ∀ j, N ≤ j → ‖Φ j n X - Φ j n H‖ ≤ W * ε := by
    intro j hj
    refine (norm_sub_le_of_sizeLE_sub C (fun i => (hAc i).isClosed) (hN j hj) hXA hHc
      (fun i => C.sizeLE_mono (hXB i) (by linarith)) hHB hHn).trans (le_of_eq ?_)
    rw [hW]
    ring
  have hz := (tendsto_pi_nhds.1 ht) ι₀
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hz.cauchySeq (η / 3) (by positivity)
  refine ⟨max N N₁, fun p hp q hq => ?_⟩
  have hpN : N ≤ φ p := (le_of_max_le_left hp).trans (hφ.le_apply)
  have hqN : N ≤ φ q := (le_of_max_le_left hq).trans (hφ.le_apply)
  have h₁ : dist (Φ (φ p) n H) (Φ (φ q) n H) < η / 3 := by
    rw [← hw, ← hw]
    exact hN₁ p (le_of_max_le_right hp) q (le_of_max_le_right hq)
  have h₂ := (hclose _ hpN).trans_lt hWε
  have h₃ := (hclose _ hqN).trans_lt hWε
  rw [← dist_eq_norm] at h₂ h₃
  have h₄ := dist_triangle4 (Φ (φ p) n X) (Φ (φ p) n H) (Φ (φ q) n H) (Φ (φ q) n X)
  rw [dist_comm (Φ (φ q) n H)] at h₄
  linarith
end YangMills.Construction.AdmissibleConstants.DiagonalSubsequence
end
