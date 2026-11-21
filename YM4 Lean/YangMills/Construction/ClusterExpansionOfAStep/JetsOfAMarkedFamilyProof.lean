import YangMills.Construction.ClusterExpansionOfAStep.DerivativesUnderAnIntegral
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfAMarkedFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped Nat
namespace YangMills.Construction.PolymerCumulant
section
variable {α ι β : Type} [MeasurableSpace α] [DecidableEq ι] {μ : Measure α} {k N : ℕ}
  {U : Set (Fin k → ℝ)} {τ₀ : Fin k → ℝ} {block : β → ι} {all near : Finset β}
  {bonds : Finset ι → Finset β} {w : Finset ι → α → ℝ} {K : α → (Fin k → ℝ) → ℝ}
  {M : β → α → (Fin k → ℝ) → ℝ} {P Q₀ Q κ : ℝ}
open Classical in
def touchedBonds (T near : Finset β) {j : ℕ} (p : Sym (Option β) j) : Finset β :=
  (T ∩ near).filter fun b => Multiset.count (some b) (p : Multiset (Option β)) ≠ 0
open Classical in
theorem card_touchedBonds_le (T near : Finset β) {j : ℕ} (p : Sym (Option β) j) :
    (touchedBonds T near p).card ≤ j := by
  have h1 : (touchedBonds T near p).image some ⊆ (p : Multiset (Option β)).toFinset := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have := (Finset.mem_filter.mp hb).2
    exact Multiset.mem_toFinset.mpr (Multiset.count_ne_zero.mp this)
  have h2 := Finset.card_le_card h1
  rw [Finset.card_image_of_injective _ (Option.some_injective β)] at h2
  have h3 : (p : Multiset (Option β)).toFinset.card ≤ Multiset.card (p : Multiset (Option β)) :=
    Multiset.toFinset_card_le _
  rw [Sym.card_coe] at h3
  exact h2.trans h3
open Classical in
theorem norm_iteratedFDeriv_kernel_mul_prod_le (h : BondExpansion μ N U τ₀ block all near bonds w K M P Q₀ Q κ)
    (a : α) (T : Finset β)
    (hT : T ⊆ all) {τ : Fin k → ℝ} (hτ : τ ∈ U) {R : ℝ} (hR : 1 ≤ R)
    (hM : ∀ b ∈ near, ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i (M b a) τ‖ ≤ R) {j : ℕ} (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun σ => K a σ * ∏ b ∈ T, M b a σ) τ‖ ≤
      ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j, ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * R) ^ j * (K a τ * ∏ b ∈ T \ touchedBonds T near p, M b a τ)) := by
  have hU := h.isOpen
  have hud : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  set T' := T ∩ near with hT'
  have hT'T : T' ⊆ T := Finset.inter_subset_left
  let f : Option β → (Fin k → ℝ) → ℝ := fun x => match x with
    | none => K a
    | some b => M b a
  have hf : ∀ x ∈ Finset.insertNone T', ContDiffOn ℝ N (f x) U := by
    intro x hx
    cases x with
    | none => exact h.kernel_contDiffOn a
    | some b =>
      have hb : b ∈ T' := by simpa using hx
      exact h.mark_contDiffOn b (hT (hT'T hb)) a
  set C₀ : ℝ := ∏ b ∈ T \ near, M b a τ₀ with hC₀
  have hprod : Set.EqOn (fun σ => K a σ * ∏ b ∈ T, M b a σ)
      (fun σ => C₀ • ∏ x ∈ Finset.insertNone T', f x σ) U := by
    intro σ hσ
    have h1 : ∏ b ∈ T, M b a σ = (∏ b ∈ T \ near, M b a σ) * ∏ b ∈ T', M b a σ := by
      rw [hT', ← Finset.prod_sdiff (Finset.inter_subset_left (s₁ := T) (s₂ := near))]
      congr 1
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext b
      simp
    have h2 : ∏ b ∈ T \ near, M b a σ = C₀ := by
      refine Finset.prod_congr rfl fun b hb => ?_
      have hb' := Finset.mem_sdiff.mp hb
      exact h.mark_eq_center b (hT hb'.1) hb'.2 a σ hσ
    simp only [Finset.prod_insertNone, smul_eq_mul]
    rw [h1, h2]
    simp only [f]
    ring
  have hC₀nn : 0 ≤ C₀ := Finset.prod_nonneg fun b hb =>
    h.mark_nonneg b (hT (Finset.mem_sdiff.mp hb).1) a τ₀ h.center_mem
  have hsm : ContDiffOn ℝ N (fun σ => ∏ x ∈ Finset.insertNone T', f x σ) U :=
    contDiffOn_prod hf
  have hjN : ((j : ℕ) : WithTop ℕ∞) ≤ (N : WithTop ℕ∞) := by exact_mod_cast hj
  have hcw : ContDiffWithinAt ℝ j (fun σ => ∏ x ∈ Finset.insertNone T', f x σ) U τ :=
    (hsm.of_le hjN) τ hτ
  have e1 : iteratedFDeriv ℝ j (fun σ => K a σ * ∏ b ∈ T, M b a σ) τ =
      C₀ • iteratedFDerivWithin ℝ j (fun σ => ∏ x ∈ Finset.insertNone T', f x σ) U τ := by
    rw [← iteratedFDerivWithin_of_isOpen j hU hτ, iteratedFDerivWithin_congr hprod hτ]
    exact iteratedFDerivWithin_const_smul_apply (a := C₀) hcw hud hτ
  rw [e1, norm_smul, Real.norm_of_nonneg hC₀nn]
  have e2 := norm_iteratedFDerivWithin_prod_le (u := Finset.insertNone T') (f := f)
    (N := (N : WithTop ℕ∞)) hf hud hτ hjN
  refine (mul_le_mul_of_nonneg_left e2 hC₀nn).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hP0 : 0 ≤ P := by linarith [h.one_le_rate]
  have hK0 := h.kernel_nonneg a τ hτ
  have hcard : ∀ x, Multiset.count x (p : Multiset (Option β)) ≤ j := fun x =>
    (Multiset.count_le_card _ _).trans_eq Sym.card_coe
  set t := touchedBonds T near p with ht
  have h1 : ‖iteratedFDerivWithin ℝ (Multiset.count none (p : Multiset (Option β))) (f none) U τ‖ ≤
      P ^ j * K a τ := by
    rw [iteratedFDerivWithin_of_isOpen _ hU hτ]
    refine (h.kernel_iteratedFDeriv_le a _ ((hcard none).trans hj) τ hτ).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h.one_le_rate (hcard none)) hK0
  have h2 : ∏ b ∈ T', ‖iteratedFDerivWithin ℝ (Multiset.count (some b) (p : Multiset (Option β)))
      (f (some b)) U τ‖ ≤
      ∏ b ∈ T', (if Multiset.count (some b) (p : Multiset (Option β)) ≠ 0 then R else M b a τ) := by
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun b hb => ?_
    rw [iteratedFDerivWithin_of_isOpen _ hU hτ]
    split_ifs with hc
    · exact hM b (Finset.mem_inter.mp hb).2 _ (Nat.one_le_iff_ne_zero.mpr hc) ((hcard _).trans hj)
    · rw [not_not.mp hc, norm_iteratedFDeriv_zero]
      exact (Real.norm_of_nonneg (h.mark_nonneg b (hT (hT'T hb)) a τ hτ)).le
  have h3 : ∏ b ∈ T', (if Multiset.count (some b) (p : Multiset (Option β)) ≠ 0 then R else M b a τ) =
      R ^ t.card * ∏ b ∈ T' \ t, M b a τ := by
    rw [Finset.prod_ite, Finset.prod_const]
    congr 2
    ext b
    simp only [ht, touchedBonds, hT', Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have h4 : ∏ b ∈ T \ t, M b a τ = C₀ * ∏ b ∈ T' \ t, M b a τ := by
    have hu : T \ t = (T \ near) ∪ (T' \ t) := by
      ext b
      simp only [ht, touchedBonds, hT', Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
        Finset.mem_inter]
      tauto
    have hdis : Disjoint (T \ near) (T' \ t) := by
      rw [Finset.disjoint_left]
      intro b hb hb'
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb').1).2
    rw [hu, Finset.prod_union hdis]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    have hb' := Finset.mem_sdiff.mp hb
    exact h.mark_eq_center b (hT hb'.1) hb'.2 a τ hτ
  have hY : 0 ≤ ∏ b ∈ T' \ t, M b a τ := Finset.prod_nonneg fun b hb =>
    h.mark_nonneg b (hT (hT'T (Finset.mem_sdiff.mp hb).1)) a τ hτ
  have h5 : ∏ x ∈ Finset.insertNone T', ‖iteratedFDerivWithin ℝ (Multiset.count x (p : Multiset (Option β)))
      (f x) U τ‖ ≤
      (P ^ j * K a τ) * (R ^ t.card * ∏ b ∈ T' \ t, M b a τ) := by
    rw [Finset.prod_insertNone, ← h3]
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
  have hpow : R ^ t.card ≤ R ^ j := pow_le_pow_right₀ hR (card_touchedBonds_le T near p)
  have hc : (0 : ℝ) ≤ ((p : Multiset (Option β)).countPerms : ℝ) := Nat.cast_nonneg _
  rw [h4, mul_pow]
  calc C₀ * (((p : Multiset (Option β)).countPerms : ℝ) * ∏ x ∈ Finset.insertNone T',
        ‖iteratedFDerivWithin ℝ (Multiset.count x (p : Multiset (Option β))) (f x) U τ‖)
      ≤ C₀ * (((p : Multiset (Option β)).countPerms : ℝ) *
        ((P ^ j * K a τ) * (R ^ t.card * ∏ b ∈ T' \ t, M b a τ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hc) hC₀nn
    _ = (C₀ * ((p : Multiset (Option β)).countPerms : ℝ) * (P ^ j * K a τ) * ∏ b ∈ T' \ t, M b a τ) *
        R ^ t.card := by ring
    _ ≤ (C₀ * ((p : Multiset (Option β)).countPerms : ℝ) * (P ^ j * K a τ) * ∏ b ∈ T' \ t, M b a τ) *
        R ^ j :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring
theorem bondWeightedIntegral_le_two_pow_mul_union
    (h : BondExpansion μ N U τ₀ block all near bonds w K M P Q₀ Q κ) (D B : Finset ι) :
    bondWeightedIntegral μ bonds w K M B τ₀ ≤ 2 ^ D.card * bondWeightedIntegral μ bonds w K M (B ∪ D) τ₀ := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert Y D hY ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hY, pow_succ]
    have := h.integral_le_two_mul_insert (B ∪ D) Y
    calc bondWeightedIntegral μ bonds w K M B τ₀
        ≤ 2 ^ D.card * bondWeightedIntegral μ bonds w K M (B ∪ D) τ₀ := ih
      _ ≤ 2 ^ D.card * (2 * bondWeightedIntegral μ bonds w K M (insert Y (B ∪ D)) τ₀) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
theorem integrable_bondIntegrand (h : BondExpansion μ N U τ₀ block all near bonds w K M P Q₀ Q κ)
    (A : Finset ι) {τ : Fin k → ℝ} (hτ : τ ∈ U) :
    Integrable (fun a => w A a * K a τ * ∏ b ∈ bonds A, M b a τ) μ := by
  by_contra hn
  have := h.integral_pos A τ hτ
  rw [bondWeightedIntegral, integral_undef hn] at this
  exact lt_irrefl _ this
theorem sum_sym_countPerms_eq_pow {γ : Type} [DecidableEq γ] (u : Finset γ) (j : ℕ) :
    ∑ p ∈ u.sym j, (((p : Multiset γ).countPerms : ℕ) : ℝ) = (u.card : ℝ) ^ j := by
  have := Finset.sum_pow (s := u) (x := fun _ => (1 : ℝ)) j
  simpa using this.symm
theorem norm_iteratedFDeriv_const_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 ≤ c) {f : E → ℝ} {j : ℕ} {τ : E} (hf : ContDiffAt ℝ j f τ) :
    ‖iteratedFDeriv ℝ j (fun σ => c * f σ) τ‖ = c * ‖iteratedFDeriv ℝ j f τ‖ := by
  have := iteratedFDeriv_const_smul_apply' (a := c) hf
  simp only [smul_eq_mul] at this
  rw [this, norm_smul, Real.norm_of_nonneg hc]
theorem bondWeightedIntegral_contDiffOn_and_iteratedFDeriv_le
    (h : BondExpansion μ N U τ₀ block all near bonds w K M P Q₀ Q κ)
    (hD : ParametricIntegral.ContDiffOnIntegralStatement) (A : Finset ι) :
    ContDiffOn ℝ N (bondWeightedIntegral μ bonds w K M A) U ∧ ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (bondWeightedIntegral μ bonds w K M A) τ₀‖ ≤
        (((near.card : ℝ) + 1) * (2 * P * Q₀)) ^ j * bondWeightedIntegral μ bonds w K M A τ₀ := by
  classical
  have hU := h.isOpen
  have hP0 : 0 ≤ P := by linarith [h.one_le_rate]
  have hQ0 : 0 ≤ Q := by linarith [h.one_le_markBound]
  have hQ₀0 : 0 ≤ Q₀ := by linarith [h.one_le_centerBound]
  set T := bonds A with hTdef
  have hTall : T ⊆ all := fun b hb => ((h.mem_bonds A b).mp hb).1
  have hsm : ∀ a, ContDiffOn ℝ N (fun σ => K a σ * ∏ b ∈ T, M b a σ) U := fun a =>
    (h.kernel_contDiffOn a).mul (contDiffOn_prod fun b hb => h.mark_contDiffOn b (hTall hb) a)
  have hat : ∀ a, ∀ σ ∈ U, ∀ j ≤ N, ContDiffAt ℝ j (fun σ => K a σ * ∏ b ∈ T, M b a σ) σ := by
    intro a σ hσ j hj
    have hjN : ((j : ℕ) : WithTop ℕ∞) ≤ (N : WithTop ℕ∞) := by exact_mod_cast hj
    exact ((hsm a).of_le hjN).contDiffAt (hU.mem_nhds hσ)
  have hassoc : ∀ a, (fun σ => w A a * K a σ * ∏ b ∈ T, M b a σ) =
      fun σ => w A a * (K a σ * ∏ b ∈ T, M b a σ) := fun a => by
    funext σ
    ring
  have hnorm : ∀ a, ∀ σ ∈ U, ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun σ => w A a * K a σ * ∏ b ∈ T, M b a σ) σ‖ =
      w A a * ‖iteratedFDeriv ℝ j (fun σ => K a σ * ∏ b ∈ T, M b a σ) σ‖ := by
    intro a σ hσ j hj
    rw [hassoc a]
    exact norm_iteratedFDeriv_const_mul (h.weight_nonneg A a) (hat a σ hσ j hj)
  have hbot : bonds ∅ = ∅ := by
    ext b
    simp [h.mem_bonds]
  have hcardU : ∀ j, (((Finset.insertNone (T ∩ near)).card : ℕ) : ℝ) ^ j ≤ ((near.card : ℝ) + 1) ^ j := by
    intro j
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ j
    rw [Finset.card_insertNone]
    have : (T ∩ near).card ≤ near.card := Finset.card_le_card Finset.inter_subset_right
    exact_mod_cast Nat.succ_le_succ this
  set W : ℝ := (((near.card : ℝ) + 1) * (P * Q)) with hW
  have hW1 : 1 ≤ W := by
    have h1 : (1 : ℝ) ≤ (near.card : ℝ) + 1 := by
      have : (0 : ℝ) ≤ near.card := Nat.cast_nonneg _
      linarith
    have h2 : (1 : ℝ) ≤ P * Q := one_le_mul_of_one_le_of_one_le h.one_le_rate h.one_le_markBound
    exact one_le_mul_of_one_le_of_one_le h1 h2
  let g : α → ℝ := fun a => W ^ N * (κ * (w ∅ a * K a τ₀))
  have hg : Integrable g μ := by
    have := integrable_bondIntegrand h ∅ h.center_mem
    simp only [hbot, Finset.prod_empty, mul_one] at this
    exact (this.const_mul κ).const_mul _
  have hbound : ∀ a, ∀ j ≤ N, ∀ σ ∈ U,
      ‖iteratedFDeriv ℝ j (fun σ => w A a * K a σ * ∏ b ∈ T, M b a σ) σ‖ ≤ g a := by
    intro a j hj σ hσ
    rw [hnorm a σ hσ j hj]
    have hK0 := h.kernel_nonneg a σ hσ
    have e1 := norm_iteratedFDeriv_kernel_mul_prod_le h a T hTall hσ h.one_le_markBound
      (fun b hb i hi hi' => h.mark_iteratedFDeriv_le b hb a i hi hi' σ hσ) hj
    have e2 : ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j, ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * Q) ^ j * (K a σ * ∏ b ∈ T \ touchedBonds T near p, M b a σ)) ≤
        ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j, ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * Q) ^ j * K a σ) := by
      refine Finset.sum_le_sum fun p _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_of_le_one_right hK0 ?_
      refine Finset.prod_le_one
        (fun b hb => h.mark_nonneg b (hTall (Finset.mem_sdiff.mp hb).1) a σ hσ)
        fun b hb => h.mark_le_one b (hTall (Finset.mem_sdiff.mp hb).1) a σ hσ
    rw [← Finset.sum_mul, sum_sym_countPerms_eq_pow] at e2
    have e3 : ((((Finset.insertNone (T ∩ near)).card : ℕ) : ℝ) ^ j) * ((P * Q) ^ j * K a σ) ≤
        W ^ N * K a σ := by
      calc _ ≤ (((near.card : ℝ) + 1) ^ j) * ((P * Q) ^ j * K a σ) :=
            mul_le_mul_of_nonneg_right (hcardU j) (by positivity)
        _ = W ^ j * K a σ := by rw [hW, mul_pow ((near.card : ℝ) + 1)]; ring
        _ ≤ W ^ N * K a σ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hW1 hj) hK0
    have hd0 := h.weight_nonneg A a
    have hdE : w A a ≤ w ∅ a := h.weight_antitone A ∅ a (Finset.empty_subset _)
    have hWN : 0 ≤ W ^ N := by positivity
    calc w A a * ‖iteratedFDeriv ℝ j (fun σ => K a σ * ∏ b ∈ T, M b a σ) σ‖
        ≤ w A a * (W ^ N * K a σ) := mul_le_mul_of_nonneg_left (e1.trans (e2.trans e3)) hd0
      _ ≤ w ∅ a * (W ^ N * K a σ) := mul_le_mul_of_nonneg_right hdE (by positivity)
      _ ≤ w ∅ a * (W ^ N * (κ * K a τ₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h.kernel_le_center a σ hσ) hWN)
            (h.weight_nonneg ∅ a)
      _ = g a := by simp only [g]; ring
  have hmeas : ∀ σ ∈ U, AEStronglyMeasurable (fun a => w A a * K a σ * ∏ b ∈ T, M b a σ) μ := fun σ hσ =>
    (integrable_bondIntegrand h A hσ).aestronglyMeasurable
  have hsmF : ∀ a, ContDiffOn ℝ N (fun σ => w A a * K a σ * ∏ b ∈ T, M b a σ) U := fun a => by
    rw [hassoc a]
    exact contDiffOn_const.mul (hsm a)
  obtain ⟨c1, c2⟩ := hD μ k N U (fun a σ => w A a * K a σ * ∏ b ∈ T, M b a σ) g hU hg hsmF hmeas hbound
  refine ⟨c1, fun j hj => ?_⟩
  let A' : Sym (Option β) j → Finset ι := fun p => A \ (touchedBonds T near p).image block
  let G : Sym (Option β) j → α → ℝ := fun p a => w (A' p) a * K a τ₀ * ∏ b ∈ bonds (A' p), M b a τ₀
  let hh : α → ℝ := fun a => ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j,
    ((p : Multiset (Option β)).countPerms : ℝ) * ((P * Q₀) ^ j * G p a)
  have hGint : ∀ p, Integrable (G p) μ := fun p => integrable_bondIntegrand h (A' p) h.center_mem
  have hhint : Integrable hh μ :=
    integrable_finsetSum _ fun p _ => ((hGint p).const_mul _).const_mul _
  have hhb : ∀ a, ‖iteratedFDeriv ℝ j (fun σ => w A a * K a σ * ∏ b ∈ T, M b a σ) τ₀‖ ≤ hh a := by
    intro a
    rw [hnorm a τ₀ h.center_mem j hj]
    have e1 := norm_iteratedFDeriv_kernel_mul_prod_le h a T hTall h.center_mem h.one_le_centerBound
      (fun b hb i hi hi' => h.mark_iteratedFDeriv_center_le b hb a i hi hi') hj
    refine (mul_le_mul_of_nonneg_left e1 (h.weight_nonneg A a)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have hK0 := h.kernel_nonneg a τ₀ h.center_mem
    set t := touchedBonds T near p with ht
    have hsub : bonds (A' p) ⊆ T \ t := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := (h.mem_bonds _ b).mp hb
      have hb3 := Finset.mem_sdiff.mp hb2
      refine Finset.mem_sdiff.mpr ⟨(h.mem_bonds A b).mpr ⟨hb1, hb3.1⟩, fun hbt => ?_⟩
      exact hb3.2 (Finset.mem_image_of_mem _ hbt)
    have hle : ∏ b ∈ T \ t, M b a τ₀ ≤ ∏ b ∈ bonds (A' p), M b a τ₀ := by
      rw [← Finset.prod_sdiff hsub]
      have hn : 0 ≤ ∏ b ∈ bonds (A' p), M b a τ₀ := Finset.prod_nonneg fun b hb =>
        h.mark_nonneg b ((h.mem_bonds _ b).mp hb).1 a τ₀ h.center_mem
      refine mul_le_of_le_one_left hn ?_
      refine Finset.prod_le_one (fun b hb => ?_) fun b hb => ?_
      · exact h.mark_nonneg b (hTall (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1) a τ₀ h.center_mem
      · exact h.mark_le_one b (hTall (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1) a τ₀ h.center_mem
    have hn2 : 0 ≤ ∏ b ∈ T \ t, M b a τ₀ := Finset.prod_nonneg fun b hb =>
      h.mark_nonneg b (hTall (Finset.mem_sdiff.mp hb).1) a τ₀ h.center_mem
    have hd : w A a ≤ w (A' p) a := h.weight_antitone A (A' p) a Finset.sdiff_subset
    have hG : w A a * (K a τ₀ * ∏ b ∈ T \ t, M b a τ₀) ≤ G p a := by
      calc w A a * (K a τ₀ * ∏ b ∈ T \ t, M b a τ₀)
          ≤ w (A' p) a * (K a τ₀ * ∏ b ∈ T \ t, M b a τ₀) :=
            mul_le_mul_of_nonneg_right hd (by positivity)
        _ ≤ w (A' p) a * (K a τ₀ * ∏ b ∈ bonds (A' p), M b a τ₀) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hK0) (h.weight_nonneg _ a)
        _ = G p a := by simp only [G]; ring
    have hc : (0 : ℝ) ≤ ((p : Multiset (Option β)).countPerms : ℝ) := Nat.cast_nonneg _
    have hPQ : 0 ≤ (P * Q₀) ^ j := by positivity
    calc w A a * (((p : Multiset (Option β)).countPerms : ℝ) *
          ((P * Q₀) ^ j * (K a τ₀ * ∏ b ∈ T \ t, M b a τ₀)))
        = ((p : Multiset (Option β)).countPerms : ℝ) * ((P * Q₀) ^ j *
          (w A a * (K a τ₀ * ∏ b ∈ T \ t, M b a τ₀))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hPQ) hc
  have hfin := c2 j hj τ₀ h.center_mem hh hhint hhb
  have hint : ∫ a, hh a ∂μ = ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j,
      ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * Q₀) ^ j * bondWeightedIntegral μ bonds w K M (A' p) τ₀) := by
    simp only [hh]
    rw [integral_finsetSum _ fun p _ => ((hGint p).const_mul _).const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_const_mul]
    rfl
  have hZ0 : 0 < bondWeightedIntegral μ bonds w K M A τ₀ := h.integral_pos A τ₀ h.center_mem
  have hAp : ∀ p, bondWeightedIntegral μ bonds w K M (A' p) τ₀ ≤
      2 ^ j * bondWeightedIntegral μ bonds w K M A τ₀ := by
    intro p
    have e1 := bondWeightedIntegral_le_two_pow_mul_union h (A ∩ (touchedBonds T near p).image block) (A' p)
    have e2 : A' p ∪ (A ∩ (touchedBonds T near p).image block) = A := by
      ext y
      simp only [A', Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [e2] at e1
    have e3 : (A ∩ (touchedBonds T near p).image block).card ≤ j :=
      (Finset.card_le_card Finset.inter_subset_right).trans
        (Finset.card_image_le.trans (card_touchedBonds_le T near p))
    exact e1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) e3) hZ0.le)
  have hchange : iteratedFDeriv ℝ j (bondWeightedIntegral μ bonds w K M A) τ₀ =
      iteratedFDeriv ℝ j (fun τ => ∫ a, w A a * K a τ * ∏ b ∈ T, M b a τ ∂μ) τ₀ := rfl
  rw [hchange]
  refine hfin.trans ?_
  rw [hint]
  have e4 : ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j,
      ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * Q₀) ^ j * bondWeightedIntegral μ bonds w K M (A' p) τ₀) ≤
      ∑ p ∈ (Finset.insertNone (T ∩ near)).sym j, ((p : Multiset (Option β)).countPerms : ℝ) *
        ((P * Q₀) ^ j * (2 ^ j * bondWeightedIntegral μ bonds w K M A τ₀)) := by
    refine Finset.sum_le_sum fun p _ => ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAp p) (by positivity)) (Nat.cast_nonneg _)
  refine e4.trans ?_
  rw [← Finset.sum_mul, sum_sym_countPerms_eq_pow]
  calc _ ≤ (((near.card : ℝ) + 1) ^ j) *
        ((P * Q₀) ^ j * (2 ^ j * bondWeightedIntegral μ bonds w K M A τ₀)) :=
        mul_le_mul_of_nonneg_right (hcardU j) (by positivity)
    _ = _ := by simp only [mul_pow]; ring
end
theorem logIteratedDerivBoundStatement_holds (hD : ParametricIntegral.ContDiffOnIntegralStatement) :
    LogIteratedDerivBoundStatement := by
  intro N hN
  refine ⟨N ! * ∑ i ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ i Real.log (Set.Ioi 0) 1‖, by positivity, ?_⟩
  intro α ι β _ _ μ k U τ₀ block all near bonds w K M P Q₀ Q κ h A
  obtain ⟨hs, hj⟩ := bondWeightedIntegral_contDiffOn_and_iteratedFDeriv_le h hD A
  have hU := h.isOpen
  have hud : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hz : 0 < bondWeightedIntegral μ bonds w K M A τ₀ := h.integral_pos A τ₀ h.center_mem
  set z := bondWeightedIntegral μ bonds w K M A τ₀ with hzdef
  refine ⟨(hs.contDiffAt (hU.mem_nhds h.center_mem)).log hz.ne', ?_⟩
  let f : (Fin k → ℝ) → ℝ := fun σ => z⁻¹ * bondWeightedIntegral μ bonds w K M A σ
  have hfs : ContDiffOn ℝ N f U := contDiffOn_const.mul hs
  have hev : (fun τ => Real.log (bondWeightedIntegral μ bonds w K M A τ)) =ᶠ[𝓝 τ₀]
      fun τ => (Real.log ∘ f) τ + Real.log z := by
    refine Filter.eventually_of_mem (hU.mem_nhds h.center_mem) fun σ hσ => ?_
    have h1 := h.integral_pos A σ hσ
    simp only [f, Function.comp]
    rw [Real.log_mul (inv_pos.mpr hz).ne' h1.ne', Real.log_inv]
    ring
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev N).eq_of_nhds]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hdrop : ‖iteratedFDeriv ℝ (N' + 1) (fun τ => (Real.log ∘ f) τ + Real.log z) τ₀‖ =
      ‖iteratedFDeriv ℝ (N' + 1) (Real.log ∘ f) τ₀‖ := by
    rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv]
    congr 2
    funext σ
    exact fderiv_add_const _
  rw [hdrop, ← iteratedFDerivWithin_of_isOpen _ hU h.center_mem]
  have hmaps : Set.MapsTo f U (Set.Ioi 0) := fun σ hσ => mul_pos (inv_pos.mpr hz) (h.integral_pos A σ hσ)
  have hf1 : f τ₀ = 1 := inv_mul_cancel₀ hz.ne'
  have hlog : ContDiffOn ℝ ((N' + 1 : ℕ) : WithTop ℕ∞) Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono fun x hx => (ne_of_gt hx : x ≠ 0)
  refine norm_iteratedFDerivWithin_comp_le hlog hfs le_rfl isOpen_Ioi.uniqueDiffOn hud hmaps h.center_mem ?_ ?_
  · intro i hi
    rw [hf1]
    exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i Real.log (Set.Ioi 0) 1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  · intro i hi1 hi2
    rw [iteratedFDerivWithin_of_isOpen _ hU h.center_mem]
    have hiN : ((i : ℕ) : WithTop ℕ∞) ≤ ((N' + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hi2
    have hat : ContDiffAt ℝ i (bondWeightedIntegral μ bonds w K M A) τ₀ :=
      (hs.of_le hiN).contDiffAt (hU.mem_nhds h.center_mem)
    rw [norm_iteratedFDeriv_const_mul (inv_pos.mpr hz).le hat]
    calc z⁻¹ * ‖iteratedFDeriv ℝ i (bondWeightedIntegral μ bonds w K M A) τ₀‖
        ≤ z⁻¹ * ((((near.card : ℝ) + 1) * (2 * P * Q₀)) ^ i * z) :=
          mul_le_mul_of_nonneg_left (hj i hi2) (inv_pos.mpr hz).le
      _ = _ := by field_simp
end YangMills.Construction.PolymerCumulant
end
