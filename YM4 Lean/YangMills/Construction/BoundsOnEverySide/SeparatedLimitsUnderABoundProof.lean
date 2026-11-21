import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABound
import YangMills.Construction.Continuum.MultilinearFunctionalsCoordinatewise
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.InfiniteLattice.WeaklyConvergentSubsequencesOfStatesProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
open SeparatedBound
open LimitGrowthFromCutoffBound (restrictToTestTuples)
open TestSpaces (SepTupleOfCard)
open TorusMetric (euclidNormVec)
open TestFunctions (sharpNormR4 closedBallR4 setDistR4)
noncomputable section
namespace BoundsOnEverySide.SubsequentialLimits
abbrev Vec4 : Type := Fin 4 → ℝ
theorem supNorm_le_euclidNormVec (v : Vec4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul (v : Vec4) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
def C1BoundedBy (f : Vec4 → ℝ) (b : ℝ) : Prop := ∀ x, |f x| ≤ b ∧ ‖fderiv ℝ f x‖ ≤ b
theorem sharpNormR4_nonneg (M : ℝ) (f : Vec4 → ℝ) : 0 ≤ sharpNormR4 M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem sharpNormR4_le_of_bound {M : ℝ} (hM : 1 ≤ M) {f : Vec4 → ℝ} (hf : ContDiff ℝ 1 f) {b : ℝ}
    (hb : C1BoundedBy f b) : sharpNormR4 M f ≤ 40 * M * b := by
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0).1
  have hlip : ∀ x y, ‖f x - f y‖ ≤ b * TestFunctions.euclidDistR4 x y := fun x y => by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (s := univ) (C := b)
      (x := y) (y := x) (fun z _ => (hf.differentiable (by norm_num)) z)
      (fun z _ => (hb z).2) convex_univ (mem_univ _) (mem_univ _)
    exact h.trans (mul_le_mul_of_nonneg_left (supNorm_le_euclidNormVec _) hb0)
  have h1 : TestFunctions.uniformNorm f ≤ b := ciSup_le fun x => (hb x).1
  have h2 : TestFunctions.lipConstR4 f ≤ b :=
    csInf_le ⟨0, fun c hc => hc.1⟩ ⟨hb0, hlip⟩
  refine max_le ?_ ?_
  · nlinarith
  · exact mul_le_mul_of_nonneg_left h2 (by linarith)
def c1On (A : Set Vec4) : Set (Vec4 → ℝ) := {f | ContDiff ℝ 1 f ∧ tsupport f ⊆ A}
theorem eq_zero_of_not_mem {A : Set Vec4} {f : Vec4 → ℝ} (hf : f ∈ c1On A) {x : Vec4} (hx : x ∉ A) :
    f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hf.2 h)
theorem fderiv_eq_zero_of_not_mem {A : Set Vec4} {f : Vec4 → ℝ} (hf : f ∈ c1On A) {x : Vec4}
    (hx : x ∉ A) : fderiv ℝ f x = 0 :=
  fderiv_of_notMem_tsupport ℝ fun h => hx (hf.2 h)
theorem sub_mem_c1On {A : Set Vec4} (hA : IsClosed A) {f h : Vec4 → ℝ} (hf : f ∈ c1On A)
    (hh : h ∈ c1On A) : f - h ∈ c1On A := by
  refine ⟨hf.1.sub hh.1, closure_minimal (fun x hx => ?_) hA⟩
  by_contra hn
  exact hx (by simp [eq_zero_of_not_mem hf hn, eq_zero_of_not_mem hh hn])
def valueDerivMap (A : Set Vec4) (f : c1On A) : C(A, ℝ × (Vec4 →L[ℝ] ℝ)) :=
  ⟨fun x => (f.1 x.1, fderiv ℝ f.1 x.1),
    ((f.2.1.continuous.comp continuous_subtype_val).prodMk
      ((f.2.1.continuous_fderiv (by norm_num)).comp continuous_subtype_val))⟩
theorem exists_c1Bound {A : Set Vec4} (hA : IsCompact A) {f : Vec4 → ℝ} (hf : f ∈ c1On A) :
    ∃ b, C1BoundedBy f b := by
  have hK : IsCompact (tsupport f) := hA.of_isClosed_subset (isClosed_tsupport _) hf.2
  obtain ⟨b₁, h₁⟩ := (show HasCompactSupport f from hK).exists_bound_of_continuous hf.1.continuous
  have hd : HasCompactSupport (fderiv ℝ f) := (show HasCompactSupport f from hK).fderiv (𝕜 := ℝ)
  obtain ⟨b₂, h₂⟩ := hd.exists_bound_of_continuous (hf.1.continuous_fderiv (by norm_num))
  exact ⟨max b₁ b₂, fun x => ⟨(h₁ x).trans (le_max_left _ _), (h₂ x).trans (le_max_right _ _)⟩⟩
theorem exists_countable_dense_c1On {A : Set Vec4} (hA : IsCompact A) :
    ∃ D : Set (Vec4 → ℝ), D.Countable ∧ D ⊆ c1On A ∧ ∀ f ∈ c1On A, ∀ ε : ℝ, 0 < ε →
      ∃ h ∈ D, C1BoundedBy (f - h) ε := by
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hs : IsSeparable (range (valueDerivMap A)) := IsSeparable.of_separableSpace _
  obtain ⟨t, hts, htc, hdense⟩ := hs.exists_countable_dense_subset
  have hpre : ∀ y : t, ∃ g : c1On A, valueDerivMap A g = y.1 := fun y => hts y.2
  choose g hg using hpre
  have := htc.to_subtype
  refine ⟨range fun y : t => (g y).1, countable_range _, ?_, fun f hf ε hε => ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (g y).2
  · obtain ⟨y, hy, hd⟩ := (Metric.mem_closure_iff (α := C(A, ℝ × (Vec4 →L[ℝ] ℝ)))).1
      (hdense ⟨⟨f, hf⟩, rfl⟩) ε hε
    refine ⟨(g ⟨y, hy⟩).1, ⟨⟨y, hy⟩, rfl⟩, fun x => ?_⟩
    set h := (g ⟨y, hy⟩).1 with hh
    have hhA : h ∈ c1On A := (g ⟨y, hy⟩).2
    by_cases hx : x ∈ A
    · have h₁ : dist (valueDerivMap A ⟨f, hf⟩ ⟨x, hx⟩) (y ⟨x, hx⟩) < ε :=
        (ContinuousMap.dist_apply_le_dist _).trans_lt hd
      have hyx : y ⟨x, hx⟩ = (h x, fderiv ℝ h x) := by
        have := hg ⟨y, hy⟩
        rw [← show valueDerivMap A (g ⟨y, hy⟩) = y from this]
        rfl
      rw [hyx] at h₁
      have h₂ : dist (f x) (h x) < ε ∧ dist (fderiv ℝ f x) (fderiv ℝ h x) < ε := by
        have h₃ : max (dist (f x) (h x)) (dist (fderiv ℝ f x) (fderiv ℝ h x)) < ε := h₁
        exact ⟨(le_max_left _ _).trans_lt h₃, (le_max_right _ _).trans_lt h₃⟩
      constructor
      · have := h₂.1
        rw [Real.dist_eq] at this
        exact this.le
      · have e : fderiv ℝ (f - h) x = fderiv ℝ f x - fderiv ℝ h x :=
          fderiv_sub ((hf.1.differentiable (by norm_num)) x)
            ((hhA.1.differentiable (by norm_num)) x)
        rw [e, ← dist_eq_norm]
        exact h₂.2.le
    · have e : fderiv ℝ (f - h) x = 0 :=
        fderiv_eq_zero_of_not_mem (sub_mem_c1On hA.isClosed hf hhA) hx
      rw [e]
      simp only [Pi.sub_apply, eq_zero_of_not_mem hf hx, eq_zero_of_not_mem hhA hx, sub_self,
        abs_zero, norm_zero, and_self]
      exact hε.le
def ballUnion (T : Finset (ℕ × ℕ)) : Set Vec4 :=
  ⋃ p ∈ T, Metric.closedBall (denseSeq Vec4 p.1) (1 / ((p.2 : ℝ) + 1))
theorem isCompact_ballUnion (T : Finset (ℕ × ℕ)) : IsCompact (ballUnion T) :=
  T.isCompact_biUnion fun _ _ => isCompact_closedBall _ _
theorem exists_ballUnion_near {K : Set Vec4} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T, K ⊆ ballUnion T ∧ ∀ y ∈ ballUnion T, ∃ x ∈ K, ‖y - x‖ < δ := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hδ)
  have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hx : ∀ x : Vec4, ∃ a : ℕ, dist x (denseSeq Vec4 a) < 1 / ((m : ℝ) + 1) := fun x =>
    (denseRange_denseSeq Vec4).exists_dist_lt x hr
  choose a ha using hx
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover
    (fun x => Metric.ball (denseSeq Vec4 (a x)) (1 / ((m : ℝ) + 1)))
    fun x _ => Metric.isOpen_ball.mem_nhds (ha x)
  classical
  refine ⟨t.image fun x => (a x, m), fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcov hy)
    refine mem_iUnion₂.2 ⟨(a x, m), Finset.mem_image_of_mem _ hxt, ?_⟩
    exact Metric.ball_subset_closedBall hyx
  · obtain ⟨p, hp, hy'⟩ := mem_iUnion₂.1 hy
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.1 hp
    refine ⟨x, htK x hxt, ?_⟩
    have h₁ : dist y (denseSeq Vec4 (a x)) ≤ 1 / ((m : ℝ) + 1) := hy'
    have h₂ := ha x
    rw [dist_comm] at h₂
    have h₃ := dist_triangle y (denseSeq Vec4 (a x)) x
    rw [← dist_eq_norm]
    linarith
theorem exists_pos_lower_bound {ι : Type*} [Finite ι] (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ g i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min g
    exact ⟨g i₀, hg i₀, hi₀⟩
theorem exists_radius_gap {n : ℕ} {A : Fin n → Set Vec4} (hA : ∀ i, IsCompact (A i))
    (hdis : Pairwise fun i k => Disjoint (A i) (A k)) :
    ∃ R d : ℝ, 0 < R ∧ 0 < d ∧ (∀ i, ∃ y, A i ⊆ closedBallR4 y R) ∧
      ∀ i k, i ≠ k → ∀ x ∈ A i, ∀ y ∈ A k, d ≤ ‖x - y‖ := by
  have hU : IsCompact (⋃ i, A i) := isCompact_iUnion hA
  obtain ⟨r, hr⟩ := hU.isBounded.subset_closedBall (0 : Vec4)
  have hpair : ∀ p : Fin n × Fin n, ∃ e : ℝ, 0 < e ∧
      (p.1 ≠ p.2 → ∀ x ∈ A p.1, ∀ y ∈ A p.2, e ≤ ‖x - y‖) := by
    rintro ⟨i, k⟩
    by_cases hik : i = k
    · exact ⟨1, one_pos, fun h => (h hik).elim⟩
    · obtain ⟨e, he, hxy⟩ := Metric.exists_pos_forall_lt_edist (hA i) (hA k).isClosed (hdis hik)
      refine ⟨e, by exact_mod_cast he, fun _ x hx y hy => ?_⟩
      have h := hxy x hx y hy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        e.coe_nonneg, dist_eq_norm] at h
      exact h.le
  choose e he hxy using hpair
  obtain ⟨d, hd, hde⟩ := exists_pos_lower_bound e he
  refine ⟨2 * (|r| + 1), d, by positivity, hd, fun i => ⟨0, fun x hx => ?_⟩,
    fun i k hik x hx y hy => (hde (i, k)).trans (hxy (i, k) hik x hx y hy)⟩
  have h₁ : ‖x‖ ≤ r := by
    simpa [dist_eq_norm] using hr (mem_iUnion.2 ⟨i, hx⟩)
  have h₂ := euclidNormVec_le_two_mul (x - 0)
  rw [sub_zero] at h₂
  show euclidNormVec (x - 0) ≤ _
  rw [sub_zero] at *
  nlinarith [le_abs_self r]
theorem supportedSeparated_of_subset {n : ℕ} {A : Fin n → Set Vec4} {R d : ℝ}
    (hR : ∀ i, ∃ y, A i ⊆ closedBallR4 y R)
    (hd : ∀ i k, i ≠ k → ∀ x ∈ A i, ∀ y ∈ A k, d ≤ ‖x - y‖) (X : SepTupleOfCard n)
    (hX : ∀ i, tsupport (X.1 i) ⊆ A i) : SupportedSeparated R d X := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hR i
    exact ⟨y, (hX i).trans hy⟩
  · refine le_iInf fun i => le_iInf fun k => le_iInf fun hik => ?_
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    exact (hd i k hik x (hX i hx) y (hX k hy)).trans (supNorm_le_euclidNormVec _)
theorem exists_supportedSeparated {n : ℕ} (X : SepTupleOfCard n) :
    ∃ R d : ℝ, 0 < R ∧ 0 < d ∧ SupportedSeparated R d X := by
  obtain ⟨R, d, hR, hd, h₁, h₂⟩ := exists_radius_gap (A := fun i => tsupport (X.1 i))
    (fun i => (X.2.1 i).2.1) X.2.2
  exact ⟨R, d, hR, hd, supportedSeparated_of_subset h₁ h₂ X fun _ => subset_rfl⟩
theorem mem_disjointSupportTuples_of_c1On {n : ℕ} {A : Fin n → Set Vec4}
    (hA : ∀ i, IsCompact (A i)) (hdis : Pairwise fun i k => Disjoint (A i) (A k))
    {u : Fin n → Vec4 → ℝ} (hu : ∀ i, u i ∈ c1On (A i)) :
    u ∈ TestSpaces.disjointSupportTuples (univ : Set Vec4) n :=
  ⟨fun i => ⟨(hu i).1, (hA i).of_isClosed_subset (isClosed_tsupport _) (hu i).2, subset_univ _⟩,
    fun i k hik => (hdis hik).mono (hu i).2 (hu k).2⟩
theorem abs_sub_le_of_c1Close {n : ℕ} {A : Fin n → Set Vec4} (hA : ∀ i, IsCompact (A i))
    (hdis : Pairwise fun i k => Disjoint (A i) (A k)) (Ψ : SepTupleOfCard n → ℝ)
    (hΨ : TestSpaces.IsMultilinearOnSep Ψ) {c M B ε : ℝ} (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hbound : ∀ Y : SepTupleOfCard n, (∀ i, tsupport (Y.1 i) ⊆ A i) →
      |Ψ Y| ≤ c * sharpNormProd M Y)
    {u v : Fin n → Vec4 → ℝ} (hu : ∀ i, u i ∈ c1On (A i)) (hv : ∀ i, v i ∈ c1On (A i))
    (huB : ∀ i, C1BoundedBy (u i) B) (hvB : ∀ i, C1BoundedBy (v i) B)
    (huv : ∀ i, C1BoundedBy (u i - v i) ε) :
    |Ψ ⟨u, mem_disjointSupportTuples_of_c1On hA hdis hu⟩ -
        Ψ ⟨v, mem_disjointSupportTuples_of_c1On hA hdis hv⟩| ≤
      n * (c * (40 * M * ε * (40 * M * B) ^ (n - 1))) := by
  classical
  set w : ℕ → Fin n → Vec4 → ℝ := fun k i => if (i : ℕ) < k then v i else u i with hw
  have hwm : ∀ k i, w k i ∈ c1On (A i) := fun k i => by
    simp only [hw]
    split_ifs
    exacts [hv i, hu i]
  have hwB : ∀ k i, C1BoundedBy (w k i) B := fun k i => by
    simp only [hw]
    split_ifs
    exacts [hvB i, huB i]
  let W : ℕ → SepTupleOfCard n := fun k => ⟨w k, mem_disjointSupportTuples_of_c1On hA hdis (hwm k)⟩
  have hstep : ∀ k, k < n → |Ψ (W k) - Ψ (W (k + 1))| ≤
      c * (40 * M * ε * (40 * M * B) ^ (n - 1)) := by
    intro k hk
    set i : Fin n := ⟨k, hk⟩ with hi
    have hwi : w k i = u i := by simp [hw, hi]
    have hwi' : w (k + 1) i = v i := by simp [hw, hi]
    have hoff : ∀ l, l ≠ i → w k l = w (k + 1) l := fun l hl => by
      have hl' : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
      simp only [hw]
      by_cases h : (l : ℕ) < k
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    have hd : u i - v i ∈ c1On (A i) := sub_mem_c1On (hA i).isClosed (hu i) (hv i)
    have hm'' : ∀ l, Function.update (w k) i (u i - v i) l ∈ c1On (A l) := fun l => by
      by_cases hl : l = i
      · subst hl
        simpa using hd
      · simpa [Function.update_of_ne hl] using hwm k l
    let Z : SepTupleOfCard n := ⟨_, mem_disjointSupportTuples_of_c1On hA hdis hm''⟩
    have hrel := hΨ i 1 (-1) (W k) (W (k + 1)) Z hoff
      (by
        show Function.update (w k) i (u i - v i) i = (1 : ℝ) • w k i + (-1 : ℝ) • w (k + 1) i
        rw [Function.update_self, hwi, hwi']
        funext x
        simp [sub_eq_add_neg])
      (fun l hl => by
        show Function.update (w k) i (u i - v i) l = w k l
        rw [Function.update_of_ne hl])
    have he : Ψ (W k) - Ψ (W (k + 1)) = Ψ Z := by rw [hrel]; ring
    rw [he]
    refine (hbound Z fun l => (hm'' l).2).trans (mul_le_mul_of_nonneg_left ?_ hc)
    unfold sharpNormProd
    have hg : ∀ l ∈ (Finset.univ : Finset (Fin n)), sharpNormR4 M (Z.1 l) ≤
        if l = i then 40 * M * ε else 40 * M * B := by
      intro l _
      by_cases hl : l = i
      · subst hl
        rw [if_pos rfl]
        show sharpNormR4 M (Function.update (w k) i (u i - v i) i) ≤ _
        rw [Function.update_self]
        exact sharpNormR4_le_of_bound hM hd.1 (huv i)
      · rw [if_neg hl]
        show sharpNormR4 M (Function.update (w k) i (u i - v i) l) ≤ _
        rw [Function.update_of_ne hl]
        exact sharpNormR4_le_of_bound hM (hwm k l).1 (hwB k l)
    refine (Finset.prod_le_prod (fun l _ => sharpNormR4_nonneg M _) hg).trans (le_of_eq ?_)
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => 40 * M * B) fun l hl => by
      rw [if_neg (Finset.ne_of_mem_erase hl)]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hsum : ∀ k, k ≤ n → |Ψ (W 0) - Ψ (W k)| ≤
      k * (c * (40 * M * ε * (40 * M * B) ^ (n - 1))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h₁ := ih (by omega)
      have h₂ := hstep k (by omega)
      have h₃ : Ψ (W 0) - Ψ (W (k + 1)) = (Ψ (W 0) - Ψ (W k)) + (Ψ (W k) - Ψ (W (k + 1))) := by
        ring
      rw [h₃]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
  have h0 : W 0 = ⟨u, mem_disjointSupportTuples_of_c1On hA hdis hu⟩ := Subtype.ext (by
    funext i
    simp [W, hw])
  have hn : W n = ⟨v, mem_disjointSupportTuples_of_c1On hA hdis hv⟩ := Subtype.ext (by
    funext i
    simp [W, hw])
  have := hsum n le_rfl
  rwa [h0, hn] at this
theorem exists_countable_universal_approximants :
    ∃ G : Set (Vec4 → ℝ), G.Countable ∧ ∀ T : Finset (ℕ × ℕ),
      ∀ f ∈ c1On (ballUnion T), ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ G, h ∈ c1On (ballUnion T) ∧ C1BoundedBy (f - h) ε := by
  choose D hDc hDs hDa using fun T => exists_countable_dense_c1On (isCompact_ballUnion T)
  refine ⟨⋃ T, D T, countable_iUnion hDc, fun T f hf ε hε => ?_⟩
  obtain ⟨h, hh, hfh⟩ := hDa T f hf ε hε
  exact ⟨h, mem_iUnion.2 ⟨T, hh⟩, hDs T hh, hfh⟩
theorem exists_common_convergent_subseq {I : Type} [Countable I] (w : I → ℕ → ℝ) (b : I → ℝ)
    (hb : ∀ ι j, |w ι j| ≤ b ι) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ι, ∃ z, Tendsto (fun i => w ι (φ i)) atTop (𝓝 z) := by
  have hK : IsCompact (Set.pi univ fun ι => Icc (-b ι) (b ι)) :=
    isCompact_univ_pi fun ι => isCompact_Icc
  obtain ⟨a, -, φ, hφ, ht⟩ := hK.tendsto_subseq (x := fun j ι => w ι j)
    fun j ι _ => abs_le.1 (hb ι j)
  exact ⟨φ, hφ, fun ι => ⟨a ι, (tendsto_pi_nhds.1 ht) ι⟩⟩
theorem C1BoundedBy.mono {f : Vec4 → ℝ} {b b' : ℝ} (h : C1BoundedBy f b) (hb : b ≤ b') :
    C1BoundedBy f b' :=
  fun x => ⟨(h x).1.trans hb, (h x).2.trans hb⟩
theorem C1BoundedBy.of_sub {f h : Vec4 → ℝ} (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h)
    {b ε : ℝ} (h₁ : C1BoundedBy f b) (h₂ : C1BoundedBy (f - h) ε) : C1BoundedBy h (b + ε) := by
  intro x
  constructor
  · have e : h x = f x - (f - h) x := by simp
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (h₁ x).1 (h₂ x).1)
  · have e : fderiv ℝ (f - h) x = fderiv ℝ f x - fderiv ℝ h x :=
      fderiv_sub ((hf.differentiable (by norm_num)) x) ((hh.differentiable (by norm_num)) x)
    have e' : fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ (f - h) x := by rw [e]; abel
    rw [e']
    exact (norm_sub_le _ _).trans (add_le_add (h₁ x).2 (h₂ x).2)
theorem exists_subseq_tendsto_all_tuples {M : ℝ} (hM : 1 ≤ M)
    (Φ : ℕ → ∀ n, SepTupleOfCard n → ℝ)
    (hml : ∀ j n, 2 ≤ n → TestSpaces.IsMultilinearOnSep (Φ j n)) (C : ℕ → ℝ → ℝ → ℝ)
    (hb : ∀ j n, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d → ∀ X : SepTupleOfCard n,
      SupportedSeparated R d X → |Φ j n X| ≤ C n d R * sharpNormProd M X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : SepTupleOfCard n,
      ∃ z, Tendsto (fun i => Φ (φ i) n X) atTop (𝓝 z) := by
  classical
  obtain ⟨G, hGc, hG⟩ := exists_countable_universal_approximants
  have := hGc.to_subtype
  let I : Type := Σ n : ℕ, Fin n → G
  let tupleOf : (ι : I) → Fin ι.1 → Vec4 → ℝ := fun ι i => (ι.2 i).1
  let w : I → ℕ → ℝ := fun ι j =>
    if h : 2 ≤ ι.1 ∧ tupleOf ι ∈ TestSpaces.disjointSupportTuples (univ : Set Vec4) ι.1 then
      Φ j ι.1 ⟨tupleOf ι, h.2⟩ else 0
  have hbd : ∀ ι, ∃ b, ∀ j, |w ι j| ≤ b := by
    intro ι
    by_cases h : 2 ≤ ι.1 ∧ tupleOf ι ∈ TestSpaces.disjointSupportTuples (univ : Set Vec4) ι.1
    · obtain ⟨R, d, hR, hd, hX⟩ :=
        exists_supportedSeparated (⟨tupleOf ι, h.2⟩ : SepTupleOfCard ι.1)
      refine ⟨C ι.1 d R * sharpNormProd M ⟨tupleOf ι, h.2⟩, fun j => ?_⟩
      simp only [w, dif_pos h]
      exact hb j _ h.1 R d hR hd _ hX
    · exact ⟨0, fun j => by simp [w, dif_neg h]⟩
  choose b hb' using hbd
  obtain ⟨φ, hφ, hlim⟩ := exists_common_convergent_subseq w b hb'
  refine ⟨φ, hφ, fun n hn X => ?_⟩
  suffices hc : CauchySeq fun i => Φ (φ i) n X from cauchySeq_tendsto_of_complete hc
  rw [Metric.cauchySeq_iff]
  intro η hη
  obtain ⟨R₀, d₀, -, hd₀, -, hsep₀⟩ := exists_radius_gap
    (A := fun i => tsupport (X.1 i)) (fun i => (X.2.1 i).2.1) X.2.2
  have hcov := fun i => exists_ballUnion_near (K := tsupport (X.1 i)) (X.2.1 i).2.1
    (δ := d₀ / 4) (by positivity)
  choose T hKT hTK using hcov
  let A : Fin n → Set Vec4 := fun i => ballUnion (T i)
  have hAc : ∀ i, IsCompact (A i) := fun i => isCompact_ballUnion _
  have hdis : Pairwise fun i k => Disjoint (A i) (A k) := by
    intro i k hik
    refine Set.disjoint_left.2 fun y hyi hyk => ?_
    obtain ⟨x, hx, hxy⟩ := hTK i y hyi
    obtain ⟨x', hx', hxy'⟩ := hTK k y hyk
    have h₁ := hsep₀ i k hik x hx x' hx'
    have h₂ : ‖x - x'‖ ≤ ‖y - x'‖ + ‖y - x‖ := by
      have e : x - x' = (y - x') - (y - x) := by abel
      rw [e]
      exact norm_sub_le _ _
    linarith
  obtain ⟨R, d, hR, hd, hRb, hsep⟩ := exists_radius_gap hAc hdis
  have hXA : ∀ i, X.1 i ∈ c1On (A i) := fun i => ⟨(X.2.1 i).1, hKT i⟩
  have hbX : ∀ i, ∃ b, C1BoundedBy (X.1 i) b := fun i => exists_c1Bound (hAc i) (hXA i)
  choose bX hbX using hbX
  set B₀ : ℝ := ∑ i, |bX i| with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hXB : ∀ i, C1BoundedBy (X.1 i) B₀ := fun i => (hbX i).mono
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |bX i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  set c : ℝ := |C n d R| with hc
  set W : ℝ := n * (c * (40 * M * (40 * M * (B₀ + 1)) ^ (n - 1))) with hW
  have hM0 : (0 : ℝ) ≤ 40 * M := by linarith
  have hW0 : 0 ≤ W := by
    have : 0 ≤ 40 * M * (B₀ + 1) := mul_nonneg hM0 (by linarith)
    positivity
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
  have happ := fun i => hG (T i) (X.1 i) (hXA i) ε hε0
  choose H hHG hHc hHn using happ
  have hHB : ∀ i, C1BoundedBy (H i) (B₀ + 1) := fun i =>
    (C1BoundedBy.of_sub (hXA i).1 (hHc i).1 (hXB i) (hHn i)).mono (by linarith)
  have hmem : H ∈ TestSpaces.disjointSupportTuples (univ : Set Vec4) n :=
    mem_disjointSupportTuples_of_c1On hAc hdis hHc
  let ι₀ : I := ⟨n, fun i => ⟨H i, hHG i⟩⟩
  have hw : ∀ j, w ι₀ j = Φ j n ⟨H, hmem⟩ := fun j =>
    dif_pos (show 2 ≤ ι₀.1 ∧ tupleOf ι₀ ∈ TestSpaces.disjointSupportTuples (univ : Set Vec4) ι₀.1
      from ⟨hn, hmem⟩)
  have hclose : ∀ j, |Φ j n X - Φ j n ⟨H, hmem⟩| ≤ W * ε := by
    intro j
    have hbound : ∀ Y : SepTupleOfCard n, (∀ i, tsupport (Y.1 i) ⊆ A i) →
        |Φ j n Y| ≤ c * sharpNormProd M Y := fun Y hY => by
      refine (hb j n hn R d hR hd Y (supportedSeparated_of_subset hRb hsep Y hY)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self _)
        (Finset.prod_nonneg fun i _ => sharpNormR4_nonneg _ _)
    have h := abs_sub_le_of_c1Close hAc hdis (Φ j n) (hml j n hn) (abs_nonneg _) hM hbound hXA hHc
      (fun i => (hXB i).mono (by linarith)) hHB hHn
    refine h.trans (le_of_eq ?_)
    rw [hW]
    ring
  obtain ⟨z, hz⟩ := hlim ι₀
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hz.cauchySeq (η / 3) (by positivity)
  refine ⟨N, fun p hp q hq => ?_⟩
  have h₁ := hN p hp q hq
  simp only [hw, Real.dist_eq] at h₁
  have h₂ := (hclose (φ p)).trans_lt hWε
  have h₃ := (hclose (φ q)).trans_lt hWε
  rw [Real.dist_eq]
  have h₄ := abs_sub_lt_iff.1 h₁
  have h₅ := abs_sub_lt_iff.1 h₂
  have h₆ := abs_sub_lt_iff.1 h₃
  exact abs_sub_lt_iff.2 ⟨by linarith [h₄.1, h₅.1, h₆.2], by linarith [h₄.2, h₅.2, h₆.1]⟩
open InfiniteLattice (compactTestFunctions ursellFunction GaugeField)
open InfiniteLattice.CenteredIdentity (UrsellIsRealSymmetricMultilinear)
theorem mem_compactTestFunctions {f : Vec4 → ℝ} (h₁ : ContDiff ℝ 1 f) (h₂ : HasCompactSupport f) :
    f ∈ compactTestFunctions := by
  obtain ⟨C, hC⟩ := h₂.exists_bound_of_continuous h₁.continuous
  exact ⟨h₁.continuous.measurable, ⟨C, hC⟩, h₂⟩
theorem tuple_mem_compactTestFunctions {n : ℕ} (X : SepTupleOfCard n) (i : Fin n) :
    X.1 i ∈ compactTestFunctions :=
  mem_compactTestFunctions (X.2.1 i).1 (X.2.1 i).2.1
def realUrsell {a : ℝ} (ν : Measure (GaugeField a)) (n : ℕ) (X : SepTupleOfCard n) : ℝ :=
  (ursellFunction ν n X.1).re
theorem isMultilinearOnSep_realUrsell {a : ℝ} {ν : Measure (GaugeField a)} {n : ℕ}
    (h : UrsellIsRealSymmetricMultilinear ν n) :
    TestSpaces.IsMultilinearOnSep (realUrsell ν n) := by
  intro i b b' X X' X'' hXX' hi hoff
  have hbT : b • X.1 i ∈ compactTestFunctions :=
    mem_compactTestFunctions ((X.2.1 i).1.const_smul b) (X.2.1 i).2.1.smul_left
  have hb'T : b' • X'.1 i ∈ compactTestFunctions :=
    mem_compactTestFunctions ((X'.2.1 i).1.const_smul b') (X'.2.1 i).2.1.smul_left
  set f₁ := Function.update X.1 i (b • X.1 i) with hf₁
  have hf₁T : ∀ l, f₁ l ∈ compactTestFunctions := fun l => by
    by_cases hl : l = i
    · subst hl
      simpa [hf₁] using hbT
    · simpa [hf₁, Function.update_of_ne hl] using tuple_mem_compactTestFunctions X l
  have e₁ : ursellFunction ν n f₁ = (b : ℂ) * ursellFunction ν n X.1 :=
    (h X.1 (tuple_mem_compactTestFunctions X)).2.2.2 i b
  have e₂ := (h f₁ hf₁T).2.2.1 i _ hb'T
  have e₃ : Function.update f₁ i (b' • X'.1 i) = Function.update X'.1 i (b' • X'.1 i) := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hf₁, Function.update_of_ne hl, hXX' l hl]
  have e₄ : ursellFunction ν n (Function.update X'.1 i (b' • X'.1 i)) =
      (b' : ℂ) * ursellFunction ν n X'.1 :=
    (h X'.1 (tuple_mem_compactTestFunctions X')).2.2.2 i b'
  have e₅ : X''.1 = Function.update f₁ i (f₁ i + b' • X'.1 i) := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hf₁, hi]
    · simp [hf₁, Function.update_of_ne hl, hoff l hl]
  have e₆ : ursellFunction ν n X''.1 =
      (b : ℂ) * ursellFunction ν n X.1 + (b' : ℂ) * ursellFunction ν n X'.1 := by
    rw [e₅, e₂, e₃, e₁, e₄]
  simp only [realUrsell, e₆, Complex.add_re, Complex.re_ofReal_mul]
theorem ofReal_realUrsell {a : ℝ} {ν : Measure (GaugeField a)} {n : ℕ}
    (h : UrsellIsRealSymmetricMultilinear ν n) (X : SepTupleOfCard n) :
    ((realUrsell ν n X : ℝ) : ℂ) = ursellFunction ν n X.1 :=
  Complex.ext (by simp [realUrsell]) (by simpa [realUrsell] using
    (h X.1 (tuple_mem_compactTestFunctions X)).1.symm)
theorem tendsto_natPred_atTop : Tendsto PNat.natPred atTop atTop := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicExtensions.tendsto_pnatNatPred_atTop <;> assumption
theorem separatedLimitsExist_of (hC : InfiniteLattice.CenteredIdentity.Statement)
    (hE : EntrywiseMultilinearity.Statement) : BoundsOnEverySide.SeparatedLimitsExist := by
  intro L hL M hM Q C hQ s
  have hstate : ∀ j n, 2 ≤ n → UrsellIsRealSymmetricMultilinear (Q.gibbs j) n :=
    fun j n hn => (hC ⟨L, hL, Q.K j, 1⟩ (Q.gibbs j) (Q.gibbs_mem j).1.1).2.1 n hn
  have hbound : ∀ j n, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d → ∀ X : SepTupleOfCard n,
      SupportedSeparated R d X →
        |realUrsell (Q.gibbs j) n X| ≤ C n d R * sharpNormProd M X := fun j n hn R d hR hd X hX =>
    (Complex.abs_re_le_norm _).trans (hQ j n hn R d hR hd X hX)
  obtain ⟨φ₀, hφ₀, hlim⟩ := exists_subseq_tendsto_all_tuples hM
    (fun j n => realUrsell (Q.gibbs j.succPNat) n)
    (fun j n hn => isMultilinearOnSep_realUrsell (hstate _ n hn)) C
    (fun j n hn => hbound _ n hn)
  choose z hz using hlim
  let φ : ℕ+ → ℕ+ := fun i => (φ₀ i.natPred).succPNat
  have hconv : ∀ n (hn : 2 ≤ n) (X : SepTupleOfCard n),
      Tendsto (fun i => realUrsell (Q.gibbs (φ i)) n X) atTop (𝓝 (z n hn X)) :=
    fun n hn X => (hz n hn X).comp tendsto_natPred_atTop
  let S : AmbientPoints.TupleMapFamily s .euclidean :=
    fun n hn f => z n hn ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
  have hmult : ∀ (n : ℕ) (hn : 2 ≤ n), TestSpaces.IsMultilinearOnSep (restrictToTestTuples S n hn) := by
    intro n hn i b b' X X' X'' h₁ h₂ h₃
    refine tendsto_nhds_unique (hconv n hn X'') ?_
    refine (((hconv n hn X).const_mul b).add ((hconv n hn X').const_mul b')).congr fun k => ?_
    exact (isMultilinearOnSep_realUrsell (hstate (φ k) n hn) i b b' X X' X'' h₁ h₂ h₃).symm
  have hml : ∀ (n : ℕ) (hn : 2 ≤ n), AmbientPoints.IsTupleMultilinear (S n hn) := fun n hn =>
    (((hE s).1 n (by omega)).2.2 _ _
      (fun f X he => congrArg (S n hn) (Subtype.ext he))).2 (hmult n hn)
  refine ⟨φ, S, ⟨?_, ?_, ⟨hml, ⟨S, hml⟩, rfl⟩, ?_, ?_⟩⟩
  · intro i i' h
    refine Nat.succPNat_lt_succPNat.2 (hφ₀ ?_)
    have h₁ := PNat.natPred_add_one i
    have h₂ := PNat.natPred_add_one i'
    have h₃ : (i : ℕ) < i' := h
    omega
  · intro n hn f
    let X : SepTupleOfCard n := ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
    refine ((Complex.continuous_ofReal.tendsto _).comp (hconv n hn X)).congr fun i => ?_
    exact ofReal_realUrsell (hstate (φ i) n hn) X
  · intro n hn f ς
    let X : SepTupleOfCard n := ⟨f.1, (AmbientPoints.mem_separatedTuples_r4_iff f.1).1 f.2⟩
    let X' : SepTupleOfCard n := ⟨AmbientPoints.permuteTuple ς f.1,
      (AmbientPoints.mem_separatedTuples_r4_iff _).1 (AmbientPoints.permuteTuple_mem f.2 ς)⟩
    refine tendsto_nhds_unique (hconv n hn X') ((hconv n hn X).congr fun i => ?_)
    exact congrArg Complex.re
      ((hstate (φ i) n hn X.1 (tuple_mem_compactTestFunctions X)).2.1 ς).symm
  · intro n hn R d hR hd X hX
    refine le_of_tendsto (hconv n hn X).abs (Eventually.of_forall fun i => ?_)
    exact hbound _ n hn R d hR hd X hX
end BoundsOnEverySide.SubsequentialLimits
end
end YangMills.Construction
