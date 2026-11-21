import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctionsProof
import YangMills.Construction.TwoPoints.PartsOfATestPlateProof
import YangMills.Construction.Continuum.FromSmallSupportsToAllSupports
import YangMills.Construction.Continuum.PartitionOfUnityAndCutoffOfClassC1
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanBalls YangMills.Construction.TestFunctions YangMills.Construction.DisjointTuples
noncomputable section
namespace YangMills.Construction.LocalVanishing
variable {k n : ℕ}
theorem abs_apply_le_sqrtSumSq (v : Fin k → ℝ) (m : Fin k) : |v m| ≤ EuclideanCoords.sqrtSumSq v := by apply _root_.YangMills.Construction.TwoPoints.TestPlates.PlatePieces.abs_apply_le_euclidNorm <;> assumption
theorem dist_lt_of_sqrtSumSq_sub_le {x y : Fin k → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hxy : EuclideanCoords.sqrtSumSq (x - y) ≤ ε / 2) : dist x y < ε := by
  rw [dist_pi_lt_iff hε]
  intro m
  have hm := abs_apply_le_sqrtSumSq (x - y) m
  rw [Real.dist_eq]
  simp only [Pi.sub_apply] at hm
  linarith
theorem continuous_sqrtSumSq :
    Continuous (EuclideanCoords.sqrtSumSq : (Fin k → ℝ) → ℝ) := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.continuous_eucNorm <;> assumption
theorem isOpen_euclidBall (c : Fin k → ℝ) (r : ℝ) : IsOpen (euclidBall c r) :=
  isOpen_lt (continuous_sqrtSumSq.comp (continuous_id.sub continuous_const)) continuous_const
theorem mem_euclidBall_self (c : Fin k → ℝ) {r : ℝ} (hr : 0 < r) : c ∈ euclidBall c r := by
  simp [euclidBall, EuclideanCoords.sqrtSumSq, hr]
theorem zero_mem_compactC1 : (0 : (Fin k → ℝ) → ℂ) ∈ compactC1 k ℂ :=
  ⟨contDiff_const, HasCompactSupport.zero⟩
theorem update_mem_of_tsupport_subset {g : Fin n → (Fin k → ℝ) → ℂ}
    (hg : g ∈ disjointSupportTuples k n) {i : Fin n}
    {u : (Fin k → ℝ) → ℂ} (hu : u ∈ compactC1 k ℂ) (hs : tsupport u ⊆ tsupport (g i)) :
    Function.update g i u ∈ disjointSupportTuples k n := by
  refine ⟨fun j => ?_, fun j l hjl => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using hu
    · simpa [Function.update_of_ne hj] using hg.1 j
  · by_cases hj : j = i
    · subst hj
      have hl : l ≠ j := hjl.symm
      rw [Function.update_self, Function.update_of_ne hl]
      exact (hg.2 hjl).mono_left hs
    · by_cases hl : l = i
      · subst hl
        rw [Function.update_self, Function.update_of_ne hj]
        exact (hg.2 hjl).mono_right hs
      · simpa [Function.update_of_ne hj, Function.update_of_ne hl] using hg.2 hjl
theorem apply_congr_tuple (D : disjointSupportTuples k n → ℂ) {p q : Fin n → (Fin k → ℝ) → ℂ}
    (hp : p ∈ disjointSupportTuples k n) (hq : q ∈ disjointSupportTuples k n) (hpq : p = q) :
    D ⟨p, hp⟩ = D ⟨q, hq⟩ := by
  subst hpq
  rfl
theorem eq_zero_of_entry_eq_zero {D : disjointSupportTuples k n → ℂ} (hD : IsSeparatelyLinear D)
    {g : Fin n → (Fin k → ℝ) → ℂ} (hg : g ∈ disjointSupportTuples k n) {i : Fin n} (hi : g i = 0) :
    D ⟨g, hg⟩ = 0 := by
  have hself : Function.update g i 0 = g := by
    rw [← hi, Function.update_eq_self]
  have hm : Function.update g i 0 ∈ disjointSupportTuples k n := by rwa [hself]
  have e₁ := hD i 1 g 0 hg hm
  have e₂ : D ⟨Function.update g i (g i + (1 : ℂ) • 0),
      update_add_smul_mem_disjointSupportTuples 1 hg hm⟩ = D ⟨g, hg⟩ :=
    apply_congr_tuple D _ _ (by rw [hi]; simpa using hself)
  have e₃ : D ⟨Function.update g i 0, hm⟩ = D ⟨g, hg⟩ := apply_congr_tuple D _ _ hself
  rw [e₂, e₃] at e₁
  have e₄ : D ⟨g, hg⟩ + D ⟨g, hg⟩ = D ⟨g, hg⟩ := by simpa using e₁.symm
  simpa using e₄
theorem exists_update_sum_eq_zero {D : disjointSupportTuples k n → ℂ} (hD : IsSeparatelyLinear D)
    {g : Fin n → (Fin k → ℝ) → ℂ} (hg : g ∈ disjointSupportTuples k n) (i : Fin n) {ι : Type*}
    (I : Finset ι) (u : ι → (Fin k → ℝ) → ℂ)
    (hc : ∀ a ∈ I, u a ∈ compactC1 k ℂ) (hs : ∀ a ∈ I, tsupport (u a) ⊆ tsupport (g i))
    (hv : ∀ a ∈ I, ∀ hm : Function.update g i (u a) ∈ disjointSupportTuples k n,
      D ⟨Function.update g i (u a), hm⟩ = 0) :
    ∃ hm : Function.update g i (∑ a ∈ I, u a) ∈ disjointSupportTuples k n,
      D ⟨Function.update g i (∑ a ∈ I, u a), hm⟩ = 0 := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hm : Function.update g i (∑ a ∈ (∅ : Finset ι), u a) ∈ disjointSupportTuples k n := by
      rw [Finset.sum_empty]
      refine update_mem_of_tsupport_subset hg zero_mem_compactC1 ?_
      intro x hx
      have : tsupport (0 : (Fin k → ℝ) → ℂ) = ∅ := by simp [tsupport]
      rw [this] at hx
      exact hx.elim
    refine ⟨hm, eq_zero_of_entry_eq_zero hD hm (i := i) ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨hm, hz⟩ := ih (fun b hb => hc b (Finset.mem_insert_of_mem hb))
      (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      (fun b hb => hv b (Finset.mem_insert_of_mem hb))
    have hamem := Finset.mem_insert_self a s
    have hf : Function.update g i (u a) ∈ disjointSupportTuples k n :=
      update_mem_of_tsupport_subset hg (hc a hamem) (hs a hamem)
    have hidem : Function.update (Function.update g i (u a)) i (∑ b ∈ s, u b) =
        Function.update g i (∑ b ∈ s, u b) := by simp
    have hg' : Function.update (Function.update g i (u a)) i (∑ b ∈ s, u b) ∈
        disjointSupportTuples k n := by rwa [hidem]
    have hsum : Function.update (Function.update g i (u a)) i
        ((Function.update g i (u a)) i + (1 : ℂ) • ∑ b ∈ s, u b) =
        Function.update g i (∑ b ∈ insert a s, u b) := by
      rw [Finset.sum_insert ha]
      simp
    have hm' : Function.update g i (∑ b ∈ insert a s, u b) ∈ disjointSupportTuples k n := by
      rw [← hsum]
      exact update_add_smul_mem_disjointSupportTuples 1 hf hg'
    refine ⟨hm', ?_⟩
    have e₁ := hD i 1 (Function.update g i (u a)) (∑ b ∈ s, u b) hf hg'
    rw [apply_congr_tuple D (update_add_smul_mem_disjointSupportTuples 1 hf hg') hm' hsum,
      hv a hamem hf, apply_congr_tuple D hg' hm hidem, hz] at e₁
    simpa using e₁
theorem mul_factor_mem {χ : (Fin k → ℝ) → ℝ} (hχ : χ ∈ compactC1 k ℝ) {g : (Fin k → ℝ) → ℂ}
    (hg : g ∈ compactC1 k ℂ) :
    (fun z => (χ z : ℂ) * g z) ∈ compactC1 k ℂ ∧
      tsupport (fun z => (χ z : ℂ) * g z) ⊆ tsupport g ∧
      tsupport (fun z => (χ z : ℂ) * g z) ⊆ tsupport χ := by
  have hsg : tsupport (fun z => (χ z : ℂ) * g z) ⊆ tsupport g := by
    refine closure_mono fun z hz => ?_
    intro h0
    exact hz (by simp [h0])
  have hsχ : tsupport (fun z => (χ z : ℂ) * g z) ⊆ tsupport χ := by
    refine closure_mono fun z hz => ?_
    intro h0
    exact hz (by simp [h0])
  refine ⟨⟨(Complex.ofRealCLM.contDiff.comp hχ.1).mul hg.1, ?_⟩, hsg, hsχ⟩
  exact hg.2.of_isClosed_subset (isClosed_tsupport _) hsg
theorem eq_zero_of_vanishesNear_supportProduct (hcut : PartitionOfUnity.C1PartitionAndCutoffExist)
    (hk : k = 2 ∨ k = 4) {D : disjointSupportTuples k n → ℂ} (hD : IsSeparatelyLinear D)
    (f : disjointSupportTuples k n) (hC : IsCompact (supportProduct f))
    (hvan : ∀ x : injectiveTuples (Fin k → ℝ) n, x.1 ∈ supportProduct f → VanishesNearConfig D x) :
    D f = 0 := by
  classical
  let X := {x : injectiveTuples (Fin k → ℝ) n // x.1 ∈ supportProduct f}
  have hρ : ∀ x : X, ∃ ρ, IsVanishingRadius D x.1 ρ := fun x => hvan x.1 x.2
  choose ρ hρ using hρ
  let c : X → Set (Fin n → Fin k → ℝ) := fun x => Set.univ.pi fun i => euclidBall (x.1.1 i) (ρ x)
  have hopen : ∀ x, IsOpen (c x) := fun x =>
    isOpen_set_pi Set.finite_univ fun i _ => isOpen_euclidBall _ _
  have hinj : ∀ z ∈ supportProduct f, z ∈ injectiveTuples (Fin k → ℝ) n := by
    intro z hz i j hij
    by_contra hne
    exact Set.disjoint_left.1 (f.2.2 hne) (hz i (Set.mem_univ i))
      (by rw [hij]; exact hz j (Set.mem_univ j))
  have hcover : supportProduct f ⊆ ⋃ x, c x := by
    intro z hz
    refine Set.mem_iUnion.2 ⟨⟨⟨z, hinj z hz⟩, hz⟩, fun i _ => ?_⟩
    exact mem_euclidBall_self _ (hρ ⟨⟨z, hinj z hz⟩, hz⟩).1
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hC hopen hcover
  let Small : ((Fin k → ℝ) → ℂ) → Prop := fun w =>
    ∀ x ∈ tsupport w, ∀ y ∈ tsupport w, EuclideanCoords.sqrtSumSq (x - y) ≤ δ / 2
  have hbase : ∀ (g : Fin n → (Fin k → ℝ) → ℂ) (hg : g ∈ disjointSupportTuples k n),
      (∀ j, tsupport (g j) ⊆ tsupport (f.1 j)) → (∀ j, Small (g j)) → D ⟨g, hg⟩ = 0 := by
    intro g hg hsub hsmall
    by_cases hempty : ∃ j, tsupport (g j) = ∅
    · obtain ⟨j, hj⟩ := hempty
      refine eq_zero_of_entry_eq_zero hD hg (i := j) ?_
      funext z
      exact image_eq_zero_of_notMem_tsupport (by rw [hj]; exact Set.notMem_empty z)
    · have hne : ∀ j, (tsupport (g j)).Nonempty := fun j =>
        Set.nonempty_iff_ne_empty.2 fun h => hempty ⟨j, h⟩
      choose z hz using hne
      have hzC : z ∈ supportProduct f := fun j _ => hsub j (hz j)
      obtain ⟨x, hx⟩ := hleb z hzC
      refine (hρ x).2 ⟨g, hg⟩ fun j w hw => ?_
      have hd : dist w (z j) < δ :=
        dist_lt_of_sqrtSumSq_sub_le hδ (hsmall j w hw (z j) (hz j))
      have hball : Function.update z j w ∈ Metric.ball z δ := by
        rw [Metric.mem_ball, dist_pi_lt_iff hδ]
        intro l
        by_cases hl : l = j
        · subst hl
          simpa using hd
        · simpa [Function.update_of_ne hl] using hδ
      have := hx hball j (Set.mem_univ j)
      simpa using this
  obtain ⟨χ, hχc, -, hχd, hχf, hχs⟩ := hcut.1 k hk (δ / 8) (by positivity)
  have hstep : ∀ S : Finset (Fin n), ∀ (g : Fin n → (Fin k → ℝ) → ℂ)
      (hg : g ∈ disjointSupportTuples k n), (∀ j, tsupport (g j) ⊆ tsupport (f.1 j)) →
      (∀ j, j ∉ S → Small (g j)) → D ⟨g, hg⟩ = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro g hg hsub hsmall
      exact hbase g hg hsub fun j => hsmall j (Finset.notMem_empty j)
    | insert i S hi ih =>
      intro g hg hsub hsmall
      have hgc := hg.1 i
      let I : Finset (Fin k → ℤ) :=
        (hχf (tsupport (g i)) hgc.2.isCompact.isBounded).toFinset
      let u : (Fin k → ℤ) → (Fin k → ℝ) → ℂ := fun a z => (χ a z : ℂ) * g i z
      have hpiece := fun a => mul_factor_mem (hχc a) hgc
      have hsum : ∑ a ∈ I, u a = g i := by
        funext z
        rw [Finset.sum_apply]
        by_cases hz : g i z = 0
        · simp [u, hz]
        · have hzs : z ∈ tsupport (g i) := subset_tsupport _ hz
          have hzero : ∀ a, a ∉ I → χ a z = 0 := by
            intro a ha
            refine image_eq_zero_of_notMem_tsupport fun hza => ha ?_
            exact (Set.Finite.mem_toFinset _).2 ⟨z, hza, hzs⟩
          have e₁ : ∑ a ∈ I, χ a z = 1 :=
            (hasSum_sum_of_ne_finset_zero hzero).unique (hχs z)
          have e₂ : ∑ a ∈ I, (χ a z : ℂ) = 1 := by
            rw [← Complex.ofReal_sum, e₁, Complex.ofReal_one]
          simp only [u]
          rw [← Finset.sum_mul, e₂, one_mul]
      have hvanish : ∀ a ∈ I, ∀ hm : Function.update g i (u a) ∈ disjointSupportTuples k n,
          D ⟨Function.update g i (u a), hm⟩ = 0 := by
        intro a _ hm
        refine ih _ hm (fun j => ?_) (fun j hj => ?_)
        · by_cases hj : j = i
          · subst hj
            rw [Function.update_self]
            exact (hpiece a).2.1.trans (hsub j)
          · rw [Function.update_of_ne hj]
            exact hsub j
        · by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
            intro x hx y hy
            have := hχd a x ((hpiece a).2.2 hx) y ((hpiece a).2.2 hy)
            linarith
          · rw [Function.update_of_ne hji]
            exact hsmall j (by simp [hji, hj])
      obtain ⟨hm, hz⟩ := exists_update_sum_eq_zero hD hg i I u (fun a _ => (hpiece a).1)
        (fun a _ => (hpiece a).2.1) hvanish
      have hself : Function.update g i (∑ a ∈ I, u a) = g := by
        rw [hsum, Function.update_eq_self]
      rw [← apply_congr_tuple D hm hg hself]
      exact hz
  exact hstep Finset.univ f.1 f.2 (fun _ => subset_rfl) (fun j hj => (hj (Finset.mem_univ j)).elim)
theorem vanishingFromLocalVanishing_of_c1Partition
    (hcut : PartitionOfUnity.C1PartitionAndCutoffExist) : VanishingFromLocalVanishing := by
  intro k hk n _ D hD
  have hcompact : ∀ f : disjointSupportTuples k n, IsCompact (supportProduct f) := fun f =>
    isCompact_univ_pi fun i => (f.2.1 i).2.isCompact
  have hdistinct : ∀ f : disjointSupportTuples k n,
      supportProduct f ⊆ injectiveTuples (Fin k → ℝ) n := by
    intro f z hz i j hij
    by_contra hne
    exact Set.disjoint_left.1 (f.2.2 hne) (hz i (Set.mem_univ i))
      (by rw [hij]; exact hz j (Set.mem_univ j))
  refine ⟨fun f => ⟨hcompact f, hdistinct f,
    eq_zero_of_vanishesNear_supportProduct hcut hk hD f (hcompact f)⟩, ?_⟩
  intro hall f
  exact eq_zero_of_vanishesNear_supportProduct hcut hk hD f (hcompact f) fun x _ => hall x
end YangMills.Construction.LocalVanishing
