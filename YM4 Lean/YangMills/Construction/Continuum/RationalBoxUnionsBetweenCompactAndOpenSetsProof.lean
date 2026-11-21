import YangMills.Construction.Continuum.ExistenceOfAStableChoiceProof
import YangMills.Construction.Continuum.RationalBoxUnionsBetweenCompactAndOpenSets
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology Metric
namespace YangMills.Construction.RatBoxSeparation
open YangMills.Construction.TestFunctions
theorem countable_ratBoxUnions : ratBoxUnions.Countable := by apply _root_.YangMills.Construction.DisjointTuples.StableChoice.countable_ratBoxUnions <;> assumption
theorem sUnion_mem_ratBoxUnions {𝓢 : Set (Set (Fin 4 → ℝ))} (hfin : 𝓢.Finite)
    (hsub : 𝓢 ⊆ ratBoxUnions) : ⋃₀ 𝓢 ∈ ratBoxUnions := by
  have hsub' : ∀ Q ∈ 𝓢, ∃ 𝓑 : Set (Set (Fin 4 → ℝ)), 𝓑.Finite ∧ (∀ B ∈ 𝓑, IsRatBox B) ∧
      Q = ⋃₀ 𝓑 := fun Q hQ => hsub hQ
  choose! F hFf hFB hFeq using hsub'
  refine ⟨⋃ Q ∈ 𝓢, F Q, hfin.biUnion hFf, ?_, ?_⟩
  · intro B hB
    obtain ⟨Q, hQ, hBQ⟩ := mem_iUnion₂.1 hB
    exact hFB Q hQ B hBQ
  · apply Subset.antisymm
    · rintro x ⟨Q, hQ, hx⟩
      rw [hFeq Q hQ] at hx
      obtain ⟨B, hB, hxB⟩ := hx
      exact ⟨B, mem_iUnion₂.2 ⟨Q, hQ, hB⟩, hxB⟩
    · rintro x ⟨B, hB, hxB⟩
      obtain ⟨Q, hQ, hBQ⟩ := mem_iUnion₂.1 hB
      refine ⟨Q, hQ, ?_⟩
      rw [hFeq Q hQ]
      exact ⟨B, hBQ, hxB⟩
def latticeCube (N : ℕ) (j : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  univ.pi fun κ => Icc ((j κ : ℝ) / N) (((j κ : ℝ) + 1) / N)
theorem isRatBox_latticeCube {N : ℕ} (hN : 0 < N) (j : Fin 4 → ℤ) :
    IsRatBox (latticeCube N j) := by
  refine ⟨fun κ => (j κ : ℚ) / N, fun κ => ((j κ : ℚ) + 1) / N, fun κ => ?_, ?_⟩
  · have h : (0 : ℚ) < N := by exact_mod_cast hN
    exact div_lt_div_of_pos_right (by linarith) h
  · simp only [latticeCube]
    push_cast
    rfl
theorem mem_latticeCube_floor {N : ℕ} (hN : 0 < N) (x : Fin 4 → ℝ) :
    x ∈ latticeCube N fun κ => ⌊(N : ℝ) * x κ⌋ := by
  intro κ _
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · rw [div_le_iff₀ hN', mul_comm]
    exact Int.floor_le _
  · rw [le_div_iff₀ hN', mul_comm]
    exact (Int.lt_floor_add_one _).le
theorem dist_le_of_mem_latticeCube {N : ℕ} (hN : 0 < N) {j : Fin 4 → ℤ} {x y : Fin 4 → ℝ}
    (hx : x ∈ latticeCube N j) (hy : y ∈ latticeCube N j) : dist x y ≤ 1 / N := by
  refine (dist_pi_le_iff (by positivity)).2 fun κ => ?_
  have h1 : x κ ∈ Icc ((j κ : ℝ) / N) (((j κ : ℝ) + 1) / N) := hx κ (mem_univ κ)
  have h2 : y κ ∈ Icc ((j κ : ℝ) / N) (((j κ : ℝ) + 1) / N) := hy κ (mem_univ κ)
  have e : ((j κ : ℝ) + 1) / N = (j κ : ℝ) / N + 1 / N := by ring
  rw [e] at h1 h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem finite_setOf_latticeCube_inter_nonempty {N : ℕ} (hN : 0 < N) {C : Set (Fin 4 → ℝ)}
    (hC : IsCompact C) :
    {j : Fin 4 → ℤ | (latticeCube N j ∩ C).Nonempty}.Finite := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  refine (Set.finite_Icc (fun _ : Fin 4 => -⌈(N : ℝ) * R⌉ - 1)
    (fun _ : Fin 4 => ⌈(N : ℝ) * R⌉)).subset ?_
  rintro j ⟨y, hy, hyC⟩
  have hyR : ∀ κ, |y κ| ≤ R := fun κ => by
    have h := (dist_le_pi_dist y 0 κ).trans (mem_closedBall.1 (hR hyC))
    simpa [Real.dist_eq] using h
  have hceil : (N : ℝ) * R ≤ (⌈(N : ℝ) * R⌉ : ℝ) := Int.le_ceil _
  constructor
  · intro κ
    have h1 : y κ ≤ ((j κ : ℝ) + 1) / N := (hy κ (mem_univ κ)).2
    rw [le_div_iff₀ hN'] at h1
    have h2 := (abs_le.1 (hyR κ)).1
    have h3 : (N : ℝ) * (-R) ≤ (N : ℝ) * y κ := mul_le_mul_of_nonneg_left h2 hN'.le
    have h4 : -(⌈(N : ℝ) * R⌉ : ℝ) - 1 ≤ (j κ : ℝ) := by nlinarith
    exact_mod_cast h4
  · intro κ
    have h1 : (j κ : ℝ) / N ≤ y κ := (hy κ (mem_univ κ)).1
    rw [div_le_iff₀ hN'] at h1
    have h2 := (abs_le.1 (hyR κ)).2
    have h3 : (N : ℝ) * y κ ≤ (N : ℝ) * R := mul_le_mul_of_nonneg_left h2 hN'.le
    have h4 : (j κ : ℝ) ≤ (⌈(N : ℝ) * R⌉ : ℝ) := by nlinarith
    exact_mod_cast h4
theorem exists_uniform_thickening {n : ℕ} {C U : Fin n → Set (Fin 4 → ℝ)}
    (hC : ∀ i, IsCompact (C i)) (hdisj : Pairwise fun i k => Disjoint (C i) (C k))
    (hU : ∀ i, IsOpen (U i)) (hCU : ∀ i, C i ⊆ U i) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, thickening δ (C i) ⊆ U i) ∧
      ∀ i k, i ≠ k → Disjoint (thickening δ (C i)) (thickening δ (C k)) := by
  have h1 : ∀ i, ∀ᶠ δ in 𝓝[>] (0 : ℝ), thickening δ (C i) ⊆ U i := by
    intro i
    obtain ⟨δ, hδ, hs⟩ := (hC i).exists_thickening_subset_open (hU i) (hCU i)
    filter_upwards [Ioo_mem_nhdsGT hδ] with e he
    exact (thickening_mono he.2.le _).trans hs
  have h2 : ∀ i k, ∀ᶠ δ in 𝓝[>] (0 : ℝ), i ≠ k →
      Disjoint (thickening δ (C i)) (thickening δ (C k)) := by
    intro i k
    by_cases hik : i = k
    · exact Eventually.of_forall fun _ h => absurd hik h
    obtain ⟨δ, hδ, hs⟩ := (hdisj hik).exists_thickenings (hC i) (hC k).isClosed
    filter_upwards [Ioo_mem_nhdsGT hδ] with e he _
    exact hs.mono (thickening_mono he.2.le _) (thickening_mono he.2.le _)
  have h3 := ((eventually_all.2 h1).and (eventually_all.2 fun i => eventually_all.2 (h2 i))).and
    self_mem_nhdsWithin
  obtain ⟨δ, ⟨hd1, hd2⟩, hδ⟩ := h3.exists
  exact ⟨δ, hδ, hd1, hd2⟩
theorem exists_ratBoxUnions_between {n : ℕ} {C U : Fin n → Set (Fin 4 → ℝ)}
    (hC : ∀ i, IsCompact (C i)) (hdisj : Pairwise fun i k => Disjoint (C i) (C k))
    (hU : ∀ i, IsOpen (U i)) (hCU : ∀ i, C i ⊆ U i) :
    ∃ Q : Fin n → Set (Fin 4 → ℝ), (∀ i, Q i ∈ ratBoxUnions) ∧
      (Pairwise fun i k => Disjoint (Q i) (Q k)) ∧ ∀ i, C i ⊆ Q i ∧ Q i ⊆ U i := by
  obtain ⟨δ, hδ, hthU, hthd⟩ := exists_uniform_thickening hC hdisj hU hCU
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hN : 0 < m + 1 := Nat.succ_pos m
  have hm' : 1 / (((m + 1 : ℕ)) : ℝ) < δ := by
    push_cast
    exact hm
  have hth : ∀ i, (⋃₀ (latticeCube (m + 1) '' {j | (latticeCube (m + 1) j ∩ C i).Nonempty})) ⊆
      thickening δ (C i) := by
    rintro i x ⟨_, ⟨j, ⟨y, hy, hyC⟩, rfl⟩, hx⟩
    exact mem_thickening_iff.2 ⟨y, hyC, (dist_le_of_mem_latticeCube hN hx hy).trans_lt hm'⟩
  refine ⟨fun i => ⋃₀ (latticeCube (m + 1) '' {j | (latticeCube (m + 1) j ∩ C i).Nonempty}),
    fun i => ?_, fun i k hik => ?_, fun i => ⟨?_, (hth i).trans (hthU i)⟩⟩
  · refine ⟨_, (finite_setOf_latticeCube_inter_nonempty hN (hC i)).image _, ?_, rfl⟩
    rintro B ⟨j, -, rfl⟩
    exact isRatBox_latticeCube hN j
  · exact (hthd i k hik).mono (hth i) (hth k)
  · intro x hx
    exact ⟨_, ⟨_, ⟨x, mem_latticeCube_floor hN x, hx⟩, rfl⟩, mem_latticeCube_floor hN x⟩
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} (hf : Differentiable ℝ f) (μ : Fin 4)
    (x : Fin 4 → ℝ) : partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.partialDerivR4_eq_fderiv <;> assumption
theorem partialDerivR4_eq_zero_of_notMem {Q : Set (Fin 4 → ℝ)} (hQ : IsClosed Q)
    {f : (Fin 4 → ℝ) → ℝ} (hf : f ∈ c1ZeroOff Q) (hdiff : Differentiable ℝ f) (μ : Fin 4)
    {x : Fin 4 → ℝ} (hx : x ∉ Q) : partialDerivR4 μ f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hQ.isOpen_compl.mem_nhds hx] with y hy
    exact hf.2 y hy
  rw [partialDerivR4_eq_fderiv hdiff, h.fderiv_eq]
  simp
theorem c1NormR4_sub_le {Q : Set (Fin 4 → ℝ)} (hQ : IsClosed Q) {f g : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ c1ZeroOff Q) (hg : g ∈ c1ZeroOff Q) {d : ℝ} (hd : 0 ≤ d)
    (h0 : ∀ x ∈ Q, dist (g x) (f x) ≤ d)
    (h1 : ∀ μ, ∀ x ∈ Q, dist (partialDerivR4 μ g x) (partialDerivR4 μ f x) ≤ d) :
    c1NormR4 (g - f) ≤ d := by
  have hfd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.1.differentiable (by simp)
  unfold c1NormR4 uniformNorm
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun μ => ciSup_le fun x => ?_)
  · by_cases hx : x ∈ Q
    · have h := h0 x hx
      rwa [dist_eq_norm] at h
    · simpa [hf.2 x hx, hg.2 x hx] using hd
  · have e : partialDerivR4 μ (g - f) x = partialDerivR4 μ g x - partialDerivR4 μ f x := by
      rw [partialDerivR4_eq_fderiv (hgd.sub hfd), partialDerivR4_eq_fderiv hgd,
        partialDerivR4_eq_fderiv hfd, fderiv_sub (hgd x) (hfd x)]
      rfl
    rw [e]
    by_cases hx : x ∈ Q
    · have h := h1 μ x hx
      rwa [dist_eq_norm] at h
    · simpa [partialDerivR4_eq_zero_of_notMem hQ hf hfd μ hx,
        partialDerivR4_eq_zero_of_notMem hQ hg hgd μ hx] using hd
theorem continuous_firstJet {Q : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ c1ZeroOff Q) :
    Continuous fun x : Q => (f x, fun μ => partialDerivR4 μ f x) := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  refine ((hd.continuous.comp continuous_subtype_val).prodMk
    (continuous_pi fun μ => ?_))
  simp only [partialDerivR4_eq_fderiv hd]
  exact (hc.comp continuous_subtype_val).clm_apply continuous_const
theorem exists_countable_dense_c1ZeroOff {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ ratBoxUnions) :
    ∃ D : Set ((Fin 4 → ℝ) → ℝ),
      D ⊆ c1ZeroOff Q ∧ D.Countable ∧ IsDenseInC1ZeroOff Q D := by
  have hc := isCompact_of_mem_ratBoxUnions hQ
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hc
  let Φ : c1ZeroOff Q → C(Q, ℝ × (Fin 4 → ℝ)) := fun f => ⟨_, continuous_firstJet f.2⟩
  obtain ⟨t, ht, htc, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range Φ)).exists_countable_dense_subset
  choose G hG using fun y : t => ht y.2
  have := htc.to_subtype
  refine ⟨Set.range fun y : t => (G y).1, ?_, countable_range _, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (G y).2
  · intro f hf ε hε
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 (hdense ⟨⟨f, hf⟩, rfl⟩) ε hε
    refine ⟨(G ⟨y, hy⟩).1, ⟨_, rfl⟩, ?_⟩
    have hb : ∀ x : Q, dist (Φ (G ⟨y, hy⟩) x) (Φ ⟨f, hf⟩ x) ≤ dist y (Φ ⟨f, hf⟩) := fun x => by
      rw [hG ⟨y, hy⟩]
      exact ContinuousMap.dist_apply_le_dist x
    refine (c1NormR4_sub_le (d := dist y (Φ ⟨f, hf⟩)) hc.isClosed hf (G ⟨y, hy⟩).2 dist_nonneg
      (fun x hx => ?_) (fun μ x hx => ?_)).trans_lt (by rwa [dist_comm])
    · exact (le_max_left _ _).trans (hb ⟨x, hx⟩)
    · exact (dist_le_pi_dist (fun ν => partialDerivR4 ν (G ⟨y, hy⟩).1 x)
        (fun ν => partialDerivR4 ν f x) μ).trans ((le_max_right _ _).trans (hb ⟨x, hx⟩))
theorem separationClaim_holds : separationClaim :=
  ⟨⟨countable_ratBoxUnions, fun _ hf hs => sUnion_mem_ratBoxUnions hf hs⟩,
    fun _ _ _ _ hC hd hO hCO => exists_ratBoxUnions_between hC hd hO hCO,
    fun _ hQ => exists_countable_dense_c1ZeroOff hQ⟩
end YangMills.Construction.RatBoxSeparation
