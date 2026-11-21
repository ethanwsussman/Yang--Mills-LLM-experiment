import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.PartitionsOfUnityOnCompactSubsetsOfPowers
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace PartitionsOfUnity
open TupleFacts (eucNorm)
section MetricFacts
variable {X : Type*} {d : X → X → ℝ}
abbrev metricSpaceOfDist (h0 : ∀ a b, d a b = 0 ↔ a = b) (hsymm : ∀ a b, d a b = d b a)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) : MetricSpace X where
  dist := d
  dist_self a := (h0 a a).2 rfl
  dist_comm := hsymm
  dist_triangle := htri
  eq_of_dist_eq_zero h := (h0 _ _).1 h
theorem closureWrt_compact_of_subset_union (h0 : ∀ a b, d a b = 0 ↔ a = b)
    (hsymm : ∀ a b, d a b = d b a) (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (T : Finset X) (C : X → Set X) (hC : ∀ j ∈ T, MetricNotions.IsCompactWrt d (C j))
    (Z : Set X) (hZ : Z ⊆ ⋃ j ∈ T, C j) :
    MetricNotions.IsCompactWrt d (MetricNotions.closureWrt d Z) ∧
      MetricNotions.closureWrt d Z ⊆ ⋃ j ∈ T, C j := by
  classical
  let _ : MetricSpace X := metricSpaceOfDist h0 hsymm htri
  have hopen : ∀ U : Set X, IsOpen U ↔ MetricNotions.IsOpenWrt d U := by
    intro U
    rw [Metric.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hb⟩ := h x hx
      refine ⟨ε, hε, fun y hy => hb ?_⟩
      show d y x < ε
      rw [hsymm]
      exact hy
    · intro h x hx
      obtain ⟨ε, hε, hb⟩ := h x hx
      refine ⟨ε, hε, fun y hy => hb y ?_⟩
      have hy' : d y x < ε := hy
      rw [hsymm]
      exact hy'
  have hcompact (S : Set X) (hS : MetricNotions.IsCompactWrt d S) : IsCompact S :=
    isCompact_generateFrom (TopologicalSpace.generateFrom_setOfPred_isOpen _).symm
      fun 𝒰 h𝒰 => hS 𝒰 fun U hU => (hopen U).1 (h𝒰 hU)
  have hcompact' : ∀ S : Set X, IsCompact S → MetricNotions.IsCompactWrt d S := by
    intro S hS 𝒰 h𝒰 hc
    obtain ⟨b, hb, hfin, hcov⟩ := hS.elim_finite_subcover_image (b := 𝒰) (c := id)
      (fun U hU => (hopen U).2 (h𝒰 U hU)) (by simpa [Set.sUnion_eq_biUnion] using hc)
    exact ⟨b, hb, hfin, by simpa [Set.sUnion_eq_biUnion] using hcov⟩
  have hcl : MetricNotions.closureWrt d Z = closure Z := by
    ext x
    rw [Metric.mem_closure_iff]
    rfl
  have hU : IsCompact (⋃ j ∈ T, C j) := T.isCompact_biUnion fun j hj => hcompact _ (hC j hj)
  have hsub : closure Z ⊆ ⋃ j ∈ T, C j := closure_minimal hZ hU.isClosed
  rw [hcl]
  exact ⟨hcompact' _ (hU.of_isClosed_subset isClosed_closure hsub), hsub⟩
end MetricFacts
section SmoothBumps
variable {p : ℕ+}
theorem contPartialsUpTo_of_contDiff (ν : ℕ) :
    ∀ G : Coords p → ℂ, ContDiff ℝ ∞ G → Coords.ContPartialsUpTo ν G := by
  induction ν with
  | zero =>
    intro G hG
    exact hG.continuous
  | succ ν ih =>
    intro G hG
    have hd : Differentiable ℝ G := hG.differentiable (by simp)
    refine ⟨hG.continuous, fun j => ⟨fun x => (hd x).lineDifferentiableAt, ih _ ?_⟩⟩
    have heq : Coords.partialAlong j G = fun x => fderiv ℝ G x (Pi.single j 1) := by
      funext x
      exact (hd x).lineDeriv_eq_fderiv
    rw [heq]
    exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
def periodTerm (ρ : ℝ) (x₀ k x : Coords p) : ℝ :=
  expNegInvGlue (ρ ^ 2 - ∑ j, (x j - x₀ j - k j) ^ 2)
theorem periodTerm_contDiff (ρ : ℝ) (x₀ k : Coords p) : ContDiff ℝ ∞ (periodTerm ρ x₀ k) := by
  have h : ContDiff ℝ ∞ fun x : Coords p => ρ ^ 2 - ∑ j, (x j - x₀ j - k j) ^ 2 := by
    refine contDiff_const.sub (ContDiff.sum fun j _ => ?_)
    exact (((contDiff_apply ℝ ℝ j).sub contDiff_const).sub contDiff_const).pow 2
  exact (expNegInvGlue.contDiff (n := ⊤)).comp h
theorem periodTerm_nonneg (ρ : ℝ) (x₀ k x : Coords p) : 0 ≤ periodTerm ρ x₀ k x :=
  expNegInvGlue.nonneg _
theorem periodTerm_pos_iff {ρ : ℝ} (hρ : 0 < ρ) (x₀ k x : Coords p) :
    0 < periodTerm ρ x₀ k x ↔ eucNorm (x - x₀ - k) < ρ := by
  have hn : eucNorm (x - x₀ - k) < ρ ↔ ∑ j, (x j - x₀ j - k j) ^ 2 < ρ ^ 2 := by
    unfold eucNorm
    exact Real.sqrt_lt' hρ
  rw [hn]
  constructor
  · intro h
    by_contra hc
    have : periodTerm ρ x₀ k x = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
    linarith
  · intro h
    exact expNegInvGlue.pos_of_pos (by linarith)
end SmoothBumps
section Lattice
variable (D : Params) (E : Kind) (p : ℕ+)
theorem periodSet_sub {a b : Coords p} (ha : a ∈ Kind.Tuple.periodSet D E p)
    (hb : b ∈ Kind.Tuple.periodSet D E p) : a - b ∈ Kind.Tuple.periodSet D E p :=
  fun i => (E.periodGroup D).sub_mem (ha i) (hb i)
theorem periodSet_add {a b : Coords p} (ha : a ∈ Kind.Tuple.periodSet D E p)
    (hb : b ∈ Kind.Tuple.periodSet D E p) : a + b ∈ Kind.Tuple.periodSet D E p :=
  fun i => (E.periodGroup D).add_mem (ha i) (hb i)
theorem periodGroup_coords_int_mul :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ k ∈ E.periodGroup D, ∀ μ, ∃ n : ℤ, k μ = (n : ℝ) * ℓ := by
  cases E with
  | euclidean =>
    refine ⟨1, one_pos, fun k hk μ => ⟨0, ?_⟩⟩
    have hk0 : k = 0 := AddSubgroup.mem_bot.mp hk
    simp [hk0]
  | torus =>
    have hL : (0 : ℝ) < (D.L : ℝ) := by
      have := D.isAdmissible.2
      exact_mod_cast (by omega : 0 < D.L)
    refine ⟨D.side, ?_, ?_⟩
    · show 0 < 2 * (D.L : ℝ) ^ (D.m : ℕ)
      positivity
    · rintro k ⟨n, hn⟩ μ
      exact ⟨n μ, hn μ⟩
theorem periodSet_finite_in_box (R : ℝ) :
    {k : Coords p | k ∈ Kind.Tuple.periodSet D E p ∧ ∀ j, |k j| ≤ R}.Finite := by
  obtain ⟨ℓ, hℓ, hco⟩ := periodGroup_coords_int_mul D E
  have hcoord : ∀ k ∈ Kind.Tuple.periodSet D E p, ∀ j, ∃ n : ℤ, k j = (n : ℝ) * ℓ := by
    intro k hk j
    have hj := j.2
    have hi : (j : ℕ) / 4 < (p : ℕ) := by omega
    have hμ : (j : ℕ) % 4 < 4 := by omega
    obtain ⟨n, hn⟩ := hco _ (hk ⟨(j : ℕ) / 4, hi⟩) ⟨(j : ℕ) % 4, hμ⟩
    refine ⟨n, ?_⟩
    rw [← hn]
    show k j = k _
    congr 1
    apply Fin.ext
    show (j : ℕ) = 4 * ((j : ℕ) / 4) + (j : ℕ) % 4
    omega
  set c : ℤ := ⌈R / ℓ⌉
  have hS : ((fun n : ℤ => (n : ℝ) * ℓ) '' Set.Icc (-c) c).Finite :=
    (Set.finite_Icc _ _).image _
  refine (Set.Finite.pi' fun _ : Fin (4 * (p : ℕ)) => hS).subset ?_
  rintro k ⟨hk, hR⟩ j
  obtain ⟨n, hn⟩ := hcoord k hk j
  refine ⟨n, ?_, hn.symm⟩
  have hb : |(n : ℝ)| ≤ c := by
    have h1 : |(n : ℝ)| * ℓ ≤ R := by
      have := hR j
      rwa [hn, abs_mul, abs_of_pos hℓ] at this
    have h2 : |(n : ℝ)| ≤ R / ℓ := by rwa [le_div_iff₀ hℓ]
    exact h2.trans (Int.le_ceil _)
  have hb' := abs_le.mp hb
  constructor
  · have : ((-c : ℤ) : ℝ) ≤ n := by push_cast; exact hb'.1
    exact_mod_cast this
  · exact_mod_cast hb'.2
variable {D E p}
theorem locallyFinite_periodTerm (ρ : ℝ) (x₀ : Coords p) :
    LocallyFinite fun k : Kind.Tuple.periodSet D E p =>
      Function.support (periodTerm ρ x₀ (k : Coords p)) := by
  intro x₁
  refine ⟨Metric.ball x₁ 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  have hfin := periodSet_finite_in_box D E p (|ρ| + 1 + ‖x₁ - x₀‖)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨k, hk⟩ ⟨x, hx, hball⟩
  refine ⟨hk, fun j => ?_⟩
  have hsum : ∑ i, (x i - x₀ i - k i) ^ 2 < ρ ^ 2 := by
    by_contra hc
    exact hx (expNegInvGlue.zero_of_nonpos (by linarith))
  have hj : (x j - x₀ j - k j) ^ 2 < ρ ^ 2 :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (x i - x₀ i - k i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)) hsum
  have h1 : |x j - x₀ j - k j| < |ρ| := sq_lt_sq.mp hj
  have h2 : |x j - x₁ j| < 1 :=
    lt_of_le_of_lt (dist_le_pi_dist x x₁ j) (Metric.mem_ball.mp hball)
  have h3 : |x₁ j - x₀ j| ≤ ‖x₁ - x₀‖ := norm_le_pi_norm (x₁ - x₀) j
  rw [abs_lt] at h1 h2
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
theorem exists_periodic_bump {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Coords p) :
    ∃ B : Coords p → ℝ, ContDiff ℝ ∞ B ∧ (∀ x, 0 ≤ B x) ∧
      (∀ x, 0 < B x ↔ ∃ k ∈ Kind.Tuple.periodSet D E p, eucNorm (x - x₀ - k) < ρ) ∧
      ∀ x, ∀ k ∈ Kind.Tuple.periodSet D E p, B (x + k) = B x := by
  classical
  have lf := locallyFinite_periodTerm (D := D) (E := E) (p := p) ρ x₀
  refine ⟨fun x => ∑ᶠ k : Kind.Tuple.periodSet D E p, periodTerm ρ x₀ (k : Coords p) x,
    ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨s, hs⟩ := finsum_eventually_eq_sum lf x
    have hsm : ContDiff ℝ ∞ fun y => ∑ k ∈ s, periodTerm ρ x₀ (k : Coords p) y :=
      ContDiff.sum fun k _ => periodTerm_contDiff ρ x₀ _
    exact hsm.contDiffAt.congr_of_eventuallyEq hs
  · intro x
    exact finsum_nonneg fun k => periodTerm_nonneg ρ x₀ _ x
  · intro x
    constructor
    · intro hpos
      by_contra hc
      have hz : ∀ k : Kind.Tuple.periodSet D E p, periodTerm ρ x₀ (k : Coords p) x = 0 := by
        intro k
        refine le_antisymm (not_lt.mp fun h => hc ?_) (periodTerm_nonneg ρ x₀ _ x)
        exact ⟨k, k.2, (periodTerm_pos_iff hρ x₀ _ x).1 h⟩
      have : (∑ᶠ k : Kind.Tuple.periodSet D E p, periodTerm ρ x₀ (k : Coords p) x) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hz
      simp only [this, lt_self_iff_false] at hpos
    · rintro ⟨k, hk, hlt⟩
      have h1 := (periodTerm_pos_iff hρ x₀ k x).2 hlt
      exact lt_of_lt_of_le h1 (single_le_finsum (⟨k, hk⟩ : Kind.Tuple.periodSet D E p)
        (f := fun k : Kind.Tuple.periodSet D E p => periodTerm ρ x₀ (k : Coords p) x)
        (lf.point_finite x) fun j => periodTerm_nonneg ρ x₀ _ x)
  · intro x k₀ hk₀
    let e : Kind.Tuple.periodSet D E p ≃ Kind.Tuple.periodSet D E p :=
      { toFun := fun k => ⟨k.1 - k₀, periodSet_sub D E p k.2 hk₀⟩
        invFun := fun k => ⟨k.1 + k₀, periodSet_add D E p k.2 hk₀⟩
        left_inv := fun k => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
    have hterm : ∀ k : Kind.Tuple.periodSet D E p,
        periodTerm ρ x₀ (k : Coords p) (x + k₀) = periodTerm ρ x₀ (e k : Coords p) x := by
      intro k
      unfold periodTerm
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      show (x j + k₀ j - x₀ j - k.1 j) ^ 2 = (x j - x₀ j - (k.1 j - k₀ j)) ^ 2
      ring
    show (∑ᶠ k : Kind.Tuple.periodSet D E p, periodTerm ρ x₀ (k : Coords p) (x + k₀)) = _
    rw [finsum_congr hterm]
    exact finsum_comp_equiv e (f := fun k : Kind.Tuple.periodSet D E p =>
      periodTerm ρ x₀ (k : Coords p) x)
end Lattice
theorem exists_smooth_bump (D : Params) (E : Kind) (p : ℕ+)
    (hQ : TupleFacts.ProjSurjectiveFibres D E p)
    (hL : TupleFacts.DistEqMinTranslateNorm D E p)
    (y₀ : E.Tuple D p) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ b : E.Tuple D p → ℝ, ContDiff ℝ ∞ (b ∘ Kind.Tuple.proj D E) ∧
      (∀ y, 0 ≤ b y) ∧ ∀ y, 0 < b y ↔ Kind.Tuple.tupleDist D E y y₀ < ρ := by
  obtain ⟨hsurj, hfib⟩ := hQ
  obtain ⟨x₀, rfl⟩ := hsurj y₀
  obtain ⟨B, hsm, hnn, hpos, hper⟩ := exists_periodic_bump (D := D) (E := E) hρ x₀
  have hlift : ∀ x, B (Function.surjInv hsurj (Kind.Tuple.proj D E x)) = B x := by
    intro x
    have h1 : Kind.Tuple.proj D E (Function.surjInv hsurj
        (Kind.Tuple.proj D E x)) = Kind.Tuple.proj D E x :=
      Function.surjInv_eq hsurj _
    have h2 := hper x _ ((hfib _ x).1 h1)
    rwa [add_sub_cancel] at h2
  refine ⟨fun y => B (Function.surjInv hsurj y), ?_, fun y => hnn _, ?_⟩
  · have : (fun y => B (Function.surjInv hsurj y)) ∘ Kind.Tuple.proj D E = B :=
      funext hlift
    rw [this]
    exact hsm
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    show 0 < B (Function.surjInv hsurj (Kind.Tuple.proj D E x)) ↔ _
    rw [hlift, hpos]
    obtain ⟨hleast, -⟩ := hL x x₀
    constructor
    · rintro ⟨k, hk, hlt⟩
      exact lt_of_le_of_lt (hleast.2 ⟨k, hk, rfl⟩) hlt
    · intro hlt
      obtain ⟨k, hk, hr⟩ := hleast.1
      exact ⟨k, hk, hr ▸ hlt⟩
theorem exists_partition (h : TupleFacts.AllFacts)
    (D : Params) (E : Kind) (p : ℕ+) : Kind.Tuple.PartitionOfUnityExists D E p := by
  classical
  obtain ⟨hQ, hL, hM, -, -, -, -, -, hOpen, -, hBalls, -⟩ := h D E p
  obtain ⟨-, heq, hsymm, htri⟩ := hM
  intro r K W hK hW hcov
  -- A set of tuples is open exactly when its preimage under the coordinate projection is open.
  let _ : TopologicalSpace (E.Tuple D p) := .coinduced (Kind.Tuple.proj D E) inferInstance
  have hKc : IsCompact K :=
    isCompact_generateFrom (TopologicalSpace.generateFrom_setOfPred_isOpen _).symm
      fun 𝒰 h𝒰 => hK 𝒰 fun U hU => (hOpen U).2 (h𝒰 hU)
  have : Nonempty (Fin (r : ℕ)) := ⟨⟨0, r.pos⟩⟩
  have hlocal : ∀ y ∈ K, ∃ (a : Fin (r : ℕ)) (ρ : ℝ) (b : E.Tuple D p → ℝ), 0 < ρ ∧
      (∀ y', Kind.Tuple.tupleDist D E y' y ≤ ρ → y' ∈ W a) ∧
      ContDiff ℝ ∞ (b ∘ Kind.Tuple.proj D E) ∧ (∀ y', 0 ≤ b y') ∧
      ∀ y', 0 < b y' ↔ Kind.Tuple.tupleDist D E y' y < ρ := by
    intro y hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨r₀, hr₀, hin⟩ := hW a y ha
    obtain ⟨b, hb1, hb2, hb3⟩ := exists_smooth_bump D E p hQ hL y (half_pos hr₀)
    refine ⟨a, r₀ / 2, b, half_pos hr₀, fun y' hy' => hin y' ?_, hb1, hb2, hb3⟩
    rw [hsymm]
    linarith
  choose! a ρ b hρ hsub hsm hnn hpos using hlocal
  -- Each bump is positive on an open ball about its center, so finitely many cover K.
  obtain ⟨T, hTK, hTcov⟩ := hKc.elim_nhds_subcover
    (fun y => {y' | Kind.Tuple.tupleDist D E y' y < ρ y}) fun y hy => by
      refine IsOpen.mem_nhds ?_ ?_
      · exact (hOpen _).1 (hBalls y (ρ y) (hρ y hy)).1
      · simpa only [Set.mem_ofPred_eq, (heq y y).2 rfl] using hρ y hy
  let s : E.Tuple D p → ℝ := fun y => ∑ j ∈ T, b j y
  have hbnn : ∀ j ∈ T, ∀ y, 0 ≤ b j y := fun j hj => hnn j (hTK j hj)
  have hs_nn : ∀ y, 0 ≤ s y := fun y => Finset.sum_nonneg fun j hj => hbnn j hj y
  have hsum_sm : ∀ T' : Finset (E.Tuple D p), T' ⊆ T →
      ContDiff ℝ ∞ fun x => ∑ j ∈ T', b j (Kind.Tuple.proj D E x) :=
    fun T' hT' => ContDiff.sum fun j hj => hsm j (hTK j (hT' hj))
  have hs_sm : ContDiff ℝ ∞ (s ∘ Kind.Tuple.proj D E) := hsum_sm T subset_rfl
  have hs_pos : ∀ y ∈ K, 0 < s y := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 (hTcov hy)
    exact Finset.sum_pos' (fun i hi => hbnn i hi y) ⟨j, hj, (hpos j (hTK j hj) y).2 hyj⟩
  have hlevel : ∀ t : ℝ, Kind.Tuple.IsOpenT D E {y | t < s y} := fun t =>
    (hOpen _).2 (isOpen_lt continuous_const hs_sm.continuous)
  -- The continuous sum of bumps is positive on K, so compactness gives a uniform lower bound.
  have hs_cont : Continuous s := continuous_coinduced_dom.2 hs_sm.continuous
  obtain ⟨δ, hδ, hδs⟩ := hKc.exists_forall_le' hs_cont.continuousOn hs_pos
  obtain ⟨ε, hε, hεδ⟩ := exists_between hδ
  have hKN : ∀ y ∈ K, ε < s y := fun y hy => hεδ.trans_le (hδs y hy)
  let den : E.Tuple D p → ℝ := fun y => s y + expNegInvGlue (ε - s y)
  have hden_pos : ∀ y, 0 < den y := by
    intro y
    rcases (hs_nn y).eq_or_lt with h0 | h0
    · have : 0 < expNegInvGlue (ε - s y) := expNegInvGlue.pos_of_pos (by rw [← h0]; simpa using hε)
      show 0 < s y + _
      linarith
    · have := expNegInvGlue.nonneg (ε - s y)
      show 0 < s y + _
      linarith
  have hden_sm : ContDiff ℝ ∞ (den ∘ Kind.Tuple.proj D E) :=
    hs_sm.add ((expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub hs_sm))
  let S : Fin (r : ℕ) → E.Tuple D p → ℝ :=
    fun c y => ∑ j ∈ T.filter (fun j => a j = c), b j y
  have hS_nn : ∀ c y, 0 ≤ S c y := fun c y =>
    Finset.sum_nonneg fun j hj => hbnn j (Finset.mem_of_mem_filter j hj) y
  have hS_le : ∀ c y, S c y ≤ s y := fun c y =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j hj _ => hbnn j hj y
  refine ⟨fun c y => ((S c y / den y : ℝ) : ℂ), ?_, ?_, {y | ε < s y}, hlevel ε, hKN, ?_⟩
  · intro c
    refine ⟨fun ν => contPartialsUpTo_of_contDiff ν _ ?_, ?_⟩
    · have hq : ContDiff ℝ ∞ fun x => S c (Kind.Tuple.proj D E x) /
          den (Kind.Tuple.proj D E x) :=
        (hsum_sm _ (Finset.filter_subset _ _)).div hden_sm fun x => (hden_pos _).ne'
      exact Complex.ofRealCLM.contDiff.comp hq
    · have hZ : {y | ((S c y / den y : ℝ) : ℂ) ≠ 0} ⊆
          ⋃ j ∈ T.filter (fun j => a j = c), {y' | Kind.Tuple.tupleDist D E y' j ≤ ρ j} := by
        intro y hy
        have hS : S c y ≠ 0 := by
          intro h0
          exact hy (by simp [h0])
        obtain ⟨j, hj, hbj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
        have hjT := Finset.mem_of_mem_filter j hj
        have hbpos : 0 < b j y := lt_of_le_of_ne (hbnn j hjT y) (Ne.symm hbj)
        simp only [Set.mem_iUnion]
        exact ⟨j, hj, ((hpos j (hTK j hjT) y).1 hbpos).le⟩
      obtain ⟨hc1, hc2⟩ := closureWrt_compact_of_subset_union heq hsymm htri
        (T.filter (fun j => a j = c)) (fun j => {y' | Kind.Tuple.tupleDist D E y' j ≤ ρ j})
        (fun j hj => (hBalls j (ρ j) (hρ j (hTK j (Finset.mem_of_mem_filter j hj)))).2.2) _ hZ
      refine ⟨hc1, hc2.trans ?_⟩
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, hj, hyj⟩ := hy
      have hjc : a j = c := (Finset.mem_filter.mp hj).2
      rw [← hjc]
      exact hsub j (hTK j (Finset.mem_of_mem_filter j hj)) y hyj
  · intro c y
    refine ⟨S c y / den y, ⟨div_nonneg (hS_nn c y) (hden_pos y).le, ?_⟩, rfl⟩
    rw [div_le_one (hden_pos y)]
    have := hS_le c y
    have := expNegInvGlue.nonneg (ε - s y)
    show S c y ≤ s y + _
    linarith
  · intro y hy
    have hy' : ε < s y := hy
    have hc : expNegInvGlue (ε - s y) = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
    have hden : den y = s y := by
      show s y + _ = s y
      rw [hc, add_zero]
    have hsum : ∑ c, S c y = s y := Finset.sum_fiberwise T a fun j => b j y
    rw [← Complex.ofReal_sum, ← Finset.sum_div, hsum, hden, div_self (by linarith)]
    simp
end PartitionsOfUnity
theorem PartitionsOfUnity.holds (h : TupleFacts.AllFacts) :
    PartitionsOfUnity.Statement := by
  intro D E p
  refine ⟨PartitionsOfUnity.exists_partition h D E p, ?_⟩
  intro K W hK hW hKW
  obtain ⟨φ, h1, h2, N, hN, hKN, hsum⟩ :=
    PartitionsOfUnity.exists_partition h D E p 1 K (fun _ => W) hK
      (fun _ => hW) (fun y hy => Set.mem_iUnion.mpr ⟨⟨0, (1 : ℕ+).pos⟩, hKW hy⟩)
  refine ⟨φ ⟨0, (1 : ℕ+).pos⟩, h1 _, h2 _, N, ⟨N, hN, hKN, subset_rfl⟩, fun y hy => ?_⟩
  have := hsum y hy
  rwa [show (∑ a : Fin ((1 : ℕ+) : ℕ), φ a y) = φ ⟨0, (1 : ℕ+).pos⟩ y from
    Fin.sum_univ_one (fun a => φ a y)] at this
end YangMills.Construction.PeriodicSpace
