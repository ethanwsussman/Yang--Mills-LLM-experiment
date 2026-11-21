import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPieces
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.LimitSpaces.FinePartitionOfUnity
def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t
theorem bump_contDiff : ContDiff ℝ 1 bump := by
  have hst : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hst.comp (contDiff_id.add contDiff_const)).sub hst
theorem bump_nonneg (t : ℝ) : 0 ≤ bump t :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))
theorem bump_le_one (t : ℝ) : bump t ≤ 1 := by
  have ha := Real.smoothTransition.le_one (t + 1)
  have hb := Real.smoothTransition.nonneg t
  unfold bump
  linarith
theorem bump_zero : bump 0 = 1 := by
  simp [bump, Real.smoothTransition.one, Real.smoothTransition.zero]
theorem bump_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : bump t = 0 := by
  unfold bump
  rcases le_abs.1 ht with hpos | hneg
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 1),
      Real.smoothTransition.one_of_one_le hpos, sub_self]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : t + 1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : t ≤ 0), sub_self]
theorem abs_lt_one_of_bump_ne_zero {t : ℝ} (ht : bump t ≠ 0) : |t| < 1 := by
  by_contra hcon
  exact ht (bump_eq_zero (not_lt.1 hcon))
theorem bump_translates_sum (t : ℝ) :
    {k : ℤ | bump (t - k) ≠ 0}.Finite ∧ ∑ᶠ k : ℤ, bump (t - k) = 1 := by
  classical
  set n : ℤ := ⌊t⌋ with hn
  have hlo : (n : ℝ) ≤ t := Int.floor_le t
  have hhi : t < n + 1 := Int.lt_floor_add_one t
  have hz : ∀ k : ℤ, k ≠ n → k ≠ n + 1 → bump (t - k) = 0 := by
    intro k hk hk'
    apply bump_eq_zero
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      exact le_abs.2 (Or.inl (by linarith))
    · have hk2 : n + 1 < k := lt_of_le_of_ne hgt (Ne.symm hk')
      have : (n : ℝ) + 2 ≤ k := by exact_mod_cast (by omega : n + 2 ≤ k)
      exact le_abs.2 (Or.inr (by linarith))
  have hsub : {k : ℤ | bump (t - k) ≠ 0} ⊆ (({n, n + 1} : Finset ℤ) : Set ℤ) := by
    intro k hk
    by_contra hcon
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hcon
    exact hk (hz k hcon.1 hcon.2)
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := {n, n + 1}) hsub,
    Finset.sum_pair (by omega : n ≠ n + 1)]
  unfold bump
  push_cast
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t - n + 1),
    Real.smoothTransition.zero_of_nonpos (by linarith : t - (n + 1) ≤ 0)]
  have : t - ((n : ℝ) + 1) + 1 = t - n := by ring
  rw [this]
  ring
structure IsPeriodicBumpFamily (h : ℝ) (Γ : Set ℝ) {J : Type} (B : J → ℝ → ℝ) (c : J → ℝ) : Prop where
  contDiff : ∀ j, ContDiff ℝ 1 (B j)
  nonneg : ∀ j t, 0 ≤ B j t
  le_one : ∀ j t, B j t ≤ 1
  periodic : ∀ j t γ, γ ∈ Γ → B j (t + γ) = B j t
  center : ∀ j, B j (c j) ≠ 0
  near : ∀ j t, B j t ≠ 0 → ∃ γ ∈ Γ, |t - γ - c j| ≤ h
  finite : ∀ t, {j | B j t ≠ 0}.Finite
  sum : ∀ t, ∑ᶠ j, B j t = 1
theorem lineBumpFamily {h : ℝ} (hh : 0 < h) :
    IsPeriodicBumpFamily h {0} (fun (j : ℤ) t => bump (t / h - j)) (fun j => h * j) where
  contDiff j := bump_contDiff.comp ((contDiff_id.div_const h).sub contDiff_const)
  nonneg j t := bump_nonneg _
  le_one j t := bump_le_one _
  periodic j t γ hγ := by
    rw [Set.mem_singleton_iff.1 hγ, add_zero]
  center j := by
    show bump (h * j / h - j) ≠ 0
    rw [mul_div_cancel_left₀ _ hh.ne', sub_self, bump_zero]
    exact one_ne_zero
  near j t ht := by
    refine ⟨0, rfl, ?_⟩
    have ha := abs_lt_one_of_bump_ne_zero ht
    have hb : t - 0 - h * j = h * (t / h - j) := by
      field_simp
      ring
    rw [hb, abs_mul, abs_of_pos hh]
    nlinarith
  finite t := (bump_translates_sum (t / h)).1
  sum t := (bump_translates_sum (t / h)).2
def periodicBump (n : ℕ) (u : ℝ) : ℝ := ∑ᶠ k : ℤ, bump (u - n * k)
theorem periodicBump_add (n : ℕ) (u : ℝ) (k : ℤ) : periodicBump n (u + n * k) = periodicBump n u := by
  unfold periodicBump
  rw [← finsum_comp_equiv (Equiv.subRight k) (f := fun k' : ℤ => bump (u - n * k'))]
  refine finsum_congr fun k' => ?_
  simp only [Equiv.subRight_apply, Int.cast_sub]
  congr 1
  ring
theorem periodicBump_nonneg (n : ℕ) (u : ℝ) : 0 ≤ periodicBump n u :=
  finsum_nonneg fun _ => bump_nonneg _
theorem periodicBump_zero {n : ℕ} (hn : 0 < n) : periodicBump n 0 = 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold periodicBump
  rw [finsum_eq_single _ (0 : ℤ)]
  · simpa using bump_zero
  · intro k hk
    apply bump_eq_zero
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    rw [zero_sub, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < n)]
    nlinarith
theorem periodicBump_contDiff {n : ℕ} (hn : 0 < n) : ContDiff ℝ 1 (periodicBump n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [contDiff_iff_contDiffAt]
  intro u₀
  set m : ℤ := ⌊u₀ / n⌋ with hm
  have hm1 : (m : ℝ) * n ≤ u₀ :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < n)).1 (Int.floor_le _)
  have hm2 : u₀ < ((m : ℝ) + 1) * n :=
    (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).1 (Int.lt_floor_add_one _)
  have hz : ∀ᶠ u in 𝓝 u₀, periodicBump n u = ∑ k ∈ Finset.Icc (m - 3) (m + 3), bump (u - n * k) := by
    filter_upwards [Ioo_mem_nhds (by linarith : u₀ - 1 < u₀) (by linarith : u₀ < u₀ + 1)] with u hu
    unfold periodicBump
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hkF
    apply hk
    apply bump_eq_zero
    simp only [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le] at hkF
    rcases hkF with hlow | hhigh
    · have h' : (k : ℝ) + 4 ≤ m := by exact_mod_cast (by omega : k + 4 ≤ m)
      refine le_abs.2 (Or.inl ?_)
      nlinarith [hu.1]
    · have h' : (m : ℝ) + 4 ≤ k := by exact_mod_cast (by omega : m + 4 ≤ k)
      refine le_abs.2 (Or.inr ?_)
      nlinarith [hu.2]
  have hc : ContDiff ℝ 1 fun u => ∑ k ∈ Finset.Icc (m - 3) (m + 3), bump (u - n * k) :=
    ContDiff.sum fun k _ => bump_contDiff.comp (contDiff_id.sub contDiff_const)
  exact hc.contDiffAt.congr_of_eventuallyEq hz
theorem periodicBump_sum (n : ℕ) [NeZero n] (u : ℝ) :
    ∑ j : Fin n, periodicBump n (u - (j : ℕ)) = 1 := by
  obtain ⟨hfin, hsum⟩ := bump_translates_sum u
  let e : Fin n × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv n).symm
  have he : ∀ (j : Fin n) (k : ℤ), e (j, k) = k * n + ((j : ℕ) : ℤ) := fun j k => rfl
  have hone : ∑ᶠ p : Fin n × ℤ, bump (u - ((e p : ℤ) : ℝ)) = 1 := by
    rw [finsum_comp_equiv e (f := fun m : ℤ => bump (u - (m : ℝ)))]
    exact hsum
  have hsupp : (Function.support fun p : Fin n × ℤ => bump (u - ((e p : ℤ) : ℝ))).Finite :=
    (hfin.preimage e.injective.injOn).subset fun p hp => hp
  rw [finsum_curry _ hsupp, finsum_eq_sum_of_fintype] at hone
  rw [← hone]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold periodicBump
  refine finsum_congr fun k => ?_
  rw [he]
  push_cast
  congr 1
  ring
theorem circleBumpFamily {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) [NeZero n] :
    IsPeriodicBumpFamily (ℓ / n) {γ | ∃ k : ℤ, γ = k * ℓ}
      (fun (j : Fin n) t => periodicBump n (t / (ℓ / n) - (j : ℕ)))
      (fun j => ℓ / n * ((j : ℕ) : ℝ)) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh : 0 < ℓ / n := div_pos hℓ hn
  have hsum : ∀ t : ℝ, ∑ j : Fin n, periodicBump n (t / (ℓ / n) - (j : ℕ)) = 1 :=
    fun t => periodicBump_sum n _
  refine ⟨fun j => ?_, fun j t => periodicBump_nonneg _ _, fun j t => ?_, ?_, fun j => ?_, ?_,
    fun t => Set.toFinite _, fun t => ?_⟩
  · exact (periodicBump_contDiff hn0).comp ((contDiff_id.div_const _).sub contDiff_const)
  · rw [← hsum t]
    exact Finset.single_le_sum (f := fun j : Fin n => periodicBump n (t / (ℓ / n) - (j : ℕ)))
      (fun i _ => periodicBump_nonneg _ _) (Finset.mem_univ j)
  · rintro j t _ ⟨k, rfl⟩
    have hshift : (t + k * ℓ) / (ℓ / n) - (j : ℕ) = (t / (ℓ / n) - (j : ℕ)) + n * k := by
      field_simp
      ring
    show periodicBump n ((t + k * ℓ) / (ℓ / n) - (j : ℕ)) = _
    rw [hshift, periodicBump_add]
  · show periodicBump n (ℓ / n * ((j : ℕ) : ℝ) / (ℓ / n) - (j : ℕ)) ≠ 0
    rw [mul_div_cancel_left₀ _ hh.ne', sub_self, periodicBump_zero hn0]
    exact one_ne_zero
  · intro j t ht
    obtain ⟨k, hk⟩ : ∃ k : ℤ, bump (t / (ℓ / n) - (j : ℕ) - n * k) ≠ 0 := by
      by_contra hcon
      exact ht (finsum_eq_zero_of_forall_eq_zero fun k => by_contra fun hk => hcon ⟨k, hk⟩)
    refine ⟨k * ℓ, ⟨k, rfl⟩, ?_⟩
    have ha := abs_lt_one_of_bump_ne_zero hk
    have hb : t - k * ℓ - ℓ / n * ((j : ℕ) : ℝ) =
        ℓ / n * (t / (ℓ / n) - (j : ℕ) - n * k) := by
      field_simp
      ring
    rw [hb, abs_mul, abs_of_pos hh]
    nlinarith
  · rw [finsum_eq_sum_of_fintype]
    exact hsum t
theorem prod_bumpFamily_sum {h : ℝ} {Γ : Set ℝ} {J : Type} {B : J → ℝ → ℝ} {c : J → ℝ}
    (hs : IsPeriodicBumpFamily h Γ B c) (x : Fin 4 → ℝ) :
    {ν : Fin 4 → J | ∏ i, B (ν i) (x i) ≠ 0}.Finite ∧ ∑ᶠ ν : Fin 4 → J, ∏ i, B (ν i) (x i) = 1 := by
  classical
  let F : Fin 4 → Finset J := fun i => (hs.finite (x i)).toFinset
  have hsub : {ν : Fin 4 → J | ∏ i, B (ν i) (x i) ≠ 0} ⊆ (Fintype.piFinset F : Set (Fin 4 → J)) := by
    intro ν hν
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    refine (hs.finite (x i)).mem_toFinset.2 fun h0 => ?_
    exact hν (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub, ← Finset.prod_univ_sum F (fun i j => B j (x i))]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← hs.sum (x i)]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro j hj
  simpa [F] using hj
def closedCube (h : ℝ) (p : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := Set.Icc (fun i => p i - h) (fun i => p i + h)
theorem mem_closedCube {h : ℝ} {p x : Fin 4 → ℝ} : x ∈ closedCube h p ↔ ∀ i, |x i - p i| ≤ h := by
  simp only [closedCube, Set.mem_Icc, Pi.le_def, abs_le]
  constructor
  · rintro ⟨hl, hu⟩ i
    constructor <;> linarith [hl i, hu i]
  · intro hx
    exact ⟨fun i => by linarith [(hx i).1], fun i => by linarith [(hx i).2]⟩
theorem euclidNormVec_le {v : Fin 4 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hv : ∀ i, |v i| ≤ a) :
    TorusMetric.euclidNormVec v ≤ 2 * a := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.sqrt_sum_sq_le_two_mul <;> assumption
theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
section AmbientFacts
variable (s : Conventions.StandingParameters) (E : Ambient)
theorem pointDist_proj_lt
    (hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y))
    {x y : Fin 4 → ℝ} {r : ℝ} (hxy : dist x y < r / 2) :
    E.pointDist s (E.proj s x) (E.proj s y) < r := by
  have ha : ∀ i, |(x - y) i| ≤ dist x y := fun i => by
    simpa [Real.dist_eq] using dist_le_pi_dist x y i
  have hb := euclidNormVec_le dist_nonneg ha
  linarith [hle x y]
theorem isOpen_preimage_proj
    (hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y))
    {U : Set (E.Carrier s)} (hU : E.IsOpenSubset s U) : IsOpen (E.proj s ⁻¹' U) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, hb⟩ := hU _ hx
  refine ⟨r / 2, by positivity, fun y hy => hb _ ?_⟩
  rw [Metric.mem_ball, dist_comm] at hy
  exact pointDist_proj_lt s E hle hy
theorem isCompactSubset_image_proj
    (hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y))
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) : E.IsCompactSubset s (E.proj s '' K) := by
  intro 𝒰 hU hcov
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun U : 𝒰 => E.proj s ⁻¹' (U : Set (E.Carrier s)))
    (fun U => isOpen_preimage_proj s E hle (hU U U.2))
    (fun x hx => by
      obtain ⟨U, hU', hxU⟩ := hcov ⟨x, hx, rfl⟩
      exact Set.mem_iUnion.2 ⟨⟨U, hU'⟩, hxU⟩)
  refine ⟨Subtype.val '' (t : Set 𝒰), ?_, (t.finite_toSet).image _, ?_⟩
  · rintro _ ⟨U, _, rfl⟩
    exact U.2
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨U, hU', hxU⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨U, ⟨U, hU', rfl⟩, hxU⟩
theorem closureSet_subset_image_proj (hd : FamilyTopology.IsMetricFunction (E.pointDist s))
    (hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y))
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) {Z : Set (E.Carrier s)}
    (hZ : Z ⊆ E.proj s '' K) : E.closureSet s Z ⊆ E.proj s '' K := by
  intro x hx
  obtain ⟨y0, hy0, -⟩ := hx 1 one_pos
  obtain ⟨q0, hq0, -⟩ := hZ hy0
  have hcont : Continuous fun q => E.pointDist s x (E.proj s q) := by
    rw [Metric.continuous_iff]
    intro b e he
    refine ⟨e / 2, by positivity, fun a ha => ?_⟩
    have hab := pointDist_proj_lt s E hle ha
    have htri1 := hd.triangle x (E.proj s a) (E.proj s b)
    have htri2 := hd.triangle x (E.proj s b) (E.proj s a)
    have hsymm := hd.symm (E.proj s a) (E.proj s b)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn ⟨q0, hq0⟩ hcont.continuousOn
  refine ⟨q, hq, ?_⟩
  by_contra hne
  have hpos : 0 < E.pointDist s x (E.proj s q) :=
    lt_of_le_of_ne (hd.nonneg _ _) fun h0 => hne ((hd.eq_zero_iff _ _).1 h0.symm).symm
  obtain ⟨y, hy, hlt⟩ := hx _ hpos
  obtain ⟨q', hq', rfl⟩ := hZ hy
  exact absurd (hmin hq') (not_le.2 hlt)
theorem isClosedSubset_closureSet (hd : FamilyTopology.IsMetricFunction (E.pointDist s))
    (Z : Set (E.Carrier s)) : E.IsClosedSubset s (E.closureSet s Z) := by
  intro x hx
  have hex : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z, ¬ E.pointDist s x y < r := by
    by_contra hcon
    refine hx fun r hr => ?_
    by_contra hcon'
    exact hcon ⟨r, hr, fun y hy hlt => hcon' ⟨y, hy, hlt⟩⟩
  obtain ⟨r, hr, hb⟩ := hex
  refine ⟨r / 2, by positivity, fun y hy hyc => ?_⟩
  obtain ⟨z, hz, hlt⟩ := hyc (r / 2) (by positivity)
  exact hb z hz (by linarith [hd.triangle x y z])
theorem isCompactSubset_closureSet (hd : FamilyTopology.IsMetricFunction (E.pointDist s))
    (hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y))
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) {Z : Set (E.Carrier s)}
    (hZ : Z ⊆ E.proj s '' K) : E.IsCompactSubset s (E.closureSet s Z) := by
  have hsub := closureSet_subset_image_proj s E hd hle hK hZ
  have hclosed : IsClosed (E.proj s ⁻¹' E.closureSet s Z) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact isOpen_preimage_proj s E hle (isClosedSubset_closureSet s E hd Z)
  have himg := isCompactSubset_image_proj s E hle (hK.inter_right hclosed)
  have heq : E.proj s '' (K ∩ E.proj s ⁻¹' E.closureSet s Z) = E.closureSet s Z := by
    ext y
    constructor
    · rintro ⟨q, ⟨-, hq⟩, rfl⟩
      exact hq
    · intro hy
      obtain ⟨q, hq, rfl⟩ := hsub hy
      exact ⟨q, ⟨hq, hy⟩, rfl⟩
  rwa [heq] at himg
end AmbientFacts
theorem exists_of_bumpFamily (hyp : AmbientMetric.Claim) (s : Conventions.StandingParameters)
    (E : Ambient) {ε h : ℝ} {Γ : Set ℝ} {J : Type} {B : J → ℝ → ℝ} {c : J → ℝ}
    (hs : IsPeriodicBumpFamily h Γ B c) (hh : 0 ≤ h) (hε : 4 * h ≤ ε)
    (hker : ∀ γ : Fin 4 → ℝ, γ ∈ E.periodGroup s ↔ ∀ i, γ i ∈ Γ)
    (hfin : ∀ C : Set (E.Carrier s), E.IsCompactSubset s C →
      {ν : Fin 4 → J | (C ∩ E.proj s '' closedCube h fun i => c (ν i)).Nonempty}.Finite) :
    ∃ (I : Type) (ψ : I → E.Carrier s → ℝ), IsFinePartitionOfUnity s E ε ψ := by
  have hP := (hyp s E).1
  have hd : FamilyTopology.IsMetricFunction (E.pointDist s) := hP.2.1
  have hle : ∀ x y, E.pointDist s (E.proj s x) (E.proj s y) ≤
      TorusMetric.euclidNormVec (x - y) := fun x y => (hP.1 x y).2
  let Φ : (Fin 4 → J) → (Fin 4 → ℝ) → ℝ := fun ν x => ∏ i, B (ν i) (x i)
  let Q : (Fin 4 → J) → Set (Fin 4 → ℝ) := fun ν => closedCube h fun i => c (ν i)
  have hper : ∀ ν x, ∀ γ ∈ E.periodGroup s, Φ ν (x + γ) = Φ ν x := fun ν x γ hγ =>
    Finset.prod_congr rfl fun i _ => hs.periodic _ _ _ ((hker γ).1 hγ i)
  have hlift : ∀ ν x, Φ ν (E.someLift s (E.proj s x)) = Φ ν x := by
    intro ν x
    obtain ⟨γ, hγ, hx⟩ := (E.isLiftOf_iff s (x := E.proj s x) (y := x) rfl
      (E.someLift s (E.proj s x))).mp (E.proj_someLift s _)
    rw [hx]
    exact hper ν x γ hγ
  let ψ : (Fin 4 → J) → E.Carrier s → ℝ := fun ν y => Φ ν (E.someLift s y)
  have hnz : ∀ ν, {y | ψ ν y ≠ 0} ⊆ E.proj s '' Q ν := by
    intro ν y hy
    have hu : ∀ i, ∃ γ ∈ Γ, |E.someLift s y i - γ - c (ν i)| ≤ h := fun i =>
      hs.near _ _ fun h0 => hy (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    choose γ hγ hb using hu
    have hγk := (hker γ).2 hγ
    refine ⟨E.someLift s y - γ, mem_closedCube.2 fun i => hb i, ?_⟩
    rw [sub_eq_add_neg, E.proj_add, E.proj_neg, (E.mem_periodGroup_iff s γ).1 hγk, neg_zero,
      add_zero]
    exact E.proj_someLift s y
  have hsup : ∀ ν, E.closedSupport s (ψ ν) ⊆ E.proj s '' Q ν := fun ν =>
    closureSet_subset_image_proj s E hd hle isCompact_Icc (hnz ν)
  refine ⟨Fin 4 → J, ψ, ⟨fun ν => ⟨?_, ?_⟩, fun ν x => ⟨?_, ?_⟩, fun ν => ?_, fun ν => ?_,
    fun C hC => ?_, fun x => ?_, fun x => ?_⟩⟩
  · have hl : E.liftFun s (ψ ν) = Φ ν := funext fun x => hlift ν x
    show ContDiff ℝ 1 (E.liftFun s (ψ ν))
    rw [hl]
    exact contDiff_prod fun i _ => (hs.contDiff (ν i)).comp (contDiff_apply ℝ ℝ i)
  · exact isCompactSubset_closureSet s E hd hle isCompact_Icc (hnz ν)
  · exact Finset.prod_nonneg fun i _ => hs.nonneg _ _
  · exact Finset.prod_le_one (fun i _ => hs.nonneg _ _) fun i _ => hs.le_one _ _
  · refine ⟨E.proj s fun i => c (ν i), fun r hr =>
      ⟨E.proj s fun i => c (ν i), ?_, ?_⟩⟩
    · show ψ ν (E.proj s fun i => c (ν i)) ≠ 0
      show Φ ν (E.someLift s (E.proj s fun i => c (ν i))) ≠ 0
      rw [hlift]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hs.center (ν i)
    · rw [(hd.eq_zero_iff _ _).2 rfl]
      exact hr
  · unfold Ambient.setDiam
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨p, hp, rfl⟩ := hsup ν hx
    obtain ⟨q, hq, rfl⟩ := hsup ν hy
    have hpq : ∀ i, |(p - q) i| ≤ 2 * h := by
      intro i
      have hpi := mem_closedCube.1 hp i
      have hqi := mem_closedCube.1 hq i
      rw [abs_le] at hpi hqi ⊢
      simp only [Pi.sub_apply]
      constructor <;> linarith [hpi.1, hpi.2, hqi.1, hqi.2]
    have := euclidNormVec_le (by positivity) hpq
    linarith [hle p q]
  · exact (hfin C hC).subset fun ν ⟨y, hyC, hyS⟩ => ⟨y, hyC, hsup ν hyS⟩
  · exact (prod_bumpFamily_sum hs _).1
  · exact (prod_bumpFamily_sum hs _).2
theorem finite_closedCubes_of_compact (hyp : AmbientMetric.Claim) (s : Conventions.StandingParameters)
    {h : ℝ} (hh : 0 < h) (C : Set (Ambient.euclidean.Carrier s))
    (hC : Ambient.euclidean.IsCompactSubset s C) :
    {ν : Fin 4 → ℤ | (C ∩ Ambient.euclidean.proj s ''
      closedCube h fun i => h * (ν i : ℝ)).Nonempty}.Finite := by
  have hd : FamilyTopology.IsMetricFunction (Ambient.euclidean.pointDist s) := (hyp s _).1.2.1
  let ball : ℕ → Set (Ambient.euclidean.Carrier s) :=
    fun N => {y | Ambient.euclidean.pointDist s 0 y < N}
  have hopen : ∀ U ∈ Set.range ball, Ambient.euclidean.IsOpenSubset s U := by
    rintro _ ⟨N, rfl⟩ y hy
    refine ⟨N - Ambient.euclidean.pointDist s 0 y, sub_pos.2 hy, fun z hz => ?_⟩
    show Ambient.euclidean.pointDist s 0 z < N
    linarith [hd.triangle 0 y z]
  have hcov : C ⊆ ⋃₀ Set.range ball := by
    intro y _
    obtain ⟨N, hN⟩ := exists_nat_gt (Ambient.euclidean.pointDist s 0 y)
    exact ⟨ball N, ⟨N, rfl⟩, hN⟩
  obtain ⟨𝒰, hsub, hfinU, hcov'⟩ := hC _ hopen hcov
  let g : Set (Ambient.euclidean.Carrier s) → ℕ := fun U => sInf {N | ball N = U}
  have hg : ∀ U ∈ 𝒰, ball (g U) = U := fun U hU => Nat.sInf_mem (s := {N | ball N = U}) (hsub hU)
  obtain ⟨N, hN⟩ := (hfinU.image g).bddAbove
  have hbound : ∀ y ∈ C, Ambient.euclidean.pointDist s 0 y < N := by
    intro y hy
    obtain ⟨U, hU, hyU⟩ := hcov' hy
    rw [← hg U hU] at hyU
    have hgN : (g U : ℝ) ≤ N := by exact_mod_cast hN ⟨U, hU, rfl⟩
    exact lt_of_lt_of_le hyU hgN
  obtain ⟨M, hM⟩ := exists_nat_gt ((N : ℝ) / h + 1)
  refine (Set.finite_Icc (fun _ => -(M : ℤ)) (fun _ => (M : ℤ))).subset ?_
  rintro ν ⟨y, hyC, q, hq, rfl⟩
  have hyN := hbound _ hyC
  have hq' : ∀ i, |q i| < N := fun i => by
    have ha := abs_le_euclidNormVec (0 - q) i
    have hb : |(0 - q) i| = |q i| := by simp
    have hc : Ambient.euclidean.pointDist s 0 q = TorusMetric.euclidNormVec (0 - q) := rfl
    have hp : Ambient.euclidean.proj s q = q := rfl
    rw [hp, hc] at hyN
    linarith
  have hν : ∀ i, |(ν i : ℝ)| < M := by
    intro i
    have hqi := mem_closedCube.1 hq i
    have hscaled : h * |(ν i : ℝ)| ≤ N + h := by
      rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh]
      have htri : |h * (ν i : ℝ)| ≤ |q i| + |q i - h * (ν i : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (h * (ν i : ℝ)) (q i)
        rw [abs_sub_comm (h * (ν i : ℝ))] at this
        linarith
      linarith [hq' i]
    have hdiv : |(ν i : ℝ)| ≤ (N : ℝ) / h + 1 := by
      rw [div_add_one hh.ne', le_div_iff₀ hh]
      linarith
    linarith
  constructor
  · intro i
    have := (abs_lt.1 (hν i)).1
    exact_mod_cast this.le
  · intro i
    have := (abs_lt.1 (hν i)).2
    exact_mod_cast this.le
theorem claim_holds (hyp : AmbientMetric.Claim) : Claim := by
  intro s E ε hε
  cases E with
  | euclidean =>
    have hh : 0 < ε / 4 := by positivity
    refine exists_of_bumpFamily hyp s Ambient.euclidean (lineBumpFamily hh) hh.le (by linarith) ?_
      (finite_closedCubes_of_compact hyp s hh)
    intro γ
    show γ ∈ (⊥ : AddSubgroup (Fin 4 → ℝ)) ↔ _
    rw [AddSubgroup.mem_bot]
    simp [funext_iff]
  | periodic =>
    have hL : (0 : ℝ) < s.L := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : 0 < s.L)
    have hℓ : 0 < s.side := by
      show 0 < PeriodicLattice.torusSide s.L s.m
      unfold PeriodicLattice.torusSide
      positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (4 * s.side / ε)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    have hn1 : n ≠ 0 := by
      rintro rfl
      simp at hn0
    have : NeZero n := ⟨hn1⟩
    refine exists_of_bumpFamily hyp s Ambient.periodic (circleBumpFamily hℓ n) (by positivity) ?_ ?_
      fun C _ => Set.toFinite _
    · have hlt : 4 * s.side < n * ε := (div_lt_iff₀ hε).1 hn
      have heq : 4 * (s.side / n) = 4 * s.side / n := by ring
      rw [heq, div_le_iff₀ hn0]
      linarith
    · intro γ
      constructor
      · rintro ⟨k, hk⟩ i
        exact ⟨k i, hk i⟩
      · intro hγ
        choose k hk using hγ
        exact ⟨k, hk⟩
end YangMills.Construction.LimitSpaces.FinePartitionOfUnity
end
