import YangMills.Construction.LimitsOfLatticeFamilies.CuttingIsometriesAndTheModulus
import YangMills.Construction.LimitsOfLatticeFamilies.FactsOfTheSetting
import YangMills.Construction.LimitsOfLatticeFamilies.LinearRelationsAmongTensors
import YangMills.Construction.LimitsOfLatticeFamilies.PartitionsOfUnityOfClassC1
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.TensorRelations
open ModelSpace C1PartitionOfUnity
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
theorem exists_linearIndependent_expansion {V : Type*} [AddCommGroup V] [Module ℝ V] {T : Type}
    [Finite T] (w : T → V) : ∃ (n : ℕ) (e : Fin n → V) (a : T → Fin n → ℝ),
      LinearIndependent ℝ e ∧ ∀ t, w t = ∑ γ, a t γ • e γ := by
  let E : Submodule ℝ V := Submodule.span ℝ (Set.range w)
  have hE : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  let b := Module.finBasis ℝ E
  refine ⟨_, fun γ => (b γ).1, fun t γ => b.repr ⟨w t, Submodule.subset_span ⟨t, rfl⟩⟩ γ,
    b.linearIndependent.map' E.subtype (Submodule.ker_subtype _), fun t => ?_⟩
  have h1 := b.sum_repr ⟨w t, Submodule.subset_span ⟨t, rfl⟩⟩
  have h2 := congrArg Subtype.val h1
  rw [Submodule.coe_sum] at h2
  exact h2.symm
theorem sum_mul_multilinear_eq_zero_of_relation {X : Type*} : ∀ (q : ℕ)
    (W : Fin q → Submodule ℝ (X → ℝ))
    (F : MultilinearMap ℝ (fun l => W l) ℝ) {T : Type} [Fintype T]
    (u : T → (l : Fin q) → W l) (c : T → ℝ),
    (∀ y : Fin q → X, ∑ t, c t * ∏ l, (u t l).1 (y l) = 0) → ∑ t, c t * F (u t) = 0 := by
  intro q
  induction q with
  | zero =>
    intro W F T _ u c h
    have h0 := h (fun i => i.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h0
    have hu : ∀ t, u t = fun i => i.elim0 := fun t => funext fun i => i.elim0
    simp only [hu, ← Finset.sum_mul, h0, zero_mul]
  | succ q ih =>
    intro W F T _ u c h
    classical
    obtain ⟨n, e, a, hli₀, hexp⟩ := exists_linearIndependent_expansion fun t => u t 0
    have hval : ∀ t x, (u t 0).1 x = ∑ γ, a t γ * (e γ).1 x := by
      intro t x
      have h1 := congrArg (fun w : W 0 => w.1 x) (hexp t)
      simpa [Submodule.coe_sum, Finset.sum_apply] using h1
    have hF : ∀ t, F (u t) = ∑ γ, a t γ * F.curryLeft (e γ) (fun l => u t l.succ) := by
      intro t
      have h1 : F (u t) = F.curryLeft (u t 0) (fun l => u t l.succ) := by
        rw [MultilinearMap.curryLeft_apply]
        congr 1
        exact (Fin.cons_self_tail (u t)).symm
      rw [h1, hexp t, map_sum, sum_apply]
      refine Finset.sum_congr rfl fun γ _ => ?_
      simp [map_smul]
    have hli : LinearIndependent ℝ (fun γ => ((e γ).1 : X → ℝ)) :=
      hli₀.map' (W 0).subtype (Submodule.ker_subtype _)
    have hP : ∀ γ (y' : Fin q → X),
        ∑ t, (c t * a t γ) * ∏ l, (u t l.succ).1 (y' l) = 0 := by
      intro γ y'
      have hs : ∑ γ, (∑ t, (c t * a t γ) * ∏ l, (u t l.succ).1 (y' l)) • ((e γ).1 : X → ℝ) = 0 := by
        funext x
        have hx := h (Fin.cons x y')
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hx]
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hval t x, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
      exact Fintype.linearIndependent_iff.1 hli _ hs γ
    have hG : ∀ γ, ∑ t, (c t * a t γ) * F.curryLeft (e γ) (fun l => u t l.succ) = 0 := fun γ =>
      ih (fun l => W l.succ) (F.curryLeft (e γ)) (fun t l => u t l.succ)
        (fun t => c t * a t γ) (hP γ)
    calc ∑ t, c t * F (u t)
        = ∑ γ, ∑ t, (c t * a t γ) * F.curryLeft (e γ) (fun l => u t l.succ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hF t, Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          ring
      _ = 0 := Finset.sum_eq_zero fun γ _ => hG γ
theorem existsUnique_linearMap_span_of_relations {V D : Type} [AddCommGroup V] [Module ℂ V]
    (τ : D → V) (C : Set D) (φ : C → ℂ)
    (hτ : ∀ (T : Type) [Fintype T] (f : T → C) (c : T → ℂ),
      ∑ t, c t • τ (f t).1 = 0 → ∑ t, c t * φ (f t) = 0) :
    ∃! Λ : Submodule.span ℂ (τ '' C) →ₗ[ℂ] ℂ, ∀ (x : D) (hx : x ∈ C),
      Λ ⟨τ x, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = φ ⟨x, hx⟩ := by
  classical
  let S := Submodule.span ℂ (τ '' C)
  let v : C → S := fun x => ⟨τ x.1, Submodule.subset_span ⟨x.1, x.2, rfl⟩⟩
  have hv : Submodule.span ℂ (Set.range v) = ⊤ := by
    have h1 := Submodule.span_span_coe_preimage (R := ℂ) (s := τ '' C)
    have h2 : Set.range v = ((↑) : S → V) ⁻¹' (τ '' C) := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨c.1, c.2, rfl⟩
      · rintro ⟨d, hd, hdx⟩
        exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
    rw [h2]
    exact h1
  let π : (C →₀ ℂ) →ₗ[ℂ] S := Finsupp.linearCombination ℂ v
  let Φ : (C →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ φ
  have hπ : LinearMap.range π = ⊤ := by
    rw [Finsupp.range_linearCombination]
    exact hv
  have hker : ∀ l, π l = 0 → Φ l = 0 := by
    intro l hl
    have h1 : ∑ t : l.support, l t.1 • τ t.1.1 = 0 := by
      have h2 := congrArg Subtype.val hl
      simp only [π, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
        Submodule.coe_smul, ZeroMemClass.coe_zero] at h2
      rw [Finset.sum_coe_sort l.support (fun x => l x • τ x.1)]
      exact h2
    have h3 := hτ l.support (fun t => t.1) (fun t => l t.1) h1
    rw [Finset.sum_coe_sort l.support (fun x => l x * φ x)] at h3
    simpa [Φ, Finsupp.linearCombination_apply, Finsupp.sum] using h3
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective π hπ
  have hform : ∀ x : C, Φ (g (v x)) = φ x := by
    intro x
    have hd : π (g (v x) - Finsupp.single x 1) = 0 := by
      have h1 : π (g (v x)) = v x := LinearMap.congr_fun hg (v x)
      rw [map_sub, h1]
      simp [π, Finsupp.linearCombination_single]
    have h2 := hker _ hd
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
    simp [Φ, Finsupp.linearCombination_single]
  refine ⟨Φ ∘ₗ g, fun x hx => hform ⟨x, hx⟩, fun Λ hΛ => ?_⟩
  refine LinearMap.ext_on_range hv fun x => ?_
  exact (hΛ x.1 x.2).trans (hform x).symm
theorem c1CompactSupp_mono {A B : Set (Y.Carrier s)} (h : A ⊆ B) :
    c1CompactSupp s Y A ⊆ c1CompactSupp s Y B :=
  fun _ hf => ⟨hf.1, hf.2.1, hf.2.2.trans h⟩
theorem exists_multilinearMap_of_disjoint
    (hW : ∀ A : Set (Y.Carrier s), ∃ W : Submodule ℝ (Y.Carrier s → ℝ),
      (W : Set _) = c1CompactSupp s Y A)
    {n : ℕ} {ρ : ℝ≥0∞} {Ψ : TupleFunctional (sepTuplesIn s Y n ρ)}
    (hΨ : IsMultilinearSep Ψ) (A : Fin n → Set (Y.Carrier s))
    (hA : ∀ l, A l ⊆ ballAtBase s Y ρ) (hdis : ∀ l k, l ≠ k → Disjoint (A l) (A k)) :
    ∃ (W : Fin n → Submodule ℝ (Y.Carrier s → ℝ)) (G : MultilinearMap ℝ (fun l => W l) ℝ),
      (∀ l, (W l : Set (Y.Carrier s → ℝ)) = c1CompactSupp s Y (A l)) ∧
        ∀ g, G g = Ψ.extend fun l => (g l).1 := by
  choose W hWA using fun l => hW (A l)
  have hmem : ∀ (l : Fin n) (x : W l), x.1 ∈ c1CompactSupp s Y (A l) := fun l x => by
    rw [← hWA l]
    exact x.2
  have upd : ∀ (m : ∀ l, W l) (i : Fin n) (z : W i),
      (fun l => (Function.update m i z l).1) = Function.update (fun l => (m l).1) i z.1 := by
    intro m i z
    funext l
    by_cases h : l = i
    · subst h
      simp
    · simp [h]
  refine ⟨W, MultilinearMap.mk' (fun g => Ψ.extend fun l => (g l).1) ?_ ?_, hWA, fun g => rfl⟩
  · intro m i x y
    have key := hΨ A hA hdis (fun l => (m l).1) (fun l => hmem l _) i x.1 (hmem i x) y.1
      (hmem i y) 1 1
    simp only [upd]
    simpa using key
  · intro m i c x
    have key := hΨ A hA hdis (fun l => (m l).1) (fun l => hmem l _) i x.1 (hmem i x) x.1
      (hmem i x) c 0
    simp only [upd]
    simpa using key
theorem mem_supportIn_of_ne_zero (hself : ∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = 0 ↔ x = y)
    {f : Y.Carrier s → ℝ} {y : Y.Carrier s} (h : f y ≠ 0) : y ∈ supportIn s Y f :=
  fun r hr => ⟨y, h, by rw [(hself y y).2 rfl]; exact hr⟩
theorem exists_pos_le_dist_supports {M : BlockScale s} (facts : SettingFactsHold s M Y) {q : ℕ}
    {T : Type} [Fintype T] (f : T → FunTuple s Y q) (hf : ∀ t, f t ∈ sepTuples s Y q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t l k, l ≠ k → ∀ y ∈ supportIn s Y (f t l), ∀ y' ∈ supportIn s Y (f t k),
      δ ≤ ModelSpace.dist s Y y y' := by
  by_cases hq : 2 ≤ q
  · have hd : ∀ t, ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ minSeparation s Y (f t) := by
      intro t
      obtain ⟨r, hr0, hr⟩ :=
        ENNReal.lt_iff_exists_nnreal_btwn.1 (facts.minSeparation_pos q hq _ (hf t)).1
      refine ⟨r, by exact_mod_cast hr0, ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact hr.le
    choose d hd0 hd using hd
    have hmin : ∃ δ : ℝ, 0 < δ ∧ ∀ t, δ ≤ d t := by
      by_cases hT : Nonempty T
      · obtain ⟨t₀, ht₀⟩ := Finite.exists_min d
        exact ⟨d t₀, hd0 t₀, ht₀⟩
      · exact ⟨1, one_pos, fun t => (hT ⟨t⟩).elim⟩
    obtain ⟨δ, hδ, hδd⟩ := hmin
    refine ⟨δ, hδ, fun t l k hlk y hy y' hy' => (hδd t).trans ?_⟩
    have h1 : minSeparation s Y (f t) ≤
        ModelSpace.infDist s Y (supportIn s Y (f t l)) (supportIn s Y (f t k)) :=
      (iInf_le _ l).trans ((iInf_le _ k).trans (iInf_le _ hlk))
    have h2 : ModelSpace.infDist s Y (supportIn s Y (f t l)) (supportIn s Y (f t k)) ≤
        ENNReal.ofReal (ModelSpace.dist s Y y y') :=
      iInf₂_le_of_le y hy (iInf₂_le y' hy')
    exact (ENNReal.ofReal_le_ofReal_iff (facts.dist_invariant.2.2.1 y y')).1
      ((hd t).trans (h1.trans h2))
  · refine ⟨1, one_pos, fun t l k hlk => ?_⟩
    exact absurd (Fin.ext (by omega)) hlk
theorem exists_partition_fine (hP : C1PartitionOfUnity.Claim) (M : BlockScale s) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (I : Type) (χ : I → c1CompactSupp s Y univ) (ς : ℝ), 0 < ς ∧ 8 * ς < δ ∧
      IsSmoothPartitionAtScale s Y ς χ := by
  cases Y with
  | euclidean =>
    obtain ⟨χ, hχ⟩ := (hP s M (δ / 16) (by positivity)).1
    exact ⟨_, χ, δ / 16, by positivity, by linarith, hχ⟩
  | torus =>
    have hside : 0 < s.side := by
      have hL : 0 < s.L := by
        have := s.isAdmissible.2
        omega
      have hL' : (0 : ℝ) < s.L := by exact_mod_cast hL
      simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
      positivity
    let w : ℕ := ⌈8 * s.side / δ⌉₊ + 3
    have hw3 : 3 ≤ w := by omega
    have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
    have hwδ : 8 * s.side / δ < w := by
      have h1 := Nat.le_ceil (8 * s.side / δ)
      have h2 : (⌈8 * s.side / δ⌉₊ : ℝ) < w := by
        have : (w : ℝ) = (⌈8 * s.side / δ⌉₊ : ℝ) + 3 := by simp [w]
        linarith
      linarith
    have : NeZero w := ⟨by omega⟩
    have hς : 0 < s.side / (w : ℝ) := by positivity
    obtain ⟨χ, hχ, -⟩ := (hP s M _ hς).2 w hw3 rfl
    refine ⟨_, χ, _, hς, ?_, hχ⟩
    rw [div_lt_iff₀ hδ] at hwδ
    rw [← mul_div_assoc, div_lt_iff₀ hw0]
    linarith
theorem sum_mul_eq_zero_of_real_relation {M : BlockScale s} (facts : SettingFactsHold s M Y)
    (hP : C1PartitionOfUnity.Claim) (hC : CutoffAndSymmetry.Assertions)
    {q : ℕ} {ρ : ℝ≥0∞} (Ψ : TupleFunctional (sepTuplesIn s Y q ρ))
    (hΨ : IsMultilinearSep Ψ) {T : Type} [Fintype T]
    (f : T → sepTuplesIn s Y q ρ) (c : T → ℝ)
    (h : ∀ y : Fin q → Y.Carrier s, ∑ t, c t * ∏ l, (f t).1 l (y l) = 0) :
    ∑ t, c t * Ψ (f t) = 0 := by
  classical
  have hself := facts.dist_invariant.2.2.2.1
  have htri := facts.dist_invariant.2.2.2.2.2.1
  have hW := facts.submodules.2.1
  obtain ⟨δ, hδ, hsep⟩ :=
    exists_pos_le_dist_supports facts (fun t => (f t).1) fun t => (f t).2.1
  obtain ⟨I, χ, ς, hς, hςδ, hχ⟩ := exists_partition_fine (Y := Y) hP M hδ
  have hfin : ∀ t l, {ι | (supportIn s Y ((f t).1 l) ∩ supportIn s Y (χ ι).1).Nonempty}.Finite :=
    fun t l => hχ.locallyFinite _ ((f t).2.1.2.1 l)
  let I₀ : Finset I :=
    (Set.finite_iUnion fun t => Set.finite_iUnion fun l => hfin t l).toFinset
  have hI₀ : ∀ t l ι, (supportIn s Y ((f t).1 l) ∩ supportIn s Y (χ ι).1).Nonempty → ι ∈ I₀ := by
    intro t l ι hι
    simp only [I₀, Set.Finite.mem_toFinset, Set.mem_iUnion]
    exact ⟨t, l, hι⟩
  let piece : T → Fin q → I → Y.Carrier s → ℝ := fun t l ι y => (χ ι).1 y * (f t).1 l y
  have hself_mem : ∀ t l, (f t).1 l ∈ c1CompactSupp s Y (supportIn s Y ((f t).1 l)) :=
    fun t l => ⟨(f t).2.1.1 l, (f t).2.1.2.1 l, subset_rfl⟩
  have hpiece : ∀ t l ι,
      piece t l ι ∈ c1CompactSupp s Y (supportIn s Y ((f t).1 l) ∩ supportIn s Y (χ ι).1) :=
    fun t l ι => ((hC s M Y).1 _ _ _ (hself_mem t l) (χ ι).2 (hχ.mem_Icc ι)).1
  have hsum : ∀ t l, ∑ ι ∈ I₀, piece t l ι = (f t).1 l := by
    intro t l
    funext y
    simp only [piece, Finset.sum_apply]
    rw [← Finset.sum_mul]
    by_cases hy : (f t).1 l y = 0
    · simp [hy]
    · have hys := mem_supportIn_of_ne_zero hself hy
      have hone : ∑ ι ∈ I₀, (χ ι).1 y = 1 := by
        refine (hasSum_sum_of_ne_finset_zero fun ι hι => ?_).unique (hχ.hasSum_one y)
        by_contra hne
        exact hι (hI₀ t l ι ⟨y, hys, mem_supportIn_of_ne_zero hself hne⟩)
      rw [hone, one_mul]
  let cut : T → (Fin q → I) → FunTuple s Y q := fun t r l => piece t l (r l)
  have hdisj : ∀ t l k, l ≠ k →
      Disjoint (supportIn s Y ((f t).1 l)) (supportIn s Y ((f t).1 k)) := fun t => (f t).2.1.2.2
  have hexp : ∀ t, Ψ.extend (f t).1 =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin q => I₀), Ψ.extend (cut t r) := by
    intro t
    obtain ⟨W, G, hWA, hG⟩ := exists_multilinearMap_of_disjoint hW hΨ
      (fun l => supportIn s Y ((f t).1 l)) (fun l => (f t).2.2 l) (hdisj t)
    have hmem : ∀ l ι, piece t l ι ∈ W l := by
      intro l ι
      exact show piece t l ι ∈ (W l : Set (Y.Carrier s → ℝ)) from by
        rw [hWA l]
        exact c1CompactSupp_mono inter_subset_left (hpiece t l ι)
    have h2 := G.map_sum_finset (fun l ι => (⟨piece t l ι, hmem l ι⟩ : W l))
      (fun _ => I₀)
    simp only [hG] at h2
    have h3 : (fun l => ((∑ ι ∈ I₀, (⟨piece t l ι, hmem l ι⟩ : W l) : W l) : Y.Carrier s → ℝ)) =
        (f t).1 := by
      funext l
      rw [Submodule.coe_sum]
      exact hsum t l
    rw [h3] at h2
    exact h2
  have hzero : ∀ t (r : Fin q → I) i,
      supportIn s Y ((f t).1 i) ∩ supportIn s Y (χ (r i)).1 = ∅ → Ψ.extend (cut t r) = 0 := by
    intro t r i hi
    obtain ⟨W, G, hWA, hG⟩ := exists_multilinearMap_of_disjoint hW hΨ
      (fun l => supportIn s Y ((f t).1 l)) (fun l => (f t).2.2 l) (hdisj t)
    have hmem : ∀ l, cut t r l ∈ W l := by
      intro l
      exact show cut t r l ∈ (W l : Set (Y.Carrier s → ℝ)) from by
        rw [hWA l]
        exact c1CompactSupp_mono inter_subset_left (hpiece t l (r l))
    have hi0 : cut t r i = 0 := by
      funext y
      by_contra hne
      have h1 := (hpiece t i (r i)).2.2 (mem_supportIn_of_ne_zero hself hne)
      rw [hi] at h1
      exact h1
    have h2 := G.map_coord_zero (m := fun l => (⟨cut t r l, hmem l⟩ : W l)) i (Subtype.ext hi0)
    rw [hG] at h2
    exact h2
  have hterm : ∀ r : Fin q → I, ∑ t, c t * Ψ.extend (cut t r) = 0 := by
    intro r
    by_cases hd : ∀ l k, l ≠ k → Disjoint (supportIn s Y (χ (r l)).1) (supportIn s Y (χ (r k)).1)
    · obtain ⟨W, G, hWA, hG⟩ := exists_multilinearMap_of_disjoint hW hΨ
        (fun l => ballAtBase s Y ρ ∩ supportIn s Y (χ (r l)).1) (fun l => inter_subset_left)
        (fun l k hlk => (hd l k hlk).mono inter_subset_right inter_subset_right)
      have hmem : ∀ t l, cut t r l ∈ W l := by
        intro t l
        exact show cut t r l ∈ (W l : Set (Y.Carrier s → ℝ)) from by
          have hsub : supportIn s Y ((f t).1 l) ∩ supportIn s Y (χ (r l)).1 ⊆
              ballAtBase s Y ρ ∩ supportIn s Y (χ (r l)).1 := fun y hy => ⟨(f t).2.2 l hy.1, hy.2⟩
          rw [hWA l]
          exact c1CompactSupp_mono hsub (hpiece t l (r l))
      have h2 := sum_mul_multilinear_eq_zero_of_relation q W G
        (fun t l => ⟨cut t r l, hmem t l⟩) c (by
        intro y
        have h3 : ∀ t, c t * ∏ l, cut t r l (y l) =
            (∏ l, (χ (r l)).1 (y l)) * (c t * ∏ l, (f t).1 l (y l)) := by
          intro t
          simp only [cut, piece, Finset.prod_mul_distrib]
          ring
        simp only [h3]
        rw [← Finset.mul_sum, h y, mul_zero])
      simpa only [hG] using h2
    · simp only [not_forall] at hd
      obtain ⟨l, k, hlk, hnd⟩ := hd
      obtain ⟨y₀, hy₀l, hy₀k⟩ := Set.not_disjoint_iff.1 hnd
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hl : (supportIn s Y ((f t).1 l) ∩ supportIn s Y (χ (r l)).1).Nonempty
      · by_cases hk : (supportIn s Y ((f t).1 k) ∩ supportIn s Y (χ (r k)).1).Nonempty
        · obtain ⟨y, hy, hyχ⟩ := hl
          obtain ⟨y', hy', hyχ'⟩ := hk
          have h1 := hsep t l k hlk y hy y' hy'
          have h2 := htri y y' y₀
          have h3 := hχ.dist_le (r l) y hyχ y₀ hy₀l
          have h4 := hχ.dist_le (r k) y₀ hy₀k y' hyχ'
          exfalso
          linarith
        · rw [hzero t r k (Set.not_nonempty_iff_eq_empty.1 hk), mul_zero]
      · rw [hzero t r l (Set.not_nonempty_iff_eq_empty.1 hl), mul_zero]
  calc ∑ t, c t * Ψ (f t)
      = ∑ t, c t * ∑ r ∈ Fintype.piFinset (fun _ : Fin q => I₀), Ψ.extend (cut t r) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hexp t, TupleFunctional.extend_of_mem Ψ (f t).2]
    _ = ∑ r ∈ Fintype.piFinset (fun _ : Fin q => I₀), ∑ t, c t * Ψ.extend (cut t r) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = 0 := Finset.sum_eq_zero fun r _ => hterm r
theorem respectsTensorRelations {M : BlockScale s} (facts : SettingFactsHold s M Y)
    (hP : C1PartitionOfUnity.Claim) (hC : CutoffAndSymmetry.Assertions)
    {q : ℕ} {ρ : ℝ≥0∞} (Ψ : TupleFunctional (sepTuplesIn s Y q ρ))
    (hΨ : IsMultilinearSep Ψ) : RespectsTensorRelations Ψ := by
  intro T _ f c hrel
  have hy : ∀ y : Fin q → Y.Carrier s,
      ∑ t, c t * ((∏ l, (f t).1 l (y l) : ℝ) : ℂ) = 0 := by
    intro y
    have h1 := congrFun hrel y
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, cTensor,
      tensorProd] using h1
  have hre := sum_mul_eq_zero_of_real_relation facts hP hC Ψ hΨ f (fun t => (c t).re) (fun y => by
    have h1 := congrArg Complex.re (hy y)
    simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re, mul_comm] using h1)
  have him := sum_mul_eq_zero_of_real_relation facts hP hC Ψ hΨ f (fun t => (c t).im) (fun y => by
    have h1 := congrArg Complex.im (hy y)
    simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im, mul_comm] using h1)
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re] using hre
  · simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im] using him
theorem existsUnique_isLinearFormOf {q : ℕ} {ρ : ℝ≥0∞}
    (Ψ : TupleFunctional (sepTuplesIn s Y q ρ))
    (hΨ : RespectsTensorRelations Ψ) : ∃! Λ, IsLinearFormOf Ψ Λ :=
  existsUnique_linearMap_span_of_relations (cTensor s Y) (sepTuplesIn s Y q ρ)
    (fun h => (Ψ h : ℂ)) fun T _ f c hrel => hΨ T f c hrel
theorem restrictTuple_update_of_notMem {q : ℕ} (g : FunTuple s Y q) (i : Fin q)
    (w : Y.Carrier s → ℝ) {B : Finset (Fin q)} (hi : i ∉ B) :
    restrictTuple (Function.update g i w) B = restrictTuple g B := by
  funext m
  have hne : B.orderEmbOfFin rfl m ≠ i := fun e =>
    hi (e ▸ Finset.orderEmbOfFin_mem B rfl m)
  simp [restrictTuple, Function.update_of_ne hne]
theorem restrictTuple_update_of_eq {q : ℕ} (g : FunTuple s Y q) (i : Fin q) (w : Y.Carrier s → ℝ)
    {B : Finset (Fin q)} (j : Fin B.card) (hj : B.orderEmbOfFin rfl j = i) :
    restrictTuple (Function.update g i w) B = Function.update (restrictTuple g B) j w := by
  funext m
  by_cases hm : m = j
  · subst hm
    simp [restrictTuple, hj]
  · have hne : B.orderEmbOfFin rfl m ≠ i := fun e =>
      hm ((B.orderEmbOfFin rfl).injective (e.trans hj.symm))
    simp [restrictTuple, Function.update_of_ne hne, Function.update_of_ne hm]
theorem isMultilinearSep_centredSum {M : BlockScale s} (facts : SettingFactsHold s M Y)
    {q : ℕ} {ρ : ℝ≥0∞} (Ψ : FunctionalSeq s Y ρ) (hΨ : IsMultilinearSeq Ψ) :
    IsMultilinearSep (centredSum Ψ q) := by
  classical
  intro A hA hdis g hg i u hu v hv α β
  have hmemSep : ∀ h : FunTuple s Y q, (∀ l, h l ∈ c1CompactSupp s Y (A l)) →
      h ∈ sepTuplesIn s Y q ρ := fun h hh =>
    ⟨⟨fun l => (hh l).1, fun l => (hh l).2.1,
      fun l k hlk => (hdis l k hlk).mono (hh l).2.2 (hh k).2.2⟩,
      fun l => (hh l).2.2.trans (hA l)⟩
  have hupd : ∀ w ∈ c1CompactSupp s Y (A i), ∀ l,
      Function.update g i w l ∈ c1CompactSupp s Y (A l) := by
    intro w hw l
    by_cases hl : l = i
    · subst hl
      simpa using hw
    · simpa [hl] using hg l
  obtain ⟨Wi, hWi⟩ := facts.submodules.2.1 (A i)
  have hcomb : α • u + β • v ∈ c1CompactSupp s Y (A i) := by
    have hu' : u ∈ Wi := by
      have : u ∈ (Wi : Set (Y.Carrier s → ℝ)) := by rw [hWi]; exact hu
      exact this
    have hv' : v ∈ Wi := by
      have : v ∈ (Wi : Set (Y.Carrier s → ℝ)) := by rw [hWi]; exact hv
      exact this
    have : α • u + β • v ∈ (Wi : Set (Y.Carrier s → ℝ)) :=
      Wi.add_mem (Wi.smul_mem α hu') (Wi.smul_mem β hv')
    rwa [hWi] at this
  have hvalue : ∀ h ∈ sepTuplesIn s Y q ρ, (centredSum Ψ q).extend h =
      ∑ π ∈ SetPartition.nonSingletonPartitions q,
        ∏ B ∈ π.parts, (Ψ B.card).extend (restrictTuple h B) := by
    intro h hh
    rw [TupleFunctional.extend_of_mem _ hh]
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun B _ => ?_
    rw [TupleFunctional.extend_of_mem _ (restrictTuple_mem hh B)]
  have hblock : ∀ π ∈ SetPartition.nonSingletonPartitions q,
      ∏ B ∈ π.parts, (Ψ B.card).extend (restrictTuple (Function.update g i (α • u + β • v)) B) =
        α * ∏ B ∈ π.parts, (Ψ B.card).extend (restrictTuple (Function.update g i u) B) +
        β * ∏ B ∈ π.parts, (Ψ B.card).extend (restrictTuple (Function.update g i v) B) := by
    intro π hπ
    obtain ⟨B', hB', hiB'⟩ := π.exists_mem (Finset.mem_univ i)
    have hcard : 2 ≤ B'.card := (Finset.mem_filter.1 hπ).2 B' hB'
    have hrange := Finset.range_orderEmbOfFin B' rfl
    obtain ⟨j, hj⟩ : i ∈ Set.range (B'.orderEmbOfFin rfl) := by
      rw [hrange]
      exact hiB'
    have hrest : ∀ w, ∏ B ∈ π.parts.erase B', (Ψ B.card).extend
        (restrictTuple (Function.update g i w) B) =
        ∏ B ∈ π.parts.erase B', (Ψ B.card).extend (restrictTuple g B) := by
      intro w
      refine Finset.prod_congr rfl fun B hB => ?_
      have hi : i ∉ B := fun hiB =>
        (Finset.mem_erase.1 hB).1 (π.eq_of_mem_parts (Finset.mem_erase.1 hB).2 hB' hiB hiB')
      rw [restrictTuple_update_of_notMem g i w hi]
    have hsplit : ∀ w, ∏ B ∈ π.parts, (Ψ B.card).extend
        (restrictTuple (Function.update g i w) B) =
        (Ψ B'.card).extend (Function.update (restrictTuple g B') j w) *
          ∏ B ∈ π.parts.erase B', (Ψ B.card).extend (restrictTuple g B) := by
      intro w
      rw [← Finset.mul_prod_erase π.parts _ hB', hrest w, restrictTuple_update_of_eq g i w j hj]
    have hmulti := hΨ B'.card hcard (fun m => A (B'.orderEmbOfFin rfl m)) (fun m => hA _)
      (fun m m' hmm => hdis _ _ fun e => hmm ((B'.orderEmbOfFin rfl).injective e))
      (restrictTuple g B') (fun m => hg _) j u (by simpa only [hj] using hu) v
      (by simpa only [hj] using hv) α β
    rw [hsplit, hsplit, hsplit, hmulti]
    ring
  rw [hvalue _ (hmemSep _ (hupd _ hcomb)), hvalue _ (hmemSep _ (hupd _ hu)),
    hvalue _ (hmemSep _ (hupd _ hv)), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hblock
theorem claim_holds (hF : SettingFactsHold.statement) (hP : C1PartitionOfUnity.Claim)
    (hC : CutoffAndSymmetry.Assertions) : Claim := by
  intro s Y q ρ _ _
  let M : BlockScale s := ⟨1, 0, by simp⟩
  have facts := hF s M Y
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩
  · have h := respectsTensorRelations facts hP hC Ψ hΨ
    exact ⟨h, existsUnique_isLinearFormOf Ψ h⟩
  · have h := isMultilinearSep_centredSum facts Ψ hΨ (q := q)
    exact ⟨h, existsUnique_isLinearFormOf _ (respectsTensorRelations facts hP hC _ h)⟩
end YangMills.Construction.LatticeLimits.TensorRelations
end
