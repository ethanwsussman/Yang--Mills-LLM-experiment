import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.ValuesOfALinearFunctionOnTensors
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror
open scoped Manifold ContDiff Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TensorValues
theorem supp_eq_tsupport (f : R4 → ℝ) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff (f : R4 → ℝ) :
    f ∈ C1c ℝ ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by
  refine and_congr Iff.rfl ?_
  have h := SeparatedTuplesR4.isCompactWrt_euclid_iff
    (d := Ambient.metric defaultMirrorData Ambient.euclidean) (fun _ _ => rfl) (tsupport f)
  have e := supp_eq_tsupport f
  show MetricNotions.IsCompactWrt _ (supp f) ↔ IsCompact (tsupport f)
  rw [e]
  exact h
theorem disjoint_supp_iff (f g : R4 → ℝ) :
    Disjoint (supp f) (supp g) ↔ Disjoint (tsupport f) (tsupport g) := by
  rw [supp_eq_tsupport, supp_eq_tsupport]
def IsSepFamily {n : ℕ} (f : Fin n → R4 → ℝ) : Prop :=
  (∀ i, ContDiff ℝ 1 (f i) ∧ HasCompactSupport (f i)) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))
theorem ofFn_mem_sepN_iff {n : ℕ} (f : Fin n → R4 → ℝ) :
    List.ofFn f ∈ sepN n ↔ IsSepFamily f := by
  constructor
  · rintro ⟨-, h₁, h₂⟩
    refine ⟨fun i => (mem_C1c_iff _).1 (h₁ _ (List.mem_ofFn.2 ⟨i, rfl⟩)), fun i j hij => ?_⟩
    have h₃ := List.pairwise_ofFn.1 h₂
    rcases lt_or_gt_of_ne hij with h | h
    · exact (disjoint_supp_iff _ _).1 (h₃ h)
    · exact ((disjoint_supp_iff _ _).1 (h₃ h)).symm
  · rintro ⟨h₁, h₂⟩
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact (mem_C1c_iff _).2 (h₁ i)
    · exact List.pairwise_ofFn.2 fun i j hij => (disjoint_supp_iff _ _).2 (h₂ hij.ne)
theorem ofFn_mem_sepAll_iff {n : ℕ} (f : Fin n → R4 → ℝ) :
    List.ofFn f ∈ sepAll ↔ IsSepFamily f := by
  rw [← ofFn_mem_sepN_iff]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
    have hl : m = n := hm.1.symm.trans List.length_ofFn
    exact hl ▸ hm
  · exact fun h => Ambient.separatedN_subset_separatedAll _ _ n h
def evalFamily (σ : sepAll → ℝ) {n : ℕ} (f : Fin n → R4 → ℝ) : ℝ :=
  Ambient.evalOrZero σ (List.ofFn f)
theorem tsupport_subset_of_zero {g h : R4 → ℝ} (H : ∀ x, h x = 0 → g x = 0) :
    tsupport g ⊆ tsupport h :=
  closure_mono fun x hx hz => hx (H x hz)
theorem exists_c1c_ne_disjoint {K : Set R4} (hK : IsCompact K) (h : R4 → ℝ) :
    ∃ c : R4 → ℝ, c ≠ h ∧ ContDiff ℝ 1 c ∧ HasCompactSupport c ∧ Disjoint (tsupport c) K := by
  obtain ⟨p, hp⟩ : ∃ p, p ∉ K := by
    by_contra hall
    exact hK.ne_univ (Set.eq_univ_of_forall fun p => by_contra fun hp => hall ⟨p, hp⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl p hp
  let b : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hb1 : b p = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by
    show 0 ≤ ε / 4
    positivity))
  have hdis : Disjoint (tsupport (b : R4 → ℝ)) K := by
    rw [b.tsupport_eq, Set.disjoint_left]
    intro x hx hxK
    refine hball ?_ hxK
    have hx' : dist x p ≤ ε / 2 := hx
    exact Metric.mem_ball.2 (by linarith)
  by_cases e : h = b
  · refine ⟨0, ?_, contDiff_const, HasCompactSupport.zero, ?_⟩
    · intro h0
      have := congrFun (h0.trans e) p
      simp [hb1] at this
    · have : tsupport (0 : R4 → ℝ) = ∅ := by simp [tsupport]
      rw [this]
      exact Set.empty_disjoint _
  · exact ⟨b, fun h' => e h'.symm, b.contDiff, b.hasCompactSupport, hdis⟩
theorem IsSepFamily.update {n : ℕ} {g : Fin n → R4 → ℝ} (hg : IsSepFamily g) (i : Fin n)
    {c : R4 → ℝ} (h₁ : ContDiff ℝ 1 c) (h₂ : HasCompactSupport c)
    (h₃ : ∀ j, j ≠ i → Disjoint (tsupport c) (tsupport (g j))) :
    IsSepFamily (Function.update g i c) := by
  refine ⟨fun j => ?_, fun j k hjk => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using ⟨h₁, h₂⟩
    · simpa [Function.update_of_ne hj] using hg.1 j
  · by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_of_ne hjk.symm]
      exact h₃ k hjk.symm
    · by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_of_ne hj]
        exact (h₃ j hj).symm
      · show Disjoint _ _
        rw [Function.update_of_ne hj, Function.update_of_ne hk]
        exact hg.2 hjk
theorem evalFamily_update {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ}
    (f : Fin n → R4 → ℝ) (i : Fin n) {h h' : R4 → ℝ}
    (hs : IsSepFamily (Function.update f i h)) (hs' : IsSepFamily (Function.update f i h'))
    (a a' : ℝ) :
    evalFamily σ (Function.update f i (a • h + a' • h')) =
      a * evalFamily σ (Function.update f i h) + a' * evalFamily σ (Function.update f i h') := by
  by_cases e : h' = h
  · subst e
    obtain ⟨c, hc, c₁, c₂, c₃⟩ := exists_c1c_ne_disjoint (K := ⋃ j ∈ Finset.univ.erase i,
      tsupport (Function.update f i h' j))
      ((Finset.univ.erase i).isCompact_biUnion fun j _ => (hs.1 j).2) h'
    have hsc : IsSepFamily (Function.update (Function.update f i h') i c) := by
      refine hs.update i c₁ c₂ fun j hj => ?_
      refine c₃.mono_right ?_
      exact Set.subset_biUnion_of_mem (u := fun j => tsupport (Function.update f i h' j))
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩))
    have key : evalFamily σ (Function.update (Function.update f i h') i
          ((a + a') • Function.update f i h' i + (0 : ℝ) • c)) =
        (a + a') * evalFamily σ (Function.update f i h') +
          0 * evalFamily σ (Function.update (Function.update f i h') i c) :=
      hσ n (Function.update f i h') i c (by simpa using hc)
        ((ofFn_mem_sepAll_iff _).2 hs) ((ofFn_mem_sepAll_iff _).2 hsc) (a + a') 0
    simp only [Function.update_self, Function.update_idem, zero_smul, add_zero, zero_mul] at key
    have e₁ : a • h' + a' • h' = (a + a') • h' := (add_smul a a' h').symm
    rw [e₁, key]
    ring
  · have key : evalFamily σ (Function.update (Function.update f i h) i
          (a • Function.update f i h i + a' • h')) =
        a * evalFamily σ (Function.update f i h) +
          a' * evalFamily σ (Function.update (Function.update f i h) i h') :=
      hσ n (Function.update f i h) i h' (by simpa using e)
        ((ofFn_mem_sepAll_iff _).2 hs)
        ((ofFn_mem_sepAll_iff _).2 (by simpa using hs')) a a'
    simpa only [Function.update_self, Function.update_idem] using key
def supportedIn (A : Set R4) : Submodule ℝ (R4 → ℝ) where
  carrier := {h | ContDiff ℝ 1 h ∧ HasCompactSupport h ∧ tsupport h ⊆ A}
  add_mem' := by
    rintro f g ⟨f₁, f₂, f₃⟩ ⟨g₁, g₂, g₃⟩
    refine ⟨f₁.add g₁, f₂.add g₂, ?_⟩
    refine closure_minimal ?_ ?_ |>.trans (Set.union_subset f₃ g₃)
    · exact (Function.support_add f g).trans
        (Set.union_subset_union (subset_tsupport f) (subset_tsupport g))
    · exact (isClosed_tsupport f).union (isClosed_tsupport g)
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    have : tsupport (0 : R4 → ℝ) = ∅ := by simp [tsupport]
    rw [this]
    exact Set.empty_subset _
  smul_mem' := by
    rintro a f ⟨f₁, f₂, f₃⟩
    have hs : tsupport (a • f) ⊆ tsupport f := tsupport_subset_of_zero fun x hx => by simp [hx]
    exact ⟨contDiff_const.smul f₁, f₂.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans f₃⟩
theorem isSepFamily_of_supportedIn {n : ℕ} {A : Fin n → Set R4}
    (hA : Pairwise fun i j => Disjoint (A i) (A j)) (v : ∀ i, supportedIn (A i)) :
    IsSepFamily fun i => (v i : R4 → ℝ) :=
  ⟨fun i => ⟨(v i).2.1, (v i).2.2.1⟩, fun _ _ hij =>
    (hA hij).mono (v _).2.2.2 (v _).2.2.2⟩
def multilinearOn {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ} {A : Fin n → Set R4}
    (hA : Pairwise fun i j => Disjoint (A i) (A j)) :
    MultilinearMap ℝ (fun i : Fin n => supportedIn (A i)) ℝ where
  toFun v := evalFamily σ fun i => (v i : R4 → ℝ)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have e : ∀ w : supportedIn (A i),
        (fun j => ((Function.update v i w j : supportedIn (A j)) : R4 → ℝ)) =
          Function.update (fun j => (v j : R4 → ℝ)) i (w : R4 → ℝ) := fun w => by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    have hx := isSepFamily_of_supportedIn hA (Function.update v i x)
    have hy := isSepFamily_of_supportedIn hA (Function.update v i y)
    rw [e] at hx hy
    have key := evalFamily_update hσ (fun j => (v j : R4 → ℝ)) i hx hy 1 1
    simp only [one_smul, one_mul] at key
    simp only [e, Submodule.coe_add]
    exact key
  map_update_smul' := by
    intro inst v i a x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    have e : ∀ w : supportedIn (A i),
        (fun j => ((Function.update v i w j : supportedIn (A j)) : R4 → ℝ)) =
          Function.update (fun j => (v j : R4 → ℝ)) i (w : R4 → ℝ) := fun w => by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    have hx := isSepFamily_of_supportedIn hA (Function.update v i x)
    rw [e] at hx
    have key := evalFamily_update hσ (fun j => (v j : R4 → ℝ)) i hx hx a 0
    simp only [zero_smul, add_zero, zero_mul] at key
    simp only [e, Submodule.coe_smul, smul_eq_mul]
    exact key
theorem evalFamily_eq_zero_of_eq_zero {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ}
    {f : Fin n → R4 → ℝ} (hf : IsSepFamily f) (i : Fin n) (h0 : f i = 0) :
    evalFamily σ f = 0 := by
  let v : ∀ k, supportedIn (tsupport (f k)) := fun k => ⟨f k, (hf.1 k).1, (hf.1 k).2, subset_rfl⟩
  exact (multilinearOn hσ (A := fun k => tsupport (f k)) hf.2).map_coord_zero (m := v) i
    (Subtype.ext h0)
theorem evalFamily_eq_sum_partition {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ}
    {J : Type} [Fintype J] [DecidableEq J] {χ : J → R4 → ℝ} (hχ : ∀ j, ContDiff ℝ 1 (χ j))
    {f : Fin n → R4 → ℝ} (hf : IsSepFamily f) (hsum : ∀ i, ∀ x ∈ tsupport (f i), ∑ j, χ j x = 1) :
    evalFamily σ f = ∑ r : Fin n → J, evalFamily σ fun k => χ (r k) * f k := by
  have hmem : ∀ k j, χ j * f k ∈ supportedIn (tsupport (f k)) := fun k j => by
    have hs : tsupport (χ j * f k) ⊆ tsupport (f k) :=
      tsupport_subset_of_zero fun x hx => by simp [hx]
    exact ⟨(hχ j).mul (hf.1 k).1, (hf.1 k).2.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
  let e : ∀ k, J → supportedIn (tsupport (f k)) := fun k j => ⟨χ j * f k, hmem k j⟩
  have hv : ∀ k, ∑ j, (e k j : R4 → ℝ) = f k := fun k => by
    funext x
    simp only [e, Finset.sum_apply, Pi.mul_apply, ← Finset.sum_mul]
    by_cases hx : x ∈ tsupport (f k)
    · rw [hsum k x hx, one_mul]
    · have : f k x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have key := (multilinearOn hσ (A := fun k => tsupport (f k)) hf.2).map_sum
    (α := fun _ => J) e
  have e₁ : (fun k => ((∑ j, e k j : supportedIn (tsupport (f k))) : R4 → ℝ)) = f := by
    funext k
    rw [Submodule.coe_sum]
    exact hv k
  have e₂ : (multilinearOn hσ (A := fun k => tsupport (f k)) hf.2) (fun k => ∑ j, e k j) =
      evalFamily σ f := by
    show evalFamily σ (fun k => ((∑ j, e k j : supportedIn (tsupport (f k))) : R4 → ℝ)) =
      evalFamily σ f
    rw [e₁]
  rw [← e₂, key]
  rfl
theorem exists_linearIndependent_combination {W : Type} [AddCommGroup W] [Module ℝ W] {ι : Type}
    (B : Finset ι) (w : ι → W) :
    ∃ (d : ℕ) (e : Fin d → W) (a : ι → Fin d → ℝ), LinearIndependent ℝ e ∧
      ∀ b ∈ B, w b = ∑ j, a b j • e j := by
  classical
  let U : Submodule ℝ W := Submodule.span ℝ ((B.image w : Finset W) : Set W)
  have : FiniteDimensional ℝ U := FiniteDimensional.span_finset ℝ _
  let bas := Module.finBasis ℝ U
  have hm : ∀ b ∈ B, w b ∈ U := fun b hb =>
    Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
  refine ⟨_, fun j => (bas j : W),
    fun b => if hb : b ∈ B then bas.repr ⟨w b, hm b hb⟩ else 0, ?_, fun b hb => ?_⟩
  · exact bas.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have := congrArg Subtype.val (bas.sum_repr ⟨w b, hm b hb⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, dif_pos hb] using this.symm
theorem sum_mul_eq_zero_of_sum_prod {X : Type} : ∀ (n : ℕ) (V : Fin n → Submodule ℝ (X → ℝ))
    (m : MultilinearMap ℝ (fun k => V k) ℝ) {ι : Type} (B : Finset ι) (r : ι → ℝ)
    (g : ι → ∀ k, V k),
    (∀ x : Fin n → X, ∑ b ∈ B, r b * ∏ k, (g b k : X → ℝ) (x k) = 0) →
      ∑ b ∈ B, r b * m (g b) = 0 := by
  intro n
  induction n with
  | zero =>
    intro V m ι B r g h
    have h₀ := h (fun k => k.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h₀
    have e : ∀ b, m (g b) = m (fun k => k.elim0) := fun b => congrArg m (funext fun k => k.elim0)
    simp only [e, ← Finset.sum_mul, h₀, zero_mul]
  | succ n ih =>
    intro V m ι B r g h
    classical
    obtain ⟨d, e, a, he, ha⟩ := exists_linearIndependent_combination B fun b => g b 0
    let u : Fin d → X → ℝ := fun j => ((e j : V 0) : X → ℝ)
    have hli : LinearIndependent ℝ u := he.map' (V 0).subtype (Submodule.ker_subtype _)
    have hj : ∀ j, ∑ b ∈ B, (r b * a b j) * m.curryLeft (e j) (fun k => g b k.succ) = 0 := by
      intro j
      refine ih (fun k => V k.succ) (m.curryLeft (e j)) B (fun b => r b * a b j)
        (fun b k => g b k.succ) fun x' => ?_
      let c : Fin d → ℝ := fun j =>
        ∑ b ∈ B, (r b * a b j) * ∏ k, (g b k.succ : X → ℝ) (x' k)
      have hz : ∑ j, c j • u j = 0 := by
        funext x₀
        have h₁ := h (Fin.cons x₀ x')
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at h₁
        have hb : ∀ b ∈ B, (g b 0 : X → ℝ) x₀ = ∑ j, a b j * u j x₀ := fun b hb => by
          rw [ha b hb]
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, u]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, c, Finset.sum_mul]
        rw [Finset.sum_comm, ← h₁]
        refine Finset.sum_congr rfl fun b hbB => ?_
        rw [hb b hbB, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      exact Fintype.linearIndependent_iff.1 hli c hz j
    have hm : ∀ b ∈ B, m (g b) = ∑ j, a b j * m.curryLeft (e j) (fun k => g b k.succ) := by
      intro b hb
      have e₁ : m (g b) = m.curryLeft (g b 0) (fun k => g b k.succ) := by
        rw [MultilinearMap.curryLeft_apply]
        exact congrArg m (Fin.cons_self_tail (g b)).symm
      rw [e₁, ha b hb]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    calc ∑ b ∈ B, r b * m (g b)
        = ∑ b ∈ B, ∑ j, (r b * a b j) * m.curryLeft (e j) (fun k => g b k.succ) :=
          Finset.sum_congr rfl fun b hb => by
            rw [hm b hb, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ b ∈ B, (r b * a b j) * m.curryLeft (e j) (fun k => g b k.succ) :=
          Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun j _ => hj j
theorem sum_mul_eq_zero_of_sum_prod_complex {X : Type} {n : ℕ} (V : Fin n → Submodule ℝ (X → ℝ))
    (m : MultilinearMap ℝ (fun k => V k) ℝ) {ι : Type} (B : Finset ι) (z : ι → ℂ)
    (g : ι → ∀ k, V k)
    (h : ∀ x : Fin n → X, ∑ b ∈ B, z b * ((∏ k, (g b k : X → ℝ) (x k) : ℝ) : ℂ) = 0) :
    ∑ b ∈ B, z b * ((m (g b) : ℝ) : ℂ) = 0 := by
  have hre := sum_mul_eq_zero_of_sum_prod n V m B (fun b => (z b).re) g fun x => by
    have := congrArg Complex.re (h x)
    simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re] using this
  have him := sum_mul_eq_zero_of_sum_prod n V m B (fun b => (z b).im) g fun x => by
    have := congrArg Complex.im (h x)
    simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im] using this
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re] using hre
  · simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im] using him
theorem exists_smallSupport_partition {K : Set R4} (hK : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (t : Finset R4) (χ : t → R4 → ℝ), (∀ j, ContDiff ℝ 1 (χ j)) ∧
      (∀ j x, χ j x ≠ 0 → dist x (j : R4) < ρ) ∧ ∀ x ∈ K, ∑ j, χ j x = 1 := by
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x ρ)
    fun x _ => Metric.ball_mem_nhds x hρ
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, R4) hK.isClosed
    (fun j : t => Metric.ball (j : R4) ρ) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩)
  refine ⟨t, fun j => f j, fun j => ?_, fun j x hx => ?_, fun x hx => ?_⟩
  · exact (f j).contMDiff.contDiff.of_le (by exact_mod_cast le_top)
  · exact hf j (subset_tsupport _ hx)
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx
theorem exists_pos_sep_dist {n : ℕ} {ι : Type} (B : Finset ι) (f : ι → Fin n → R4 → ℝ)
    (hf : ∀ b, IsSepFamily (f b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ B, ∀ i k, i ≠ k → ∀ x ∈ tsupport (f b i), ∀ y ∈ tsupport (f b k),
      δ ≤ dist x y := by
  have h : ∀ b ∈ B, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i k, i ≠ k → ∀ x ∈ tsupport (f b i),
      ∀ y ∈ tsupport (f b k), δ ≤ dist x y := by
    intro b _
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => ?_
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun δ h => absurd hik h
    · obtain ⟨r, hr, H⟩ := Metric.exists_pos_forall_lt_edist ((hf b).1 i).2
        (isClosed_tsupport _) ((hf b).2 hik)
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < r from hr)] with δ hδ _ x hx y hy
      have h₁ := H x hx y hy
      rw [edist_nndist, ENNReal.coe_lt_coe] at h₁
      have h₂ : (r : ℝ) < dist x y := by exact_mod_cast h₁
      exact hδ.2.trans h₂.le
  obtain ⟨δ, hδ, hδ'⟩ := (((Filter.eventually_all_finset B).2 h).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ', hδ⟩
theorem IsSepFamily.mul_left {n : ℕ} {f : Fin n → R4 → ℝ} (hf : IsSepFamily f)
    {c : Fin n → R4 → ℝ} (hc : ∀ k, ContDiff ℝ 1 (c k)) : IsSepFamily fun k => c k * f k := by
  have hs : ∀ k, tsupport (c k * f k) ⊆ tsupport (f k) := fun k =>
    tsupport_subset_of_zero fun x hx => by simp [hx]
  exact ⟨fun k => ⟨(hc k).mul (hf.1 k).1,
    (hf.1 k).2.of_isClosed_subset (isClosed_tsupport _) (hs k)⟩, fun i j hij =>
      (hf.2 hij).mono (hs i) (hs j)⟩
theorem sum_evalFamily_eq_zero {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ} {ι : Type}
    (B : Finset ι) (z : ι → ℂ) (f : ι → Fin n → R4 → ℝ) (hf : ∀ b, IsSepFamily (f b))
    (hT : ∀ x : Fin n → R4, ∑ b ∈ B, z b * ((∏ k, f b k (x k) : ℝ) : ℂ) = 0) :
    ∑ b ∈ B, z b * ((evalFamily σ (f b) : ℝ) : ℂ) = 0 := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_sep_dist B f hf
  have hK : IsCompact (⋃ b ∈ B, ⋃ i, tsupport (f b i)) :=
    B.isCompact_biUnion fun b _ => isCompact_iUnion fun i => ((hf b).1 i).2
  obtain ⟨t, χ, hχ, hsmall, hsum⟩ := exists_smallSupport_partition hK (ρ := δ / 8) (by positivity)
  have hexp : ∀ b ∈ B, evalFamily σ (f b) =
      ∑ r : Fin n → t, evalFamily σ fun k => χ (r k) * f b k :=
    fun b hb => evalFamily_eq_sum_partition hσ hχ (hf b) fun i x hx =>
      hsum x (Set.mem_biUnion hb (Set.mem_iUnion.2 ⟨i, hx⟩))
  have hinner : ∀ r : Fin n → t,
      ∑ b ∈ B, z b * ((evalFamily σ (fun k => χ (r k) * f b k) : ℝ) : ℂ) = 0 := by
    intro r
    by_cases hd : Pairwise fun i k => Disjoint (Metric.closedBall (r i : R4) (δ / 8))
        (Metric.closedBall (r k : R4) (δ / 8))
    · have hmem : ∀ b k, χ (r k) * f b k ∈ supportedIn (Metric.closedBall (r k : R4) (δ / 8)) := by
        intro b k
        have hs : tsupport (χ (r k) * f b k) ⊆ tsupport (f b k) :=
          tsupport_subset_of_zero fun x hx => by simp [hx]
        refine ⟨(hχ _).mul ((hf b).1 k).1,
          ((hf b).1 k).2.of_isClosed_subset (isClosed_tsupport _) hs,
          closure_minimal ?_ Metric.isClosed_closedBall⟩
        intro x hx
        have hx' : χ (r k) x * f b k x ≠ 0 := hx
        exact (hsmall _ _ (left_ne_zero_of_mul hx')).le
      refine sum_mul_eq_zero_of_sum_prod_complex
        (fun k => supportedIn (Metric.closedBall (r k : R4) (δ / 8))) (multilinearOn hσ hd) B z
        (fun b k => ⟨_, hmem b k⟩) fun x => ?_
      have e : ∀ b, ((∏ k, (χ (r k) * f b k) (x k) : ℝ) : ℂ) =
          ((∏ k, χ (r k) (x k) : ℝ) : ℂ) * ((∏ k, f b k (x k) : ℝ) : ℂ) := fun b => by
        rw [← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
        rfl
      calc ∑ b ∈ B, z b * ((∏ k, (χ (r k) * f b k) (x k) : ℝ) : ℂ)
          = ((∏ k, χ (r k) (x k) : ℝ) : ℂ) * ∑ b ∈ B, z b * ((∏ k, f b k (x k) : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by rw [e b]; ring
        _ = 0 := by rw [hT x, mul_zero]
    · simp only [Pairwise, not_forall] at hd
      obtain ⟨i, k, hik, hnd⟩ := hd
      obtain ⟨w, hw₁, hw₂⟩ := Set.not_disjoint_iff.1 hnd
      refine Finset.sum_eq_zero fun b hb => ?_
      have hs : IsSepFamily fun k' => χ (r k') * f b k' := (hf b).mul_left fun k' => hχ _
      have hz : χ (r i) * f b i = 0 ∨ χ (r k) * f b k = 0 := by
        by_contra hcon
        rw [not_or] at hcon
        obtain ⟨x, hx⟩ := Function.ne_iff.1 hcon.1
        obtain ⟨y, hy⟩ := Function.ne_iff.1 hcon.2
        have hx' : χ (r i) x * f b i x ≠ 0 := hx
        have hy' : χ (r k) y * f b k y ≠ 0 := hy
        have h₀ := hsep b hb i k hik x (subset_tsupport _ (right_ne_zero_of_mul hx'))
          y (subset_tsupport _ (right_ne_zero_of_mul hy'))
        have d₁ := hsmall _ _ (left_ne_zero_of_mul hx')
        have d₂ := hsmall _ _ (left_ne_zero_of_mul hy')
        have d₃ : dist w (r i : R4) ≤ δ / 8 := hw₁
        have d₄ : dist w (r k : R4) ≤ δ / 8 := hw₂
        have t₁ := dist_triangle x (r i : R4) w
        have t₂ := dist_triangle x w y
        have t₃ := dist_triangle w (r k : R4) y
        rw [dist_comm (r i : R4) w] at t₁
        rw [dist_comm (r k : R4) y] at t₃
        linarith
      rcases hz with h | h
      · rw [evalFamily_eq_zero_of_eq_zero hσ hs i h]
        simp
      · rw [evalFamily_eq_zero_of_eq_zero hσ hs k h]
        simp
  calc ∑ b ∈ B, z b * ((evalFamily σ (f b) : ℝ) : ℂ)
      = ∑ b ∈ B, ∑ r : Fin n → t, z b * ((evalFamily σ (fun k => χ (r k) * f b k) : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun b hb => by
          rw [hexp b hb, Complex.ofReal_sum, Finset.mul_sum]
    _ = ∑ r : Fin n → t, ∑ b ∈ B, z b * ((evalFamily σ (fun k => χ (r k) * f b k) : ℝ) : ℂ) :=
        Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun r _ => hinner r
theorem ofFn_get_cast_eq {α : Type*} (X : List α) {n : ℕ} (h : X.length = n) :
    List.ofFn (fun i : Fin n => X.get (Fin.cast h.symm i)) = X := by
  subst h
  exact List.ofFn_get X
theorem evalOrZero_of_mem (σ : sepAll → ℝ) (X : sepAll) : Ambient.evalOrZero σ X.1 = σ X :=
  dif_pos X.2
theorem sum_eq_zero_of_sum_tensor {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) (n : ℕ)
    (B : Finset sepAll) (z : sepAll → ℂ) (hB : ∀ X ∈ B, X.1.length = n)
    (hT : ∑ X ∈ B, z X • tensorAt n X = 0) : ∑ X ∈ B, z X * ((σ X : ℝ) : ℂ) = 0 := by
  have hl : ∀ X : {X // X ∈ B}, X.1.1.length = n := fun X => hB _ X.2
  let f : {X // X ∈ B} → Fin n → R4 → ℝ := fun X i => X.1.1.get (Fin.cast (hl X).symm i)
  have hfe : ∀ X, List.ofFn (f X) = X.1.1 := fun X => ofFn_get_cast_eq _ (hl X)
  have hf : ∀ X, IsSepFamily (f X) := fun X =>
    (ofFn_mem_sepAll_iff _).1 ((hfe X).symm ▸ X.1.2)
  have key := sum_evalFamily_eq_zero hσ B.attach (fun X => z X.1) f hf fun x => by
    have h₁ := congrFun hT x
    rw [← Finset.sum_attach] at h₁
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun X _ => ?_) h₁
    rw [tensorAt_of_length _ (hl X), tensorOfFns_apply, Complex.ofReal_prod]
    rfl
  rw [← Finset.sum_attach]
  refine Eq.trans (Finset.sum_congr rfl fun X _ => ?_) key
  have e : evalFamily σ (f X) = σ X.1 :=
    (congrArg (Ambient.evalOrZero σ) (hfe X)).trans (evalOrZero_of_mem σ X.1)
  rw [e]
theorem liftReal_apply (σ : sepAll → ℝ) (G : FreeSep) :
    liftReal σ G = ∑ X ∈ G.support, G X * ((σ X : ℝ) : ℂ) := by
  simp [liftReal, liftLin, Finsupp.linearCombination_apply, Finsupp.sum]
theorem tensorComp_apply (n : ℕ) (G : FreeSep) :
    tensorComp n G = ∑ X ∈ G.support, G X • tensorAt n X := by
  simp [tensorComp, liftLin, Finsupp.linearCombination_apply, Finsupp.sum]
theorem length_of_mem_combSpan {n : ℕ} {G : FreeSep} (hG : G ∈ combSpan n) :
    ∀ X ∈ G.support, X.1.length = n := by
  have h : combSpan n ≤ Finsupp.supported ℂ ℂ {X : sepAll | X.1.length = n} := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    have hm : X ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ n hX
    show toFree X ∈ Finsupp.supported ℂ ℂ {X : sepAll | X.1.length = n}
    rw [toFree_of_mem hm]
    exact Finsupp.single_mem_supported ℂ 1 hX.1
  exact fun X hX => (Finsupp.mem_supported ℂ G).1 (h hG) hX
theorem liftReal_eq_of_tensorComp_eq {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) {n : ℕ}
    {F F' : FreeSep} (hF : F ∈ combSpan n) (hF' : F' ∈ combSpan n)
    (hT : tensorComp n F = tensorComp n F') : liftReal σ F = liftReal σ F' := by
  have hG : tensorComp n (F - F') = 0 := by rw [map_sub, hT, sub_self]
  rw [tensorComp_apply] at hG
  have h := sum_eq_zero_of_sum_tensor hσ n (F - F').support ⇑(F - F')
    (length_of_mem_combSpan (sub_mem hF hF')) hG
  rw [← liftReal_apply, map_sub] at h
  exact sub_eq_zero.1 h
def freeComb {n : ℕ} {ι : Type} (B : Finset ι) (z : ι → ℂ) (f : ι → Fin n → R4 → ℝ) :
    FreeSep :=
  ∑ b ∈ B, z b • toFree (List.ofFn (f b))
theorem freeComb_mem {n : ℕ} {ι : Type} {B : Finset ι} (z : ι → ℂ)
    {f : ι → Fin n → R4 → ℝ} (hf : ∀ b ∈ B, List.ofFn (f b) ∈ sepN n) :
    freeComb B z f ∈ combSpan n :=
  Submodule.sum_mem _ fun b hb =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hf b hb, rfl⟩)
theorem tensorComp_toFree_ofFn {n : ℕ} {f : Fin n → R4 → ℝ}
    (h : List.ofFn f ∈ sepN n) :
    tensorComp n (toFree (List.ofFn f)) = realTensor f := by
  have hm : List.ofFn f ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ n h
  refine (liftLin_toFree (tensorAt n) ⟨_, hm⟩).trans ?_
  refine (tensorAt_of_length _ h.1).trans ?_
  funext x
  rw [tensorOfFns_apply, realTensor, tensorOfFns_apply]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [cplxEntries]
theorem tensorComp_freeComb {n : ℕ} {ι : Type} {B : Finset ι} (z : ι → ℂ)
    {f : ι → Fin n → R4 → ℝ} (hf : ∀ b ∈ B, List.ofFn (f b) ∈ sepN n) :
    tensorComp n (freeComb B z f) = combTensor B z f := by
  simp only [freeComb, combTensor, map_sum, map_smul]
  exact Finset.sum_congr rfl fun b hb => by rw [tensorComp_toFree_ofFn (hf b hb)]
theorem liftReal_freeComb (σ : sepAll → ℝ) {n : ℕ} {ι : Type} {B : Finset ι} (z : ι → ℂ)
    {f : ι → Fin n → R4 → ℝ} (hf : ∀ b ∈ B, List.ofFn (f b) ∈ sepN n) :
    liftReal σ (freeComb B z f) = combValue σ B z f := by
  simp only [freeComb, combValue, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hm : List.ofFn (f b) ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ n (hf b hb)
  have e₁ := liftLin_toFree (fun X : sepAll => ((σ X : ℝ) : ℂ)) ⟨_, hm⟩
  have e₂ := evalOrZero_of_mem σ ⟨_, hm⟩
  congr 1
  exact e₁.trans (congrArg _ e₂.symm)
theorem map_combSpan (n : ℕ) :
    (combSpan n).map (tensorComp n) = tupleTensorSpan n := by
  rw [combSpan, Submodule.map_span, tupleTensorSpan]
  congr 1
  ext T
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    have hfe := ofFn_get_cast_eq X hX.1
    have hmem : List.ofFn (fun i : Fin n => X.get (Fin.cast hX.1.symm i)) ∈ sepN n :=
      hfe.symm ▸ hX
    refine ⟨_, hmem, ?_⟩
    have e := tensorComp_toFree_ofFn hmem
    rw [hfe] at e
    exact e
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨_, hf, rfl⟩, tensorComp_toFree_ofFn hf⟩
theorem agreesOnSameTensors {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) :
    AgreesOnSameTensors σ := by
  classical
  intro F F' h
  have h' := (sameTensors_iff F F').1 h
  have hG : ∀ n, tensorComp n (F - F') = 0 := fun n => by rw [map_sub, h' n, sub_self]
  have key : liftReal σ (F - F') = 0 := by
    rw [liftReal_apply, ← Finset.sum_fiberwise_of_maps_to (g := fun X : sepAll => X.1.length)
      (t := (F - F').support.image fun X : sepAll => X.1.length)
      (fun X hX => Finset.mem_image_of_mem _ hX)]
    refine Finset.sum_eq_zero fun n _ => sum_eq_zero_of_sum_tensor hσ n _ ⇑(F - F')
      (fun X hX => (Finset.mem_filter.1 hX).2) ?_
    rw [Finset.sum_filter_of_ne fun X _ hne => ?_, ← tensorComp_apply, hG]
    by_contra hl
    exact hne (by rw [tensorAt_of_length_ne X hl, smul_zero])
  rw [map_sub] at key
  exact sub_eq_zero.1 key
theorem isLinearOnSpan {σ : sepAll → ℝ} (hσ : IsEntrywiseLinear σ) :
    IsLinearOnSpan σ := by
  intro n _
  have hmap := map_combSpan n
  let T' : combSpan n →ₗ[ℂ] tupleTensorSpan n :=
    ((tensorComp n).comp (combSpan n).subtype).codRestrict _ fun F => by
      rw [← hmap]
      exact ⟨F.1, F.2, rfl⟩
  have hsurj : LinearMap.range T' = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨t, ht⟩
    rw [← hmap] at ht
    obtain ⟨F, hF, rfl⟩ := ht
    exact ⟨⟨F, hF⟩, rfl⟩
  obtain ⟨g, hg⟩ := T'.exists_rightInverse_of_surjective hsurj
  refine ⟨(liftReal σ).comp ((combSpan n).subtype.comp g), fun {ι} B z f hf => ?_⟩
  have h₁ : tensorComp n (g ⟨_, combTensor_mem_sepTensorSpan z hf⟩ : FreeSep) =
      combTensor B z f :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨_, combTensor_mem_sepTensorSpan z hf⟩)
  show liftReal σ (g ⟨_, combTensor_mem_sepTensorSpan z hf⟩ : FreeSep) = _
  rw [← liftReal_freeComb σ z hf]
  exact liftReal_eq_of_tensorComp_eq hσ (g _).2 (freeComb_mem z hf)
    (h₁.trans (tensorComp_freeComb z hf).symm)
theorem entrywiseLinearValues : EntrywiseLinearValues := by
  intro σ hσ
  refine ⟨?_, ?_, ?_, isLinearOnSpan hσ, agreesOnSameTensors hσ⟩
  · intro n _ ι B z f hf hT
    have h := liftReal_eq_of_tensorComp_eq hσ (freeComb_mem z hf) (zero_mem _)
      (by rw [tensorComp_freeComb z hf, hT, map_zero])
    rwa [liftReal_freeComb σ z hf, map_zero] at h
  · intro n _ ι ι' B B' z z' f f' hf hf' hT
    have h := liftReal_eq_of_tensorComp_eq hσ (freeComb_mem z hf) (freeComb_mem z' hf')
      (by rw [tensorComp_freeComb z hf, tensorComp_freeComb z' hf', hT])
    rwa [liftReal_freeComb σ z hf, liftReal_freeComb σ z' hf'] at h
  · exact fun n _ F hF F' hF' hT => liftReal_eq_of_tensorComp_eq hσ hF hF' hT
end YangMills.Construction.EuclideanFunctionals.TensorValues
