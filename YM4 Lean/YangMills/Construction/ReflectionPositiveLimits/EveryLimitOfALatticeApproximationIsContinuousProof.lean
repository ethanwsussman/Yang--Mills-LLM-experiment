import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.Continuum.FunctionsOfClassC1SupportedInACompactSetFormABanachSpace
import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.NormedSpaces.MultilinearSequenceUniformBound
import YangMills.Construction.ReflectionPositiveLimits.EveryLimitOfALatticeApproximationIsContinuous
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory TopologicalSpace Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContinuityProof
open YangMills.Construction.TestFunctions
open YangMills.Construction.InfiniteLattice (ElementaryPlaquette faceEnergy)
theorem c1NormR4_nonneg (f : ScalarField) : 0 ≤ c1NormR4 f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
theorem abs_le_c1NormR4 {f : ScalarField} (hf : Continuous f) (hsupp : HasCompactSupport f)
    (x : Space) : |f x| ≤ c1NormR4 f := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf
  have hbdd : BddAbove (Set.range fun x => ‖f x‖) := ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩
  rw [← Real.norm_eq_abs]
  exact (le_ciSup hbdd x).trans (le_max_left _ _)
def C1Space (K : Compacts Space) : Type := c1Supported K
instance (K : Compacts Space) : AddCommGroup (C1Space K) :=
  inferInstanceAs (AddCommGroup (c1Supported K))
instance (K : Compacts Space) : Module ℝ (C1Space K) :=
  inferInstanceAs (Module ℝ (c1Supported K))
instance (K : Compacts Space) : Norm (C1Space K) :=
  inferInstanceAs (Norm (c1Supported K))
namespace C1Space
variable {K : Compacts Space}
def ofSupported (u : c1Supported K) : C1Space K := u
def toSupported (u : C1Space K) : c1Supported K := u
def fn (u : C1Space K) : ScalarField := u.toSupported.1
theorem contDiff (u : C1Space K) : ContDiff ℝ 1 u.fn := u.toSupported.2.1
theorem tsupport_subset (u : C1Space K) : tsupport u.fn ⊆ K := u.toSupported.2.2
theorem hasCompactSupport (u : C1Space K) : HasCompactSupport u.fn :=
  K.isCompact.of_isClosed_subset (isClosed_tsupport _) u.tsupport_subset
theorem fn_add (u w : C1Space K) :
    (u + w).fn = (1 : ℝ) • u.fn + (1 : ℝ) • w.fn := by
  rw [one_smul, one_smul]
  rfl
theorem fn_smul (a : ℝ) (u : C1Space K) :
    (a • u).fn = a • u.fn + (0 : ℝ) • u.fn := by
  rw [zero_smul, add_zero]
  rfl
end C1Space
section Tuples
variable {k : ℕ} {K : Fin k → Compacts Space}
theorem ofFn_mem_separatedSet (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i'))
    (u : ∀ i, C1Space (K i)) : List.ofFn (fun i => (u i).fn) ∈ separatedSet := by
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact ⟨(u i).contDiff, (u i).hasCompactSupport, Set.subset_univ _⟩
  · rw [List.pairwise_ofFn]
    intro i i' hii
    exact (hK i i' hii.ne).mono (u i).tsupport_subset (u i').tsupport_subset
def tupleOfSections (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i'))
    (u : ∀ i, C1Space (K i)) : Tuple :=
  ⟨List.ofFn fun i => (u i).fn, ofFn_mem_separatedSet hK u⟩
theorem exists_tupleOfSections (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i'))
    (T : Tuple) (hk : T.len = k) (hs : ∀ i : Fin k, tsupport (componentAt T i) ⊆ K i) :
    ∃ u : ∀ i, C1Space (K i), tupleOfSections hK u = T ∧ ∀ i, (u i).fn = componentAt T i := by
  have hlen : T.1.length = k := hk
  have hget : ∀ i : Fin k, componentAt T i = T.1[(i : ℕ)]'(hlen ▸ i.2) := fun i => by
    rw [componentAt, List.getD_eq_getElem _ _ (hlen ▸ i.2)]
  have hreg : ∀ i : Fin k, IsC1R4 (componentAt T i) := fun i =>
    (T.2.1 _ (by rw [hget]; exact List.getElem_mem _)).1
  refine ⟨fun i => C1Space.ofSupported ⟨componentAt T i, mem_c1Supported.2 ⟨hreg i, hs i⟩⟩,
    Subtype.ext ?_, fun i => rfl⟩
  refine List.ext_getElem (by simp [tupleOfSections, hlen]) fun n h₁ h₂ => ?_
  have hn : n < k := by simpa [tupleOfSections] using h₁
  simp only [tupleOfSections, List.getElem_ofFn]
  exact hget ⟨n, hn⟩
theorem ofFn_eq_take_append_cons_drop_of_agree {α : Type*} (g g' : Fin k → α) (i : Fin k)
    (h : ∀ l, l ≠ i → g l = g' l) :
    List.ofFn g = (List.ofFn g').take i ++ g i :: (List.ofFn g').drop (i + 1) := by
  have ht : (List.ofFn g).take i = (List.ofFn g').take i := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    have hn : n < i := by simp at h₁; omega
    simp only [List.getElem_take, List.getElem_ofFn]
    exact h _ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hd : (List.ofFn g).drop (i + 1) = (List.ofFn g').drop (i + 1) := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact h _ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hi : (i : ℕ) < (List.ofFn g).length := by simp
  calc List.ofFn g = (List.ofFn g).take i ++ (List.ofFn g).drop i :=
        (List.take_append_drop _ _).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hi, ht, hd, List.getElem_ofFn]
end Tuples
section Forms
variable {L : ℕ} (A : LatticeSequence L) (j : ℕ+) {k : ℕ} {K : Fin k → Compacts Space}
theorem mean_update [DecidableEq (Fin k)] (hlin : IsSlotLinear (A.mean j))
    (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i'))
    (m : ∀ i, C1Space (K i)) (i : Fin k) (v x y : C1Space (K i)) (α α' : ℝ)
    (hv : v.fn = α • x.fn + α' • y.fn) :
    A.mean j (tupleOfSections hK (Function.update m i v)) =
      α * A.mean j (tupleOfSections hK (Function.update m i x)) +
        α' * A.mean j (tupleOfSections hK (Function.update m i y)) := by
  set front := (List.ofFn fun l => (m l).fn).take i with hfront
  set back := (List.ofFn fun l => (m l).fn).drop (i + 1) with hback
  have hl : ∀ u : C1Space (K i),
      (tupleOfSections hK (Function.update m i u)).1 = front ++ u.fn :: back := fun u => by
    have h := ofFn_eq_take_append_cons_drop_of_agree
      (fun l => (Function.update m i u l).fn)
      (fun l => (m l).fn) i fun l hli => by rw [Function.update_of_ne hli]
    simpa [tupleOfSections] using h
  have hmem : ∀ u : C1Space (K i), front ++ u.fn :: back ∈ separatedSet := fun u =>
    hl u ▸ (tupleOfSections hK (Function.update m i u)).2
  have heq : ∀ u : C1Space (K i),
      tupleOfSections hK (Function.update m i u) = ⟨_, hmem u⟩ := fun u => Subtype.ext (hl u)
  have key := hlin front back _ _ α α' (hmem x) (hmem y)
  rw [heq x, heq y, ← key]
  exact congrArg _ (Subtype.ext ((hl v).trans (by rw [hv])))
def meanForm (hlin : IsSlotLinear (A.mean j))
    (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i')) :
    MultilinearMap ℝ (fun i => C1Space (K i)) ℝ where
  toFun u := A.mean j (tupleOfSections hK u)
  map_update_add' := by
    intro _ m i x y
    rw [mean_update A j hlin hK m i (x + y) x y 1 1 (C1Space.fn_add x y)]
    simp
  map_update_smul' := by
    intro _ m i a x
    rw [mean_update A j hlin hK m i (a • x) x x a 0 (C1Space.fn_smul a x)]
    simp
theorem meanForm_apply (hlin : IsSlotLinear (A.mean j))
    (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i')) (u : ∀ i, C1Space (K i)) :
    meanForm A j hlin hK u = A.mean j (tupleOfSections hK u) := rfl
theorem exists_smeared_bound (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hodd : Odd L) (h13 : 13 ≤ L) {S : Set Space} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : ScalarField, Continuous f → tsupport f ⊆ S →
      ∀ U, |A.smeared j f U| ≤ B * c1NormR4 f := by
  let s : Conventions.StandingParameters := ⟨L, ⟨hodd, h13⟩, A.level j, 1⟩
  obtain ⟨⟨-, hen⟩, hfin⟩ := hP s (A.measure j).1 (A.measure j).2
  have hF := hfin S hS.isBounded
  refine ⟨(hF.toFinset.card : ℝ) * (2 + |A.shift j|), by positivity, fun f hf hsupp U => ?_⟩
  have hcs : HasCompactSupport f := hS.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hsub : Function.support (fun p : ElementaryPlaquette
      (PeriodicLattice.meshSize L ((A.level j : ℕ) : ℤ)) =>
      f p.center * (faceEnergy U p - A.shift j)) ⊆ ↑hF.toFinset := by
    intro p hp
    have hne : f p.center ≠ 0 := fun h0 => hp (by simp [h0])
    exact Finset.mem_coe.2 (hF.mem_toFinset.2 (hsupp (subset_tsupport f hne)))
  have hsum : A.smeared j f U = ∑ p ∈ hF.toFinset,
      f p.center * (faceEnergy U p - A.shift j) :=
    finsum_eq_sum_of_support_subset _ hsub
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ hF.toFinset,
      |f p.center * (faceEnergy U p - A.shift j)| ≤
        c1NormR4 f * (2 + |A.shift j|) := by
    intro p _
    rw [abs_mul]
    have h₁ := abs_le_c1NormR4 hf hcs p.center
    have h₂ := (hen p).2 U
    have h₃ : |faceEnergy U p - A.shift j| ≤ 2 + |A.shift j| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h₂.1]
      linarith [h₂.2]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) (c1NormR4_nonneg f)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)
theorem rep_tupleOfSections (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i'))
    (u : ∀ i, C1Space (K i)) (U : A.Fields j) :
    A.rep j (tupleOfSections hK u) U = ∏ i, A.smeared j (u i).fn U := by
  simp [LatticeSequence.rep, tupleOfSections, List.map_ofFn, List.prod_ofFn,
    Finset.prod_apply]
theorem exists_meanForm_bound (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hodd : Odd L) (h13 : 13 ≤ L)
    (hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i')) :
    ∃ c : ℝ, ∀ u : ∀ i, C1Space (K i),
      |A.mean j (tupleOfSections hK u)| ≤ c * ∏ i, ‖u i‖ := by
  choose B hB0 hB using fun i => exists_smeared_bound A j hP hodd h13 (K i).isCompact
  refine ⟨∏ i, B i, fun u => ?_⟩
  have hpt : ∀ U, ‖A.rep j (tupleOfSections hK u) U‖ ≤ (∏ i, B i) * ∏ i, ‖u i‖ := fun U => by
    rw [rep_tupleOfSections, Real.norm_eq_abs, Finset.abs_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ =>
      hB i _ (u i).contDiff.continuous (u i).tsupport_subset U
  have : IsProbabilityMeasure (A.measure j).1 := (A.measure j).2
  have h₁ := norm_integral_le_of_norm_le_const (μ := (A.measure j).1) (ae_of_all _ hpt)
  simpa [LatticeSequence.mean] using h₁
end Forms
theorem bddAbove_range_abs_of_tendsto_pnat {s : ℕ+ → ℝ} {l : ℝ} (h : Tendsto s atTop (𝓝 l)) :
    BddAbove (Set.range fun n => |s n|) := by
  have hsucc : Tendsto Nat.succPNat atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by
      rw [← PNat.coe_le_coe, Nat.succPNat_coe]
      omega⟩
  obtain ⟨M, hM⟩ := (h.comp hsucc).abs.bddAbove_range
  refine ⟨M, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hM ⟨n.natPred, by simp⟩
theorem c1NormR4_le_add_sub (hC : C1Banach.BanachAndComparable) {K : Compacts Space}
    (x y : C1Space K) : c1NormR4 x.fn ≤ c1NormR4 y.fn + c1NormR4 (x.fn - y.fn) := by
  have h := (hC K).1.2.1.norm_triangle y.toSupported (x.toSupported - y.toSupported)
  rw [add_sub_cancel] at h
  exact h
section Constant
variable {L : ℕ}
theorem exists_multilinear_constant (hR : TupleRepresentatives.Statement)
    (hU : NormedSpaces.MultilinearSequenceUniformBound)
    (hC : C1Banach.BanachAndComparable)
    (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hodd : Odd L) (h13 : 13 ≤ L) (A : LatticeSequence L) (σ : Tuple → ℝ)
    (hσ : A.HasLimit σ) {k : ℕ} (hk : 0 < k) (S : Fin k → Set Space)
    (hS : ∀ i, IsCompact (S i)) (hd : ∀ i i', i ≠ i' → Disjoint (S i) (S i')) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T T' : Tuple, T.len = k → T'.len = k →
      (∀ i : Fin k, tsupport (componentAt T i) ∪ tsupport (componentAt T' i) ⊆ S i) →
      (∀ j, |A.mean j T| ≤ C * ∏ i : Fin k, c1NormR4 (componentAt T i)) ∧
        |σ T - σ T'| ≤ C * ∑ i : Fin k, c1NormR4 (componentAt T i - componentAt T' i) *
          ∏ i' ∈ Finset.univ.erase i,
            max (c1NormR4 (componentAt T i')) (c1NormR4 (componentAt T' i')) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
  let K : Fin N → Compacts Space := fun i => ⟨S i, hS i⟩
  have hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i') := hd
  have hlin : ∀ j, IsSlotLinear (A.mean j) := fun j =>
    (hR L hodd h13 A j).2.2.2.2.2.2.2.2.2.2.1
  have hcore : ∀ i, NormedSpace.Core ℝ (C1Space (K i)) := fun i => (hC (K i)).1.2.1
  let g : ∀ i, NormedAddCommGroup (C1Space (K i)) := fun i =>
    NormedAddCommGroup.ofCore (hcore i)
  let v : ∀ i, NormedSpace ℝ (C1Space (K i)) := fun i => NormedSpace.ofCore (hcore i)
  have hcomp : ∀ i, CompleteSpace (C1Space (K i)) := fun i => by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    obtain ⟨l, hl⟩ := (hC (K i)).1.2.2 u fun ε hε => by
      obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.1 hu ε hε
      refine ⟨M, fun a ha b hb => ?_⟩
      have := hM a ha b hb
      rwa [dist_eq_norm] at this
    refine ⟨C1Space.ofSupported l, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := hl ε hε
    refine ⟨M, fun a ha => ?_⟩
    rw [dist_eq_norm]
    exact hM a ha
  obtain ⟨C₀, hC₀⟩ := hU N (fun i => C1Space (K i)) (fun n => meanForm A n (hlin n) hK)
    (fun n => exists_meanForm_bound A n hP hodd h13 hK)
    (fun f => bddAbove_range_abs_of_tendsto_pnat (hσ.2 (tupleOfSections hK f)))
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have H : ∀ (j : ℕ+) (u : ∀ i, C1Space (K i)),
      ‖meanForm A j (hlin j) hK u‖ ≤ max C₀ 0 * ∏ i, ‖u i‖ := fun j u =>
    (hC₀ j u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  refine ⟨max C₀ 0, hC0, fun T T' hT hT' hs => ?_⟩
  obtain ⟨m₁, e₁, f₁⟩ := exists_tupleOfSections hK T hT fun i => Set.subset_union_left.trans (hs i)
  obtain ⟨m₂, e₂, f₂⟩ :=
    exists_tupleOfSections hK T' hT' fun i => Set.subset_union_right.trans (hs i)
  have n₁ : ∀ i : Fin N, c1NormR4 (componentAt T i) = ‖m₁ i‖ := fun i => by
    rw [← f₁ i]
    rfl
  have n₂ : ∀ i : Fin N, c1NormR4 (componentAt T' i) = ‖m₂ i‖ := fun i => by
    rw [← f₂ i]
    rfl
  have n₃ : ∀ i : Fin N, c1NormR4 (componentAt T i - componentAt T' i) = ‖m₁ i - m₂ i‖ := fun i => by
    rw [← f₁ i, ← f₂ i]
    rfl
  refine ⟨fun j => ?_, ?_⟩
  · have h := H j m₁
    rw [Real.norm_eq_abs, meanForm_apply, e₁] at h
    simpa only [n₁] using h
  · have hj : ∀ j, |A.mean j T - A.mean j T'| ≤ max C₀ 0 * ∑ i, ∏ l,
        if l = i then ‖m₁ i - m₂ i‖ else max ‖m₁ l‖ ‖m₂ l‖ := fun j => by
      have h := (meanForm A j (hlin j) hK).norm_image_sub_le_of_bound' hC0 (H j) m₁ m₂
      rw [Real.norm_eq_abs, meanForm_apply, meanForm_apply, e₁, e₂] at h
      exact h
    refine (le_of_tendsto' ((hσ.2 T).sub (hσ.2 T')).abs hj).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [n₃, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl), n₁, n₂]
theorem limit_isAdmissiblyContinuous (hR : TupleRepresentatives.Statement)
    (hU : NormedSpaces.MultilinearSequenceUniformBound)
    (hC : C1Banach.BanachAndComparable)
    (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hodd : Odd L) (h13 : 13 ≤ L) (A : LatticeSequence L) (σ : Tuple → ℝ)
    (hσ : A.HasLimit σ) : IsAdmissiblyContinuous σ := by
  rintro n₀ seq T ⟨hlen, S, hS, hd, hsub, hto⟩
  rcases Nat.eq_zero_or_pos T.len with h0 | hk
  · have hT : T.1 = [] := List.length_eq_zero_iff.1 h0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hn' : (seq n).1 = [] := List.length_eq_zero_iff.1 ((hlen n hn).trans h0)
    exact congrArg σ (Subtype.ext (hT.trans hn'.symm))
  · obtain ⟨C, hC0, hCb⟩ := exists_multilinear_constant hR hU hC hP hodd h13 A σ hσ hk S hS hd
    let K : Fin T.len → Compacts Space := fun i => ⟨S i, hS i⟩
    have hK : ∀ i i', i ≠ i' → Disjoint (K i : Set Space) (K i') := hd
    have htri : ∀ n ≥ n₀, ∀ i : Fin T.len, c1NormR4 (componentAt (seq n) i) ≤
        c1NormR4 (componentAt T i) + c1NormR4 (componentAt (seq n) i - componentAt T i) := fun n hn i => by
      obtain ⟨m₁, -, f₁⟩ := exists_tupleOfSections hK (seq n) (hlen n hn)
        fun i => Set.subset_union_left.trans (hsub n hn i)
      obtain ⟨m₂, -, f₂⟩ := exists_tupleOfSections hK T rfl
        fun i => Set.subset_union_right.trans (hsub n hn i)
      rw [← f₁ i, ← f₂ i]
      exact c1NormR4_le_add_sub hC (m₁ i) (m₂ i)
    have hbound : ∀ n ≥ n₀, |σ (seq n) - σ T| ≤ C * ∑ i : Fin T.len,
        c1NormR4 (componentAt (seq n) i - componentAt T i) * ∏ i' ∈ Finset.univ.erase i,
          (c1NormR4 (componentAt T i') + c1NormR4 (componentAt (seq n) i' - componentAt T i')) := by
      intro n hn
      refine (hCb (seq n) T (hlen n hn) rfl (hsub n hn)).2.trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hC0)
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
        (fun _ _ => le_max_of_le_left (c1NormR4_nonneg _)) fun i' _ => ?_) (c1NormR4_nonneg _)
      exact max_le (htri n hn i') (le_add_of_nonneg_right (c1NormR4_nonneg _))
    have hlimit : Tendsto (fun n => C * ∑ i : Fin T.len,
        c1NormR4 (componentAt (seq n) i - componentAt T i) * ∏ i' ∈ Finset.univ.erase i,
          (c1NormR4 (componentAt T i') + c1NormR4 (componentAt (seq n) i' - componentAt T i')))
        atTop (𝓝 0) := by
      have h : Tendsto (fun n => C * ∑ i : Fin T.len,
          c1NormR4 (componentAt (seq n) i - componentAt T i) * ∏ i' ∈ Finset.univ.erase i,
            (c1NormR4 (componentAt T i') + c1NormR4 (componentAt (seq n) i' - componentAt T i')))
          atTop (𝓝 (C * ∑ i : Fin T.len, 0 * ∏ i' ∈ Finset.univ.erase i,
            (c1NormR4 (componentAt T i') + 0))) :=
        (tendsto_finsetSum _ fun i _ => (hto i).mul
          (tendsto_finsetProd _ fun i' _ => tendsto_const_nhds.add (hto i'))).const_mul C
      simpa using h
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlimit)
    filter_upwards [eventually_ge_atTop n₀] with n hn using hbound n hn
end Constant
theorem limitIsContinuous_holds (hR : TupleRepresentatives.Statement)
    (hU : NormedSpaces.MultilinearSequenceUniformBound)
    (hC : C1Banach.BanachAndComparable)
    (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite) :
    LimitContinuity.LimitIsContinuous := by
  intro L hodd h13 A σ hσ
  refine ⟨fun k hk S hS hd => ?_, limit_isAdmissiblyContinuous hR hU hC hP hodd h13 A σ hσ⟩
  obtain ⟨C, -, h⟩ := exists_multilinear_constant hR hU hC hP hodd h13 A σ hσ hk S hS hd
  exact ⟨C, h⟩
end YangMills.Construction.ReflectionPositivity.LimitContinuityProof
