import YangMills.Construction.LatticeFields.FieldsAndDifferences
import YangMills.Construction.LatticeFields.BlockAveragingProof
import YangMills.Construction.LatticeFields.PointwiseBoundsOfDecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace BlockAvgDuality
def SqSummable {X : Type} (g : X → ℝ) : Prop := Summable fun x => g x ^ 2
theorem summable_mul_of_sqSummable {X : Type} {u v : X → ℝ} (hu : SqSummable u)
    (hv : SqSummable v) : Summable fun x => u x * v x := by apply _root_.YangMills.DeltaSharedProofs.p500472 <;> assumption
theorem SqSummable.add {X : Type} {g h : X → ℝ} (hg : SqSummable g) (hh : SqSummable h) :
    SqSummable fun x => g x + h x := by apply _root_.YangMills.DeltaSharedProofs.p1251 <;> assumption
theorem SqSummable.const_mul {X : Type} (c : ℝ) {g : X → ℝ} (hg : SqSummable g) :
    SqSummable fun x => c * g x := by apply _root_.YangMills.DeltaSharedProofs.p501093 <;> assumption
theorem SqSummable.finsetSum {X ι : Type} (t : Finset ι) {g : ι → X → ℝ}
    (hg : ∀ i ∈ t, SqSummable (g i)) : SqSummable fun x => ∑ i ∈ t, g i x := by apply _root_.YangMills.DeltaSharedProofs.p501383 <;> assumption
theorem SqSummable.comp_injective {X X' : Type} {g : X' → ℝ} (hg : SqSummable g) {f : X → X'}
    (hf : Function.Injective f) : SqSummable fun x => g (f x) :=
  Summable.comp_injective hg hf
section Fibers
variable {S Y K : Type} [AddCommGroup S] [Fintype K] (Φ : Y × K ≃ S)
end Fibers
section Pairs
theorem tsum_prod_eq_sum_tsum {X J : Type} [Fintype J] {F : X → J → ℝ}
    (hF : Summable fun p : X × J => F p.1 p.2) :
    ∑' p : X × J, F p.1 p.2 = ∑ i, ∑' x, F x i := by
  have hs : Summable fun q : J × X => F q.2 q.1 := (Equiv.prodComm J X).summable_iff.mpr hF
  calc ∑' p : X × J, F p.1 p.2 = ∑' q : J × X, F q.2 q.1 :=
        ((Equiv.prodComm J X).tsum_eq fun p : X × J => F p.1 p.2).symm
    _ = ∑' i, ∑' x, F x i := hs.tsum_prod
    _ = ∑ i, ∑' x, F x i := tsum_fintype _
end Pairs
section Forms
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d} {I K : Type} [Fintype I] [Fintype K]
theorem latticeSpacing_pos : 0 < latticeSpacing N := by apply _root_.YangMills.Construction.LatticeFields.PointwiseOfDecay.latticeSpacing_pos <;> assumption
theorem latticeSpacing_one : latticeSpacing 1 = 1 := by simp [latticeSpacing]
omit [NeZero N] [Fintype I] in
theorem fieldInner_deltaField (x : LatticeSite N κ) (i : I) (G : LatticeField N κ I) :
    fieldInner (deltaField x i : LatticeField N κ I) G = latticeSpacing N ^ d * G x i := by
  classical
  unfold fieldInner
  rw [tsum_eq_single (x, i)]
  · simp [deltaField]
  · intro p hp
    have hp' : p ∉ ({(x, i)} : Set (LatticeSite N κ × I)) := by simpa using hp
    simp [deltaField, Set.indicator_of_notMem hp']
end Forms
section Blocks
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
def cellOffset (N : ℕ) (k : Fin d → Fin N) : scaledIntLattice d N :=
  ⟨fun μ => latticeSpacing N * ((k μ : ℕ) : ℝ), fun μ => ⟨((k μ : ℕ) : ℤ), by simp⟩⟩
def cellPoint (q : LatticeSite 1 κ × (Fin d → Fin N)) : LatticeSite N κ :=
  unitSiteHom N κ q.1 + toSite N κ (cellOffset N q.2)
theorem cellOffset_nonneg (k : Fin d → Fin N) (μ : Fin d) :
    0 ≤ (cellOffset N k : Fin d → ℝ) μ := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.cellOffset_nonneg <;> assumption
theorem cellOffset_lt_one (k : Fin d → Fin N) (μ : Fin d) :
    (cellOffset N k : Fin d → ℝ) μ < 1 := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.cellOffset_lt_one <;> assumption
theorem exists_int_of_unitLattice (w : scaledIntLattice d 1) (μ : Fin d) :
    ∃ m : ℤ, (w : Fin d → ℝ) μ = m := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.exists_int_coord_unit <;> assumption
theorem exists_cellOffset (w : scaledIntLattice d 1) (v : scaledIntLattice d N)
    (h : ∀ μ, (w : Fin d → ℝ) μ ≤ (v : Fin d → ℝ) μ ∧ (v : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1) :
    ∃ k, v = AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w + cellOffset N k := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have key : ∀ μ, ∃ r : Fin N, (v : Fin d → ℝ) μ =
      (w : Fin d → ℝ) μ + latticeSpacing N * (((r : ℕ)) : ℝ) := by
    intro μ
    obtain ⟨n, hn⟩ := v.2 μ
    obtain ⟨m, hm⟩ := exists_int_of_unitLattice w μ
    have hv : (v : Fin d → ℝ) μ = latticeSpacing N * n := hn
    have ht : (((n - N * m : ℤ)) : ℝ) = N * ((v : Fin d → ℝ) μ - (w : Fin d → ℝ) μ) := by
      rw [hv, hm, latticeSpacing]
      push_cast
      field_simp
    have h0 : 0 ≤ n - N * m := by
      have : (0 : ℝ) ≤ ((n - N * m : ℤ) : ℝ) := by
        rw [ht]
        exact mul_nonneg hN.le (sub_nonneg.mpr (h μ).1)
      exact_mod_cast this
    have h1 : n - N * m < N := by
      have : ((n - N * m : ℤ) : ℝ) < N := by
        rw [ht]
        have := (h μ).2
        nlinarith
      exact_mod_cast this
    obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨⟨r, by omega⟩, ?_⟩
    have hr' : (r : ℝ) = N * ((v : Fin d → ℝ) μ - (w : Fin d → ℝ) μ) := by
      rw [← ht, hr]
      simp
    change (v : Fin d → ℝ) μ = (w : Fin d → ℝ) μ + latticeSpacing N * (r : ℝ)
    rw [hr', latticeSpacing]
    field_simp
    ring
  choose k hk using key
  refine ⟨k, Subtype.ext (funext fun μ => ?_)⟩
  exact hk μ
theorem cellPoint_toSite (w : scaledIntLattice d 1) (k : Fin d → Fin N) :
    cellPoint (toSite 1 κ w, k) =
      toSite N κ (AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w + cellOffset N k) := by
  rw [map_add]
  rfl
theorem cellPoint_surjective : Function.Surjective (cellPoint (N := N) (κ := κ)) := by
  intro x
  obtain ⟨v, rfl⟩ := toSite_surjective N κ x
  let w : scaledIntLattice d 1 := ⟨fun μ => (⌊(v : Fin d → ℝ) μ⌋ : ℝ), fun μ =>
    ⟨⌊(v : Fin d → ℝ) μ⌋, by simp [latticeSpacing]⟩⟩
  obtain ⟨k, hk⟩ := exists_cellOffset (N := N) w v fun μ =>
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  exact ⟨(toSite 1 κ w, k), by rw [cellPoint_toSite, hk]⟩
theorem cellPoint_injective : Function.Injective (cellPoint (N := N) (κ := κ)) := by
  rintro ⟨y, k⟩ ⟨y', k'⟩ h
  obtain ⟨w, rfl⟩ := toSite_surjective 1 κ y
  obtain ⟨w', rfl⟩ := toSite_surjective 1 κ y'
  rw [cellPoint_toSite, cellPoint_toSite] at h
  set a := AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w with ha
  set a' := AddSubgroup.inclusion (scaledIntLattice_one_le (d := d) N) w' with ha'
  have hz : (((a + cellOffset N k) - (a' + cellOffset N k') : scaledIntLattice d N) :
      Fin d → ℝ) ∈ periodSubgroup κ := by
    rw [← toSite_eq_zero_iff N κ, map_sub, h, sub_self]
  have hint := periodSubgroup_le_scaledIntLattice 1 κ hz
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hkk : k = k' := by
    funext μ
    obtain ⟨n, hn⟩ := hint μ
    obtain ⟨m, hm⟩ := exists_int_of_unitLattice w μ
    obtain ⟨m', hm'⟩ := exists_int_of_unitLattice w' μ
    have hn' : ((w : Fin d → ℝ) μ + latticeSpacing N * ((k μ : ℕ) : ℝ)) -
        ((w' : Fin d → ℝ) μ + latticeSpacing N * ((k' μ : ℕ) : ℝ)) = latticeSpacing 1 * n := hn
    rw [latticeSpacing_one, one_mul] at hn'
    have hdiv : ((((k μ : ℕ) : ℤ) - ((k' μ : ℕ) : ℤ) : ℤ)) = N * (n - m + m') := by
      have : ((((k μ : ℕ) : ℝ)) - (((k' μ : ℕ)) : ℝ)) = N * ((n : ℝ) - m + m') := by
        rw [hm, hm', latticeSpacing] at hn'
        field_simp at hn'
        linarith
      exact_mod_cast this
    have hz0 : ((k μ : ℕ) : ℤ) - ((k' μ : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) ⟨_, hdiv⟩ ?_
      have h1 := (k μ).2
      have h2 := (k' μ).2
      rw [abs_lt]
      omega
    exact Fin.ext (by omega)
  subst hkk
  have hw : ((w - w' : scaledIntLattice d 1) : Fin d → ℝ) ∈ periodSubgroup κ := by
    have : (((a + cellOffset N k) - (a' + cellOffset N k) : scaledIntLattice d N) :
        Fin d → ℝ) = ((w - w' : scaledIntLattice d 1) : Fin d → ℝ) := by
      funext μ
      simp [ha, ha']
    rwa [this] at hz
  have hy : toSite 1 κ w = toSite 1 κ w' := by
    have := (toSite_eq_zero_iff 1 κ (w - w')).mpr hw
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  rw [hy]
def cellEquiv : LatticeSite 1 κ × (Fin d → Fin N) ≃ LatticeSite N κ :=
  Equiv.ofBijective cellPoint ⟨cellPoint_injective, cellPoint_surjective⟩
theorem coarseBlock_eq_range (y : LatticeSite 1 κ) :
    coarseBlock N y = Set.range fun k : Fin d → Fin N => cellEquiv (N := N) (y, k) := by
  ext x
  constructor
  · rintro ⟨w, v, rfl, rfl, h⟩
    obtain ⟨k, hk⟩ := exists_cellOffset (N := N) w v h
    have hb : cellEquiv (N := N) (toSite 1 κ w, k) = cellPoint (toSite 1 κ w, k) := rfl
    exact ⟨k, hb.trans (by rw [cellPoint_toSite, hk])⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨w, rfl⟩ := toSite_surjective 1 κ y
    refine ⟨w, _, rfl, (cellPoint_toSite w k).symm, fun μ => ?_⟩
    have h0 := cellOffset_nonneg k μ
    have h1 := cellOffset_lt_one k μ
    change (w : Fin d → ℝ) μ ≤ (w : Fin d → ℝ) μ + (cellOffset N k : Fin d → ℝ) μ ∧
      (w : Fin d → ℝ) μ + (cellOffset N k : Fin d → ℝ) μ < (w : Fin d → ℝ) μ + 1
    constructor <;> linarith
theorem directionIndex_zero (i : Fin 1 → Fin d) : directionIndex (i 0) = i := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.directionIndex_apply_zero <;> assumption
end Blocks
end BlockAvgDuality
end YangMills.Construction.LatticeFields
