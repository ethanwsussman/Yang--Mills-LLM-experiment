import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.InfiniteLattice.StatesWithAGivenMirrorDominateLocalObservablesProof
import YangMills.Construction.InfiniteLattice.UnfoldedAndFoldedArraysOfALadder
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
namespace PeriodLatticeProof
def heightLinear (n : AmbientSpace) : AmbientSpace →ₗ[ℝ] ℝ where
  toFun x := n ⬝ᵥ x
  map_add' x y := dotProduct_add n x y
  map_smul' c x := by simp [dotProduct_smul]
theorem dotProduct_eq_zero_of_mem_parallel {n y : AmbientSpace}
    (hy : y ∈ parallelPeriodLattice n) : n ⬝ᵥ y = 0 := by apply _root_.YangMills.Construction.NormalFamilies.MirrorLadder.dotProduct_eq_zero_of_mem_parallelPeriodLattice <;> assumption
theorem dotProduct_add_zsmul_of_mem_parallel {n y : AmbientSpace}
    (hy : y ∈ parallelPeriodLattice n) (w : AmbientSpace) (m : ℤ) :
    n ⬝ᵥ (y + m • w) = (m : ℝ) * (n ⬝ᵥ w) := by
  rw [dotProduct_add, dotProduct_eq_zero_of_mem_parallel hy, zero_add, ← Int.cast_smul_eq_zsmul ℝ,
    dotProduct_smul, smul_eq_mul]
theorem span_parallelPeriodLattice_eq_ker {n : AmbientSpace} (hn : n ∈ normalSet) :
    Submodule.span ℝ (parallelPeriodLattice n : Set AmbientSpace) = LinearMap.ker (heightLinear n) := by
  have he := dotProduct_firstNonzeroBasisVec hn
  refine le_antisymm (Submodule.span_le.mpr fun y hy => ?_) fun x hx => ?_
  · exact LinearMap.mem_ker.mpr (dotProduct_eq_zero_of_mem_parallel hy)
  have hx0 : n ⬝ᵥ x = 0 := LinearMap.mem_ker.mp hx
  have hw : ∀ μ : Fin 4, coordVec μ - (n μ) • firstNonzeroBasisVec n ∈
      Submodule.span ℝ (parallelPeriodLattice n : Set AmbientSpace) := by
    intro μ
    have hdot : n ⬝ᵥ coordVec μ = n μ := by simp [coordVec]
    obtain ⟨k, hk⟩ := exists_int_dotProduct_latticePoint hn (axisStep 1 μ)
    have hnμ : n μ = k := by
      rw [← hdot]
      exact hk
    have hs : coordVec μ - (k : ℝ) • firstNonzeroBasisVec n ∈ latticeSubgroup 1 := by
      rw [Int.cast_smul_eq_zsmul]
      exact sub_mem (axisStep 1 μ).2 (zsmul_mem (firstNonzeroBasisVec_mem_latticeSubgroup n) k)
    have hp : (2 * ((1 : ℤ) : ℝ)) • (coordVec μ - (k : ℝ) • firstNonzeroBasisVec n) ∈
        parallelPeriodLattice n := by
      refine AddSubgroup.mem_inf.mpr ⟨two_mul_smul_mem_evenLattice 1 hs, ?_⟩
      change n ⬝ᵥ _ = 0
      rw [dotProduct_smul, dotProduct_sub, dotProduct_smul, hdot, he, hnμ]
      simp
    have := Submodule.smul_mem _ ((2 : ℝ)⁻¹)
      (Submodule.subset_span (s := (parallelPeriodLattice n : Set AmbientSpace)) hp)
    rw [smul_smul] at this
    rw [hnμ]
    simpa using this
  have hsum : ∑ μ, x μ * n μ = 0 := by
    rw [← hx0]
    simp only [dotProduct, mul_comm]
  have hx' : x = ∑ μ, x μ • (coordVec μ - (n μ) • firstNonzeroBasisVec n) := by
    ext ν
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    have h1 : ∑ μ, x μ * coordVec μ ν = x ν := by
      simp [coordVec, Pi.single_apply]
    have h2 : ∑ μ, x μ * (n μ * firstNonzeroBasisVec n ν) = 0 := by
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, hsum, zero_mul]
    rw [h1, h2, sub_zero]
  rw [hx']
  exact Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ (hw μ)
theorem finrank_span_parallelPeriodLattice {n : AmbientSpace} (hn : n ∈ normalSet) :
    Module.finrank ℝ (Submodule.span ℝ (parallelPeriodLattice n : Set AmbientSpace)) = 3 := by
  rw [span_parallelPeriodLattice_eq_ker hn]
  have hsurj : Function.Surjective (heightLinear n) := fun t => ⟨t • firstNonzeroBasisVec n, by
    change n ⬝ᵥ (t • firstNonzeroBasisVec n) = t
    rw [dotProduct_smul, dotProduct_firstNonzeroBasisVec hn]
    simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (heightLinear n)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega
theorem parallelLatticeSpansHyperplane_holds {n : AmbientSpace} (hn : n ∈ normalSet) :
    ParallelLatticeSpansHyperplane n := by
  refine ⟨?_, finrank_span_parallelPeriodLattice hn, fun x hx => ?_⟩
  · rw [span_parallelPeriodLattice_eq_ker hn]
    ext x
    exact LinearMap.mem_ker
  · rw [linearReflect_apply, dotProduct_eq_zero_of_mem_parallel hx]
    simp
theorem evenLattice_le_latticeSubgroup : evenLattice ≤ latticeSubgroup 1 := by apply _root_.YangMills.Construction.InfiniteLattice.MirrorDomination.evenLattice_le_latticeSubgroup <;> assumption
theorem even_smul_firstNonzeroBasisVec_mem {h : ℤ} (he : Even h) (n : AmbientSpace) :
    (h : ℝ) • firstNonzeroBasisVec n ∈ evenLattice := by
  obtain ⟨t, rfl⟩ := he
  have := two_mul_smul_mem_evenLattice t (firstNonzeroBasisVec_mem_latticeSubgroup n)
  rwa [show (2 * (t : ℝ)) = (((t + t : ℤ)) : ℝ) by push_cast; ring] at this
def ladderAtOrigin {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet) (he : Even h) (h2 : 2 ≤ h) :
    MirrorLadder where
  normal := n
  normal_mem := hn
  offset := 0
  offset_allowed := ⟨fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  spacing := h
  even_spacing := he
  two_le_spacing := h2
theorem two_mul_smul_dualVector_mem {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet) (he : Even h)
    (h2 : 2 ≤ h) : (2 * (h : ℝ)) • dualVector n ∈ evenLattice :=
  (ladderAtOrigin hn he h2).two_mul_spacing_smul_dualVector_mem
theorem disjoint_zmultiples_of_dotProduct_ne_zero {n w : AmbientSpace} (hw : n ⬝ᵥ w ≠ 0) :
    Disjoint (parallelPeriodLattice n) (AddSubgroup.zmultiples w) := by
  rw [AddSubgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx'
  have h0 : n ⬝ᵥ (k • w) = 0 := dotProduct_eq_zero_of_mem_parallel hx
  rw [← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, smul_eq_mul] at h0
  have hk : (k : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right hw
  have hk' : k = 0 := by exact_mod_cast hk
  simp [hk']
theorem nonempty_linearEquiv_latticePoint : Nonempty ((Fin 4 → ℤ) ≃ₗ[ℤ] LatticePoint 1) := by
  let e₀ : (Fin 4 → ℤ) →+ LatticePoint 1 :=
    { toFun := fun m => ⟨fun μ => (m μ : ℝ) * 1, m, fun _ => rfl⟩
      map_zero' := Subtype.ext (funext fun μ => by simp)
      map_add' := fun m m' => Subtype.ext (funext fun μ => by simp) }
  have hbij : Function.Bijective e₀ := by
    refine ⟨fun m m' hmm => funext fun μ => ?_, ?_⟩
    · have := congrFun (congrArg Subtype.val hmm) μ
      have h' : (m μ : ℝ) * 1 = (m' μ : ℝ) * 1 := this
      simpa using h'
    · rintro ⟨x, m, hm⟩
      exact ⟨m, Subtype.ext (funext fun μ => (hm μ).symm)⟩
  exact ⟨(AddEquiv.ofBijective e₀ hbij).toIntLinearEquiv⟩
theorem finrank_latticePoint : Module.finrank ℤ (LatticePoint 1) = 4 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_latticePoint
  rw [← e.finrank_eq, Module.finrank_fin_fun]
theorem finrank_eq_four_of_finiteIndex {H : AddSubgroup AmbientSpace} (hle : H ≤ latticeSubgroup 1)
    (hfin : (H.addSubgroupOf (latticeSubgroup 1)).FiniteIndex) : Module.finrank ℤ H = 4 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_latticePoint
  have : Module.Finite ℤ (LatticePoint 1) := Module.Finite.equiv e
  let N : Submodule ℤ (LatticePoint 1) := AddSubgroup.toIntSubmodule (H.addSubgroupOf (latticeSubgroup 1))
  have hq : Module.finrank ℤ (LatticePoint 1 ⧸ N) = 0 := by
    apply Module.finrank_eq_zero_of_rank_eq_zero
    rw [rank_eq_zero_iff]
    intro c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N c
    refine ⟨((H.addSubgroupOf (latticeSubgroup 1)).index : ℤ), by exact_mod_cast hfin.index_ne_zero, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change ((H.addSubgroupOf (latticeSubgroup 1)).index : ℤ) • x ∈ H.addSubgroupOf (latticeSubgroup 1)
    rw [natCast_zsmul]
    exact AddSubgroup.nsmul_index_mem _ x
  have h1 := N.finrank_quotient_add_finrank
  have h2 : Module.finrank ℤ H = Module.finrank ℤ N :=
    (AddSubgroup.addSubgroupOfEquivOfLe hle).symm.toIntLinearEquiv.finrank_eq
  rw [hq, zero_add, finrank_latticePoint] at h1
  rw [h2, h1]
theorem axialPeriodLattice_le_evenLattice {n : AmbientSpace} {h : ℤ} (he : Even h) :
    axialPeriodLattice n h ≤ evenLattice :=
  sup_le inf_le_left (AddSubgroup.zmultiples_le.mpr (even_smul_firstNonzeroBasisVec_mem he n))
theorem normalPeriodLattice_le_evenLattice {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) : normalPeriodLattice n h ≤ evenLattice :=
  sup_le inf_le_left (AddSubgroup.zmultiples_le.mpr (two_mul_smul_dualVector_mem hn he h2))
theorem image_linearReflect_normalPeriodLattice {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet) :
    linearReflect n '' (normalPeriodLattice n h : Set AmbientSpace) = normalPeriodLattice n h := by
  have hs := dotProduct_dualVector hn
  have hgd : n ⬝ᵥ ((2 * (h : ℝ)) • dualVector n) = 2 * (h : ℝ) := by
    rw [dotProduct_smul, hs]
    simp
  have hθ : ∀ y ∈ parallelPeriodLattice n, ∀ k : ℤ,
      linearReflect n (y + k • ((2 * (h : ℝ)) • dualVector n)) =
        y + (-k) • ((2 * (h : ℝ)) • dualVector n) := by
    intro y hy k
    rw [linearReflect_apply, dotProduct_add_zsmul_of_mem_parallel hy, hgd]
    have : (2 * ((k : ℝ) * (2 * (h : ℝ)))) • dualVector n =
        (k + k) • ((2 * (h : ℝ)) • dualVector n) := by
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
      push_cast
      congr 1
      ring
    rw [this, add_zsmul, neg_zsmul]
    abel
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, k, rfl⟩ := mem_normalPeriodLattice_iff.mp hx
    rw [hθ y hy k]
    exact mem_normalPeriodLattice_iff.mpr ⟨y, hy, -k, rfl⟩
  · intro x hx
    obtain ⟨y, hy, k, rfl⟩ := mem_normalPeriodLattice_iff.mp hx
    exact ⟨y + (-k) • ((2 * (h : ℝ)) • dualVector n),
      mem_normalPeriodLattice_iff.mpr ⟨y, hy, -k, rfl⟩, by rw [hθ y hy (-k), neg_neg]⟩
theorem axialPeriodsHaveFiniteIndex_holds {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) : AxialPeriodsHaveFiniteIndex n h := by
  have hh : (h : ℝ) ≠ 0 := by
    have : h ≠ 0 := by omega
    exact_mod_cast this
  have hdq : n ⬝ᵥ ((h : ℝ) • firstNonzeroBasisVec n) ≠ 0 := by
    rw [dotProduct_smul, dotProduct_firstNonzeroBasisVec hn]
    simpa using hh
  have hdp : n ⬝ᵥ ((2 * (h : ℝ)) • dualVector n) ≠ 0 := by
    rw [dotProduct_smul, dotProduct_dualVector hn]
    simpa using hh
  have hq : axialPeriodLattice n h ≤ latticeSubgroup 1 :=
    (axialPeriodLattice_le_evenLattice he).trans evenLattice_le_latticeSubgroup
  have hp : normalPeriodLattice n h ≤ latticeSubgroup 1 :=
    (normalPeriodLattice_le_evenLattice hn he h2).trans evenLattice_le_latticeSubgroup
  have hqf : ((axialPeriodLattice n h).addSubgroupOf (latticeSubgroup 1)).FiniteIndex :=
    (ladderAtOrigin hn he h2).finiteIndex_axialSublattice
  have hpf : ((normalPeriodLattice n h).addSubgroupOf (latticeSubgroup 1)).FiniteIndex :=
    (ladderAtOrigin hn he h2).finiteIndex_normalSublattice
  have hq0 : (axialPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0 := hqf.index_ne_zero
  have hp0 : (normalPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0 := hpf.index_ne_zero
  refine ⟨even_smul_firstNonzeroBasisVec_mem he n, two_mul_smul_dualVector_mem hn he h2,
    axialPeriodLattice_le_evenLattice he, normalPeriodLattice_le_evenLattice hn he h2,
    disjoint_zmultiples_of_dotProduct_ne_zero hdq, disjoint_zmultiples_of_dotProduct_ne_zero hdp,
    finrank_eq_four_of_finiteIndex hq hqf, finrank_eq_four_of_finiteIndex hp hpf, ⟨hq, hq0⟩,
    ⟨hp, hp0⟩, ?_, image_linearReflect_normalPeriodLattice hn⟩
  rw [axialPeriodDensity, if_pos ⟨hq, hq0⟩]
  exact inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq0)
theorem sub_mem_parallelPeriodLattice {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) :
    (2 * (h : ℝ)) • dualVector n - (2 * (h : ℝ)) • firstNonzeroBasisVec n ∈
      parallelPeriodLattice n := by
  refine AddSubgroup.mem_inf.mpr ⟨sub_mem (two_mul_smul_dualVector_mem hn he h2)
    (two_mul_smul_mem_evenLattice h (firstNonzeroBasisVec_mem_latticeSubgroup n)), ?_⟩
  change n ⬝ᵥ _ = 0
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_dualVector hn,
    dotProduct_firstNonzeroBasisVec hn, sub_self]
theorem normalPeriodLattice_eq_sup {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet) (he : Even h)
    (h2 : 2 ≤ h) :
    normalPeriodLattice n h =
      parallelPeriodLattice n ⊔ AddSubgroup.zmultiples ((2 * (h : ℝ)) • firstNonzeroBasisVec n) := by
  have hd := sub_mem_parallelPeriodLattice hn he h2
  apply le_antisymm
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    rw [show (2 * (h : ℝ)) • dualVector n =
      ((2 * (h : ℝ)) • dualVector n - (2 * (h : ℝ)) • firstNonzeroBasisVec n) +
        (2 * (h : ℝ)) • firstNonzeroBasisVec n by abel]
    exact add_mem (AddSubgroup.mem_sup_left hd)
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _))
  · refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    rw [show (2 * (h : ℝ)) • firstNonzeroBasisVec n =
      (2 * (h : ℝ)) • dualVector n -
        ((2 * (h : ℝ)) • dualVector n - (2 * (h : ℝ)) • firstNonzeroBasisVec n) by abel]
    exact sub_mem (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _))
      (AddSubgroup.mem_sup_left hd)
theorem add_zsmul_mem_normalPeriodLattice_iff {n y : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) (hy : y ∈ parallelPeriodLattice n) (m : ℤ) :
    y + m • ((h : ℝ) • firstNonzeroBasisVec n) ∈ normalPeriodLattice n h ↔ Even m := by
  have hh : (h : ℝ) ≠ 0 := by
    have : h ≠ 0 := by omega
    exact_mod_cast this
  have hg : (2 * (h : ℝ)) • firstNonzeroBasisVec n =
      (2 : ℤ) • ((h : ℝ) • firstNonzeroBasisVec n) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    norm_num
  rw [normalPeriodLattice_eq_sup hn he h2]
  constructor
  · intro hmem
    obtain ⟨y', hy', _, ⟨r, rfl⟩, hsum⟩ := AddSubgroup.mem_sup.mp hmem
    have hsum' := congrArg (fun x => n ⬝ᵥ x) hsum
    simp only at hsum'
    rw [dotProduct_add_zsmul_of_mem_parallel hy', dotProduct_add_zsmul_of_mem_parallel hy,
      dotProduct_smul, dotProduct_smul, dotProduct_firstNonzeroBasisVec hn] at hsum'
    simp only [smul_eq_mul, mul_one] at hsum'
    have hr : (m : ℝ) = ((r + r : ℤ) : ℝ) := by
      push_cast
      apply mul_right_cancel₀ hh
      linarith
    exact ⟨r, by exact_mod_cast hr⟩
  · rintro ⟨r, rfl⟩
    refine AddSubgroup.mem_sup.mpr ⟨y, hy, r • ((2 * (h : ℝ)) • firstNonzeroBasisVec n),
      AddSubgroup.mem_zmultiples_iff.mpr ⟨r, rfl⟩, ?_⟩
    rw [hg, smul_smul, mul_two]
theorem relIndex_normalPeriodLattice_eq_two {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) :
    (normalPeriodLattice n h).relIndex (axialPeriodLattice n h) = 2 := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_two_iff]
  have hg : (h : ℝ) • firstNonzeroBasisVec n ∈ axialPeriodLattice n h :=
    AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
  refine ⟨⟨_, hg⟩, fun b => ?_⟩
  obtain ⟨y, hy, k, hk⟩ := mem_axialPeriodLattice_iff.mp b.2
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add]
  rw [← hk, add_assoc, ← add_one_zsmul, add_zsmul_mem_normalPeriodLattice_iff hn he h2 hy,
    add_zsmul_mem_normalPeriodLattice_iff hn he h2 hy, Int.even_add_one]
  by_cases hev : Even k <;> simp [hev, Xor]
theorem normalPeriodsHaveIndexTwo_holds {n : AmbientSpace} {h : ℤ} (hn : n ∈ normalSet)
    (he : Even h) (h2 : 2 ≤ h) : NormalPeriodsHaveIndexTwo n h := by
  have hh : (h : ℝ) ≠ 0 := by
    have : h ≠ 0 := by omega
    exact_mod_cast this
  have hle : normalPeriodLattice n h ≤ axialPeriodLattice n h := by
    rw [normalPeriodLattice_eq_sup hn he h2]
    refine sup_le le_sup_left (AddSubgroup.zmultiples_le.mpr ?_)
    rw [show (2 * (h : ℝ)) • firstNonzeroBasisVec n =
      (2 : ℤ) • ((h : ℝ) • firstNonzeroBasisVec n) by
        rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
        norm_num]
    exact zsmul_mem (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)) 2
  have hfi := axialPeriodsHaveFiniteIndex_holds hn he h2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hq, hq0⟩, -⟩ := hfi
  refine ⟨sub_mem_parallelPeriodLattice hn he h2, normalPeriodLattice_eq_sup hn he h2,
    disjoint_zmultiples_of_dotProduct_ne_zero ?_, hle, relIndex_normalPeriodLattice_eq_two hn he h2, ?_⟩
  · rw [dotProduct_smul, dotProduct_firstNonzeroBasisVec hn]
    simpa using hh
  · rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle hq, relIndex_normalPeriodLattice_eq_two hn he h2,
      axialPeriodDensity, if_pos ⟨hq, hq0⟩]
    push_cast
    rw [div_inv_eq_mul]
theorem periodsShiftTheSlabs_holds (L : MirrorLadder) : PeriodsShiftTheSlabs L := by
  have hne := L.spacing_ne_zero
  have he := dotProduct_firstNonzeroBasisVec L.normal_mem
  have hs := dotProduct_dualVector L.normal_mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨y, hy, k, rfl⟩ := mem_axialPeriodLattice_iff.mp hv
    refine ⟨k, ?_⟩
    rw [dotProduct_add_zsmul_of_mem_parallel hy, dotProduct_smul, he]
    simp
  · intro m
    refine ⟨m • ((L.spacing : ℝ) • firstNonzeroBasisVec L.normal),
      zsmul_mem (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)) m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, dotProduct_smul, he]
    simp
  · intro v k m _ hm
    have hmv : L.normal ⬝ᵥ (v : AmbientSpace) = (m : ℝ) * (L.spacing : ℝ) := by
      rw [hm]
      field_simp
    have e1 : ((k + m : ℤ) : ℝ) * (L.spacing : ℝ) = (k : ℝ) * L.spacing + (m : ℝ) * L.spacing := by
      push_cast
      ring
    have e2 : (((k + m : ℤ) : ℝ) + 1) * (L.spacing : ℝ) =
        ((k : ℝ) + 1) * L.spacing + (m : ℝ) * L.spacing := by
      push_cast
      ring
    ext x
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      have hz : L.normal ⬝ᵥ ((shift v).toFun z) = L.normal ⬝ᵥ z + (m : ℝ) * L.spacing := by
        change L.normal ⬝ᵥ (z + (v : AmbientSpace)) = _
        rw [dotProduct_add, hmv]
      refine ⟨?_, ?_⟩
      · rw [hz, e1]
        linarith
      · rw [hz, e2]
        linarith
    · rintro ⟨h1, h2⟩
      rw [e1] at h1
      rw [e2] at h2
      have hz : L.normal ⬝ᵥ (x - (v : AmbientSpace)) = L.normal ⬝ᵥ x - (m : ℝ) * L.spacing := by
        rw [dotProduct_sub, hmv]
      refine ⟨x - (v : AmbientSpace), ⟨?_, ?_⟩, ?_⟩
      · rw [hz]
        linarith
      · rw [hz]
        linarith
      · change x - (v : AmbientSpace) + (v : AmbientSpace) = x
        abel
  · intro v hv
    obtain ⟨y, hy, k, rfl⟩ := mem_normalPeriodLattice_iff.mp hv
    refine ⟨k, ?_⟩
    rw [dotProduct_add_zsmul_of_mem_parallel hy, dotProduct_smul, hs]
    simp
  · intro m
    refine ⟨m • ((2 * (L.spacing : ℝ)) • dualVector L.normal),
      zsmul_mem (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)) m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, dotProduct_smul, hs]
    simp
  · intro j y hy
    rw [dotProduct_add, dotProduct_eq_zero_of_mem_parallel hy, dotProduct_smul, he]
    simp
  · intro i y hy
    rw [dotProduct_add, dotProduct_eq_zero_of_mem_parallel hy, dotProduct_smul, hs]
    simp
theorem periodLatticeProperties_holds : PeriodLatticeProperties :=
  ⟨fun _ hn _ he h2 => ⟨parallelLatticeSpansHyperplane_holds hn,
    axialPeriodsHaveFiniteIndex_holds hn he h2, normalPeriodsHaveIndexTwo_holds hn he h2⟩,
    periodsShiftTheSlabs_holds⟩
end PeriodLatticeProof
end YangMills.Construction.NormalFamilies
