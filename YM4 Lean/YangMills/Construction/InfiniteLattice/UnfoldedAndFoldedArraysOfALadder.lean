import YangMills.Construction.InfiniteLattice.ImageOfABondAndWhatALocalObservableReads
import YangMills.Construction.InfiniteLattice.LadderOfMirrorsOfOneFamily
import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import YangMills.Construction.ReflectionPositivity.PeriodLatticesSplitForANormal
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
theorem exists_int_dotProduct_latticePoint {n : AmbientSpace} (hn : n ∈ normalSet)
    (x : LatticePoint 1) : ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) = k := by
  obtain ⟨m, hm⟩ := x.2
  have hc : ∀ μ, coordVec μ ⬝ᵥ (x : AmbientSpace) = m μ := fun μ => by
    simp [coordVec, hm μ]
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, ν, -, rfl | rfl⟩
  · exact ⟨m μ, hc μ⟩
  · exact ⟨m μ + m ν, by rw [add_dotProduct, hc, hc]; push_cast; rfl⟩
  · exact ⟨m μ - m ν, by rw [sub_dotProduct, hc, hc]; push_cast; rfl⟩
theorem firstNonzeroBasisVec_mem_latticeSubgroup (n : AmbientSpace) :
    firstNonzeroBasisVec n ∈ latticeSubgroup 1 :=
  (axisStep 1 (firstNonzeroIndex n)).2
theorem two_smul_dualVector_mem_latticeSubgroup {n : AmbientSpace} (hn : n ∈ normalSet) :
    (2 : ℝ) • dualVector n ∈ latticeSubgroup 1 := by
  have hc : ∀ μ, coordVec μ ∈ latticeSubgroup 1 := fun μ => (axisStep 1 μ).2
  have hdot : ∀ μ ν : Fin 4, μ < ν → coordVec μ ⬝ᵥ coordVec ν = 0 :=
    fun μ ν h => by simp [coordVec, h.ne]
  have hdot' : ∀ μ ν : Fin 4, μ < ν → coordVec ν ⬝ᵥ coordVec μ = 0 :=
    fun μ ν h => by simp [coordVec, h.ne']
  have hone : ∀ μ : Fin 4, coordVec μ ⬝ᵥ coordVec μ = 1 := fun μ => by
    simp [coordVec]
  have half : ∀ w : AmbientSpace, (2 : ℝ) • ((2 : ℝ)⁻¹ • w) = w := fun w => by
    rw [smul_smul]; norm_num
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, ν, hlt, rfl | rfl⟩
  · rw [dualVector, normSq_eq_dotProduct, hone, inv_one, one_smul, two_smul]
    exact add_mem (hc μ) (hc μ)
  · have : (coordVec μ + coordVec ν) ⬝ᵥ (coordVec μ + coordVec ν) = 2 := by
      simp only [add_dotProduct, dotProduct_add, hone, hdot μ ν hlt, hdot' μ ν hlt]
      norm_num
    rw [dualVector, normSq_eq_dotProduct, this, half]
    exact add_mem (hc μ) (hc ν)
  · have : (coordVec μ - coordVec ν) ⬝ᵥ (coordVec μ - coordVec ν) = 2 := by
      simp only [sub_dotProduct, dotProduct_sub, hone, hdot μ ν hlt, hdot' μ ν hlt]
      norm_num
    rw [dualVector, normSq_eq_dotProduct, this, half]
    exact sub_mem (hc μ) (hc ν)
theorem two_mul_smul_mem_evenLattice (t : ℤ) {w : AmbientSpace} (hw : w ∈ latticeSubgroup 1) :
    (2 * (t : ℝ)) • w ∈ evenLattice := by
  obtain ⟨m, hm⟩ := hw
  refine ⟨t • m, fun μ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hm μ, Pi.smul_apply, Int.cast_mul]
  ring
theorem finiteIndex_addSubgroupOf_latticeSubgroup {H : AddSubgroup AmbientSpace} {N : ℕ}
    (hN : N ≠ 0) (h : ∀ x : LatticePoint 1, (N : ℝ) • (x : AmbientSpace) ∈ H) :
    (H.addSubgroupOf (latticeSubgroup 1)).FiniteIndex := by
  let e : (Fin 4 → ℤ) →+ LatticePoint 1 :=
    { toFun := fun m => ⟨fun μ => (m μ : ℝ) * 1, m, fun _ => rfl⟩
      map_zero' := Subtype.ext (funext fun μ => by simp)
      map_add' := fun m m' => Subtype.ext (funext fun μ => by simp) }
  have he : Function.Surjective e := by
    rintro ⟨x, m, hm⟩
    exact ⟨m, Subtype.ext (funext fun μ => (hm μ).symm)⟩
  have : AddGroup.FG (LatticePoint 1) := AddGroup.fg_of_surjective he
  have htorsion : IsAddTorsion (LatticePoint 1 ⧸ H.addSubgroupOf (latticeSubgroup 1)) := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have : ((N • x : LatticePoint 1) : AmbientSpace) = (N : ℝ) • (x : AmbientSpace) := by
      rw [AddSubgroup.coe_nsmul, Nat.cast_smul_eq_nsmul]
    rw [this]
    exact h x
  have : Finite (LatticePoint 1 ⧸ H.addSubgroupOf (latticeSubgroup 1)) :=
    AddCommGroup.finite_of_fg_isAddTorsion _ htorsion
  exact AddSubgroup.finiteIndex_of_finite_quotient
theorem measurable_pullbackField_image (r : LatticeSymmetry 1) (S : Set AmbientSpace) :
    @Measurable _ _ (regionSigma (r.toFun '' S)) (regionSigma S) r.pullbackField := by
  rw [measurable_iff_le_map]
  refine iSup₂_le fun b hb => ?_
  rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp,
    ← MeasurableSpace.comap_le_iff_le_map]
  exact le_iSup₂_of_le (r.linkMap b) ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩ le_rfl
theorem continuous_pullbackField (r : LatticeSymmetry 1) : Continuous r.pullbackField := by
  have hval : Continuous fun U : GaugeField 1 => (U.1 : Link 1 → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_subtype_val
  exact Continuous.subtype_mk
    (f := fun U : GaugeField 1 => fun b => U.1 (r.linkMap b))
    (continuous_pi fun b => (continuous_apply _).comp hval) fun U => (r.pullbackField U).2
theorem actOn_mem_continuousLocalFunctions (r : LatticeSymmetry 1)
    (hr : Continuous r.toFun) {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    r.actOn F ∈ continuousLocalFunctions 1 := by
  have hr' := continuous_pullbackField r
  obtain ⟨⟨hb, C, hC⟩, ⟨S, hS, hm⟩, hc⟩ := hF
  refine ⟨⟨hb.comp hr'.measurable, C, fun U => hC _⟩, ⟨r.toFun '' S, ?_, ?_⟩, hc.comp hr'⟩
  · obtain ⟨R, hR⟩ := hS.subset_closedBall 0
    exact ((isCompact_closedBall 0 R).image hr).isBounded.subset (Set.image_mono hR)
  · exact Measurable.comp hm (measurable_pullbackField_image r S)
theorem continuous_reflectAcross (n : AmbientSpace) (c : ℝ) : Continuous (reflectAcross n c) := by
  unfold reflectAcross
  exact continuous_id.sub ((continuous_const.mul
    ((continuous_const.dotProduct continuous_id).sub continuous_const)).smul continuous_const)
namespace MirrorLadder
variable (L : MirrorLadder)
def axialSublattice : AddSubgroup (LatticePoint 1) :=
  (axialPeriodLattice L.normal L.spacing).addSubgroupOf (latticeSubgroup 1)
def normalSublattice : AddSubgroup (LatticePoint 1) :=
  (normalPeriodLattice L.normal L.spacing).addSubgroupOf (latticeSubgroup 1)
theorem exists_natCast_eq_two_mul_spacing :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℝ) = 2 * (L.spacing : ℝ) := by
  have h := L.two_le_spacing
  refine ⟨(2 * L.spacing).toNat, by omega, ?_⟩
  have : ((2 * L.spacing).toNat : ℤ) = 2 * L.spacing := Int.toNat_of_nonneg (by omega)
  exact_mod_cast this
theorem finiteIndex_axialSublattice : L.axialSublattice.FiniteIndex := by
  obtain ⟨N, hN, hNh⟩ := L.exists_natCast_eq_two_mul_spacing
  refine finiteIndex_addSubgroupOf_latticeSubgroup hN fun x => ?_
  obtain ⟨k, hk⟩ := exists_int_dotProduct_latticePoint L.normal_mem x
  have hb := dotProduct_firstNonzeroBasisVec L.normal_mem
  set b := firstNonzeroBasisVec L.normal with hbdef
  have hw : (x : AmbientSpace) - k • b ∈ latticeSubgroup 1 :=
    sub_mem x.2 (zsmul_mem (firstNonzeroBasisVec_mem_latticeSubgroup _) k)
  refine mem_axialPeriodLattice_iff.mpr ⟨(2 * (L.spacing : ℝ)) • ((x : AmbientSpace) - k • b),
    AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩, 2 * k, ?_⟩
  · exact two_mul_smul_mem_evenLattice L.spacing hw
  · change L.normal ⬝ᵥ _ = 0
    rw [dotProduct_smul, dotProduct_sub, dotProduct_smul, hk, hb]
    simp
  · rw [hNh, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_sub, smul_smul, smul_smul]
    push_cast
    rw [show 2 * (k : ℝ) * (L.spacing : ℝ) = 2 * (L.spacing : ℝ) * (k : ℝ) by ring]
    abel
theorem two_mul_spacing_smul_dualVector_mem :
    (2 * (L.spacing : ℝ)) • dualVector L.normal ∈ evenLattice := by
  obtain ⟨t, ht⟩ := L.even_spacing
  have := two_mul_smul_mem_evenLattice t (two_smul_dualVector_mem_latticeSubgroup L.normal_mem)
  rw [smul_smul] at this
  rw [ht]
  push_cast
  rwa [show 2 * ((t : ℝ) + (t : ℝ)) = 2 * (t : ℝ) * 2 by ring]
theorem finiteIndex_normalSublattice : L.normalSublattice.FiniteIndex := by
  obtain ⟨N, hN, hNh⟩ := L.exists_natCast_eq_two_mul_spacing
  refine finiteIndex_addSubgroupOf_latticeSubgroup hN fun x => ?_
  obtain ⟨k, hk⟩ := exists_int_dotProduct_latticePoint L.normal_mem x
  have hn := dotProduct_dualVector L.normal_mem
  have hm := L.two_mul_spacing_smul_dualVector_mem
  set g := (2 * (L.spacing : ℝ)) • dualVector L.normal with hg
  have hx : (2 * (L.spacing : ℝ)) • (x : AmbientSpace) ∈ evenLattice :=
    two_mul_smul_mem_evenLattice L.spacing x.2
  refine mem_normalPeriodLattice_iff.mpr
    ⟨(2 * (L.spacing : ℝ)) • (x : AmbientSpace) - k • g,
      AddSubgroup.mem_inf.mpr ⟨sub_mem hx (zsmul_mem hm k), ?_⟩, k, ?_⟩
  · change L.normal ⬝ᵥ _ = 0
    rw [dotProduct_sub, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, dotProduct_smul, hg,
      dotProduct_smul, hk, hn]
    simp only [smul_eq_mul]
    ring
  · rw [hNh]
    abel
def upperWallOfSlabZero : NormalLevelPair 1 where
  normal := L.normal
  normal_mem := L.normal_mem
  level := L.offset + (L.spacing : ℝ)
  allowed := by
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨k, hk⟩ := L.offset_allowed.1 hq
      exact ⟨k + 2 * L.spacing, by rw [hk]; push_cast; ring⟩
    · obtain ⟨k, hk⟩ := L.offset_allowed.2 hq
      exact ⟨k + L.spacing, by rw [hk]; push_cast; ring⟩
structure SlabZeroGenerator where
  toFun : GaugeField 1 → ℂ
  mem_continuousLocal : toFun ∈ continuousLocalFunctions 1
  im_eq_zero : ∀ U, (toFun U).im = 0
  supportLiesIn : SupportLiesIn toFun (L.slab 0)
variable {L}
variable (A : L.SlabZeroGenerator)
def SlabZeroGenerator.reflected : GaugeField 1 → ℂ :=
  L.upperWallOfSlabZero.reflectObservable A.toFun
theorem SlabZeroGenerator.reflected_mem : A.reflected ∈ continuousLocalFunctions 1 :=
  actOn_mem_continuousLocalFunctions _ (continuous_reflectAcross _ _) A.mem_continuousLocal
theorem SlabZeroGenerator.reflected_im (U : GaugeField 1) : (A.reflected U).im = 0 :=
  A.im_eq_zero _
def SlabZeroGenerator.unfoldedArray : LocalObservableArray where
  sublattice := L.axialSublattice
  sublattice_finiteIndex := L.finiteIndex_axialSublattice
  size := 1
  one_le_size := le_rfl
  gen := fun _ => A.toFun
  gen_mem := fun _ => A.mem_continuousLocal
  gen_im := fun _ => A.im_eq_zero
def SlabZeroGenerator.foldedArray : LocalObservableArray where
  sublattice := L.normalSublattice
  sublattice_finiteIndex := L.finiteIndex_normalSublattice
  size := 2
  one_le_size := by norm_num
  gen := ![A.toFun, A.reflected]
  gen_mem := by
    intro ι
    fin_cases ι
    · exact A.mem_continuousLocal
    · exact A.reflected_mem
  gen_im := by
    intro ι
    fin_cases ι
    · exact A.im_eq_zero
    · exact A.reflected_im
def UnfoldedLabelInSlab (i : A.unfoldedArray.Label) (k : ℤ) : Prop :=
  ∃ y ∈ parallelPeriodLattice L.normal,
    ((i.1 : LatticePoint 1) : AmbientSpace) =
      y + ((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal
def FoldedLabelInSlab (i : A.foldedArray.Label) (k : ℤ) : Prop :=
  ∃ a : ℤ, ∃ y ∈ parallelPeriodLattice L.normal,
    ((i.1 : LatticePoint 1) : AmbientSpace) =
        y + (2 * (a : ℝ) * (L.spacing : ℝ)) • dualVector L.normal ∧
      k = 2 * a + (i.2 : ℕ)
theorem spacing_ne_zero (L : MirrorLadder) : (L.spacing : ℝ) ≠ 0 := by
  have h := L.two_le_spacing
  exact_mod_cast (by omega : L.spacing ≠ 0)
theorem dotProduct_eq_zero_of_mem_parallelPeriodLattice {n y : AmbientSpace}
    (hy : y ∈ parallelPeriodLattice n) : n ⬝ᵥ y = 0 :=
  (AddSubgroup.mem_inf.mp hy).2
theorem exists_unfoldedLabelInSlab (i : A.unfoldedArray.Label) :
    ∃ k, UnfoldedLabelInSlab A i k := by
  have hmem : ((i.1 : LatticePoint 1) : AmbientSpace) ∈ axialPeriodLattice L.normal L.spacing :=
    AddSubgroup.mem_addSubgroupOf.mp i.1.2
  obtain ⟨y, hy, j, hyj⟩ := mem_axialPeriodLattice_iff.mp hmem
  refine ⟨j, y, hy, ?_⟩
  rw [← hyj, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
theorem exists_foldedLabelInSlab (i : A.foldedArray.Label) :
    ∃ k, FoldedLabelInSlab A i k := by
  have hmem : ((i.1 : LatticePoint 1) : AmbientSpace) ∈ normalPeriodLattice L.normal L.spacing :=
    AddSubgroup.mem_addSubgroupOf.mp i.1.2
  obtain ⟨y, hy, j, hyj⟩ := mem_normalPeriodLattice_iff.mp hmem
  refine ⟨2 * j + (i.2 : ℕ), j, y, hy, ?_, rfl⟩
  rw [← hyj, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  congr 2
  ring
theorem unfoldedLabelInSlab_iff (i : A.unfoldedArray.Label) (k : ℤ) :
    UnfoldedLabelInSlab A i k ↔
      (k : ℝ) = L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) := by
  have hslab : ∀ j, UnfoldedLabelInSlab A i j →
      (j : ℝ) = L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) := by
    rintro j ⟨y, hy, hv⟩
    rw [hv, dotProduct_add, dotProduct_eq_zero_of_mem_parallelPeriodLattice hy, dotProduct_smul,
      dotProduct_firstNonzeroBasisVec L.normal_mem, smul_eq_mul, mul_one, zero_add,
      mul_div_cancel_right₀ _ (spacing_ne_zero L)]
  refine ⟨hslab k, fun hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_unfoldedLabelInSlab A i
  have : k = j := by exact_mod_cast hk.trans (hslab j hj).symm
  rwa [this]
theorem foldedLabelInSlab_iff (i : A.foldedArray.Label) (k : ℤ) :
    FoldedLabelInSlab A i k ↔
      (k : ℝ) = L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) +
        ((i.2 : ℕ) : ℝ) := by
  have hslab : ∀ j, FoldedLabelInSlab A i j →
      (j : ℝ) = L.normal ⬝ᵥ ((i.1 : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) +
        ((i.2 : ℕ) : ℝ) := by
    rintro j ⟨a, y, hy, hv, rfl⟩
    rw [hv, dotProduct_add, dotProduct_eq_zero_of_mem_parallelPeriodLattice hy, dotProduct_smul,
      dotProduct_dualVector L.normal_mem, smul_eq_mul, mul_one, zero_add,
      mul_div_cancel_right₀ _ (spacing_ne_zero L)]
    push_cast
    ring
  refine ⟨hslab k, fun hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_foldedLabelInSlab A i
  have : k = j := by exact_mod_cast hk.trans (hslab j hj).symm
  rwa [this]
structure IsAdaptedTorus (L : MirrorLadder) (Γ : PeriodSublattice 1) (J : ℕ) : Prop where
  one_le : 1 ≤ J
  le_normalSublattice : Γ.periods ≤ L.normalSublattice
  splits : Γ.SplitsAlongWithHalfPeriod L.normal ((J : ℤ) * L.spacing)
def TermInSlabClass (𝔸 : LocalObservableArray) (inSlab : 𝔸.Label → ℤ → Prop)
    (Γ : PeriodSublattice 1) (J : ℕ) (c : 𝔸.Cosets Γ × Fin 𝔸.size) (r : ZMod (2 * J)) : Prop :=
  ∃ (v : 𝔸.sublattice) (k : ℤ), (v : 𝔸.Cosets Γ) = c.1 ∧ inSlab (v, c.2) k ∧
    (k : ZMod (2 * J)) = r
theorem IsAdaptedTorus.exists_dotProduct_eq {Γ : PeriodSublattice 1} {J : ℕ}
    (hΓ : L.IsAdaptedTorus Γ J) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    ∃ m : ℤ, L.normal ⬝ᵥ (γ : AmbientSpace) = (m : ℝ) * (2 * (J : ℝ) * (L.spacing : ℝ)) := by
  obtain ⟨-, -, P, hP⟩ := hΓ.splits
  have hmem : (γ : AmbientSpace) ∈ Γ.toAmbient := ⟨γ, hγ, rfl⟩
  rw [← hP.sup_eq, AddSubgroup.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  have hy0 : L.normal ⬝ᵥ y = 0 := hP.height_eq_zero y hy
  have hs : ReflectionPositivity.NormalPlanes.normalOverNormSq L.normal = dualVector L.normal := by
    rw [dualVector, normSq_eq_dotProduct]
    rfl
  refine ⟨m, ?_⟩
  rw [← hyz, dotProduct_add, hy0, zero_add, hs, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul,
    dotProduct_smul, dotProduct_dualVector L.normal_mem]
  simp only [smul_eq_mul, mul_one]
  push_cast
  ring
theorem IsAdaptedTorus.intCast_slab_eq {Γ : PeriodSublattice 1} {J : ℕ}
    (hΓ : L.IsAdaptedTorus Γ J) (𝔸 : LocalObservableArray) {v v' : 𝔸.sublattice}
    (hv : (v : 𝔸.Cosets Γ) = v') {k k' : ℤ} {s : ℝ}
    (hk : (k : ℝ) = L.normal ⬝ᵥ ((v : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) + s)
    (hk' : (k' : ℝ) = L.normal ⬝ᵥ ((v' : LatticePoint 1) : AmbientSpace) / (L.spacing : ℝ) + s) :
    (k : ZMod (2 * J)) = k' := by
  have hmem : (((-v + v' : 𝔸.sublattice)) : LatticePoint 1) ∈ Γ.periods :=
    AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp hv)
  obtain ⟨m, hm⟩ := hΓ.exists_dotProduct_eq hmem
  have hd : L.normal ⬝ᵥ ((v' : LatticePoint 1) : AmbientSpace) -
      L.normal ⬝ᵥ ((v : LatticePoint 1) : AmbientSpace) =
      (m : ℝ) * (2 * (J : ℝ) * (L.spacing : ℝ)) := by
    rw [← hm]
    simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, dotProduct_add, dotProduct_neg]
    ring
  have hne := spacing_ne_zero L
  have hr : (k' : ℝ) - k = (m : ℝ) * (2 * (J : ℝ)) := by
    rw [hk, hk', add_sub_add_right_eq_sub, ← sub_div, hd]
    field_simp
  have hz : k' - k = ((2 * J : ℕ) : ℤ) * m := by
    have : ((k' - k : ℤ) : ℝ) = (((2 * J : ℕ) : ℤ) * m : ℤ) := by
      push_cast
      rw [hr]
      ring
    exact_mod_cast this
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub k k' (2 * J)).mpr ⟨m, hz⟩
theorem termInSlabClass_folded_iff {Γ : PeriodSublattice 1} {J : ℕ}
    (hΓ : L.IsAdaptedTorus Γ J) (c : A.foldedArray.Cosets Γ × Fin A.foldedArray.size)
    (r : ZMod (2 * J)) {v : A.foldedArray.sublattice} (hv : (v : A.foldedArray.Cosets Γ) = c.1)
    {k : ℤ} (hk : FoldedLabelInSlab A (v, c.2) k) :
    TermInSlabClass A.foldedArray (FoldedLabelInSlab A) Γ J c r ↔
      (k : ZMod (2 * J)) = r := by
  refine ⟨?_, fun h => ⟨v, k, hv, hk, h⟩⟩
  rintro ⟨v', k', hv', hk', rfl⟩
  exact hΓ.intCast_slab_eq A.foldedArray (hv.trans hv'.symm)
    ((foldedLabelInSlab_iff A _ _).mp hk) ((foldedLabelInSlab_iff A _ _).mp hk')
end MirrorLadder
end NormalFamilies
end YangMills.Construction
