import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import YangMills.Construction.TransferOperators.InsertedOperatorsOfABlockAreContractionsProof
import YangMills.Construction.TransferOperators.IntegrandOfAnInsertionIsAProductOfKernels
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergy
import YangMills.Construction.TransferOperators.TorusWeightIsAProductOverLayers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory InfiniteLattice SpinHarmonics
open scoped ComplexOrder
noncomputable section
namespace TransferOperators.ExpShiftIntegrand
variable {μ : Fin 4}
theorem linkClass_translate (L : PeriodSublattice 1) (p : PositiveLink 1) {δ : LatticePoint 1}
    (hδ : δ ∈ L.periods) : L.linkClass (p.translate δ) = L.linkClass p := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.linkClass_translate <;> assumption
theorem level_zsmul_axisStep (ν : Fin 4) (n : ℤ) :
    level ν (n • axisStep 1 μ) = if ν = μ then n else 0 := by
  have h : ((level ν (n • axisStep 1 μ) : ℤ) : ℝ) = ((if ν = μ then n else 0 : ℤ) : ℝ) := by
    rw [level_cast]
    change n • (Pi.single μ (1 : ℝ) : AmbientSpace) ν = _
    by_cases e : ν = μ
    · subst e
      simp
    · simp [e]
  exact_mod_cast h
theorem zsmul_axisStep_mem_periods (Γ : CubicPeriodSublattice) {n : ℤ}
    (hn : ((n : ℤ) : ZMod Γ.side) = 0) :
    n • axisStep 1 μ ∈ Γ.lattice.periods := by
  have h := Γ.sub_mem_periods (x := 0) (x' := n • axisStep 1 μ) fun ν => by
    have h₀ : level ν (0 : LatticePoint 1) = 0 := by
      apply Int.cast_injective (α := ℝ)
      rw [level_cast]
      simp
    rw [h₀, level_zsmul_axisStep]
    split_ifs
    · simp [hn]
    · simp
  simpa using h
theorem cast_sub_levelRep (Γ : CubicPeriodSublattice) (j : ℤ) :
    (((j - CubicPeriodSublattice.levelRep Γ (Γ.levelClass j) : ℤ)) : ZMod Γ.side) = 0 := by
  simp [CubicPeriodSublattice.levelRep, CubicPeriodSublattice.levelClass]
theorem spatialQuotientLink_eq (Γ : CubicPeriodSublattice) (j : ℤ) (b : SliceLink μ) :
    Γ.spatialQuotientLink (Γ.levelClass j) (Γ.linkClass b) =
      Γ.lattice.linkClass (spatialLink μ j b) := by
  obtain ⟨γ, hγ, hb⟩ := Γ.mem_linkOrbit_linkRep b
  set b₀ := CubicPeriodSublattice.linkRep (Γ.linkClass b) with hb₀
  set r := Γ.levelRep (Γ.levelClass j) with hr
  have hmem : γ + (j - r) • axisStep 1 μ ∈ Γ.lattice.periods :=
    add_mem (AddSubgroup.mem_inf.mp hγ).1 (zsmul_axisStep_mem_periods Γ (cast_sub_levelRep Γ j))
  have ht : (b.source : LatticePoint 1) = (b₀.source : LatticePoint 1) + γ :=
    congrArg (fun l : Link 1 => l.initial) hb
  have hh : (b.target : LatticePoint 1) = (b₀.target : LatticePoint 1) + γ :=
    congrArg (fun l : Link 1 => l.terminal) hb
  have key : spatialLink μ j b =
      (spatialLink μ r b₀).translate (γ + (j - r) • axisStep 1 μ) := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change pointAtLevel μ j b.source = pointAtLevel μ r b₀.source + (γ + (j - r) • axisStep 1 μ)
      simp only [pointAtLevel, sub_smul]
      rw [ht]
      abel
    · change pointAtLevel μ j b.target = pointAtLevel μ r b₀.target + (γ + (j - r) • axisStep 1 μ)
      simp only [pointAtLevel, sub_smul]
      rw [hh]
      abel
  rw [key, linkClass_translate _ _ hmem]
  rfl
theorem temporalQuotientLink_eq (Γ : CubicPeriodSublattice) (j : ℤ) (y : SliceSite μ) :
    Γ.temporalQuotientLink (Γ.levelClass j) (Γ.vertexClass y) =
      Γ.lattice.linkClass (temporalLink μ j y) := by
  have hrep : Γ.vertexOrbit μ (CubicPeriodSublattice.vertexRep (Γ.vertexClass y)) =
      Γ.vertexOrbit μ y := (Γ.vertexClass y).2.choose_spec
  have hy : y ∈ Γ.vertexOrbit μ (CubicPeriodSublattice.vertexRep (Γ.vertexClass y)) := by
    rw [hrep]
    exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨γ, hγ, hy'⟩ := hy
  set y₀ := CubicPeriodSublattice.vertexRep (Γ.vertexClass y) with hy₀
  set r := Γ.levelRep (Γ.levelClass j) with hr
  have hmem : γ + (j - r) • axisStep 1 μ ∈ Γ.lattice.periods :=
    add_mem (AddSubgroup.mem_inf.mp hγ).1 (zsmul_axisStep_mem_periods Γ (cast_sub_levelRep Γ j))
  have key : temporalLink μ j y =
      (temporalLink μ r y₀).translate (γ + (j - r) • axisStep 1 μ) := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · change pointAtLevel μ j y = pointAtLevel μ r y₀ + (γ + (j - r) • axisStep 1 μ)
      simp only [pointAtLevel, sub_smul]
      rw [hy']
      abel
    · change pointAtLevel μ (j + 1) y = pointAtLevel μ (r + 1) y₀ + (γ + (j - r) • axisStep 1 μ)
      simp only [pointAtLevel, sub_smul, add_smul, one_smul]
      rw [hy']
      abel
  rw [key, linkClass_translate _ _ hmem]
  rfl
theorem pointAtLevel_add (i : ℤ) (y : SliceSite μ) (v : LatticePoint 1) :
    pointAtLevel μ i y + v =
      pointAtLevel μ (i + level μ v) (y + slicePart μ v) := by
  change i • axisStep 1 μ + (y : LatticePoint 1) + v = (i + level μ v) • axisStep 1 μ +
    ((y : LatticePoint 1) + (v - level μ v • axisStep 1 μ))
  rw [add_smul]
  abel
theorem lift_apply_positive (L : PeriodSublattice 1) (U : L.QuotientField)
    (p : PositiveLink 1) : (L.lift U).1 p.1 = U (L.linkClass p) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.lift_apply_positive <;> assumption
theorem spatialLinkVariable_shift (Γ : CubicPeriodSublattice) (U : Γ.lattice.QuotientField)
    (v : LatticePoint 1) (i : ℤ) (b : SliceLink μ) :
    spatialLinkVariable μ ((shift v).pullbackField (Γ.lattice.lift U)) i b =
      Γ.sliceField (μ := μ) U (Γ.levelClass (i + level μ v))
        (Γ.linkClass (b.translate (slicePart μ v))) := by
  have hlink : (shift v).linkMap (spatialLink μ i b).1 =
      (spatialLink μ (i + level μ v) (b.translate (slicePart μ v))).1 := by
    refine InfiniteLattice.Link.ext ?_ ?_
    · exact pointAtLevel_add i b.source v
    · exact pointAtLevel_add i b.target v
  change (Γ.lattice.lift U).1 ((shift v).linkMap (spatialLink μ i b).1) = _
  rw [hlink, lift_apply_positive]
  change _ = U (Γ.spatialQuotientLink _ _)
  rw [spatialQuotientLink_eq]
theorem temporalLinkVariable_shift (Γ : CubicPeriodSublattice) (U : Γ.lattice.QuotientField)
    (v : LatticePoint 1) (i : ℤ) (y : SliceSite μ) :
    temporalLinkVariable μ ((shift v).pullbackField (Γ.lattice.lift U)) i y =
      Γ.temporalSliceField (μ := μ) U (Γ.levelClass (i + level μ v))
        (Γ.vertexClass (y + slicePart μ v)) := by
  have hlink : (shift v).linkMap (temporalLink μ i y).1 =
      (temporalLink μ (i + level μ v) (y + slicePart μ v)).1 := by
    refine InfiniteLattice.Link.ext ?_ ?_
    · exact pointAtLevel_add i y v
    · have h := pointAtLevel_add (i + 1) y v
      rw [add_right_comm] at h
      exact h
  change (Γ.lattice.lift U).1 ((shift v).linkMap (temporalLink μ i y).1) = _
  rw [hlink, lift_apply_positive]
  change _ = U (Γ.temporalQuotientLink _ _)
  rw [temporalQuotientLink_eq]
theorem parallelTransport_bottom (U : GaugeField 1) (i : ℤ) (y : SliceSite μ) :
    (⟨i, i + 1, lt_add_one i⟩ : Stack).parallelTransport μ U i y = 1 := by
  simp [Stack.parallelTransport]
theorem parallelTransport_top (U : GaugeField 1) (i : ℤ) (y : SliceSite μ) :
    (⟨i, i + 1, lt_add_one i⟩ : Stack).parallelTransport μ U (i + 1) y =
      temporalLinkVariable μ U i y := by
  simp [Stack.parallelTransport]
theorem translate_source (b : SliceLink μ) (z : SliceSite μ) :
    (b.translate z).source = b.source + z := rfl
theorem translate_target (b : SliceLink μ) (z : SliceSite μ) :
    (b.translate z).target = b.target + z := rfl
theorem transportedRestriction_bottom (Γ : CubicPeriodSublattice) (B : Block μ)
    (U : Γ.lattice.QuotientField) (v : LatticePoint 1) (i : ℤ) :
    (⟨i, i + 1, lt_add_one i⟩ : Stack).transportedRestriction μ
        ((shift v).pullbackField (Γ.lattice.lift U)) i
        (B.links : Set (SliceLink μ)) =
      fun b => Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v) (Γ.blockCopy B v b) := by
  funext b
  simp only [Stack.transportedRestriction, Stack.transportedLinkVariable, parallelTransport_bottom,
    one_mul, inv_one, mul_one]
  exact spatialLinkVariable_shift Γ U v i b.1
theorem transportedRestriction_top (Γ : CubicPeriodSublattice) (B : Block μ)
    (U : Γ.lattice.QuotientField) (v : LatticePoint 1) (i : ℤ) :
    (⟨i, i + 1, lt_add_one i⟩ : Stack).transportedRestriction μ
        ((shift v).pullbackField (Γ.lattice.lift U)) (i + 1)
        (B.links : Set (SliceLink μ)) =
      fun b => Γ.orbitGaugeAct
        (Γ.temporalSliceField (μ := μ) U (Γ.copyLevel μ i v))
        (Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v + 1)) (Γ.blockCopy B v b) := by
  funext b
  have hj : Γ.levelClass (i + 1 + level μ v) = Γ.copyLevel μ i v + 1 := by
    simp only [CubicPeriodSublattice.copyLevel, CubicPeriodSublattice.levelClass]
    push_cast
    ring
  simp only [Stack.transportedRestriction, Stack.transportedLinkVariable, parallelTransport_top,
    temporalLinkVariable_shift, spatialLinkVariable_shift, hj]
  rw [CubicPeriodSublattice.blockCopy, Γ.orbitGaugeAct_linkClass, translate_source,
    translate_target]
  rfl
theorem logKernelRatio_shift (Γ : CubicPeriodSublattice) (B : Block μ) (β : ℝ)
    (Ξ : B.L2Operator) (U : Γ.lattice.QuotientField) (v : LatticePoint 1) (i : ℤ) :
    B.logKernelRatio β Ξ i ((shift v).pullbackField (Γ.lattice.lift U)) =
      Complex.log
        (sqrtKernelSandwich β Ξ
            (fun b => Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v) (Γ.blockCopy B v b))
            (fun b => Γ.orbitGaugeAct
              (Γ.temporalSliceField (μ := μ) U (Γ.copyLevel μ i v))
              (Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v + 1)) (Γ.blockCopy B v b)) /
          linkProductKernel β
            (fun b => Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v) (Γ.blockCopy B v b))
            (fun b => Γ.orbitGaugeAct
              (Γ.temporalSliceField (μ := μ) U (Γ.copyLevel μ i v))
              (Γ.sliceField (μ := μ) U (Γ.copyLevel μ i v + 1)) (Γ.blockCopy B v b))) := by
  simp only [Block.logKernelRatio]
  rw [transportedRestriction_bottom, transportedRestriction_top]
theorem ofReal_exp_re_log_div {k C : ℂ} (hk : 0 < k) (hC : C.im = 0) (hC' : 0 < C.re) :
    ((Real.exp (Complex.log (k / C)).re : ℝ) : ℂ) = k / C := by
  obtain ⟨hk₁, hk₂⟩ := Complex.lt_def.mp hk
  have ek : k = (k.re : ℂ) := Complex.ext rfl (by simpa using hk₂.symm)
  have eC : C = (C.re : ℂ) := Complex.ext rfl (by simpa using hC)
  have hr : 0 < k.re / C.re := div_pos (by simpa using hk₁) hC'
  have e : k / C = ((k.re / C.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← ek, ← eC]
  rw [e, Complex.log_ofReal_re, Real.exp_log hr]
theorem finprod_eq_prod_parts_mul_rest {E : Type} [Finite E] {n : ℕ} (parts : Fin n → Set E)
    (R : Set E) (h : IsPartitionWithRest parts R) (f : E → ℂ) :
    ∏ᶠ b, f b = (∏ t, ∏ᶠ b : ↥(parts t), f b) * ∏ᶠ b : ↥R, f b := by
  have hall : ∏ᶠ b, f b = ∏ᶠ b ∈ (⋃ t, parts t) ∪ R, f b := by
    rw [h.2.2.2, finprod_mem_univ]
  rw [hall, finprod_mem_union (Set.disjoint_iUnion_left.mpr h.2.2.1) (Set.toFinite _)
    (Set.toFinite _), finprod_mem_iUnion h.2.1 (fun _ => Set.toFinite _)]
  simp only [finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]
theorem cosetRep_mem (Γ : CubicPeriodSublattice) {Q' : AddSubgroup (LatticePoint 1)}
    (c : Γ.CosetsMod Q') : Γ.cosetRep c ∈ Q' :=
  (Quotient.out c : Q').2
theorem cosetRep_sub_not_mem (Γ : CubicPeriodSublattice) {Q' : AddSubgroup (LatticePoint 1)}
    {c c' : Γ.CosetsMod Q'} (h : c ≠ c') :
    Γ.cosetRep c - Γ.cosetRep c' ∉ Γ.lattice.periods := by apply _root_.YangMills.Construction.TransferOperators.LevelProductOps.cosetRep_sub_notMem_periods <;> assumption
theorem mem_cosetsAtLevel (Γ : CubicPeriodSublattice) {i : ℤ} {Q' : AddSubgroup (LatticePoint 1)}
    {j : ZMod Γ.side} {c : Γ.CosetsMod Q'} :
    c ∈ Γ.cosetsAtLevel μ i Q' j ↔ Γ.copyLevel μ i (Γ.cosetRep c) = j := by
  simp [CubicPeriodSublattice.cosetsAtLevel]
theorem sqrtKernelSandwich_levelProductOp
    (hP : SandwichKernelProductStatement)
    (hF : SandwichKernelRelabelStatement)
    (hK : KernelSymmetryAndGaugeInvariance.Statement)
    {β : ℝ} (hβ : 0 < β) (Γ : CubicPeriodSublattice) (B : Block μ) (Ξ : B.L2Operator) {i : ℤ}
    {Q' : AddSubgroup (LatticePoint 1)} (hC : Γ.BlockCopiesDisjoint B i Q') (j : ZMod Γ.side)
    (u w : Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    sqrtKernelSandwich β (Γ.levelProductOp B Ξ i Q' j) u w =
      linkProductKernel β u w * ∏ c ∈ Γ.cosetsAtLevel μ i Q' j,
        (sqrtKernelSandwich β Ξ (fun b => u (Γ.blockCopy B (Γ.cosetRep c) b))
            (fun b => w (Γ.blockCopy B (Γ.cosetRep c) b)) /
          linkProductKernel β (fun b => u (Γ.blockCopy B (Γ.cosetRep c) b))
            (fun b => w (Γ.blockCopy B (Γ.cosetRep c) b))) := by
  have : Nonempty ↥(B.links : Set (SliceLink μ)) := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨⟨b, hb⟩⟩
  have : Nonempty (Γ.LinkOrbits μ) := by
    obtain ⟨b⟩ := ‹Nonempty ↥(B.links : Set (SliceLink μ))›
    exact ⟨Γ.linkClass b.1⟩
  set L := (Γ.cosetsAtLevel μ i Q' j).toList with hL
  have hnd : L.Nodup := Finset.nodup_toList _
  have hmemL : ∀ t : Fin L.length, L.get t ∈ Γ.cosetsAtLevel μ i Q' j := fun t =>
    (Finset.mem_toList).mp (List.get_mem L t)
  let v : Fin L.length → LatticePoint 1 := fun t => Γ.cosetRep (L.get t)
  let parts : Fin L.length → Set (Γ.LinkOrbits μ) := fun t => Γ.blockCopyRange B (v t)
  let Xs : ∀ t, HaarL2 ↥(parts t) →L[ℂ] HaarL2 ↥(parts t) :=
    fun t => Γ.operatorCopy B Ξ (v t)
  let R : Set (Γ.LinkOrbits μ) := (⋃ t, parts t)ᶜ
  have hdu : IsPartitionWithRest parts R := by
    refine ⟨fun t => Set.range_nonempty _, ?_, ?_, Set.union_compl_self _⟩
    · intro t t' htt
      have hne : L.get t ≠ L.get t' := fun e => htt (hnd.get_inj_iff.mp e)
      refine hC.2.2 (v t) (cosetRep_mem Γ _) (v t') (cosetRep_mem Γ _)
        (cosetRep_sub_not_mem Γ hne) ?_
      rw [(mem_cosetsAtLevel Γ).mp (hmemL t), (mem_cosetsAtLevel Γ).mp (hmemL t')]
    · intro t
      exact Set.disjoint_left.mpr fun x hx hR => hR (Set.mem_iUnion.mpr ⟨t, hx⟩)
  have hop : Γ.levelProductOp B Ξ i Q' j = tensorOneProduct parts Xs := by
    unfold CubicPeriodSublattice.levelProductOp tensorOneProduct
    congr 1
    conv_lhs => rw [← hL, ← List.ofFn_get L, List.map_ofFn]
    rfl
  have hbij : ∀ t, Function.Bijective (Set.rangeFactorization (Γ.blockCopy B (v t))) := fun t =>
    ⟨fun x y h => hC.2.1 (v t) (cosetRep_mem Γ _) (congrArg Subtype.val h),
      Set.rangeFactorization_surjective⟩
  have hfac : ∀ t, sqrtKernelSandwich β (Xs t) (restrictTo (parts t) u)
      (restrictTo (parts t) w) =
      sqrtKernelSandwich β Ξ (fun b => u (Γ.blockCopy B (v t) b))
        (fun b => w (Γ.blockCopy B (v t) b)) :=
    fun t => (hF β hβ _ _ _ Ξ (hbij t)).2.2.2.2 _ _
  have hbk : ∀ t, ∏ᶠ b : ↥(parts t), singleBondWeight β (u b * (w b)⁻¹) =
      linkProductKernel β (fun b => u (Γ.blockCopy B (v t) b))
        (fun b => w (Γ.blockCopy B (v t) b)) :=
    fun t => (finprod_eq_of_bijective _ (hbij t) fun _ => rfl).symm
  have hne : ∀ t, linkProductKernel β (fun b => u (Γ.blockCopy B (v t) b))
      (fun b => w (Γ.blockCopy B (v t) b)) ≠ 0 := by
    intro t h
    have h₁ := ((hK β hβ).1 ↥(B.links : Set (SliceLink μ))).1
      (fun b => u (Γ.blockCopy B (v t) b)) (fun b => w (Γ.blockCopy B (v t) b))
    have h₂ := h₁.2.2.1
    rw [h] at h₂
    exact absurd h₂ (not_le.mpr (by simpa using Real.exp_pos _))
  have hlist : ∀ g : Γ.CosetsMod Q' → ℂ, ∏ c ∈ Γ.cosetsAtLevel μ i Q' j, g c =
      ∏ t : Fin L.length, g (L.get t) := by
    intro g
    rw [← Finset.prod_map_toList, ← hL, ← List.prod_ofFn]
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn]
    rfl
  rw [hop, (hP β hβ (Γ.LinkOrbits μ) L.length parts R Xs hdu).2 u w, linkProductKernel,
    finprod_eq_prod_parts_mul_rest parts R hdu, hlist]
  simp only [hfac, hbk]
  rw [Finset.prod_div_distrib]
  have hne' : ∏ t : Fin L.length, linkProductKernel β (fun b => u (Γ.blockCopy B (v t) b))
      (fun b => w (Γ.blockCopy B (v t) b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hne t
  have halg : ∀ a c r : ℂ, c ≠ 0 → a * r = c * r * (a / c) := fun a c r h => by
    field_simp
  exact halg _ _ _ hne'
theorem ofReal_exp_cosetSumOfShifts (Γ : CubicPeriodSublattice) (B : Block μ) (β : ℝ)
    (Ξ : B.L2Operator) (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) (U : Γ.lattice.QuotientField)
    (r : Γ.CosetsMod Q' → ℂ)
    (hr : ∀ c, ((Real.exp (Γ.lattice.periodize
      ((shift (Γ.cosetRep c)).actOn (B.logKernelRatio β Ξ i)) U).re : ℝ) : ℂ)
        = r c) [Fintype (Γ.CosetsMod Q')] :
    ((Real.exp (Γ.lattice.cosetSumOfShifts Q' (B.logKernelRatio β Ξ i) U) : ℝ) : ℂ) =
      ∏ c, r c := by
  rw [PeriodSublattice.cosetSumOfShifts, finsum_eq_sum_of_fintype, Real.exp_sum,
    Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun c _ => hr c
theorem prodStatement_holds (hW : BoltzmannWeight.ProdSlicesStatement)
    (hC : BlockCopies.DisjointStatement)
    (hP : SandwichKernelProductStatement)
    (hF : SandwichKernelRelabelStatement)
    (hK : KernelSymmetryAndGaugeInvariance.Statement) : ProdStatement := by
  classical
  intro β hβ μ B Ξ _ _ _ hpos i Q' hQ hD Γ hΓ U
  have hcop := hC μ B i Q' hQ hD Γ hΓ
  have : Nonempty ↥(B.links : Set (SliceLink μ)) := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨⟨b, hb⟩⟩
  let : Fintype (Γ.CosetsMod Q') := Fintype.ofFinite _
  let J : Γ.CosetsMod Q' → ZMod Γ.side := fun c => Γ.copyLevel μ i (Γ.cosetRep c)
  let u : ZMod Γ.side → Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary :=
    fun j => Γ.sliceField (μ := μ) U j
  let w : ZMod Γ.side → Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary := fun j =>
    Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U j)
      (Γ.sliceField (μ := μ) U (j + 1))
  let q : ZMod Γ.side → Γ.CosetsMod Q' → ℂ := fun j c =>
    sqrtKernelSandwich β Ξ (fun b => u j (Γ.blockCopy B (Γ.cosetRep c) b))
        (fun b => w j (Γ.blockCopy B (Γ.cosetRep c) b)) /
      linkProductKernel β (fun b => u j (Γ.blockCopy B (Γ.cosetRep c) b))
        (fun b => w j (Γ.blockCopy B (Γ.cosetRep c) b))
  have hexp : ((Real.exp (Γ.lattice.cosetSumOfShifts Q'
      (B.logKernelRatio β Ξ i) U) : ℝ) : ℂ) = ∏ c, q (J c) c := by
    refine ofReal_exp_cosetSumOfShifts Γ B β Ξ i Q' U _ fun c => ?_
    have hb := ((hK β hβ).1 ↥(B.links : Set (SliceLink μ))).1
      (fun b => u (J c) (Γ.blockCopy B (Γ.cosetRep c) b))
      (fun b => w (J c) (Γ.blockCopy B (Γ.cosetRep c) b))
    change ((Real.exp (B.logKernelRatio β Ξ i
      ((shift (Γ.cosetRep c)).pullbackField
        (Γ.lattice.lift U))).re : ℝ) : ℂ) = _
    rw [logKernelRatio_shift]
    exact ofReal_exp_re_log_div (hpos _ _) hb.2.1 (lt_of_lt_of_le (Real.exp_pos _) hb.2.2.1)
  have hfib : ∏ c, q (J c) c = ∏ j, ∏ c ∈ Γ.cosetsAtLevel μ i Q' j, q j c := by
    rw [← Finset.prod_fiberwise Finset.univ J]
    refine Finset.prod_congr rfl fun j _ => ?_
    refine Finset.prod_congr (Finset.ext fun c => ?_) fun c hc => ?_
    · simp [mem_cosetsAtLevel Γ, J]
    · rw [show J c = j from (mem_cosetsAtLevel Γ).mp hc]
  rw [Complex.ofReal_mul, hexp, hfib, hW β hβ μ Γ U, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sqrtKernelSandwich_levelProductOp hP hF hK hβ Γ B Ξ hcop j]
  ring
end TransferOperators.ExpShiftIntegrand
end
end YangMills.Construction
