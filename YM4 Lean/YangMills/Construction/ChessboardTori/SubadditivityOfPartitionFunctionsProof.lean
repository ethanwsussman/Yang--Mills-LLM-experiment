import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.InducedMaps
import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import YangMills.Construction.ChessboardTori.ReflectionsAndTranslationsOfSlabs
import YangMills.Construction.ChessboardTori.SubadditivityOfPartitionFunctions
import YangMills.Construction.ChessboardTori.TraceFormula
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace SubmultiplicativityProof
variable {D : ChessboardSetup}
def periodSubgroupOf (W : AmbientSpace → ℂ) : AddSubgroup AmbientSpace where
  carrier := {v | ∀ x, W (x + v) = W x}
  zero_mem' := fun x => by simp
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have h := ha (x + -a)
    rw [neg_add_cancel_right] at h
    exact h.symm
theorem two_cellSide_smul_mem (g : ReflectionGrid D) {W : AmbientSpace → ℂ}
    (hW : g.IsReflectionPeriodic W) (μ : Fin 4) :
    (2 * g.cellSide) • coordVec μ ∈ periodSubgroupOf W := by
  intro x
  have h1 := congrFun (hW.2.1 μ 1) (g.reflect μ 0 x)
  have h0 := congrFun (hW.2.1 μ 0) x
  simp only [Function.comp] at h1 h0
  have hcomp : g.reflect μ 1 (g.reflect μ 0 x) = x + (2 * g.cellSide) • coordVec μ := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [ReflectionGrid.reflect, coordVec]
      ring
    · simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h]
  rw [← hcomp, h1, h0]
  simp
theorem mem_periodSubgroupOf (g : ReflectionGrid D) {W : AmbientSpace → ℂ}
    (hW : g.IsReflectionPeriodic W) (v : AmbientSpace)
    (z : Fin 4 → ℤ) (hv : ∀ μ, v μ = (z μ : ℝ) * (2 * g.cellSide)) : v ∈ periodSubgroupOf W := by
  have hsum : v = ∑ μ, z μ • ((2 * g.cellSide) • coordVec μ) := by
    funext ν
    rw [Finset.sum_apply, Finset.sum_eq_single ν]
    · simp [coordVec, hv ν]
    · intro μ _ hμ
      simp [coordVec, Pi.single_eq_of_ne hμ.symm]
    · simp
  rw [hsum]
  exact sum_mem fun μ _ => zsmul_mem (two_cellSide_smul_mem g hW μ) _
theorem periodic_of_boxPeriods (g : ReflectionGrid D) {W : AmbientSpace → ℂ}
    (hW : g.IsReflectionPeriodic W)
    (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (hev : ∀ μ, Even (n μ)) :
    ∀ x, ∀ v ∈ (g.boxPeriods n hn).subgroup, W (x + v) = W x := by
  intro x v hv
  have h : ∀ μ, ∃ k : ℤ, k • (D.periodLengths (g.boxPeriods n hn).mult μ) = v μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hv) μ (mem_univ μ))
  choose k hk using h
  choose c hc using fun μ => (hev μ)
  refine mem_periodSubgroupOf g hW v (fun μ => k μ * c μ) (fun μ => ?_) x
  rw [← hk μ, zsmul_eq_mul]
  change (k μ : ℝ) * (((n μ * g.cellRatio : ℤ) : ℝ) * D.mesh) = _
  rw [g.cellSide_eq, hc μ]
  push_cast
  ring
theorem boxPeriods_congr (g : ReflectionGrid D) {n n' : Fin 4 → ℤ} (hn : ∀ μ, 2 ≤ n μ)
    (hn' : ∀ μ, 2 ≤ n' μ) (h : n = n') : g.boxPeriods n hn = g.boxPeriods n' hn' := by
  subst h
  rfl
theorem isCoordDiagonal_of_reflect (g : ReflectionGrid D) (μ : Fin 4) (κ : ℤ)
    (f : AmbientSpace → AmbientSpace)
    (hf : ∀ x, f x = g.reflect μ κ x) : IsCoordDiagonal (linearComponent f) := by
  have hex : ∃ R, HasLinearComponent f R := by
    refine ⟨LinearMap.id - (LinearMap.toSpanSingleton ℝ AmbientSpace (coordVec μ)).comp
      ((2 : ℝ) • LinearMap.proj μ), (2 * (g.origin μ + κ * g.cellSide)) • coordVec μ,
      fun x => ?_⟩
    rw [hf]
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [ReflectionGrid.reflect, coordVec, LinearMap.toSpanSingleton_apply]
      ring
    · simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h,
        LinearMap.toSpanSingleton_apply]
  obtain ⟨v, hv⟩ : HasLinearComponent f (linearComponent f) := Classical.epsilon_spec hex
  intro ν
  have h0 := hv 0
  have h1 := hv (coordVec ν)
  rw [map_zero, zero_add] at h0
  have h2 : linearComponent f (coordVec ν) =
      g.reflect μ κ (coordVec ν) - g.reflect μ κ 0 := by
    rw [← hf, ← hf, h0, h1]
    simp
  refine ⟨if ν = μ then -1 else 1, ?_⟩
  rw [h2]
  funext ρ
  by_cases h : ν = μ
  · subst h
    by_cases h' : ρ = ν
    · subst h'
      simp [ReflectionGrid.reflect, coordVec]
      ring
    · simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h']
  · by_cases h' : ρ = μ
    · subst h'
      simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne (Ne.symm h)]
    · simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h', h]
theorem descend_mapFace (hI : QuotientMapsStatement) (P : PeriodSubgroup D)
    (r : D.LatticeSym) (hd : IsCoordDiagonal (linearComponent r.toFun))
    {W : AmbientSpace → ℂ}
    (hper : ∀ x, ∀ v ∈ P.subgroup, W (x + v) = W x)
    (hrefl : ∀ x, W (r.toFun x) = starRingEnd ℂ (W x)) (p : P.Face) :
    P.descend W (P.faceCenter (P.mapFace (P.quotientMap r) p)) =
      starRingEnd ℂ (P.descend W (P.faceCenter p)) := by
  obtain ⟨hinv, hact, -, -, -⟩ := (hI D).1 P r ((hI D).2.2.1 P r hd)
  obtain ⟨x, hx⟩ := BoxTorus.projection_surjective P.sideLengths (P.faceCenter p)
  have hx' : P.proj x = P.faceCenter p := hx
  have hind : P.proj (r.toFun x) = P.quotientMap r (P.proj x) := congrFun hinv.1 x
  rw [hact.2.2.2.2.2.2.2 p, ← hx', ← hind, PeriodSubgroup.descend_proj _ hper,
    PeriodSubgroup.descend_proj _ hper, hrefl]
namespace Slab
variable (T : TransferSetup D) (W : AmbientSpace → ℂ)
def faceWeight (m : SlabCount) : (T.torusPeriods m).Face → ℂ :=
  fun p => (T.torusPeriods m).descend W ((T.torusPeriods m).faceCenter p)
def slabKernel (m : SlabCount) : T.SlabConfig → ℂ := T.slabBoltzmann m (faceWeight T W m) 0
variable {T W}
theorem even_cellCounts (hev : ∀ ν, Even (T.transverseCells ν)) {m : SlabCount}
    (hm : Even (m : ℕ)) (ν : Fin 4) : Even (T.cellCounts m ν) := by
  unfold TransferSetup.cellCounts
  split_ifs with h
  · exact_mod_cast hm
  · exact hev _
theorem periodic (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) :
    ∀ x, ∀ v ∈ (T.torusPeriods m).subgroup, W (x + v) = W x :=
  periodic_of_boxPeriods T.grid hW _ _ (even_cellCounts hev hm)
theorem faceWeight_bounded (hW : T.grid.IsReflectionPeriodic W) (m : SlabCount) :
    ∃ C : ℝ, ∀ p, ‖faceWeight T W m p‖ ≤ C := by
  obtain ⟨C, hC⟩ := hW.1
  exact ⟨C, fun p => hC _⟩
theorem faceWeight_crossing (hQ : ProjOnEdgesAndFaces.Statement)
    (hA : TransferAssertions.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (p : (T.torusPeriods m).Face)
    (hp : T.IsCrossingFace m p) : faceWeight T W m p = 0 := by
  obtain ⟨hC, -, -⟩ := hQ D (T.torusPeriods m)
  obtain ⟨-, -, -, -, hCr, -⟩ := hA D T m
  obtain ⟨p', rfl⟩ := hC.2.2.2.1 p
  obtain ⟨b, hb, k, hk⟩ := ((hCr.2.2 p').1).mpr hp
  have h0 : W p'.center = 0 := hW.2.2 p' ⟨b, hb, T.axis, k, hk⟩
  unfold faceWeight
  rw [hC.2.2.2.2.2.2 p', PeriodSubgroup.descend_proj _ (periodic hW hev hm), h0]
theorem faceWeight_flip (hI : QuotientMapsStatement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (k : ZMod (m : ℕ)) (p : (T.torusPeriods m).Face) :
    faceWeight T W m ((T.torusPeriods m).mapFace (T.slabFlip m k) p) =
      starRingEnd ℂ (faceWeight T W m p) := by
  exact descend_mapFace hI (T.torusPeriods m) (T.planeReflection ((k.cast : ℤ) + 1))
    (isCoordDiagonal_of_reflect T.grid T.axis _ _ fun _ => rfl) (periodic hW hev hm)
    (fun x => congrFun (hW.2.1 T.axis _) x) p
theorem slabKernel_bounded (hA : TransferAssertions.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (m : SlabCount) :
    T.IsBoundedMeasurable (slabKernel T W m) := by
  obtain ⟨-, -, -, -, -, -, -, -, hWt⟩ := hA D T m
  obtain ⟨hc, hb, -⟩ := (hWt _ (faceWeight_bounded hW m)).1 0
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨hc.measurable, hb⟩
theorem slabBoltzmann_natCast (hA : TransferAssertions.Statement)
    (hI : QuotientMapsStatement) (hS : SlabSymmetries.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (k : ℕ) :
    T.slabBoltzmann m (faceWeight T W m) (k : ZMod (m : ℕ)) =
      if Even k then slabKernel T W m else T.reflectConj (slabKernel T W m) := by
  obtain ⟨-, -, -, -, -, hRev, -⟩ := hA D T m
  have hb := slabKernel_bounded hA hW m
  induction k with
  | zero => simp [slabKernel]
  | succ k ih =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hS D T m hm (k : ZMod (m : ℕ))
    have hstep := (hlast _ (faceWeight_bounded hW m)).2
      (fun p _ => faceWeight_flip hI hW hev hm _ p)
    rw [Nat.cast_succ, hstep, ih]
    by_cases he : Even k
    · rw [if_pos he, if_neg (by simpa [Nat.even_add_one] using he)]
    · rw [if_neg he, if_pos (by simpa [Nat.even_add_one] using he)]
      exact (hRev.2.2.2 _ _ hb hb).2.1
theorem weightedPartition_eq_alternating (hQ : ProjOnEdgesAndFaces.Statement)
    (hA : TransferAssertions.Statement)
    (hI : QuotientMapsStatement) (hS : SlabSymmetries.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) :
    (T.torusPeriods m).weightedPartition W =
      T.alternatingSlabIntegral m hm (slabKernel T W m) := by
  obtain ⟨-, -, -, -, -, -, -, -, hWt⟩ := hA D T m
  have h := (hWt _ (faceWeight_bounded hW m)).2
    (fun p hp => faceWeight_crossing hQ hA hW hev hm p hp)
  refine h.trans ?_
  unfold TransferSetup.alternatingSlabIntegral
  congr 1
  funext k
  have hk := slabBoltzmann_natCast hA hI hS hW hev hm k.val
  rwa [ZMod.natCast_zmod_val] at hk
def transverseLift (T : TransferSetup D) (y : T.TransverseTorus) : TransverseAxis T.axis → ℝ :=
  fun ν => (QuotientAddGroup.mk_surjective (y ν)).choose
theorem coe_transverseLift (T : TransferSetup D) (y : T.TransverseTorus)
    (ν : TransverseAxis T.axis) :
    ((transverseLift T y ν : ℝ) : AddCircle (T.transverseSide ν)) = y ν :=
  (QuotientAddGroup.mk_surjective (y ν)).choose_spec
theorem proj_ambientPoint (T : TransferSetup D) (m : SlabCount) (t : ℝ)
    (y : T.TransverseTorus) :
    (T.torusPeriods m).proj (T.ambientPoint t (transverseLift T y)) = T.torusPoint m t y := by
  funext ν
  by_cases hν : ν = T.axis
  · subst hν
    rw [TransferSetup.torusPoint_axis]
    change ((T.ambientPoint t (transverseLift T y) T.axis : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths T.axis)) = _
    simp [TransferSetup.ambientPoint]
  · change _ = T.torusPoint m t y (⟨ν, hν⟩ : TransverseAxis T.axis).1
    rw [TransferSetup.torusPoint_transverse, ← coe_transverseLift T y ⟨ν, hν⟩,
      addCircleCast_coe]
    change ((T.ambientPoint t (transverseLift T y) ν : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths ν)) = _
    simp [TransferSetup.ambientPoint, hν]
theorem descend_torusPoint (hW : T.grid.IsReflectionPeriodic W)
    (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (t : ℝ) (y : T.TransverseTorus) :
    (T.torusPeriods m).descend W (T.torusPoint m t y) =
      W (T.ambientPoint t (transverseLift T y)) := by
  rw [← proj_ambientPoint T m t y]
  exact PeriodSubgroup.descend_proj _ (periodic hW hev hm) _
theorem coe_sliceTime_slabSliceIndex (T : TransferSetup D) (m : SlabCount) (c : ℤ) :
    ((T.sliceTime ((T.slabSliceIndex m 0 c).cast : ℤ) : ℝ) :
        AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((T.sliceTime c : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
  refine T.coe_sliceTime_eq m ?_
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ?_
  simp [TransferSetup.slabSliceIndex]
theorem faceWeight_sliceFace (hA : TransferAssertions.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (c : ℤ) (q : T.TransverseFace) :
    faceWeight T W m (T.sliceFace m (T.slabSliceIndex m 0 c) q) =
      W (T.ambientPoint (T.sliceTime c) (transverseLift T (T.faceCentre q))) := by
  obtain ⟨-, -, -, hPl, -⟩ := hA D T m
  unfold faceWeight
  rw [(hPl.2.1 _ q).2, T.torusPoint_congr m (coe_sliceTime_slabSliceIndex T m c),
    descend_torusPoint hW hev hm]
theorem faceWeight_axialFace (hA : TransferAssertions.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m : SlabCount} (hm : Even (m : ℕ)) (c : ℤ) (b : T.PositiveTransverseEdge) :
    faceWeight T W m (T.axialFace m (T.slabSliceIndex m 0 c) b) =
      W (T.ambientPoint (T.sliceTime c + D.mesh / 2) (transverseLift T (T.edgeMidpoint b))) := by
  obtain ⟨-, -, -, hPl, -⟩ := hA D T m
  have hcl : ((T.sliceTime ((T.slabSliceIndex m 0 c).cast : ℤ) + D.mesh / 2 : ℝ) :
      AddCircle ((T.torusPeriods m).sideLengths T.axis)) =
      ((T.sliceTime c + D.mesh / 2 : ℝ) : AddCircle ((T.torusPeriods m).sideLengths T.axis)) := by
    rw [AddCircle.coe_add, AddCircle.coe_add, coe_sliceTime_slabSliceIndex]
  unfold faceWeight
  rw [(hPl.2.2 _ b).1, T.torusPoint_congr m hcl, descend_torusPoint hW hev hm]
theorem slabKernel_eq (hA : TransferAssertions.Statement)
    (hW : T.grid.IsReflectionPeriodic W) (hev : ∀ ν, Even (T.transverseCells ν))
    {m m' : SlabCount} (hm : Even (m : ℕ)) (hm' : Even (m' : ℕ)) :
    slabKernel T W m = slabKernel T W m' := by
  funext η
  unfold slabKernel TransferSetup.slabBoltzmann
  simp only [faceWeight_sliceFace hA hW hev hm, faceWeight_sliceFace hA hW hev hm',
    faceWeight_axialFace hA hW hev hm, faceWeight_axialFace hA hW hev hm']
end Slab
theorem even_scaleCoord {n : Fin 4 → ℤ} (hev : ∀ ν, Even (n ν)) (μ : Fin 4) (j : ℕ)
    (ν : Fin 4) : Even (scaleCoord n μ j ν) := by
  by_cases h : ν = μ
  · subst h
    simpa [scaleCoord] using (hev ν).mul_left (j : ℤ)
  · simpa [scaleCoord, Function.update_of_ne h] using hev ν
def transferSetupOf (g : ReflectionGrid D) (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (μ : Fin 4) :
    TransferSetup D :=
  ⟨g, μ, fun ν => n ν.1, fun ν => hn ν.1⟩
def slabCountOf (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (μ : Fin 4) : SlabCount :=
  ⟨(n μ).toNat, by have := hn μ; omega⟩
theorem natCast_slabCountOf (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (μ : Fin 4) :
    (((slabCountOf n hn μ : SlabCount) : ℕ) : ℤ) = n μ :=
  Int.toNat_of_nonneg (by have := hn μ; omega)
theorem submultiplicative_one_axis (hQ : ProjOnEdgesAndFaces.Statement)
    (hA : TransferAssertions.Statement) (hI : QuotientMapsStatement)
    (hS : SlabSymmetries.Statement) (hT : CyclicTraceFormula.Statement)
    (g : ReflectionGrid D) {W : AmbientSpace → ℂ} (hW : g.IsReflectionPeriodic W)
    (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (hev : ∀ μ, Even (n μ)) (μ : Fin 4) (j : ℕ)
    (hj : 1 ≤ j) :
    ((g.boxPeriods n hn).weightedPartition W).im = 0 ∧
      ((g.boxPeriods (scaleCoord n μ j)
        (two_le_scaleCoord hn μ hj)).weightedPartition W).im = 0 ∧
      0 ≤ ((g.boxPeriods (scaleCoord n μ j)
        (two_le_scaleCoord hn μ hj)).weightedPartition W).re ∧
      ((g.boxPeriods (scaleCoord n μ j)
        (two_le_scaleCoord hn μ hj)).weightedPartition W).re ≤
        ((g.boxPeriods n hn).weightedPartition W).re ^ j := by
  set T := transferSetupOf g n hn μ with hTdef
  set m := slabCountOf n hn μ with hmdef
  have hmc : (((m : SlabCount) : ℕ) : ℤ) = n μ := natCast_slabCountOf n hn μ
  have hm : Even (m : ℕ) := by
    have := hev μ
    rw [← hmc] at this
    exact_mod_cast this
  set m' := SlabCount.scale j hj m with hm'def
  have hm' : Even (m' : ℕ) := SlabCount.even_scale j hj hm
  have hevT : ∀ ν, Even (T.transverseCells ν) := fun ν => hev ν.1
  have hWT : T.grid.IsReflectionPeriodic W := hW
  have hP : T.torusPeriods m = g.boxPeriods n hn := by
    refine boxPeriods_congr g _ _ ?_
    funext ν
    unfold TransferSetup.cellCounts
    split_ifs with h
    · have h' : ν = μ := h
      subst h'
      exact hmc
    · rfl
  have hP' : T.torusPeriods m' = g.boxPeriods (scaleCoord n μ j)
      (two_le_scaleCoord hn μ hj) := by
    refine boxPeriods_congr g _ _ ?_
    funext ν
    unfold TransferSetup.cellCounts
    split_ifs with h
    · have h' : ν = μ := h
      subst h'
      simp only [scaleCoord, Function.update_self]
      rw [← hmc]
      simp [hm'def, SlabCount.scale]
    · have h' : ν ≠ μ := h
      simp [scaleCoord, Function.update_of_ne h']
      rfl
  rw [← hP, ← hP', Slab.weightedPartition_eq_alternating hQ hA hI hS hWT hevT hm,
    Slab.weightedPartition_eq_alternating hQ hA hI hS hWT hevT hm',
    Slab.slabKernel_eq hA hWT hevT hm' hm]
  have hb := Slab.slabKernel_bounded hA hWT m
  obtain ⟨h1, -, h3⟩ := (hT D T).2.2 m hm
  obtain ⟨-, -, hreal, -⟩ := h1 _ hb
  obtain ⟨i1, i2, i3⟩ := h3 _ hb j hj
  refine ⟨?_, i1, i2, i3⟩
  rw [hreal]
  exact Complex.ofReal_im _
theorem submultiplicative_diagonal (g : ReflectionGrid D) {W : AmbientSpace → ℂ}
    (hone : ∀ (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ), (∀ μ, Even (n μ)) →
      ∀ (μ : Fin 4) (j : ℕ) (hj : 1 ≤ j),
        ((g.boxPeriods n hn).weightedPartition W).im = 0 ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).im = 0 ∧
        0 ≤ ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ≤
          ((g.boxPeriods n hn).weightedPartition W).re ^ j)
    (c : ℤ) (hc : 2 ≤ c) (hce : Even c) (j : ℕ) (hj : 1 ≤ j) (hjc : 2 ≤ (j : ℤ) * c) :
    ((g.boxPeriods (fun _ => c) (fun _ => hc)).weightedPartition W).im = 0 ∧
      ((g.boxPeriods (fun _ => (j : ℤ) * c) (fun _ => hjc)).weightedPartition W).im = 0 ∧
      0 ≤ ((g.boxPeriods (fun _ => (j : ℤ) * c) (fun _ => hjc)).weightedPartition W).re ∧
      ((g.boxPeriods (fun _ => (j : ℤ) * c) (fun _ => hjc)).weightedPartition W).re ≤
        ((g.boxPeriods (fun _ => c) (fun _ => hc)).weightedPartition W).re ^ (j ^ 4) := by
  have e0 : ∀ μ : Fin 4, Even ((fun _ => c : Fin 4 → ℤ) μ) := fun _ => hce
  have b0 : ∀ μ : Fin 4, 2 ≤ (fun _ => c : Fin 4 → ℤ) μ := fun _ => hc
  have b1 := two_le_scaleCoord b0 0 hj
  have e1 := even_scaleCoord e0 0 j
  have b2 := two_le_scaleCoord b1 1 hj
  have e2 := even_scaleCoord e1 1 j
  have b3 := two_le_scaleCoord b2 2 hj
  have e3 := even_scaleCoord e2 2 j
  obtain ⟨i0, -, p1, l1⟩ := hone _ b0 e0 0 j hj
  obtain ⟨-, -, p2, l2⟩ := hone _ b1 e1 1 j hj
  obtain ⟨-, -, p3, l3⟩ := hone _ b2 e2 2 j hj
  obtain ⟨-, i4, p4, l4⟩ := hone _ b3 e3 3 j hj
  have hU : scaleCoord (scaleCoord (scaleCoord (scaleCoord (fun _ => c) 0 j) 1 j) 2 j)
      3 j = fun _ => (j : ℤ) * c := by
    funext ν
    fin_cases ν <;> simp [scaleCoord, Function.update]
  rw [boxPeriods_congr g (fun _ => hjc) (two_le_scaleCoord b3 3 hj) hU.symm]
  refine ⟨i0, i4, p4, l4.trans ?_⟩
  have s3 := pow_le_pow_left₀ p3 l3 j
  have s2 := pow_le_pow_left₀ (pow_nonneg p2 j) (pow_le_pow_left₀ p2 l2 j) j
  have s1 := pow_le_pow_left₀ (pow_nonneg (pow_nonneg p1 j) j)
    (pow_le_pow_left₀ (pow_nonneg p1 j) (pow_le_pow_left₀ p1 l1 j) j) j
  refine s3.trans (s2.trans (s1.trans (le_of_eq ?_)))
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  congr 1
  ring
theorem submultiplicative_tori (hAr : ReflectionGridArithmetic.Statement) (g : ReflectionGrid D)
    {W : AmbientSpace → ℂ}
    (hW : g.IsReflectionPeriodic W)
    (hone : ∀ (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ), (∀ μ, Even (n μ)) →
      ∀ (μ : Fin 4) (j : ℕ) (hj : 1 ≤ j),
        ((g.boxPeriods n hn).weightedPartition W).im = 0 ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).im = 0 ∧
        0 ≤ ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ∧
        ((g.boxPeriods (scaleCoord n μ j)
          (two_le_scaleCoord hn μ hj)).weightedPartition W).re ≤
          ((g.boxPeriods n hn).weightedPartition W).re ^ j)
    (m' : ℕ+) (h1 : PeriodicLattice.torusSide D.L m' ≤ PeriodicLattice.torusSide D.L D.m)
    (h2 : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m') :
    (D.partitionFunctionOfPeriodic W).im = 0 ∧
      ((D.withExponent m').partitionFunctionOfPeriodic W).im = 0 ∧
      0 ≤ (D.partitionFunctionOfPeriodic W).re ∧
      (D.partitionFunctionOfPeriodic W).re ≤
        ((D.withExponent m').partitionFunctionOfPeriodic W).re ^
          ((PeriodicLattice.torusSide D.L D.m / PeriodicLattice.torusSide D.L m') ^ 4 : ℝ) := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  have hLn : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  have hmm : (m' : ℕ) ≤ (D.m : ℕ) := by
    have h : (D.L : ℝ) ^ (m' : ℕ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := by
      simp only [PeriodicLattice.torusSide] at h1
      linarith
    exact (pow_le_pow_iff_right₀ hL).mp h
  obtain ⟨-, -, -, hg⟩ := hAr D
  obtain ⟨⟨-, -, hev, hn, hgrp, hZ⟩, -⟩ := (hg g).2 (h2.trans h1)
  obtain ⟨-, -, -, hg'⟩ := hAr (D.withExponent m')
  obtain ⟨⟨hq', -, hev', hn', hgrp', hZ'⟩, -⟩ := (hg' (g.withExponent m')).2 h2
  have hq : g.q ≤ ((m' : ℕ) : ℤ) := hq'
  set c : ℤ := (g.withExponent m').cellsPerTorusSide with hcdef
  have hc : c = 2 * (D.L : ℤ) ^ (((m' : ℕ) : ℤ) - g.q).toNat := rfl
  have hc2 : 2 ≤ c := hn'
  have hce : Even c := hev'
  set j : ℕ := D.L ^ ((D.m : ℕ) - (m' : ℕ)) with hjdef
  have hj : 1 ≤ j := Nat.one_le_pow _ _ hLn
  have hnc : g.cellsPerTorusSide = (j : ℤ) * c := by
    have hexp : (((D.m : ℕ) : ℤ) - g.q).toNat =
        ((D.m : ℕ) - (m' : ℕ)) + (((m' : ℕ) : ℤ) - g.q).toNat := by omega
    rw [hc, ReflectionGrid.cellsPerTorusSide, hexp, pow_add, hjdef]
    push_cast
    ring
  have hjc : 2 ≤ (j : ℤ) * c := hnc ▸ hn
  obtain ⟨i0, i4, p4, l4⟩ := submultiplicative_diagonal g hone c hc2 hce j hj hjc
  have E1 : (g.boxPeriods (fun _ => (j : ℤ) * c) (fun _ => hjc)).weightedPartition W =
      D.partitionFunctionOfPeriodic W := by
    rw [boxPeriods_congr g (fun _ => hjc) (fun _ => hn) (funext fun _ => hnc.symm)]
    refine hZ W hW.1 ?_
    rw [← hgrp]
    exact periodic_of_boxPeriods g hW _ _ fun _ => hev
  have E0 : (g.boxPeriods (fun _ => c) (fun _ => hc2)).weightedPartition W =
      (D.withExponent m').partitionFunctionOfPeriodic W := by
    refine Eq.trans ?_ (hZ' W hW.1 ?_)
    · rfl
    · rw [← hgrp']
      intro x v hv
      exact periodic_of_boxPeriods g hW (fun _ => c) (fun _ => hc2) (fun _ => hce) x v hv
  rw [E0] at i0 l4
  rw [E1] at i4 p4 l4
  refine ⟨i4, i0, p4, ?_⟩
  have hexp : ((PeriodicLattice.torusSide D.L D.m / PeriodicLattice.torusSide D.L m') ^ 4 : ℝ) =
      ((j ^ 4 : ℕ) : ℝ) := by
    have hs : (D.L : ℝ) ^ (D.m : ℕ) = (j : ℝ) * (D.L : ℝ) ^ (m' : ℕ) := by
      rw [hjdef]
      push_cast
      rw [← pow_add, Nat.sub_add_cancel hmm]
    have hd : PeriodicLattice.torusSide D.L D.m / PeriodicLattice.torusSide D.L m' = (j : ℝ) := by
      simp only [PeriodicLattice.torusSide]
      rw [hs]
      field_simp
    rw [hd]
    push_cast
    rfl
  rw [hexp, Real.rpow_natCast]
  exact l4
end SubmultiplicativityProof
open SubmultiplicativityProof in
theorem PartitionFunctionSubmultiplicativity.proof (hAr : ReflectionGridArithmetic.Statement)
    (hI : QuotientMapsStatement) (hA : TransferAssertions.Statement)
    (hQ : ProjOnEdgesAndFaces.Statement) (hT : CyclicTraceFormula.Statement)
    (hS : SlabSymmetries.Statement) :
    PartitionFunctionSubmultiplicativity.Statement := by
  intro D g W hW
  have hone := fun (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (hev : ∀ μ, Even (n μ)) (μ : Fin 4)
    (j : ℕ) (hj : 1 ≤ j) => submultiplicative_one_axis hQ hA hI hS hT g hW n hn hev μ j hj
  refine ⟨fun x k => ?_, fun n hn hev => ⟨periodic_of_boxPeriods g hW n hn hev, hone n hn hev⟩,
    fun m' h1 h2 => submultiplicative_tori hAr g hW hone m' h1 h2⟩
  exact mem_periodSubgroupOf g hW _ k (fun μ => by simp [TestFunctions.latticeTranslate]; ring) x
end YangMills.Construction.ChessboardTori
end
