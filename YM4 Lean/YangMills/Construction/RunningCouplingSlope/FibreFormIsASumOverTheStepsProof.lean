import YangMills.Construction.RunningCouplingSlope.ExcessFormIsTheHessianOfTheChart
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheSteps
import YangMills.Construction.RunningCouplingSlope.FibreFormIsTheSumOfTheExcessForms
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.LevelOfAChainReadsTheFieldOfItsStep
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.PositiveBondsOfALevelAreThoseOfAFrame
import YangMills.Construction.SoftAverages.QuaternionsAsMatrices
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
namespace FibreHessianSteps
variable {L n k : ℕ}
private def coordSite (d : ℤ) (z : Fin 4 → ℤ) : PeriodicLattice.Site L n d :=
  PeriodicLattice.offsetSite 0 z
private theorem coe_coordSite (d : ℤ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L d) := by
    show (PeriodicLattice.sublattice L n d).subtype (coordSite d z) = _
    simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem coordSite_congr {d : ℤ} {P : ℕ}
    (hP : (P : ℝ) * PeriodicLattice.meshSize L d = PeriodicLattice.torusSide L n) {z z' : Fin 4 → ℤ}
    (h : ∀ ν, ∃ m : ℤ, z ν - z' ν = m * P) : coordSite (L := L) (n := n) d z = coordSite d z' := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_coordSite, coe_coordSite, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  obtain ⟨m, hm⟩ := h ν
  refine ⟨m, ?_⟩
  rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul]
  congr 1
  exact_mod_cast hm.symm
private theorem unitStep_eq_coordSite (d : ℤ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n d μ = coordSite d (Pi.single μ 1) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_coordSite]
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem coordSite_add (d : ℤ) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) d z + coordSite d w = coordSite d (z + w) := by
  refine Subtype.ext (funext fun ν => ?_)
  have e : ((coordSite (L := L) (n := n) d z + coordSite d w : PeriodicLattice.Site L n d) :
      PeriodicLattice.FourTorus L n) ν =
      ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν +
      ((coordSite (L := L) (n := n) d w : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν := rfl
  rw [e, coe_coordSite, coe_coordSite, coe_coordSite, ← AddCircle.coe_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring
private theorem coe_toSublattice [NeZero L] {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L n i) :
    ((y.toSublattice i' : PeriodicLattice.Site L n i') : PeriodicLattice.FourTorus L n) = y :=
  Classical.epsilon_spec (p := fun x : PeriodicLattice.Site L n i' =>
    (x : PeriodicLattice.FourTorus L n) = y)
    ⟨⟨y.1, PeriodicLattice.sublattice_mono (Nat.pos_of_ne_zero (NeZero.ne L)) n h y.2⟩, rfl⟩
private def imagQuat (c : Fin 3 → ℝ) : ℍ[ℝ] := ⟨0, c 0, c 1, c 2⟩
private theorem imaginaryComponents_imagQuat (c : Fin 3 → ℝ) : imaginaryComponents (imagQuat c) = c := by
  funext i
  fin_cases i <;> rfl
private theorem I_smul_eq_quaternionToMatrix {B : Matrices.ComplexMatrix2}
    (hB : B ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Complex.I • B = SoftAverages.quaternionToMatrix (imagQuat (suTwoComponents B)) := by
  obtain ⟨h1, h2⟩ := hB
  have e00 : (B 0 0).im = 0 := by
    have := congrFun (congrFun h1 0) 0
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact Complex.conj_eq_iff_im.mp this.symm
  have e10 : B 1 0 = star (B 0 1) := by
    have := congrFun (congrFun h1 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e11 : B 1 1 = -B 0 0 := by
    simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] at h2
    linear_combination h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SoftAverages.quaternionToMatrix, imagQuat, suTwoComponents, e10, e11] <;>
    apply Complex.ext <;> simp [e00]
private theorem suTwoComponents_I_inv_smul (w : ℍ[ℝ]) :
    suTwoComponents (Complex.I⁻¹ • SoftAverages.quaternionToMatrix w) = imaginaryComponents w := by
  funext i
  fin_cases i <;> simp [suTwoComponents, imaginaryComponents, SoftAverages.quaternionToMatrix]
private theorem quaternionToMatrix_inv (g : BlockAverages.UnitQuaternion) :
    (SoftAverages.quaternionToMatrix (g : ℍ[ℝ]))⁻¹ =
      SoftAverages.quaternionToMatrix ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← SoftAverages.quaternionToMatrix_mul]
  have : (g : ℍ[ℝ]) * ((g⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  rw [this, SoftAverages.quaternionToMatrix_one]
abbrev _root_.YangMills.DeltaSharedProofs.p502200 := @quaternionToMatrix_inv
private theorem suTwoComponents_conj_sub (w : BlockAverages.UnitQuaternion) {B₁ B₂ : Matrices.ComplexMatrix2}
    (h₁ : B₁ ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (h₂ : B₂ ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    suTwoComponents (Matrices.ComplexMatrix2.conjugateBy (SoftAverages.quaternionToMatrix (w : ℍ[ℝ])) B₁ - B₂) =
      imaginaryComponents ((w : ℍ[ℝ]) * imagQuat (suTwoComponents B₁) *
        ((w⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - imagQuat (suTwoComponents B₂)) := by
  rw [← suTwoComponents_I_inv_smul]
  congr 1
  have hI : (Complex.I⁻¹ : ℂ) * Complex.I = 1 := inv_mul_cancel₀ Complex.I_ne_zero
  have s1 := I_smul_eq_quaternionToMatrix h₁
  have s2 := I_smul_eq_quaternionToMatrix h₂
  have hsub : SoftAverages.quaternionToMatrix ((w : ℍ[ℝ]) * imagQuat (suTwoComponents B₁) *
      ((w⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - imagQuat (suTwoComponents B₂)) =
      SoftAverages.quaternionToMatrix ((w : ℍ[ℝ]) * imagQuat (suTwoComponents B₁) *
        ((w⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) -
      SoftAverages.quaternionToMatrix (imagQuat (suTwoComponents B₂)) :=
    map_sub SoftAverages.quaternionToMatrixRingHom _ _
  rw [hsub, SoftAverages.quaternionToMatrix_mul, SoftAverages.quaternionToMatrix_mul, ← s1, ← s2,
    ← quaternionToMatrix_inv, Matrices.ComplexMatrix2.conjugateBy, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_smul, hI, one_smul, one_smul]
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N : ℕ, torusSideBelow L s N = N * L ^ s
  | 0, _ => by simp [torusSideBelow]
  | s + 1, N => by
    show torusSideBelow L s (N * L) = _
    rw [torusSideBelow_eq L s, pow_succ]
    ring
private theorem period_top (L n K j : ℕ) (hj : j < K) (i : Fin 4) :
    (frameAtStep L n K j).period (frameAtStep L n K j).top i = 2 * L ^ (n + (K - (j + 1))) := by
  simp only [BlockAverages.BlockFrame.period, frameAtStep, TorusFields.torusFrame, sideAtStep,
    BlockAverages.BlockFrame.top, Nat.sub_self, pow_zero, mul_one]
  rw [torusSideBelow_eq, pow_add]
  ring
private theorem period_depth (L n K j : ℕ) (hj : j < K) (i : Fin 4) :
    (frameAtStep L n K j).period (frameAtStep L n K j).depth i = 2 * L ^ (n + (K - j)) := by
  have e : K - j = (K - (j + 1)) + 1 := by omega
  simp only [BlockAverages.BlockFrame.period, frameAtStep, TorusFields.torusFrame, sideAtStep,
    BlockAverages.BlockFrame.top]
  rw [torusSideBelow_eq, e, Nat.add_sub_cancel_left, pow_one, ← add_assoc, pow_succ, pow_add]
  ring
abbrev _root_.YangMills.SharedProofs.p69486 := @period_depth
private theorem meshSize_mul_period (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) :
    ((2 * L ^ (n + (K - j)) : ℕ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth K j) =
      PeriodicLattice.torusSide L n := by
  have e : PeriodicLattice.levelDepth K j = ((K - j : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth, Nat.cast_sub hj]
  simp only [PeriodicLattice.meshSize, PeriodicLattice.torusSide, e]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
private theorem extent_pos {L n K j : ℕ} (hL : 0 < L) (i : Fin 4) :
    0 < (frameAtStep L n K j).extent i := by
  simp only [frameAtStep, TorusFields.torusFrame, sideAtStep]
  rw [torusSideBelow_eq]
  positivity
private theorem mem_innerBonds (hL : Conventions.IsAdmissibleBlockingFactor L) {K j l : ℕ}
    (b : (frameAtStep L n K j).Site l × Fin 4) :
    b ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n K j)) l := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hc := fun {l : ℕ} (x : (frameAtStep L n K j).Site l) =>
    FrameTorusAction.mem_sitesOfCells_of_forall_mem (F := frameAtStep L n K j) hL.1
      (fun i => extent_pos hL0 i)
      (FrameTorusAction.mem_finiteCells _ (fun i => extent_pos hL0 i)) x
  simp only [BlockAverages.innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨hc _, hc _⟩
private def vertexValue {K j : ℕ} {F : BlockAverages.BlockFrame} {l : ℕ}
    (g : Tower.Vertex L n K j → Matrices.ComplexMatrix2) : F.Site l → BlockAverages.imaginaryQuaternions :=
  fun x => ColdStepAtMirrorFrames.toImaginary (WithLp.toLp 2
    (suTwoComponents (g (coordSite (PeriodicLattice.levelDepth K j) (BlockAverages.siteCoords x)))))
private theorem siteCoords_siteOfCoords {F : BlockAverages.BlockFrame} {l : ℕ} (c : Fin 4 → ℤ) (ν : Fin 4) :
    ∃ m : ℤ, BlockAverages.siteCoords (BlockAverages.siteOfCoords (F := F) l c) ν - c ν =
      m * ((F.period l ν : ℕ) : ℤ) := by
  have h₁ : (((BlockAverages.siteCoords (BlockAverages.siteOfCoords (F := F) l c) ν : ℤ)) :
      ZMod (F.period l ν)) = (c ν : ZMod (F.period l ν)) :=
    ZMod.intCast_zmod_cast _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h₁
  obtain ⟨m, hm⟩ := h₁
  exact ⟨-m, by linear_combination -hm⟩
private theorem target_edgeOfCoords (hL : 0 < L) {K j : ℕ} (hj : j < K)
    (x : (frameAtStep L n K j).Site (frameAtStep L n K j).depth) (i : Fin 4) :
    (edgeOfCoords (L := L) (n := n) (k := K) j (x, i)).target =
      coordSite (PeriodicLattice.levelDepth K j)
        (BlockAverages.siteCoords (x + BlockAverages.unitStep (frameAtStep L n K j).depth i)) := by
  have hper := period_depth L n K j hj
  have e₀ : (edgeOfCoords (L := L) (n := n) (k := K) j (x, i)).target =
      coordSite (PeriodicLattice.levelDepth K j) (BlockAverages.siteCoords x) +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth K j) i := rfl
  rw [e₀, unitStep_eq_coordSite, coordSite_add]
  refine coordSite_congr (meshSize_mul_period hL hj.le) fun ν => ?_
  have h₀ : (((BlockAverages.siteCoords (x + BlockAverages.unitStep (frameAtStep L n K j).depth i) ν : ℤ)) :
      ZMod ((frameAtStep L n K j).period (frameAtStep L n K j).depth ν)) =
      (x + BlockAverages.unitStep (frameAtStep L n K j).depth i :
        (frameAtStep L n K j).Site (frameAtStep L n K j).depth) ν :=
    ZMod.intCast_zmod_cast _
  have hx : (((BlockAverages.siteCoords x ν : ℤ)) :
      ZMod ((frameAtStep L n K j).period (frameAtStep L n K j).depth ν)) = x ν :=
    ZMod.intCast_zmod_cast _
  have h₁ : (((BlockAverages.siteCoords x ν + (Pi.single i (1 : ℤ) : Fin 4 → ℤ) ν : ℤ)) :
      ZMod ((frameAtStep L n K j).period (frameAtStep L n K j).depth ν)) =
      (((BlockAverages.siteCoords (x + BlockAverages.unitStep (frameAtStep L n K j).depth i) ν : ℤ)) :
        ZMod ((frameAtStep L n K j).period (frameAtStep L n K j).depth ν)) := by
    rw [h₀, Int.cast_add, hx]
    rfl
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h₁
  obtain ⟨m, hm⟩ := h₁
  have hc : (((frameAtStep L n K j).period (frameAtStep L n K j).depth ν : ℕ) : ℤ) =
      ((2 * L ^ (n + (K - j)) : ℕ) : ℤ) := by exact_mod_cast hper ν
  rw [hc] at hm
  refine ⟨-m, ?_⟩
  show BlockAverages.siteCoords x ν + (Pi.single i (1 : ℤ) : Fin 4 → ℤ) ν -
    BlockAverages.siteCoords (x + BlockAverages.unitStep (frameAtStep L n K j).depth i) ν = _
  linear_combination -hm
private theorem covDiff_components (hL : 0 < L) {K j : ℕ} (hj : j < K)
    {U : Tower.Edge L n K j → Matrices.ComplexMatrix2}
    {g : Tower.Vertex L n K j → Matrices.ComplexMatrix2} (hg : g ∈ Tower.vertexFunctionSpace L n K j)
    {w : (frameAtStep L n K j).GaugeField (frameAtStep L n K j).depth}
    (hw : ∀ b, U (edgeOfCoords j b) =
      SoftAverages.quaternionToMatrix ((w b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
    (b : (frameAtStep L n K j).Site (frameAtStep L n K j).depth × Fin 4) :
    suTwoComponents (Tower.covDiff U g (edgeOfCoords j b)) =
      imaginaryComponents (covariantDifference w (vertexValue g) b) := by
  obtain ⟨x, i⟩ := b
  have hpos : (edgeOfCoords (L := L) (n := n) (k := K) j (x, i)).IsPositivelyOriented :=
    ⟨i, by simp [edgeOfCoords, PeriodicLattice.Bond.forwardFrom]⟩
  have e₁ : Tower.covDiff U g (edgeOfCoords j (x, i)) =
      Matrices.ComplexMatrix2.conjugateBy (U (edgeOfCoords j (x, i)))
        (g (edgeOfCoords (L := L) (n := n) (k := K) j (x, i)).target) -
        g (edgeOfCoords (L := L) (n := n) (k := K) j (x, i)).source := by
    simp [Tower.covDiff, Tower.extendOddly, hpos]
  rw [e₁, hw, target_edgeOfCoords hL hj]
  exact suTwoComponents_conj_sub _ (hg _ (Set.mem_univ _)) (hg _ (Set.mem_univ _))
private theorem vertexValue_cellCentre (hL : 0 < L) [NeZero L] {K j : ℕ} (hj : j < K)
    {g : Tower.Vertex L n K j → Matrices.ComplexMatrix2} (hg : Tower.restrictVertexFunction (j + 1) g = 0)
    (z : (frameAtStep L n K j).Cell) :
    vertexValue (F := frameAtStep L n K j) (l := (frameAtStep L n K j).depth) g
      (BlockAverages.cellCentre (frameAtStep L n K j).depth z) = 0 := by
  have hd : PeriodicLattice.levelDepth K (j + 1) ≤ PeriodicLattice.levelDepth K j := by
    simp only [PeriodicLattice.levelDepth]; omega
  set y : Tower.Vertex L n K (j + 1) :=
    coordSite (PeriodicLattice.levelDepth K (j + 1)) (BlockAverages.siteCoords z) with hy
  have e₁ : coordSite (L := L) (n := n) (PeriodicLattice.levelDepth K j)
      (BlockAverages.siteCoords (BlockAverages.cellCentre (F := frameAtStep L n K j) (frameAtStep L n K j).depth z)) =
      y.toSublattice (PeriodicLattice.levelDepth K j) := by
    have hs₀ : coordSite (L := L) (n := n) (PeriodicLattice.levelDepth K j)
        (BlockAverages.siteCoords (BlockAverages.cellCentre (F := frameAtStep L n K j) (frameAtStep L n K j).depth z)) =
        coordSite (PeriodicLattice.levelDepth K j) fun ν => (L : ℤ) * BlockAverages.siteCoords z ν := by
      refine coordSite_congr (meshSize_mul_period hL hj.le) fun ν => ?_
      obtain ⟨m, hm⟩ := siteCoords_siteOfCoords (F := frameAtStep L n K j) (l := (frameAtStep L n K j).depth)
        (fun i => ((frameAtStep L n K j).blockSide : ℤ) ^
          ((frameAtStep L n K j).top - (frameAtStep L n K j).depth) * BlockAverages.siteCoords z i) ν
      refine ⟨m, ?_⟩
      have hc : (((frameAtStep L n K j).period (frameAtStep L n K j).depth ν : ℕ) : ℤ) =
          ((2 * L ^ (n + (K - j)) : ℕ) : ℤ) := by exact_mod_cast period_depth L n K j hj ν
      rw [hc] at hm
      have hq : ((frameAtStep L n K j).blockSide : ℤ) ^
          ((frameAtStep L n K j).top - (frameAtStep L n K j).depth) = (L : ℤ) := by
        simp [frameAtStep, TorusFields.torusFrame, BlockAverages.BlockFrame.top]
      have hm' : BlockAverages.siteCoords
          (BlockAverages.cellCentre (F := frameAtStep L n K j) (frameAtStep L n K j).depth z) ν -
          ((frameAtStep L n K j).blockSide : ℤ) ^
            ((frameAtStep L n K j).top - (frameAtStep L n K j).depth) * BlockAverages.siteCoords z ν =
          m * ((2 * L ^ (n + (K - j)) : ℕ) : ℤ) := hm
      rw [hq] at hm'
      exact hm'
    rw [hs₀]
    refine Subtype.ext ?_
    rw [coe_toSublattice hd y]
    funext ν
    rw [hy, coe_coordSite, coe_coordSite]
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    have e₃ : PeriodicLattice.levelDepth K j = PeriodicLattice.levelDepth K (j + 1) + 1 := by
      simp only [PeriodicLattice.levelDepth]
      push_cast
      ring
    congr 1
    rw [e₃]
    simp only [PeriodicLattice.meshSize]
    rw [neg_add, zpow_add₀ hLr]
    push_cast
    field_simp
  have e₂ : g (y.toSublattice (PeriodicLattice.levelDepth K j)) = 0 := congrFun hg y
  simp only [vertexValue]
  rw [e₁, e₂]
  ext <;> simp [ColdStepAtMirrorFrames.toImaginary, suTwoComponents]
private theorem imaginaryComponents_frameVelocity {F : BlockAverages.BlockFrame} {K j l : ℕ}
    (B : Tower.Edge L n K j → Matrices.ComplexMatrix2) (x : F.Site l) (i : Fin 4) :
    imaginaryComponents (frameVelocityOfForm j B x i : ℍ[ℝ]) = suTwoComponents (B (edgeOfCoords j (x, i))) :=
  imaginaryComponents_imagQuat _
private theorem exists_levelCoord (hP : FramePositiveEdgesBijective)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {K j : ℕ} (hj : j + 1 < K)
    (c : (frameAtStep L n K j).Site (frameAtStep L n K j).top × Fin 4) (d : Fin 3) :
    ∃ e' : LevelCoord (frameAtStep L n K (j + 1)), ∀ B : Tower.Edge L n K (j + 1) → Matrices.ComplexMatrix2,
      levelCoords (⟨j + 1, hj⟩ : Fin K) B e' = suTwoComponents (B (edgeOfCoords (j + 1) c)) d := by
  classical
  have h₁ := hP L hL n K (j + 1) hn hj.le (frameAtStep L n K j) (frameAtStep L n K j).top
    (period_top L n K j (by omega))
  have h₂ := hP L hL n K (j + 1) hn hj.le (frameAtStep L n K (j + 1))
    (frameAtStep L n K (j + 1)).depth (period_depth L n K (j + 1) hj)
  obtain ⟨b, hb⟩ := h₂.2.2 _ (h₁.1 c)
  by_cases ht : BlockAverages.IsAxialTreeBond b
  · refine ⟨.inr (⟨b, ?_⟩, d), fun B => ?_⟩
    · exact Finset.mem_filter.2 ⟨mem_innerBonds hL b, ht⟩
    · show suTwoComponents (B (edgeOfCoords (j + 1) b)) d = _
      rw [hb]
  · refine ⟨.inl (⟨b, ?_⟩, d), fun B => ?_⟩
    · exact Finset.mem_filter.2 ⟨mem_innerBonds hL b, ht⟩
    · show suTwoComponents (B (edgeOfCoords (j + 1) b)) d = _
      rw [hb]
open Classical in
private def chainMatrix {K : ℕ}
    (M : (j : Fin K) → Matrix (ReferenceDensity.ChartCoord (frameAtStep L n K j))
      (TopCoord (frameAtStep L n K j)) ℝ)
    (τ : (j : Fin K) → TopCoord (frameAtStep L n K j) → Option (ChainCoord L n K)) :
    Matrix (ChainCoord L n K) (ChainCoord L n K) ℝ
  | ⟨j, .inl i⟩, e' => ∑ c, if τ j c = some e' then M j i c else 0
  | ⟨_, .inr _⟩, _ => 0
private theorem mulVec_chainMatrix {K : ℕ}
    (M : (j : Fin K) → Matrix (ReferenceDensity.ChartCoord (frameAtStep L n K j))
      (TopCoord (frameAtStep L n K j)) ℝ)
    (τ : (j : Fin K) → TopCoord (frameAtStep L n K j) → Option (ChainCoord L n K))
    (y : ChainCoord L n K → ℝ) (j : Fin K) (i : ReferenceDensity.ChartCoord (frameAtStep L n K j)) :
    Matrix.mulVec (chainMatrix M τ) y ⟨j, .inl i⟩ =
      Matrix.mulVec (M j) (fun c => (τ j c).elim 0 y) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, chainMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases h : τ j c with _ | e₀
  · simp
  · rw [Finset.sum_eq_single e₀]
    · simp
    · intro e' _ hne
      have : ¬ some e₀ = some e' := fun e => hne (Option.some.inj e).symm
      simp [this]
    · simp
private theorem le_torusSideBelow {L : ℕ} (hL : 1 ≤ L) : ∀ s N : ℕ, N ≤ torusSideBelow L s N
  | 0, _ => le_rfl
  | s + 1, N => (Nat.le_mul_of_pos_right N hL).trans (le_torusSideBelow hL s (N * L))
private theorem tendsto_minimizerBelow (hN : MinimizerNearTrivialField) {a ρ : ℝ} (ha : 0 < a)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    ∀ (s k N : ℕ), 2 * L ≤ N →
    Tendsto (minimizerBelow a ρ L k s N) (𝓝 (TorusFields.trivialField N))
      (𝓝 (TorusFields.trivialField (torusSideBelow L s N)))
  | 0, _, _, _ => tendsto_id
  | s + 1, k, N, hm => by
    have h := (hN a ha L hL (k - 1) N ρ hm h0 h1).1
    have hL1 : 1 ≤ L := by have := hL.2; omega
    exact (tendsto_minimizerBelow hN ha hL h0 h1 s (k - 1) (N * L)
      (hm.trans (Nat.le_mul_of_pos_right N hL1))).comp h
private def StepHessianClaim (a ρ : ℝ) (L n K j : ℕ) (V : TorusFields.TorusField (2 * L ^ n)) : Prop :=
  ∃ M : Matrix (ReferenceDensity.ChartCoord (frameAtStep L n K j)) (TopCoord (frameAtStep L n K j)) ℝ,
    ∀ (A : (frameAtStep L n K j).Site (frameAtStep L n K j).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
      (v : (frameAtStep L n K j).Site (frameAtStep L n K j).top → Fin 4 → BlockAverages.imaginaryQuaternions)
      (x : ReferenceDensity.ChartCoord (frameAtStep L n K j) → ℝ)
      (γ : (frameAtStep L n K j).Site (frameAtStep L n K j).depth → BlockAverages.imaginaryQuaternions),
      (∀ z : (frameAtStep L n K j).Cell, γ (BlockAverages.cellCentre (frameAtStep L n K j).depth z) = 0) →
      (∀ i : ReferenceDensity.ChartCoord (frameAtStep L n K j),
        imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
        chartTangentCoords a ρ (topFieldAtStep a ρ L n K j V) x i +
          imaginaryComponents (covariantDifference (stepMinimizer a ρ (topFieldAtStep a ρ L n K j V)) γ i.1.1) i.2 +
          Matrix.mulVec M (topCoords v) i) →
      (∀ (i : TreeCoord (frameAtStep L n K j)), imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
        imaginaryComponents (covariantDifference (stepMinimizer a ρ (topFieldAtStep a ρ L n K j V)) γ i.1.1) i.2) →
      excessHessian a (stepMinimizer a ρ (topFieldAtStep a ρ L n K j V)) (topFieldAtStep a ρ L n K j V) A v =
        dotProduct x (Matrix.mulVec (chartHessianAtStep a ρ L n K j V) x)
end FibreHessianSteps
open FibreHessianSteps in
theorem fibreHessianSumOverSteps
    (hS : ExcessHessianEqChartHessian)
    (hT : FibreHessianEqSumExcessHessians)
    (hN : MinimizerNearTrivialField)
    (hP : FramePositiveEdgesBijective)
    (hC : ChainLevelIsStepMinimizer)
    (hM : ChainMapsAtMinimizers) :
    FibreHessianSumOverSteps := by
  classical
  intro a ha L hL k n hn ρ h0 h1
  have hL1 : 1 ≤ L := by have := hL.2; omega
  have hL0 : 0 < L := hL1
  have : NeZero L := ⟨hL0.ne'⟩
  have hbase : 2 * L ≤ 2 * L ^ n := by
    have h : L ^ 1 ≤ L ^ n := Nat.pow_le_pow_right hL1 hn
    rw [pow_one] at h
    omega
  have hstep : ∀ j, j ∈ Finset.range (k + 1) →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), StepHessianClaim a ρ L n (k + 1) j V := by
    intro j _
    have hs : 2 * L ≤ torusSideBelow L (k + 1 - (j + 1)) (2 * L ^ n) :=
      hbase.trans (le_torusSideBelow hL1 _ _)
    exact (tendsto_minimizerBelow hN ha hL h0 h1 (k + 1 - (j + 1)) (k + 1) (2 * L ^ n) hbase).eventually
      (hS a ha L hL j _ ρ hs h0 h1)
  filter_upwards [hT a ha L hL k n hn ρ h0 h1, hM a ha L hL (k + 1) n (by omega) hn,
    (Filter.eventually_all_finset (Finset.range (k + 1))).2 hstep] with V eT eM eS W hW X hX hR
  have hmaps := eM W hW X hX
  have hclaim : ∀ j : Fin (k + 1), StepHessianClaim a ρ L n (k + 1) j V :=
    fun j => eS j (Finset.mem_range.2 j.2)
  choose M hMs using hclaim
  have hex : ∀ (j : Fin (k + 1)) (c : TopCoord (frameAtStep L n (k + 1) j)),
      ∃ o : Option (ChainCoord L n (k + 1)),
        (∀ e', o = some e' → (j : ℕ) < coordLevel e') ∧
        ∀ ξ : LevelForms L n (k + 1), tangentTransport X ξ (k + 1) = 0 →
          o.elim 0 (transportCoords X ξ) =
            topCoords (frameVelocityOfForm ((j : ℕ) + 1) (tangentTransport X ξ ((j : ℕ) + 1))) c := by
    intro j c
    by_cases h : (j : ℕ) + 1 < k + 1
    · obtain ⟨e', he⟩ := exists_levelCoord hP hL hn h c.1.1 c.2
      refine ⟨some ⟨⟨(j : ℕ) + 1, h⟩, e'⟩, ?_, fun ξ _ => ?_⟩
      · intro e₁ h₁
        obtain rfl := Option.some.inj h₁
        show (j : ℕ) < (j : ℕ) + 1
        omega
      · show levelCoords (⟨(j : ℕ) + 1, h⟩ : Fin (k + 1)) (tangentTransport X ξ ((j : ℕ) + 1)) e' = _
        rw [he]
        unfold topCoords
        rw [imaginaryComponents_frameVelocity]
    · obtain ⟨j, hj⟩ := j
      have e : j = k := by simp only at h; omega
      subst e
      refine ⟨none, by simp, fun ξ h0 => ?_⟩
      unfold topCoords
      rw [imaginaryComponents_frameVelocity]
      simp only [h0]
      simp [suTwoComponents]
      rcases c with ⟨c₁, d⟩
      fin_cases d <;> rfl
  choose τ hτ₁ hτ₂ using hex
  refine ⟨chainMatrix M τ, ?_, ?_, ?_⟩
  · rintro ⟨j, e | e⟩ e' hle
    · show (∑ c, if τ j c = some e' then M j e c else 0) = 0
      refine Finset.sum_eq_zero fun c _ => if_neg fun h => ?_
      have := hτ₁ j c e' h
      exact absurd hle (not_le.2 this)
    · rfl
  · intro j i e'
    rfl
  · intro ξ x hx
    rw [eT W hW X hX hR ξ]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨g, hg, hg0, hge⟩ := hx j
    have hmv : tangentTransport X (ξ : LevelForms L n (k + 1)) (k + 1) = 0 := by
      have h₁ := hmaps.topDeriv_spec (ξ : LevelForms L n (k + 1))
      rw [LinearMap.mem_ker.1 ξ.2] at h₁
      exact h₁.symm
    have hread : ∀ b, levelField X j (edgeOfCoords j b) = SoftAverages.quaternionToMatrix
        ((stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V) b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) :=
      hC a ρ L hL (k + 1) n hn V X hR j j.2
    have hgc := covDiff_components hL0 j.2 hg hread
    have hN₂ : Matrix.mulVec (M j) (topCoords (frameVelocityOfForm ((j : ℕ) + 1)
        (tangentTransport X (ξ : LevelForms L n (k + 1)) ((j : ℕ) + 1)))) =
        Matrix.mulVec (M j) (fun c => (τ j c).elim 0
          (transportCoords X (ξ : LevelForms L n (k + 1)))) := by
      congr 1
      funext c
      exact (hτ₂ j c _ hmv).symm
    refine hMs j _ _ (x j) (vertexValue g) (vertexValue_cellCentre hL0 j.2 hg0) (fun i => ?_) (fun i => ?_)
    · have h₁ := hge (.inl i)
      simp only [Pi.sub_apply] at h₁
      rw [mulVec_chainMatrix] at h₁
      have h₂ : transportCoords X (ξ : LevelForms L n (k + 1)) ⟨j, .inl i⟩ =
          imaginaryComponents (frameVelocityOfForm (F := frameAtStep L n (k + 1) j) (j : ℕ)
            (tangentTransport X (ξ : LevelForms L n (k + 1)) j) i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 := by
        rw [imaginaryComponents_frameVelocity]
        rfl
      have h₃ : levelCoords j (Tower.covDiff (levelField X j) g) (.inl i) =
          imaginaryComponents (covariantDifference (stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V))
            (vertexValue g) i.1.1) i.2 := by
        rw [← hgc]
        rfl
      have h₄ : chartDirection a ρ L n (k + 1) V j (x j) (.inl i) =
          chartTangentCoords a ρ (topFieldAtStep a ρ L n (k + 1) j V) (x j) i := rfl
      rw [h₃, h₄, h₂, ← hN₂] at h₁
      linarith
    · have h₁ := hge (.inr i)
      simp only [Pi.sub_apply] at h₁
      have h₂ : transportCoords X (ξ : LevelForms L n (k + 1)) ⟨j, .inr i⟩ =
          imaginaryComponents (frameVelocityOfForm (F := frameAtStep L n (k + 1) j) (j : ℕ)
            (tangentTransport X (ξ : LevelForms L n (k + 1)) j) i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 := by
        rw [imaginaryComponents_frameVelocity]
        rfl
      have h₃ : levelCoords j (Tower.covDiff (levelField X j) g) (.inr i) =
          imaginaryComponents (covariantDifference (stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V))
            (vertexValue g) i.1.1) i.2 := by
        rw [← hgc]
        rfl
      have h₅ : Matrix.mulVec (chainMatrix M τ)
          (transportCoords X (ξ : LevelForms L n (k + 1))) ⟨j, .inr i⟩ = 0 := by
        simp [Matrix.mulVec, dotProduct, chainMatrix]
      have h₄ : chartDirection a ρ L n (k + 1) V j (x j) (.inr i) = 0 := rfl
      rw [h₃, h₄, h₂, h₅] at h₁
      linarith
end RunningCouplingSlope
end YangMills.Construction
end
