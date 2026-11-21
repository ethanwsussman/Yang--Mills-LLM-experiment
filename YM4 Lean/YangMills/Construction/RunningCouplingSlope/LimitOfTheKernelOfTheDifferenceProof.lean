import YangMills.Construction.RunningCouplingSlope.LimitOfTheKernelOfTheDifference
import YangMills.Construction.RunningCouplingSlope.SecondDifferentialsAtSummableFields
import YangMills.Construction.RunningCouplingSlope.TheDifferenceIsASumOfLocalDeterminants
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import YangMills.Construction.Towers.ScaledKernelsAreHolomorphicInTheFormAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.DifferenceKernelLimit
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.Tower.CriticalBranchResponse
open YangMills.Construction.Tower.ResponseOperators (ClassFnEqForm)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel)
open YangMills.Construction.LocalKernels (projPositiveEdge)
open YangMills.Construction.LocalKernels.Periodisation
open YangMills.Construction.RunningCouplingSlope.SummableFields (periodize)
variable {L k : ℕ}
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliCoeff_pauliFamily (a b : Fin 3) :
    pauliCoeff a (Matrices.ComplexMatrix2.pauliFamily b) = if a = b then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) :
    pauliCoeff a (0 : Matrices.ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem real_smul_eq_complex_smul (x : ℝ) (Y : Matrices.ComplexMatrix2) :
    x • Y = (x : ℂ) • Y := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
private theorem pauliCoeff_real_smul (x : ℝ) {Y : Matrices.ComplexMatrix2}
    (hY : Y ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (x • Y) = (x : ℂ) * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels.pauliCoeff_real_smul <;> assumption
private theorem mem_traceless_of_mem_hermitianTraceless {Y : Matrices.ComplexMatrix2}
    (h : Y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Y ∈ Matrices.ComplexMatrix2.traceless := h.2
private theorem pauliCoeff_add {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
private theorem translate_neg_translate {F : PeriodicData} (hF : IsPeriodic F) (n : Fin 4 → ℤ)
    (ι : F.Carrier) : F.translate (-n) (F.translate n ι) = ι := by
  rw [← hF.translate_add, add_neg_cancel, hF.translate_zero]
private theorem mkQuot_eq_iff {F : PeriodicData} (hF : IsPeriodic F) (s : ℕ)
    (ι ι' : F.Carrier) :
    F.mkQuot s ι = F.mkQuot s ι' ↔ ∃ n : Fin 4 → ℤ, ι' = F.translate (s • n) ι := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
private theorem tsum_over_class {F : PeriodicData} (hF : IsPeriodic F) {s : ℕ} (hs : 0 < s)
    (g : F.Carrier → ℂ) (ι : F.Carrier) :
    (∑' κ : {κ : F.Carrier // F.mkQuot s κ = F.mkQuot s ι}, g κ) =
      ∑' n : Fin 4 → ℤ, g (F.translate (s • n) ι) := by
  have hinj : Function.Injective fun n : Fin 4 → ℤ => F.translate (s • n) ι := by
    intro m n h
    have h' : F.translate (s • m) ι = F.translate (s • n) ι := h
    have e := congrArg (F.translate (-(s • n))) h'
    rw [translate_neg_translate hF, ← hF.translate_add] at e
    have e3 := hF.free _ _ e
    have e4 : s • m = s • n := add_neg_eq_zero.1 e3
    funext μ
    have := congrFun e4 μ
    simp only [Pi.smul_apply, nsmul_eq_mul] at this
    have hs' : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
    exact mul_left_cancel₀ hs' this
  let E : (Fin 4 → ℤ) ≃ {κ : F.Carrier // F.mkQuot s κ = F.mkQuot s ι} :=
    Equiv.ofBijective (fun n => ⟨F.translate (s • n) ι, ((mkQuot_eq_iff hF s ι _).2 ⟨n, rfl⟩).symm⟩)
      ⟨fun m n h => hinj (congrArg Subtype.val h), fun κ => by
        obtain ⟨n, hn⟩ := (mkQuot_eq_iff hF s ι κ.1).1 κ.2.symm
        exact ⟨n, Subtype.ext hn.symm⟩⟩
  exact (E.tsum_eq fun κ => g κ.1).symm
abbrev _root_.YangMills.SharedProofs.p39301 := @tsum_over_class
private def latticeVertexAt (L k : ℕ) (z : Fin 4 → ℤ) : Tower.FullSpace.Vertex L k k :=
  ∑ μ, z μ • InfiniteLattice.axisStep (meshAt L k k) μ
private def secondAxisEdgeAt (L k : ℕ) (z : Fin 4 → ℤ) : PeriodicOperators.PosEdge L k k :=
  ⟨InfiniteLattice.Link.forwardFrom (latticeVertexAt L k z) SlopeCoefficient.secondAxis,
    SlopeCoefficient.secondAxis, by
    simp [InfiniteLattice.Link.forwardFrom]⟩
private def thirdColourIndex (L k : ℕ) (z : Fin 4 → ℤ) : (colourEdges L k k).Carrier :=
  (2, secondAxisEdgeAt L k z)
private def scaledResponseColumn (L k : ℕ) (z : Fin 4 → ℤ) : (colourEdges L k 0).Carrier → ℂ :=
  fun ι => (finestMesh L k : ℂ) * responseKernel L k ι (thirdColourIndex L k z)
private theorem latticeVertexAt_apply (L k : ℕ) (z : Fin 4 → ℤ) (μ : Fin 4) :
    ((latticeVertexAt L k z : Tower.FullSpace.Vertex L k k) : InfiniteLattice.AmbientSpace) μ =
      (z μ : ℝ) * meshAt L k k := by
  simp only [latticeVertexAt, AddSubgroup.val_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single μ]
  · simp [InfiniteLattice.axisStep]
  · intro ν _ hν
    simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν.symm]
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p500957 := @latticeVertexAt_apply
private theorem projVertex_latticeVertexAt (L n k : ℕ) (z : Fin 4 → ℤ) :
    Tower.FullSpace.projVertex L n k k (latticeVertexAt L k z) = PeriodicLattice.offsetSite 0 z := by
  apply Subtype.ext
  funext μ
  have h1 : ((Tower.FullSpace.projVertex L n k k (latticeVertexAt L k z) : Vertex L n k k) :
      PeriodicLattice.FourTorus L n) μ =
      (((z μ : ℝ) * meshAt L k k : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rw [← latticeVertexAt_apply]
    rfl
  rw [h1]
  simp only [PeriodicLattice.offsetSite, AddSubgroup.val_finsetSum,
    AddSubgroup.coe_zsmul, Finset.sum_apply, Pi.smul_apply, zero_add]
  rw [Finset.sum_eq_single μ]
  · simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same,
      meshSize_levelDepth]
    rw [← zsmul_eq_mul]
    exact QuotientAddGroup.mk_zsmul _ _ _
  · intro ν _ hν
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν.symm]
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p3164 := @projVertex_latticeVertexAt
private theorem projVertex_add_axisStep (L n k : ℕ) (x : Tower.FullSpace.Vertex L k k) (μ : Fin 4) :
    Tower.FullSpace.projVertex L n k k (x + InfiniteLattice.axisStep (meshAt L k k) μ) =
      Tower.FullSpace.projVertex L n k k x +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ := by
  apply Subtype.ext
  funext ν
  have h1 : ((Tower.FullSpace.projVertex L n k k (x + InfiniteLattice.axisStep (meshAt L k k) μ) :
      Vertex L n k k) : PeriodicLattice.FourTorus L n) ν =
      (((x : InfiniteLattice.AmbientSpace) ν +
        (Pi.single μ (meshAt L k k) : InfiniteLattice.AmbientSpace) ν :
        ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := rfl
  have h2 : ((Tower.FullSpace.projVertex L n k k x : Vertex L n k k) :
      PeriodicLattice.FourTorus L n) ν =
      (((x : InfiniteLattice.AmbientSpace) ν : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := rfl
  rw [h1, AddCircle.coe_add]
  show _ = ((Tower.FullSpace.projVertex L n k k x : Vertex L n k k) :
    PeriodicLattice.FourTorus L n) ν + _
  rw [h2]
  congr 1
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, meshAt, PeriodicLattice.meshSize]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
abbrev _root_.YangMills.SharedProofs.p27769 := @projVertex_add_axisStep
private theorem projPositiveEdge_secondAxisEdgeAt {L n k : ℕ} (hB : ProjEdgesCompatible L n k k)
    (z : Fin 4 → ℤ) :
    (projPositiveEdge L n k k (secondAxisEdgeAt L k z)).1 =
      PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) SlopeCoefficient.secondAxis := by
  rw [hB.2.1]
  obtain ⟨h1, h2⟩ := hB.1 (secondAxisEdgeAt L k z).1
  refine PeriodicLattice.Bond.ext ?_ ?_
  · rw [h1]
    exact projVertex_latticeVertexAt L n k z
  · rw [h2]
    show Tower.FullSpace.projVertex L n k k (latticeVertexAt L k z + _) = _
    rw [projVertex_add_axisStep, projVertex_latticeVertexAt]
    rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502410 := @projPositiveEdge_secondAxisEdgeAt
open Classical in
private theorem coeffsOnEdges_pauliUnitForm (hIdx : IsPeriodic (colourEdges L k k)) {n : ℕ}
    (hC : ProjCellsClassified L n k k) (hB : ProjEdgesCompatible L n k k) (z : Fin 4 → ℤ)
    (ι : (colourEdges L k k).Carrier) :
    PeriodicForm.coeffsOnEdges L n k k (pauliUnitForm L n k z) ι =
      if (colourEdges L k k).mkQuot (periodSide L n) ι =
          (colourEdges L k k).mkQuot (periodSide L n) (thirdColourIndex L k z) then 1 else 0 := by
  have hval : PeriodicForm.coeffsOnEdges L n k k (pauliUnitForm L n k z) ι =
      pauliCoeff ι.1 (if (projPositiveEdge L n k k ι.2).1 =
        PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) SlopeCoefficient.secondAxis then
          Matrices.ComplexMatrix2.pauliFamily 2 else 0) := by
    simp only [PeriodicForm.coeffsOnEdges, toPauliCoeffs, restrictToPositiveEdges, pauliUnitForm,
      extendOddly]
    rw [if_pos (projPositiveEdge L n k k ι.2).2]
  rw [hval]
  have hcell := (hC .edge).2
  by_cases hq : (projPositiveEdge L n k k ι.2).1 =
      PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) SlopeCoefficient.secondAxis
  · rw [if_pos hq, pauliCoeff_pauliFamily]
    have hq' : projPositiveEdge L n k k ι.2 = projPositiveEdge L n k k (secondAxisEdgeAt L k z) :=
      Subtype.ext (hq.trans (projPositiveEdge_secondAxisEdgeAt hB z).symm)
    obtain ⟨m, hm⟩ := (hcell ι.2 (secondAxisEdgeAt L k z)).1 hq'
    by_cases hcol : ι.1 = 2
    · rw [if_pos hcol, if_pos]
      refine (mkQuot_eq_iff hIdx _ _ _).2 ⟨m, ?_⟩
      exact Prod.ext hcol.symm hm
    · rw [if_neg hcol, if_neg]
      intro hcl
      obtain ⟨t, ht⟩ := (mkQuot_eq_iff hIdx _ _ _).1 hcl
      exact hcol (congrArg Prod.fst ht).symm
  · rw [if_neg hq, pauliCoeff_zero, if_neg]
    intro hcl
    obtain ⟨t, ht⟩ := (mkQuot_eq_iff hIdx _ _ _).1 hcl
    apply hq
    have h4 := (hcell ι.2 (secondAxisEdgeAt L k z)).2 ⟨t, congrArg Prod.snd ht⟩
    exact (congrArg Subtype.val h4).trans (projPositiveEdge_secondAxisEdgeAt hB z)
private theorem pauliUnitForm_mem (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (z : Fin 4 → ℤ) :
    pauliUnitForm L n k z ∈ edgeFormSpace L n k k := by
  classical
  have hpauli : Matrices.ComplexMatrix2.pauliFamily 2 ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
    refine ⟨?_, (pauliFamily_mem_traceless 2)⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliZ, Matrix.conjTranspose_apply]
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [pauliUnitForm, extendOddly, if_pos hb]
    split_ifs
    · exact hpauli
    · exact Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
  · simp only [pauliUnitForm, extendOddly]
    rcases h₉ L n k hL hn hk k le_rfl b with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · rw [if_neg hr, if_pos hb]
      rfl
    · rw [if_pos hr, if_neg hb, neg_neg]
abbrev _root_.YangMills.SharedProofs.p32844 := @pauliUnitForm_mem
private theorem response_reads_as_periodized_column
    (hP0 : IsPeriodic (colourEdges L k 0)) (hPk : IsPeriodic (colourEdges L k k))
    (hcov : IsShiftInvariant (colourEdges L k k) (colourEdges L k 0) (responseKernel L k)) {n : ℕ}
    (hs : 0 < periodSide L n) (hC : ProjCellsClassified L n k k) (hB : ProjEdgesCompatible L n k k)
    (z : Fin 4 → ℤ) (hmem : pauliUnitForm L n k z ∈ edgeFormSpace L n k k)
    (hAt : ResponseImagesFullSide.AtForm L n k ⟨_, hmem⟩) :
    ClassFnEqForm L n k 0
      (restrictToPositiveEdges
        (meshScaledResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → Matrices.ComplexMatrix2))
      (periodize (colourEdges L k 0) (periodSide L n) (scaledResponseColumn L k z)) := by
  classical
  intro ι
  set s := periodSide L n with hsdef
  set u := thirdColourIndex L k z with hu
  have hRHS : toPauliCoeffs (restrictToPositiveEdges
        (meshScaledResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → Matrices.ComplexMatrix2))
        (ι.1, projPositiveEdge L n k 0 ι.2) =
      (finestMesh L k : ℂ) * PeriodicForm.coeffsOnEdges L n k 0
        (periodicResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → Matrices.ComplexMatrix2) ι := by
    have hb := (projPositiveEdge L n k 0 ι.2).2
    have hmem' := (periodicResponse L n k (pauliUnitForm L n k z)).2.1 _ hb
    simp only [toPauliCoeffs, PeriodicForm.coeffsOnEdges, restrictToPositiveEdges, meshScaledResponse]
    exact pauliCoeff_real_smul _ (mem_traceless_of_mem_hermitianTraceless hmem') _
  rw [hRHS]
  have hread := congrFun hAt.resp_coeffs ι
  simp only at hread
  rw [hread]
  have hsum : applyKernel (responseKernel L k) (PeriodicForm.coeffsOnEdges L n k k
        (pauliUnitForm L n k z)) ι =
      ∑' m : Fin 4 → ℤ, responseKernel L k ι ((colourEdges L k k).translate (s • m) u) := by
    rw [← tsum_over_class hPk hs (responseKernel L k ι) u]
    simp only [applyKernel]
    refine Eq.trans ?_ (tsum_subtype
      {κ | (colourEdges L k k).mkQuot s κ = (colourEdges L k k).mkQuot s u}
      (responseKernel L k ι)).symm
    refine tsum_congr fun κ => ?_
    rw [coeffsOnEdges_pauliUnitForm hPk hC hB z κ]
    by_cases h : (colourEdges L k k).mkQuot s κ = (colourEdges L k k).mkQuot s u
    · rw [if_pos h, mul_one, Set.indicator_of_mem (by exact h)]
    · rw [if_neg h, mul_zero, Set.indicator_of_notMem (by exact h)]
  rw [hsum, periodize, tsum_over_class hP0 hs, ← tsum_mul_left,
    ← (Equiv.neg (Fin 4 → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [scaledResponseColumn, Equiv.neg_apply, smul_neg]
  congr 1
  have h1 := hcov (-(s • m)) ι ((colourEdges L k k).translate (s • m) u)
  rw [translate_neg_translate hPk] at h1
  exact h1
private theorem summable_scaledResponseColumn (hSums : ExponentialSums.Bounds)
    (hP0 : IsPeriodic (colourEdges L k 0))
    (hPer : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0) (responseKernel L k))
    (z : Fin 4 → ℤ) : Summable (scaledResponseColumn L k z) := by
  obtain ⟨-, C, δ, hC, hδ, hb⟩ := hPer
  have h1 := ((hSums δ hδ).2.2 _ hP0 ((colourEdges L k k).pos (thirdColourIndex L k z))).1
  have h2 : Summable fun ι : (colourEdges L k 0).Carrier => ‖(finestMesh L k : ℂ)‖ * (C *
      Real.exp (-δ * TorusMetric.euclidNormVec ((colourEdges L k 0).pos ι -
        (colourEdges L k k).pos (thirdColourIndex L k z)))) := (h1.mul_left _).mul_left _
  refine Summable.of_norm_bounded h2 fun ι => ?_
  rw [scaledResponseColumn, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ _) (norm_nonneg _)
section SecondDerivatives
variable {N : ℕ}
private def HasSecondDerivAtOrigin (g : (Fin N → ℝ) → ℝ)
    (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) : Prop :=
  (∀ᶠ v in 𝓝 (0 : Fin N → ℝ), DifferentiableAt ℝ g v) ∧ HasFDerivAt (fderiv ℝ g) A 0
private theorem HasSecondDerivAtOrigin.add {g₁ g₂ : (Fin N → ℝ) → ℝ}
    {A₁ A₂ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} (h₁ : HasSecondDerivAtOrigin g₁ A₁)
    (h₂ : HasSecondDerivAtOrigin g₂ A₂) :
    HasSecondDerivAtOrigin (fun v => g₁ v + g₂ v) (A₁ + A₂) := by
  refine ⟨(h₁.1.and h₂.1).mono fun v h => h.1.add h.2, ?_⟩
  have e : fderiv ℝ (fun v => g₁ v + g₂ v) =ᶠ[𝓝 0] fderiv ℝ g₁ + fderiv ℝ g₂ := by
    filter_upwards [h₁.1, h₂.1] with v a b
    exact fderiv_fun_add a b
  exact (h₁.2.add h₂.2).congr_of_eventuallyEq e
private theorem HasSecondDerivAtOrigin.const_mul {g : (Fin N → ℝ) → ℝ}
    {A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} (c : ℝ) (h : HasSecondDerivAtOrigin g A) :
    HasSecondDerivAtOrigin (fun v => c * g v) (c • A) := by
  refine ⟨h.1.mono fun v hv => hv.const_mul c, ?_⟩
  have e : fderiv ℝ (fun v => c * g v) =ᶠ[𝓝 0] c • fderiv ℝ g := by
    filter_upwards [h.1] with v a
    exact fderiv_const_mul a c
  exact (h.2.const_smul c).congr_of_eventuallyEq e
private theorem HasSecondDerivAtOrigin.add_const {g : (Fin N → ℝ) → ℝ}
    {A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} (c : ℝ) (h : HasSecondDerivAtOrigin g A) :
    HasSecondDerivAtOrigin (fun v => g v + c) A := by
  refine ⟨h.1.mono fun v hv => hv.add_const c, ?_⟩
  have e : fderiv ℝ (fun v => g v + c) = fderiv ℝ g := by
    funext v
    exact fderiv_add_const c
  rw [e]
  exact h.2
private theorem hasSecondDerivAtOrigin_zero :
    HasSecondDerivAtOrigin (fun _ : Fin N → ℝ => (0 : ℝ)) 0 := by
  refine ⟨Eventually.of_forall fun v => differentiableAt_const _, ?_⟩
  have e : fderiv ℝ (fun _ : Fin N → ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext v
    simp
  rw [e]
  exact hasFDerivAt_const _ _
private theorem HasSecondDerivAtOrigin.mixed_deriv {g : (Fin N → ℝ) → ℝ}
    {A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ} (h : HasSecondDerivAtOrigin g A)
    (u v : Fin N → ℝ) :
    deriv (fun σ : ℝ => deriv (fun τ : ℝ => g (σ • u + τ • v)) 0) 0 = A u v := by
  have hc : Tendsto (fun σ : ℝ => σ • u) (𝓝 0) (𝓝 0) := by
    have : Continuous fun σ : ℝ => σ • u := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have ev : (fun σ : ℝ => deriv (fun τ : ℝ => g (σ • u + τ • v)) 0) =ᶠ[𝓝 0]
      fun σ => fderiv ℝ g (σ • u) v := by
    filter_upwards [hc.eventually h.1] with σ hσ
    have hline : HasDerivAt (fun τ : ℝ => σ • u + τ • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (σ • u)
    have hσ' : HasFDerivAt g (fderiv ℝ g (σ • u)) (σ • u + (0 : ℝ) • v) := by
      simpa using hσ.hasFDerivAt
    exact (hσ'.comp_hasDerivAt (0 : ℝ) hline).deriv
  rw [Filter.EventuallyEq.deriv_eq ev]
  have hline : HasDerivAt (fun σ : ℝ => σ • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h0 : HasFDerivAt (fderiv ℝ g) A ((0 : ℝ) • u) := by simpa using h.2
  have h1 := h0.comp_hasDerivAt (0 : ℝ) hline
  exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv
end SecondDerivatives
section Terms
variable {s N : ℕ}
private def localTermInCoords (D : LocalLogDetTerm L k)
    (e : Fin N ≃ (colourEdges L k 0).QuotMod s) (w : Fin N → ℝ) : ℝ :=
  D.coeff * realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op e w +
    D.coeff * Real.log ‖LinearMap.det (quotOperator (colourEdges L k 0) D.idx D.op s 0)‖
private theorem eval_eq_localTermInCoords (D : LocalLogDetTerm L k)
    (e : Fin N ≃ (colourEdges L k 0).QuotMod s) (w : Fin N → ℝ) :
    D.eval s (ofRealCoords e w) = localTermInCoords D e w := by
  simp only [LocalLogDetTerm.eval, localTermInCoords, realLogAbsDetDiffInCoords,
    realLogAbsDetDiff]
  ring
private def termSecondDeriv (D : LocalLogDetTerm L k) (e : Fin N ≃ (colourEdges L k 0).QuotMod s) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op e)) 0
private theorem hasSecondDerivAtOrigin_localTerm {D : LocalLogDetTerm L k}
    {e : Fin N ≃ (colourEdges L k 0).QuotMod s}
    (h : HasSecondFDerivAtZero (realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op e)) :
    HasSecondDerivAtOrigin (localTermInCoords D e) (D.coeff • termSecondDeriv D e) :=
  (HasSecondDerivAtOrigin.const_mul D.coeff
    (g := realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op e)
    ⟨h.1, h.2.hasFDerivAt⟩).add_const _
private theorem hasSecondDerivAtOrigin_listSum (e : Fin N ≃ (colourEdges L k 0).QuotMod s) :
    ∀ Ds : List (LocalLogDetTerm L k),
      (∀ D ∈ Ds, HasSecondFDerivAtZero
        (realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op e)) →
      HasSecondDerivAtOrigin (fun w => (Ds.map fun D => localTermInCoords D e w).sum)
        (Ds.map fun D => D.coeff • termSecondDeriv D e).sum
  | [], _ => by simpa using hasSecondDerivAtOrigin_zero
  | D :: Ds, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (hasSecondDerivAtOrigin_localTerm (h D (by simp))).add
      (hasSecondDerivAtOrigin_listSum e Ds fun D' hD' => h D' (by simp [hD']))
private theorem listSum_secondDeriv_apply (e : Fin N ≃ (colourEdges L k 0).QuotMod s)
    (u v : Fin N → ℝ) :
    ∀ Ds : List (LocalLogDetTerm L k),
      (Ds.map fun D => D.coeff • termSecondDeriv D e).sum u v =
        (Ds.map fun D => D.coeff * termSecondDeriv D e u v).sum
  | [] => by simp
  | D :: Ds => by
    simp only [List.map_cons, List.sum_cons, add_apply,
      smul_apply, smul_eq_mul, listSum_secondDeriv_apply e u v Ds]
private theorem complexifiedSecondDeriv_re_of_real {g : (Fin N → ℝ) → ℝ}
    (z z' : Coordinates.ComplexCoordinates N)
    (h : ∀ j, (z j).im = 0) (h' : ∀ j, (z' j).im = 0) :
    (complexifiedSecondDeriv g z z').re =
      fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).re) (fun j => (z' j).re) := by
  have e1 : (fun j => (z j).im) = 0 := funext h
  have e2 : (fun j => (z' j).im) = 0 := funext h'
  simp [complexifiedSecondDeriv, e1, e2]
end Terms
private theorem im_periodize {F : PeriodicData} {f : F.Carrier → ℂ} (hf : Summable f)
    (hr : ∀ κ, (f κ).im = 0) (s : ℕ) (c : F.QuotMod s) : (periodize F s f c).im = 0 := by
  have hs' : Summable fun κ : {κ : F.Carrier // F.mkQuot s κ = c} => f κ := hf.subtype _
  rw [periodize, Complex.im_tsum hs']
  simp [hr]
theorem differenceKernel_tendsto
    (hK : SummableFields.SecondDerivConvergence)
    (hB : DifferenceIsLocalLogDetSum)
    (hLogdet : PeriodicOperators.LogDetSecondDerivs.Claim)
    (hImg : ResponseImagesFullSide.ResponseImagesHold)
    (hResp : Tower.ResponseOperators.Claim)
    (hSums : ExponentialSums.Bounds)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy) :
    DifferenceKernelLimitExists.Claim := by
  classical
  intro a ha L hL k hk
  have hP0 := (hIdx L hL k 0 (Nat.zero_le k)).2.1
  have hPk := (hIdx L hL k k le_rfl).2.1
  obtain ⟨δ₀, -, hAll⟩ := hResp
  have hAt := hAll L hL k hk
  have hPer := hAt.resp_periodic
  have hcov := hPer.1
  obtain ⟨Ds, hDs, hev⟩ := hB a ha L hL k hk
  have hLpos : 0 < L := by have := hL.2; omega
  have hs : ∀ n, 0 < periodSide L n := fun n => by
    have := pow_pos hLpos n
    simp only [periodSide]
    omega
  have hfin : ∀ n, Finite ((colourEdges L k 0).QuotMod (periodSide L n)) := fun n =>
    (hQuot _ _ hP0 hP0 _ (hs n)).1.2.1
  have hsideTo : Tendsto (fun n => periodSide L n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    have h1 : n < L ^ n := Nat.lt_pow_self (by have := hL.2; omega)
    simp only [periodSide, id]
    omega
  have key : ∀ z, ∃ l : ℝ, Tendsto (fun n => differenceKernelFinite a L n k z) atTop (𝓝 l) := by
    intro z
    have hf₀ := summable_scaledResponseColumn hSums hP0 hPer 0
    have hf₁ := summable_scaledResponseColumn hSums hP0 hPer z
    have hreal : ∀ z' ι, (scaledResponseColumn L k z' ι).im = 0 := by
      intro z' ι
      have := hAt.resp_real.1 ι (thirdColourIndex L k z')
      simp [scaledResponseColumn, Complex.mul_im, this]
    let e : ∀ n, Fin (Nat.card ((colourEdges L k 0).QuotMod (periodSide L n))) ≃
        (colourEdges L k 0).QuotMod (periodSide L n) := fun n =>
      have := hfin n
      (Finite.equivFin _).symm
    let P : (Fin 4 → ℤ) → ∀ n, (colourEdges L k 0).QuotMod (periodSide L n) → ℂ :=
      fun z' n => periodize (colourEdges L k 0) (periodSide L n) (scaledResponseColumn L k z')
    let X : LocalLogDetTerm L k → ℕ → ℝ := fun D n =>
      (realLogAbsDetSecondDeriv (colourEdges L k 0) D.idx D.op (e n) (P 0 n) (P z n)).re
    have hlim1 : ∀ D ∈ Ds, ∃ l : ℝ, Tendsto (X D) atTop (𝓝 l) := by
      intro D hD
      have hA := hDs D hD
      obtain ⟨l, hl⟩ := hK _ D.idx hP0 hA.periodic D.op hA.local_op hA.symbol_isUnit hA.real_on_real
        _ _ hf₀ hf₁
      refine ⟨l.re, ?_⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨s₀, hs₀⟩ := hl ε hε
      obtain ⟨n₀, hn₀⟩ := (tendsto_atTop.1 hsideTo s₀).exists_forall_of_atTop
      refine ⟨n₀, fun n hn => ?_⟩
      have h1 := hs₀ _ (hn₀ n hn) _ (e n)
      rw [Real.dist_eq, ← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans_lt h1
    choose! lim hlim using hlim1
    have hsum : Tendsto (fun n => (Ds.map fun D => D.coeff * X D n).sum) atTop
        (𝓝 (Ds.map fun D => D.coeff * lim D).sum) :=
      tendsto_list_sum Ds fun D hD => (hlim D hD).const_mul _
    refine ⟨_, hsum.congr' ?_⟩
    have hsecond : ∀ᶠ n in atTop, ∀ D ∈ {D | D ∈ Ds}, HasSecondFDerivAtZero
        (realLogAbsDetDiffInCoords (colourEdges L k 0) D.idx D.op (e n)) := by
      refine (Filter.eventually_all_finite (List.finite_toSet Ds)).2 fun D hD => ?_
      have hA := hDs D hD
      obtain ⟨-, -, -, -, -, hrp⟩ := hLogdet _ D.idx hP0 hA.periodic D.op hA.local_op hA.symbol_isUnit
      obtain ⟨s₂, C, c', -, -, h2⟩ := hrp hA.real_on_real
      filter_upwards [hsideTo.eventually_ge_atTop s₂] with n hn
      exact (h2 _ hn _ (e n)).2.1
    filter_upwards [hev, hsecond, eventually_gt_atTop 0] with n hn1 hsec hn
    obtain ⟨c, ε, hε, hform⟩ := hn1
    obtain ⟨hC, hBd⟩ := (hCells L hL k n hn).1 k le_rfl
    have hmem : ∀ z', pauliUnitForm L n k z' ∈ edgeFormSpace L n k k := fun z' =>
      pauliUnitForm_mem h₉ hL hn hk z'
    have read : ∀ z', ClassFnEqForm L n k 0
        (restrictToPositiveEdges
          (meshScaledResponse L n k (pauliUnitForm L n k z') : Edge L n k 0 → Matrices.ComplexMatrix2))
        (P z' n) := fun z' =>
      response_reads_as_periodized_column hP0 hPk hcov (hs n) hC hBd z' (hmem z')
        (hImg L hL k hk n hn ⟨_, hmem z'⟩)
    set r₀ := meshScaledResponse L n k (pauliUnitForm L n k 0) with hr₀
    set r₁ := meshScaledResponse L n k (pauliUnitForm L n k z) with hr₁
    set g₀ : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ := fun x => (P 0 n x).re with hg₀
    set g₁ : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ := fun x => (P z n x).re with hg₁
    have hc₀ : ∀ x, ((g₀ x : ℝ) : ℂ) = P 0 n x := fun x =>
      Complex.ext (by simp [hg₀]) (by simpa using (im_periodize hf₀ (hreal 0) _ x).symm)
    have hc₁ : ∀ x, ((g₁ x : ℝ) : ℂ) = P z n x := fun x =>
      Complex.ext (by simp [hg₁]) (by simpa using (im_periodize hf₁ (hreal z) _ x).symm)
    set u : Fin _ → ℝ := fun j => g₀ (e n j) with hu
    set v : Fin _ → ℝ := fun j => g₁ (e n j) with hv
    have hE := (hasSecondDerivAtOrigin_listSum (e n) Ds hsec).add_const c
    have hm := hE.mixed_deriv u v
    have hsmall : ∀ᶠ p : ℝ × ℝ in 𝓝 0, ∀ x, |p.1 * g₀ x + p.2 * g₁ x| < ε := by
      have := hfin n
      refine eventually_all.2 fun x => ?_
      have hcont : Continuous fun p : ℝ × ℝ => |p.1 * g₀ x + p.2 * g₁ x| := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, abs_zero] at h0
      exact h0.eventually_lt_const hε
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 0,
        chainMinusBackground a (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ p.1 • (r₀ : Edge L n k 0 → Matrices.ComplexMatrix2) +
            algebraMap ℝ ℂ p.2 • (r₁ : Edge L n k 0 → Matrices.ComplexMatrix2))
          (trivialField L n k 0)) =
        (Ds.map fun D => localTermInCoords D (e n) (p.1 • u + p.2 • v)).sum + c := by
      filter_upwards [hsmall] with p hp
      have hcoe : ((p.1 • r₀ + p.2 • r₁ : edgeFormSpace L n k 0) :
          Edge L n k 0 → Matrices.ComplexMatrix2) =
          algebraMap ℝ ℂ p.1 • (r₀ : Edge L n k 0 → Matrices.ComplexMatrix2) +
            algebraMap ℝ ℂ p.2 • (r₁ : Edge L n k 0 → Matrices.ComplexMatrix2) := by
        funext b
        simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
          Complex.coe_algebraMap]
        rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul]
      have hreadp : ClassFnEqForm L n k 0
          (restrictToPositiveEdges ((p.1 • r₀ + p.2 • r₁ : edgeFormSpace L n k 0) :
            Edge L n k 0 → Matrices.ComplexMatrix2))
          (fun x => ((p.1 * g₀ x + p.2 * g₁ x : ℝ) : ℂ)) := by
        intro ι
        have e₀ := read 0 ι
        have e₁ := read z ι
        have hb := (projPositiveEdge L n k 0 ι.2).2
        have m₀ := mem_traceless_of_mem_hermitianTraceless (r₀.2.1 _ hb)
        have m₁ := mem_traceless_of_mem_hermitianTraceless (r₁.2.1 _ hb)
        simp only [toPauliCoeffs, restrictToPositiveEdges] at e₀ e₁ ⊢
        simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
        rw [pauliCoeff_add (by rw [real_smul_eq_complex_smul]; exact Submodule.smul_mem _ _ m₀)
          (by rw [real_smul_eq_complex_smul]; exact Submodule.smul_mem _ _ m₁),
          pauliCoeff_real_smul _ m₀, pauliCoeff_real_smul _ m₁, ← e₀, ← e₁, ← hc₀, ← hc₁]
        push_cast
        ring
      have hval := hform (p.1 • r₀ + p.2 • r₁) _ hreadp hp
      rw [hcoe] at hval
      rw [hval]
      congr 1
      have hfield : (fun x => p.1 * g₀ x + p.2 * g₁ x) =
          ofRealCoords (e n) (p.1 • u + p.2 • v) := by
        funext x
        simp [ofRealCoords, hu, hv]
      rw [hfield]
      exact congrArg List.sum (List.map_congr_left fun D _ => eval_eq_localTermInCoords D (e n) _)
    have hnear' : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
        chainMinusBackground a (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ p.1 • (r₀ : Edge L n k 0 → Matrices.ComplexMatrix2) +
            algebraMap ℝ ℂ p.2 • (r₁ : Edge L n k 0 → Matrices.ComplexMatrix2))
          (trivialField L n k 0)) =
        (Ds.map fun D => localTermInCoords D (e n) (p.1 • u + p.2 • v)).sum + c := hnear
    have hcurry := hnear'.curry_nhds
    have hmid : (fun σ : ℝ => deriv (fun τ : ℝ => chainMinusBackground a (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ σ • (r₀ : Edge L n k 0 → Matrices.ComplexMatrix2) +
            algebraMap ℝ ℂ τ • (r₁ : Edge L n k 0 → Matrices.ComplexMatrix2))
          (trivialField L n k 0))) 0) =ᶠ[𝓝 0]
        fun σ => deriv (fun τ : ℝ =>
          (Ds.map fun D => localTermInCoords D (e n) (σ • u + τ • v)).sum + c) 0 := by
      filter_upwards [hcurry] with σ hσ
      exact Filter.EventuallyEq.deriv_eq hσ
    have hm' : deriv (fun σ : ℝ => deriv (fun τ : ℝ =>
        (Ds.map fun D => localTermInCoords D (e n) (σ • u + τ • v)).sum + c) 0) 0 = _ := hm
    have hkap : differenceKernelFinite a L n k z = deriv (fun σ : ℝ => deriv (fun τ : ℝ =>
        chainMinusBackground a (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ σ • (r₀ : Edge L n k 0 → Matrices.ComplexMatrix2) +
            algebraMap ℝ ℂ τ • (r₁ : Edge L n k 0 → Matrices.ComplexMatrix2))
          (trivialField L n k 0))) 0) 0 :=
      rfl
    rw [hkap, hmid.deriv_eq, hm', listSum_secondDeriv_apply]
    refine congrArg List.sum (List.map_congr_left fun D _ => ?_)
    congr 1
    have him : ∀ (w : ∀ n, (colourEdges L k 0).QuotMod (periodSide L n) → ℂ),
        (∀ x, (w n x).im = 0) → ∀ j, (toCoords (e n) (w n) j).im = 0 :=
      fun w h j => h _
    exact complexifiedSecondDeriv_re_of_real _ _ (him (P 0) (im_periodize hf₀ (hreal 0) _))
      (him (P z) (im_periodize hf₁ (hreal z) _))
  choose κ hκ using key
  exact ⟨κ, hκ⟩
end YangMills.Construction.RunningCouplingSlope.DifferenceKernelLimit
end
