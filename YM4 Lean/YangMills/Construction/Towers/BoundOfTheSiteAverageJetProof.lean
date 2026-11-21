import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.PeriodicOperators.ComponentsOfAJetWithBoundedRows
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.BackgroundsCutToBondsNearAPoint
import YangMills.Construction.Towers.BoundOfTheSiteAverageJet
import YangMills.Construction.Towers.PropertiesOfTheResponse
import YangMills.Construction.Towers.TheMassiveJetsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBoundProof
open PeriodicOperators
open BackgroundJets
open Tower.FreeResolvents (trivialRescaledOperators)
open SubRadiusMeanBounds (fineFieldNorm scaledForm)
open LocalizedBackgrounds (edgeFibre)
open BackgroundProperties (vertexSmoothingFn)
open _root_.YangMills.Construction.Tower.FullSpace.IteratedSmallFieldMeans
  (FullConditions cubeEdges smallFormBall)
section Kernels
variable {N N' : Type}
def indicatorAt (i₀ : N) : N → ℂ := open Classical in fun x => if x = i₀ then 1 else 0
theorem indicatorAt_of_ne {i₀ x : N} (h : x ≠ i₀) : indicatorAt i₀ x = 0 := by simp [indicatorAt, h]
theorem kernel_apply_eq_of_represents {T : KernelMatrix N N'} {F : (N → ℂ) → N' → ℂ}
    (h : Represents T F) (j : N') (i₀ : N) : T j i₀ = F (indicatorAt i₀) j := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
theorem map_zero_of_represents {T : KernelMatrix N N'} {F : (N → ℂ) → N' → ℂ}
    (h : Represents T F) (j : N') : F 0 j = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.map_zero_of_represents <;> assumption
end Kernels
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_congr {σ : Type} {c c' : Fin 3 × σ → ℂ} {x : σ}
    (h : ∀ a, c (a, x) = c' (a, x)) : ofPauliCoeffs c x = ofPauliCoeffs c' x := by
  simp only [ofPauliCoeffs, h]
theorem isPositivelyOriented_or_opposite {a : ℝ} (e : InfiniteLattice.Link a) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
section SeriesExpansions
variable {L k : ℕ}
def edgeForm (ζ : (remainderIndex L k).Carrier → ℂ) : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs ζ
theorem edgeForm_of_pos (ζ : (remainderIndex L k).Carrier → ℂ) {e : FullSpace.Edge L k 0}
    (h : e.IsPositivelyOriented) :
    edgeForm ζ e = ∑ a, ζ (a, ⟨e, h⟩) • Matrices.ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_pos <;> assumption
theorem edgeForm_of_not_pos (ζ : (remainderIndex L k).Carrier → ℂ) {e : FullSpace.Edge L k 0}
    (h : ¬ e.IsPositivelyOriented) : edgeForm ζ e = -edgeForm ζ e.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_not_pos <;> assumption
def positiveCubeEdges (y : FullSpace.Vertex L k k) : Set (PeriodicOperators.PosEdge L k 0) :=
  {e | e.1 ∈ cubeEdges y}
def rowFieldSupport (j : (colourVertices L k k).Carrier) : Set (remainderIndex L k).Carrier :=
  edgeFibre L k (positiveCubeEdges j.2)
def rowIndexSupport (j : (colourVertices L k k).Carrier) : Set (colourVertices L k 0).Carrier :=
  {i | (i.2 : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k j.2}
theorem scaledForm_eqOn {ζ ζ' : (remainderIndex L k).Carrier → ℂ}
    {j : (colourVertices L k k).Carrier} (h : EqOn ζ ζ' (rowFieldSupport j)) :
    EqOn (scaledForm L k ζ) (scaledForm L k ζ') (cubeEdges j.2) := by
  have hp : ∀ e ∈ cubeEdges j.2, e.IsPositivelyOriented → edgeForm ζ e = edgeForm ζ' e := by
    intro e heS he
    rw [edgeForm_of_pos _ he, edgeForm_of_pos _ he]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : ((a, ⟨e, he⟩) : (remainderIndex L k).Carrier) ∈ rowFieldSupport j := heS
    rw [h this]
  have hf : ∀ e ∈ cubeEdges j.2, edgeForm ζ e = edgeForm ζ' e := by
    intro e heS
    by_cases he : e.IsPositivelyOriented
    · exact hp e heS he
    · have hr : e.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite e).resolve_left he
      rw [edgeForm_of_not_pos _ he, edgeForm_of_not_pos _ he,
        hp _ (show e.opposite ∈ cubeEdges j.2 from ⟨heS.2, heS.1⟩) hr]
  intro e heS
  exact congrArg (fun X : Matrices.ComplexMatrix2 => (finestMesh L k)⁻¹ • X) (hf e heS)
theorem rescaledR_represents (hK : ThreeMapKernels.OnFullSpace L k)
    {U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    Represents (rescaledOperators L k U).R
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k 0))
        (vertexCoordinate (FullSpace.Vertex L k k)) (iterAdjointCubeAverage L k U k)) :=
  (hK.2.2.2 U hU).2.represents
theorem rescaledR_apply (hK : ThreeMapKernels.OnFullSpace L k)
    {U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (j : (colourVertices L k k).Carrier) (i : (colourVertices L k 0).Carrier) :
    (rescaledOperators L k U).R j i =
      pauliCoeff j.1 (iterAdjointCubeAverage L k U k (ofPauliCoeffs (indicatorAt i)) j.2) :=
  kernel_apply_eq_of_represents (rescaledR_represents hK hU) j i
section Requirements
variable {ρ C : ℝ} (hS : FullConditions L k ρ C)
  (hK : ThreeMapKernels.OnFullSpace L k)
  (hsm : ∀ ζ, fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ →
    scaledForm L k ζ ∈ smallFormBall L k ρ ∧
      remainderGaugeField (scaledForm L k ζ) = gaugeFieldOfForm L k ζ)
include hS hsm in
theorem gaugeFieldOfForm_mem {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ) :
    gaugeFieldOfForm L k ζ ∈ smallIterateFields L k := by
  have h := (hS.pointwise _ (hsm ζ hζ).1).mem_smallIterate
  rwa [(hsm ζ hζ).2] at h
include hS hK hsm in
theorem vertexSmoothingFn_eq_of_eqOn {ζ ζ' : (remainderIndex L k).Carrier → ℂ}
    (hζ : fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ) (hζ' : fineFieldNorm L k ζ' ≤ ENNReal.ofReal ρ)
    (j : (colourVertices L k k).Carrier) (i : (colourVertices L k 0).Carrier)
    (h : EqOn ζ ζ' (rowFieldSupport j)) :
    vertexSmoothingFn L k ζ j i = vertexSmoothingFn L k ζ' j i := by
  change (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R j i =
    (rescaledOperators L k (gaugeFieldOfForm L k ζ')).R j i
  rw [rescaledR_apply hK (gaugeFieldOfForm_mem hS hsm hζ),
    rescaledR_apply hK (gaugeFieldOfForm_mem hS hsm hζ')]
  have h1 := hS.locality.local_R j.2 _ (hsm ζ hζ).1 _ (hsm ζ' hζ').1
    (ofPauliCoeffs (indicatorAt i)) (ofPauliCoeffs (indicatorAt i)) (ofPauliCoeffs_mem_traceless _)
    (ofPauliCoeffs_mem_traceless _) (fun _ _ => rfl) (scaledForm_eqOn h)
  rw [(hsm ζ hζ).2, (hsm ζ' hζ').2] at h1
  rw [h1]
include hS hK hsm in
theorem vertexSmoothingFn_eq_zero {ζ : (remainderIndex L k).Carrier → ℂ}
    (hζ : fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ)
    (j : (colourVertices L k k).Carrier) (i : (colourVertices L k 0).Carrier)
    (hi : i ∉ rowIndexSupport j) : vertexSmoothingFn L k ζ j i = 0 := by
  change (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R j i = 0
  have hU := gaugeFieldOfForm_mem hS hsm hζ
  rw [rescaledR_apply hK hU]
  have ha := (hsm ζ hζ).1
  have h1 := hS.locality.local_R j.2 _ ha _ ha (ofPauliCoeffs (indicatorAt i)) (ofPauliCoeffs 0)
    (ofPauliCoeffs_mem_traceless _) (ofPauliCoeffs_mem_traceless _)
    (fun x hx => ofPauliCoeffs_congr fun a => ?_) (fun _ _ => rfl)
  · rw [(hsm ζ hζ).2] at h1
    rw [h1]
    exact map_zero_of_represents (rescaledR_represents hK hU) j
  · refine indicatorAt_of_ne fun he => hi ?_
    change (i.2 : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k j.2
    rw [← he]
    exact hx
end Requirements
theorem abs_sub_le_half_of_mem_cubeOfOrder (hL : 0 < L) {y : FullSpace.Vertex L k k}
    {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L (meshAt L k 0) k y) (μ : Fin 4) :
    |x μ - (y : InfiniteLattice.AmbientSpace) μ| ≤ 1 / 2 := by
  obtain ⟨ν, hν, rfl⟩ := hx
  have hco : ((y : InfiniteLattice.AmbientSpace) + ∑ ρ, Pi.single ρ ((ν ρ : ℝ) * meshAt L k 0)) μ -
      (y : InfiniteLattice.AmbientSpace) μ = (ν μ : ℝ) * meshAt L k 0 := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hco]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have ha : 0 < meshAt L k 0 := by
    unfold meshAt
    exact zpow_pos hLr _
  have h1 : meshAt L k 0 * (L : ℝ) ^ k = 1 := by
    unfold meshAt
    simp [zpow_neg, hLr.ne']
  have h2 : 2 * |(ν μ : ℝ)| ≤ (L : ℝ) ^ k - 1 := by
    have := hν μ
    have h3 : ((2 * |ν μ| : ℤ) : ℝ) ≤ (((L : ℤ) ^ k - 1 : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h3
    exact h3
  rw [abs_mul, abs_of_pos ha]
  nlinarith
section Partition
variable (hP : RefinedCubesPartition L k k k) (hL : 0 < L)
include hP hL in
theorem rowIndexSupport_finite (j : (colourVertices L k k).Carrier) :
    (rowIndexSupport j).Finite := by
  have h := hP.ncard_eq j.2
  rw [Nat.sub_self] at h
  have hb : (cubeOfOrder L (meshAt L k 0) k j.2).Finite :=
    Set.finite_of_ncard_pos (by rw [h]; positivity)
  have hs : ((univ : Set (Fin 3)) ×ˢ cubeOfOrder L (meshAt L k 0) k j.2).Finite :=
    finite_univ.prod hb
  refine Set.Finite.of_finite_image
    (f := fun i : (colourVertices L k 0).Carrier => (i.1, (i.2 : InfiniteLattice.AmbientSpace)))
    (hs.subset ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨mem_univ _, hi⟩
  · intro i _ i₂ _ h
    have h' := Prod.ext_iff.1
      (show (i.1, (i.2 : InfiniteLattice.AmbientSpace)) =
        (i₂.1, (i₂.2 : InfiniteLattice.AmbientSpace)) from h)
    exact Prod.ext h'.1 (Subtype.ext h'.2)
include hP in
theorem encard_rows_le_three (i : (colourVertices L k 0).Carrier) :
    {j : (colourVertices L k k).Carrier | i ∈ rowIndexSupport j}.encard ≤ ((3 : ℕ) : ℕ∞) := by
  have h := hP.existsUnique_mem
  rw [Nat.sub_self] at h
  obtain ⟨y, -, hu⟩ := h i.2
  have hsub : {j : (colourVertices L k k).Carrier | i ∈ rowIndexSupport j} ⊆
      (fun a : Fin 3 => ((a, y) : (colourVertices L k k).Carrier)) '' univ := by
    intro j hj
    exact ⟨j.1, mem_univ _, Prod.ext rfl (hu _ hj).symm⟩
  calc _ ≤ _ := encard_le_encard hsub
    _ ≤ (univ : Set (Fin 3)).encard := encard_image_le _ _
    _ = ((3 : ℕ) : ℕ∞) := by simp [Set.encard_univ]
end Partition
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = fun _ => 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.gaugeFieldOfForm_zero <;> assumption
theorem vertexSmoothingJet_f00 (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    (vertexSmoothingJet L k p μPlus μMinus).f00 =
      symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R := by
  simp only [vertexSmoothingJet, jetAlongResponse, jetAlong, coeffZero,
    gaugeFieldOfForm_zero, trivialRescaledOperators]
end SeriesExpansions
theorem exp_half_sum_im_le {δ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip (2 * δ)) :
    Real.exp (1 / 2 * ∑ μ, |(κ μ).im|) ≤ Real.exp (4 * δ) := by
  refine Real.exp_le_exp.2 ?_
  have h := fun μ => hκ μ
  simp only [Fin.sum_univ_four]
  linarith [h 0, h 1, h 2, h 3]
theorem mem_imStrip_of_real {δ : ℝ} (hδ : 0 ≤ δ) {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) :
    κ ∈ imStrip (2 * δ) := fun μ => by
  rw [hκ μ, abs_zero]
  positivity
theorem vertexSmoothingJetBound_holds (hRows : PeriodicOperators.BoundedExpansionJets.ComponentBounds)
    (hAvg : SubRadiusMeanBounds.MeanBoundsBelowRadius)
    (hCut : LocalizedBackgrounds.LocalizedBackgroundBound)
    (hIter : Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hLoc : ScaledMeansLocality.MeansAreLocal)
    (hZ : BlockPathContourPivotStatement)
    (hKer : ThreeMapKernels.Claim)
    (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hResp : Tower.ResponseProperties.AllProperties)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim) : VertexSmoothingJetBound := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδI, hC₀, hAdm⟩ := hNum
  have eδ : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ₀⟩)) hδ₀
  have hδ : 0 < stripHalfWidth := by rw [eδ]; exact hδI.1
  intro L hL
  have hN := hIter.1 L hL
  obtain ⟨hρ, -, hCc, hTow⟩ := id hN
  set ρ := Tower.IteratedSmallFieldMeans.smallRadius L with hρdef
  set Cc := Tower.IteratedSmallFieldMeans.boundConstant L with hCdef
  have hCr := hResp.2.2.1
  set Cr := Tower.ResponseProperties.responseConstant with hCrdef
  set M : ℝ := Real.exp (4 * stripHalfWidth * (1 / 2)) * |Cr| with hM
  have hM0 : 0 ≤ M := by positivity
  set E : ℝ := Real.exp (4 * stripHalfWidth) with hE
  have hCc0 : 0 ≤ Cc := by linarith
  set β₁ : ℝ := Real.sqrt ((3 : ℕ) : ℝ) * (Cc * ρ⁻¹ * M) * E with hβ₁
  set β₂ : ℝ := Real.sqrt ((3 : ℕ) : ℝ) * (4 * Cc * ρ⁻¹ ^ 2 * M * M) * E with hβ₂
  have hβ₁0 : 0 ≤ β₁ := by positivity
  have hβ₂0 : 0 ≤ β₂ := by positivity
  have hC₀0 : 0 ≤ C₀ := by linarith
  refine ⟨C₀ + β₁ + β₁ + β₂, by positivity, ?_⟩
  intro k hk μPlus μMinus p hp
  have hLpos : 0 < L := by have := hL.2; omega
  have hm : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  obtain ⟨hNorm, hBelow, hSmall, -, hBdd⟩ := hAvg L hL k hk ρ Cc hN
  have hS := (hTow k hk).2
  have hK := (hKer L hL k hk).2
  have hPart : RefinedCubesPartition L k k k := (hZ L hL k k k hk le_rfl le_rfl).2.1
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos (by exact_mod_cast hLpos) _
  have hs : 0 < finestMesh L k * ρ / 3 := by positivity
  have hlocal : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) (vertexSmoothingFn L k) := by
    obtain ⟨ρ', R, hmeet, -⟩ := (hLoc L hL k hk ρ Cc hN).2
    exact ⟨ρ', R, hmeet⟩
  have hrows : PeriodicOperators.BoundedExpansionJets.RowLocalized (remainderIndex L k)
      (colourVertices L k 0) (colourVertices L k k) (vertexSmoothingFn L k) rowFieldSupport
      rowIndexSupport (finestMesh L k * ρ / 3) (1 / 2) 3 :=
    { eq_of_eqOn := fun j i ζ ζ' hζ hζ' h =>
        vertexSmoothingFn_eq_of_eqOn hS hK hSmall (hBelow ζ hζ) (hBelow ζ' hζ') j i h
      eq_zero_of_not_mem := fun j i hi ζ hζ =>
        vertexSmoothingFn_eq_zero hS hK hSmall (hBelow ζ hζ) j i hi
      finite_support := rowIndexSupport_finite hPart hLpos
      pos_near := fun j i hi μ => abs_sub_le_half_of_mem_cubeOfOrder hLpos hi μ
      encard_le := encard_rows_le_three hPart }
  have hcut : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ μ, ∀ j : (colourVertices L k k).Carrier,
      fineFieldNorm L k ((rowFieldSupport j).indicator (phaseField (remainderIndex L k) q
        (scaledResponseField L k q μ) ((colourVertices L k k).pos j))) ≤ ENNReal.ofReal M := by
    intro q hq μ j
    refine (hCut L hL k hk q hq μ _ (1 / 2) (by norm_num) (positiveCubeEdges j.2)
      (fun κ hκ ν => abs_sub_le_half_of_mem_cubeOfOrder hLpos hκ.1 ν) Cr hCr).trans
        (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
  have hb := fun κ => hRows (remainderIndex L k) (colourVertices L k 0) (colourVertices L k k)
    (hIdx L hL k 0 (Nat.zero_le _)).2.1
    (hIdx L hL k 0 (Nat.zero_le _)).1 (hIdx L hL k k le_rfl).1
    (vertexSmoothingFn L k) hlocal (fineFieldNorm L k) ρ Cc hρ hCc0 hNorm hBdd rowFieldSupport
    rowIndexSupport (finestMesh L k * ρ / 3) (1 / 2) 3 hs (by norm_num) hrows p
    (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus) M hM0
    (hcut p hp μPlus) (hcut (-p) hm μMinus) κ
  have hAss : FreeStrip.StripBounds L k stripHalfWidth C₀ := by
    rw [eδ]
    exact hAdm.2.2 L hL k hk
  have h00 : (⨆ κ ∈ imStrip (2 * stripHalfWidth),
      quotHomNorm ((vertexSmoothingJet L k p μPlus μMinus).f00 κ)) ≤ ENNReal.ofReal C₀ := by
    refine iSup₂_le fun κ hκ => ?_
    rw [vertexSmoothingJet_f00]
    exact hAss.1.vertex_avg.2 κ hκ
  have hexp : ∀ κ ∈ imStrip (2 * stripHalfWidth), ∀ x : ℝ, 0 ≤ x →
      x * Real.exp (1 / 2 * ∑ μ, |(κ μ).im|) ≤ x * E := fun κ hκ x hx =>
    mul_le_mul_of_nonneg_left (exp_half_sum_im_le hκ) hx
  have h10 : (⨆ κ ∈ stripAddShift stripHalfWidth p,
      quotHomNorm ((vertexSmoothingJet L k p μPlus μMinus).f10 κ)) ≤ ENNReal.ofReal β₁ :=
    iSup₂_le fun κ hκ => (hb κ).1.trans
      (ENNReal.ofReal_le_ofReal (hexp κ hκ.1 _ (by positivity)))
  have h01 : (⨆ κ ∈ stripSubShift stripHalfWidth p,
      quotHomNorm ((vertexSmoothingJet L k p μPlus μMinus).f01 κ)) ≤ ENNReal.ofReal β₁ :=
    iSup₂_le fun κ hκ => (hb κ).2.1.trans
      (ENNReal.ofReal_le_ofReal (hexp κ hκ.1 _ (by positivity)))
  have h11 : (⨆ κ ∈ realDualPoints,
      quotHomNorm ((vertexSmoothingJet L k p μPlus μMinus).f11 κ)) ≤ ENNReal.ofReal β₂ :=
    iSup₂_le fun κ hκ => (hb κ).2.2.trans
      (ENNReal.ofReal_le_ofReal (hexp κ (mem_imStrip_of_real hδ.le hκ) _ (by positivity)))
  calc JetQuad.jetNorm stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus)
      ≤ ENNReal.ofReal C₀ + ENNReal.ofReal β₁ + ENNReal.ofReal β₁ + ENNReal.ofReal β₂ := by
        unfold JetQuad.jetNorm
        gcongr
    _ = ENNReal.ofReal (C₀ + β₁ + β₁ + β₂) := by
        rw [ENNReal.ofReal_add (by positivity) hβ₂0, ENNReal.ofReal_add (by positivity) hβ₁0,
          ENNReal.ofReal_add hC₀0 hβ₁0]
end YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBoundProof
end
