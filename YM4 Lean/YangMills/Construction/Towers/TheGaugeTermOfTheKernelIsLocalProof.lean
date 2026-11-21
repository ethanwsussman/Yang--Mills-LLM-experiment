import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFieldsProof
import YangMills.Construction.Towers.EntriesOfTheIteratedMapsProof
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheGaugeTermOfTheKernelIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.GaugeTermLocality
open Matrices
open PeriodicOperators FieldValueFunctions IteratedKernelEntries
open UnsymmetrisedKernelTerms
open PeriodicOperators.HolomorphicCoordinateClosure
open FieldValueFunctions.LocalComponents (covDiffEntry)
open TorusMetric (euclidNormVec)
theorem isSupBelow_mono {F : PeriodicData} {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ} (h : IsSupBelow F ζ ρ)
    (hle : ρ ≤ ρ') : IsSupBelow F ζ ρ' := by apply _root_.YangMills.Construction.PeriodicOperators.LocalAgreement.isSupBelow_mono <;> assumption
theorem sum_smul_pauliFamily_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem eq_sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
theorem halfTrace_sum_mul_sum (j x : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace
        ((∑ e, j e • ComplexMatrix2.pauliFamily e) * ∑ a, x a • ComplexMatrix2.pauliFamily a) =
      ∑ e, ∑ a, j e * x a *
        ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily e * ComplexMatrix2.pauliFamily a) := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.halfTrace_mul_sum_smul <;> assumption
theorem real_smul_eq_complex_smul (r : ℝ) (M : ComplexMatrix2) : r • M = (r : ℂ) • M := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
section Distances
variable {a : ℝ}
theorem finite_latticePoints_near (ha : 0 < a) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    {s : InfiniteLattice.LatticePoint a |
      ∀ i, |(s : InfiniteLattice.AmbientSpace) i - x i| < r}.Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.finite_points_near <;> assumption
theorem cubeOfOrder_coord_near {a' : ℝ} (ha' : 0 < a') {L n : ℕ} {y : InfiniteLattice.LatticePoint a}
    {x : InfiniteLattice.AmbientSpace} (hx : x ∈ cubeOfOrder L a' n y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < (L : ℝ) ^ n * a' / 2 := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.abs_sub_centre_lt_of_mem_cubeOfOrder <;> assumption
end Distances
variable {L k : ℕ}
theorem meshAt_pos (hL : 0 < L) (j : ℕ) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem pow_mul_meshAt_zero (hL : 0 < L) : (L : ℝ) ^ k * meshAt L k 0 = 1 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold meshAt
  rw [← zpow_natCast, ← zpow_add₀ hL']
  simp
theorem cubeOfOrder_coord_lt_half (hL : 0 < L) {y : Vertex L k k} {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L (meshAt L k 0) k y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < 1 / 2 := by
  have h := cubeOfOrder_coord_near (meshAt_pos hL 0) hx i
  rwa [pow_mul_meshAt_zero hL] at h
theorem terminal_sub_initial_le_one (hL : 0 < L) (c : Edge L k 0) (i : Fin 4) :
    |(c.terminal : InfiniteLattice.AmbientSpace) i -
      (c.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.abs_terminal_sub_initial_le_one <;> assumption
theorem indicesWithin_finite {hL : 0 < L}
    (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite)
    (x : InfiniteLattice.AmbientSpace) (r : ℝ) : (indicesWithin L k hL x r).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.indicesWithin_finite <;> assumption
def unitVec {N : Type} (ι : N) : N → ℂ :=
  open Classical in fun ι₀ => if ι₀ = ι then 1 else 0
theorem applyKernel_unitVec {N N' : Type} (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (unitVec ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem ofPauliCoeffs_unitVec (a : Fin 3) (x : Vertex L k 0) :
    (ofPauliCoeffs (unitVec ((a, x) : Fin 3 × Vertex L k 0)) : Vertex L k 0 → ComplexMatrix2) =
      vertexBasisFunction a x := by
  classical
  funext y
  by_cases h : y = x
  · subst h
    simp [ofPauliCoeffs, vertexBasisFunction, unitVec, Prod.ext_iff]
  · simp [ofPauliCoeffs, vertexBasisFunction, unitVec, Prod.ext_iff, h]
theorem ofCoeffs_unitVec (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    (edgePauliCoordinates L k 0).ofCoeffs (unitVec ((a, b) : Fin 3 × PositiveEdge (meshAt L k 0))) =
      basisForm a b := by
  classical
  unfold basisForm edgePauliCoordinates
  dsimp only
  refine congrArg (@extendOddly (meshAt L k 0)) (funext fun c => ?_)
  by_cases hc : c.IsPositivelyOriented
  · rw [dif_pos hc]
    by_cases e : c = b.1
    · have e' : (⟨c, hc⟩ : PositiveEdge (meshAt L k 0)) = b := Subtype.ext e
      rw [if_pos e, e']
      simp [ofPauliCoeffs, unitVec, Prod.ext_iff]
    · have e' : (⟨c, hc⟩ : PositiveEdge (meshAt L k 0)) ≠ b :=
        fun h => e (congrArg Subtype.val h)
      rw [if_neg e]
      simp [ofPauliCoeffs, unitVec, Prod.ext_iff, e']
  · rw [dif_neg hc, if_neg fun e : c = b.1 => hc (by rw [e]; exact b.2)]
theorem transposeOfValues_mem (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (g : S'.index → ComplexMatrix2) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.transposeOfValues_mem <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
section Gauge
variable {U : Edge L k 0 → ComplexMatrix2}
theorem toPauliCoeffs_covDiffTranspose_basisForm
    (HD : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (edgePauliCoordinates L k 0) (covDiff U))
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) (ι : Fin 3 × Vertex L k 0) :
    toPauliCoeffs (covDiffTranspose L k U (basisForm a b)) ι =
      PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
        (covDiff U) (a, b) ι := by
  have e := (applyKernel_unitVec _ _ _).symm.trans (congrFun (HD.swap_represents
    (unitVec ((a, b) : Fin 3 × PositiveEdge (meshAt L k 0)))).2 ι)
  have e₂ : PauliComponentsOfSymmetricKernel.transposeOnCoeffs (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (covDiff U) (unitVec ((a, b) : Fin 3 × PositiveEdge (meshAt L k 0))) =
      toPauliCoeffs (covDiffTranspose L k U (basisForm a b)) :=
    congrArg (fun B => toPauliCoeffs (covDiffTranspose L k U B))
      (ofCoeffs_unitVec a b)
  rw [e₂] at e
  exact e.symm
theorem toPauliCoeffs_iterAdjointCubeAverage
    (HA : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k))
    {d : Vertex L k 0 → ComplexMatrix2} (hd : ∀ x, d x ∈ ComplexMatrix2.traceless) :
    toPauliCoeffs (iterAdjointCubeAverage L k U k d) =
      applyKernel (iterAverageKernel L k U) (toPauliCoeffs d) := by
  have e := (HA.represents (toPauliCoeffs d)).2
  have e₂ : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L k 0))
      (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k) (toPauliCoeffs d) =
      toPauliCoeffs (iterAdjointCubeAverage L k U k d) := by
    show toPauliCoeffs (iterAdjointCubeAverage L k U k (ofPauliCoeffs (toPauliCoeffs d))) = _
    rw [ofPauliCoeffs_toPauliCoeffs hd]
  rw [e₂] at e
  exact e.symm
theorem toPauliCoeffs_iterAverageTranspose
    (HA : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k))
    {g : Vertex L k k → ComplexMatrix2} (hg : ∀ y, g y ∈ ComplexMatrix2.traceless) :
    toPauliCoeffs (iterAverageTranspose L k U g) =
      applyKernel (swapKernel (iterAverageKernel L k U)) (toPauliCoeffs g) := by
  have e := (HA.swap_represents (toPauliCoeffs g)).2
  have e₂ : PauliComponentsOfSymmetricKernel.transposeOnCoeffs (vertexCoordinate (Vertex L k 0))
      (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k) (toPauliCoeffs g) =
      toPauliCoeffs (iterAverageTranspose L k U g) :=
    congrArg (fun f => toPauliCoeffs (iterAverageTranspose L k U f))
      (ofPauliCoeffs_toPauliCoeffs hg)
  rw [e₂] at e
  exact e.symm
theorem gaugeFixingTerm_basisForm_eq_sum
    (HD : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (edgePauliCoordinates L k 0) (covDiff U))
    (HA : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k))
    (hA : ∀ f ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule,
      iterAdjointCubeAverage L k U k f ∈ (pairedFunctions (Vertex L k k)).complexSubmodule)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0))
    {D : Fin 3 × Vertex L k 0 → ℂ}
    (hD : ∀ ι, PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (covDiff U) (a, b) ι = D ι)
    {E : Finset (Fin 3 × Vertex L k 0)} {Y : Finset (Fin 3 × Vertex L k k)}
    (hE : ∀ ι, ι ∉ E → D ι = 0)
    (hY : ∀ κ, κ ∉ Y → ∀ ι ∈ E, iterAverageKernel L k U κ ι = 0)
    (x : Vertex L k 0) :
    gaugeFixingTerm L k U (basisForm a b) x =
      ∑ e, (D (e, x) + -(((L : ℝ) ^ (4 * k) : ℝ) : ℂ) *
        ∑ κ ∈ Y, iterAverageKernel L k U κ (e, x) *
          ∑ ι ∈ E, iterAverageKernel L k U κ ι * D ι) • ComplexMatrix2.pauliFamily e := by
  obtain ⟨d, hdd⟩ : ∃ d, d = covDiffTranspose L k U (basisForm a b) :=
    ⟨_, rfl⟩
  have hd₀ : d ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule := by
    rw [hdd]
    exact transposeOfValues_mem _ _ _ _
  have hd : ∀ x, d x ∈ ComplexMatrix2.traceless := fun x => hd₀ x (Set.mem_univ x)
  have cd : ∀ ι, toPauliCoeffs d ι = D ι := fun ι => by
    rw [hdd]
    exact (toPauliCoeffs_covDiffTranspose_basisForm HD a b ι).trans (hD ι)
  obtain ⟨g, hgg⟩ : ∃ g, g = iterAdjointCubeAverage L k U k d := ⟨_, rfl⟩
  have hg₀ : g ∈ (pairedFunctions (Vertex L k k)).complexSubmodule := by
    rw [hgg]
    exact hA d hd₀
  have hg : ∀ y, g y ∈ ComplexMatrix2.traceless := fun y => hg₀ y (Set.mem_univ y)
  have cg : ∀ κ, toPauliCoeffs g κ =
      ∑ ι ∈ E, iterAverageKernel L k U κ ι * D ι := by
    intro κ
    rw [hgg, toPauliCoeffs_iterAdjointCubeAverage HA hd]
    unfold applyKernel
    rw [tsum_eq_sum (s := E) fun ι hι => by rw [cd ι, hE ι hι, mul_zero]]
    exact Finset.sum_congr rfl fun ι _ => by rw [cd ι]
  have cg₀ : ∀ κ, κ ∉ Y → toPauliCoeffs g κ = 0 := by
    intro κ hκ
    rw [cg κ]
    exact Finset.sum_eq_zero fun ι hι => by rw [hY κ hκ ι hι, zero_mul]
  obtain ⟨h, hhh⟩ : ∃ h, h = iterAverageTranspose L k U g := ⟨_, rfl⟩
  have hh₀ : h ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule := by
    rw [hhh]
    exact transposeOfValues_mem _ _ _ _
  have hh : ∀ x, h x ∈ ComplexMatrix2.traceless := fun x => hh₀ x (Set.mem_univ x)
  have ch : ∀ ι, toPauliCoeffs h ι = ∑ κ ∈ Y, iterAverageKernel L k U κ ι *
      ∑ ι' ∈ E, iterAverageKernel L k U κ ι' * D ι' := by
    intro ι
    rw [hhh, toPauliCoeffs_iterAverageTranspose HA hg]
    unfold applyKernel swapKernel
    rw [tsum_eq_sum (s := Y) fun κ hκ => by rw [cg₀ κ hκ, mul_zero]]
    exact Finset.sum_congr rfl fun κ _ => by rw [cg κ]
  have eG : gaugeFixingTerm L k U (basisForm a b) x = d x - ((L : ℝ) ^ (4 * k)) • h x := by
    unfold gaugeFixingTerm
    rw [← hdd, ← hgg, ← hhh]
    rfl
  have ed : d x = ∑ e, D (e, x) • ComplexMatrix2.pauliFamily e :=
    (eq_sum_pauliCoeff_smul (hd x)).trans (Finset.sum_congr rfl fun e _ => by
      rw [show pauliCoeff e (d x) = D (e, x) from cd (e, x)])
  have eh : h x = ∑ e, (∑ κ ∈ Y, iterAverageKernel L k U κ (e, x) *
      ∑ ι' ∈ E, iterAverageKernel L k U κ ι' * D ι') • ComplexMatrix2.pauliFamily e :=
    (eq_sum_pauliCoeff_smul (hh x)).trans (Finset.sum_congr rfl fun e _ => by
      rw [show pauliCoeff e (h x) = _ from ch (e, x)])
  rw [eG, real_smul_eq_complex_smul, ed, eh, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [add_smul, neg_mul, neg_smul, mul_smul, sub_eq_add_neg]
end Gauge
section EvaluationMaps
variable {hL : 0 < L}
theorem kernel_covDiff_eq_pauliCoeff {U : Edge L k 0 → ComplexMatrix2}
    (HD : PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L k 0))
      (edgePauliCoordinates L k 0) (covDiff U))
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) (ι : Fin 3 × Vertex L k 0) :
    PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (covDiff U) (a, b) ι =
      pauliCoeff a (covDiff U (vertexBasisFunction ι.1 ι.2) b.1) := by
  refine (applyKernel_unitVec _ _ _).symm.trans
    ((congrFun (HD.represents (unitVec ι)).2 (a, b)).trans ?_)
  show pauliCoeff a (covDiff U (ofPauliCoeffs (unitVec ι)) b.1) = _
  have e : (ofPauliCoeffs (unitVec ι) : Vertex L k 0 → ComplexMatrix2) =
      vertexBasisFunction ι.1 ι.2 := ofPauliCoeffs_unitVec ι.1 ι.2
  rw [e]
theorem gaugeFixingTerm_coeffsHolomorphicOn {ρ ρ₁ : ℝ} (hρ : 0 < ρ) (h₁ : 0 < ρ₁) (hle : ρ ≤ ρ₁)
    (hC : HolomorphicCoordinateClosure.ClosureHolds)
    (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite)
    (hU : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL ζ ∈ smallIterateFields L k)
    (hK : Tower.ThreeMapKernels.OnFullSpace L k)
    (hM : ∀ U ∈ smallIterateFields L k, ∀ f ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule,
      iterAdjointCubeAverage L k U k f ∈ (pairedFunctions (Vertex L k k)).complexSubmodule)
    (hDz : ∀ (a' a : Fin 3) (b' : PositiveEdge (meshAt L k 0)) (x : Vertex L k 0),
      x ≠ b'.1.initial → x ≠ b'.1.terminal → ∀ f, covDiffEntry L k hL a' b' a x f = 0)
    (hDr : ∀ (a' a : Fin 3) (b' : PositiveEdge (meshAt L k 0)) (x : Vertex L k 0)
      (ρ : ℝ), 0 < ρ → HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
        (backgroundCoords L k hL {b'.1}) (covDiffEntry L k hL a' b' a x))
    (hAr : ∀ (y : Vertex L k k) (a' : Fin 3) (ι : Fin 3 × Vertex L k 0),
      HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ₁
        (backgroundCoords L k hL (edgesNear L k y 2))
        fun f => averageKernelFn L k hL f (a', y) ι)
    (hAz : ∀ (y : Vertex L k k) (a' a : Fin 3) (x : Vertex L k 0),
      (x : InfiniteLattice.AmbientSpace) ∉ cubeOfOrder L (meshAt L k 0) k y →
      ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ₁ → averageKernelFn L k hL f (a', y) (a, x) = 0)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    CoeffsHolomorphicOn (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2)))
      (verticesWithin L k b.1.initial 2)
      (fun ζ => gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
        (basisForm a b)) := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : InfiniteLattice.AmbientSpace, x₀ = b.1.initial := ⟨_, rfl⟩
  rw [← hx₀]
  have hY₀ : {y : Vertex L k k |
      ∀ i, |(y : InfiniteLattice.AmbientSpace) i - x₀ i| < 3 / 2}.Finite :=
    finite_latticePoints_near (meshAt_pos hL k) x₀ _
  have hends : ∀ x : Vertex L k 0, (x = b.1.initial ∨ x = b.1.terminal) →
      ∀ i, |(x : InfiniteLattice.AmbientSpace) i - x₀ i| ≤ 1 := by
    rintro x (rfl | rfl) i
    · rw [hx₀]
      simp
    · rw [hx₀]
      exact terminal_sub_initial_le_one hL b.1 i
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin 3 × Vertex L k 0),
      E = Finset.univ ×ˢ ({b.1.initial, b.1.terminal} : Finset (Vertex L k 0)) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Finset (Fin 3 × Vertex L k k),
      Y = Finset.univ ×ˢ hY₀.toFinset := ⟨_, rfl⟩
  have memE : ∀ ι : Fin 3 × Vertex L k 0, ι ∈ E ↔ (ι.2 = b.1.initial ∨ ι.2 = b.1.terminal) := by
    intro ι
    simp [hEdef]
  have memY : ∀ κ : Fin 3 × Vertex L k k, κ ∈ Y ↔
      ∀ i, |(κ.2 : InfiniteLattice.AmbientSpace) i - x₀ i| < 3 / 2 := by
    intro κ
    simp [hYdef]
  let D : ((fieldPeriodicData L k hL).Carrier → ℂ) → Fin 3 × Vertex L k 0 → ℂ :=
    fun ζ ι => covDiffEntry L k hL a b ι.1 ι.2 ζ
  let A : ((fieldPeriodicData L k hL).Carrier → ℂ) → Fin 3 × Vertex L k k →
      Fin 3 × Vertex L k 0 → ℂ :=
    fun ζ κ ι => averageKernelFn L k hL ζ κ ι
  let φ : Fin 3 → Vertex L k 0 → ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ := fun e x ζ =>
    D ζ (e, x) + -(((L : ℝ) ^ (4 * k) : ℝ) : ℂ) *
      ∑ κ ∈ Y, A ζ κ (e, x) * ∑ ι ∈ E, A ζ κ ι * D ζ ι
  have hDE : ∀ ζ ι, ι ∉ E → D ζ ι = 0 := by
    intro ζ ι hι
    have h := (memE ι).not.1 hι
    push Not at h
    exact hDz _ _ _ _ h.1 h.2 ζ
  have hYE : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ κ, κ ∉ Y → ∀ ι ∈ E, A ζ κ ι = 0 := by
    intro ζ hζ κ hκ ι hι
    have h := (memY κ).not.1 hκ
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine hAz κ.2 κ.1 ι.1 ι.2 (fun hb => ?_) ζ (isSupBelow_mono hζ hle)
    have u₁ := cubeOfOrder_coord_lt_half hL hb i
    have u₂ := hends ι.2 ((memE ι).1 hι) i
    have u₃ := abs_sub_le ((κ.2 : InfiniteLattice.AmbientSpace) i)
      ((ι.2 : InfiniteLattice.AmbientSpace) i) (x₀ i)
    have u₄ := abs_sub_comm ((κ.2 : InfiniteLattice.AmbientSpace) i)
      ((ι.2 : InfiniteLattice.AmbientSpace) i)
    linarith
  have hexp : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ x,
      gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b) x =
        ∑ e, φ e x ζ • ComplexMatrix2.pauliFamily e := by
    intro ζ hζ x
    have hs := hU ζ hζ
    exact gaugeFixingTerm_basisForm_eq_sum (hK.2.1 _ hs.1) (hK.2.2.2 _ hs).2 (hM _ hs) a b
      (fun ι => kernel_covDiff_eq_pauliCoeff (hK.2.1 _ hs.1) a b ι) (hDE ζ) (hYE ζ hζ) x
  have hT₀ : (backgroundCoords L k hL (edgesNear L k x₀ (7 / 2))).Finite :=
    (indicesWithin_finite hfin x₀ (7 / 2)).subset (by
      rintro _ ⟨e, c, hc, rfl⟩
      exact fun i => (hc i).1)
  have hT := hC (fieldPeriodicData L k hL) ρ _ hρ hT₀
  have hT₁ := hC (fieldPeriodicData L k hL) ρ₁ _ h₁ hT₀
  have hrD : ∀ ι, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesNear L k x₀ (7 / 2))) fun ζ => D ζ ι := by
    intro ι
    refine hT.of_subset _ _ ?_ (hDr a ι.1 b ι.2 ρ hρ)
    rintro _ ⟨e, c, hc, rfl⟩
    have hc' : c.1 = b.1 := hc
    refine ⟨e, c, fun i => ?_, rfl⟩
    rw [hc', hx₀]
    have := terminal_sub_initial_le_one hL b.1 i
    constructor
    · simp
    · linarith
  have hrA : ∀ κ ∈ Y, ∀ ι, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesNear L k x₀ (7 / 2))) fun ζ => A ζ κ ι := by
    intro κ hκ ι
    have hκ' := (memY κ).1 hκ
    refine hT₁.of_radius_le ρ _ hρ hle (hT₁.of_subset _ _ ?_ (hAr κ.2 κ.1 ι))
    rintro _ ⟨e, c, hc, rfl⟩
    refine ⟨e, c, fun i => ?_, rfl⟩
    have v₁ := hκ' i
    have v₂ := hc i
    have w₁ := abs_sub_le ((c.1.initial : InfiniteLattice.AmbientSpace) i)
      ((κ.2 : InfiniteLattice.AmbientSpace) i) (x₀ i)
    have w₂ := abs_sub_le ((c.1.terminal : InfiniteLattice.AmbientSpace) i)
      ((κ.2 : InfiniteLattice.AmbientSpace) i) (x₀ i)
    exact ⟨by linarith [v₂.1], by linarith [v₂.2]⟩
  have hrφ : ∀ e x, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesNear L k x₀ (7 / 2))) (φ e x) := by
    intro e x
    refine hT.add _ _ (hrD _) (hT.mul _ _ (hT.const _) (hT.sum _ _ fun κ hκ => ?_))
    refine hT.mul _ _ (hrA κ hκ _) (hT.sum _ _ fun ι _ => ?_)
    exact hT.mul _ _ (hrA κ hκ _) (hrD _)
  refine ⟨finite_latticePoints_near (meshAt_pos hL 0) x₀ _, ?_, ?_, ?_⟩
  · intro ζ hζ x hx
    have hx' : ¬ ∀ i, |(x : InfiniteLattice.AmbientSpace) i - x₀ i| < 2 := hx
    push Not at hx'
    obtain ⟨i, hi⟩ := hx'
    have hx₁ : ∀ y : Vertex L k 0, (y = b.1.initial ∨ y = b.1.terminal) → x ≠ y := by
      rintro y hy rfl
      have := hends _ hy i
      linarith
    rw [show gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
      (basisForm a b) x = _ from hexp ζ hζ x]
    refine Finset.sum_eq_zero fun e _ => ?_
    have hφ : φ e x ζ = 0 := by
      have z₁ : D ζ (e, x) = 0 := hDz _ _ _ _ (hx₁ _ (Or.inl rfl)) (hx₁ _ (Or.inr rfl)) ζ
      have z₂ : ∑ κ ∈ Y, A ζ κ (e, x) * ∑ ι ∈ E, A ζ κ ι * D ζ ι = 0 := by
        refine Finset.sum_eq_zero fun κ _ => ?_
        by_cases hb : (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k κ.2
        · have z₃ : ∑ ι ∈ E, A ζ κ ι * D ζ ι = 0 := by
            refine Finset.sum_eq_zero fun ι hι => ?_
            have z₄ : A ζ κ ι = 0 := by
              refine hAz κ.2 κ.1 ι.1 ι.2 (fun hb' => ?_) ζ (isSupBelow_mono hζ hle)
              have u₁ := cubeOfOrder_coord_lt_half hL hb i
              have u₂ := cubeOfOrder_coord_lt_half hL hb' i
              have u₃ := hends ι.2 ((memE ι).1 hι) i
              have u₄ := abs_sub_le ((x : InfiniteLattice.AmbientSpace) i)
                ((κ.2 : InfiniteLattice.AmbientSpace) i) ((ι.2 : InfiniteLattice.AmbientSpace) i)
              have u₅ := abs_sub_le ((x : InfiniteLattice.AmbientSpace) i)
                ((ι.2 : InfiniteLattice.AmbientSpace) i) (x₀ i)
              have u₆ := abs_sub_comm ((κ.2 : InfiniteLattice.AmbientSpace) i)
                ((ι.2 : InfiniteLattice.AmbientSpace) i)
              linarith
            rw [z₄, zero_mul]
          rw [z₃, mul_zero]
        · have z₄ : A ζ κ (e, x) = 0 := hAz κ.2 κ.1 e x hb ζ (isSupBelow_mono hζ hle)
          rw [z₄, zero_mul]
      show D ζ (e, x) + _ * (∑ κ ∈ Y, A ζ κ (e, x) * ∑ ι ∈ E, A ζ κ ι * D ζ ι) = 0
      rw [z₁, z₂, mul_zero, add_zero]
    rw [hφ, zero_smul]
  · intro ζ hζ x
    show gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b) x ∈ _
    rw [hexp ζ hζ x]
    exact sum_smul_pauliFamily_mem _
  · intro x _ e
    refine hT.congr_below _ _ (fun ζ hζ => ?_) (hrφ e x)
    rw [hexp ζ hζ x, pauliCoeff_sum_smul]
end EvaluationMaps
section Pairing
variable {hL : 0 < L}
theorem traceFinsumPairing_holomorphic {P : Type} {ρ : ℝ}
    {T T₁ T₂ : Set (fieldPeriodicData L k hL).Carrier} {S' S : Set P}
    {Φ' Φ : ((fieldPeriodicData L k hL).Carrier → ℂ) → P → ComplexMatrix2}
    (hT : ClosureProperties (fieldPeriodicData L k hL) ρ T)
    (V' : CoeffsHolomorphicOn (fieldPeriodicData L k hL) ρ T₁ S' Φ')
    (V : CoeffsHolomorphicOn (fieldPeriodicData L k hL) ρ T₂ S Φ) (h₁ : T₁ ⊆ T) (h₂ : T₂ ⊆ T) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T
      fun ζ => Tower.traceFinsumPairing (Φ' ζ) (Φ ζ) := by
  classical
  have r' : ∀ p ∈ S', ∀ e, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T
      fun ζ => pauliCoeff e (Φ' ζ p) :=
    fun p hp e => hT.of_subset _ _ h₁ (V'.holomorphic_coeff p hp e)
  have r : ∀ e p, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T
      fun ζ => pauliCoeff e (Φ ζ p) := by
    intro e p
    by_cases hp : p ∈ S
    · exact hT.of_subset _ _ h₂ (V.holomorphic_coeff p hp e)
    · refine hT.congr_below _ _ (fun ζ hζ => ?_) (hT.const 0)
      rw [V.eq_zero_of_not_mem ζ hζ p hp]
      simpa using (pauliCoeff_sum_smul (fun _ => 0) e).symm
  have hR : HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T
      fun ζ => ∑ p ∈ V'.finite.toFinset,
        ∑ e, ∑ a, pauliCoeff e (Φ' ζ p) * pauliCoeff a (Φ ζ p) *
          ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily e * ComplexMatrix2.pauliFamily a) :=
    hT.sum _ _ fun p hp => hT.sum _ _ fun e _ => hT.sum _ _ fun a _ =>
      hT.mul _ _ (hT.mul _ _ (r' p (V'.finite.mem_toFinset.1 hp) e) (r a p)) (hT.const _)
  refine hT.congr_below _ _ (fun ζ hζ => ?_) hR
  unfold Tower.traceFinsumPairing
  rw [finsum_eq_sum_of_support_subset (s := V'.finite.toFinset) _ fun p hp => ?_]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [← halfTrace_sum_mul_sum, ← eq_sum_pauliCoeff_smul (V'.mem_traceless ζ hζ p),
      ← eq_sum_pauliCoeff_smul (V.mem_traceless ζ hζ p)]
  · by_contra hn
    refine hp ?_
    have hn' : p ∉ S' := by simpa using hn
    simp [V'.eq_zero_of_not_mem ζ hζ p hn', ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem traceFinsumPairing_eq_zero {P : Type} {f f' : P → ComplexMatrix2}
    (h : ∀ p, f p = 0 ∨ f' p = 0) :
    Tower.traceFinsumPairing f f' = 0 := by
  unfold Tower.traceFinsumPairing
  refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
  rcases h p with h | h <;> simp [h, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
end Pairing
theorem claim (hC : HolomorphicCoordinateClosure.ClosureHolds)
    (hFin : CovariantFiniteRange.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement)
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hI : IteratedKernelEntries.Claim)
    (hE : FieldValueFunctions.LocalComponents.EntriesAreLocalAndEntire)
    (hKer : Tower.ThreeMapKernels.Claim)
    (hRel : CovariantIterRelations) : GaugeTermLocality.Claim := by
  intro L hL hStd k hk
  obtain ⟨ρ₁, h₁, hI, -⟩ := hI L hL hStd k hk
  obtain ⟨ρ₂, h₂, hS⟩ := (hSmall L hL hStd k hk).2
  obtain ⟨-, hE₂, -⟩ := hE L hL hStd k
  have hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite :=
    (hFin.1 _ ((hTower L hStd k).2 _).1).1
  have hM : ∀ U ∈ smallIterateFields L k, ∀ f ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule,
      iterAdjointCubeAverage L k U k f ∈ (pairedFunctions (Vertex L k k)).complexSubmodule := by
    intro U hU f hf
    obtain ⟨T, hTval, -, -⟩ := (hRel L hStd k k le_rfl U hU).2.2
    have e : iterAdjointCubeAverage L k U k f = (T ⟨f, hf⟩).1 := (hTval ⟨f, hf⟩).symm
    rw [e]
    exact (T ⟨f, hf⟩).2
  have hρ : 0 < min ρ₁ ρ₂ := lt_min h₁ h₂
  have hV : ∀ (a : Fin 3) (b : PositiveEdge (meshAt L k 0)),
      CoeffsHolomorphicOn (fieldPeriodicData L k hL) (min ρ₁ ρ₂)
        (backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2)))
        (verticesWithin L k b.1.initial 2)
        (fun ζ => gaugeFixingTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
          (basisForm a b)) :=
    gaugeFixingTerm_coeffsHolomorphicOn hρ h₁ (min_le_left _ _) hC hfin
      (fun ζ hζ => hS ζ (isSupBelow_mono hζ (min_le_right _ _))) (hKer L hStd k hk).2 hM
      (fun a' a b' x n₁ n₂ => (hE₂ a' a b' x).1 n₁ n₂) (fun a' a b' x => (hE₂ a' a b' x).2)
      (fun y a' ι => (hI y a').2.1 ι) (fun y a' a x => (hI y a').2.2 a x)
  refine ⟨min ρ₁ ρ₂, hρ, fun a' b' a b => ⟨?_, fun _ => ?_⟩⟩
  · rintro ⟨i, hi⟩ ζ hζ
    refine traceFinsumPairing_eq_zero fun x => ?_
    by_cases hx : x ∈ verticesWithin L k b'.1.initial 2
    · refine Or.inr ((hV a b).eq_zero_of_not_mem ζ hζ x fun hn => ?_)
      have u₁ := hx i
      have u₂ := hn i
      have u₃ := abs_sub_le ((b.1.initial : InfiniteLattice.AmbientSpace) i)
        ((x : InfiniteLattice.AmbientSpace) i) ((b'.1.initial : InfiniteLattice.AmbientSpace) i)
      have u₄ := abs_sub_comm ((b.1.initial : InfiniteLattice.AmbientSpace) i)
        ((x : InfiniteLattice.AmbientSpace) i)
      linarith
    · exact Or.inl ((hV a' b').eq_zero_of_not_mem ζ hζ x hx)
  · have hT : ClosureProperties (fieldPeriodicData L k hL) (min ρ₁ ρ₂)
        (indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2)) :=
      hC _ _ _ hρ ((indicesWithin_finite hfin _ _).union (indicesWithin_finite hfin _ _))
    refine traceFinsumPairing_holomorphic hT (hV a' b') (hV a b) ?_ ?_
    · rintro _ ⟨e, c, hc, rfl⟩
      refine Or.inl fun i => ?_
      have := (hc i).1
      show |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
      linarith
    · rintro _ ⟨e, c, hc, rfl⟩
      exact Or.inr fun i => (hc i).1
end YangMills.Construction.Tower.FullSpace.GaugeTermLocality
end
