import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FreeOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem euclidNormVec_sub_comm (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) = euclidNormVec (w - v) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_le_two_mul_of_abs_le {v : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ μ, |v μ| ≤ c) : euclidNormVec v ≤ 2 * c := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
section LocalKernels
variable {I I' I'' : PeriodicData}
def IsLocalKernel (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsShiftInvariant I I' T ∧ ∃ ϱ : ℝ, VanishesOutsideRadius I I' ϱ T
theorem finiteRange_of_invariant (hD : CovariantFiniteRange.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {ϱ : ℝ} {T : I'.Carrier → I.Carrier → ℂ}
    (hc : IsShiftInvariant I I' T) (hv : VanishesOutsideRadius I I' ϱ T) :
    HasFiniteRangeEveryRate I I' T := by
  have hq : IsPhaseCovariant I I' 0 T := fun n ι' ι => by
    rw [hc n ι' ι]
    simp [bilinDot]
  have hz : dephasedKernel I I' 0 T = T := by
    funext ι' ι
    simp [dephasedKernel, bilinDot]
  have h := (hD.2 I I' hI hI' 0 ϱ T hq hv).1
  rw [hz] at h
  exact ⟨h.periodic, h.finiteRange, h.decays⟩
theorem IsLocalKernel.finiteRange (hD : CovariantFiniteRange.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (h : IsLocalKernel I I' T) :
    HasFiniteRangeEveryRate I I' T := by
  obtain ⟨hc, ϱ, hv⟩ := h
  exact finiteRange_of_invariant hD hI hI' hc hv
def translateEquiv (hI : IsPeriodic I) (n : Fin 4 → ℤ) : I.Carrier ≃ I.Carrier where
  toFun := I.translate n
  invFun := I.translate (-n)
  left_inv ι := by
    show I.translate (-n) (I.translate n ι) = ι
    rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
  right_inv ι := by
    show I.translate n (I.translate (-n) ι) = ι
    rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
theorem IsLocalKernel.add {T S : I'.Carrier → I.Carrier → ℂ} (hT : IsLocalKernel I I' T)
    (hS : IsLocalKernel I I' S) : IsLocalKernel I I' (T + S) := by
  obtain ⟨hc, ϱ, hv⟩ := hT
  obtain ⟨hc', ϱ', hv'⟩ := hS
  refine ⟨fun n ι' ι => by simp only [Pi.add_apply, hc n ι' ι, hc' n ι' ι], max ϱ ϱ', fun ι' ι h => ?_⟩
  have h₁ : ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ := fun e => h (e.trans (le_max_left _ _))
  have h₂ : ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ' :=
    fun e => h (e.trans (le_max_right _ _))
  simp only [Pi.add_apply, hv ι' ι h₁, hv' ι' ι h₂, add_zero]
theorem IsLocalKernel.sub {T S : I'.Carrier → I.Carrier → ℂ} (hT : IsLocalKernel I I' T)
    (hS : IsLocalKernel I I' S) : IsLocalKernel I I' (T - S) := by
  obtain ⟨hc, ϱ, hv⟩ := hT
  obtain ⟨hc', ϱ', hv'⟩ := hS
  refine ⟨fun n ι' ι => by simp only [Pi.sub_apply, hc n ι' ι, hc' n ι' ι], max ϱ ϱ', fun ι' ι h => ?_⟩
  have h₁ : ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ := fun e => h (e.trans (le_max_left _ _))
  have h₂ : ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ' :=
    fun e => h (e.trans (le_max_right _ _))
  simp only [Pi.sub_apply, hv ι' ι h₁, hv' ι' ι h₂, sub_zero]
theorem IsLocalKernel.transpose (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsLocalKernel I I' T) :
    IsLocalKernel I' I (kernelTranspose I I' T) := by
  obtain ⟨hc, ϱ, hv⟩ := hT
  refine ⟨fun n ι ι' => ?_, ϱ, fun ι ι' h => ?_⟩
  · simp only [kernelTranspose, wTranspose, PeriodicData.weightOf, hI.componentOf_translate,
      hI'.componentOf_translate, hc n ι' ι]
  · rw [euclidNormVec_sub_comm] at h
    simp only [kernelTranspose, wTranspose, hv ι' ι h, mul_zero]
theorem IsLocalKernel.comp (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ}
    {S : I.Carrier → I''.Carrier → ℂ} (hT : IsLocalKernel I I' T) (hS : IsLocalKernel I'' I S) :
    IsLocalKernel I'' I' (compKernel T S) := by
  obtain ⟨hc, ϱ, hv⟩ := hT
  obtain ⟨hc', ϱ', hv'⟩ := hS
  refine ⟨fun n ι' ι'' => ?_, ϱ + ϱ', fun ι' ι'' h => ?_⟩
  · show ∑' ι, T (I'.translate n ι') ι * S ι (I''.translate n ι'') = ∑' ι, T ι' ι * S ι ι''
    rw [← (translateEquiv hI n).tsum_eq]
    refine tsum_congr fun ι => ?_
    show T (I'.translate n ι') (I.translate n ι) * S (I.translate n ι) (I''.translate n ι'') = _
    rw [hc n ι' ι, hc' n ι ι'']
  · show ∑' ι, T ι' ι * S ι ι'' = 0
    have hz : ∀ ι, T ι' ι * S ι ι'' = 0 := fun ι => by
      by_contra hne
      have h₁ : T ι' ι ≠ 0 := left_ne_zero_of_mul hne
      have h₂ : S ι ι'' ≠ 0 := right_ne_zero_of_mul hne
      have e₁ : euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ := by
        by_contra e
        exact h₁ (hv ι' ι e)
      have e₂ : euclidNormVec (I.pos ι - I''.pos ι'') ≤ ϱ' := by
        by_contra e
        exact h₂ (hv' ι ι'' e)
      refine h (le_trans ?_ (add_le_add e₁ e₂))
      have := euclidNormVec_add_le (I'.pos ι' - I.pos ι) (I.pos ι - I''.pos ι'')
      simpa using this
    simp [hz]
theorem IsLocalKernel.congr {T S : I'.Carrier → I.Carrier → ℂ} (h : IsLocalKernel I I' T)
    (e : S = T) : IsLocalKernel I I' S :=
  e ▸ h
theorem IsLocalKernel.finite_support_row (hD : CovariantFiniteRange.Claim)
    (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ} (hT : IsLocalKernel I I' T)
    (ι' : I'.Carrier) : {ι | T ι' ι ≠ 0}.Finite := by
  obtain ⟨_, ϱ, hv⟩ := hT
  refine ((hD.1 I hI).1 (I'.pos ι') ϱ).subset fun ι hι => ?_
  by_contra e
  refine hι (hv ι' ι fun h => e ?_)
  show euclidNormVec (I.pos ι - I'.pos ι') ≤ ϱ
  rwa [euclidNormVec_sub_comm]
theorem IsLocalKernel.compSummableAt {J : Type} (hD : CovariantFiniteRange.Claim)
    (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ} (S : I.Carrier → J → ℂ)
    (hT : IsLocalKernel I I' T) (ι' : I'.Carrier) (ι'' : J) : CompSummableAt T S ι' ι'' := by
  refine summable_of_hasFiniteSupport ((hT.finite_support_row hD hI ι').subset fun ι hι => ?_)
  intro e
  apply hι
  simp [e]
end LocalKernels
section KernelsFromMaps
variable {N N' : Type}
open Classical in
def indicatorAt (ι : N) : N → ℂ := fun x => if x = ι then 1 else 0
theorem kernel_eq_apply_indicator {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (hT : Represents T M) (ι' : N') (ι : N) : T ι' ι = M (indicatorAt ι) ι' := by
  rw [← (hT (indicatorAt ι)).2]
  show T ι' ι = ∑' x, T ι' x * indicatorAt ι x
  rw [tsum_eq_single ι]
  · simp [indicatorAt]
  · intro x hx
    simp [indicatorAt, hx]
theorem represents_of_finsum {Θ : Type} [Fintype Θ] (γ : N' → Θ → ℂ) (idx : Θ → N' → N)
    {M : (N → ℂ) → N' → ℂ} (hM : ∀ f ι', M f ι' = ∑ θ, γ ι' θ * f (idx θ ι')) :
    Represents (kernelOfMap M) M := by
  classical
  refine Classical.epsilon_spec (p := fun T => Represents T M)
    ⟨fun ι' ι => ∑ θ, if idx θ ι' = ι then γ ι' θ else 0, fun f => ⟨fun ι' => ?_, ?_⟩⟩
  · refine summable_of_hasFiniteSupport
      ((Finset.univ.image fun θ => idx θ ι').finite_toSet.subset fun ι hι => ?_)
    by_contra e
    apply hι
    have : ∀ θ, idx θ ι' ≠ ι := fun θ h => e (by simp [← h])
    simp [this]
  · funext ι'
    rw [hM]
    refine HasSum.tsum_eq ?_
    have h : ∀ θ ∈ (Finset.univ : Finset Θ), HasSum
        (fun ι => (if idx θ ι' = ι then γ ι' θ else 0) * f ι) (γ ι' θ * f (idx θ ι')) := fun θ _ => by
      convert hasSum_single (idx θ ι') (f := fun ι => (if idx θ ι' = ι then γ ι' θ else 0) * f ι)
        (fun ι hι => by simp [Ne.symm hι]) using 1
      simp
    convert hasSum_sum h using 1
    funext ι
    rw [Finset.sum_mul]
end KernelsFromMaps
section RangeThreeKernels
variable {I I' : PeriodicData}
theorem isRangeThreeKernel_of_map (hD : CovariantFiniteRange.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {M : (I.Carrier → ℂ) → I'.Carrier → ℂ}
    (hT : Represents T M)
    (hcov : ∀ n f ι', M f (I'.translate n ι') = M (fun ι => f (I.translate n ι)) ι')
    (hloc : ∀ f ι', (∀ ι, euclidNormVec (I'.pos ι' - I.pos ι) ≤ 3 → f ι = 0) → M f ι' = 0) :
    IsRangeThreeKernelOf I I' T M := by
  classical
  have hc : IsShiftInvariant I I' T := fun n ι' ι => by
    rw [kernel_eq_apply_indicator hT, kernel_eq_apply_indicator hT, hcov]
    congr 1
    funext x
    have hinj : I.translate n x = I.translate n ι ↔ x = ι := (translateEquiv hI n).injective.eq_iff
    simp only [indicatorAt, hinj]
  have hv : VanishesOutsideRadius I I' 3 T := fun ι' ι h => by
    rw [kernel_eq_apply_indicator hT]
    refine hloc _ _ fun x hx => ?_
    have : x ≠ ι := fun e => h (e ▸ hx)
    simp [indicatorAt, this]
  have hl : IsLocalKernel I I' T := ⟨hc, 3, hv⟩
  refine ⟨hc, hv, finiteRange_of_invariant hD hI hI' hc hv, fun f ι' => ?_, fun f => (hT f).2⟩
  refine (hl.finite_support_row hD hI ι').subset fun ι hι => ?_
  intro e
  apply hι
  simp [e]
theorem isRangeThreeKernel_of_sum (hD : CovariantFiniteRange.Claim) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {Θ : Type} [Fintype Θ] (γ : I'.Carrier → Θ → ℂ)
    (idx : Θ → I'.Carrier → I.Carrier) {M : (I.Carrier → ℂ) → I'.Carrier → ℂ}
    (hM : ∀ f ι', M f ι' = ∑ θ, γ ι' θ * f (idx θ ι'))
    (hγ : ∀ n ι' θ, γ (I'.translate n ι') θ = γ ι' θ)
    (hidx : ∀ n ι' θ, idx θ (I'.translate n ι') = I.translate n (idx θ ι'))
    (hnear : ∀ ι' θ, euclidNormVec (I'.pos ι' - I.pos (idx θ ι')) ≤ 3) :
    IsRangeThreeKernelOf I I' (kernelOfMap M) M := by
  refine isRangeThreeKernel_of_map hD hI hI' (represents_of_finsum γ idx hM)
    (fun n f ι' => ?_) fun f ι' h => ?_
  · simp only [hM, hγ, hidx]
  · rw [hM]
    exact Finset.sum_eq_zero fun θ _ => by rw [h _ (hnear ι' θ), mul_zero]
end RangeThreeKernels
section PauliCoordinates
def pauliCombination (z : Fin 3 → ℂ) : Matrices.ComplexMatrix2 :=
  ∑ c, z c • Matrices.ComplexMatrix2.pauliFamily c
theorem pauliCombination_mem (z : Fin 3 → ℂ) :
    pauliCombination z ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
theorem pauliCoeff_pauliCombination (z : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (pauliCombination z) = z a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCombination_zero : pauliCombination 0 = 0 := by simp [pauliCombination]
theorem pauliCombination_add (z w : Fin 3 → ℂ) :
    pauliCombination z + pauliCombination w = pauliCombination (z + w) := by
  simp [pauliCombination, add_smul, Finset.sum_add_distrib]
theorem pauliCombination_sub (z w : Fin 3 → ℂ) :
    pauliCombination z - pauliCombination w = pauliCombination (z - w) := by
  simp [pauliCombination, sub_smul, Finset.sum_sub_distrib]
theorem real_smul_eq_complex_smul (r : ℝ) (X : Matrices.ComplexMatrix2) : r • X = (r : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem real_smul_pauliCombination (r : ℝ) (z : Fin 3 → ℂ) :
    r • pauliCombination z = pauliCombination fun c => (r : ℂ) * z c := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.real_smul_pauliSum <;> assumption
theorem pauliCoeff_real_smul_zero (r : ℝ) (a : Fin 3) :
    pauliCoeff a (r • (0 : Matrices.ComplexMatrix2)) = 0 := by
  rw [smul_zero, ← pauliCombination_zero, pauliCoeff_pauliCombination]
  rfl
theorem ofPauliCoeffs_apply {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x = pauliCombination fun c => f (c, x) := rfl
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (f : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (f : Fin 3 × σ → ℂ) :
    ofPauliCoeffs f ∈ Matrices.GroupLieProduct.tracelessFunctions σ := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.ofPauliCoeffs_mem <;> assumption
end PauliCoordinates
section ShiftedLattices
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem meshAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    meshAt L k j ≤ 1 := by
  have : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  exact zpow_le_one_of_nonpos₀ this (by omega)
theorem meshAt_self (k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem forwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem eq_forwardFrom {a : ℝ} {b : InfiniteLattice.Link a} {μ : Fin 4}
    (h : b.terminal - b.initial = InfiniteLattice.axisStep a μ) :
    b = InfiniteLattice.Link.forwardFrom b.initial μ := by apply _root_.YangMills.Construction.Tower.FullSpace.CubesAndPaths.eq_forwardFrom <;> assumption
structure ShiftAction (L k j : ℕ) (n : Fin 4 → ℤ) : Prop where
  coe_vertexImage : ∀ x : FullSpace.Vertex L k j,
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) + castVec n
theorem shiftAction (hG : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hj : j ≤ k) (n : Fin 4 → ℤ) : ShiftAction L k j n :=
  ⟨fun x => ((hG L hL k j hk hj n).2.1 x).1⟩
section SingleShift
variable {n : Fin 4 → ℤ}
theorem ShiftAction.vertexImage_add (h : ShiftAction L k j n) (x y : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) (x + y) : FullSpace.Vertex L k j) =
      FullSpace.vertexImage (intShift n) x + y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, h.coe_vertexImage]
  abel
theorem ShiftAction.vertexImage_sub (h : ShiftAction L k j n) (x y : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) x - FullSpace.vertexImage (intShift n) y :
      FullSpace.Vertex L k j) = x - y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, h.coe_vertexImage]
  abel
theorem ShiftAction.edgeImage_endpoints (h : ShiftAction L k j n) (b : FullSpace.Edge L k j) :
    (FullSpace.edgeImage (intShift n) b).initial = FullSpace.vertexImage (intShift n) b.initial ∧
      (FullSpace.edgeImage (intShift n) b).terminal =
        FullSpace.vertexImage (intShift n) b.terminal := by
  refine Classical.epsilon_spec
    (p := fun b' : FullSpace.Edge L k j => b'.initial = FullSpace.vertexImage (intShift n) b.initial ∧
      b'.terminal = FullSpace.vertexImage (intShift n) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift n) b.initial, FullSpace.vertexImage (intShift n) b.terminal, ?_⟩,
      rfl, rfl⟩
  rw [h.vertexImage_sub]
  exact b.isAdjacent
theorem ShiftAction.edgeImage_sub (h : ShiftAction L k j n) (b : FullSpace.Edge L k j) :
    (FullSpace.edgeImage (intShift n) b).terminal - (FullSpace.edgeImage (intShift n) b).initial =
      b.terminal - b.initial := by
  rw [(h.edgeImage_endpoints b).1, (h.edgeImage_endpoints b).2, h.vertexImage_sub]
theorem ShiftAction.edgeImage_isPositivelyOriented (h : ShiftAction L k j n) {b : FullSpace.Edge L k j}
    (hb : b.IsPositivelyOriented) : (FullSpace.edgeImage (intShift n) b).IsPositivelyOriented := by
  obtain ⟨μ, e⟩ := hb
  exact ⟨μ, (h.edgeImage_sub b).trans e⟩
theorem ShiftAction.edgeImage_forwardFrom (h : ShiftAction L k j n) (x : FullSpace.Vertex L k j)
    (μ : Fin 4) :
    FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) x) μ := by
  refine InfiniteLattice.Link.ext (h.edgeImage_endpoints _).1 ?_
  rw [(h.edgeImage_endpoints _).2]
  exact h.vertexImage_add x _
theorem ShiftAction.shiftEdge_val (h : ShiftAction L k j n) (b : PosEdge L k j) :
    (shiftEdge n b).1 = FullSpace.edgeImage (intShift n) b.1 :=
  Classical.epsilon_spec (p := fun b' : PosEdge L k j =>
    b'.1 = FullSpace.edgeImage (intShift n) b.1) ⟨⟨_, h.edgeImage_isPositivelyOriented b.2⟩, rfl⟩
end SingleShift
theorem vertexImage_neg_vertexImage {n₀ : Fin 4 → ℤ} (h : ShiftAction L k j n₀)
    (h' : ShiftAction L k j (-n₀)) (x : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift (-n₀)) (FullSpace.vertexImage (intShift n₀) x) :
      FullSpace.Vertex L k j) = x := by
  apply Subtype.ext
  rw [h'.coe_vertexImage, h.coe_vertexImage]
  funext μ
  simp [castVec]
end ShiftedLattices
section Coboundaries
variable {L k j : ℕ}
open YangMills.Construction.PeriodicOperators.TowerTranslations (posEdgeForward)
theorem euclidNormVec_sub_self_le (x : AmbientSpace) : euclidNormVec (x - x) ≤ 3 := by
  simp [euclidNormVec]
theorem euclidNormVec_sub_axisStep_le {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4)
    (h₀ : 0 ≤ a) (h₁ : a ≤ 1) :
    euclidNormVec ((x : AmbientSpace) -
      ((x + InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace)) ≤ 3 := by
  have e : (x : AmbientSpace) -
      ((x + InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      -(Pi.single μ a) := by
    show (x : AmbientSpace) - ((x : AmbientSpace) + Pi.single μ a) = _
    abel
  rw [e]
  have h := euclidNormVec_le_two_mul_of_abs_le (v := -(Pi.single μ a : Fin 4 → ℝ)) (c := 3 / 2)
    (by norm_num) fun ν => by
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.neg_apply, Pi.single_eq_same, abs_neg, abs_of_nonneg h₀]
        linarith
      · simp only [Pi.neg_apply, Pi.single_eq_of_ne hν, neg_zero, abs_zero]
        norm_num
  linarith
theorem edgePauliCoordinates_ofCoeffs_apply (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ)
    (b : FullSpace.Edge L k j) (h : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs f b = pauliCombination fun c => f (c, ⟨b, h⟩) := by
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos h, dif_pos h]
  rfl
theorem edgePauliCoordinates_ofCoeffs_forwardFrom (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ)
    (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs f (InfiniteLattice.Link.forwardFrom x μ) =
      pauliCombination fun c => f (c, posEdgeForward x μ) :=
  edgePauliCoordinates_ofCoeffs_apply f _ (forwardFrom_isPositivelyOriented x μ)
theorem exists_eq_posEdgeForward (b : PosEdge L k j) :
    ∃ (x : FullSpace.Vertex L k j) (μ : Fin 4), b = posEdgeForward x μ := by
  obtain ⟨μ, h⟩ := b.2
  exact ⟨b.1.initial, μ, Subtype.ext (eq_forwardFrom h)⟩
theorem translate_posEdgeForward {n : Fin 4 → ℤ} (h : ShiftAction L k j n) (c : Fin 3)
    (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    (colourEdges L k j).translate n (c, posEdgeForward x μ) =
      (c, posEdgeForward (FullSpace.vertexImage (intShift n) x) μ) := by
  show (c, shiftEdge n (posEdgeForward x μ)) = _
  congr 1
  apply Subtype.ext
  rw [h.shiftEdge_val]
  exact h.edgeImage_forwardFrom x μ
def endpointIndices (L k j : ℕ) (θ : Fin 2) (ι : (colourEdges L k j).Carrier) :
    (colourVertices L k j).Carrier :=
  (ι.1, ![ι.2.1.terminal, ι.2.1.initial] θ)
def boundaryIndices (L k j : ℕ) (θ : Fin 4) (ι : (colourFaces L k j).Carrier) :
    (colourEdges L k j).Carrier :=
  (ι.1, ![posEdgeForward ι.2.corner ι.2.lowAxis,
    posEdgeForward (ι.2.corner + InfiniteLattice.axisStep (meshAt L k j) ι.2.lowAxis) ι.2.highAxis,
    posEdgeForward (ι.2.corner + InfiniteLattice.axisStep (meshAt L k j) ι.2.highAxis) ι.2.lowAxis,
    posEdgeForward ι.2.corner ι.2.highAxis] θ)
theorem vertexCoboundary_isRangeThreeKernel (hD : CovariantFiniteRange.Claim)
    (hT : TowerIndexSets.Claim) (hG : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j ≤ k) :
    IsRangeThreeKernelOf (colourVertices L k j) (colourEdges L k j)
      (FullSpace.scaledVertexCoboundaryKernel L k j)
      ((vertexCoordinate (FullSpace.Vertex L k j)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k j)
        FullSpace.scaledVertexCoboundary) := by
  have hm := fun n => shiftAction (j := j) hG hL hk hj n
  have ha := meshAt_pos hL k j
  have h₁ := meshAt_le_one hL hj
  refine isRangeThreeKernel_of_sum hD (hT L hL k j hj).1 (hT L hL k j hj).2.1 (Θ := Fin 2)
    (fun _ => ![(((meshAt L k j)⁻¹ : ℝ) : ℂ), -(((meshAt L k j)⁻¹ : ℝ) : ℂ)])
    (endpointIndices L k j) ?_ (fun _ _ _ => rfl) ?_ ?_
  · rintro (f : Fin 3 × FullSpace.Vertex L k j → ℂ) ⟨a, b⟩
    rw [Fin.sum_univ_two]
    show pauliCoeff a ((meshAt L k j)⁻¹ •
      (ofPauliCoeffs f b.1.terminal - ofPauliCoeffs f b.1.initial)) = _
    rw [ofPauliCoeffs_apply, ofPauliCoeffs_apply, pauliCombination_sub, real_smul_pauliCombination,
      pauliCoeff_pauliCombination]
    simp only [endpointIndices, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · rintro n ⟨a, b⟩ θ
    obtain ⟨x, μ, rfl⟩ := exists_eq_posEdgeForward b
    show endpointIndices L k j θ ((colourEdges L k j).translate n (a, posEdgeForward x μ)) =
      (colourVertices L k j).translate n (endpointIndices L k j θ (a, posEdgeForward x μ))
    rw [translate_posEdgeForward (hm n)]
    fin_cases θ
    · show (a, FullSpace.vertexImage (intShift n) x + InfiniteLattice.axisStep _ μ) =
        (a, FullSpace.vertexImage (intShift n) (x + InfiniteLattice.axisStep _ μ))
      rw [(hm n).vertexImage_add]
    · rfl
  · rintro ⟨a, b⟩ θ
    obtain ⟨x, μ, rfl⟩ := exists_eq_posEdgeForward b
    fin_cases θ
    · exact euclidNormVec_sub_axisStep_le x μ ha.le h₁
    · exact euclidNormVec_sub_self_le x
theorem edgeCoboundary_isRangeThreeKernel (hD : CovariantFiniteRange.Claim)
    (hT : TowerIndexSets.Claim) (hG : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j ≤ k) :
    IsRangeThreeKernelOf (colourEdges L k j) (colourFaces L k j)
      (FullSpace.scaledEdgeCoboundaryKernel L k j)
      ((FullSpace.edgePauliCoordinates L k j).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k j))
        FullSpace.scaledEdgeCoboundary) := by
  have hm := fun n => shiftAction (j := j) hG hL hk hj n
  have ha := meshAt_pos hL k j
  have h₁ := meshAt_le_one hL hj
  refine isRangeThreeKernel_of_sum hD (hT L hL k j hj).2.1 (hT L hL k j hj).2.2 (Θ := Fin 4)
    (fun _ => ![(((meshAt L k j)⁻¹ : ℝ) : ℂ), (((meshAt L k j)⁻¹ : ℝ) : ℂ),
      -(((meshAt L k j)⁻¹ : ℝ) : ℂ), -(((meshAt L k j)⁻¹ : ℝ) : ℂ)])
    (boundaryIndices L k j) ?_ (fun _ _ _ => rfl) ?_ ?_
  · rintro (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) ⟨a, p⟩
    have e : ∀ (x : FullSpace.Vertex L k j) (μ : Fin 4),
        (FullSpace.edgePauliCoordinates L k j).ofCoeffs f (InfiniteLattice.Link.forwardFrom x μ) =
          pauliCombination fun c => f (c, posEdgeForward x μ) :=
      fun x μ => edgePauliCoordinates_ofCoeffs_forwardFrom f x μ
    rw [Fin.sum_univ_four]
    show pauliCoeff a ((meshAt L k j)⁻¹ •
      ((FullSpace.edgePauliCoordinates L k j).ofCoeffs f (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) +
        (FullSpace.edgePauliCoordinates L k j).ofCoeffs f (InfiniteLattice.Link.forwardFrom
          (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis) -
        (FullSpace.edgePauliCoordinates L k j).ofCoeffs f (InfiniteLattice.Link.forwardFrom
          (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis) -
        (FullSpace.edgePauliCoordinates L k j).ofCoeffs f
          (InfiniteLattice.Link.forwardFrom p.corner p.highAxis))) = _
    rw [e, e, e, e, pauliCombination_add, pauliCombination_sub, pauliCombination_sub,
      real_smul_pauliCombination, pauliCoeff_pauliCombination]
    show _ = _ * f (a, posEdgeForward p.corner p.lowAxis) + _ * f (a, posEdgeForward _ p.highAxis) +
      _ * f (a, posEdgeForward _ p.lowAxis) + _ * f (a, posEdgeForward p.corner p.highAxis)
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.cons_val]
    ring
  · rintro n ⟨a, p⟩ θ
    have e₁ := fun x μ => translate_posEdgeForward (hm n) a x μ
    have e₂ := fun x y => (hm n).vertexImage_add x y
    fin_cases θ
    · exact (e₁ _ _).symm
    · show (a, posEdgeForward
          (FullSpace.vertexImage (intShift n) p.corner + InfiniteLattice.axisStep _ p.lowAxis)
          p.highAxis) = (colourEdges L k j).translate n (a, posEdgeForward
          (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis)
      rw [e₁, e₂]
    · show (a, posEdgeForward
          (FullSpace.vertexImage (intShift n) p.corner + InfiniteLattice.axisStep _ p.highAxis)
          p.lowAxis) = (colourEdges L k j).translate n (a, posEdgeForward
          (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis)
      rw [e₁, e₂]
    · exact (e₁ _ _).symm
  · rintro ⟨a, p⟩ θ
    fin_cases θ
    · exact euclidNormVec_sub_self_le _
    · exact euclidNormVec_sub_axisStep_le p.corner _ ha.le h₁
    · exact euclidNormVec_sub_axisStep_le p.corner _ ha.le h₁
    · exact euclidNormVec_sub_self_le _
end Coboundaries
section Averages
variable {L k : ℕ}
structure CubeProperties (L k m : ℕ) : Prop where
  cube_add : ∀ y v : FullSpace.Vertex L k k,
    FullSpace.cubeOfOrder L (meshAt L k m) k (y + v) =
      FullSpace.spaceTranslation (v : AmbientSpace) '' FullSpace.cubeOfOrder L (meshAt L k m) k y
  crossingPath_eq : ∀ (c : FullSpace.Edge L k k) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k k) μ →
      ∀ x : FullSpace.Vertex L k m,
        (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k m) k c.initial →
          FullSpace.crossingPath c x = (List.range (L ^ k)).map fun i =>
            InfiniteLattice.Link.forwardFrom
              (x + i • InfiniteLattice.axisStep (meshAt L k m) μ) μ
  crossingPath_vertices_mem : ∀ c : FullSpace.Edge L k k, c.IsPositivelyOriented →
    ∀ x : FullSpace.Vertex L k m,
      (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k m) k c.initial →
        ∀ z : FullSpace.Vertex L k m,
          (z = x ∨ z = FullSpace.shifted c x ∨
              ∃ b ∈ FullSpace.crossingPath c x, z = b.initial ∨ z = b.terminal) →
            (z : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k m) k c.initial ∪
              FullSpace.cubeOfOrder L (meshAt L k m) k c.terminal
  near_of_mem_union : ∀ c : FullSpace.Edge L k k, c.IsPositivelyOriented →
    ∀ x ∈ FullSpace.cubeOfOrder L (meshAt L k m) k c.initial ∪
        FullSpace.cubeOfOrder L (meshAt L k m) k c.terminal,
      ∃ ν : Fin 4 → ℤ, x = FullSpace.offsetPoint (meshAt L k m) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k m| < 3 / 2 * meshAt L k k
  near_of_mem : ∀ c : FullSpace.Edge L k k, c.IsPositivelyOriented →
    ∀ x ∈ FullSpace.cubeOfOrder L (meshAt L k m) k c.initial, ∃ ν : Fin 4 → ℤ,
      x = FullSpace.offsetPoint (meshAt L k m) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k m| < 1 / 2 * meshAt L k k
theorem cubeProperties (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) : CubeProperties L k 0 := by
  obtain ⟨-, h₁, -, h₃, -, h₅, -⟩ := hZ L hL k k k hk le_rfl le_rfl
  have h : CubeProperties L k (k - k) :=
    ⟨h₁.image_add, h₃.crossingPath_eq, h₃.crossingPath_vertex_mem, h₅.sites_near, h₅.sites_nearer⟩
  rwa [Nat.sub_self] at h
theorem euclidNormVec_sub_offsetPoint_le {y : AmbientSpace} {ν : Fin 4 → ℤ} {a B : ℝ}
    (hB : B ≤ 3 / 2) (h : ∀ ρ, |(ν ρ : ℝ) * a| < B) :
    euclidNormVec (y - FullSpace.offsetPoint a y ν) ≤ 3 := by
  have e : y - FullSpace.offsetPoint a y ν = -fun μ => (ν μ : ℝ) * a := by
    rw [FullSpace.offsetPoint, Finset.univ_sum_single]
    abel
  rw [e]
  have := euclidNormVec_le_two_mul_of_abs_le (v := -fun μ => (ν μ : ℝ) * a) (c := 3 / 2)
    (by norm_num) fun ρ => by
      simp only [Pi.neg_apply, abs_neg]
      exact ((h ρ).trans_le hB).le
  linarith
theorem vertexImage_vertexImage_neg {j : ℕ} {n : Fin 4 → ℤ} (h : ShiftAction L k j n)
    (h' : ShiftAction L k j (-n)) (x : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) (FullSpace.vertexImage (intShift (-n)) x) :
      FullSpace.Vertex L k j) = x := by
  apply Subtype.ext
  rw [h.coe_vertexImage, h'.coe_vertexImage]
  funext μ
  simp [castVec]
theorem edgeImage_neg_edgeImage {j : ℕ} {n : Fin 4 → ℤ} (h : ShiftAction L k j n)
    (h' : ShiftAction L k j (-n)) (b : FullSpace.Edge L k j) :
    FullSpace.edgeImage (intShift (-n)) (FullSpace.edgeImage (intShift n) b) = b :=
  InfiniteLattice.Link.ext
    (by rw [(h'.edgeImage_endpoints _).1, (h.edgeImage_endpoints _).1,
      vertexImage_neg_vertexImage h h'])
    (by rw [(h'.edgeImage_endpoints _).2, (h.edgeImage_endpoints _).2,
      vertexImage_neg_vertexImage h h'])
theorem edgeImage_edgeImage_neg {j : ℕ} {n : Fin 4 → ℤ} (h : ShiftAction L k j n)
    (h' : ShiftAction L k j (-n)) (b : FullSpace.Edge L k j) :
    FullSpace.edgeImage (intShift n) (FullSpace.edgeImage (intShift (-n)) b) = b :=
  InfiniteLattice.Link.ext
    (by rw [(h.edgeImage_endpoints _).1, (h'.edgeImage_endpoints _).1,
      vertexImage_vertexImage_neg h h'])
    (by rw [(h.edgeImage_endpoints _).2, (h'.edgeImage_endpoints _).2,
      vertexImage_vertexImage_neg h h'])
theorem bijOn_of_leftInverse_rightInverse {α : Type} {e e' : α → α} {s t : Set α}
    (he : MapsTo e s t) (he' : MapsTo e' t s) (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ x, e (e' x) = x) :
    BijOn e s t :=
  ⟨he, (Function.LeftInverse.injective h₁).injOn, fun y hy => ⟨e' y, he' hy, h₂ y⟩⟩
theorem vertexImage_mem_baseVerticesOfCube (F : CubeProperties L k 0) {n : Fin 4 → ℤ}
    (h₀ : ShiftAction L k 0 n) (hₖ : ShiftAction L k k n)
    {y : FullSpace.Vertex L k k} {x : FullSpace.Vertex L k 0}
    (hx : x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y) :
    FullSpace.vertexImage (intShift n) x ∈
      FullSpace.TrivialLinearization.baseVerticesOfCube L k k
        (FullSpace.vertexImage (intShift n) y) := by
  show ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) : AmbientSpace) ∈
    FullSpace.cubeOfOrder L (meshAt L k 0) k (FullSpace.vertexImage (intShift n) y)
  have e : (FullSpace.vertexImage (intShift n) y : FullSpace.Vertex L k k) =
      y + FullSpace.vertexImage (intShift n) 0 := by
    rw [add_comm, ← hₖ.vertexImage_add, zero_add]
  rw [e, F.cube_add]
  refine ⟨x, hx, ?_⟩
  show (x : AmbientSpace) +
    ((FullSpace.vertexImage (intShift n) 0 : FullSpace.Vertex L k k) : AmbientSpace) = _
  rw [hₖ.coe_vertexImage, h₀.coe_vertexImage]
  simp
theorem vertexAverage_isRangeThreeKernel (hD : CovariantFiniteRange.Claim)
    (hT : TowerIndexSets.Claim) (hG : TowerTranslations.Claim)
    (F : CubeProperties L k 0) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {R : KernelMatrix (Fin 3 × FullSpace.Vertex L k 0) (Fin 3 × FullSpace.Vertex L k k)}
    {M : ((Fin 3 × FullSpace.Vertex L k 0) → ℂ) → (Fin 3 × FullSpace.Vertex L k k) → ℂ}
    (hgives : Represents R M)
    (hmean : ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k 0),
      ∀ y : FullSpace.Vertex L k k, ofPauliCoeffs (applyKernel R (toPauliCoeffs l)) y =
        (finestMesh L k ^ 4) •
          ∑ᶠ x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y, l x) :
    IsRangeThreeKernelOf (colourVertices L k 0) (colourVertices L k k) R M := by
  have hm₀ := fun n => shiftAction (j := 0) hG hL hk (Nat.zero_le k) n
  have hmₖ := fun n => shiftAction (j := k) hG hL hk le_rfl n
  have hform : ∀ (f : Fin 3 × FullSpace.Vertex L k 0 → ℂ) (a : Fin 3) (y : FullSpace.Vertex L k k),
      M f (a, y) = pauliCoeff a ((finestMesh L k ^ 4) •
        ∑ᶠ x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y, ofPauliCoeffs f x) := by
    intro f a y
    have e := hmean (ofPauliCoeffs f) (ofPauliCoeffs_mem f) y
    rw [toPauliCoeffs_ofPauliCoeffs] at e
    rw [← (hgives f).2, ← e, ofPauliCoeffs_apply, pauliCoeff_pauliCombination]
  refine isRangeThreeKernel_of_map hD (hT L hL k 0 (Nat.zero_le k)).1 (hT L hL k k le_rfl).1
    hgives ?_ ?_
  · rintro n (f : Fin 3 × FullSpace.Vertex L k 0 → ℂ) ⟨a, y⟩
    show M f (a, FullSpace.vertexImage (intShift n) y) =
      M (fun ι => f (ι.1, FullSpace.vertexImage (intShift n) ι.2)) (a, y)
    rw [hform, hform]
    have hb : BijOn (FullSpace.vertexImage (intShift n) : FullSpace.Vertex L k 0 → _)
        (FullSpace.TrivialLinearization.baseVerticesOfCube L k k y)
        (FullSpace.TrivialLinearization.baseVerticesOfCube L k k
          (FullSpace.vertexImage (intShift n) y)) := by
      refine bijOn_of_leftInverse_rightInverse (e' := FullSpace.vertexImage (intShift (-n)))
        (fun x hx => vertexImage_mem_baseVerticesOfCube F (hm₀ n) (hmₖ n) hx) (fun x hx => ?_)
        (vertexImage_neg_vertexImage (hm₀ n) (hm₀ (-n)))
        (vertexImage_vertexImage_neg (hm₀ n) (hm₀ (-n)))
      have := vertexImage_mem_baseVerticesOfCube F (hm₀ (-n)) (hmₖ (-n)) hx
      rwa [vertexImage_neg_vertexImage (hmₖ n) (hmₖ (-n))] at this
    rw [finsum_mem_eq_of_bijOn _ hb (g := ofPauliCoeffs f)
      (f := ofPauliCoeffs fun ι => f (ι.1, FullSpace.vertexImage (intShift n) ι.2)) fun x _ => rfl]
  · rintro (f : Fin 3 × FullSpace.Vertex L k 0 → ℂ) ⟨a, y⟩ h
    rw [hform]
    have e : ∑ᶠ x ∈ FullSpace.TrivialLinearization.baseVerticesOfCube L k k y,
        ofPauliCoeffs f x = 0 := by
      refine (finsum_mem_congr (g := fun _ => (0 : Matrices.ComplexMatrix2)) rfl fun x hx => ?_).trans
        (finsum_mem_zero _)
      obtain ⟨ν, hν, hb⟩ := F.near_of_mem (InfiniteLattice.Link.forwardFrom y 0)
        (forwardFrom_isPositivelyOriented y 0) x hx
      have hn : euclidNormVec ((y : AmbientSpace) - (x : AmbientSpace)) ≤ 3 := by
        rw [hν]
        refine euclidNormVec_sub_offsetPoint_le (B := 1 / 2 * meshAt L k k) ?_ hb
        rw [meshAt_self]
        norm_num
      have hz : (fun c => f (c, x)) = 0 := by
        funext c
        exact h (c, x) hn
      rw [ofPauliCoeffs_apply, hz, pauliCombination_zero]
    rw [e]
    exact pauliCoeff_real_smul_zero _ _
theorem toPauliCoeffs_restrict_edgeValue {j : ℕ}
    (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) :
    toPauliCoeffs (FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L k j).ofCoeffs f)) = f := by
  funext ⟨a, b⟩
  show pauliCoeff a ((FullSpace.edgePauliCoordinates L k j).ofCoeffs f b.1) = _
  rw [edgePauliCoordinates_ofCoeffs_apply f b.1 b.2, pauliCoeff_pauliCombination]
theorem edgePauliCoordinates_ofCoeffs_mem {j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs f ∈
      (FullSpace.edgePairedSpace (meshAt L k j)).complexSubmodule := by
  have ha := meshAt_pos hL k j
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [edgePauliCoordinates_ofCoeffs_apply f b hb]
    exact pauliCombination_mem _
  · by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented := fun h =>
        InfiniteLattice.opposite_notMem_positiveLinks ha
          (InfiniteLattice.mem_positiveLinks_iff.mpr hb)
          (InfiniteLattice.mem_positiveLinks_iff.mpr h)
      simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos hb, if_neg hr,
        InfiniteLattice.Link.opposite_opposite]
      rfl
    · have hr : b.opposite.IsPositivelyOriented := by
        rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem b with h | h
        · exact absurd (InfiniteLattice.mem_positiveLinks_iff.mp h) hb
        · exact InfiniteLattice.mem_positiveLinks_iff.mp h
      simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_neg hb, if_pos hr, neg_neg]
theorem mapsTo_crossingIncidences (F : CubeProperties L k 0) {n : Fin 4 → ℤ}
    (h₀ : ShiftAction L k 0 n) (hₖ : ShiftAction L k k n) {c : FullSpace.Edge L k k} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k k) μ) :
    MapsTo (fun q : FullSpace.Vertex L k 0 × FullSpace.Edge L k 0 =>
        (FullSpace.vertexImage (intShift n) q.1, FullSpace.edgeImage (intShift n) q.2))
      (FullSpace.RescaledConditions.crossingIncidences L k c)
      (FullSpace.RescaledConditions.crossingIncidences L k (FullSpace.edgeImage (intShift n) c)) := by
  rintro ⟨x, b⟩ ⟨hx, hb⟩
  have hx' : FullSpace.vertexImage (intShift n) x ∈
      FullSpace.TrivialLinearization.baseVerticesOfCube L k k
        (FullSpace.edgeImage (intShift n) c).initial := by
    rw [(hₖ.edgeImage_endpoints c).1]
    exact vertexImage_mem_baseVerticesOfCube F h₀ hₖ hx
  refine ⟨hx', ?_⟩
  show FullSpace.edgeImage (intShift n) b ∈
    FullSpace.crossingPath _ (FullSpace.vertexImage (intShift n) x)
  rw [F.crossingPath_eq _ μ ((hₖ.edgeImage_sub c).trans hc) _ hx']
  rw [F.crossingPath_eq c μ hc x hx] at hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  refine List.mem_map.mpr ⟨i, hi, ?_⟩
  rw [h₀.edgeImage_forwardFrom, h₀.vertexImage_add]
theorem edgeAverage_isRangeThreeKernel (hD : CovariantFiniteRange.Claim)
    (hT : TowerIndexSets.Claim) (hG : TowerTranslations.Claim)
    (F : CubeProperties L k 0) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {Q : KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k k))}
    {M : ((Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) → ℂ) →
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k k)) → ℂ}
    (hgives : Represents Q M)
    (hmean : ∀ b' ∈ (FullSpace.edgePairedSpace (meshAt L k 0)).complexSubmodule,
      ∀ c : FullSpace.PositiveEdge (meshAt L k k),
        ofPauliCoeffs (applyKernel Q (toPauliCoeffs (FullSpace.restrictToPositiveEdges b'))) c =
          (finestMesh L k ^ 5) •
            ∑ᶠ q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1, b' q.2) :
    IsRangeThreeKernelOf (colourEdges L k 0) (colourEdges L k k) Q M := by
  have hm₀ := fun n => shiftAction (j := 0) hG hL hk (Nat.zero_le k) n
  have hmₖ := fun n => shiftAction (j := k) hG hL hk le_rfl n
  have hform : ∀ (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) (a : Fin 3)
      (c : FullSpace.PositiveEdge (meshAt L k k)),
      M f (a, c) = pauliCoeff a ((finestMesh L k ^ 5) •
        ∑ᶠ q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1,
          (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f q.2) := by
    intro f a c
    have e := hmean _ (edgePauliCoordinates_ofCoeffs_mem hL f) c
    rw [toPauliCoeffs_restrict_edgeValue] at e
    rw [← (hgives f).2, ← e, ofPauliCoeffs_apply, pauliCoeff_pauliCombination]
  have hpos : ∀ (c : FullSpace.PositiveEdge (meshAt L k k)) (q : FullSpace.Vertex L k 0 ×
      FullSpace.Edge L k 0), q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1 →
      q.2.IsPositivelyOriented := by
    rintro c ⟨x, b⟩ ⟨hx, hb⟩
    obtain ⟨μ, hμ⟩ := c.2
    have hb' : b ∈ FullSpace.crossingPath c.1 x := hb
    rw [F.crossingPath_eq c.1 μ hμ x hx] at hb'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb'
    exact forwardFrom_isPositivelyOriented _ _
  refine isRangeThreeKernel_of_map hD (hT L hL k 0 (Nat.zero_le k)).2.1 (hT L hL k k le_rfl).2.1
    hgives ?_ ?_
  · rintro n (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) ⟨a, c⟩
    show M f (a, shiftEdge n c) = M (fun ι => f (ι.1, shiftEdge n ι.2)) (a, c)
    rw [hform, hform, (hmₖ n).shiftEdge_val]
    obtain ⟨μ, hμ⟩ := c.2
    have hb : BijOn (fun q : FullSpace.Vertex L k 0 × FullSpace.Edge L k 0 =>
          (FullSpace.vertexImage (intShift n) q.1, FullSpace.edgeImage (intShift n) q.2))
        (FullSpace.RescaledConditions.crossingIncidences L k c.1)
        (FullSpace.RescaledConditions.crossingIncidences L k
          (FullSpace.edgeImage (intShift n) c.1)) := by
      refine bijOn_of_leftInverse_rightInverse (e' := fun q =>
        (FullSpace.vertexImage (intShift (-n)) q.1, FullSpace.edgeImage (intShift (-n)) q.2))
        (mapsTo_crossingIncidences F (hm₀ n) (hmₖ n) hμ) (fun q hq => ?_)
        (fun q => Prod.ext (vertexImage_neg_vertexImage (hm₀ n) (hm₀ (-n)) _)
          (edgeImage_neg_edgeImage (hm₀ n) (hm₀ (-n)) _))
        (fun q => Prod.ext (vertexImage_vertexImage_neg (hm₀ n) (hm₀ (-n)) _)
          (edgeImage_edgeImage_neg (hm₀ n) (hm₀ (-n)) _))
      have := mapsTo_crossingIncidences F (hm₀ (-n)) (hmₖ (-n))
        (((hmₖ n).edgeImage_sub c.1).trans hμ) hq
      rwa [edgeImage_neg_edgeImage (hmₖ n) (hmₖ (-n))] at this
    have hv : ∀ q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1,
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs (fun ι => f (ι.1, shiftEdge n ι.2)) q.2 =
          (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (FullSpace.edgeImage (intShift n) q.2) := by
      intro q hq
      have hp := hpos c q hq
      have e : shiftEdge n (⟨q.2, hp⟩ : PosEdge L k 0) =
          ⟨FullSpace.edgeImage (intShift n) q.2, (hm₀ n).edgeImage_isPositivelyOriented hp⟩ :=
        Subtype.ext ((hm₀ n).shiftEdge_val _)
      refine (edgePauliCoordinates_ofCoeffs_apply _ q.2 hp).trans (Eq.trans ?_
        (edgePauliCoordinates_ofCoeffs_apply f _ ((hm₀ n).edgeImage_isPositivelyOriented hp)).symm)
      simp only [e]
    exact congrArg (fun S => pauliCoeff a ((finestMesh L k ^ 5) • S))
      (finsum_mem_eq_of_bijOn _ hb (g := fun q =>
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f q.2) hv).symm
  · rintro (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) ⟨a, c⟩ h
    rw [hform]
    have e : ∑ᶠ q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1,
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f q.2 = 0 := by
      refine (finsum_mem_congr (g := fun _ => (0 : Matrices.ComplexMatrix2)) rfl fun q hq => ?_).trans
        (finsum_mem_zero _)
      have hp := hpos c q hq
      obtain ⟨hx, hb⟩ := hq
      have hz := F.crossingPath_vertices_mem c.1 c.2 q.1 hx q.2.initial
        (Or.inr (Or.inr ⟨q.2, hb, Or.inl rfl⟩))
      obtain ⟨ν, hν, hbd⟩ := F.near_of_mem_union c.1 c.2 _ hz
      have hn : euclidNormVec ((c.1.initial : AmbientSpace) - (q.2.initial : AmbientSpace)) ≤ 3 := by
        rw [hν]
        refine euclidNormVec_sub_offsetPoint_le (B := 3 / 2 * meshAt L k k) ?_ hbd
        rw [meshAt_self]
        norm_num
      have hzero : (fun c' => f (c', ⟨q.2, hp⟩)) = 0 := by
        funext c'
        exact h (c', ⟨q.2, hp⟩) hn
      rw [edgePauliCoordinates_ofCoeffs_apply f q.2 hp, hzero, pauliCombination_zero]
    rw [e]
    exact pauliCoeff_real_smul_zero _ _
end Averages
section FiniteRange
variable {L k : ℕ}
theorem IsRangeThreeKernelOf.isLocalKernel {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}
    {M : (I.Carrier → ℂ) → I'.Carrier → ℂ} (h : IsRangeThreeKernelOf I I' T M) :
    IsLocalKernel I I' T :=
  ⟨h.shift_invariant, 3, h.vanishes_outside⟩
theorem freeOperatorsFiniteRange_of_local (hD : CovariantFiniteRange.Claim)
    (hT : TowerIndexSets.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hAt : FullSpace.RescaledConditions.OnFullSpace L k)
    (hs : ∀ j : ℕ, j ≤ k → IsLocalKernel (colourVertices L k j) (colourEdges L k j)
      (FullSpace.scaledVertexCoboundaryKernel L k j))
    (hp : ∀ j : ℕ, j ≤ k → IsLocalKernel (colourEdges L k j) (colourFaces L k j)
      (FullSpace.scaledEdgeCoboundaryKernel L k j))
    (hQ : IsLocalKernel (colourEdges L k 0) (colourEdges L k k)
      (FullSpace.rescaledOperators L k fun _ => 1).Q)
    (hR : IsLocalKernel (colourVertices L k 0) (colourVertices L k k)
      (FullSpace.rescaledOperators L k fun _ => 1).R) :
    FreeOperatorsFiniteRange L k := by
  obtain ⟨-, -, -, -, -, hOne, -⟩ := hAt
  have z := Nat.zero_le k
  have iS₀ := (hT L hL k 0 z).1
  have iB₀ := (hT L hL k 0 z).2.1
  have iP₀ := (hT L hL k 0 z).2.2
  have iS := (hT L hL k k le_rfl).1
  have iB := (hT L hL k k le_rfl).2.1
  have lD : IsLocalKernel (colourVertices L k 0) (colourEdges L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).D := (hs 0 z).congr hOne.D_eq
  have lDt : IsLocalKernel (colourEdges L k 0) (colourVertices L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Dt := lD.transpose iS₀ iB₀
  have lQt : IsLocalKernel (colourEdges L k k) (colourEdges L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Qt := hQ.transpose iB₀ iB
  have lRt : IsLocalKernel (colourVertices L k k) (colourVertices L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Rt := hR.transpose iS₀ iS
  have lBt := (hp 0 z).transpose iB₀ iP₀
  have lK : IsLocalKernel (colourEdges L k 0) (colourEdges L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).K :=
    ((lBt.comp iP₀ (hp 0 z)).add ((hs 0 z).comp iS₀ ((hs 0 z).transpose iS₀ iB₀))).congr
      hOne.K_eq
  have lDelta : IsLocalKernel (colourVertices L k 0) (colourVertices L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Delta := lDt.comp iB₀ lD
  have lDRt := lD.comp iS₀ lRt
  have lRDt := hR.comp iS₀ lDt
  have lQtQ := lQt.comp iB hQ
  have lRtR := lRt.comp iS hR
  have lXi : IsLocalKernel (colourEdges L k 0) (colourEdges L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Xi := (lK.sub (lDRt.comp iS lRDt)).add lQtQ
  have lY : IsLocalKernel (colourVertices L k 0) (colourVertices L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).Y := lDelta.add lRtR
  have lX : IsLocalKernel (colourEdges L k 0) (colourEdges L k 0)
      (FullSpace.rescaledOperators L k fun _ => 1).X := lXi.sub lQtQ
  refine
    { compositions :=
        { D_Dt := lD.compSummableAt hD iS₀ _
          Dt_D := lDt.compSummableAt hD iB₀ _
          D_Rt := lD.compSummableAt hD iS₀ _
          R_Dt := hR.compSummableAt hD iS₀ _
          D_Rt_R_Dt := lDRt.compSummableAt hD iS _
          Qt_Q := lQt.compSummableAt hD iB _
          Rt_R := lRt.compSummableAt hD iS _ }
      vertexCoboundary_transpose := fun j hj =>
        ((hs j hj).transpose (hT L hL k j hj).1 (hT L hL k j hj).2.1).finiteRange hD
          (hT L hL k j hj).2.1 (hT L hL k j hj).1
      edgeCoboundary_transpose := fun j hj =>
        ((hp j hj).transpose (hT L hL k j hj).2.1 (hT L hL k j hj).2.2).finiteRange hD
          (hT L hL k j hj).2.2 (hT L hL k j hj).2.1
      edgeAverage_transpose := lQt.finiteRange hD iB iB₀
      vertexAverage_transpose := lRt.finiteRange hD iS iS₀
      K := lK.finiteRange hD iB₀ iB₀
      Delta := lDelta.finiteRange hD iS₀ iS₀
      Xi := lXi.finiteRange hD iB₀ iB₀
      Y := lY.finiteRange hD iS₀ iS₀
      X := lX.finiteRange hD iB₀ iB₀ }
end FiniteRange
theorem freeOperatorsArePeriodic (hT : TowerIndexSets.Claim) (hD : CovariantFiniteRange.Claim)
    (hG : TowerTranslations.Claim) (hZ : BlockPathContourPivotStatement)
    (hS : RescaledConditions.Holds) : FreeOperatorsArePeriodic := by
  refine ⟨fun I I' hI hI' => ⟨fun ϱ T _ hc hv => finiteRange_of_invariant hD hI hI' hc hv,
    fun T hT' hF δ hδ => ?_⟩, fun L hL k hk => ?_⟩
  · obtain ⟨ϱ, hv⟩ := hF
    exact (finiteRange_of_invariant hD hI hI' hT'.1 hv).2.2 δ hδ
  · have hAt := (hS L hL k hk).2
    obtain ⟨-, -, hU, h₁, -, hOne, hMeans⟩ := id hAt
    obtain ⟨-, hRel, -⟩ := hU _ h₁
    have F := cubeProperties hZ hL hk
    have hs := fun j (hj : j ≤ k) => vertexCoboundary_isRangeThreeKernel (j := j) hD hT hG hL hk hj
    have hp := fun j (hj : j ≤ k) => edgeCoboundary_isRangeThreeKernel (j := j) hD hT hG hL hk hj
    have hQ := edgeAverage_isRangeThreeKernel hD hT hG F hL hk hRel.Q_represents hMeans.2.2.1
    have hR := vertexAverage_isRangeThreeKernel hD hT hG F hL hk hRel.R_represents hMeans.1
    exact ⟨⟨hs, hp, hQ, hR⟩, freeOperatorsFiniteRange_of_local hD hT hL hAt
      (fun j hj => (hs j hj).isLocalKernel) (fun j hj => (hp j hj).isLocalKernel)
      hQ.isLocalKernel hR.isLocalKernel⟩
end YangMills.Construction.Tower.FreeOperators
end
