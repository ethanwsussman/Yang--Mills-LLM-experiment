import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOneProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.RunningCouplingSlope.NoiseAndCovarianceAtOneArePositive
import YangMills.Construction.RunningCouplingSlope.SymbolsOfThePlainSaddlesProof
import YangMills.Construction.RunningCouplingSlope.TheFlatPlainStepIsLocalProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FlatNoisePositivity
open Tower PeriodicOperators Tower.RescaledConditions Matrices
section Kernels
variable {N N' : Type}
private theorem kernelMatrix_apply_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (i' : N') (i : N) : T i' i = M (open Classical in Pi.single i 1) i' := by apply _root_.YangMills.SharedProofs.p81620 <;> assumption
private theorem kernelOfMap_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : kernelOfMap M = T := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.kernelOfMap_eq <;> assumption
private theorem represents_of_linear [Finite N] {M : (N → ℂ) → N' → ℂ}
    (hadd : ∀ f g, M (f + g) = M f + M g) (hsmul : ∀ (w : ℂ) f, M (w • f) = w • M f) :
    Represents (open Classical in fun i' i => M (Pi.single i 1) i') M := by
  classical
  have := Fintype.ofFinite N
  have h0 : M 0 = 0 := by simpa using hsmul 0 0
  have hsum : ∀ (s : Finset N) (F : N → N → ℂ), M (∑ i ∈ s, F i) = ∑ i ∈ s, M (F i) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  intro f
  refine ⟨fun i' => (hasSum_fintype _).summable, ?_⟩
  funext i'
  have hf : f = ∑ i, f i • (Pi.single i 1 : N → ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hf, hsum]
  simp only [applyKernel, tsum_fintype, Finset.sum_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end Kernels
section Edges
variable {L n k m : ℕ}
private theorem two_le_side (hL : Conventions.IsAdmissibleBlockingFactor L) : 2 ≤ L := by
  have := hL.2
  omega
private theorem xor_oriented (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hm : m ≤ k) (b : Edge L n k m) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.uniqueOrientation <;> assumption
private theorem extendOddly_opposite (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hm : m ≤ k) (f : Edge L n k m → ComplexMatrix2) (b : Edge L n k m) :
    extendOddly f b.opposite = -extendOddly f b := by
  classical
  have hrr : b.opposite.opposite = b := rfl
  rcases xor_oriented hL hn hm b with ⟨hp, hr⟩ | ⟨hp, hr⟩
  · simp only [extendOddly, if_pos hp, if_neg hr, hrr]
  · simp only [extendOddly, if_neg hr, if_pos hp, neg_neg]
private theorem value_mem_traceless (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hm : m ≤ k) {B : Edge L n k m → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k m)
    (b : Edge L n k m) : B b ∈ ComplexMatrix2.traceless := by
  rcases xor_oriented hL hn hm b with ⟨hp, -⟩ | ⟨hr, -⟩
  · exact hB.1 b hp
  · have h1 : B b = -B b.opposite := by
      have := hB.2 b.opposite
      have hrr : b.opposite.opposite = b := rfl
      rwa [hrr] at this
    rw [h1]
    exact ComplexMatrix2.traceless.neg_mem (hB.1 _ hr)
private theorem weight_smul_mem_hermitian {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.inverseFourthPowerWeight_smul_mem <;> assumption
private theorem crossingSmoothing_mem (S : AddSubmonoid ComplexMatrix2)
    (hw : ∀ X ∈ S, PeriodicLattice.inverseFourthPowerWeight L • X ∈ S)
    {B : Edge L n k m → ComplexMatrix2} (hB : ∀ b, B b ∈ S) (c : Edge L n k (m + 1)) :
    crossingSmoothing L n k m B c ∈ S := by
  refine hw _ (finsum_mem_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun x _ => ?_)
  refine S.list_sum_mem ?_
  intro X hX
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hX
  exact hB b
private theorem vertexSmoothing_mem (S : AddSubmonoid ComplexMatrix2)
    (hw : ∀ X ∈ S, PeriodicLattice.inverseFourthPowerWeight L • X ∈ S)
    {l : Vertex L n k m → ComplexMatrix2} (hl : ∀ x, l x ∈ S) (y : Vertex L n k (m + 1)) :
    vertexSmoothing L n k m l y ∈ S :=
  hw _ (finsum_mem_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun x _ => hl x)
end Edges
section Flat
variable {L n k m : ℕ}
private theorem normalizedMean_flat (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    {c : Edge L n k (m + 1)} (hc : c.IsPositivelyOriented) :
    normalizedMean (fun _ : Edge L n k m => (1 : ComplexMatrix2)) c = 1 :=
  (hD L hL n k m hn hm 0 (edgeFormSpace L n k m).zero_mem c hc).2.2.1
private theorem meanRadius_flat (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    {c : Edge L n k (m + 1)} (hc : c.IsPositivelyOriented) :
    meanRadius (fun _ : Edge L n k m => (1 : ComplexMatrix2)) c = 1 :=
  (hD L hL n k m hn hm 0 (edgeFormSpace L n k m).zero_mem c hc).2.1
private theorem meanIterate_flat (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : ∀ m, m ≤ k →
    meanIterate (trivialField L n k 0) m = fun _ => (1 : ComplexMatrix2)
  | 0, _ => rfl
  | m + 1, hm => by
    have hmk : m < k := hm
    have ih := meanIterate_flat hD hL hn m hmk.le
    have e : meanIterate (trivialField L n k 0) (m + 1) = fieldOfPositiveValues
        fun c => (1 : ComplexMatrix2) * normalizedMean (meanIterate (trivialField L n k 0) m) c.1 := by
      show levelField _ (m + 1) = _
      rw [levelField, dif_pos hmk]
      rfl
    rw [e, ih]
    funext b
    unfold fieldOfPositiveValues
    split_ifs with h1 h2
    · simp [normalizedMean_flat hD hL hn hmk h1]
    · simp [normalizedMean_flat hD hL hn hmk h2]
    · rfl
private theorem meanCovariantStep_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hm : m < k) (V B : Edge L n k m → ComplexMatrix2) (c : Edge L n k (m + 1)) :
    meanCovariantStep V B c.opposite = -meanCovariantStep V B c := by
  have h := show m + 1 ≤ k from hm
  simp only [meanCovariantStep, Pi.add_apply, holLeftDifferential, covDiff,
    extendOddly_opposite hL hn h]
  abel
private theorem covariantSmoothingDeriv_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hm : m < k) (V B : Edge L n k m → ComplexMatrix2) (c : Edge L n k (m + 1)) :
    covariantSmoothingDeriv V B c.opposite = -covariantSmoothingDeriv V B c := by
  have h := show m + 1 ≤ k from hm
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv, Pi.add_apply,
    holLeftDifferential, covDiff, extendOddly_opposite hL hn h]
  abel
private theorem meanCovariantStep_flat (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    {B : Edge L n k m → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k m) :
    meanCovariantStep (fun _ : Edge L n k m => (1 : ComplexMatrix2)) B =
      crossingSmoothing L n k m B := by
  obtain ⟨h1, -, -, -, h5, -⟩ := hS m hm
  obtain ⟨e1, e2, e3⟩ := h5 B hB
  rw [← e3]
  have hpos : ∀ c : Edge L n k (m + 1), c.IsPositivelyOriented →
      meanCovariantStep (fun _ : Edge L n k m => (1 : ComplexMatrix2)) B c =
        covariantSmoothingDeriv (trivialField L n k m) B c := by
    intro c hc
    simp only [meanCovariantStep, covariantSmoothingDeriv, Pi.add_apply, h1]
    have a1 := hP L hL n k m hn hm B hB c hc
    have a2 : complexSmoothingDeriv (trivialField L n k m) B c =
        linearSmoothing L n k m B c := congrFun e1 c
    rw [a1, a2]
    congr 1
    classical
    simp only [covDiff, extendOddly, if_pos hc, normalizedMean_flat hD hL hn hm hc]
  funext c
  rcases xor_oriented hL hn (show m + 1 ≤ k from hm) c with ⟨hp, -⟩ | ⟨hr, -⟩
  · exact hpos c hp
  · have h1 := hpos c.opposite hr
    rw [meanCovariantStep_opposite hL hn hm, covariantSmoothingDeriv_opposite hL hn hm] at h1
    exact neg_injective (by simpa using neg_injective (by simpa using h1))
private theorem crossingSmoothing_mem_complexEdgeForms (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    {B : Edge L n k m → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k m) :
    crossingSmoothing L n k m B ∈ complexEdgeForms L n k (m + 1) := by
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · refine crossingSmoothing_mem ComplexMatrix2.traceless.toAddSubgroup.toAddSubmonoid
      (fun X hX => ?_) (value_mem_traceless hL hn hm.le hB) c
    exact ComplexMatrix2.traceless.smul_mem _ hX
  · rw [← meanCovariantStep_flat hD hP hS hL hn hm hB, meanCovariantStep_opposite hL hn hm]
private theorem meanCovariant_flat (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : ∀ m, m ≤ k →
    ∀ B ∈ complexEdgeForms L n k 0,
      meanCovariant (trivialField L n k 0) m B = crossingSmoothingIter L n k m B ∧
        crossingSmoothingIter L n k m B ∈ complexEdgeForms L n k m
  | 0, _, B, hB => ⟨rfl, hB⟩
  | m + 1, hm, B, hB => by
    have hmk : m < k := hm
    obtain ⟨e, hmem⟩ := meanCovariant_flat hD hP hS hL hn m hmk.le B hB
    have e2 : crossingSmoothingIter L n k (m + 1) B =
        crossingSmoothing L n k m (crossingSmoothingIter L n k m B) := rfl
    rw [e2]
    refine ⟨?_, crossingSmoothing_mem_complexEdgeForms hD hP hS hL hn hmk hmem⟩
    show meanCovariantStep (meanIterate (trivialField L n k 0) m)
      (meanCovariant (trivialField L n k 0) m B) = _
    rw [meanIterate_flat hD hL hn m hmk.le, e]
    exact meanCovariantStep_flat hD hP hS hL hn hmk hmem
end Flat
section Real
variable {L n k m : ℕ}
private theorem pauliCoeff_im {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a Y).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
private theorem ofPauliCoeffs_mem_hermitian {σ : Type} {f : Fin 3 × σ → ℂ}
    (hf : ∀ i, (f i).im = 0) (x : σ) : ofPauliCoeffs f x ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p63155 <;> assumption
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
open Classical in
private theorem edgeOfCoeffs_eq (f : Fin 3 × PositiveEdge L n k m → ℂ) :
    (edgePauliCoordinates L n k m).ofCoeffs f =
      extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0 := rfl
private theorem edgeOfCoeffs_mem_hermitian {f : Fin 3 × PositiveEdge L n k m → ℂ}
    (hf : ∀ i, (f i).im = 0) (b : Edge L n k m) :
    (edgePauliCoordinates L n k m).ofCoeffs f b ∈ ComplexMatrix2.hermitianTraceless := by
  classical
  have h : ∀ c : Edge L n k m,
      (if h : c.IsPositivelyOriented then ofPauliCoeffs f ⟨c, h⟩ else (0 : ComplexMatrix2)) ∈
        ComplexMatrix2.hermitianTraceless := by
    intro c
    split_ifs with h
    · exact ofPauliCoeffs_mem_hermitian hf _
    · exact ComplexMatrix2.hermitianTraceless.zero_mem
  rw [edgeOfCoeffs_eq]
  unfold extendOddly
  split_ifs
  · exact h b
  · exact ComplexMatrix2.hermitianTraceless.neg_mem (h _)
private theorem edgeOfCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hm : m ≤ k) (f : Fin 3 × PositiveEdge L n k m → ℂ) :
    (edgePauliCoordinates L n k m).ofCoeffs f ∈ complexEdgeForms L n k m := by
  classical
  rw [edgeOfCoeffs_eq]
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite hL hn hm _ b⟩
  have hb' : b.IsPositivelyOriented := hb
  show extendOddly _ b ∈ ComplexMatrix2.traceless
  simp only [extendOddly, if_pos hb', dif_pos hb']
  exact ofPauliCoeffs_mem_traceless f _
end Real
section Step
variable {L n k m : ℕ}
private theorem finite_vertex (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Finite (Vertex L n k m) :=
  SeparatedSequences.BaseParameters.site_finite (by have := two_le_side hL; omega) _ _
private theorem finite_index (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Finite (Fin 3 × PositiveEdge L n k m) := by
  have := finite_vertex (n := n) (k := k) (m := m) hL
  have : Finite (Edge L n k m) :=
    Finite.of_injective (fun b : Edge L n k m => (b.source, b.target)) fun b b' h => by
      cases b
      cases b'
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  infer_instance
private theorem edgeFormPathSum_add (B B' : Edge L n k m → ComplexMatrix2)
    (Γ : List (Edge L n k m)) :
    edgeFormPathSum (B + B') Γ = edgeFormPathSum B Γ + edgeFormPathSum B' Γ := by apply _root_.YangMills.SharedProofs.p16344 <;> assumption
private theorem edgeFormPathSum_smul (w : ℂ) (B : Edge L n k m → ComplexMatrix2)
    (Γ : List (Edge L n k m)) : edgeFormPathSum (w • B) Γ = w • edgeFormPathSum B Γ := by apply _root_.YangMills.SharedProofs.p18157 <;> assumption
private theorem crossingSmoothing_add (hL : Conventions.IsAdmissibleBlockingFactor L)
    (B B' : Edge L n k m → ComplexMatrix2) :
    crossingSmoothing L n k m (B + B') =
      crossingSmoothing L n k m B + crossingSmoothing L n k m B' := by
  have := finite_vertex (n := n) (k := k) (m := m) hL
  funext c
  simp only [crossingSmoothing, Pi.add_apply, edgeFormPathSum_add]
  rw [finsum_mem_add_distrib (Set.toFinite _), smul_add]
private theorem crossingSmoothing_smul (hL : Conventions.IsAdmissibleBlockingFactor L) (w : ℂ)
    (B : Edge L n k m → ComplexMatrix2) :
    crossingSmoothing L n k m (w • B) = w • crossingSmoothing L n k m B := by
  have := finite_vertex (n := n) (k := k) (m := m) hL
  funext c
  simp only [crossingSmoothing, Pi.smul_apply, edgeFormPathSum_smul]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), ← Finset.smul_sum, smul_comm]
private def formOfCoeffs (f : Fin 3 × PositiveEdge L n k m → ℂ) : Edge L n k m → ComplexMatrix2 :=
  (edgePauliCoordinates L n k m).ofCoeffs f
private theorem formOfCoeffs_eq (f : Fin 3 × PositiveEdge L n k m → ℂ) (b : Edge L n k m) :
    formOfCoeffs f b = open Classical in
      extendOddly (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0) b :=
  rfl
private theorem formOfCoeffs_add (f g : Fin 3 × PositiveEdge L n k m → ℂ) :
    formOfCoeffs (f + g) = formOfCoeffs f + formOfCoeffs g := by
  classical
  funext b
  have h : ∀ c : Edge L n k m,
      (if h : c.IsPositivelyOriented then ofPauliCoeffs (f + g) ⟨c, h⟩ else 0) =
        (if h : c.IsPositivelyOriented then ofPauliCoeffs f ⟨c, h⟩ else (0 : ComplexMatrix2)) +
          (if h : c.IsPositivelyOriented then ofPauliCoeffs g ⟨c, h⟩ else (0 : ComplexMatrix2)) := by
    intro c
    split_ifs
    · simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
    · simp
  rw [Pi.add_apply, formOfCoeffs_eq, formOfCoeffs_eq, formOfCoeffs_eq]
  simp only [extendOddly, h]
  split_ifs
  · rfl
  · abel
  · simp
private theorem formOfCoeffs_smul (w : ℂ) (f : Fin 3 × PositiveEdge L n k m → ℂ) :
    formOfCoeffs (w • f) = w • formOfCoeffs f := by
  classical
  funext b
  have h : ∀ c : Edge L n k m,
      (if h : c.IsPositivelyOriented then ofPauliCoeffs (w • f) ⟨c, h⟩ else 0) =
        w • (if h : c.IsPositivelyOriented then ofPauliCoeffs f ⟨c, h⟩ else (0 : ComplexMatrix2)) := by
    intro c
    split_ifs
    · simp [ofPauliCoeffs, Finset.smul_sum, smul_smul]
    · simp
  rw [Pi.smul_apply, formOfCoeffs_eq, formOfCoeffs_eq]
  simp only [extendOddly, h]
  split_ifs
  · rfl
  · simp
  · simp
private def coeffStep (L n k m : ℕ) (f : Fin 3 × PositiveEdge L n k m → ℂ) :
    Fin 3 × PositiveEdge L n k (m + 1) → ℂ :=
  fun i => pauliCoeff i.1
    ((((L : ℝ)⁻¹ : ℝ) : ℂ) • crossingSmoothing L n k m (formOfCoeffs f) i.2.1)
private theorem pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (c : ℂ)
    (a : Fin 3) : pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add {X Y : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (h' : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
private theorem coeffStep_add (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    (f g : Fin 3 × PositiveEdge L n k m → ℂ) :
    coeffStep L n k m (f + g) = coeffStep L n k m f + coeffStep L n k m g := by
  funext i
  have hf := value_mem_traceless hL hn (show m + 1 ≤ k from hm)
    (crossingSmoothing_mem_complexEdgeForms hD hP hS hL hn hm (edgeOfCoeffs_mem hL hn hm.le f)) i.2.1
  have hg := value_mem_traceless hL hn (show m + 1 ≤ k from hm)
    (crossingSmoothing_mem_complexEdgeForms hD hP hS hL hn hm (edgeOfCoeffs_mem hL hn hm.le g)) i.2.1
  change crossingSmoothing L n k m (formOfCoeffs f) i.2.1 ∈ ComplexMatrix2.traceless at hf
  change crossingSmoothing L n k m (formOfCoeffs g) i.2.1 ∈ ComplexMatrix2.traceless at hg
  simp only [coeffStep, Pi.add_apply]
  rw [formOfCoeffs_add, crossingSmoothing_add hL, Pi.add_apply,
    pauliCoeff_smul (ComplexMatrix2.traceless.add_mem hf hg), pauliCoeff_add hf hg,
    pauliCoeff_smul hf, pauliCoeff_smul hg]
  ring
private theorem coeffStep_smul (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k) (w : ℂ)
    (f : Fin 3 × PositiveEdge L n k m → ℂ) :
    coeffStep L n k m (w • f) = w • coeffStep L n k m f := by
  funext i
  have hf := value_mem_traceless hL hn (show m + 1 ≤ k from hm)
    (crossingSmoothing_mem_complexEdgeForms hD hP hS hL hn hm (edgeOfCoeffs_mem hL hn hm.le f)) i.2.1
  change crossingSmoothing L n k m (formOfCoeffs f) i.2.1 ∈ ComplexMatrix2.traceless at hf
  simp only [coeffStep, Pi.smul_apply, smul_eq_mul]
  rw [formOfCoeffs_smul, crossingSmoothing_smul hL, Pi.smul_apply,
    pauliCoeff_smul (ComplexMatrix2.traceless.smul_mem w hf), pauliCoeff_smul hf, pauliCoeff_smul hf]
  ring
private theorem meanStepKernel_im_flat (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hm : m < k)
    (i' : Fin 3 × PositiveEdge L n k (m + 1)) (i : Fin 3 × PositiveEdge L n k m) :
    (meanStepKernel L n k (trivialField L n k 0) m i' i).im = 0 := by
  classical
  have := finite_index (n := n) (k := k) (m := m) hL
  have hM : (edgePauliCoordinates L n k m).mapOnCoeffs (edgePauliCoordinates L n k (m + 1))
      (fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate (trivialField L n k 0) m) B) =
      coeffStep L n k m := by
    funext (f : Fin 3 × PositiveEdge L n k m → ℂ) (i' : Fin 3 × PositiveEdge L n k (m + 1))
    have hs := meanCovariantStep_flat hD hP hS hL hn hm (edgeOfCoeffs_mem hL hn hm.le f)
    change meanCovariantStep _ (formOfCoeffs f) = crossingSmoothing L n k m (formOfCoeffs f) at hs
    show pauliCoeff i'.1 ((L : ℝ)⁻¹ • meanCovariantStep
      (meanIterate (trivialField L n k 0) m) (formOfCoeffs f) i'.2.1) = _
    rw [meanIterate_flat hD hL hn m hm.le, hs, ← Complex.coe_smul]
    rfl
  have hG := represents_of_linear (coeffStep_add hD hP hS hL hn hm) (coeffStep_smul hD hP hS hL hn hm)
  have hK : meanStepKernel L n k (trivialField L n k 0) m = kernelOfMap (coeffStep L n k m) := by
    show kernelOfMap _ = _
    rw [hM]
    rfl
  rw [hK, kernelOfMap_eq_of_represents hG]
  refine pauliCoeff_im ?_ _
  have hw : ∀ X ∈ ComplexMatrix2.hermitianTraceless.toAddSubmonoid,
      PeriodicLattice.inverseFourthPowerWeight L • X ∈
        ComplexMatrix2.hermitianTraceless.toAddSubmonoid :=
    fun X hX => weight_smul_mem_hermitian hX
  rw [Complex.coe_smul]
  refine ComplexMatrix2.hermitianTraceless.smul_mem _
    (crossingSmoothing_mem ComplexMatrix2.hermitianTraceless.toAddSubmonoid hw (fun b => ?_) _)
  refine edgeOfCoeffs_mem_hermitian (fun q => ?_) b
  simp only [Pi.single_apply]
  split_ifs <;> simp
end Step
section Matrices
variable {I T : Type}
private theorem of_compKernel {A B C : Type} [Fintype B] (X : KernelMatrix B A)
    (Y : KernelMatrix C B) : Matrix.of (compKernel X Y) = Matrix.of X * Matrix.of Y := by apply _root_.YangMills.DeltaSharedProofs.p17742 <;> assumption
private theorem of_meshTranspose {σ σ' : Type} (a a' : ℝ)
    (X : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose a a' X) = (a' ^ 4 / a ^ 4) • (Matrix.of X).transpose := by
  ext i j
  simp [meshTranspose, PeriodicOperators.wTranspose, meshWeight, Complex.real_smul]
private theorem conjTranspose_eq_transpose_of_real {A B : Type} {X : Matrix A B ℂ}
    (h : ∀ i j, (X i j).im = 0) : X.conjTranspose = X.transpose := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  exact Complex.conj_eq_iff_im.2 (h j i)
private theorem schur_contraction [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    {X : Matrix I I ℂ} (hX : X.PosSemidef) (A : Matrix T I ℂ)
    (hu : IsUnit (Matrix.det (X + A.conjTranspose * A))) :
    (A * (X + A.conjTranspose * A)⁻¹ * A.conjTranspose).PosSemidef ∧
      (1 - A * (X + A.conjTranspose * A)⁻¹ * A.conjTranspose).PosSemidef := by
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ, Ξ = X + A.conjTranspose * A := ⟨_, rfl⟩
  rw [← hΞ] at hu ⊢
  have hpsd : Ξ.PosSemidef := by
    rw [hΞ]
    exact hX.add (Matrix.posSemidef_conjTranspose_mul_self A)
  have hpd : Ξ.PosDef := hpsd.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  refine ⟨hpsd.inv.mul_mul_conjTranspose_same A, ?_⟩
  have hb : (Matrix.fromBlocks Ξ A.conjTranspose A.conjTranspose.conjTranspose 1).PosSemidef := by
    have e : Matrix.fromBlocks Ξ A.conjTranspose A.conjTranspose.conjTranspose (1 : Matrix T T ℂ) =
        Matrix.fromRows (1 : Matrix I I ℂ) (0 : Matrix T I ℂ) * X *
            (Matrix.fromRows (1 : Matrix I I ℂ) (0 : Matrix T I ℂ)).conjTranspose +
          (Matrix.fromCols A (1 : Matrix T T ℂ)).conjTranspose * Matrix.fromCols A 1 := by
      rw [hΞ, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
        Matrix.fromRows_mul_fromCols, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add]
      simp
    rw [e]
    exact (hX.mul_mul_conjTranspose_same _).add (Matrix.posSemidef_conjTranspose_mul_self _)
  have : Invertible Ξ := (Matrix.isUnit_iff_isUnit_det _).2 hu |>.invertible
  have := (Matrix.PosDef.fromBlocks₁₁ A.conjTranspose (1 : Matrix T T ℂ) hpd).1 hb
  simpa using this
end Matrices
section Noise
variable {L n k : ℕ}
private theorem noiseCovariance_posSemidef {a : ℝ} (ha : 0 < a) (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing) (hS : ∀ i < k, TrivialStep L n k i)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : ∀ m, m ≤ k →
    (Matrix.of (noiseCovariance a L n k (trivialField L n k 0) m)).PosSemidef
  | 0, _ => Matrix.PosSemidef.zero
  | m + 1, hm => by
    classical
    have hmk : m < k := hm
    have ih := noiseCovariance_posSemidef ha hD hP hS hL hn m hmk.le
    have f0 := finite_index (n := n) (k := k) (m := m) hL
    have f1 := finite_index (n := n) (k := k) (m := m + 1) hL
    let _ : Fintype (Fin 3 × PositiveEdge L n k m) := Fintype.ofFinite _
    let _ : Fintype (Fin 3 × PositiveEdge L n k (m + 1)) := Fintype.ofFinite _
    obtain ⟨U, hU⟩ : ∃ U, U = trivialField L n k 0 := ⟨_, rfl⟩
    rw [← hU] at ih ⊢
    obtain ⟨S, hSdef⟩ : ∃ S, S = meanStepKernel L n k U m := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G, G = noiseCovariance a L n k U m := ⟨_, rfl⟩
    rw [← hG] at ih
    have hreal : ∀ p q, ((Matrix.of S) p q).im = 0 := by
      intro p q
      rw [hSdef, hU]
      exact meanStepKernel_im_flat hD hP hS hL hn hmk p q
    have hinv : Matrix.of (invRadiusDiag U m) = 1 := by
      ext p q
      simp only [Matrix.of_apply, invRadiusDiag, Matrix.one_apply, hU]
      rw [meanIterate_flat hD hL hn m hmk.le, meanRadius_flat hD hL hn hmk q.2.2]
      simp
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = meshAt L k (m + 1) ^ 4 / meshAt L k m ^ 4 := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by
      rw [hc]
      positivity
    have e : Matrix.of (noiseCovariance a L n k U (m + 1)) =
        a⁻¹ • (1 : Matrix _ _ ℂ) + ((L : ℝ) ^ (-2 : ℤ) * c) •
          (Matrix.of S * Matrix.of G * (Matrix.of S).conjTranspose) := by
      have h0 : Matrix.of (noiseCovariance a L n k U (m + 1)) =
          ((a⁻¹ : ℝ) : ℂ) • Matrix.of (invRadiusDiag U m) +
            (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) • Matrix.of (compKernel (compKernel S G)
              (meshTranspose (meshAt L k m) (meshAt L k (m + 1)) S)) := by
        rw [hSdef, hG, noiseCovariance]
        rfl
      rw [h0, hinv, of_compKernel, of_compKernel, of_meshTranspose,
        ← conjTranspose_eq_transpose_of_real hreal, ← hc, Complex.coe_smul, Complex.coe_smul,
        Matrix.mul_smul, smul_smul]
    rw [e]
    exact (Matrix.PosSemidef.one.smul (inv_nonneg.2 ha.le)).add
      ((ih.mul_mul_conjTranspose_same _).smul (by positivity))
end Noise
section Rescaled
variable {L n k m : ℕ}
private theorem kernel_im_eq_zero {r r' : PauliComponentsOfSymmetricKernel} {T : KernelMatrix r.Index r'.Index}
    {F : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hg : Represents T (r.mapOnCoeffs r' F))
    (hF : ∀ f : r.Index → ℂ, (∀ i, (f i).im = 0) → ∀ i', (r'.coeffs (F (r.ofCoeffs f)) i').im = 0)
    (i' : r'.Index) (i : r.Index) : (T i' i).im = 0 := by
  classical
  rw [kernelMatrix_apply_eq hg]
  refine hF _ (fun q => ?_) i'
  simp only [Pi.single_apply]
  split_ifs <;> simp
private theorem crossingSmoothingIter_mem {B : Edge L n k 0 → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.hermitianTraceless) :
    ∀ m (b : Edge L n k m), crossingSmoothingIter L n k m B b ∈ ComplexMatrix2.hermitianTraceless
  | 0, b => hB b
  | m + 1, b => crossingSmoothing_mem ComplexMatrix2.hermitianTraceless.toAddSubmonoid
      (fun _ h => weight_smul_mem_hermitian h) (crossingSmoothingIter_mem hB m) b
private theorem vertexSmoothingIter_mem {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    ∀ m (x : Vertex L n k m), vertexSmoothingIter L n k m l x ∈ ComplexMatrix2.hermitianTraceless
  | 0, x => hl x
  | m + 1, x => vertexSmoothing_mem ComplexMatrix2.hermitianTraceless.toAddSubmonoid
      (fun _ h => weight_smul_mem_hermitian h) (vertexSmoothingIter_mem hl m) x
private theorem finite_face_index (hL : Conventions.IsAdmissibleBlockingFactor L) :
    Finite (Fin 3 × Face L n k 0) := by
  have := finite_vertex (n := n) (k := k) (m := 0) hL
  have : Finite (Face L n k 0) :=
    Finite.of_injective (fun p : Face L n k 0 => (p.origin, p.firstAxis, p.secondAxis))
      fun p p' e => by
        cases p
        cases p'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        rfl
  infer_instance
private theorem topCovariance_between (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hOne : TrivialRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (vertexCoordinate (Face L n k 0))
      (rescaledOperators L n k (trivialField L n k 0)) scaledVertexCoboundary
      scaledEdgeCoboundary scaledVertexCoboundary (crossingSmoothingIter L n k k)
      (vertexSmoothingIter L n k k))
    (hRR : compKernel (rescaledOperators L n k (trivialField L n k 0)).R
      (rescaledOperators L n k (trivialField L n k 0)).Rt = unitKernel (Fin 3 × Vertex L n k k))
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
    [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
    [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)]
    (hu : IsUnit (Matrix.det (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi))) :
    (topCovariance (trivialField L n k 0)).PosSemidef ∧
      (1 - topCovariance (trivialField L n k 0)).PosSemidef := by
  classical
  have fp := finite_face_index (n := n) (k := k) hL
  let _ : Fintype (Fin 3 × Face L n k 0) := Fintype.ofFinite _
  obtain ⟨p, hp⟩ : ∃ p, p = rescaledOperators L n k (trivialField L n k 0) := ⟨_, rfl⟩
  rw [← hp] at hOne hRR hu
  have hη : p.eta = finestMesh L k := by rw [hp]; rfl
  have htop : p.coarse = meshAt L k k := by rw [hp]; rfl
  have hη0 : p.eta ≠ 0 := by
    rw [hη]
    have : (0 : ℝ) < L := by
      have := two_le_side hL
      positivity
    unfold finestMesh meshAt
    positivity
  have rQ : ∀ i j, (Matrix.of p.Q i j).im = 0 := by
    refine kernel_im_eq_zero hOne.Q_represents fun f hf i' => ?_
    refine pauliCoeff_im ?_ _
    exact ComplexMatrix2.hermitianTraceless.smul_mem _
      (crossingSmoothingIter_mem (edgeOfCoeffs_mem_hermitian hf) k _)
  have rR : ∀ i j, (Matrix.of p.R i j).im = 0 := by
    refine kernel_im_eq_zero hOne.R_represents fun f hf i' => ?_
    exact pauliCoeff_im (vertexSmoothingIter_mem (ofPauliCoeffs_mem_hermitian hf) k _) _
  have rD : ∀ i j, (Matrix.of p.D i j).im = 0 := by
    rw [hOne.D_eq]
    refine kernel_im_eq_zero hOne.vertex_represents fun f hf i' => ?_
    refine pauliCoeff_im ?_ _
    exact ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sub_mem (ofPauliCoeffs_mem_hermitian hf _)
        (ofPauliCoeffs_mem_hermitian hf _))
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × Face L n k 0),
      d₁ = (edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary := ⟨_, rfl⟩
  have rd₁ : ∀ i j, (Matrix.of d₁ i j).im = 0 := by
    rw [hd₁]
    refine kernel_im_eq_zero hOne.edge_represents fun f hf i' => ?_
    refine pauliCoeff_im ?_ _
    have hb := edgeOfCoeffs_mem_hermitian (n := n) (k := k) (m := 0) hf
    exact ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sub_mem (ComplexMatrix2.hermitianTraceless.sub_mem
        (ComplexMatrix2.hermitianTraceless.add_mem (hb _) (hb _)) (hb _)) (hb _))
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = p.coarse ^ 4 / p.eta ^ 4 := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by
    rw [hw]
    positivity
  have one_eta : p.eta ^ 4 / p.eta ^ 4 = 1 := div_self (pow_ne_zero _ hη0)
  have tD : Matrix.of (meshTranspose p.eta p.eta p.D) = (Matrix.of p.D).conjTranspose := by
    rw [of_meshTranspose, one_eta, one_smul, conjTranspose_eq_transpose_of_real rD]
  have td₁ : Matrix.of (meshTranspose p.eta p.eta d₁) = (Matrix.of d₁).conjTranspose := by
    rw [of_meshTranspose, one_eta, one_smul, conjTranspose_eq_transpose_of_real rd₁]
  have tR : Matrix.of p.Rt = w • (Matrix.of p.R).conjTranspose := by
    show Matrix.of (meshTranspose p.eta p.coarse p.R) = _
    rw [of_meshTranspose, ← hw, conjTranspose_eq_transpose_of_real rR]
  have tQ : Matrix.of p.Qt = w • (Matrix.of p.Q).conjTranspose := by
    show Matrix.of (meshTranspose p.eta p.coarse p.Q) = _
    rw [of_meshTranspose, ← hw, conjTranspose_eq_transpose_of_real rQ]
  have hone : ∀ (σ : Type) [Fintype (Fin 3 × σ)] [DecidableEq (Fin 3 × σ)],
      Matrix.of (unitKernel (Fin 3 × σ)) = 1 := by
    intro σ _ _
    ext i j
    simp [unitKernel, Matrix.one_apply]
  have hRRm : Matrix.of p.R * Matrix.of p.Rt = 1 := by
    rw [← of_compKernel, hRR, hone]
  obtain ⟨O, hO⟩ : ∃ O, O = Matrix.of (complementProj p) := ⟨_, rfl⟩
  have hOe : O = 1 - Matrix.of p.Rt * Matrix.of p.R := by
    rw [hO, ← of_compKernel, ← hone (Vertex L n k 0)]
    rfl
  have hOh : O.conjTranspose = O := by
    have hOe' : O = 1 - w • ((Matrix.of p.R).conjTranspose * Matrix.of p.R) := by
      rw [hOe, tR, Matrix.smul_mul]
    rw [hOe', Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp
  have hOO : O * O = O := by
    have e : Matrix.of p.Rt * Matrix.of p.R * (Matrix.of p.Rt * Matrix.of p.R) =
        Matrix.of p.Rt * Matrix.of p.R := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of p.R), hRRm, Matrix.one_mul]
    rw [hOe, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e]
    simp
  have hOpsd : O.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self O
    rwa [hOh, hOO] at this
  have hX : (Matrix.of p.X).PosSemidef := by
    have e : Matrix.of p.X = (Matrix.of d₁).conjTranspose * Matrix.of d₁ +
        Matrix.of p.D * O * (Matrix.of p.D).conjTranspose := by
      have h0 := congrArg Matrix.of hOne.X_eq
      rw [← hOne.D_eq, ← hd₁] at h0
      refine h0.trans ?_
      show Matrix.of (compKernel (meshTranspose p.eta p.eta d₁) d₁) +
        Matrix.of (compKernel (compKernel p.D (complementProj p))
          (meshTranspose p.eta p.eta p.D)) = _
      rw [of_compKernel, of_compKernel, of_compKernel, tD, td₁, ← hO]
    rw [e]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).add (hOpsd.mul_mul_conjTranspose_same _)
  have hXi : Matrix.of p.Xi = Matrix.of p.X +
      (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q).conjTranspose *
        (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q) := by
    have h1 : Matrix.of p.X = Matrix.of p.Xi - Matrix.of (compKernel p.Qt p.Q) := rfl
    have h2 : (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q).conjTranspose *
        (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q) = Matrix.of (compKernel p.Qt p.Q) := by
      rw [of_compKernel, tQ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw0, Complex.coe_smul, Matrix.smul_mul]
    rw [h1, h2, sub_add_cancel]
  have hC : topCovariance (trivialField L n k 0) =
      (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q) * (Matrix.of p.Xi)⁻¹ *
        (((Real.sqrt w : ℝ) : ℂ) • Matrix.of p.Q).conjTranspose := by
    have h3 : topCovariance (trivialField L n k 0) =
        Matrix.of p.Q * (Matrix.of p.Xi)⁻¹ * Matrix.of p.Qt := by
      rw [hp]
      rfl
    rw [h3, tQ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, smul_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw0, Complex.coe_smul]
  rw [hC]
  rw [hXi] at hu ⊢
  exact schur_contraction hX _ hu
end Rescaled
theorem flatNoiseCovariancePositive_holds (hD : NormalizedMeanAtOne)
    (hP : HolDifferentialAtOneEqSmoothing)
    (hSt : RescaledTrivialSteps)
    (hO : TrivialFieldRescaledRelations.Statement)
    (hR : RescaledIterRelations) :
    FlatNoiseCovariancePositive := by
  intro a ha L hL k n hk hn
  obtain ⟨hmem, hS⟩ := hSt L hL k hk n hn
  have hOne := hO L hL k hk n hn
  refine ⟨?_, noiseCovariance_posSemidef ha hD hP hS hL hn k le_rfl, ?_⟩
  · have hM : (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        (fun B => finestMesh L k • meanCovariant (trivialField L n k 0) k B) =
        (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
          (fun B => (finestMesh L k) • crossingSmoothingIter L n k k B) := by
      funext (f : Fin 3 × PositiveEdge L n k 0 → ℂ)
      have := (meanCovariant_flat hD hP hS hL hn k le_rfl _
        (edgeOfCoeffs_mem hL hn (Nat.zero_le k) f)).1
      show (edgePauliCoordinates L n k k).coeffs (finestMesh L k • meanCovariant _ k _) = _
      rw [this]
      rfl
    show kernelOfMap _ = _
    rw [hM]
    exact kernelOfMap_eq_of_represents hOne.Q_represents
  · intro _ _ _ _ _ _ _ _
    exact topCovariance_between hL hn hOne (hR L hL k hk n hn _ hmem).R_comp_Rt
end YangMills.Construction.RunningCouplingSlope.FlatNoisePositivity
end
