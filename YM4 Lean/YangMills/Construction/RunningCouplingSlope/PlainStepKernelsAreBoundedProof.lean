import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsAreBounded
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.StepKernelBound
open Tower
open Matrices
open PeriodicOperators (KernelMatrix applyKernel wOpNorm OpNormSummable wNorm
  NormSummable wUnitBall Represents kernelOfMap)
open Tower.SmoothingContraction (TorusOpNormLE)
open Tower.SmoothingStepsNearFree (MapNormLE distFromOne)
section Norms
variable {σ σ' : Type}
private theorem wNorm_meshWeight_add_le [Finite σ] {a : ℝ} (ha : 0 < a) (f g : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (f + g) ≤
      wNorm (meshWeight a) f + wNorm (meshWeight a) g := by apply _root_.YangMills.SharedProofs.p20251 <;> assumption
private theorem wNorm_meshWeight_smul [Finite σ] {a : ℝ} (ha : 0 < a) (w : ℂ) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) (w • f) = ‖w‖ * wNorm (meshWeight a) f := by apply _root_.YangMills.SharedProofs.p8315 <;> assumption
private theorem wNorm_meshWeight_nonneg (a : ℝ) (f : Fin 3 × σ → ℂ) : 0 ≤ wNorm (meshWeight a) f :=
  Real.sqrt_nonneg _
private theorem eq_zero_of_wNorm_eq_zero [Finite σ] {a : ℝ} (ha : 0 < a) {f : Fin 3 × σ → ℂ}
    (h : wNorm (meshWeight a) f = 0) : f = 0 := by apply _root_.YangMills.SharedProofs.p4646 <;> assumption
private theorem normSummable_of_finite [Finite σ] (w : Fin 3 × σ → ℝ) (f : Fin 3 × σ → ℂ) :
    NormSummable w f := by apply _root_.YangMills.SharedProofs.p57614 <;> assumption
private structure IsComplexLinear (M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ) : Prop where
  add : ∀ f g, M (f + g) = M f + M g
  smul : ∀ (w : ℂ) f, M (w • f) = w • M f
private theorem le_of_wOpNorm_le [Finite σ] [Finite σ'] {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hc : 0 ≤ c) {M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ} (hM : IsComplexLinear M)
    (h : wOpNorm (meshWeight a) (meshWeight a') univ M ≤ ENNReal.ofReal c)
    (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a') (M f) ≤ c * wNorm (meshWeight a) f := by
  by_cases h0 : wNorm (meshWeight a) f = 0
  · have e := eq_zero_of_wNorm_eq_zero ha h0
    have e₀ : M 0 = 0 := by
      have := hM.smul 0 0
      simpa using this
    have e₁ := wNorm_meshWeight_smul ha' (0 : ℂ) (0 : Fin 3 × σ' → ℂ)
    rw [zero_smul, norm_zero, zero_mul] at e₁
    rw [h0, mul_zero, e, e₀, e₁]
  have hpos : 0 < wNorm (meshWeight a) f :=
    lt_of_le_of_ne (wNorm_meshWeight_nonneg a f) (Ne.symm h0)
  obtain ⟨t, ht⟩ : ∃ t, t = wNorm (meshWeight a) f := ⟨_, rfl⟩
  rw [← ht] at hpos ⊢
  have hu : ((t⁻¹ : ℝ) : ℂ) • f ∈ wUnitBall (meshWeight a) univ := by
    refine ⟨mem_univ _, normSummable_of_finite _ _, ?_⟩
    rw [wNorm_meshWeight_smul ha, ← ht, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
      inv_mul_cancel₀ hpos.ne']
  have h₁ : ENNReal.ofReal (wNorm (meshWeight a') (M (((t⁻¹ : ℝ) : ℂ) • f))) ≤
      ENNReal.ofReal c :=
    le_trans (le_iSup₂ (f := fun g (_ : g ∈ wUnitBall (meshWeight a) univ) =>
      ENNReal.ofReal (wNorm (meshWeight a') (M g))) _ hu) h
  have h₂ := (ENNReal.ofReal_le_ofReal_iff hc).1 h₁
  rw [hM.smul, wNorm_meshWeight_smul ha', Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le)] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₂ hpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm t c] at h₃
end Norms
private structure ReadsFaithfully (r : PauliComponentsOfSymmetricKernel) : Prop where
  fin : Finite r.Place
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  left : ∀ c, r.coeffs (r.ofCoeffs c) = c
  right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  smul : ∀ (w : ℂ) c, r.ofCoeffs (w • c) = w • r.ofCoeffs c
private theorem applyKernel_basisImages {r r' : PauliComponentsOfSymmetricKernel} [Finite r.Place]
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : IsComplexLinear (r.mapOnCoeffs r' m)) (f : r.Index → ℂ) :
    applyKernel (r.kernelOfBasisImages r' m) f = r.mapOnCoeffs r' m f := by
  classical
  cases nonempty_fintype r.Place
  have hzero : r.mapOnCoeffs r' m 0 = 0 := by
    have := hm.smul 0 0
    simpa using this
  have hsum : ∀ s : Finset r.Index, r.mapOnCoeffs r' m (∑ ι ∈ s, f ι • Pi.single ι (1 : ℂ)) =
      ∑ ι ∈ s, f ι • r.mapOnCoeffs r' m (Pi.single ι 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert ι s hι ih =>
      rw [Finset.sum_insert hι, Finset.sum_insert hι, hm.add, hm.smul, ih]
  have hf : f = ∑ ι, f ι • Pi.single ι (1 : ℂ) := by
    funext ι
    simp [Finset.sum_apply, Pi.single_apply]
  funext ι'
  conv_rhs => rw [hf, hsum]
  unfold applyKernel PauliComponentsOfSymmetricKernel.kernelOfBasisImages
  rw [tsum_fintype, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem isComplexLinear_of {r r' : PauliComponentsOfSymmetricKernel} (hr : ReadsFaithfully r)
    (P : (r'.space.index → ComplexMatrix2) → Prop)
    (cadd : ∀ X Y, P X → P Y → r'.coeffs (X + Y) = r'.coeffs X + r'.coeffs Y)
    (csmul : ∀ (w : ℂ) X, P X → r'.coeffs (w • X) = w • r'.coeffs X)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hP : ∀ X ∈ r.space.complexSubmodule, P (m X))
    (madd : ∀ X ∈ r.space.complexSubmodule, ∀ Y ∈ r.space.complexSubmodule, m (X + Y) = m X + m Y)
    (msmul : ∀ (w : ℂ), ∀ X ∈ r.space.complexSubmodule, m (w • X) = w • m X) :
    IsComplexLinear (r.mapOnCoeffs r' m) where
  add f g := by
    show r'.coeffs (m (r.ofCoeffs (f + g))) = r'.coeffs (m (r.ofCoeffs f)) +
      r'.coeffs (m (r.ofCoeffs g))
    rw [hr.add, madd _ (hr.mem f) _ (hr.mem g), cadd _ _ (hP _ (hr.mem f)) (hP _ (hr.mem g))]
  smul w f := by
    show r'.coeffs (m (r.ofCoeffs (w • f))) = w • r'.coeffs (m (r.ofCoeffs f))
    rw [hr.smul, msmul w _ (hr.mem f), csmul w _ (hP _ (hr.mem f))]
section Coefficients
private theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (w : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (w • X) = w * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end Coefficients
private theorem readsFaithfully_of {r : PauliComponentsOfSymmetricKernel} (fin : Finite r.Place)
    (mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule) (left : ∀ c, r.coeffs (r.ofCoeffs c) = c)
    (right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f)
    (cadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      r.coeffs (f + g) = r.coeffs f + r.coeffs g)
    (csmul : ∀ (w : ℂ), ∀ f ∈ r.space.complexSubmodule, r.coeffs (w • f) = w • r.coeffs f) :
    ReadsFaithfully r where
  fin := fin
  mem := mem
  left := left
  right := right
  add c c' := by
    have e := cadd _ (mem c) _ (mem c')
    rw [left, left] at e
    rw [← e, right _ (Submodule.add_mem _ (mem c) (mem c'))]
  smul w c := by
    have e := csmul w _ (mem c)
    rw [left] at e
    rw [← e, right _ (Submodule.smul_mem _ w (mem c))]
section Forms
variable {L n k j : ℕ}
private theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
private theorem extendOddly_opposite (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.SharedProofs.p17859 <;> assumption
private def TracelessOnPositive (X : Edge L n k j → ComplexMatrix2) : Prop :=
  ∀ b : Edge L n k j, b.IsPositivelyOriented → X b ∈ ComplexMatrix2.traceless
private theorem edge_coeffs_add {X Y : Edge L n k j → ComplexMatrix2} (hX : TracelessOnPositive X)
    (hY : TracelessOnPositive Y) :
    (edgePauliCoordinates L n k j).coeffs (X + Y) =
      (edgePauliCoordinates L n k j).coeffs X + (edgePauliCoordinates L n k j).coeffs Y := by apply _root_.YangMills.DeltaSharedProofs.p501675 <;> assumption
private theorem edge_coeffs_smul (w : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : TracelessOnPositive X) :
    (edgePauliCoordinates L n k j).coeffs (w • X) = w • (edgePauliCoordinates L n k j).coeffs X := by apply _root_.YangMills.DeltaSharedProofs.p501619 <;> assumption
private theorem tracelessOnPositive_of_mem {X : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) : TracelessOnPositive X := hX.1
private def positiveValuesOfCoeffs (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
private theorem edge_ofCoeffs_of_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
private theorem edgePauliCoordinates_faithful (hfin : Finite (Edge L n k j))
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    ReadsFaithfully (edgePauliCoordinates L n k j) := by
  have hmem : ∀ c, (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := fun c =>
    ⟨fun b hb => by
      rw [edge_ofCoeffs_of_pos c hb]
      exact ofPauliCoeffs_mem_traceless c _,
     fun b => extendOddly_opposite (positiveValuesOfCoeffs c) (hx b)⟩
  refine readsFaithfully_of (r := edgePauliCoordinates L n k j) ?_ hmem ?_ ?_ ?_ ?_
  · exact (inferInstanceAs (Finite {b : Edge L n k j // b.IsPositivelyOriented}))
  · intro c
    funext ι
    have e : (edgePauliCoordinates L n k j).ofCoeffs c ι.2.1 = ofPauliCoeffs c ι.2 :=
      edge_ofCoeffs_of_pos c ι.2.2
    show pauliCoeff ι.1 ((edgePauliCoordinates L n k j).ofCoeffs c ι.2.1) = c ι
    rw [e]
    exact pauliCoeff_combination (fun a => c (a, ι.2)) ι.1
  · intro f hf
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs f) b = f b := fun b hb =>
      (edge_ofCoeffs_of_pos _ hb).trans (pauliCombination_pauliCoeff (hf.1 b hb))
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hrb : b.opposite.IsPositivelyOriented := by
        rcases hx b with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hb
        · exact h
      have e₁ := (hmem ((edgePauliCoordinates L n k j).coeffs f)).2 b.opposite
      have e₂ : (b.opposite).opposite = b := rfl
      rw [e₂, hpos _ hrb, hf.2 b, neg_neg] at e₁
      exact e₁
  · exact fun _ hf _ hg => edge_coeffs_add hf.1 hg.1
  · exact fun w _ hf => edge_coeffs_smul w hf.1
private theorem value_mem_traceless_of_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) (b : Edge L n k j) :
    X b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.SharedProofs.p16313 <;> assumption
private theorem covDiff_add (W : Edge L n k j → ComplexMatrix2) (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff W (l + l') = covDiff W l + covDiff W l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
private theorem covDiff_smul (W : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (w : ℂ) : covDiff W (w • l) = w • covDiff W l := by apply _root_.YangMills.SharedProofs.p24956 <;> assumption
private theorem edgeFormPathSum_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless)
    (Γ : List (Edge L n k j)) : edgeFormPathSum B Γ ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.SharedProofs.p3039 <;> assumption
variable [Finite (Vertex L n k j)]
private theorem crossingSmoothing_add (B B' : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (B + B') =
      crossingSmoothing L n k j B + crossingSmoothing L n k j B' := by apply _root_.YangMills.SharedProofs.p41844 <;> assumption
private theorem crossingSmoothing_smul (w : ℂ) (B : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (w • B) = w • crossingSmoothing L n k j B := by apply _root_.YangMills.SharedProofs.p16432 <;> assumption
private theorem crossingSmoothing_traceless {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) :
    TracelessOnPositive (crossingSmoothing L n k j B) := by apply _root_.YangMills.DeltaSharedProofs.p502043 <;> assumption
end Forms
private structure Hypotheses : Prop where
  plainSteps : MeanStepNearFree.Claim
  steps : Tower.SmoothingStepsNearFree.Claim
  contractions : Tower.SmoothingContraction.Claim
  linear : Tower.StepMapsComplexLinear.Claim
  near : NormalizedMeanNearOne
  differential : HolDifferentialLinear
  averaging : Tower.SmoothingNearIdentity
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteBonds : Tower.BondSetFields.ProductStructureHolds
section Tower
variable {L n k : ℕ}
private theorem edge_orientation_xor (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
private theorem finite_edges (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.finiteBonds L hL k j hj).1 n hn).2.1
private theorem finite_vertices (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Vertex L n k j) :=
  have := finite_edges G hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0) fun _ _ h =>
    congrArg PeriodicLattice.Bond.source h
private theorem edgePauliCoordinates_faithful_at (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {j : ℕ} (hj : j ≤ k) : ReadsFaithfully (edgePauliCoordinates L n k j) :=
  edgePauliCoordinates_faithful (finite_edges G hL hn hj) (edge_orientation_xor G hL hn hk hj)
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private structure OneStepInputs (L n k j : ℕ) (C : ℝ) (V : Edge L n k j → ComplexMatrix2) : Prop where
  small : V ∈ smallComplexFields L n k j
  group : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  trace : ∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
    holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless
  linear : ∀ (w : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
    holLeftDifferential normalizedMean V (w • B + B') =
      w • holLeftDifferential normalizedMean V B +
        holLeftDifferential normalizedMean V B'
  near : MapNormLE (meshAt L k j) (meshAt L k (j + 1))
    (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1))
    (fun B => (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k j B))
    (C * distFromOne V)
  nearSite : MapNormLE (meshAt L k j) (meshAt L k (j + 1))
    (vertexCoordinate (Vertex L n k j)) (vertexCoordinate (Vertex L n k (j + 1)))
    (fun l => adjointCubeAverage V l - vertexSmoothing L n k j l)
    (C * distFromOne V)
section Step
variable {j : ℕ} {C : ℝ} {V : Edge L n k j → ComplexMatrix2}
private theorem meanCovariantStep_mem (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k)
    (hj : j < k) (h : OneStepInputs L n k j C V) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V B ∈ complexEdgeForms L n k (j + 1) := by
  obtain ⟨h₁, _, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have hdrift := (h₁ B hB).2
  have hdiff : holLeftDifferential normalizedMean V B ∈ complexEdgeForms L n k (j + 1) :=
    ⟨fun c hc => h.trace B c hc,
     fun c => extendOddly_opposite _ (edge_orientation_xor G hL hn hk (show j + 1 ≤ k from hj) c)⟩
  refine Submodule.add_mem _ hdiff ⟨fun c hc => ?_, fun c => ?_⟩
  · have e : covDiff (normalizedMean V) (contourLogDrift V B) c =
        ComplexMatrix2.conjugateBy (normalizedMean V c) (contourLogDrift V B c.target) -
          contourLogDrift V B c.source := extendOddly_of_pos _ hc
    rw [e]
    exact ComplexMatrix2.traceless.sub_mem
      ((G.conjugation.2.2 _ (G.conjugation.1 _ (h.group c hc))).2.2.2.1 (hdrift _)) (hdrift _)
  · exact extendOddly_opposite _ (edge_orientation_xor G hL hn hk (show j + 1 ≤ k from hj) c)
private theorem meanCovariantStep_add (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k)
    (h : OneStepInputs L n k j C V) {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (B + B') = meanCovariantStep V B + meanCovariantStep V B' := by
  obtain ⟨_, h₂, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B' hB' 1).2
  have e₁ := h.linear 1 B B'
  rw [one_smul, one_smul] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_add]
  abel
private theorem meanCovariantStep_smul (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k)
    (h : OneStepInputs L n k j C V) (w : ℂ) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (w • B) = w • meanCovariantStep V B := by
  obtain ⟨_, h₂, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B hB (w - 1)).2
  have e₁ := h.linear (w - 1) B B
  have e : (w - 1) • B + B = w • B := by
    rw [sub_smul, one_smul, sub_add_cancel]
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (w - 1) • x + x = w • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rw [e, e'] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_smul, smul_add]
private abbrev freeEdgeStep (L n k j : ℕ) (B : Edge L n k j → ComplexMatrix2) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • crossingSmoothing L n k j B
private abbrev edgeStepDeviation (V B : Edge L n k j → ComplexMatrix2) :
    Edge L n k (j + 1) → ComplexMatrix2 :=
  (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k j B)
private theorem real_smul_eq_complex_smul_fun {ι : Type} (t : ℝ) (Y : ι → ComplexMatrix2) :
    t • Y = (t : ℂ) • Y := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
private theorem freeEdgeStep_traceless (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    TracelessOnPositive (freeEdgeStep L n k j B) := fun c hc => by
  have := finite_vertices G hL hn hj.le
  unfold freeEdgeStep
  rw [real_smul_eq_complex_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _
    (crossingSmoothing_traceless
      (value_mem_traceless_of_mem (edge_orientation_xor G hL hn hk hj.le) hB) c hc)
private theorem edgeStepDeviation_traceless (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) (hj : j < k) (h : OneStepInputs L n k j C V) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) : TracelessOnPositive (edgeStepDeviation V B) := fun c hc => by
  have := finite_vertices G hL hn hj.le
  unfold edgeStepDeviation
  rw [real_smul_eq_complex_smul_fun]
  exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
    ((meanCovariantStep_mem G hL hn hk hj h hB).1 c hc)
    (crossingSmoothing_traceless
      (value_mem_traceless_of_mem (edge_orientation_xor G hL hn hk hj.le) hB) c hc))
private theorem freeEdgeStep_add [Finite (Vertex L n k j)] (X Y : Edge L n k j → ComplexMatrix2) :
    freeEdgeStep L n k j (X + Y) = freeEdgeStep L n k j X + freeEdgeStep L n k j Y := by
  unfold freeEdgeStep
  rw [crossingSmoothing_add, smul_add]
private theorem freeEdgeStep_smul [Finite (Vertex L n k j)] (w : ℂ) (X : Edge L n k j → ComplexMatrix2) :
    freeEdgeStep L n k j (w • X) = w • freeEdgeStep L n k j X := by
  unfold freeEdgeStep
  rw [crossingSmoothing_smul, real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
private theorem edgeStepDeviation_add (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : OneStepInputs L n k j C V) {X Y : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) (hY : Y ∈ complexEdgeForms L n k j) :
    edgeStepDeviation V (X + Y) = edgeStepDeviation V X + edgeStepDeviation V Y := by
  have := finite_vertices G hL hn hj.le
  unfold edgeStepDeviation
  rw [meanCovariantStep_add G hL hn hj h hX hY, crossingSmoothing_add, ← smul_add, add_sub_add_comm]
private theorem edgeStepDeviation_smul (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : OneStepInputs L n k j C V) (w : ℂ)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) :
    edgeStepDeviation V (w • X) = w • edgeStepDeviation V X := by
  have := finite_vertices G hL hn hj.le
  unfold edgeStepDeviation
  rw [meanCovariantStep_smul G hL hn hj h w hX, crossingSmoothing_smul, ← smul_sub,
    real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
private theorem freeEdgeStep_linear (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) :
    IsComplexLinear ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      (freeEdgeStep L n k j)) := by
  have := finite_vertices G hL hn hj.le
  refine isComplexLinear_of (edgePauliCoordinates_faithful_at G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun w _ hX => edge_coeffs_smul w hX)
    (fun X hX => freeEdgeStep_traceless G hL hn hk hj hX) ?_ ?_
  · intro X _ Y _
    exact freeEdgeStep_add X Y
  · intro w X _
    exact freeEdgeStep_smul w X
private theorem edgeStepDeviation_linear (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (h : OneStepInputs L n k j C V) :
    IsComplexLinear ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      (edgeStepDeviation V)) := by
  have := finite_vertices G hL hn hj.le
  refine isComplexLinear_of (edgePauliCoordinates_faithful_at G hL hn hk hj.le)
    (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun w _ hX => edge_coeffs_smul w hX)
    (fun X hX => edgeStepDeviation_traceless G hL hn hk hj h hX) ?_ ?_
  · intro X hX Y hY
    exact edgeStepDeviation_add G hL hn hj h hX hY
  · intro w X hX
    exact edgeStepDeviation_smul G hL hn hj h w hX
private theorem l1NormVec_zero : TorusMetric.l1NormVec (0 : Fin 4 → ℝ) = 0 := by
  simp [TorusMetric.l1NormVec]
private theorem distFromOne_nonneg (V : Edge L n k j → ComplexMatrix2) : 0 ≤ distFromOne V :=
  ENNReal.toReal_nonneg
private theorem edgeStepDeviation_le (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (hC : 0 ≤ C) (h : OneStepInputs L n k j C V)
    (g : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (edgeStepDeviation V) g) ≤
      (C * distFromOne V) * wNorm (meshWeight (meshAt L k j)) g := by
  have := (edgePauliCoordinates_faithful_at G hL hn hk hj.le).fin
  have := (edgePauliCoordinates_faithful_at G hL hn hk (show j + 1 ≤ k from hj)).fin
  exact le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1))
    (mul_nonneg hC (distFromOne_nonneg _)) (edgeStepDeviation_linear G hL hn hk hj h) h.near.2 g
private theorem freeEdgeStep_le (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (g : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j) g) ≤
      wNorm (meshWeight (meshAt L k j)) g := by
  have := (edgePauliCoordinates_faithful_at G hL hn hk hj.le).fin
  have := (edgePauliCoordinates_faithful_at G hL hn hk (show j + 1 ≤ k from hj)).fin
  have hlin := freeEdgeStep_linear G hL hn hk hj
  have hc := (((G.contractions L hL k hk).2.1 n hn).2.1 j hj).1.2
  have e : applyKernel ((edgePauliCoordinates L n k j).kernelOfBasisImages (edgePauliCoordinates L n k (j + 1))
      (freeEdgeStep L n k j)) = (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      (freeEdgeStep L n k j) := funext (applyKernel_basisImages hlin)
  have hc' : wOpNorm (meshWeight (meshAt L k j))
      (meshWeight (meshAt L k (j + 1)))
      univ ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j)) ≤
      ENNReal.ofReal 1 := by
    rw [← e]
    refine hc.trans (le_of_eq ?_)
    rw [l1NormVec_zero]
    simp
  have := le_of_wOpNorm_le (meshAt_pos hL k j) (meshAt_pos hL k (j + 1)) zero_le_one hlin hc' g
  simpa using this
private theorem scaledStep_coeffs_split (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (h : OneStepInputs L n k j C V)
    {X : Edge L n k j → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k (j + 1)).coeffs ((((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V X) =
      (edgePauliCoordinates L n k (j + 1)).coeffs (edgeStepDeviation V X) +
        (edgePauliCoordinates L n k (j + 1)).coeffs (freeEdgeStep L n k j X) := by
  have e : (((L : ℝ)⁻¹ : ℝ) : ℂ) • meanCovariantStep V X =
      edgeStepDeviation V X + freeEdgeStep L n k j X := by
    unfold edgeStepDeviation freeEdgeStep
    rw [← smul_add, sub_add_cancel, real_smul_eq_complex_smul_fun]
  exact (congrArg (edgePauliCoordinates L n k (j + 1)).coeffs e).trans (edge_coeffs_add
    (edgeStepDeviation_traceless G hL hn hk hj h hX) (freeEdgeStep_traceless G hL hn hk hj hX))
end Step
private theorem scaled_isComplexLinear {s e : ℕ} (hs : ReadsFaithfully (edgePauliCoordinates L n k s)) (a : ℝ)
    {M : (Edge L n k s → ComplexMatrix2) → Edge L n k e → ComplexMatrix2}
    (hm : ∀ X ∈ complexEdgeForms L n k s, M X ∈ complexEdgeForms L n k e)
    (ha : ∀ X ∈ complexEdgeForms L n k s, ∀ Y ∈ complexEdgeForms L n k s, M (X + Y) = M X + M Y)
    (hz : ∀ (w : ℂ), ∀ X ∈ complexEdgeForms L n k s, M (w • X) = w • M X) :
    IsComplexLinear ((edgePauliCoordinates L n k s).mapOnCoeffs (edgePauliCoordinates L n k e) fun B => a • M B) := by
  have hz' : ∀ (w : ℂ), ∀ X ∈ complexEdgeForms L n k s, a • M (w • X) = w • a • M X := by
    intro w X hX
    rw [hz w X hX, real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
  refine isComplexLinear_of hs (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun w _ hX => edge_coeffs_smul w hX) ?_ ?_ ?_
  · intro X hX
    have : (a : ℂ) • M X ∈ complexEdgeForms L n k e := Submodule.smul_mem _ _ (hm X hX)
    rw [real_smul_eq_complex_smul_fun]
    exact tracelessOnPositive_of_mem this
  · intro X hX Y hY
    exact (congrArg (fun x => a • x) (ha X hX Y hY)).trans (smul_add a _ _)
  · intro w X hX
    exact hz' w X hX
private theorem meshAt_succ (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) :
    meshAt L k (m + 1) = L * meshAt L k m := by apply _root_.YangMills.SharedProofs.p23229 <;> assumption
private theorem smoothingStepConstant_nonneg (L : ℕ) : 0 ≤ smoothingStepConstant L := by
  unfold smoothingStepConstant
  positivity
private theorem distFromOne_le {j : ℕ} {V : Edge L n k j → ComplexMatrix2} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) ≤ x) : distFromOne V ≤ x :=
  ENNReal.toReal_le_of_le_ofReal hx (iSup_le fun b => ENNReal.ofReal_le_ofReal (h b))
private theorem scaledStep_kernel_le (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k)
    {j : ℕ} (hj : j < k) {C : ℝ} (hC : 0 ≤ C) {V : Edge L n k j → ComplexMatrix2}
    (h : OneStepInputs L n k j C V) (g : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
      (applyKernel ((edgePauliCoordinates L n k j).kernel (edgePauliCoordinates L n k (j + 1))
        fun B => (L : ℝ)⁻¹ • meanCovariantStep V B) g) ≤
      (1 + C * distFromOne V) * wNorm (meshWeight (meshAt L k j)) g := by
  have hr := edgePauliCoordinates_faithful_at G hL hn hk hj.le
  have hr' := edgePauliCoordinates_faithful_at G hL hn hk (show j + 1 ≤ k from hj)
  have := hr.fin
  have := hr'.fin
  have hlin : IsComplexLinear ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      fun B => (L : ℝ)⁻¹ • meanCovariantStep V B) :=
    scaled_isComplexLinear hr _ (fun X hX => meanCovariantStep_mem G hL hn hk hj h hX)
      (fun X hX Y hY => meanCovariantStep_add G hL hn hj h hX hY)
      (fun w X hX => meanCovariantStep_smul G hL hn hj h w hX)
  have hT : Represents ((edgePauliCoordinates L n k j).kernelOfBasisImages (edgePauliCoordinates L n k (j + 1))
      fun B => (L : ℝ)⁻¹ • meanCovariantStep V B)
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
        fun B => (L : ℝ)⁻¹ • meanCovariantStep V B) := fun f =>
    ⟨fun ι' => Summable.of_finite, applyKernel_basisImages hlin f⟩
  have hK : Represents ((edgePauliCoordinates L n k j).kernel (edgePauliCoordinates L n k (j + 1))
      fun B => (L : ℝ)⁻¹ • meanCovariantStep V B)
      ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
        fun B => (L : ℝ)⁻¹ • meanCovariantStep V B) :=
    Classical.epsilon_spec (⟨_, hT⟩ : ∃ T, Represents T _)
  rw [(hK g).2]
  have hX : (edgePauliCoordinates L n k j).ofCoeffs g ∈ complexEdgeForms L n k j := hr.mem g
  have e : (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
      (fun B => (L : ℝ)⁻¹ • meanCovariantStep V B) g =
      (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (edgeStepDeviation V) g +
        (edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j) g := by
    have e₁ := scaledStep_coeffs_split G hL hn hk hj h hX
    rw [← real_smul_eq_complex_smul_fun] at e₁
    exact e₁
  rw [e]
  have h₁ := wNorm_meshWeight_add_le (meshAt_pos hL k (j + 1))
    ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (edgeStepDeviation V) g)
    ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1)) (freeEdgeStep L n k j) g)
  have h₂ := edgeStepDeviation_le G hL hn hk hj hC h g
  have h₃ := freeEdgeStep_le G hL hn hk hj g
  linarith
private theorem l2_opNorm_le_of_weighted {I I' : Type} [Fintype I] [Fintype I'] [DecidableEq I]
    [DecidableEq I'] {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a') (hc : 0 ≤ c) (T : I' → I → ℂ)
    (hb : ∀ f, wNorm (fun _ : I' => a' ^ 4) (applyKernel T f) ≤
      c * wNorm (fun _ : I => a ^ 4) f) :
    ‖(Matrix.of T : Matrix I' I ℂ)‖ ≤ c * (a ^ 2 / a' ^ 2) := by
  have nrm : ∀ {J : Type} [Fintype J] {b : ℝ}, 0 < b → ∀ f : J → ℂ,
      wNorm (fun _ : J => b ^ 4) f = b ^ 2 * ‖(WithLp.toLp 2 f : EuclideanSpace ℂ J)‖ := by
    intro J _ b hb f
    unfold wNorm
    rw [tsum_fintype, EuclideanSpace.norm_eq]
    have e : ∑ i, b ^ 4 * ‖f i‖ ^ 2 =
        (b ^ 2) ^ 2 * ∑ i, ‖(WithLp.toLp 2 f : EuclideanSpace ℂ J) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        show _ = (b ^ 2) ^ 2 * ‖f i‖ ^ 2
        ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h := hb (WithLp.ofLp x)
  rw [nrm ha', nrm ha] at h
  have e : (WithLp.toLp 2 (applyKernel T (WithLp.ofLp x)) : EuclideanSpace ℂ I') =
      (Matrix.toEuclideanLin (Matrix.of T)) x := by
    rw [Matrix.toEuclideanLin_apply]
    congr 1
    funext i
    simp only [applyKernel, tsum_fintype, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have h' : a' ^ 2 * ‖(Matrix.toEuclideanLin (Matrix.of T)) x‖ ≤ c * (a ^ 2 * ‖x‖) := by
    rw [← e]
    exact h
  show ‖(Matrix.toEuclideanLin (Matrix.of T)) x‖ ≤ _
  have hp : 0 < a' ^ 2 := by positivity
  rw [show c * (a ^ 2 / a' ^ 2) * ‖x‖ = c * (a ^ 2 * ‖x‖) / a' ^ 2 by ring, le_div_iff₀ hp]
  linarith
end Tower
private theorem stepKernelNormBound_of_hypotheses (G : Hypotheses) : StepKernelNormBound := by
  intro L hL
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hS⟩ := G.plainSteps L hL
  obtain ⟨ρ₂, hρ₂, hN⟩ := G.near L hL
  obtain ⟨ρ₃, hρ₃, hD⟩ := G.differential L hL
  have hρL := (G.averaging.1 L hL).2.2.pos
  obtain ⟨r, hr, hr₁, hr₂, hr₃, hr₄⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ρ₁ ∧ r ≤ ρ₂ ∧ r ≤ ρ₃ ∧
      r ≤ polydiscRadius L / 2 :=
    ⟨min (min ρ₁ ρ₂) (min ρ₃ (polydiscRadius L / 2)),
      lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hK₀ := smoothingStepConstant_nonneg L
  set K := C₁ + smoothingStepConstant L with hK
  have hKnn : 0 ≤ K := by positivity
  have hK1 : 0 < K + 1 := by linarith
  obtain ⟨ρ, hρ, hρr, hρK⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ K * ρ ≤ 1 := by
    refine ⟨min (r / 2) (1 / (K + 1)), lt_min (by positivity) (by positivity),
      (min_le_left _ _).trans_lt (by linarith), ?_⟩
    have h₁ : min (r / 2) (1 / (K + 1)) ≤ 1 / (K + 1) := min_le_right _ _
    have h₂ := mul_le_mul_of_nonneg_left h₁ hKnn
    refine h₂.trans ?_
    rw [mul_one_div, div_le_one hK1]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  intro n k hn hk U hU j hj _ _ _ _
  obtain ⟨hV, hbd⟩ := hU j hj
  have hb : ∀ b, ComplexMatrix2.operatorNorm (meanIterate U j b - 1) < r :=
    fun b => (hbd b).trans_lt hρr
  have hd₀ := distFromOne_nonneg (meanIterate U j)
  have hD' := hD n k j hn hj _ hV fun b => (hb b).trans_le hr₃
  have hA := (G.steps L hL n k j hn hj _ hV fun b => (hb b).trans_le hr₄).2
  have hB := hS n k j hn hj _ hV fun b => (hb b).trans_le hr₁
  have hfacts : OneStepInputs L n k j K (meanIterate U j) := by
    refine ⟨⟨hV, fun b => ?_⟩, fun c hc => ?_, hD'.1, hD'.2, ⟨hB.1, hB.2.trans ?_⟩,
      ⟨hA.1, hA.2.trans ?_⟩⟩
    · linarith [hb b]
    · exact (hN n k j hn hj _ hV (fun b => (hb b).trans_le hr₂) c hc).2.2.2.1
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hd₀)
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hd₀)
  have hdist := distFromOne_le hρ.le hbd
  have hone : 1 + K * distFromOne (meanIterate U j) ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hdist hKnn
    linarith
  have hm := l2_opNorm_le_of_weighted (meshAt_pos hL k j) (meshAt_pos hL k (j + 1)) (zero_le_two)
    (meanStepKernel L n k U j) fun f => (scaledStep_kernel_le G hL hn hk hj hKnn hfacts f).trans
      (mul_le_mul_of_nonneg_right hone (wNorm_meshWeight_nonneg _ _))
  refine hm.trans (le_of_eq ?_)
  have hℓ := meshAt_pos hL k j
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    have : 0 < L := by omega
    exact_mod_cast this.ne'
  rw [meshAt_succ hL]
  field_simp
theorem stepKernelNormBound_holds (h₁ : MeanStepNearFree.Claim)
    (h₂ : Tower.SmoothingStepsNearFree.Claim)
    (h₃ : Tower.SmoothingContraction.Claim)
    (h₄ : Tower.StepMapsComplexLinear.Claim)
    (h₅ : NormalizedMeanNearOne) (h₆ : HolDifferentialLinear)
    (h₇ : Tower.SmoothingNearIdentity)
    (h₈ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₉ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₁₀ : Tower.BondSetFields.ProductStructureHolds) : StepKernelNormBound :=
  stepKernelNormBound_of_hypotheses ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
end YangMills.Construction.RunningCouplingSlope.StepKernelBound
end
