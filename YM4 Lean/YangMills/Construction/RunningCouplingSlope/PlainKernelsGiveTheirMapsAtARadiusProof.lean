import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMapsAtARadius
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanKernelsRepresent
open YangMills.Construction.Tower
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel wOpNorm OpNormSummable wNorm
  NormSummable wUnitBall Represents kernelOfMap)
section Norms
variable {σ σ' : Type}
private structure IsCLinear (M : (Fin 3 × σ → ℂ) → Fin 3 × σ' → ℂ) : Prop where
  add : ∀ f g, M (f + g) = M f + M g
  smul : ∀ (z : ℂ) f, M (z • f) = z • M f
end Norms
private structure IsFaithful (r : PauliComponentsOfSymmetricKernel) : Prop where
  fin : Finite r.Place
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  left : ∀ c, r.coeffs (r.ofCoeffs c) = c
  right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
private theorem applyKernel_basisImages {r r' : PauliComponentsOfSymmetricKernel} [Finite r.Place]
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : IsCLinear (r.mapOnCoeffs r' m)) (f : r.Index → ℂ) :
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
private theorem isCLinear_mapOnCoeffs {r r' : PauliComponentsOfSymmetricKernel} (hr : IsFaithful r)
    (P : (r'.space.index → ComplexMatrix2) → Prop)
    (cadd : ∀ X Y, P X → P Y → r'.coeffs (X + Y) = r'.coeffs X + r'.coeffs Y)
    (csmul : ∀ (z : ℂ) X, P X → r'.coeffs (z • X) = z • r'.coeffs X)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hP : ∀ X ∈ r.space.complexSubmodule, P (m X))
    (madd : ∀ X ∈ r.space.complexSubmodule, ∀ Y ∈ r.space.complexSubmodule, m (X + Y) = m X + m Y)
    (msmul : ∀ (z : ℂ), ∀ X ∈ r.space.complexSubmodule, m (z • X) = z • m X) :
    IsCLinear (r.mapOnCoeffs r' m) where
  add f g := by
    show r'.coeffs (m (r.ofCoeffs (f + g))) = r'.coeffs (m (r.ofCoeffs f)) +
      r'.coeffs (m (r.ofCoeffs g))
    rw [hr.add, madd _ (hr.mem f) _ (hr.mem g), cadd _ _ (hP _ (hr.mem f)) (hP _ (hr.mem g))]
  smul z f := by
    show r'.coeffs (m (r.ofCoeffs (z • f))) = z • r'.coeffs (m (r.ofCoeffs f))
    rw [hr.smul, msmul z _ (hr.mem f), csmul z _ (hP _ (hr.mem f))]
section Coefficients
private theorem pauliCoeff_pauliSum (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem pauliSum_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end Coefficients
private theorem isFaithful_of {r : PauliComponentsOfSymmetricKernel} (fin : Finite r.Place)
    (mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule) (left : ∀ c, r.coeffs (r.ofCoeffs c) = c)
    (right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f)
    (cadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      r.coeffs (f + g) = r.coeffs f + r.coeffs g)
    (csmul : ∀ (z : ℂ), ∀ f ∈ r.space.complexSubmodule, r.coeffs (z • f) = z • r.coeffs f) :
    IsFaithful r where
  fin := fin
  mem := mem
  left := left
  right := right
  add c c' := by
    have e := cadd _ (mem c) _ (mem c')
    rw [left, left] at e
    rw [← e, right _ (Submodule.add_mem _ (mem c) (mem c'))]
  smul z c := by
    have e := csmul z _ (mem c)
    rw [left] at e
    rw [← e, right _ (Submodule.smul_mem _ z (mem c))]
section Vertices
variable {σ : Type}
private theorem vertex_mem_iff {f : σ → ComplexMatrix2} :
    f ∈ (vertexCoordinate σ).space.complexSubmodule ↔ ∀ x, f x ∈ ComplexMatrix2.traceless :=
  ⟨fun h x => Submodule.mem_pi.1 h x (mem_univ x), fun h => Submodule.mem_pi.2 fun x _ => h x⟩
private theorem vertex_coeffs_add {f g : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (f + g) = (vertexCoordinate σ).coeffs f + (vertexCoordinate σ).coeffs g :=
  funext fun ι => pauliCoeff_add ι.1 (hf ι.2) (hg ι.2)
private theorem vertex_coeffs_smul (z : ℂ) {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) :
    (vertexCoordinate σ).coeffs (z • f) = z • (vertexCoordinate σ).coeffs f :=
  funext fun ι => pauliCoeff_smul ι.1 z (hf ι.2)
private theorem vertexCoordinate_isFaithful [Finite σ] : IsFaithful (vertexCoordinate σ) :=
  isFaithful_of (r := vertexCoordinate σ) (inferInstanceAs (Finite σ))
    (fun c => vertex_mem_iff.2 (ofPauliCoeffs_mem c))
    (fun c => funext fun ι => pauliCoeff_pauliSum (fun a => c (a, ι.2)) ι.1)
    (fun _ hf => funext fun x => pauliSum_pauliCoeff (vertex_mem_iff.1 hf x))
    (fun _ hf _ hg => vertex_coeffs_add (vertex_mem_iff.1 hf) (vertex_mem_iff.1 hg))
    (fun z _ hf => vertex_coeffs_smul z (vertex_mem_iff.1 hf))
end Vertices
section EdgeForms
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
private theorem edge_coeffs_smul (z : ℂ) {X : Edge L n k j → ComplexMatrix2}
    (hX : TracelessOnPositive X) :
    (edgePauliCoordinates L n k j).coeffs (z • X) = z • (edgePauliCoordinates L n k j).coeffs X := by apply _root_.YangMills.DeltaSharedProofs.p501619 <;> assumption
private theorem tracelessOnPositive_of_mem {X : Edge L n k j → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) : TracelessOnPositive X := hX.1
private def positiveValuesOfCoeffs (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
private theorem edge_ofCoeffs_of_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
private theorem edgePauliCoordinates_isFaithful (hfin : Finite (Edge L n k j))
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    IsFaithful (edgePauliCoordinates L n k j) := by
  have hmem : ∀ c, (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := fun c =>
    ⟨fun b hb => by
      rw [edge_ofCoeffs_of_pos c hb]
      exact ofPauliCoeffs_mem c _, fun b => extendOddly_opposite (positiveValuesOfCoeffs c) (hx b)⟩
  refine isFaithful_of (r := edgePauliCoordinates L n k j) ?_ hmem ?_ ?_ ?_ ?_
  · exact (inferInstanceAs (Finite {b : Edge L n k j // b.IsPositivelyOriented}))
  · intro c
    funext ι
    have e : (edgePauliCoordinates L n k j).ofCoeffs c ι.2.1 = ofPauliCoeffs c ι.2 :=
      edge_ofCoeffs_of_pos c ι.2.2
    show pauliCoeff ι.1 ((edgePauliCoordinates L n k j).ofCoeffs c ι.2.1) = c ι
    rw [e]
    exact pauliCoeff_pauliSum (fun a => c (a, ι.2)) ι.1
  · intro f hf
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs f) b = f b := fun b hb =>
      (edge_ofCoeffs_of_pos _ hb).trans (pauliSum_pauliCoeff (hf.1 b hb))
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
  · exact fun z _ hf => edge_coeffs_smul z hf.1
private theorem covDiff_add (W : Edge L n k j → ComplexMatrix2) (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff W (l + l') = covDiff W l + covDiff W l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
private theorem covDiff_smul (W : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (z : ℂ) : covDiff W (z • l) = z • covDiff W l := by apply _root_.YangMills.SharedProofs.p24956 <;> assumption
variable [Finite (Vertex L n k j)]
end EdgeForms
private structure Inputs : Prop where
  linear : StepMapsComplexLinear.Claim
  near : NormalizedMeanNearOne
  differential : HolDifferentialLinear
  smoothing : SmoothingNearIdentity
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteBonds : BondSetFields.ProductStructureHolds
private theorem represents_of_isCLinear {r r' : PauliComponentsOfSymmetricKernel} (hr : IsFaithful r)
    (hr' : IsFaithful r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hlin : IsCLinear (r.mapOnCoeffs r' m)) :
    Represents (r.kernel r' m) (r.mapOnCoeffs r' m) := by
  have := hr.fin
  have := hr'.fin
  have hT : Represents (r.kernelOfBasisImages r' m) (r.mapOnCoeffs r' m) := fun f =>
    ⟨fun ι' => Summable.of_finite, applyKernel_basisImages hlin f⟩
  exact Classical.epsilon_spec (⟨_, hT⟩ : ∃ T, Represents T (r.mapOnCoeffs r' m))
private theorem iterate_complexLinear {r : ℕ → PauliComponentsOfSymmetricKernel} {k : ℕ}
    (w : ∀ j, ((r j).space.index → ComplexMatrix2) → (r (j + 1)).space.index → ComplexMatrix2)
    (It : ∀ j, ((r 0).space.index → ComplexMatrix2) → (r j).space.index → ComplexMatrix2)
    (h0 : ∀ B, It 0 B = B) (hs : ∀ j < k, ∀ B, It (j + 1) B = w j (It j B))
    (wmem : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, w j X ∈ (r (j + 1)).space.complexSubmodule)
    (wadd : ∀ j < k, ∀ X ∈ (r j).space.complexSubmodule, ∀ Y ∈ (r j).space.complexSubmodule,
      w j (X + Y) = w j X + w j Y)
    (wsmul : ∀ j < k, ∀ (z : ℂ), ∀ X ∈ (r j).space.complexSubmodule, w j (z • X) = z • w j X) :
    ∀ j ≤ k, (∀ X ∈ (r 0).space.complexSubmodule, It j X ∈ (r j).space.complexSubmodule) ∧
      (∀ X ∈ (r 0).space.complexSubmodule, ∀ Y ∈ (r 0).space.complexSubmodule,
        It j (X + Y) = It j X + It j Y) ∧
      (∀ (z : ℂ), ∀ X ∈ (r 0).space.complexSubmodule, It j (z • X) = z • It j X) := by apply _root_.YangMills.SharedProofs.p68818 <;> assumption
section TowerLevels
variable {L n k : ℕ}
private theorem edge_xor_opposite (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
private theorem finite_edge (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.finiteBonds L hL k j hj).1 n hn).2.1
private theorem finite_vertex (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Vertex L n k j) :=
  have := finite_edge G hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0) fun _ _ h =>
    congrArg PeriodicLattice.Bond.source h
private theorem edgePauliCoordinates_faithful (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) : IsFaithful (edgePauliCoordinates L n k j) :=
  edgePauliCoordinates_isFaithful (finite_edge G hL hn hj) (edge_xor_opposite G hL hn hk hj)
private theorem vertexCoordinate_faithful (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : IsFaithful (vertexCoordinate (Vertex L n k j)) :=
  have := finite_vertex G hL hn hj
  vertexCoordinate_isFaithful
private structure StepData (L n k j : ℕ) (C : ℝ) (V : Edge L n k j → ComplexMatrix2) : Prop where
  small : V ∈ smallComplexFields L n k j
  group : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  trace : ∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
    holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless
  linear : ∀ (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
    holLeftDifferential normalizedMean V (z • B + B') =
      z • holLeftDifferential normalizedMean V B + holLeftDifferential normalizedMean V B'
section OneStep
variable {j : ℕ} {C : ℝ} {V : Edge L n k j → ComplexMatrix2}
private theorem meanCovariantStep_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j < k) (h : StepData L n k j C V)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V B ∈ complexEdgeForms L n k (j + 1) := by
  obtain ⟨h₁, _, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have hdrift := (h₁ B hB).2
  have hdiff : holLeftDifferential normalizedMean V B ∈ complexEdgeForms L n k (j + 1) :=
    ⟨fun c hc => h.trace B c hc,
      fun c => extendOddly_opposite _ (edge_xor_opposite G hL hn hk (show j + 1 ≤ k from hj) c)⟩
  refine Submodule.add_mem _ hdiff ⟨fun c hc => ?_, fun c => ?_⟩
  · have e : covDiff (normalizedMean V) (contourLogDrift V B) c =
        ComplexMatrix2.conjugateBy (normalizedMean V c) (contourLogDrift V B c.target) -
          contourLogDrift V B c.source := extendOddly_of_pos _ hc
    rw [e]
    exact ComplexMatrix2.traceless.sub_mem
      ((G.conjugation.2.2 _ (G.conjugation.1 _ (h.group c hc))).2.2.2.1 (hdrift _)) (hdrift _)
  · exact extendOddly_opposite _ (edge_xor_opposite G hL hn hk (show j + 1 ≤ k from hj) c)
private theorem meanCovariantStep_add (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepData L n k j C V) {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (B + B') = meanCovariantStep V B + meanCovariantStep V B' := by
  obtain ⟨_, h₂, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B' hB' 1).2
  have e₁ := h.linear 1 B B'
  rw [one_smul, one_smul] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_add]
  abel
private theorem meanCovariantStep_smul (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepData L n k j C V) (z : ℂ) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V (z • B) = z • meanCovariantStep V B := by
  obtain ⟨_, h₂, _, _⟩ := G.linear L hL n k j hn hj V h.small
  have e₂ := (h₂ B hB B hB (z - 1)).2
  have e₁ := h.linear (z - 1) B B
  have e : (z - 1) • B + B = z • B := by
    rw [sub_smul, one_smul, sub_add_cancel]
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rw [e, e'] at e₁ e₂
  unfold meanCovariantStep
  rw [e₁, e₂, covDiff_smul, smul_add]
private theorem adjointCubeAverage_add (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepData L n k j C V) {l l' : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hl' : ∀ x, l' x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (l + l') = adjointCubeAverage V l + adjointCubeAverage V l' := by
  obtain ⟨_, _, _, h₄⟩ := G.linear L hL n k j hn hj V h.small
  have e := (h₄ l l' hl hl' 1).2
  rwa [one_smul, one_smul] at e
private theorem adjointCubeAverage_smul (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepData L n k j C V) (z : ℂ)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V (z • l) = z • adjointCubeAverage V l := by
  obtain ⟨_, _, _, h₄⟩ := G.linear L hL n k j hn hj V h.small
  have e := (h₄ l l hl hl (z - 1)).2
  have e' : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (x : E), (z - 1) • x + x = z • x := by
    intro E _ _ x
    rw [sub_smul, one_smul, sub_add_cancel]
  rwa [e', e'] at e
private theorem adjointCubeAverage_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (h : StepData L n k j C V) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (y : Vertex L n k (j + 1)) :
    adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := by
  obtain ⟨_, _, h₃, _⟩ := G.linear L hL n k j hn hj V h.small
  exact (h₃ l hl).2 y
private theorem real_smul_eq_complex_smul_fun {ι : Type} (t : ℝ) (Y : ι → ComplexMatrix2) :
    t • Y = (t : ℂ) • Y := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
end OneStep
variable {C : ℝ} {U : Edge L n k 0 → ComplexMatrix2}
private theorem meanCovariant_complexLinear (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (h : ∀ j < k, StepData L n k j C (meanIterate U j)) :
    (∀ X ∈ complexEdgeForms L n k 0, meanCovariant U k X ∈ complexEdgeForms L n k k) ∧
    (∀ X ∈ complexEdgeForms L n k 0, ∀ Y ∈ complexEdgeForms L n k 0,
      meanCovariant U k (X + Y) = meanCovariant U k X + meanCovariant U k Y) ∧
    (∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k 0,
      meanCovariant U k (z • X) = z • meanCovariant U k X) :=
  iterate_complexLinear (r := fun j => edgePauliCoordinates L n k j) (k := k)
    (fun j => meanCovariantStep (meanIterate U j)) (fun j => meanCovariant U j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => meanCovariantStep_mem G hL hn hk hj (h j hj) hX)
    (fun j hj X hX Y hY => meanCovariantStep_add G hL hn hj (h j hj) hX hY)
    (fun j hj z X hX => meanCovariantStep_smul G hL hn hj (h j hj) z hX) k le_rfl
private theorem isCLinear_scaled {s e : ℕ} (hs : IsFaithful (edgePauliCoordinates L n k s)) (a : ℝ)
    {M : (Edge L n k s → ComplexMatrix2) → Edge L n k e → ComplexMatrix2}
    (hm : ∀ X ∈ complexEdgeForms L n k s, M X ∈ complexEdgeForms L n k e)
    (ha : ∀ X ∈ complexEdgeForms L n k s, ∀ Y ∈ complexEdgeForms L n k s, M (X + Y) = M X + M Y)
    (hz : ∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k s, M (z • X) = z • M X) :
    IsCLinear ((edgePauliCoordinates L n k s).mapOnCoeffs (edgePauliCoordinates L n k e) fun B => a • M B) := by
  have hz' : ∀ (z : ℂ), ∀ X ∈ complexEdgeForms L n k s, a • M (z • X) = z • a • M X := by
    intro z X hX
    rw [hz z X hX, real_smul_eq_complex_smul_fun, real_smul_eq_complex_smul_fun, smul_comm]
  refine isCLinear_mapOnCoeffs hs (fun X => TracelessOnPositive (L := L) (n := n) (k := k) X)
    (fun _ _ hX hY => edge_coeffs_add hX hY) (fun z _ hX => edge_coeffs_smul z hX) ?_ ?_ ?_
  · intro X hX
    have : (a : ℂ) • M X ∈ complexEdgeForms L n k e := Submodule.smul_mem _ _ (hm X hX)
    rw [real_smul_eq_complex_smul_fun]
    exact tracelessOnPositive_of_mem this
  · intro X hX Y hY
    exact (congrArg (fun x => a • x) (ha X hX Y hY)).trans (smul_add a _ _)
  · intro z X hX
    exact hz' z X hX
private theorem represents_meanKernelQ (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (h : ∀ j < k, StepData L n k j C (meanIterate U j)) :
    Represents (meanKernelQ L n k U) ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
      fun B => finestMesh L k • meanCovariant U k B) := by
  obtain ⟨hm, ha, hz⟩ := meanCovariant_complexLinear G hL hn hk h
  exact represents_of_isCLinear (edgePauliCoordinates_faithful G hL hn hk (Nat.zero_le k))
    (edgePauliCoordinates_faithful G hL hn hk le_rfl)
    (isCLinear_scaled (edgePauliCoordinates_faithful G hL hn hk (Nat.zero_le k)) _ hm ha hz)
private theorem represents_meanKernelR (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (h : ∀ j < k, StepData L n k j C (meanIterate U j)) :
    Represents (meanKernelR L n k U) ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k k)) (composedCubeAverage (quietPoint U) k)) := by
  have hr := vertexCoordinate_faithful (k := k) G hL hn (Nat.zero_le k)
  have hl := iterate_complexLinear (r := fun j => vertexCoordinate (Vertex L n k j)) (k := k)
    (fun j => adjointCubeAverage (meanIterate U j))
    (fun j => composedCubeAverage (quietPoint U) j)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun j hj X hX => vertex_mem_iff.2
      (adjointCubeAverage_mem G hL hn hj (h j hj) (vertex_mem_iff.1 hX)))
    (fun j hj X hX Y hY => adjointCubeAverage_add G hL hn hj (h j hj) (vertex_mem_iff.1 hX)
      (vertex_mem_iff.1 hY))
    (fun j hj z X hX => adjointCubeAverage_smul G hL hn hj (h j hj) z (vertex_mem_iff.1 hX))
    k le_rfl
  obtain ⟨hm, ha, hz⟩ := hl
  have hlin : IsCLinear ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs
      (vertexCoordinate (Vertex L n k k)) (composedCubeAverage (quietPoint U) k)) := by
    have := finite_vertex (k := k) G hL hn le_rfl
    refine isCLinear_mapOnCoeffs hr
      (fun X : Vertex L n k k → ComplexMatrix2 => ∀ x, X x ∈ ComplexMatrix2.traceless)
      (fun _ _ hX hY => vertex_coeffs_add hX hY) (fun z _ hX => vertex_coeffs_smul z hX)
      (fun X hX => vertex_mem_iff.1 (hm X hX)) ha hz
  exact represents_of_isCLinear hr (vertexCoordinate_faithful G hL hn le_rfl) hlin
end TowerLevels
private theorem claim_holds (G : Inputs) : Claim := by
  intro L hL
  obtain ⟨ρ₂, hρ₂, hN⟩ := G.near L hL
  obtain ⟨ρ₃, hρ₃, hD⟩ := G.differential L hL
  have hρL := (G.smoothing.1 L hL).2.2.pos
  obtain ⟨r, hr, hr₂, hr₃, hr₄⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ρ₂ ∧ r ≤ ρ₃ ∧
      r ≤ polydiscRadius L / 2 :=
    ⟨min ρ₂ (min ρ₃ (polydiscRadius L / 2)),
      lt_min hρ₂ (lt_min hρ₃ (by linarith)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨r, hr, ?_⟩
  intro n k hn hk U hU
  have hfacts : ∀ j < k, StepData L n k j 0 (meanIterate U j) := by
    intro j hj
    have hV := (hU j hj).1
    have hb := (hU j hj).2
    have hD' := hD n k j hn hj _ hV fun b => (hb b).trans_le hr₃
    refine ⟨⟨hV, fun b => ?_⟩, fun c hc => ?_, hD'.1, hD'.2⟩
    · linarith [hb b]
    · exact (hN n k j hn hj _ hV (fun b => (hb b).trans_le hr₂) c hc).2.2.2.1
  exact ⟨represents_meanKernelQ G hL hn hk hfacts, represents_meanKernelR G hL hn hk hfacts⟩
theorem claim_of (h₄ : StepMapsComplexLinear.Claim)
    (h₅ : NormalizedMeanNearOne) (h₆ : HolDifferentialLinear)
    (h₇ : SmoothingNearIdentity)
    (h₈ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₉ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₁₀ : BondSetFields.ProductStructureHolds) : Claim :=
  claim_holds ⟨h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
end YangMills.Construction.RunningCouplingSlope.MeanKernelsRepresent
end
