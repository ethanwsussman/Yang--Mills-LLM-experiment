import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLattice
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import YangMills.Construction.Towers.PlaquettesOfABondProof
import YangMills.Construction.Towers.TransposesOfTheDifferencesAtAPointOfTheUnitLattice
import YangMills.Construction.Towers.TwoOperatorsMultiplyPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (axisStep)
open PeriodicOperators (toComplexVec bilinDot)
namespace Tower.PlaneWaveEigenProof
section Forms
variable {a : ℝ}
theorem axisStep_apply_self (μ : Fin 4) :
    ((axisStep a μ : InfiniteLattice.LatticePoint a) : Fin 4 → ℝ) μ = a := by
  show (Pi.single μ a : Fin 4 → ℝ) μ = a
  simp
theorem axisStep_apply_ne {μ ν : Fin 4} (h : ν ≠ μ) :
    ((axisStep a μ : InfiniteLattice.LatticePoint a) : Fin 4 → ℝ) ν = 0 := by
  show (Pi.single μ a : Fin 4 → ℝ) ν = 0
  simp [Pi.single_eq_of_ne h]
theorem axisStep_injective (ha : a ≠ 0) {μ ν : Fin 4} (h : axisStep a μ = axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem forwardFrom_isPositivelyOriented (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem isPositivelyOriented_opposite_of_not {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_opposite (ha : a ≠ 0) (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.extendOddly_opposite <;> assumption
theorem extendOddly_forwardFrom (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.extendOddly f (InfiniteLattice.Link.forwardFrom x μ) =
      f (InfiniteLattice.Link.forwardFrom x μ) := by
  classical
  unfold FullSpace.extendOddly
  rw [if_pos (forwardFrom_isPositivelyOriented x μ)]
theorem oddForm_ext {B B' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : ∀ b, B b.opposite = -B b) (hB' : ∀ b, B' b.opposite = -B' b)
    (h : ∀ x μ, B (InfiniteLattice.Link.forwardFrom x μ) = B' (InfiniteLattice.Link.forwardFrom x μ)) :
    B = B' := by
  have hp : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b := by
    rintro b ⟨μ, hμ⟩
    have e : b = InfiniteLattice.Link.forwardFrom b.initial μ := by
      refine InfiniteLattice.Link.ext rfl ?_
      show b.terminal = b.initial + axisStep a μ
      rw [← hμ]
      abel
    rw [e]
    exact h _ _
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hb
  · have e := hp _ (isPositivelyOriented_opposite_of_not hb)
    rw [hB, hB'] at e
    exact neg_injective e
theorem vertexCoboundary_mem {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    FullSpace.vertexCoboundary l ∈ FullSpace.complexEdgeForms a := by
  refine ⟨fun b _ => Matrices.ComplexMatrix2.traceless.sub_mem (hl _) (hl _), fun b => ?_⟩
  simp [FullSpace.vertexCoboundary, InfiniteLattice.Link.opposite]
theorem extendOddly_mem (ha : a ≠ 0) {f : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hf : ∀ b, f b ∈ Matrices.ComplexMatrix2.traceless) :
    FullSpace.extendOddly f ∈ FullSpace.complexEdgeForms a := by
  classical
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite ha f b⟩
  show FullSpace.extendOddly f b ∈ Matrices.ComplexMatrix2.traceless
  unfold FullSpace.extendOddly
  rw [if_pos hb]
  exact hf b
end Forms
theorem transposeOfValues_congr (S S' : PairedFunctionSpace)
    {m m' : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2}
    (h : ∀ f ∈ S.complexSubmodule, m f = m' f) :
    PairedFunctionSpace.transposeOfValues S S' m = PairedFunctionSpace.transposeOfValues S S' m' := by
  have e : PairedFunctionSpace.linearOfValues S S' m = PairedFunctionSpace.linearOfValues S S' m' := by
    unfold PairedFunctionSpace.linearOfValues
    congr 1
    funext T
    apply propext
    constructor
    · intro hT f
      rw [hT f, h f f.2]
    · intro hT f
      rw [hT f, h f f.2]
  unfold PairedFunctionSpace.transposeOfValues
  rw [e]
section Numbers
variable {L : ℕ}
theorem meshAt_ne_zero (L : ℕ) : meshAt L 0 0 ≠ 0 := by
  simp [meshAt]
theorem meshAt_eq_one (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
def planePhase (q : Fin 4 → ℂ) (x : FullSpace.Vertex L 0 0) : ℂ :=
  Complex.exp (Complex.I * bilinDot q (toComplexVec x))
def forwardFactor (q : Fin 4 → ℂ) (μ : Fin 4) : ℂ := Complex.exp (Complex.I * q μ)
def backwardFactor (q : Fin 4 → ℂ) (μ : Fin 4) : ℂ := Complex.exp (-(Complex.I * q μ))
theorem forwardFactor_mul_backwardFactor (q : Fin 4 → ℂ) (μ : Fin 4) :
    forwardFactor q μ * backwardFactor q μ = 1 := by
  simp [forwardFactor, backwardFactor, ← Complex.exp_add]
theorem axisSymbol_eq (q : Fin 4 → ℂ) (μ : Fin 4) :
    Massive.axisSymbol μ q = (backwardFactor q μ - 1) * (forwardFactor q μ - 1) := by
  have e : Complex.cos (q μ) = (forwardFactor q μ + backwardFactor q μ) / 2 := by
    simp only [forwardFactor, backwardFactor, Complex.cos]
    congr 2
    · rw [mul_comm]
    · rw [neg_mul, mul_comm]
  unfold Massive.axisSymbol
  rw [e]
  linear_combination (-1 : ℂ) * forwardFactor_mul_backwardFactor q μ
theorem planePhase_add (q : Fin 4 → ℂ) (x y : FullSpace.Vertex L 0 0) :
    planePhase q (x + y) = planePhase q x * planePhase q y := by
  simp only [planePhase, ← Complex.exp_add, ← mul_add]
  congr 2
  simp [bilinDot, toComplexVec, mul_add, Finset.sum_add_distrib]
theorem planePhase_axisStep (q : Fin 4 → ℂ) (μ : Fin 4) :
    planePhase (L := L) q (axisStep (meshAt L 0 0) μ) = forwardFactor q μ := by
  unfold planePhase forwardFactor
  congr 2
  unfold bilinDot toComplexVec
  rw [Finset.sum_eq_single μ]
  · rw [axisStep_apply_self, meshAt_eq_one]
    simp
  · intro ν _ h
    rw [axisStep_apply_ne h]
    simp
  · simp
theorem planePhase_add_axisStep (q : Fin 4 → ℂ) (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    planePhase q (x + axisStep (meshAt L 0 0) μ) = planePhase q x * forwardFactor q μ := by
  rw [planePhase_add, planePhase_axisStep]
theorem planePhase_sub_axisStep (q : Fin 4 → ℂ) (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    planePhase q (x - axisStep (meshAt L 0 0) μ) = planePhase q x * backwardFactor q μ := by
  have e := planePhase_add_axisStep q (x - axisStep (meshAt L 0 0) μ) μ
  rw [sub_add_cancel] at e
  calc planePhase q (x - axisStep (meshAt L 0 0) μ)
      = planePhase q (x - axisStep (meshAt L 0 0) μ) * (forwardFactor q μ * backwardFactor q μ) := by
        rw [forwardFactor_mul_backwardFactor, mul_one]
    _ = planePhase q x * backwardFactor q μ := by rw [e]; ring
end Numbers
section Waves
variable {L : ℕ}
theorem vertexPlaneWave_apply (q : Fin 4 → ℂ) (X : Matrices.ComplexMatrix2) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexPlaneWave L q X x = planePhase q x • X := rfl
theorem vertexPlaneWave_mem (q : Fin 4 → ℂ) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexPlaneWave L q X x ∈ Matrices.ComplexMatrix2.traceless :=
  Matrices.ComplexMatrix2.traceless.smul_mem _ hX
theorem vertexCoboundary_vertexPlaneWave (q : Fin 4 → ℂ) (X : Matrices.ComplexMatrix2)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.vertexCoboundary (FullSpace.vertexPlaneWave L q X) (InfiniteLattice.Link.forwardFrom x μ) =
      (planePhase q x * (forwardFactor q μ - 1)) • X := by
  show FullSpace.vertexPlaneWave L q X (x + axisStep (meshAt L 0 0) μ) - FullSpace.vertexPlaneWave L q X x = _
  rw [vertexPlaneWave_apply, vertexPlaneWave_apply, planePhase_add_axisStep, mul_sub, mul_one, sub_smul]
theorem edgePlaneWave_forwardFrom (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.edgePlaneWave L q c (InfiniteLattice.Link.forwardFrom x μ) = planePhase q x • c μ := by
  classical
  unfold FullSpace.edgePlaneWave
  rw [extendOddly_forwardFrom]
  show planePhase q x • _ = _
  congr 1
  rw [Finset.sum_eq_single μ]
  · rw [if_pos]
    show x + axisStep (meshAt L 0 0) μ - x = _
    abel
  · intro ν _ h
    rw [if_neg]
    intro e
    have e' : axisStep (meshAt L 0 0) μ = axisStep (meshAt L 0 0) ν := by
      rw [← e]
      show _ = x + axisStep (meshAt L 0 0) μ - x
      abel
    exact h (axisStep_injective (meshAt_ne_zero L) e').symm
  · simp
theorem edgePlaneWave_mem (q : Fin 4 → ℂ) {c : Fin 4 → Matrices.ComplexMatrix2}
    (hc : ∀ μ, c μ ∈ Matrices.ComplexMatrix2.traceless) :
    FullSpace.edgePlaneWave L q c ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
  classical
  refine extendOddly_mem (meshAt_ne_zero L) fun b => Matrices.ComplexMatrix2.traceless.smul_mem _ ?_
  refine Matrices.ComplexMatrix2.traceless.sum_mem fun μ _ => ?_
  split_ifs
  · exact hc μ
  · exact Matrices.ComplexMatrix2.traceless.zero_mem
theorem edgePlaneWave_opposite (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) :
    FullSpace.edgePlaneWave L q c b.opposite = -FullSpace.edgePlaneWave L q c b :=
  extendOddly_opposite (meshAt_ne_zero L) _ b
theorem edgeCoboundary_edgePlaneWave (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2)
    (p : FullSpace.Face L 0 0) :
    FullSpace.edgeCoboundary (FullSpace.edgePlaneWave L q c) p =
      planePhase q p.corner • ((forwardFactor q p.lowAxis - 1) • c p.highAxis -
        (forwardFactor q p.highAxis - 1) • c p.lowAxis) := by
  unfold FullSpace.edgeCoboundary
  simp only [edgePlaneWave_forwardFrom, planePhase_add_axisStep]
  module
theorem edgeCoboundary_edgePlaneWave_mem (q : Fin 4 → ℂ) {c : Fin 4 → Matrices.ComplexMatrix2}
    (hc : ∀ μ, c μ ∈ Matrices.ComplexMatrix2.traceless) :
    FullSpace.edgeCoboundary (FullSpace.edgePlaneWave L q c) ∈
      Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Face L 0 0) := by
  intro p _
  rw [edgeCoboundary_edgePlaneWave]
  exact Matrices.ComplexMatrix2.traceless.smul_mem _
    (Matrices.ComplexMatrix2.traceless.sub_mem (Matrices.ComplexMatrix2.traceless.smul_mem _ (hc _))
      (Matrices.ComplexMatrix2.traceless.smul_mem _ (hc _)))
end Waves
section Transposes
variable {L : ℕ}
open UnitLatticeAdjoints (vertexCoboundaryAdjoint edgeCoboundaryAdjoint)
theorem covDiffAdjoint_one
    (h₁ : ∀ l ∈ (vertexCoordinate (FullSpace.Vertex L 0 0)).space.complexSubmodule,
      FullSpace.covDiff (fun _ : FullSpace.Edge L 0 0 => (1 : Matrices.ComplexMatrix2)) l =
        FullSpace.vertexCoboundary l)
    (B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) :
    FullSpace.covDiffAdjoint (fun _ => 1) B = vertexCoboundaryAdjoint L B := congrFun (transposeOfValues_congr (pairedFunctions _) (FullSpace.edgePairedSpace _) h₁) B
theorem vertexCoboundaryAdjoint_edgePlaneWave
    (h₂ : ∀ b ∈ FullSpace.complexEdgeForms (meshAt L 0 0), ∀ x : FullSpace.Vertex L 0 0,
      vertexCoboundaryAdjoint L b x =
        ∑ μ : Fin 4, (b (InfiniteLattice.Link.forwardFrom (x - axisStep (meshAt L 0 0) μ) μ) -
          b (InfiniteLattice.Link.forwardFrom x μ)))
    (q : Fin 4 → ℂ) {c : Fin 4 → Matrices.ComplexMatrix2}
    (hc : ∀ μ, c μ ∈ Matrices.ComplexMatrix2.traceless) :
    vertexCoboundaryAdjoint L (FullSpace.edgePlaneWave L q c) =
      FullSpace.vertexPlaneWave L q (∑ ν, (backwardFactor q ν - 1) • c ν) := by
  funext x
  rw [h₂ _ (edgePlaneWave_mem q hc) x, vertexPlaneWave_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [edgePlaneWave_forwardFrom, edgePlaneWave_forwardFrom, planePhase_sub_axisStep]
  module
theorem vertexCoboundaryAdjoint_vertexCoboundary_vertexPlaneWave
    (h₂ : ∀ b ∈ FullSpace.complexEdgeForms (meshAt L 0 0), ∀ x : FullSpace.Vertex L 0 0,
      vertexCoboundaryAdjoint L b x =
        ∑ μ : Fin 4, (b (InfiniteLattice.Link.forwardFrom (x - axisStep (meshAt L 0 0) μ) μ) -
          b (InfiniteLattice.Link.forwardFrom x μ)))
    (q : Fin 4 → ℂ) {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    vertexCoboundaryAdjoint L (FullSpace.vertexCoboundary (FullSpace.vertexPlaneWave L q X)) =
      Massive.latticeSymbol q • FullSpace.vertexPlaneWave L q X := by
  funext x
  rw [h₂ _ (vertexCoboundary_mem (vertexPlaneWave_mem q hX)) x]
  simp only [vertexCoboundary_vertexPlaneWave, planePhase_sub_axisStep, Pi.smul_apply,
    vertexPlaneWave_apply]
  rw [Massive.latticeSymbol, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [axisSymbol_eq]
  module
theorem sum_gt_add_sum_lt {M : Type} [AddCommMonoid M] (μ : Fin 4) (g : Fin 4 → M)
    (hg : g μ = 0) :
    (∑ ν : {ν : Fin 4 // μ < ν}, g ν.1) + ∑ ν : {ν : Fin 4 // ν < μ}, g ν.1 = ∑ ν, g ν := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun ν => μ < ν) (by simp) g,
    ← Finset.sum_subtype (Finset.univ.filter fun ν => ν < μ) (by simp) g,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rcases lt_trichotomy μ ν with h | h | h
  · simp [h, h.le.not_gt]
  · subst h
    simp [hg]
  · simp [h, h.le.not_gt]
theorem edgeCoboundaryAdjoint_edgeCoboundary_edgePlaneWave
    (h₂ : ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Face L 0 0),
      ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
        edgeCoboundaryAdjoint L f (InfiniteLattice.Link.forwardFrom x μ) =
          (∑ ν : {ν : Fin 4 // μ < ν},
            (f ⟨x, μ, ν.1, ν.2⟩ - f ⟨x - axisStep (meshAt L 0 0) ν.1, μ, ν.1, ν.2⟩)) -
          ∑ ν : {ν : Fin 4 // ν < μ},
            (f ⟨x, ν.1, μ, ν.2⟩ - f ⟨x - axisStep (meshAt L 0 0) ν.1, ν.1, μ, ν.2⟩))
    (q : Fin 4 → ℂ) {c : Fin 4 → Matrices.ComplexMatrix2}
    (hc : ∀ μ, c μ ∈ Matrices.ComplexMatrix2.traceless)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    edgeCoboundaryAdjoint L (FullSpace.edgeCoboundary (FullSpace.edgePlaneWave L q c))
        (InfiniteLattice.Link.forwardFrom x μ) =
      planePhase q x • ∑ ν, (1 - backwardFactor q ν) •
        ((forwardFactor q μ - 1) • c ν - (forwardFactor q ν - 1) • c μ) := by
  rw [h₂ _ (edgeCoboundary_edgePlaneWave_mem q hc) x μ]
  rw [← sum_gt_add_sum_lt μ _ (by simp), smul_add, Finset.smul_sum, Finset.smul_sum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [edgeCoboundary_edgePlaneWave, planePhase_sub_axisStep]
    module
  · refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [edgeCoboundary_edgePlaneWave, planePhase_sub_axisStep]
    module
end Transposes
theorem latticeSymbol_identity_at_edge (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2) (μ : Fin 4) :
    (∑ ν, (1 - backwardFactor q ν) • ((forwardFactor q μ - 1) • c ν - (forwardFactor q ν - 1) • c μ)) +
        (forwardFactor q μ - 1) • ∑ ν, (backwardFactor q ν - 1) • c ν =
      Massive.latticeSymbol q • c μ := by
  rw [Massive.latticeSymbol, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [axisSymbol_eq]
  module
theorem planeWaveEigen_holds (hD : CoboundariesAtIdentity)
    (hT : UnitLatticeAdjoints.AdjointFormulas) : TwoOperators.PlaneWaveEigen := by
  intro L hL
  obtain ⟨d₁, d₂⟩ := hD L hL
  obtain ⟨t₁, t₂⟩ := hT L hL
  have vertex_mem : ∀ {q : Fin 4 → ℂ} {X : Matrices.ComplexMatrix2},
      X ∈ Matrices.ComplexMatrix2.traceless →
      FullSpace.vertexPlaneWave L q X ∈ (vertexCoordinate (FullSpace.Vertex L 0 0)).space.complexSubmodule :=
    fun hX x _ => vertexPlaneWave_mem _ hX x
  refine ⟨fun q X hX => ?_, fun q c hc => ?_⟩
  · unfold FullSpace.gaugeLaplacian
    rw [covDiffAdjoint_one d₁, d₁ _ (vertex_mem hX)]
    exact vertexCoboundaryAdjoint_vertexCoboundary_vertexPlaneWave t₁ q hX
  · have hY : (∑ ν, (backwardFactor q ν - 1) • c ν) ∈ Matrices.ComplexMatrix2.traceless :=
      Matrices.ComplexMatrix2.traceless.sum_mem fun ν _ =>
        Matrices.ComplexMatrix2.traceless.smul_mem _ (hc ν)
    unfold FullSpace.massiveHessian
    rw [covDiffAdjoint_one d₁, vertexCoboundaryAdjoint_edgePlaneWave t₁ q hc]
    refine oddForm_ext (fun b => ?_) (fun b => ?_) fun x μ => ?_
    · have r₁ : ∀ b : FullSpace.Edge L 0 0,
          FullSpace.complexHessianOperator (fun _ => 1) (FullSpace.edgePlaneWave L q c) b.opposite =
            -FullSpace.complexHessianOperator (fun _ => 1) (FullSpace.edgePlaneWave L q c) b :=
        fun b => extendOddly_opposite (meshAt_ne_zero L) _ b
      have r₂ : ∀ b : FullSpace.Edge L 0 0,
          FullSpace.covDiff (fun _ => 1)
              (FullSpace.vertexPlaneWave L q (∑ ν, (backwardFactor q ν - 1) • c ν)) b.opposite =
            -FullSpace.covDiff (fun _ => 1)
              (FullSpace.vertexPlaneWave L q (∑ ν, (backwardFactor q ν - 1) • c ν)) b :=
        fun b => extendOddly_opposite (meshAt_ne_zero L) _ b
      rw [Pi.add_apply, Pi.add_apply, r₁, r₂, neg_add]
    · simp only [Pi.smul_apply, edgePlaneWave_opposite, smul_neg]
    · have e : FullSpace.complexHessianOperator (fun _ => 1) (FullSpace.edgePlaneWave L q c)
            (InfiniteLattice.Link.forwardFrom x μ) =
          planePhase q x • ∑ ν, (1 - backwardFactor q ν) •
            ((forwardFactor q μ - 1) • c ν - (forwardFactor q ν - 1) • c μ) := by
        rw [d₂ _ (edgePlaneWave_mem q hc)]
        exact edgeCoboundaryAdjoint_edgeCoboundary_edgePlaneWave t₂ q hc x μ
      rw [Pi.add_apply, e, d₁ _ (vertex_mem hY), vertexCoboundary_vertexPlaneWave, Pi.smul_apply,
        edgePlaneWave_forwardFrom, mul_smul, ← smul_add, latticeSymbol_identity_at_edge, smul_comm]
end Tower.PlaneWaveEigenProof
end YangMills.Construction
end
