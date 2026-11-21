import YangMills.Construction.Towers.IteratedAveragesBoundsAtTheSideInfinityProof
import YangMills.Construction.PeriodicOperators.TransposeOfAPeriodicOperatorProof
import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.TheFlatPlainStepIsLocal
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FullLattice.FlatMeanStep
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
private theorem euclidNormVec_sub_comm (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) = euclidNormVec (w - v) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
private theorem euclidNormVec_sub_offsetPoint_le {y : AmbientSpace} {ν : Fin 4 → ℤ} {a B : ℝ}
    (hB : B ≤ 3 / 2) (h : ∀ ρ, |(ν ρ : ℝ) * a| < B) :
    euclidNormVec (y - FullSpace.offsetPoint a y ν) ≤ 3 := by apply _root_.YangMills.Construction.Tower.FreeOperators.euclidNormVec_sub_offsetPoint_le <;> assumption
section LinearMaps
variable {N N' : Type}
open Classical in
private def basisFun (ι : N) : N → ℂ := fun x => if x = ι then 1 else 0
private theorem kernel_eq_apply_basisFun {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (hT : Represents T M) (ι' : N') (ι : N) : T ι' ι = M (basisFun ι) ι' := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
private theorem represents_of_local {M : (N → ℂ) → N' → ℂ} {R : N' → Set N}
    (hadd : ∀ f g, M (f + g) = M f + M g) (hsmul : ∀ (w : ℂ) f, M (w • f) = w • M f)
    (hrows : ∀ ι', (R ι').Finite) (hloc : ∀ f ι', (∀ ι ∈ R ι', f ι = 0) → M f ι' = 0) :
    Represents (fun ι' ι => M (basisFun ι) ι') M := by
  classical
  have hzero : ∀ {ι ι'}, ι ∉ R ι' → M (basisFun ι) ι' = 0 := fun {ι ι'} hι =>
    hloc _ _ fun x hx => by
      have : x ≠ ι := fun e => hι (e ▸ hx)
      simp [basisFun, this]
  intro f
  refine ⟨fun ι' => ?_, ?_⟩
  · refine summable_of_hasFiniteSupport ((hrows ι').subset fun ι hι => ?_)
    by_contra h
    apply hι
    simp [hzero h]
  funext ι'
  let Ml : (N → ℂ) →ₗ[ℂ] (N' → ℂ) := ⟨⟨M, hadd⟩, hsmul⟩
  let F : Finset N := (hrows ι').toFinset
  let g : N → ℂ := ∑ ι ∈ F, f ι • basisFun ι
  have hg : ∀ ι ∈ R ι', (f - g) ι = 0 := by
    intro ι hι
    have hF : ι ∈ F := (hrows ι').mem_toFinset.2 hι
    have : g ι = f ι := by
      simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisFun]
      rw [Finset.sum_eq_single ι]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · exact fun h' => absurd hF h'
    simp [this]
  have e1 : Ml (f - g) ι' = 0 := hloc _ _ hg
  have e2 : M f ι' = Ml g ι' := by
    have : Ml f ι' - Ml g ι' = 0 := by
      rw [map_sub] at e1
      simpa using e1
    exact sub_eq_zero.1 this
  have e3 : Ml g ι' = ∑ ι ∈ F, M (basisFun ι) ι' * f ι := by
    simp only [g, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [mul_comm]
    rfl
  rw [e2, e3]
  unfold applyKernel
  refine tsum_eq_sum fun ι hι => ?_
  show M (basisFun ι) ι' * f ι = 0
  rw [hzero fun h' => hι ((hrows ι').mem_toFinset.2 h'), zero_mul]
private theorem represents_kernelOfMap {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : Represents (kernelOfMap M) M :=
  Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, h⟩
end LinearMaps
section PauliCoefficients
private theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
private theorem pauliCoeff_im {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a Y).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
private theorem pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (c : ℂ)
    (a : Fin 3) : pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add {X Y : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (h' : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem ofPauliCoeffs_mem_hermitianTraceless {σ : Type} {f : Fin 3 × σ → ℂ}
    (hf : ∀ i, (f i).im = 0) (x : σ) : ofPauliCoeffs f x ∈ ComplexMatrix2.hermitianTraceless := by
  refine ComplexMatrix2.hermitianTraceless.sum_mem fun a _ => ?_
  have h : f (a, x) = ((f (a, x)).re : ℂ) := by
    apply Complex.ext <;> simp [hf]
  rw [h, Complex.coe_smul]
  exact ComplexMatrix2.hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)
abbrev _root_.YangMills.SharedProofs.p63155 := @ofPauliCoeffs_mem_hermitianTraceless
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end PauliCoefficients
section Edges
variable {L k j : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem meshAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    meshAt L k j ≤ 1 := by apply _root_.YangMills.Construction.Tower.FreeOperators.meshAt_le_one <;> assumption
private theorem xor_isPositive_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
private theorem extendOddly_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : FullSpace.Edge L k j → ComplexMatrix2) (b : FullSpace.Edge L k j) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.SharedProofs.p3001 <;> assumption
private abbrev ColourEdge (L k j : ℕ) : Type := Fin 3 × FullSpace.PositiveEdge (meshAt L k j)
private def edgeForm (f : ColourEdge L k j → ℂ) : FullSpace.Edge L k j → ComplexMatrix2 :=
  (FullSpace.edgePauliCoordinates L k j).ofCoeffs f
private theorem edgeForm_eq (f : ColourEdge L k j → ℂ) (b : FullSpace.Edge L k j) :
    edgeForm f b = open Classical in
      FullSpace.extendOddly
        (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0) b := rfl
private theorem edgeForm_of_isPositive (f : ColourEdge L k j → ℂ) {b : FullSpace.Edge L k j}
    (h : b.IsPositivelyOriented) : edgeForm f b = ofPauliCoeffs f ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_apply <;> assumption
private theorem edgeForm_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : ColourEdge L k j → ℂ) : edgeForm f ∈ FullSpace.complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_mem <;> assumption
private theorem edgeForm_mem_traceless (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : ColourEdge L k j → ℂ) (b : FullSpace.Edge L k j) :
    edgeForm f b ∈ ComplexMatrix2.traceless := by
  rcases xor_isPositive_opposite (meshAt_pos hL k j) b with ⟨hp, -⟩ | ⟨hr, -⟩
  · rw [edgeForm_of_isPositive f hp]
    exact ofPauliCoeffs_mem_traceless f _
  · have h1 : edgeForm f b = -edgeForm f b.opposite := by
      have := (edgeForm_mem hL f).2 b.opposite
      have hrr : b.opposite.opposite = b := rfl
      rwa [hrr] at this
    rw [h1, edgeForm_of_isPositive f hr]
    exact ComplexMatrix2.traceless.neg_mem (ofPauliCoeffs_mem_traceless f _)
private theorem edgeForm_mem_hermitianTraceless (hL : Conventions.IsAdmissibleBlockingFactor L)
    {f : ColourEdge L k j → ℂ} (hf : ∀ i, (f i).im = 0) (b : FullSpace.Edge L k j) :
    edgeForm f b ∈ ComplexMatrix2.hermitianTraceless := by
  rcases xor_isPositive_opposite (meshAt_pos hL k j) b with ⟨hp, -⟩ | ⟨hr, -⟩
  · rw [edgeForm_of_isPositive f hp]
    exact ofPauliCoeffs_mem_hermitianTraceless hf _
  · have h1 : edgeForm f b = -edgeForm f b.opposite := by
      have := (edgeForm_mem hL f).2 b.opposite
      have hrr : b.opposite.opposite = b := rfl
      rwa [hrr] at this
    rw [h1, edgeForm_of_isPositive f hr]
    exact ComplexMatrix2.hermitianTraceless.neg_mem (ofPauliCoeffs_mem_hermitianTraceless hf _)
private theorem edgeForm_add (f g : ColourEdge L k j → ℂ) :
    edgeForm (f + g) = edgeForm f + edgeForm g := by
  classical
  funext b
  have h : ∀ c : FullSpace.Edge L k j,
      (if h : c.IsPositivelyOriented then ofPauliCoeffs (f + g) ⟨c, h⟩ else 0) =
      (if h : c.IsPositivelyOriented then ofPauliCoeffs f ⟨c, h⟩ else (0 : ComplexMatrix2)) +
        (if h : c.IsPositivelyOriented then ofPauliCoeffs g ⟨c, h⟩ else (0 : ComplexMatrix2)) := by
    intro c
    split_ifs
    · simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
    · simp
  rw [Pi.add_apply, edgeForm_eq, edgeForm_eq, edgeForm_eq]
  simp only [FullSpace.extendOddly, h]
  split_ifs
  · rfl
  · abel
  · simp
private theorem edgeForm_smul (w : ℂ) (f : ColourEdge L k j → ℂ) :
    edgeForm (w • f) = w • edgeForm f := by
  classical
  funext b
  have h : ∀ c : FullSpace.Edge L k j,
      (if h : c.IsPositivelyOriented then ofPauliCoeffs (w • f) ⟨c, h⟩ else 0) =
      w • (if h : c.IsPositivelyOriented then ofPauliCoeffs f ⟨c, h⟩ else (0 : ComplexMatrix2)) := by
    intro c
    split_ifs
    · simp [ofPauliCoeffs, Finset.smul_sum, smul_smul]
    · simp
  rw [Pi.smul_apply, edgeForm_eq, edgeForm_eq]
  simp only [FullSpace.extendOddly, h]
  split_ifs
  · rfl
  · simp
  · simp
end Edges
section OneStep
variable {L k j : ℕ}
private structure CubeFacts (L k j : ℕ) : Prop where
  image_add : ∀ y v : FullSpace.Vertex L k (j + 1),
    FullSpace.cubeOfOrder L (meshAt L k j) 1 (y + v) =
      FullSpace.spaceTranslation (v : AmbientSpace) '' FullSpace.cubeOfOrder L (meshAt L k j) 1 y
  path_eq : ∀ (c : FullSpace.Edge L k (j + 1)) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k (j + 1)) μ →
      ∀ x : FullSpace.Vertex L k j,
        (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 c.initial →
          FullSpace.crossingPath c x = (List.range (L ^ 1)).map fun i =>
            InfiniteLattice.Link.forwardFrom
              (x + i • InfiniteLattice.axisStep (meshAt L k j) μ) μ
  path_mem : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ x : FullSpace.Vertex L k j,
      (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 c.initial →
        ∀ w : FullSpace.Vertex L k j,
          (w = x ∨ w = FullSpace.shifted c x ∨
              ∃ b ∈ FullSpace.crossingPath c x, w = b.initial ∨ w = b.terminal) →
            (w : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 c.initial ∪
              FullSpace.cubeOfOrder L (meshAt L k j) 1 c.terminal
  near : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ x ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 c.initial ∪
        FullSpace.cubeOfOrder L (meshAt L k j) 1 c.terminal,
      ∃ ν : Fin 4 → ℤ, x = FullSpace.offsetPoint (meshAt L k j) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k j| < 3 / 2 * meshAt L k (j + 1)
private theorem cubeFacts (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j < k) :
    CubeFacts L k j := by
  obtain ⟨-, h₁, -, h₃, -, h₅, -⟩ := hZ L hL k 1 (j + 1) hk (by omega) (by omega)
  exact ⟨h₁.image_add, h₃.crossingPath_eq, h₃.crossingPath_vertex_mem, h₅.sites_near⟩
private theorem forwardFrom_isPositive {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
private theorem crossingSmoothing_mem (S : AddSubmonoid ComplexMatrix2)
    (hw : ∀ X ∈ S, PeriodicLattice.inverseFourthPowerWeight L • X ∈ S)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : ∀ b, B b ∈ S)
    (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L B c ∈ S := by apply _root_.YangMills.SharedProofs.p19945 <;> assumption
private theorem crossingSmoothing_mem_traceless (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : ColourEdge L k j → ℂ) (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (edgeForm f) c ∈
      ComplexMatrix2.traceless :=
  crossingSmoothing_mem (L := L) (k := k) (j := j)
    ComplexMatrix2.traceless.toAddSubgroup.toAddSubmonoid
    (fun X hX => ComplexMatrix2.traceless.smul_mem _ hX) (fun b => edgeForm_mem_traceless hL f b) c
private theorem edgeFormPathSum_add {a : ℝ} (B B' : InfiniteLattice.Link a → ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    FullSpace.edgeFormPathSum (B + B') Γ =
      FullSpace.edgeFormPathSum B Γ + FullSpace.edgeFormPathSum B' Γ := by apply _root_.YangMills.Construction.Tower.FullSpace.IterBounds.sumAlong_add <;> assumption
private theorem edgeFormPathSum_smul {a : ℝ} (w : ℂ) (B : InfiniteLattice.Link a → ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    FullSpace.edgeFormPathSum (w • B) Γ = w • FullSpace.edgeFormPathSum B Γ := by
  induction Γ with
  | nil => simp [FullSpace.edgeFormPathSum, FullSpace.sumAlong]
  | cons b l ih =>
    simp only [FullSpace.edgeFormPathSum, FullSpace.sumAlong, List.map_cons, List.sum_cons,
      Pi.smul_apply] at ih ⊢
    rw [ih, smul_add]
private theorem crossingSmoothing_add (hfin : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cubeVertices L (meshAt L k j) y).Finite)
    (B B' : FullSpace.Edge L k j → ComplexMatrix2) :
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (B + B') =
      FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L B +
        FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L B' := by
  funext c
  simp only [FullSpace.crossingSmoothing, Pi.add_apply, edgeFormPathSum_add]
  rw [finsum_mem_add_distrib (hfin c.initial), smul_add]
private theorem crossingSmoothing_smul (hfin : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cubeVertices L (meshAt L k j) y).Finite) (w : ℂ)
    (B : FullSpace.Edge L k j → ComplexMatrix2) :
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (w • B) =
      w • FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L B := by
  funext c
  simp only [FullSpace.crossingSmoothing, Pi.smul_apply, edgeFormPathSum_smul]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin c.initial),
    finsum_mem_eq_finite_toFinset_sum _ (hfin c.initial), ← Finset.smul_sum, smul_comm]
private def coeffStep (L k j : ℕ) (f : ColourEdge L k j → ℂ) : ColourEdge L k (j + 1) → ℂ :=
  fun i => pauliCoeff i.1
    ((((L : ℝ)⁻¹ : ℝ) : ℂ) •
      FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (edgeForm f) i.2.1)
private theorem coeffStep_add (hfin : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cubeVertices L (meshAt L k j) y).Finite)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (f g : ColourEdge L k j → ℂ) :
    coeffStep L k j (f + g) = coeffStep L k j f + coeffStep L k j g := by
  funext i
  have hf := crossingSmoothing_mem_traceless hL f i.2.1
  have hg := crossingSmoothing_mem_traceless hL g i.2.1
  simp only [coeffStep, Pi.add_apply]
  rw [edgeForm_add, crossingSmoothing_add hfin, Pi.add_apply,
    pauliCoeff_smul (ComplexMatrix2.traceless.add_mem hf hg),
    pauliCoeff_add hf hg, pauliCoeff_smul hf, pauliCoeff_smul hg]
  ring
private theorem coeffStep_smul (hfin : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cubeVertices L (meshAt L k j) y).Finite)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (w : ℂ) (f : ColourEdge L k j → ℂ) :
    coeffStep L k j (w • f) = w • coeffStep L k j f := by
  funext i
  have hf := crossingSmoothing_mem_traceless hL f i.2.1
  simp only [coeffStep, Pi.smul_apply, smul_eq_mul]
  rw [edgeForm_smul, crossingSmoothing_smul hfin, Pi.smul_apply,
    pauliCoeff_smul (ComplexMatrix2.traceless.smul_mem w hf),
    pauliCoeff_smul hf, pauliCoeff_smul hf]
  ring
private theorem coeffStep_eq_zero_of_far (F : CubeFacts L k j)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (f : ColourEdge L k j → ℂ)
    (ι' : ColourEdge L k (j + 1))
    (h : ∀ ι, euclidNormVec ((colourEdges L k (j + 1)).pos ι' -
      (colourEdges L k j).pos ι) ≤ 3 → f ι = 0) : coeffStep L k j f ι' = 0 := by
  obtain ⟨a, c⟩ := ι'
  have e : FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (edgeForm f) c.1 = 0 := by
    have e1 : ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.1.initial,
        FullSpace.edgeFormPathSum (edgeForm f) (FullSpace.crossingPath c.1 x) = 0 := by
      refine (finsum_mem_congr (g := fun _ => (0 : ComplexMatrix2)) rfl fun x hx => ?_).trans
        (finsum_mem_zero _)
      obtain ⟨μ, hμ⟩ := c.2
      show ((FullSpace.crossingPath c.1 x).map (edgeForm f)).sum = 0
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      have hp : b.IsPositivelyOriented := by
        have hb' := hb
        rw [F.path_eq c.1 μ hμ x hx] at hb'
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb'
        exact forwardFrom_isPositive _ _
      have hw := F.path_mem c.1 c.2 x hx b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))
      obtain ⟨ν, hν, hbd⟩ := F.near c.1 c.2 _ hw
      have hn : euclidNormVec ((c.1.initial : AmbientSpace) - (b.initial : AmbientSpace)) ≤ 3 := by
        rw [hν]
        refine euclidNormVec_sub_offsetPoint_le (B := 3 / 2 * meshAt L k (j + 1)) ?_ hbd
        have := meshAt_le_one (L := L) (k := k) (j := j + 1) hL hj
        linarith
      have hzero : ∀ a', f (a', ⟨b, hp⟩) = 0 := fun a' => h (a', ⟨b, hp⟩) hn
      rw [edgeForm_of_isPositive f hp]
      simp [ofPauliCoeffs, hzero]
    show PeriodicLattice.inverseFourthPowerWeight L • _ = _
    rw [e1, smul_zero]
  simp only [coeffStep]
  rw [e, smul_zero]
  exact pauliCoeff_zero a
private structure ShiftFacts (L k j : ℕ) (n : Fin 4 → ℤ) : Prop where
  coe_vertexImage : ∀ x : FullSpace.Vertex L k j,
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) + castVec n
private theorem shiftFacts (hG : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j ≤ k) (n : Fin 4 → ℤ) :
    ShiftFacts L k j n :=
  ⟨fun x => ((hG L hL k j hk hj n).2.1 x).1⟩
section OneShift
variable {n : Fin 4 → ℤ}
private theorem ShiftFacts.vertexImage_add (h : ShiftFacts L k j n) (x y : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) (x + y) : FullSpace.Vertex L k j) =
      FullSpace.vertexImage (intShift n) x + y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, h.coe_vertexImage]
  abel
private theorem ShiftFacts.vertexImage_sub (h : ShiftFacts L k j n) (x y : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) x - FullSpace.vertexImage (intShift n) y :
      FullSpace.Vertex L k j) = x - y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, h.coe_vertexImage]
  abel
private theorem ShiftFacts.edgeImage_ends (h : ShiftFacts L k j n) (b : FullSpace.Edge L k j) :
    (FullSpace.edgeImage (intShift n) b).initial = FullSpace.vertexImage (intShift n) b.initial ∧
      (FullSpace.edgeImage (intShift n) b).terminal =
        FullSpace.vertexImage (intShift n) b.terminal := by
  refine Classical.epsilon_spec
    (p := fun b' : FullSpace.Edge L k j =>
      b'.initial = FullSpace.vertexImage (intShift n) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift n) b.initial, FullSpace.vertexImage (intShift n) b.terminal,
      ?_⟩, rfl, rfl⟩
  rw [h.vertexImage_sub]
  exact b.isAdjacent
private theorem ShiftFacts.edgeImage_sub (h : ShiftFacts L k j n) (b : FullSpace.Edge L k j) :
    (FullSpace.edgeImage (intShift n) b).terminal - (FullSpace.edgeImage (intShift n) b).initial =
      b.terminal - b.initial := by
  rw [(h.edgeImage_ends b).1, (h.edgeImage_ends b).2, h.vertexImage_sub]
private theorem ShiftFacts.edgeImage_isPositive (h : ShiftFacts L k j n) {b : FullSpace.Edge L k j}
    (hb : b.IsPositivelyOriented) : (FullSpace.edgeImage (intShift n) b).IsPositivelyOriented := by
  obtain ⟨μ, e⟩ := hb
  exact ⟨μ, (h.edgeImage_sub b).trans e⟩
private theorem ShiftFacts.edgeImage_forwardFrom (h : ShiftFacts L k j n)
    (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) x) μ := by
  refine InfiniteLattice.Link.ext (h.edgeImage_ends _).1 ?_
  rw [(h.edgeImage_ends _).2]
  exact h.vertexImage_add x _
private theorem ShiftFacts.shiftEdge_coe (h : ShiftFacts L k j n) (b : PosEdge L k j) :
    (shiftEdge n b).1 = FullSpace.edgeImage (intShift n) b.1 :=
  Classical.epsilon_spec (p := fun b' : PosEdge L k j =>
    b'.1 = FullSpace.edgeImage (intShift n) b.1) ⟨⟨_, h.edgeImage_isPositive b.2⟩, rfl⟩
end OneShift
private theorem vertexImage_neg_vertexImage {n₀ : Fin 4 → ℤ} (h : ShiftFacts L k j n₀)
    (h' : ShiftFacts L k j (-n₀)) (x : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift (-n₀)) (FullSpace.vertexImage (intShift n₀) x) :
      FullSpace.Vertex L k j) = x := by
  apply Subtype.ext
  rw [h'.coe_vertexImage, h.coe_vertexImage]
  funext μ
  simp [castVec]
private theorem vertexImage_vertexImage_neg {j : ℕ} {n : Fin 4 → ℤ} (h : ShiftFacts L k j n)
    (h' : ShiftFacts L k j (-n)) (x : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift n) (FullSpace.vertexImage (intShift (-n)) x) :
      FullSpace.Vertex L k j) = x := by
  apply Subtype.ext
  rw [h.coe_vertexImage, h'.coe_vertexImage]
  funext μ
  simp [castVec]
private theorem bijOn_of_mapsTo_of_inverse {α : Type} {e e' : α → α} {s t : Set α}
    (he : MapsTo e s t) (he' : MapsTo e' t s) (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ x, e (e' x) = x) :
    BijOn e s t :=
  ⟨he, (Function.LeftInverse.injective h₁).injOn, fun y hy => ⟨e' y, he' hy, h₂ y⟩⟩
private theorem vertexImage_mem_cubeOfOrder (F : CubeFacts L k j) {n : Fin 4 → ℤ}
    (h₀ : ShiftFacts L k j n) (h₁ : ShiftFacts L k (j + 1) n) {y : FullSpace.Vertex L k (j + 1)}
    {x : FullSpace.Vertex L k j}
    (hx : (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 y) :
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : AmbientSpace) ∈
      FullSpace.cubeOfOrder L (meshAt L k j) 1
        (FullSpace.vertexImage (intShift n) y : FullSpace.Vertex L k (j + 1)) := by
  have e : (FullSpace.vertexImage (intShift n) y : FullSpace.Vertex L k (j + 1)) =
      y + FullSpace.vertexImage (intShift n) 0 := by
    rw [add_comm y, ← h₁.vertexImage_add, zero_add]
  rw [e, F.image_add]
  refine ⟨x, hx, ?_⟩
  show (x : AmbientSpace) +
    ((FullSpace.vertexImage (intShift n) 0 : FullSpace.Vertex L k (j + 1)) : AmbientSpace) = _
  rw [h₁.coe_vertexImage, h₀.coe_vertexImage]
  simp
private theorem edgeForm_translate {n : Fin 4 → ℤ} (h₀ : ShiftFacts L k j n)
    (f : ColourEdge L k j → ℂ) {b : FullSpace.Edge L k j} (hp : b.IsPositivelyOriented) :
    edgeForm (fun ι => f ((colourEdges L k j).translate n ι)) b =
      edgeForm f (FullSpace.edgeImage (intShift n) b) := by
  have e : shiftEdge n (⟨b, hp⟩ : PosEdge L k j) =
      ⟨FullSpace.edgeImage (intShift n) b, h₀.edgeImage_isPositive hp⟩ :=
    Subtype.ext (h₀.shiftEdge_coe _)
  rw [edgeForm_of_isPositive _ hp, edgeForm_of_isPositive f (h₀.edgeImage_isPositive hp)]
  simp only [ofPauliCoeffs]
  refine Finset.sum_congr rfl fun a _ => ?_
  show f (a, shiftEdge n ⟨b, hp⟩) • _ = _
  rw [e]
private theorem coeffStep_translate (F : CubeFacts L k j) {n : Fin 4 → ℤ}
    (h₀ : ShiftFacts L k j n) (h₀' : ShiftFacts L k j (-n)) (h₁ : ShiftFacts L k (j + 1) n)
    (h₁' : ShiftFacts L k (j + 1) (-n)) (f : ColourEdge L k j → ℂ)
    (ι' : ColourEdge L k (j + 1)) :
    coeffStep L k j f ((colourEdges L k (j + 1)).translate n ι') =
      coeffStep L k j (fun ι => f ((colourEdges L k j).translate n ι)) ι' := by
  obtain ⟨a, c⟩ := ι'
  show pauliCoeff a (_ • FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L (edgeForm f)
      (shiftEdge n c).1) = pauliCoeff a (_ • FullSpace.crossingSmoothing
        (a := meshAt L k (j + 1)) L
          (edgeForm fun ι => f ((colourEdges L k j).translate n ι)) c.1)
  rw [h₁.shiftEdge_coe]
  obtain ⟨μ, hμ⟩ := c.2
  have hmove : ∀ {x : FullSpace.Vertex L k j}, (x : AmbientSpace) ∈
      FullSpace.cubeOfOrder L (meshAt L k j) 1 c.1.initial →
      (FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) ∈
        FullSpace.cubeVertices L (meshAt L k j) (FullSpace.edgeImage (intShift n) c.1).initial := by
    intro x hx
    show ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : AmbientSpace) ∈
      FullSpace.cubeOfOrder L (meshAt L k j) 1 (FullSpace.edgeImage (intShift n) c.1).initial
    rw [(h₁.edgeImage_ends c.1).1]
    exact vertexImage_mem_cubeOfOrder F h₀ h₁ hx
  have hb : BijOn (fun x : FullSpace.Vertex L k j => FullSpace.vertexImage (intShift n) x)
      (FullSpace.cubeVertices L (meshAt L k j) c.1.initial)
      (FullSpace.cubeVertices L (meshAt L k j) (FullSpace.edgeImage (intShift n) c.1).initial) := by
    refine bijOn_of_mapsTo_of_inverse (e' := fun x => FullSpace.vertexImage (intShift (-n)) x)
      (fun x hx => hmove hx) (fun x hx => ?_)
      (fun x => vertexImage_neg_vertexImage h₀ h₀' x)
      (fun x => vertexImage_vertexImage_neg h₀ h₀' x)
    have hx' : (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1
        (FullSpace.vertexImage (intShift n) c.1.initial : FullSpace.Vertex L k (j + 1)) := by
      have := hx
      rw [show FullSpace.cubeVertices L (meshAt L k j)
          (FullSpace.edgeImage (intShift n) c.1).initial = _ from rfl,
        (h₁.edgeImage_ends c.1).1] at this
      exact this
    have h2 := vertexImage_mem_cubeOfOrder F h₀' h₁' hx'
    rw [vertexImage_neg_vertexImage h₁ h₁'] at h2
    exact h2
  have hv : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.1.initial,
      FullSpace.edgeFormPathSum (edgeForm fun ι => f ((colourEdges L k j).translate n ι))
          (FullSpace.crossingPath c.1 x) =
        FullSpace.edgeFormPathSum (edgeForm f)
          (FullSpace.crossingPath (FullSpace.edgeImage (intShift n) c.1)
            (FullSpace.vertexImage (intShift n) x)) := by
    intro x hx
    rw [F.path_eq c.1 μ hμ x hx,
      F.path_eq _ μ ((h₁.edgeImage_sub c.1).trans hμ) _ (hmove hx)]
    show (List.map _ (List.map _ _)).sum = (List.map _ (List.map _ _)).sum
    congr 1
    simp only [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    rw [edgeForm_translate h₀ f (forwardFrom_isPositive _ _), h₀.edgeImage_forwardFrom,
      h₀.vertexImage_add]
  have e := finsum_mem_eq_of_bijOn _ hb (g := fun x =>
    FullSpace.edgeFormPathSum (edgeForm f)
      (FullSpace.crossingPath (FullSpace.edgeImage (intShift n) c.1) x)) hv
  show pauliCoeff a (_ • PeriodicLattice.inverseFourthPowerWeight L • _) =
    pauliCoeff a (_ • PeriodicLattice.inverseFourthPowerWeight L • _)
  rw [e]
end OneStep
section Kernels
variable {I I' : PeriodicData}
private theorem kernelTranspose_isShiftInvariant (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hc : IsShiftInvariant I I' T) :
    IsShiftInvariant I' I (kernelTranspose I I' T) := by apply _root_.YangMills.Construction.PeriodicOperators.TransposeProof.isShiftInvariant_kernelTranspose <;> assumption
private theorem kernelTranspose_vanishes {T : I'.Carrier → I.Carrier → ℂ} {ϱ : ℝ}
    (hv : VanishesOutsideRadius I I' ϱ T) : VanishesOutsideRadius I' I ϱ (kernelTranspose I I' T) :=
  fun ι ι' h => by
    rw [euclidNormVec_sub_comm] at h
    simp only [kernelTranspose, PeriodicOperators.wTranspose, hv ι' ι h, mul_zero]
private theorem translate_injective (hI : IsPeriodic I) (n : Fin 4 → ℤ) :
    Function.Injective (I.translate n) := by
  intro a b e
  have e' := congrArg (I.translate (-n)) e
  rwa [← hI.translate_add, ← hI.translate_add, add_neg_cancel, hI.translate_zero,
    hI.translate_zero] at e'
end Kernels
theorem finiteRange_of_freeAndCovariant (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hCov : CovariantFiniteRange.Claim)
    (hMean : MeanMapsAtTrivialField) (hIdx : TowerIndexSets.Claim)
    (hG : TowerTranslations.Claim)
    (hZ : BlockPathContourPivotStatement)
    (hObj : SelectedObjects.Statement) :
    MeanStepAtTrivialFieldFiniteRange := by
  classical
  intro L hL k hk j hj
  have hI := (hIdx L hL k j hj.le).2.1
  have hI' := (hIdx L hL k (j + 1) hj).2.1
  have F := cubeFacts hZ hL hk hj
  have hfin : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cubeVertices L (meshAt L k j) y).Finite :=
    ((hObj L hL).2 k (j + 1) (by omega) hj).cubeVertices_finite
  have hM : (FullSpace.edgePauliCoordinates L k j).mapOnCoeffs (FullSpace.edgePauliCoordinates L k (j + 1))
      (fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate (fun _ => 1) j) B) =
        coeffStep L k j := by
    funext (f : ColourEdge L k j → ℂ) (i' : ColourEdge L k (j + 1))
    have hs := (hMean L hL k hk).2.2.1 j hj (edgeForm f) (edgeForm_mem hL f)
    have hi := (hMean L hL k hk).1 j hj.le
    show pauliCoeff i'.1 ((L : ℝ)⁻¹ • meanCovariantStep
      (meanIterate (fun _ => 1) j) (edgeForm f) i'.2.1) = _
    rw [hi, hs, ← Complex.coe_smul]
    rfl
  have hR := represents_of_local (coeffStep_add hfin hL) (coeffStep_smul hfin hL)
    (R := fun ι' => nearIndices (colourEdges L k j) ((colourEdges L k (j + 1)).pos ι') 3)
    (fun ι' => (hCov.1 _ hI).1 _ 3)
    (fun f ι' h => coeffStep_eq_zero_of_far F hL hj f ι' fun ι hι => h ι (by
      show euclidNormVec _ ≤ 3
      rwa [euclidNormVec_sub_comm]))
  have hRep : Represents (meanStepKernel L k (fun _ => 1) j) (coeffStep L k j) := by
    have e : meanStepKernel L k (fun _ => 1) j = kernelOfMap (coeffStep L k j) :=
      congrArg kernelOfMap hM
    rw [e]
    exact represents_kernelOfMap hR
  have hc : IsShiftInvariant (colourEdges L k j) (colourEdges L k (j + 1))
      (meanStepKernel L k (fun _ => 1) j) := fun n ι' ι => by
    refine ((kernel_eq_apply_basisFun hRep _ _).trans
      ((coeffStep_translate F (shiftFacts hG hL hk hj.le n)
        (shiftFacts hG hL hk hj.le (-n)) (shiftFacts hG hL hk hj n)
          (shiftFacts hG hL hk hj (-n)) _ ι').trans ?_)).trans
        (kernel_eq_apply_basisFun hRep ι' ι).symm
    refine congrArg (fun g => coeffStep L k j g ι') (funext fun x => ?_)
    have hiff : (colourEdges L k j).translate n x = (colourEdges L k j).translate n ι ↔ x = ι :=
      (translate_injective hI n).eq_iff
    simp only [basisFun]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  have hv : VanishesOutsideRadius (colourEdges L k j) (colourEdges L k (j + 1)) 3
      (meanStepKernel L k (fun _ => 1) j) := fun ι' ι h => by
    refine (kernel_eq_apply_basisFun hRep ι' ι).trans
      (coeffStep_eq_zero_of_far F hL hj _ ι' fun x hx => ?_)
    have : x ≠ ι := fun e => h (e ▸ hx)
    exact if_neg this
  refine ⟨(hFree.1 _ _ hI hI').1 3 _ (by norm_num) hc hv,
    (hFree.1 _ _ hI' hI).1 3 _ (by norm_num) (kernelTranspose_isShiftInvariant hI hI' hc)
      (kernelTranspose_vanishes hv), fun ι' ι => ?_⟩
  refine (congrArg Complex.im (kernel_eq_apply_basisFun hRep ι' ι)).trans ?_
  show (pauliCoeff ι'.1 _).im = 0
  refine pauliCoeff_im ?_ _
  have hw : ∀ X ∈ ComplexMatrix2.hermitianTraceless.toAddSubmonoid,
      PeriodicLattice.inverseFourthPowerWeight L • X ∈
        ComplexMatrix2.hermitianTraceless.toAddSubmonoid := fun X hX => by
    rw [PeriodicLattice.inverseFourthPowerWeight, Complex.coe_smul]
    exact ComplexMatrix2.hermitianTraceless.smul_mem _ hX
  rw [Complex.coe_smul]
  refine ComplexMatrix2.hermitianTraceless.smul_mem _
    (crossingSmoothing_mem (L := L) (k := k) (j := j)
      ComplexMatrix2.hermitianTraceless.toAddSubmonoid hw (fun b => ?_) _)
  refine edgeForm_mem_hermitianTraceless hL (fun q => ?_) b
  simp only [basisFun]
  split_ifs <;> simp
end FullLattice.FlatMeanStep
theorem meanStepAtTrivialFieldFiniteRange_holds
    (hFree : Tower.FreeOperators.FreeOperatorsArePeriodic)
    (hCov : PeriodicOperators.CovariantFiniteRange.Claim)
    (hMean : MeanMapsAtTrivialField)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hG : PeriodicOperators.TowerTranslations.Claim)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hObj : Tower.SelectedObjects.Statement) :
    MeanStepAtTrivialFieldFiniteRange := by apply _root_.YangMills.Construction.RunningCouplingSlope.FullLattice.FlatMeanStep.finiteRange_of_freeAndCovariant <;> assumption
end YangMills.Construction.RunningCouplingSlope
end
