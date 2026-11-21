import YangMills.Construction.Towers.IteratedAveragesAreHolomorphicOnASide
import YangMills.Construction.Towers.ScaledKernelsAreHolomorphicInTheFormAtTheSideInfinityProof
import YangMills.Construction.Towers.ScaledKernelsOfIteratedAveragesAreHolomorphicOnASide
import YangMills.Construction.Towers.StepKernelsAreHolomorphicOnASide
import YangMills.Construction.Towers.StepKernelsOfTheCovariantAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.RescaledKernelsHolomorphy
open Matrices
open PeriodicOperators
open StepKernels (IsBoundedTracelessEndo stepKernel positiveDoubleBlockEdges)
open StepKernelHolomorphy (smoothingDerivCoeff conjugationCoeff)
open DoubleBlockPolydisc (leftComponents)
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem combination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (z : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (z • X) = z * pauliCoeff a X := by
  have e : z • X = ∑ b, (z * pauliCoeff b X) • ComplexMatrix2.pauliFamily b := by
    simp only [mul_smul]
    rw [← Finset.smul_sum, combination_pauliCoeff hX]
  conv_lhs => rw [e]
  exact pauliCoeff_combination (fun b => z * pauliCoeff b X) a
theorem pauliCoeff_sum {α : Type} (u : Finset α) (g : α → ComplexMatrix2)
    (h : ∀ i ∈ u, g i ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (∑ i ∈ u, g i) = ∑ i ∈ u, pauliCoeff a (g i) := by apply _root_.YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels.pauliCoeff_sum <;> assumption
theorem pauliCoeff_endo_apply {T : ComplexMatrix2 → ComplexMatrix2} {C : ℝ}
    (hT : IsBoundedTracelessEndo T C) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) :
    pauliCoeff a (T X) =
      ∑ s, pauliCoeff s X * pauliCoeff a (T (ComplexMatrix2.pauliFamily s)) := by
  have hp := pauliFamily_mem_traceless
  have hm : ∀ (z : ℂ) (s : Fin 3), z • ComplexMatrix2.pauliFamily s ∈ ComplexMatrix2.traceless :=
    fun z s => Submodule.smul_mem _ _ (hp s)
  have hT' : ∀ s, T (ComplexMatrix2.pauliFamily s) ∈ ComplexMatrix2.traceless :=
    fun s => hT.mapsTo _ (hp s)
  have hm' : ∀ (z : ℂ) (s : Fin 3),
      z • T (ComplexMatrix2.pauliFamily s) ∈ ComplexMatrix2.traceless :=
    fun z s => Submodule.smul_mem _ _ (hT' s)
  have e : T X = pauliCoeff 0 X • T (ComplexMatrix2.pauliFamily 0) +
      pauliCoeff 1 X • T (ComplexMatrix2.pauliFamily 1) +
      pauliCoeff 2 X • T (ComplexMatrix2.pauliFamily 2) := by
    conv_lhs => rw [← combination_pauliCoeff hX, Fin.sum_univ_three]
    rw [hT.map_add _ (Submodule.add_mem _ (hm _ _) (hm _ _)) _ (hm _ _),
      hT.map_add _ (hm _ _) _ (hm _ _), hT.map_smul _ _ (hp _), hT.map_smul _ _ (hp _),
      hT.map_smul _ _ (hp _)]
  rw [e, pauliCoeff_add (Submodule.add_mem _ (hm' _ _) (hm' _ _)) (hm' _ _),
    pauliCoeff_add (hm' _ _) (hm' _ _), pauliCoeff_smul _ (hT' _), pauliCoeff_smul _ (hT' _),
    pauliCoeff_smul _ (hT' _), Fin.sum_univ_three]
end Coefficients
section Kernels
variable {N N' : Type}
theorem applyKernel_single [DecidableEq N] (T : KernelMatrix N N') (i : N) (i' : N') :
    applyKernel T (Pi.single i 1) i' = T i' i := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_single <;> assumption
theorem entry_eq_of_represents [DecidableEq N] {T : KernelMatrix N N'}
    {M : (N → ℂ) → N' → ℂ} (h : Represents T M) (i : N) (i' : N') :
    T i' i = M (Pi.single i 1) i' := by
  rw [← applyKernel_single T i i', (h _).2]
theorem kernelOfMap_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : Represents (kernelOfMap M) M :=
  Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, h⟩
end Kernels
section Generic
variable {σ : Type} [Fintype σ]
theorem operatorNorm_le_supNorm (A : σ → ComplexMatrix2) (i : σ) :
    ComplexMatrix2.operatorNorm (A i) ≤ GroupLieProduct.supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem supNorm_lt_iff {ρ : ℝ} (hρ : 0 < ρ) (A : σ → ComplexMatrix2) :
    GroupLieProduct.supNorm A < ρ ↔ ∀ i, ComplexMatrix2.operatorNorm (A i) < ρ := by apply _root_.YangMills.SharedProofs.p9363 <;> assumption
theorem isOpen_supNorm_lt {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen {A : σ → ComplexMatrix2 | GroupLieProduct.supNorm A < ρ} := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isOpen_supNorm_lt <;> assumption
theorem isSupOpen_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    GroupLieProduct.IsSupOpen (GroupLieProduct.supBall σ ρ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isSupOpen_supBall <;> assumption
theorem isOpen_val_preimage_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen ((Subtype.val : GroupLieProduct.tracelessPiSubmodule σ → σ → ComplexMatrix2) ⁻¹'
      GroupLieProduct.supBall σ ρ) := by
  have e : (Subtype.val : GroupLieProduct.tracelessPiSubmodule σ → σ → ComplexMatrix2) ⁻¹'
      GroupLieProduct.supBall σ ρ =
      (Subtype.val : GroupLieProduct.tracelessPiSubmodule σ → σ → ComplexMatrix2) ⁻¹'
        {A | GroupLieProduct.supNorm A < ρ} := by
    ext A
    exact ⟨fun h => h.2, fun h => ⟨fun i => A.2 i (mem_univ i), h⟩⟩
  rw [e]
  exact (isOpen_supNorm_lt hρ).preimage continuous_subtype_val
end Generic
section Analytic
variable {ι κ : Type} [Fintype ι] [Fintype κ]
def scalarMatrixCoords : Coordinates.ComplexCoordinates 1 →L[ℂ] Coordinates.ComplexCoordinates 4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Coordinates.ComplexCoordinates.matrixEquiv (z 0 • (1 : ComplexMatrix2))
      map_add' := fun z w => by
        simp only [Pi.add_apply, add_smul]
        rfl
      map_smul' := fun c z => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        rfl }
theorem isHolomorphicToCoords_smul_one {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → ℂ}
    (h : GroupLieProduct.IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W Φ) :
    GroupLieProduct.IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W
      fun p => Φ p • (1 : ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels.isHolomorphicToCoords_smul_one <;> assumption
theorem exists_analyticAt_of_isHolomorphicToCoords
    (hAn : GroupLieProduct.HolomorphicMatrixAnalyticity)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ℂ}
    (h : GroupLieProduct.IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W Φ)
    {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ W) :
    ∃ H : (ι ⊕ κ → ComplexMatrix2) → ℂ, AnalyticAt ℂ H p ∧ ∀ᶠ w in 𝓝 p, w ∈ W → Φ w = H w := by
  obtain ⟨G, hG, hev⟩ := hAn ι κ b W _ (Or.inl (isHolomorphicToCoords_smul_one h)) p hp
  let e : ComplexMatrix2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ 0 0)
  refine ⟨fun w => e (G w), (ContinuousLinearMap.analyticAt _ _).comp hG, ?_⟩
  filter_upwards [hev] with w hw hW
  have := hw hW
  show Φ w = G w 0 0
  rw [← this]
  simp
theorem differentiableOn_comp_of_isHolomorphic
    (hAn : GroupLieProduct.HolomorphicMatrixAnalyticity)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {D : Set P} (hD : IsOpen D)
    {τ : Type} [Fintype τ] {W : Set (τ → ComplexMatrix2)} {φ : (τ → ComplexMatrix2) → ℂ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (hφ : GroupLieProduct.IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm
      (leftComponents ⁻¹' W) (φ ∘ leftComponents))
    {v : P → τ → ComplexMatrix2} (hv : ∀ i, DifferentiableOn ℂ (fun A => v A i) D)
    (hW : MapsTo v D W) :
    DifferentiableOn ℂ (fun A => φ (v A)) D := by
  intro A₀ hA₀
  let point : P → τ ⊕ Empty → ComplexMatrix2 := fun A => Sum.elim (v A) fun e => e.elim
  have hdp : DifferentiableAt ℂ point A₀ := by
    refine differentiableAt_pi.2 ?_
    rintro (i | e)
    · exact (hv i).differentiableAt (hD.mem_nhds hA₀)
    · exact e.elim
  have hp : point A₀ ∈ leftComponents ⁻¹' W := hW hA₀
  obtain ⟨H, hH, hev⟩ := exists_analyticAt_of_isHolomorphicToCoords hAn hφ hp
  have hc : DifferentiableAt ℂ (fun A => H (point A)) A₀ :=
    hH.differentiableAt.comp A₀ hdp
  have htend := hdp.continuousAt.tendsto.eventually hev
  have hcongr : (fun A => φ (v A)) =ᶠ[𝓝 A₀] fun A => H (point A) := by
    filter_upwards [htend, hD.mem_nhds hA₀] with A h₁ h₂
    exact h₁ (hW h₂)
  exact (hc.congr_of_eventuallyEq hcongr).differentiableWithinAt
end Analytic
section Levels
variable {L n k : ℕ} {F : Finset (Edge L n k 0)}
def antisymmetrizedForm (hF : ∀ b, b ∈ F) (A : F → ComplexMatrix2) :
    Edge L n k 0 → ComplexMatrix2 :=
  fun b => (1 / 2 : ℂ) • (A ⟨b, hF b⟩ - A ⟨b.opposite, hF _⟩)
def fieldAt (hF : ∀ b, b ∈ F) (A : F → ComplexMatrix2) : Edge L n k 0 → ComplexMatrix2 :=
  remainderGaugeField (antisymmetrizedForm hF A)
def levelIterate (hF : ∀ b, b ∈ F) (j : ℕ) (A : F → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.complexBlockFieldAtLevel j (fieldAt hF A)
theorem antisymmetrizedForm_of_form (hF : ∀ b, b ∈ F) {a : Edge L n k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) : antisymmetrizedForm hF (fun b => a b) = a := by
  funext b
  have h : a b.opposite = -a b := ha.2 b
  simp only [antisymmetrizedForm, h, sub_neg_eq_add]
  rw [← two_smul ℂ (a b), smul_smul]
  norm_num
theorem antisymmetrizedForm_mem (hF : ∀ b, b ∈ F) {ρ : ℝ} {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) :
    antisymmetrizedForm hF A ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hA.1 _) (hA.1 _))
  · simp only [antisymmetrizedForm, PeriodicLattice.Bond.opposite_opposite]
    rw [← smul_neg, neg_sub]
theorem operatorNorm_antisymmetrizedForm_le (hF : ∀ b, b ∈ F) (A : F → ComplexMatrix2)
    (b : Edge L n k 0) :
    ComplexMatrix2.operatorNorm (antisymmetrizedForm hF A b) ≤ GroupLieProduct.supNorm A := by
  have h₁ := operatorNorm_le_supNorm A ⟨b, hF b⟩
  have h₂ := operatorNorm_le_supNorm A ⟨b.opposite, hF _⟩
  have h₃ := norm_sub_le (A ⟨b, hF b⟩) (A ⟨b.opposite, hF _⟩)
  simp only [ComplexMatrix2.operatorNorm, antisymmetrizedForm, norm_smul] at h₁ h₂ ⊢
  norm_num
  linarith
theorem maxOperatorNorm_antisymmetrizedForm_lt (hF : ∀ b, b ∈ F) {ρ : ℝ} (hρ : 0 < ρ)
    {A : F → ComplexMatrix2} (hA : A ∈ GroupLieProduct.supBall F ρ) :
    maxOperatorNorm (antisymmetrizedForm hF A) < ENNReal.ofReal ρ := by
  have hle : maxOperatorNorm (antisymmetrizedForm hF A) ≤
      ENNReal.ofReal (GroupLieProduct.supNorm A) :=
    iSup_le fun b => ENNReal.ofReal_le_ofReal (operatorNorm_antisymmetrizedForm_le hF A b)
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2)
def restrictAntisymmetrized (hF : ∀ b, b ∈ F) (F' : Finset (Edge L n k 0)) :
    GroupLieProduct.tracelessPiSubmodule F →ₗ[ℂ] GroupLieProduct.tracelessPiSubmodule F' where
  toFun A := ⟨fun b => antisymmetrizedForm hF A.1 b.1, fun b _ =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (A.2 _ (mem_univ _)) (A.2 _ (mem_univ _)))⟩
  map_add' A A' := by
    ext b : 2
    simp only [antisymmetrizedForm, Submodule.coe_add, Pi.add_apply]
    rw [← smul_add]
    congr 1
    abel
  map_smul' z A := by
    ext b : 2
    simp only [antisymmetrizedForm, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [← smul_sub, smul_comm]
theorem differentiableOn_levelIterate
    (hD : GroupLieProduct.HolomorphicOnTracelessIffDifferentiable)
    (hF : ∀ b, b ∈ F) {ρ : ℝ} (hρ : 0 < ρ) {j : ℕ} {c : Edge L n k j}
    {F' : Finset (Edge L n k 0)} {f' : (F' → ComplexMatrix2) → ComplexMatrix2}
    {e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (hf : GroupLieProduct.IsHolomorphicOnTraceless e Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall F' ρ) f')
    (hv : ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a < ENNReal.ofReal ρ →
      f' (fun b => a b) = PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) c) :
    DifferentiableOn ℂ
      (fun A : GroupLieProduct.tracelessPiSubmodule F => levelIterate hF j A.1 c)
      (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
  have h₁ := ((hD F' ComplexMatrix2 4 e Coordinates.ComplexCoordinates.matrixEquiv
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩ (GroupLieProduct.supBall F' ρ) f').1 hf).2
  let R := LinearMap.toContinuousLinearMap (restrictAntisymmetrized hF F')
  have hmaps : MapsTo R (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ)
      (Subtype.val ⁻¹' GroupLieProduct.supBall F' ρ) := by
    intro A hA
    refine ⟨fun b => (R A).2 b (mem_univ b), (supNorm_lt_iff hρ _).2 fun b => ?_⟩
    exact (operatorNorm_antisymmetrizedForm_le hF A.1 b.1).trans_lt hA.2
  refine (h₁.comp R.differentiableOn hmaps).congr fun A hA => ?_
  exact (hv _ (antisymmetrizedForm_mem hF hA) (maxOperatorNorm_antisymmetrizedForm_lt hF hρ hA)).symm
theorem extendFromPositive_restrictToPositive {j : ℕ} {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b : Edge L n k j, V b.opposite = (V b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ V) b = V b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
structure InductionData (hF : ∀ b, b ∈ F) (ρ : ℝ) : Prop where
  radius_pos : 0 < ρ
  admissible : Conventions.IsAdmissibleBlockingFactor L
  side_pos : 0 < n
  stepBounds : StepKernels.StepKernelBounds
  stepHolomorphy : StepKernelHolomorphy.StepKernelsHolomorphic
  analyticity : GroupLieProduct.HolomorphicMatrixAnalyticity
  edges_finite : ∀ j, Finite (Edge L n k j)
  vertices_finite : ∀ j, Finite (Vertex L n k j)
  extendOddly_opposite : ∀ j ≤ k, ∀ (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j),
    extendOddly f b.opposite = -extendOddly f b
  small : ∀ A ∈ GroupLieProduct.supBall F ρ, ∀ j < k,
    levelIterate hF j A ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
      ∀ b : Edge L n k j,
        ComplexMatrix2.operatorNorm (levelIterate hF j A b - 1) < polydiscRadius L / 2
  iterates : ∀ j ≤ k, ∀ c : Edge L n k j, DifferentiableOn ℂ
    (fun A : GroupLieProduct.tracelessPiSubmodule F => levelIterate hF j A.1 c)
    (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ)
namespace InductionData
variable {hF : ∀ b, b ∈ F} {ρ : ℝ}
theorem iterate_near_one (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k) (b : Edge L n k j) :
    ComplexMatrix2.operatorNorm (levelIterate hF j A b - 1) < 3 / 4 * polydiscRadius L := by
  have h₁ := (S.small A hA j hj).2 b
  have h₂ : 0 ≤ ComplexMatrix2.operatorNorm (levelIterate hF j A b - 1) := norm_nonneg _
  linarith
theorem smoothingDeriv_mem (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv (levelIterate hF j A) B ∈ complexEdgeForms L n k (j + 1) := by
  refine ⟨fun c hc => ?_, fun c => ?_⟩
  · obtain ⟨h₁, h₂, -⟩ := S.stepBounds L S.admissible n k j S.side_pos hj c hc _
      (S.small A hA j hj).1 (S.iterate_near_one hA hj)
    rw [h₁ B hB]
    exact finsum_mem_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
      (fun _ _ => ComplexMatrix2.traceless.add_mem)
      fun b hb => (h₂ b hb).mapsTo _ (hB.1 b hb.2)
  · have hr := S.extendOddly_opposite (j + 1) hj
    simp only [covariantSmoothingDeriv, Pi.add_apply, complexSmoothingDeriv,
      holLeftDifferential, covDiff]
    rw [hr, hr, neg_add]
theorem iterCovariantDeriv_mem (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) (j : ℕ) (hj : j ≤ k) :
    iterCovariantDeriv L n k (fieldAt hF A) j B ∈ complexEdgeForms L n k j := by
  induction j with
  | zero => exact hB
  | succ j ih => exact S.smoothingDeriv_mem hA hj (ih (Nat.le_of_succ_le hj))
theorem forwardFrom_zero_positive {j : ℕ} (y : Vertex L n k j) :
    (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented := ⟨0, add_sub_cancel_left _ _⟩
theorem conjugation_bounded (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    IsBoundedTracelessEndo
      (ComplexMatrix2.conjugateBy
        (PeriodicLattice.complexMeanContourHolonomy (levelIterate hF j A) y x)) 3 :=
  (S.stepBounds L S.admissible n k j S.side_pos hj _ (forwardFrom_zero_positive y) _
    (S.small A hA j hj).1 (S.iterate_near_one hA hj)).2.2 y (Or.inl rfl) x hx
theorem iterAdjointCubeAverage_mem (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (j : ℕ) (hj : j ≤ k) (y : Vertex L n k j) :
    iterAdjointCubeAverage L n k (fieldAt hF A) j l y ∈ ComplexMatrix2.traceless := by
  induction j with
  | zero => exact hl y
  | succ j ih =>
    have hjk : j < k := hj
    refine Submodule.smul_mem _ _ ?_
    exact finsum_mem_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
      (fun _ _ => ComplexMatrix2.traceless.add_mem)
      fun x hx => (S.conjugation_bounded hA hjk y hx).mapsTo _ (ih hjk.le x)
def doubleBlockValues (hF : ∀ b, b ∈ F) {j : ℕ} (c : Edge L n k (j + 1))
    (A : F → ComplexMatrix2) :
    DoubleBlockPolydisc.positiveDoubleBlockBonds c → ComplexMatrix2 :=
  fun b => levelIterate hF j A b.1
theorem levelIterate_mem_polydisc (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1)) :
    levelIterate hF j A ∈ nearIdentityPolydisc (3 / 4 * polydiscRadius L) c := by
  have h₁ : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ
      (levelIterate hF j A) :=
    (S.small A hA j hj).1
  exact ⟨⟨fun b _ => h₁.1 b (mem_univ b), fun b _ => h₁.2 b (mem_univ b)⟩,
    fun b _ => S.iterate_near_one hA hj b⟩
theorem fieldOfValues_spec (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1)) :
    DoubleBlockPolydisc.fieldOfValues c (doubleBlockValues hF c A) ∈
        nearIdentityPolydisc (3 / 4 * polydiscRadius L) c ∧
      EqOn (levelIterate hF j A)
        (DoubleBlockPolydisc.fieldOfValues c (doubleBlockValues hF c A))
        (DoubleBlockPolydisc.doubleBlockBonds c) := by
  have h₁ : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ
      (levelIterate hF j A) :=
    (S.small A hA j hj).1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hag : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      DoubleBlockPolydisc.fieldOfValues c (doubleBlockValues hF c A) b =
        levelIterate hF j A b :=
    fun b hb => extendFromPositive_restrictToPositive hclosed (fun b => h₁.2 b (mem_univ b)) b hb
  refine ⟨⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩, fun b hb => (hag b hb).symm⟩
  · rw [hag b hb]
    exact h₁.1 b (mem_univ b)
  · rw [hag b hb, hag _ (hclosed b hb)]
    exact h₁.2 b (mem_univ b)
  · rw [hag b hb]
    exact S.iterate_near_one hA hj b
theorem doubleBlockValues_mem (S : InductionData hF ρ) {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1)) :
    doubleBlockValues hF c A ∈
      DoubleBlockPolydisc.polydiscPositive (3 / 4 * polydiscRadius L) c :=
  ⟨_, ⟨_, S.levelIterate_mem_polydisc hA hj c, rfl⟩, rfl⟩
theorem differentiableOn_smoothingCoeff (S : InductionData hF ρ) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) (b : PositiveEdge L n k j)
    (hb : b.1 ∈ DoubleBlockPolydisc.doubleBlockBonds c) (a' s : Fin 3) :
    DifferentiableOn ℂ
      (fun A : GroupLieProduct.tracelessPiSubmodule F =>
        pauliCoeff a' (stepKernel (levelIterate hF j A.1) c b.1 (ComplexMatrix2.pauliFamily s)))
      (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
  have hold := S.stepHolomorphy L S.admissible n k j S.side_pos hj c hc
  obtain ⟨inst, hφ⟩ := hold.smoothing_holomorphic b hb a' s
  have h := differentiableOn_comp_of_isHolomorphic S.analyticity
    (isOpen_val_preimage_supBall S.radius_pos) (hφ OneLoop.pauliBasis)
    (v := fun A : GroupLieProduct.tracelessPiSubmodule F => doubleBlockValues hF c A.1)
    (fun i => S.iterates j hj.le i.1) (fun A hA => S.doubleBlockValues_mem hA hj c)
  refine h.congr fun A hA => ?_
  obtain ⟨h₁, h₂⟩ := S.fieldOfValues_spec hA hj c
  exact hold.smoothing_local _ (S.levelIterate_mem_polydisc hA hj c) _ h₁ h₂ b hb a' s
theorem differentiableOn_conjugationCoeff (S : InductionData hF ρ) {j : ℕ} (hj : j < k)
    (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) (a' s : Fin 3) :
    DifferentiableOn ℂ
      (fun A : GroupLieProduct.tracelessPiSubmodule F =>
        pauliCoeff a' (ComplexMatrix2.conjugateBy
          (PeriodicLattice.complexMeanContourHolonomy (levelIterate hF j A.1) y x)
          (ComplexMatrix2.pauliFamily s)))
      (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
  have hc := forwardFrom_zero_positive y
  have hold := S.stepHolomorphy L S.admissible n k j S.side_pos hj _ hc
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
      (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  obtain ⟨inst, hφ⟩ := hold.conjugation_holomorphic y hy x hx a' s
  have h := differentiableOn_comp_of_isHolomorphic S.analyticity
    (isOpen_val_preimage_supBall S.radius_pos) (hφ OneLoop.pauliBasis)
    (v := fun A : GroupLieProduct.tracelessPiSubmodule F => doubleBlockValues hF _ A.1)
    (fun i => S.iterates j hj.le i.1) (fun A hA => S.doubleBlockValues_mem hA hj _)
  refine h.congr fun A hA => ?_
  obtain ⟨h₁, h₂⟩ := S.fieldOfValues_spec hA hj (PeriodicLattice.Bond.forwardFrom y 0)
  exact hold.conjugation_local _ (S.levelIterate_mem_polydisc hA hj _) _ h₁ h₂ y hy x hx a' s
theorem differentiableOn_iterCovariantDeriv (S : InductionData hF ρ)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k 0) (j : ℕ) (hj : j ≤ k)
    (c : Edge L n k j) (hc : c.IsPositivelyOriented) (a' : Fin 3) :
    DifferentiableOn ℂ
      (fun A : GroupLieProduct.tracelessPiSubmodule F =>
        pauliCoeff a' (iterCovariantDeriv L n k (fieldAt hF A.1) j B c))
      (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
  induction j generalizing a' with
  | zero => exact differentiableOn_const (pauliCoeff a' (B c))
  | succ j ih =>
    have hjk : j < k := hj
    have := S.edges_finite j
    have hfin : (positiveDoubleBlockEdges c).Finite := Set.toFinite _
    have hd : DifferentiableOn ℂ
        (fun A : GroupLieProduct.tracelessPiSubmodule F =>
          ∑ b ∈ hfin.toFinset, ∑ s,
            pauliCoeff s (iterCovariantDeriv L n k (fieldAt hF A.1) j B b) *
              pauliCoeff a' (stepKernel (levelIterate hF j A.1) c b (ComplexMatrix2.pauliFamily s)))
        (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
      refine DifferentiableOn.fun_sum fun b hb => DifferentiableOn.fun_sum fun s _ => ?_
      have hb' := hfin.mem_toFinset.1 hb
      exact (ih hjk.le _ hb'.2 s).mul
        (S.differentiableOn_smoothingCoeff hjk hc ⟨b, hb'.2⟩ hb'.1 a' s)
    refine hd.congr fun A hA => ?_
    obtain ⟨h₁, h₂, -⟩ := S.stepBounds L S.admissible n k j S.side_pos hjk c hc _
      (S.small A.1 hA j hjk).1 (S.iterate_near_one hA hjk)
    have hI := S.iterCovariantDeriv_mem hA hB j hjk.le
    show pauliCoeff a' (covariantSmoothingDeriv (levelIterate hF j A.1)
      (iterCovariantDeriv L n k (fieldAt hF A.1) j B) c) = _
    rw [h₁ _ hI, finsum_mem_eq_finite_toFinset_sum _ hfin,
      pauliCoeff_sum _ _ (fun b hb => (h₂ b (hfin.mem_toFinset.1 hb)).mapsTo _
        (hI.1 b (hfin.mem_toFinset.1 hb).2))]
    exact Finset.sum_congr rfl fun b hb => pauliCoeff_endo_apply
      (h₂ b (hfin.mem_toFinset.1 hb)) (hI.1 b (hfin.mem_toFinset.1 hb).2) a'
theorem differentiableOn_iterAdjointCubeAverage (S : InductionData hF ρ)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (j : ℕ)
    (hj : j ≤ k) (y : Vertex L n k j) (a' : Fin 3) :
    DifferentiableOn ℂ
      (fun A : GroupLieProduct.tracelessPiSubmodule F =>
        pauliCoeff a' (iterAdjointCubeAverage L n k (fieldAt hF A.1) j l y))
      (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
  induction j generalizing a' with
  | zero => exact differentiableOn_const (pauliCoeff a' (l y))
  | succ j ih =>
    have hjk : j < k := hj
    have := S.vertices_finite j
    have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
        Set (Vertex L n k j)).Finite := Set.toFinite _
    have hd : DifferentiableOn ℂ
        (fun A : GroupLieProduct.tracelessPiSubmodule F =>
          PeriodicLattice.inverseFourthPowerWeight L * ∑ x ∈ hfin.toFinset, ∑ s,
            pauliCoeff s (iterAdjointCubeAverage L n k (fieldAt hF A.1) j l x) *
              pauliCoeff a' (ComplexMatrix2.conjugateBy
                (PeriodicLattice.complexMeanContourHolonomy (levelIterate hF j A.1) y x)
                (ComplexMatrix2.pauliFamily s)))
        (Subtype.val ⁻¹' GroupLieProduct.supBall F ρ) := by
      refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun x hx =>
        DifferentiableOn.fun_sum fun s _ => ?_) _
      exact (ih hjk.le x s).mul
        (S.differentiableOn_conjugationCoeff hjk y (hfin.mem_toFinset.1 hx) a' s)
    refine hd.congr fun A hA => ?_
    have hm : ∀ x, iterAdjointCubeAverage L n k (fieldAt hF A.1) j l x ∈
        ComplexMatrix2.traceless :=
      fun x => S.iterAdjointCubeAverage_mem hA hl j hjk.le x
    have hT := fun x (hx : x ∈ hfin.toFinset) =>
      S.conjugation_bounded hA hjk y (hfin.mem_toFinset.1 hx)
    show pauliCoeff a' (PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ComplexMatrix2.conjugateBy
          (PeriodicLattice.complexMeanContourHolonomy (levelIterate hF j A.1) y x)
          (iterAdjointCubeAverage L n k (fieldAt hF A.1) j l x)) = _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
      pauliCoeff_smul _ (Submodule.sum_mem _ fun x hx => (hT x hx).mapsTo _ (hm x)),
      pauliCoeff_sum _ _ (fun x hx => (hT x hx).mapsTo _ (hm x))]
    exact congrArg _ (Finset.sum_congr rfl fun x hx =>
      pauliCoeff_endo_apply (hT x hx) (hm x) a')
end InductionData
end Levels
section Entries
variable {L n k : ℕ}
open Classical in
def unitForm (i : Fin 3 × PositiveEdge L n k 0) : Edge L n k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L n k 0).ofCoeffs (Pi.single i 1)
open Classical in
def unitFunction (i : Fin 3 × Vertex L n k 0) : Vertex L n k 0 → ComplexMatrix2 :=
  (vertexCoordinate (Vertex L n k 0)).ofCoeffs (Pi.single i 1)
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
open Classical in
theorem ofCoeffs_mem_complexEdgeForms
    (hrev : ∀ (f : Edge L n k 0 → ComplexMatrix2) (b : Edge L n k 0),
      extendOddly f b.opposite = -extendOddly f b)
    (f : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    (edgePauliCoordinates L n k 0).ofCoeffs f ∈ complexEdgeForms L n k 0 := by
  have e : (edgePauliCoordinates L n k 0).ofCoeffs f = extendOddly fun b =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0 := rfl
  rw [e]
  refine ⟨fun b hb => ?_, fun b => hrev _ b⟩
  have e₂ : (extendOddly fun b : Edge L n k 0 =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0) b =
      ofPauliCoeffs f ⟨b, hb⟩ := by
    unfold extendOddly
    simp only [if_pos hb, dif_pos hb]
  rw [e₂]
  exact ofPauliCoeffs_mem _ _
theorem unitFunction_mem (i : Fin 3 × Vertex L n k 0) (x : Vertex L n k 0) :
    unitFunction i x ∈ ComplexMatrix2.traceless :=
  ofPauliCoeffs_mem _ x
open Classical in
theorem rescaled_Q_apply (hK : ThreeMapKernels.OnTorus L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k)
    (hm : ∀ B ∈ complexEdgeForms L n k 0,
      iterCovariantDeriv L n k U k B ∈ complexEdgeForms L n k k)
    (hrev : ∀ (f : Edge L n k 0 → ComplexMatrix2) (b : Edge L n k 0),
      extendOddly f b.opposite = -extendOddly f b)
    (i' : Fin 3 × PositiveEdge L n k k) (i : Fin 3 × PositiveEdge L n k 0) :
    (rescaledOperators L n k U).Q i' i = (finestMesh L k : ℂ) *
      pauliCoeff i'.1 (iterCovariantDeriv L n k U k (unitForm i) i'.2.1) := by
  have hk := (hK.2.2.2 U hU).1
  have hg := hk.smul_represents (finestMesh L k : ℂ)
  have e : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
      (fun B => finestMesh L k • iterCovariantDeriv L n k U k B) =
      (finestMesh L k : ℂ) • PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0)
        (edgePauliCoordinates L n k k) (iterCovariantDeriv L n k U k) := by
    funext f κ
    have hv := (hm _ (ofCoeffs_mem_complexEdgeForms hrev f)).1 κ.2.1 κ.2.2
    show pauliCoeff κ.1 ((finestMesh L k • iterCovariantDeriv L n k U k
        ((edgePauliCoordinates L n k 0).ofCoeffs f)) κ.2.1) = (finestMesh L k : ℂ) *
      pauliCoeff κ.1 (iterCovariantDeriv L n k U k
        ((edgePauliCoordinates L n k 0).ofCoeffs f) κ.2.1)
    rw [← pauliCoeff_smul _ hv]
    congr 1
  have hg' : Represents ((finestMesh L k : ℂ) •
      (edgePauliCoordinates L n k 0).kernel (edgePauliCoordinates L n k k) (iterCovariantDeriv L n k U k))
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • iterCovariantDeriv L n k U k B) := by
    rw [e]
    exact hg
  have h := entry_eq_of_represents (kernelOfMap_represents hg') i i'
  have hQ : (rescaledOperators L n k U).Q = kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs
      (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • iterCovariantDeriv L n k U k B) := rfl
  rw [hQ, h, e]
  rfl
open Classical in
theorem rescaled_R_apply (hK : ThreeMapKernels.OnTorus L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k)
    (i' : Fin 3 × Vertex L n k k) (i : Fin 3 × Vertex L n k 0) :
    (rescaledOperators L n k U).R i' i =
      pauliCoeff i'.1 (iterAdjointCubeAverage L n k U k (unitFunction i) i'.2) :=
  entry_eq_of_represents (hK.2.2.2 U hU).2.represents i i'
theorem restrict_mem_supBall {F : Finset (Edge L n k 0)} {ρ : ℝ} (hρ : 0 < ρ)
    {a : Edge L n k 0 → ComplexMatrix2} (ha : a ∈ complexEdgeForms L n k 0)
    (hs : maxOperatorNorm a < ENNReal.ofReal ρ) :
    (fun b : F => a b) ∈ GroupLieProduct.supBall F ρ := by
  refine ⟨fun b => ?_, (supNorm_lt_iff hρ _).2 fun b => ?_⟩
  · rcases PeriodicLattice.Bond.positive_or_opposite_positive b.1 with h | h
    · exact ha.1 _ h
    · have e : a b.1.opposite = -a b.1 := ha.2 b.1
      have h' : a b.1.opposite ∈ ComplexMatrix2.traceless := ha.1 _ h
      rw [e] at h'
      have h'' := ComplexMatrix2.traceless.neg_mem h'
      rw [neg_neg] at h''
      exact h''
  · have h₁ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (a b.1)) ≤ maxOperatorNorm a :=
      le_iSup (fun i => ENNReal.ofReal (ComplexMatrix2.operatorNorm (a i))) b.1
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 (h₁.trans_lt hs)
end Entries
theorem rescaledKernelsHolomorphicOnTorus (hK : ThreeMapKernels.Claim)
    (hI : IteratedMeansHolomorphic.IteratedMeansHolomorphicOnSide)
    (hH : StepKernelHolomorphy.StepKernelsHolomorphic)
    (hS : StepKernels.StepKernelBounds)
    (hAn : GroupLieProduct.HolomorphicMatrixAnalyticity)
    (hD : GroupLieProduct.HolomorphicOnTracelessIffDifferentiable)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement) :
    RescaledKernelsHolomorphicOnTorus := by
  intro L hL ρ hρ k hk n hn hprem
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hsites : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite hLpos n _
  have hbonds : ∀ j, Finite (Edge L n k j) := fun j =>
    have := hsites j
    Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have := hbonds 0
  let _ := Fintype.ofFinite (Edge L n k 0)
  have hF : ∀ b : Edge L n k 0, b ∈ (Finset.univ : Finset (Edge L n k 0)) := Finset.mem_univ
  have hrev : ∀ j ≤ k, ∀ (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j),
      extendOddly f b.opposite = -extendOddly f b := by
    intro j hj f b
    have hx := ((hO ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
    have hx' : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := hx
    unfold extendOddly
    rcases hx' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [if_neg h₂, if_pos h₁, PeriodicLattice.Bond.opposite_opposite]
    · rw [if_pos h₁, if_neg h₂, neg_neg]
  have S : InductionData hF ρ :=
    { radius_pos := hρ
      admissible := hL
      side_pos := hn
      stepBounds := hS
      stepHolomorphy := hH
      analyticity := hAn
      edges_finite := hbonds
      vertices_finite := hsites
      extendOddly_opposite := hrev
      small := fun A hA j hj =>
        hprem _ (antisymmetrizedForm_mem hF hA) (maxOperatorNorm_antisymmetrizedForm_lt hF hρ hA) j hj
      iterates := fun j hj c => by
        obtain ⟨F', f', hf, hv⟩ := hI L hL ρ hρ n k hn hk hprem j hj c
        exact differentiableOn_levelIterate hD hF hρ (hf OneLoop.pauliBasis) hv }
  have hlin : IsLinearMap ℂ (LeftChartFields.scalarCoords) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsmall : ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a < ENNReal.ofReal ρ →
      remainderGaugeField a ∈ smallIterateFields L n k := by
    intro a ha hs
    refine ⟨(hprem a ha hs 0 hk).1, fun j hj => ⟨(hprem a ha hs j hj).1, fun b => ?_⟩⟩
    have h₁ := (hprem a ha hs j hj).2 b
    have h₂ : 0 ≤ ComplexMatrix2.operatorNorm
        (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) :=
      norm_nonneg _
    linarith
  have hconf : ∀ a ∈ complexEdgeForms L n k 0,
      fieldAt hF (fun b => a b) = remainderGaugeField a := by
    intro a ha
    unfold fieldAt
    rw [antisymmetrizedForm_of_form hF ha]
  have hKs := (hK L hL k hk).1 n hn
  classical
  refine ⟨fun i' i => ⟨Finset.univ, fun A => (finestMesh L k : ℂ) * pauliCoeff i'.1
      (iterCovariantDeriv L n k (fieldAt hF A) k (unitForm i) i'.2.1),
      fun e => ?_, fun a ha hs => ?_⟩,
    fun i' i => ⟨Finset.univ, fun A => pauliCoeff i'.1
      (iterAdjointCubeAverage L n k (fieldAt hF A) k (unitFunction i) i'.2),
      fun e => ?_, fun a ha hs => ?_⟩⟩
  · exact (hD _ ℂ 1 e _ hlin _ _).2 ⟨isSupOpen_supBall hρ,
      (S.differentiableOn_iterCovariantDeriv
        (ofCoeffs_mem_complexEdgeForms (hrev 0 (Nat.zero_le k)) _) k le_rfl i'.2.1 i'.2.2
        i'.1).const_mul _⟩
  · have hm : ∀ B ∈ complexEdgeForms L n k 0,
        iterCovariantDeriv L n k (remainderGaugeField a) k B ∈
          complexEdgeForms L n k k := fun B hB => by
      rw [← hconf a ha]
      exact S.iterCovariantDeriv_mem (restrict_mem_supBall hρ ha hs) hB k le_rfl
    show _ * pauliCoeff _ (iterCovariantDeriv L n k
      (fieldAt hF fun b => a b) k _ _) = _
    rw [hconf a ha]
    exact (rescaled_Q_apply hKs (hsmall a ha hs) hm (hrev 0 (Nat.zero_le k)) i' i).symm
  · exact (hD _ ℂ 1 e _ hlin _ _).2 ⟨isSupOpen_supBall hρ,
      S.differentiableOn_iterAdjointCubeAverage (unitFunction_mem i) k le_rfl i'.2 i'.1⟩
  · show pauliCoeff _ (iterAdjointCubeAverage L n k
      (fieldAt hF fun b => a b) k _ _) = _
    rw [hconf a ha]
    exact (rescaled_R_apply hKs (hsmall a ha hs) i' i).symm
end YangMills.Construction.Tower.RescaledKernelsHolomorphy
end
