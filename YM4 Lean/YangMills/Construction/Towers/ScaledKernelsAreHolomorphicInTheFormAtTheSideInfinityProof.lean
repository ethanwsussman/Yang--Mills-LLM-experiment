import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.IteratesAreHolomorphicInTheFormAtTheSideInfinityProof
import YangMills.Construction.Towers.ScaledKernelsAreHolomorphicInTheFormAtTheSideInfinity
import YangMills.Construction.Towers.StepKernelsAreHolomorphicAtTheSideInfinity
import YangMills.Construction.Towers.StepKernelsOfTheIteratedAveragesAtTheSideInfinity
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocalProof
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.GroupLieProduct
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels
open YangMills.Construction.Matrices
open YangMills.Construction.Coordinates
open YangMills.Construction.Tower.LeftChartFields (scalarCoords)
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean meanOfDefined)
open YangMills.Construction.Tower.DoubleBlockPolydisc (leftComponents)
open YangMills.Construction.Tower.DoubleBlockPolydisc.Infinite (doubleBlockBonds
  positiveDoubleBlockBonds polydiscPositive fieldOfValues)
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy (kernelCoeff contourConjCoeff
  IsHolomorphicInValues DependsOnlyOnDoubleBlock)
open YangMills.Construction.Tower.FullSpace.StepKernels (singleLinkForm positiveDoubleCubeLinks
  StepKernelsAt IsBoundedTracelessEndo)
section Tuples
variable {σ : Type} [Fintype σ]
theorem supNorm_eq_norm (A : σ → ComplexMatrix2) : supNorm A = ‖A‖ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.supNorm_eq_norm <;> assumption
theorem isHolomorphicIn_of_analyticAt {N N' : ℕ} {U : Set (ComplexCoordinates N)}
    {φ : ComplexCoordinates N → ComplexCoordinates N'} (hU : IsOpen U)
    (h : ∀ w ∈ U, AnalyticAt ℂ φ w) : ComplexCoordinates.IsHolomorphicIn U φ := by apply _root_.YangMills.Construction.Tower.FullSpace.IterHolomorphy.isHolomorphicIn_of_analyticAt <;> assumption
theorem isHolomorphicIn_comp_clm {N N' N'' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (h : ComplexCoordinates.IsHolomorphicIn O f)
    (T : ComplexCoordinates N' →L[ℂ] ComplexCoordinates N'') :
    ComplexCoordinates.IsHolomorphicIn O (T ∘ f) :=
  ⟨h.1, T.continuous.comp_continuousOn h.2.1, fun a ha j => (h.2.2 a ha j).mono fun ζ hζ =>
    T.differentiableAt.comp ζ hζ⟩
def scalarCLM : ℂ →L[ℂ] ComplexCoordinates 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
def matrixCoordsCLM : ComplexMatrix2 →L[ℂ] ComplexCoordinates 4 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexCoordinates.matrixEquiv
      map_add' := fun X Y => by
        funext t
        simp [ComplexCoordinates.matrixEquiv]
      map_smul' := fun c X => by
        funext t
        simp [ComplexCoordinates.matrixEquiv] }
def topLeftEntry : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X 0 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def unitMatrixCoords : ComplexCoordinates 1 →L[ℂ] ComplexCoordinates 4 :=
  matrixCoordsCLM.comp ((ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : ComplexMatrix2))
def coordsTupleCLM (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    ComplexCoordinates (Fintype.card σ * 3) →L[ℂ] σ → ComplexMatrix2 :=
  ContinuousLinearMap.pi fun i => ∑ c : Fin 3,
    (ContinuousLinearMap.proj (finProdFinEquiv (ν i, c))).smulRight (β c : ComplexMatrix2)
theorem coordsTupleCLM_apply (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : ComplexCoordinates (Fintype.card σ * 3)) :
    coordsTupleCLM β ν w = tupleOfCoords β ν w := by
  funext i
  simp [coordsTupleCLM, tupleOfCoords, ComplexCoordinates.tracelessTuple]
theorem tupleOfCoords_mem (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : ComplexCoordinates (Fintype.card σ * 3)) :
    tupleOfCoords β ν w ∈ tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
def IsLocallyAnalyticOnBall {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (ρ : ℝ)
    (f : (σ → ComplexMatrix2) → E) : Prop :=
  ∀ A ∈ supBall σ ρ, ∃ g : (σ → ComplexMatrix2) → E, AnalyticAt ℂ g A ∧
    ∀ᶠ B in 𝓝 A, B ∈ supBall σ ρ → f B = g B
theorem isHolomorphicOnTraceless_of_locallyAnalytic
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ρ : ℝ)
    (f : (σ → ComplexMatrix2) → ℂ) (h : IsLocallyAnalyticOnBall ρ f) :
    IsHolomorphicOnTraceless β scalarCoords (supBall σ ρ) f := by
  refine ⟨⟨fun A hA => hA.1, fun A hA => ⟨ρ - supNorm A, sub_pos.2 hA.2, fun B hB hlt =>
    ⟨hB, ?_⟩⟩⟩, fun ν => ?_⟩
  · have h1 : ‖B‖ ≤ ‖B - A‖ + ‖A‖ := by simpa using norm_add_le (B - A) A
    rw [supNorm_eq_norm] at hlt ⊢
    rw [supNorm_eq_norm] at hlt
    linarith
  · have hT : ∀ w, tupleOfCoords β ν w = coordsTupleCLM β ν w := fun w =>
      (coordsTupleCLM_apply β ν w).symm
    have hU : tupleOfCoords β ν ⁻¹' supBall σ ρ =
        {w | ‖coordsTupleCLM β ν w‖ < ρ} := by
      ext w
      show tupleOfCoords β ν w ∈ supBall σ ρ ↔ ‖coordsTupleCLM β ν w‖ < ρ
      rw [← hT]
      exact ⟨fun hw => by rw [← supNorm_eq_norm]; exact hw.2,
        fun hw => ⟨tupleOfCoords_mem β ν w, by rw [supNorm_eq_norm]; exact hw⟩⟩
    have hopen : IsOpen (tupleOfCoords β ν ⁻¹' supBall σ ρ) := by
      rw [hU]
      exact isOpen_lt (by fun_prop) continuous_const
    refine isHolomorphicIn_of_analyticAt hopen fun w hw => ?_
    obtain ⟨g, hg, hev⟩ := h _ hw
    have hcont : ContinuousAt (tupleOfCoords β ν) w := by
      have : tupleOfCoords β ν = coordsTupleCLM β ν := funext hT
      rw [this]
      exact (coordsTupleCLM β ν).continuous.continuousAt
    have hana : AnalyticAt ℂ (fun w => scalarCLM (g (coordsTupleCLM β ν w))) w := by
      have h1 : AnalyticAt ℂ (coordsTupleCLM β ν) w := (coordsTupleCLM β ν).analyticAt w
      have h2 : AnalyticAt ℂ g (coordsTupleCLM β ν w) := by rwa [← hT]
      exact scalarCLM.analyticAt _ |>.comp (h2.comp h1)
    refine hana.congr ?_
    filter_upwards [hcont.eventually hev, hopen.mem_nhds hw] with v hv hv'
    show scalarCLM (g (coordsTupleCLM β ν v)) = scalarCoords _
    rw [← hT, ← hv hv']
    rfl
theorem isHolomorphicToCoords_smul_one {ι κ : Type} [Fintype ι] [Fintype κ]
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ℂ}
    (h : IsHolomorphicToCoords β scalarCoords W Φ) :
    IsHolomorphicToCoords β ComplexCoordinates.matrixEquiv W
      fun p => Φ p • (1 : ComplexMatrix2) := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨hW, unitMatrixCoords.continuous.comp_continuousOn hc, fun p hp' => ?_⟩
  obtain ⟨O, h0, hO, hT, hν⟩ := hp p hp'
  exact ⟨O, h0, hO, hT, fun ν => isHolomorphicIn_comp_clm (hν ν) unitMatrixCoords⟩
end Tuples
section Narrowing
variable {β : Type}
def restrictFamily {F F' : Finset β} (h : F ⊆ F') :
    (F' → ComplexMatrix2) →L[ℂ] (F → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun c => ContinuousLinearMap.proj ⟨c.1, h c.2⟩
theorem restrictFamily_mem_supBall {F F' : Finset β} (h : F ⊆ F') {ρ : ℝ}
    {A : F' → ComplexMatrix2} (hA : A ∈ supBall F' ρ) : restrictFamily h A ∈ supBall F ρ := by
  refine ⟨fun c => hA.1 _, ?_⟩
  have hle : ‖restrictFamily h A‖ ≤ ‖A‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => norm_le_pi_norm A ⟨c.1, h c.2⟩
  rw [supNorm_eq_norm]
  have := hA.2
  rw [supNorm_eq_norm] at this
  linarith
theorem IsLocallyAnalyticOnBall.comp_restrictFamily {F F' : Finset β} (h : F ⊆ F') {ρ : ℝ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : (F → ComplexMatrix2) → E}
    (hf : IsLocallyAnalyticOnBall ρ f) : IsLocallyAnalyticOnBall ρ (f ∘ restrictFamily h) := by
  intro A hA
  obtain ⟨g, hg, hev⟩ := hf _ (restrictFamily_mem_supBall h hA)
  refine ⟨g ∘ restrictFamily h, hg.comp ((restrictFamily h).analyticAt A), ?_⟩
  filter_upwards [(restrictFamily h).continuous.continuousAt.eventually hev] with B hB hBball
  exact hB (restrictFamily_mem_supBall h hBball)
end Narrowing
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem combination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_eq_equiv {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ a := dif_pos hX
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (z : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (z • X) = z * pauliCoeff a X := by
  rw [pauliCoeff_eq_equiv (ComplexMatrix2.traceless.smul_mem z hX), pauliCoeff_eq_equiv hX]
  have e : (⟨z • X, ComplexMatrix2.traceless.smul_mem z hX⟩ : ComplexMatrix2.traceless) =
      z • ⟨X, hX⟩ := rfl
  rw [e, map_smul]
  rfl
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_sum {ι : Type} (s : Finset ι) (Y : ι → ComplexMatrix2)
    (hY : ∀ i ∈ s, Y i ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (∑ i ∈ s, Y i) = ∑ i ∈ s, pauliCoeff a (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pauliCoeff_zero a
  | insert i s hi ih =>
    have hs : ∀ i ∈ s, Y i ∈ ComplexMatrix2.traceless := fun j hj =>
      hY j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      pauliCoeff_add (hY i (Finset.mem_insert_self i s)) (Submodule.sum_mem _ hs), ih hs]
theorem pauliCoeff_linearMap {f : ComplexMatrix2 → ComplexMatrix2}
    (T : ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless)
    (hT : ∀ X : ↥ComplexMatrix2.traceless, (T X : ComplexMatrix2) = f X) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (a' : Fin 3) :
    pauliCoeff a' (f X) =
      ∑ a, pauliCoeff a X * pauliCoeff a' (f (ComplexMatrix2.pauliFamily a)) := by
  have hmem : ∀ a, f (ComplexMatrix2.pauliFamily a) ∈ ComplexMatrix2.traceless := fun a =>
    hT ⟨_, pauliFamily_mem_traceless a⟩ ▸ (T ⟨_, pauliFamily_mem_traceless a⟩).2
  have e : (⟨X, hX⟩ : ComplexMatrix2.traceless) =
      ∑ a, pauliCoeff a X •
        (⟨ComplexMatrix2.pauliFamily a, pauliFamily_mem_traceless a⟩ : ComplexMatrix2.traceless) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (combination_pauliCoeff hX).symm
  have e₂ : f X = ∑ a, pauliCoeff a X • f (ComplexMatrix2.pauliFamily a) := by
    rw [← hT ⟨X, hX⟩, e, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Submodule.coe_smul, hT]
  rw [e₂, pauliCoeff_sum _ _ fun a _ => ComplexMatrix2.traceless.smul_mem _ (hmem a)]
  exact Finset.sum_congr rfl fun a _ => pauliCoeff_smul _ (hmem a) _
theorem pauliCoeff_real_smul (r : ℝ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (r • X) = (r : ℂ) * pauliCoeff a X := by
  rw [← pauliCoeff_smul _ hX]
  congr 1
end Coefficients
section EvaluationMaps
variable {L k : ℕ}
def InFormBall (ρ : ℝ) (a : Edge L k 0 → ComplexMatrix2) : Prop :=
  a ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a < ENNReal.ofReal ρ
def AnalyticRepresentationOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (ρ : ℝ)
    (F : Finset (Edge L k 0)) (φ : (Edge L k 0 → ComplexMatrix2) → E) : Prop :=
  ∃ f : (F → ComplexMatrix2) → E, IsLocallyAnalyticOnBall ρ f ∧
    ∀ a, InFormBall ρ a → f (fun c => a c) = φ a
def AnalyticRepresentation {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (ρ : ℝ)
    (φ : (Edge L k 0 → ComplexMatrix2) → E) : Prop :=
  ∃ F : Finset (Edge L k 0), (∀ b ∈ F, b.IsPositivelyOriented) ∧ AnalyticRepresentationOn ρ F φ
variable {ρ : ℝ}
theorem AnalyticRepresentationOn.mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F F' : Finset (Edge L k 0)} (h : F ⊆ F') {φ : (Edge L k 0 → ComplexMatrix2) → E}
    (hφ : AnalyticRepresentationOn ρ F φ) : AnalyticRepresentationOn ρ F' φ := by
  obtain ⟨f, hf, hv⟩ := hφ
  exact ⟨f ∘ restrictFamily h, hf.comp_restrictFamily h, fun a ha => hv a ha⟩
theorem AnalyticRepresentation.congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ ψ : (Edge L k 0 → ComplexMatrix2) → E} (hφ : AnalyticRepresentation ρ φ)
    (e : ∀ a, InFormBall ρ a → ψ a = φ a) : AnalyticRepresentation ρ ψ := by
  obtain ⟨F, hF, f, hf, hv⟩ := hφ
  exact ⟨F, hF, f, hf, fun a ha => (hv a ha).trans (e a ha).symm⟩
theorem AnalyticRepresentation.const (z : ℂ) : AnalyticRepresentation (L := L) (k := k) ρ fun _ => z :=
  ⟨∅, by simp, fun _ => z, fun _ _ => ⟨fun _ => z, analyticAt_const,
    Eventually.of_forall fun _ _ => rfl⟩, fun _ _ => rfl⟩
theorem AnalyticRepresentationOn.add {F : Finset (Edge L k 0)}
    {φ ψ : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hφ : AnalyticRepresentationOn ρ F φ) (hψ : AnalyticRepresentationOn ρ F ψ) :
    AnalyticRepresentationOn ρ F fun a => φ a + ψ a := by
  obtain ⟨f, hf, hv⟩ := hφ
  obtain ⟨g, hg, hw⟩ := hψ
  refine ⟨fun A => f A + g A, fun A hA => ?_, fun a ha => congrArg₂ (· + ·) (hv a ha) (hw a ha)⟩
  obtain ⟨f', hf', ef⟩ := hf A hA
  obtain ⟨g', hg', eg⟩ := hg A hA
  refine ⟨fun B => f' B + g' B, hf'.add hg', ?_⟩
  filter_upwards [ef, eg] with B h₁ h₂ hB
  rw [h₁ hB, h₂ hB]
theorem AnalyticRepresentationOn.mul {F : Finset (Edge L k 0)}
    {φ ψ : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hφ : AnalyticRepresentationOn ρ F φ) (hψ : AnalyticRepresentationOn ρ F ψ) :
    AnalyticRepresentationOn ρ F fun a => φ a * ψ a := by
  obtain ⟨f, hf, hv⟩ := hφ
  obtain ⟨g, hg, hw⟩ := hψ
  refine ⟨fun A => f A * g A, fun A hA => ?_, fun a ha => congrArg₂ (· * ·) (hv a ha) (hw a ha)⟩
  obtain ⟨f', hf', ef⟩ := hf A hA
  obtain ⟨g', hg', eg⟩ := hg A hA
  refine ⟨fun B => f' B * g' B, hf'.mul hg', ?_⟩
  filter_upwards [ef, eg] with B h₁ h₂ hB
  rw [h₁ hB, h₂ hB]
theorem AnalyticRepresentation.add {φ ψ : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hφ : AnalyticRepresentation ρ φ) (hψ : AnalyticRepresentation ρ ψ) :
    AnalyticRepresentation ρ fun a => φ a + ψ a := by
  classical
  obtain ⟨F, hF, h⟩ := hφ
  obtain ⟨F', hF', h'⟩ := hψ
  refine ⟨F ∪ F', fun b hb => ?_, (h.mono Finset.subset_union_left).add
    (h'.mono Finset.subset_union_right)⟩
  rcases Finset.mem_union.1 hb with hb | hb
  · exact hF b hb
  · exact hF' b hb
theorem AnalyticRepresentation.mul {φ ψ : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hφ : AnalyticRepresentation ρ φ) (hψ : AnalyticRepresentation ρ ψ) :
    AnalyticRepresentation ρ fun a => φ a * ψ a := by
  classical
  obtain ⟨F, hF, h⟩ := hφ
  obtain ⟨F', hF', h'⟩ := hψ
  refine ⟨F ∪ F', fun b hb => ?_, (h.mono Finset.subset_union_left).mul
    (h'.mono Finset.subset_union_right)⟩
  rcases Finset.mem_union.1 hb with hb | hb
  · exact hF b hb
  · exact hF' b hb
theorem AnalyticRepresentation.sum {ι : Type} (s : Finset ι) {φ : ι → (Edge L k 0 → ComplexMatrix2) → ℂ}
    (h : ∀ i ∈ s, AnalyticRepresentation ρ (φ i)) : AnalyticRepresentation ρ fun a => ∑ i ∈ s, φ i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AnalyticRepresentation.const (L := L) (k := k) (ρ := ρ) 0
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun a _ => ?_
    rw [Finset.sum_insert hi]
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem exists_form_of_mem_supBall
    (hxor : ∀ b : Edge L k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hρ : 0 < ρ) (F : Finset (Edge L k 0)) (hF : ∀ b ∈ F, b.IsPositivelyOriented)
    {A : F → ComplexMatrix2} (hA : A ∈ supBall F ρ) :
    ∃ a : Edge L k 0 → ComplexMatrix2, InFormBall ρ a ∧ (fun c : F => a c) = A := by
  classical
  let a₀ : Edge L k 0 → ComplexMatrix2 := fun b => if h : b ∈ F then A ⟨b, h⟩ else 0
  let a : Edge L k 0 → ComplexMatrix2 := extendOddly a₀
  have hap : ∀ b : Edge L k 0, b.IsPositivelyOriented → a b = a₀ b := fun b hb => by
    show (if b.IsPositivelyOriented then _ else _) = _
    rw [if_pos hb]
  have han : ∀ b : Edge L k 0, ¬ b.IsPositivelyOriented → a b = -a₀ b.opposite := fun b hb => by
    show (if b.IsPositivelyOriented then _ else _) = _
    rw [if_neg hb]
  have ha₀ : ∀ b, a₀ b ∈ ComplexMatrix2.traceless := fun b => by
    by_cases h : b ∈ F
    · simp only [a₀, dif_pos h]
      exact hA.1 _
    · simp only [a₀, dif_neg h]
      exact ComplexMatrix2.traceless.zero_mem
  have hnorm₀ : ∀ b, ComplexMatrix2.operatorNorm (a₀ b) ≤ supNorm A := fun b => by
    by_cases h : b ∈ F
    · simp only [a₀, dif_pos h]
      rw [supNorm_eq_norm]
      exact norm_le_pi_norm A ⟨b, h⟩
    · simp only [a₀, dif_neg h]
      rw [supNorm_eq_norm]
      simp
  have hnorm : ∀ b, ComplexMatrix2.operatorNorm (a b) ≤ supNorm A := fun b => by
    by_cases h : b.IsPositivelyOriented
    · rw [hap b h]
      exact hnorm₀ b
    · rw [han b h]
      simpa using hnorm₀ b.opposite
  refine ⟨a, ⟨⟨fun b hb => ?_, fun b => ?_⟩, ?_⟩, ?_⟩
  · rw [hap b hb]
    exact ha₀ b
  · rcases hxor b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [han _ h2, hap b h1]
      rfl
    · rw [hap _ h1, han b h2, neg_neg]
  · refine lt_of_le_of_lt (iSup_le fun b => ENNReal.ofReal_le_ofReal (hnorm b)) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2
  · funext c
    rw [hap _ (hF _ c.2)]
    simp [a₀]
theorem AnalyticRepresentation.comp_holomorphic (H : HolomorphicMatrixAnalyticity)
    (hxor : ∀ b : Edge L k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hρ : 0 < ρ) {P : Type} [Fintype P] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W₀ : Set (P → ComplexMatrix2)) (Φ : (P → ComplexMatrix2) → ℂ)
    (hΦ : IsHolomorphicToCoords β scalarCoords (leftComponents ⁻¹' W₀)
      fun p => Φ (leftComponents p))
    (v : P → (Edge L k 0 → ComplexMatrix2) → ComplexMatrix2) (hv : ∀ i, AnalyticRepresentation ρ (v i))
    (hmem : ∀ a, InFormBall ρ a → (fun i => v i a) ∈ W₀) :
    AnalyticRepresentation ρ fun a => Φ fun i => v i a := by
  classical
  choose F hFpos hR using hv
  let F' : Finset (Edge L k 0) := Finset.univ.biUnion F
  have hF' : ∀ b ∈ F', b.IsPositivelyOriented := fun b hb => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hb
    exact hFpos i b hi
  have hR' : ∀ i, AnalyticRepresentationOn ρ F' (v i) := fun i =>
    (hR i).mono (Finset.subset_biUnion_of_mem F (Finset.mem_univ i))
  choose f hf hval using hR'
  let pt : (F' → ComplexMatrix2) → P ⊕ Empty → ComplexMatrix2 :=
    fun A => Sum.elim (fun i => f i A) fun e => e.elim
  have hW : ∀ A ∈ supBall F' ρ, pt A ∈ leftComponents ⁻¹' W₀ := fun A hA => by
    obtain ⟨a, ha, rfl⟩ := exists_form_of_mem_supBall hxor hρ F' hF' hA
    have e : leftComponents (pt fun c : F' => a c) = fun i => v i a :=
      funext fun i => hval i a ha
    show leftComponents _ ∈ W₀
    rw [e]
    exact hmem a ha
  refine ⟨F', hF', fun A => Φ fun i => f i A, fun A hA => ?_, fun a ha => ?_⟩
  · obtain ⟨G, hG, hev⟩ :=
      H P Empty β _ _ (Or.inl (isHolomorphicToCoords_smul_one hΦ)) (pt A) (hW A hA)
    choose g hg hgev using fun i => hf i A hA
    let germPt : (F' → ComplexMatrix2) → P ⊕ Empty → ComplexMatrix2 :=
      fun B => Sum.elim (fun i => g i B) fun e => e.elim
    have hgermPt : AnalyticAt ℂ germPt A := by
      have : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
      rw [analyticAt_pi_iff]
      rintro (i | e)
      · exact hg i
      · exact e.elim
    have hgA : germPt A = pt A := by
      funext s
      rcases s with i | e
      · exact ((hgev i).self_of_nhds hA).symm
      · exact e.elim
    refine ⟨fun B => topLeftEntry (G (germPt B)),
      topLeftEntry.analyticAt _ |>.comp (AnalyticAt.comp (by rwa [hgA]) hgermPt), ?_⟩
    have hcont : ∀ᶠ B in 𝓝 A, germPt B ∈ {w | w ∈ leftComponents ⁻¹' W₀ →
        Φ (leftComponents w) • (1 : ComplexMatrix2) = G w} := by
      apply hgermPt.continuousAt.eventually
      rw [hgA]
      exact hev
    filter_upwards [hcont, eventually_all.2 hgev] with B hB hB' hBball
    have e : germPt B = pt B := by
      funext s
      rcases s with i | e
      · exact (hB' i hBball).symm
      · exact e.elim
    have h₁ := hB (e ▸ hW B hBball)
    rw [← h₁, e]
    show Φ (fun i => f i B) = ((Φ (leftComponents (pt B)) • (1 : ComplexMatrix2)) 0 0)
    simp
    rfl
  · exact congrArg Φ (funext fun i => hval i a ha)
end EvaluationMaps
section Iterates
variable {L k : ℕ} {ρ : ℝ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
def pauliBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.Basis.ofEquivFun OneLoop.pauliCoordinateEquiv
theorem levelwiseMean_eq_some
    (hxor : ∀ (i : ℕ) (b : Edge L k i), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (W : Edge L k 0 → ComplexMatrix2)
    (hW : ∀ j < k, complexIter L k j W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
      ∀ b : Edge L k j, ComplexMatrix2.operatorNorm (complexIter L k j W b - 1) <
        polydiscRadius L / 2) :
    ∀ i ≤ k, ∀ c : Edge L k i, levelwiseMean W i c = some (complexIter L k i W c) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterHolomorphy.levelwiseMean_eq_some_iter <;> assumption
theorem remainderGaugeField_apply (a : Edge L k 0 → ComplexMatrix2) {b : Edge L k 0}
    (hb : b.IsPositivelyOriented) :
    remainderGaugeField a b =
      ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a b)) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterHolomorphy.remainderGaugeField_apply_of_pos <;> assumption
def expFactors (η : ℝ) {σ : Type} (A : σ → ComplexMatrix2) : σ ⊕ Empty → ComplexMatrix2 :=
  asGroupFactors fun s => ComplexMatrix2.matExp (Complex.I • (η • A s))
theorem analyticAt_expFactors (η : ℝ) {σ : Type} [Fintype σ] (A : σ → ComplexMatrix2) :
    AnalyticAt ℂ (expFactors η : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) A := by apply _root_.YangMills.Construction.Tower.FullSpace.IterHolomorphy.analyticAt_expFamily <;> assumption
theorem analyticInCoords_complexIter (H₁ : HolomorphicMatrixAnalyticity)
    (H₂ : SupportOfMeans.SupportOfMeansHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hρ : 0 < ρ) (hk : 1 ≤ k)
    (hP : SmallIterates L k ρ) {j : ℕ} (hj : j ≤ k) (b : Edge L k j) :
    AnalyticRepresentation ρ fun a => complexIter L k j (remainderGaugeField a) b := by
  have hS := (H₂ L hL k hk).2
  have hxor : ∀ (i : ℕ) (c : Edge L k i),
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented :=
    fun i c => xor_isPositivelyOriented_opposite (meshAt_pos hL k i) c
  obtain ⟨hfin, -⟩ := hS.finite_nonempty j hj b
  have hR := hS.dependsOnlyOn j hj b hfin.toFinset hfin.coe_toFinset
  obtain ⟨f₀, hw⟩ := hR.exists_representation
  have hhol := hR.representation_holomorphic f₀ hw
  have hFpos : ∀ c ∈ hfin.toFinset, c.IsPositivelyOriented := fun c hc =>
    (hfin.mem_toFinset.1 hc).1
  have hform : ∀ a : Edge L k 0 → ComplexMatrix2, InFormBall ρ a →
      remainderGaugeField a ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup ∧
        levelwiseMean (remainderGaugeField a) j b =
          some (complexIter L k j (remainderGaugeField a) b) := fun a ha =>
    ⟨(hP a ha.1 ha.2 0 (by omega)).1, levelwiseMean_eq_some hxor _ (hP a ha.1 ha.2) j hj b⟩
  have hval : ∀ a : Edge L k 0 → ComplexMatrix2,
      (fun c : hfin.toFinset => remainderGaugeField a c) =
      fun c : hfin.toFinset => ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a c)) :=
    fun a => by
    funext c
    exact remainderGaugeField_apply a (hFpos _ c.2)
  have hformed : ∀ a : Edge L k 0 → ComplexMatrix2, InFormBall ρ a →
      (fun c : hfin.toFinset => remainderGaugeField a c) ∈
        SupportOfMeans.definedLocus
          (SupportOfMeans.Unbounded.baseFields L k) hfin.toFinset
          (SupportOfMeans.Unbounded.meanAt b) := fun a ha => by
    obtain ⟨hc, hm⟩ := hform a ha
    refine (hR.isSome_iff _ hc).1 ?_
    show (levelwiseMean (remainderGaugeField a) j b).isSome
    rw [hm]
    rfl
  refine ⟨hfin.toFinset, hFpos,
    fun A => f₀ fun c => ComplexMatrix2.matExp (Complex.I • (finestMesh L k • A c)),
    fun A hA => ?_, fun a ha => ?_⟩
  · obtain ⟨β⟩ : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := ⟨pauliBasis⟩
    have hmem : ∀ B ∈ supBall hfin.toFinset ρ,
        (fun c => ComplexMatrix2.matExp (Complex.I • (finestMesh L k • B c))) ∈
          SupportOfMeans.definedLocus
            (SupportOfMeans.Unbounded.baseFields L k) hfin.toFinset
            (SupportOfMeans.Unbounded.meanAt b) := by
      intro B hB
      obtain ⟨a, ha, rfl⟩ := exists_form_of_mem_supBall (hxor 0) hρ hfin.toFinset hFpos hB
      rw [← hval a]
      exact hformed a ha
    obtain ⟨G, hG, hev⟩ := H₁ hfin.toFinset Empty β _ _ (Or.inr (hhol β))
      (expFactors (finestMesh L k) A) ⟨_, hmem A hA, rfl⟩
    refine ⟨fun B => G (expFactors (finestMesh L k) B),
      hG.comp (analyticAt_expFactors _ A), ?_⟩
    have hc := (analyticAt_expFactors (finestMesh L k) A).continuousAt
    filter_upwards [hc.eventually hev] with B hB hBball
    exact hB ⟨_, hmem B hBball, rfl⟩
  · obtain ⟨hc, hm⟩ := hform a ha
    have hv := hw.eq_some _ hc (hformed a ha)
    have hv' : levelwiseMean (remainderGaugeField a) j b =
        some (f₀ fun c => remainderGaugeField a c) := hv
    rw [hm] at hv'
    show f₀ (fun c : hfin.toFinset =>
        ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a c))) =
      complexIter L k j (remainderGaugeField a) b
    rw [Option.some.inj hv', hval a]
end Iterates
structure Hypotheses : Prop where
  analytic : HolomorphicMatrixAnalyticity
  support : SupportOfMeans.SupportOfMeansHolds
  stepBounds : StepKernels.StepKernelBounds
  holomorphy : StepKernelHolomorphy.KernelsHolomorphic
  kernels : ThreeMapKernels.Claim
  polydiscs : DoubleBlockPolydisc.PolydiscsHold
  cubes : BlockStructure
section Step
variable {L k j : ℕ}
def axisZeroLink {a : ℝ} (y : InfiniteLattice.LatticePoint a) : InfiniteLattice.Link a :=
  InfiniteLattice.Link.forwardFrom y 0
theorem axisZeroLink_isPositivelyOriented {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    (axisZeroLink y).IsPositivelyOriented :=
  ⟨0, add_sub_cancel_left _ _⟩
structure IsNearOne (V : Edge L k j → ComplexMatrix2) : Prop where
  field : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup
  near : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2
theorem IsNearOne.radius_pos {V : Edge L k j → ComplexMatrix2} (h : IsNearOne V) :
    0 < polydiscRadius L := by
  have h₀ : 0 ≤ ComplexMatrix2.operatorNorm (V (axisZeroLink 0) - 1) := norm_nonneg _
  have := h.near (axisZeroLink 0)
  linarith
theorem IsNearOne.norm_lt {V : Edge L k j → ComplexMatrix2} (h : IsNearOne V) (b : Edge L k j) :
    ComplexMatrix2.operatorNorm (V b - 1) < 3 / 4 * polydiscRadius L := by
  have := h.radius_pos
  have := h.near b
  linarith
theorem IsNearOne.mem {V : Edge L k j → ComplexMatrix2} (h : IsNearOne V) :
    V ∈ smallComplexFields L k j :=
  ⟨h.field, fun b => by
    have := h.radius_pos
    have := h.near b
    linarith⟩
theorem IsNearOne.polydisc {V : Edge L k j → ComplexMatrix2} (h : IsNearOne V)
    (c : Edge L k (j + 1)) :
    V ∈ nearIdentityPolydisc L k j (3 / 4 * polydiscRadius L) c :=
  ⟨⟨fun b _ => h.field.1 b, fun b _ => h.field.2 b⟩, fun b _ => h.norm_lt b⟩
theorem extendOddly_opposite {a : ℝ} (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem covariantSmoothingDeriv_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (V B : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1)) :
    covariantSmoothingDeriv V B c.opposite = -covariantSmoothingDeriv V B c := by
  show complexSmoothingDeriv V B c.opposite +
      covDiff (smoothingMap L k j V) (contourLogDrift V B) c.opposite =
    -(complexSmoothingDeriv V B c +
      covDiff (smoothingMap L k j V) (contourLogDrift V B) c)
  rw [neg_add]
  congr 1
  · unfold complexSmoothingDeriv holLeftDifferential
    exact extendOddly_opposite (meshAt_pos hL k (j + 1)) _ c
  · unfold covDiff
    exact extendOddly_opposite (meshAt_pos hL k (j + 1)) _ c
theorem singleLink_mem_traceless {V : Edge L k j → ComplexMatrix2} {c : Edge L k (j + 1)}
    (hK : StepKernelsAt V c) {b : Edge L k j} (hb : b ∈ positiveDoubleCubeLinks c)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    covariantSmoothingDeriv V (singleLinkForm b X) c ∈ ComplexMatrix2.traceless := by
  obtain ⟨T, hT, -⟩ := hK.kernel_bound b hb
  have e : covariantSmoothingDeriv V (singleLinkForm b X) c = (T ⟨X, hX⟩ : ComplexMatrix2) :=
    (hT ⟨X, hX⟩).symm
  rw [e]
  exact (T ⟨X, hX⟩).2
theorem covariantSmoothingDeriv_mem_traceless {V : Edge L k j → ComplexMatrix2}
    {c : Edge L k (j + 1)} (hK : StepKernelsAt V c) (hfin : (positiveDoubleCubeLinks c).Finite)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c ∈ ComplexMatrix2.traceless := by
  rw [hK.sum_eq_finsum B hB, finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Submodule.sum_mem _ fun b hb =>
    singleLink_mem_traceless hK (hfin.mem_toFinset.1 hb) (hB.1 b (hfin.mem_toFinset.1 hb).2)
theorem pauliCoeff_covariantSmoothingDeriv {V : Edge L k j → ComplexMatrix2}
    {c : Edge L k (j + 1)} (hK : StepKernelsAt V c) (hfin : (positiveDoubleCubeLinks c).Finite)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) (a' : Fin 3) :
    pauliCoeff a' (covariantSmoothingDeriv V B c) =
      ∑ b ∈ hfin.toFinset, ∑ a, pauliCoeff a (B b) *
        pauliCoeff a'
          (covariantSmoothingDeriv V (singleLinkForm b (ComplexMatrix2.pauliFamily a)) c) := by
  rw [hK.sum_eq_finsum B hB, finsum_mem_eq_finite_toFinset_sum _ hfin,
    pauliCoeff_sum _ _ fun b hb =>
      singleLink_mem_traceless hK (hfin.mem_toFinset.1 hb) (hB.1 b (hfin.mem_toFinset.1 hb).2)]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨T, hT, -⟩ := hK.kernel_bound b (hfin.mem_toFinset.1 hb)
  exact pauliCoeff_linearMap (f := fun X => covariantSmoothingDeriv V (singleLinkForm b X) c) T hT
    (hB.1 b (hfin.mem_toFinset.1 hb).2) a'
theorem conjugateBy_mem_traceless {M : ComplexMatrix2}
    (hM : IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy M) 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy M X ∈ ComplexMatrix2.traceless := by
  obtain ⟨T, hT, -⟩ := hM
  have e : ComplexMatrix2.conjugateBy M X = (T ⟨X, hX⟩ : ComplexMatrix2) := (hT ⟨X, hX⟩).symm
  rw [e]
  exact (T ⟨X, hX⟩).2
theorem adjointCubeAverage_mem_traceless {V : Edge L k j → ComplexMatrix2}
    {y : Vertex L k (j + 1)}
    (hA : ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy (complexContourMean L V y x)) 3)
    (hfin : (cubeVertices L (meshAt L k j) y).Finite) {l : Vertex L k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := by
  unfold adjointCubeAverage
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun x hx =>
    conjugateBy_mem_traceless (hA x (hfin.mem_toFinset.1 hx)) (hl x))
theorem pauliCoeff_adjointCubeAverage {V : Edge L k j → ComplexMatrix2}
    {y : Vertex L k (j + 1)}
    (hA : ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy (complexContourMean L V y x)) 3)
    (hfin : (cubeVertices L (meshAt L k j) y).Finite) {l : Vertex L k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (a' : Fin 3) :
    pauliCoeff a' (adjointCubeAverage V l y) =
      PeriodicLattice.inverseFourthPowerWeight L * ∑ x ∈ hfin.toFinset, ∑ a, pauliCoeff a (l x) *
        pauliCoeff a' (ComplexMatrix2.conjugateBy (complexContourMean L V y x)
          (ComplexMatrix2.pauliFamily a)) := by
  unfold adjointCubeAverage
  have hs : ∀ x ∈ hfin.toFinset,
      ComplexMatrix2.conjugateBy (complexContourMean L V y x) (l x) ∈ ComplexMatrix2.traceless :=
    fun x hx => conjugateBy_mem_traceless (hA x (hfin.mem_toFinset.1 hx)) (hl x)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, pauliCoeff_smul _ (Submodule.sum_mem _ hs),
    pauliCoeff_sum _ _ hs]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨T, hT, -⟩ := hA x (hfin.mem_toFinset.1 hx)
  exact pauliCoeff_linearMap T hT (hl x) a'
end Step
section Products
variable {L k : ℕ} {ρ : ℝ}
theorem isNearOne_complexIter (hP : SmallIterates L k ρ) {a : Edge L k 0 → ComplexMatrix2}
    (ha : InFormBall ρ a) {j : ℕ} (hj : j < k) :
    IsNearOne (complexIter L k j (remainderGaugeField a)) :=
  ⟨(hP a ha.1 ha.2 j hj).1, (hP a ha.1 ha.2 j hj).2⟩
theorem positiveDoubleCubeLinks_finite (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    (positiveDoubleCubeLinks c).Finite :=
  ((G.polydiscs L hL k j hj).2 c hc).finite_open.positive_finite
theorem cubeVertices_finite (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite := by
  have hblocks := G.cubes L k (j + 1) hL (by omega) (by omega) (by omega)
  have hcard := (hblocks.2.1 y).2.2.1
  have hpos : 0 < L ^ 4 := by
    have := hL.2
    positivity
  have hf : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_pos (hcard.symm ▸ hpos)
  exact hf.preimage Subtype.val_injective.injOn
theorem stepKernelsAt_of_nearOne (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (hj : j < k) {V : Edge L k j → ComplexMatrix2} (hV : IsNearOne V)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) : StepKernelsAt V c :=
  G.stepBounds L hL k j hj c hc V hV.field hV.norm_lt
theorem conjBounds_of_nearOne (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (hj : j < k) {V : Edge L k j → ComplexMatrix2} (hV : IsNearOne V)
    (y : Vertex L k (j + 1)) :
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy (complexContourMean L V y x)) 3 :=
  (stepKernelsAt_of_nearOne G hL hj hV (axisZeroLink_isPositivelyOriented y)).conj_bound y
    (Or.inl rfl)
theorem iterCovariantDeriv_mem (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : Edge L k 0 → ComplexMatrix2} (hU : ∀ i < k, IsNearOne (complexIter L k i U))
    {E : Edge L k 0 → ComplexMatrix2} (hE : E ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ j ≤ k, iterCovariantDeriv L k U j E ∈ complexEdgeForms (meshAt L k j) := by
  intro j
  induction j with
  | zero => exact fun _ => hE
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    refine ⟨fun c hc => ?_, fun c => covariantSmoothingDeriv_opposite hL _ _ c⟩
    exact covariantSmoothingDeriv_mem_traceless (stepKernelsAt_of_nearOne G hL hj' (hU j hj') hc)
      (positiveDoubleCubeLinks_finite G hL hj' hc) (ih hj'.le)
theorem iterAdjointCubeAverage_mem (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : Edge L k 0 → ComplexMatrix2} (hU : ∀ i < k, IsNearOne (complexIter L k i U))
    {l : Vertex L k 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ∀ j ≤ k, ∀ x, iterAdjointCubeAverage L k U j l x ∈ ComplexMatrix2.traceless := by
  intro j
  induction j with
  | zero => exact fun _ => hl
  | succ j ih =>
    intro hj y
    have hj' : j < k := hj
    exact adjointCubeAverage_mem_traceless (conjBounds_of_nearOne G hL hj' (hU j hj') y)
      (cubeVertices_finite G hL hj' y) (ih hj'.le)
theorem analyticInCoords_of_holomorphicInValues (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hρ : 0 < ρ) (hk : 1 ≤ k)
    (hP : SmallIterates L k ρ) {j : ℕ} (hj : j < k) {c : Edge L k (j + 1)}
    (h : (Edge L k j → ComplexMatrix2) → ℂ)
    (hh : IsHolomorphicInValues (3 / 4 * polydiscRadius L) c h)
    (hr : DependsOnlyOnDoubleBlock (3 / 4 * polydiscRadius L) c h) :
    AnalyticRepresentation ρ fun a : Edge L k 0 → ComplexMatrix2 =>
      h (complexIter L k j (remainderGaugeField a)) := by
  obtain ⟨inst, hh⟩ := hh
  obtain ⟨β⟩ : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := ⟨pauliBasis⟩
  have hc := AnalyticRepresentation.comp_holomorphic (L := L) (k := k) (ρ := ρ) G.analytic
    (fun b => xor_isPositivelyOriented_opposite (meshAt_pos hL k 0) b) hρ β
    (polydiscPositive L k j (3 / 4 * polydiscRadius L) c)
    (fun v => h (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v)) (hh β)
    (fun i a => complexIter L k j (remainderGaugeField a) i.1)
    (fun i => analyticInCoords_complexIter G.analytic G.support hL hρ hk hP hj.le i.1)
    (fun a ha => ⟨_, ⟨_, (isNearOne_complexIter hP ha hj).polydisc c, rfl⟩, rfl⟩)
  refine hc.congr fun a ha => ?_
  exact hr _ (isNearOne_complexIter hP ha hj).mem ((isNearOne_complexIter hP ha hj).polydisc c)
theorem analyticInCoords_pauliCoeff_iterCovariantDeriv (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hρ : 0 < ρ)
    (hk : 1 ≤ k) (hP : SmallIterates L k ρ) {E : Edge L k 0 → ComplexMatrix2}
    (hE : E ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ j ≤ k, ∀ c : Edge L k j, c.IsPositivelyOriented → ∀ a' : Fin 3,
      AnalyticRepresentation ρ fun a : Edge L k 0 → ComplexMatrix2 => pauliCoeff a'
        (iterCovariantDeriv L k (remainderGaugeField a) j E c) := by
  intro j
  induction j with
  | zero => exact fun _ c _ a' => AnalyticRepresentation.const (pauliCoeff a' (E c))
  | succ j ih =>
    intro hj c hc a'
    have hj' : j < k := hj
    have hfin := positiveDoubleCubeLinks_finite G hL hj' hc
    have hH := G.holomorphy L hL k j hj' c hc
    have hterm : ∀ b ∈ hfin.toFinset, ∀ a : Fin 3,
        AnalyticRepresentation ρ fun ā : Edge L k 0 → ComplexMatrix2 => pauliCoeff a'
          (covariantSmoothingDeriv (complexIter L k j (remainderGaugeField ā))
            (singleLinkForm b (ComplexMatrix2.pauliFamily a)) c) := fun b hb a => by
      have hbP := hfin.mem_toFinset.1 hb
      exact analyticInCoords_of_holomorphicInValues G hL hρ hk hP hj'
        (fun V => kernelCoeff V c ⟨b, hbP.2⟩ a a')
        (hH.holomorphic_kernel ⟨b, hbP.2⟩ hbP.1 a a') (hH.local_kernel ⟨b, hbP.2⟩ hbP.1 a a')
    refine (AnalyticRepresentation.sum hfin.toFinset fun b hb =>
      AnalyticRepresentation.sum Finset.univ fun a _ =>
        (ih hj'.le b (hfin.mem_toFinset.1 hb).2 a).mul (hterm b hb a)).congr fun ā hā => ?_
    exact pauliCoeff_covariantSmoothingDeriv
      (stepKernelsAt_of_nearOne G hL hj' (isNearOne_complexIter hP hā hj') hc) hfin
      (iterCovariantDeriv_mem G hL (fun i hi => isNearOne_complexIter hP hā hi) hE j hj'.le) a'
theorem analyticInCoords_pauliCoeff_iterAdjointCubeAverage (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hρ : 0 < ρ)
    (hk : 1 ≤ k) (hP : SmallIterates L k ρ) {l : Vertex L k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ∀ j ≤ k, ∀ (y : Vertex L k j) (a' : Fin 3),
      AnalyticRepresentation ρ fun a : Edge L k 0 → ComplexMatrix2 => pauliCoeff a'
        (iterAdjointCubeAverage L k (remainderGaugeField a) j l y) := by
  intro j
  induction j with
  | zero => exact fun _ y a' => AnalyticRepresentation.const (pauliCoeff a' (l y))
  | succ j ih =>
    intro hj y a'
    have hj' : j < k := hj
    have hfin := cubeVertices_finite G hL hj' y
    have hH := G.holomorphy L hL k j hj' (axisZeroLink y) (axisZeroLink_isPositivelyOriented y)
    have hterm : ∀ x ∈ hfin.toFinset, ∀ a : Fin 3,
        AnalyticRepresentation ρ fun ā : Edge L k 0 → ComplexMatrix2 => pauliCoeff a'
          (ComplexMatrix2.conjugateBy
            (complexContourMean L (complexIter L k j (remainderGaugeField ā)) y x)
            (ComplexMatrix2.pauliFamily a)) := fun x hx a => by
      have hxB := hfin.mem_toFinset.1 hx
      exact analyticInCoords_of_holomorphicInValues G hL hρ hk hP hj' (c := axisZeroLink y)
        (fun V => contourConjCoeff V y x a a')
        (hH.holomorphic_conj y (Or.inl rfl) x hxB a a')
        (hH.local_conj y (Or.inl rfl) x hxB a a')
    refine ((AnalyticRepresentation.const (PeriodicLattice.inverseFourthPowerWeight L)).mul
      (AnalyticRepresentation.sum hfin.toFinset fun x hx => AnalyticRepresentation.sum Finset.univ fun a _ =>
        (ih hj'.le x a).mul (hterm x hx a))).congr fun ā hā => ?_
    exact pauliCoeff_adjointCubeAverage
      (conjBounds_of_nearOne G hL hj' (isNearOne_complexIter hP hā hj') y) hfin
      (iterAdjointCubeAverage_mem G hL (fun i hi => isNearOne_complexIter hP hā hi) hl j hj'.le) a'
def indicatorAt {N : Type} (ι : N) : N → ℂ := open Classical in fun i => if i = ι then 1 else 0
theorem applyKernel_indicatorAt {N N' : Type} (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (indicatorAt ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem ofCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : (edgePauliCoordinates L k 0).Index → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs f ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.ofCoeffs_mem_complexEdgeForms <;> assumption
theorem Q_apply (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (hsmall : ∀ i < k, IsNearOne (complexIter L k i U))
    (ι' : Fin 3 × PositiveEdge (meshAt L k k))
    (ι : Fin 3 × PositiveEdge (meshAt L k 0)) :
    (rescaledOperators L k U).Q ι' ι = ((finestMesh L k : ℝ) : ℂ) * pauliCoeff ι'.1
      (iterCovariantDeriv L k U k ((edgePauliCoordinates L k 0).ofCoeffs (indicatorAt ι)) ι'.2.1) := by
  have hQ := ((G.kernels L hL k hk).2.2.2.2 U hU).1
  have hval : ∀ (f : (edgePauliCoordinates L k 0).Index → ℂ) (ι'' : (edgePauliCoordinates L k k).Index),
      pauliCoeff ι''.1 ((finestMesh L k • iterCovariantDeriv L k U k
          ((edgePauliCoordinates L k 0).ofCoeffs f)) ι''.2.1) =
        ((finestMesh L k : ℝ) : ℂ) * pauliCoeff ι''.1
          (iterCovariantDeriv L k U k ((edgePauliCoordinates L k 0).ofCoeffs f) ι''.2.1) :=
    fun f ι'' => pauliCoeff_real_smul _
      ((iterCovariantDeriv_mem G hL hsmall (ofCoeffs_mem hL f) k le_rfl).1 _ ι''.2.2) _
  have hM : ((finestMesh L k : ℝ) : ℂ) • (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k)
        (iterCovariantDeriv L k U k) =
      (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k)
        fun B => finestMesh L k • iterCovariantDeriv L k U k B := by
    funext f ι''
    exact (hval f ι'').symm
  have hg : Represents ((edgePauliCoordinates L k 0).kernel (edgePauliCoordinates L k k)
        fun B => finestMesh L k • iterCovariantDeriv L k U k B)
      ((edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k)
        fun B => finestMesh L k • iterCovariantDeriv L k U k B) :=
    Classical.epsilon_spec (p := fun T => Represents T ((edgePauliCoordinates L k 0).mapOnCoeffs
      (edgePauliCoordinates L k k) fun B => finestMesh L k • iterCovariantDeriv L k U k B))
      ⟨_, hM ▸ hQ.smul_represents _⟩
  have e := applyKernel_indicatorAt ((edgePauliCoordinates L k 0).kernel (edgePauliCoordinates L k k)
    fun B => finestMesh L k • iterCovariantDeriv L k U k B) ι ι'
  rw [(hg _).2] at e
  exact e.symm.trans (hval _ ι')
theorem R_apply (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (ι' : Fin 3 × Vertex L k k) (ι : Fin 3 × Vertex L k 0) :
    (rescaledOperators L k U).R ι' ι = pauliCoeff ι'.1
      (iterAdjointCubeAverage L k U k (ofPauliCoeffs (indicatorAt ι)) ι'.2) := by
  have hR := ((G.kernels L hL k hk).2.2.2.2 U hU).2
  have e := applyKernel_indicatorAt ((vertexCoordinate (Vertex L k 0)).kernel
    (vertexCoordinate (Vertex L k k)) (iterAdjointCubeAverage L k U k)) ι ι'
  rw [(hR.represents _).2] at e
  exact e.symm
theorem remainderGaugeField_mem_smallIterateFields (hP : SmallIterates L k ρ) (hk : 1 ≤ k)
    {a : Edge L k 0 → ComplexMatrix2} (ha : InFormBall ρ a) :
    remainderGaugeField a ∈ smallIterateFields L k :=
  ⟨(hP a ha.1 ha.2 0 (by omega)).1, fun _ hi => (isNearOne_complexIter hP ha hi).mem⟩
end Products
theorem kernelEntriesHolomorphic_holds (H₁ : HolomorphicMatrixAnalyticity)
    (H₂ : SupportOfMeans.SupportOfMeansHolds)
    (H₃ : StepKernels.StepKernelBounds)
    (H₄ : StepKernelHolomorphy.KernelsHolomorphic) (H₅ : ThreeMapKernels.Claim)
    (H₆ : DoubleBlockPolydisc.PolydiscsHold) (H₇ : BlockStructure) :
    KernelEntriesHolomorphic := by
  have G : Hypotheses := ⟨H₁, H₂, H₃, H₄, H₅, H₆, H₇⟩
  intro L hL ρ hρ k hk hP
  refine ⟨fun ι' ι => ?_, fun ι' ι => ?_⟩
  · have hr : AnalyticRepresentation (L := L) (k := k) ρ fun a : Edge L k 0 → ComplexMatrix2 =>
        (rescaledOperators L k (remainderGaugeField a)).Q ι' ι :=
      ((AnalyticRepresentation.const _).mul
        (analyticInCoords_pauliCoeff_iterCovariantDeriv G hL hρ hk hP (ofCoeffs_mem hL _) k le_rfl
          ι'.2.1 ι'.2.2 ι'.1)).congr fun a ha =>
        Q_apply G hL hk (remainderGaugeField_mem_smallIterateFields hP hk ha)
          (fun _ hi => isNearOne_complexIter hP ha hi) ι' ι
    obtain ⟨F, -, f, hf, hv⟩ := hr
    exact ⟨F, f, fun β => isHolomorphicOnTraceless_of_locallyAnalytic β ρ f hf,
      fun a ha hs => hv a ⟨ha, hs⟩⟩
  · have hr : AnalyticRepresentation (L := L) (k := k) ρ fun a : Edge L k 0 → ComplexMatrix2 =>
        (rescaledOperators L k (remainderGaugeField a)).R ι' ι :=
      (analyticInCoords_pauliCoeff_iterAdjointCubeAverage G hL hρ hk hP
        (l := ofPauliCoeffs (indicatorAt ι)) (fun x => pauli_combination_mem_traceless _) k le_rfl
        ι'.2 ι'.1).congr fun a ha =>
          R_apply G hL hk (remainderGaugeField_mem_smallIterateFields hP hk ha) ι' ι
    obtain ⟨F, -, f, hf, hv⟩ := hr
    exact ⟨F, f, fun β => isHolomorphicOnTraceless_of_locallyAnalytic β ρ f hf,
      fun a ha hs => hv a ⟨ha, hs⟩⟩
end YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels
end
