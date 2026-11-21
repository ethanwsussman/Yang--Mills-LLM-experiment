import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.WightmanReconstruction.SmoothToolkit
def vecLength {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)
def IsUnitVec {d : ℕ} (e : Fin d → ℝ) : Prop := vecLength e = 1
def ExistsMollifier : Prop := ∃ j, IsStandardMollifier j
def IsSmoothStepFunction (g : ℝ → ℝ) : Prop :=
  g ∈ smoothMaps ℝ ℝ ∧ (∀ t, 0 ≤ g t ∧ g t ≤ 1) ∧ (∀ t, t ≤ 1 → g t = 0) ∧
    ∀ t, 2 ≤ t → g t = 1
def IsBallCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (len : E → ℝ)
    (f : E → ℝ) : Prop :=
  f ∈ TestSpaces.smoothCompactSupp (Set.univ : Set E) ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    (∀ x, len x ≤ 1 → f x = 1) ∧ ∀ x, 2 ≤ len x → f x = 0
def ballCutoffVec (g : ℝ → ℝ) (d : ℕ) (x : Fin d → ℝ) : ℝ := 1 - g (vecLength x ^ 2)
def ballCutoffTuple (g : ℝ → ℝ) (n : ℕ) (x : TestSpaces.PointTuple n) : ℝ :=
  1 - g (TestSpaces.tupleNorm x ^ 2)
def lineCutoff (g : ℝ → ℝ) (t : ℝ) : ℝ := 1 - g (4 * t ^ 2)
def CutoffsOfSmoothStep : Prop :=
  (∃ g, IsSmoothStepFunction g) ∧
    ∀ g, IsSmoothStepFunction g →
      (∀ d : ℕ, 1 ≤ d → IsBallCutoff vecLength (ballCutoffVec g d)) ∧
      (∀ n : ℕ, 1 ≤ n → IsBallCutoff TestSpaces.tupleNorm (ballCutoffTuple g n)) ∧
      lineCutoff g ∈ TestSpaces.smoothCompactSupp (Set.univ : Set ℝ) ∧
      (∀ t, 0 ≤ lineCutoff g t ∧ lineCutoff g t ≤ 1) ∧
      (∀ t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), lineCutoff g t = 1) ∧
      ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → lineCutoff g t = 0
def openBox4 (lo hi : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi Set.univ fun μ => Set.Ioo (lo μ) (hi μ)
def BoxIndicatorIsPointwiseLimit : Prop :=
  ∀ lo hi : Fin 4 → ℝ, (∀ μ, lo μ < hi μ) →
    ∃ h : ℕ → (Fin 4 → ℝ) → ℝ,
      (∀ j, 1 ≤ j → h j ∈ TestSpaces.smoothCompactSupp (Set.univ : Set (Fin 4 → ℝ)) ∧
        ∀ x, 0 ≤ h j x ∧ h j x ≤ 1) ∧
      ∀ x, Tendsto (fun j => h j x) atTop (𝓝 ((openBox4 lo hi).indicator (fun _ => (1 : ℝ)) x))
def IsSmoothPartitionOfUnityOn {n r : ℕ} (K : Set (TestSpaces.PointTuple n))
    (U : Fin r → Set (TestSpaces.PointTuple n)) (χ : Fin r → TestSpaces.PointTuple n → ℝ) : Prop :=
  (∀ i, χ i ∈ TestSpaces.smoothCompactSupp (U i)) ∧
    ∃ N : Set (TestSpaces.PointTuple n), IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∑ i, χ i x = 1
def ExistsSmoothPartitionOfUnity : Prop :=
  ∀ n r : ℕ, 1 ≤ n → 1 ≤ r → ∀ (K : Set (TestSpaces.PointTuple n))
    (U : Fin r → Set (TestSpaces.PointTuple n)),
    IsCompact K → (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
      ∃ χ, IsSmoothPartitionOfUnityOn K U χ
def ContinuousOrthogonalToTestVanishes : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (U : Set (TestSpaces.PointTuple n)) (u : TestSpaces.PointTuple n → ℂ),
    IsOpen U → ContinuousOn u U →
    (∀ h : TestSpaces.PointTuple n → ℝ, h ∈ TestSpaces.smoothCompactSupp U →
      ∫ x, (h x : ℂ) * u x = 0) →
      ∀ x ∈ U, u x = 0
def planeRotation {d : ℕ} (e w : Fin d → ℝ) (θ : ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := x + (Real.cos θ - 1) • ((e ⬝ᵥ x) • e + (w ⬝ᵥ x) • w) +
    Real.sin θ • ((e ⬝ᵥ x) • w - (w ⬝ᵥ x) • e)
  map_add' x y := by
    simp only [dotProduct_add, add_smul, smul_add, smul_sub]
    abel
  map_smul' c x := by
    simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_add, smul_sub, mul_smul]
    rw [smul_comm (Real.cos θ - 1) c, smul_comm (Real.cos θ - 1) c, smul_comm (Real.sin θ) c,
      smul_comm (Real.sin θ) c]
def PlaneRotationsAndTransitivity : Prop :=
  ∀ d : ℕ, d = 3 ∨ d = 4 →
    (∀ (e w : Fin d → ℝ) (θ : ℝ), IsUnitVec e → IsUnitVec w → e ⬝ᵥ w = 0 →
      LinearMap.toMatrix' (planeRotation e w θ) ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ ∧
        planeRotation e w θ e = Real.cos θ • e + Real.sin θ • w) ∧
    ∀ e e' : Fin d → ℝ, IsUnitVec e → IsUnitVec e' →
      ∃ R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ, R.mulVec e = e'
def ExistsUnitVecNotOrthogonal : Prop :=
  ∀ (r : ℕ) (y : Fin r → Fin 4 → ℝ), (∀ i, y i ≠ 0) →
    ∃ e : Fin 4 → ℝ, IsUnitVec e ∧ ∀ i, e ⬝ᵥ y i ≠ 0
def SchwartzIntegrable : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ φ ∈ TestSpaces.schwartzSet n,
    Integrable φ ∧
      ENNReal.ofReal (lOneNorm φ) ≤
        TestSpaces.weightIntegral 5 ^ n * TestSpaces.weightedSeminorm (5 * n) φ
def Toolkit : Prop :=
  ExistsMollifier ∧ CutoffsOfSmoothStep ∧ BoxIndicatorIsPointwiseLimit ∧
    ExistsSmoothPartitionOfUnity ∧ ContinuousOrthogonalToTestVanishes ∧
    PlaneRotationsAndTransitivity ∧ ExistsUnitVecNotOrthogonal ∧ SchwartzIntegrable
end YangMills.Construction.WightmanReconstruction.SmoothToolkit
end
