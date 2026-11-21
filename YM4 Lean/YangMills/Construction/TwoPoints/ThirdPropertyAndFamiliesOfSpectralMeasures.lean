import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import YangMills.Construction.TwoPoints.SpectralMeasuresInTheEightFrames
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction
open SpectralCalculus
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
abbrev realCc1In {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (O : Set X) :
    Submodule ℝ (X → ℂ) :=
  realValuedPart (cc1In O)
def rotateFun {E : Type*} (R : Matrix.orthogonalGroup (Fin 4) ℝ) (f : AmbientSpace → E) :
    AmbientSpace → E :=
  fun x => f (((R⁻¹ : Matrix.orthogonalGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).mulVec x)
def derivUniformNorm (f : ℝ → ℂ) : ℝ := TestFunctions.uniformNorm (deriv f)
def gradPlane (f : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : Fin 2 → ℂ :=
  fun i => fderiv ℝ f y (Pi.single i 1)
def gradPlaneNorm (f : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, ‖gradPlane f y i‖ ^ 2)
def gradPlaneEsup (f : (Fin 2 → ℝ) → ℂ) : ℝ≥0∞ :=
  ⨆ y, ENNReal.ofReal (gradPlaneNorm f y)
def gradPlaneSup (f : (Fin 2 → ℝ) → ℂ) : ℝ := (gradPlaneEsup f).toReal
def ofRealFun (f : AmbientSpace → ℝ) : AmbientSpace → ℂ := fun x => (f x : ℂ)
structure IsSmallPositiveWith (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (ϑ r : ℝ) (u : ℝ → ℝ) : Prop where
  radius_pos : 0 < r
  rate_pos : ∀ d ∈ Ioc 0 r, 0 < u d
  rate_tendsto : Tendsto u (𝓝[>] 0) (𝓝 0)
  nonneg : ∀ d ∈ Ioc 0 r, ∀ p ∈ TestFunctions.separatedPairsR4 d ϑ,
    ofRealFun p.1 ∈ compactC1Real → ofRealFun p.2 ∈ compactC1Real →
      0 ≤ S (ofRealFun p.1) (ofRealFun p.2)
  le_rate : ∀ d ∈ Ioc 0 r, ∀ p ∈ TestFunctions.separatedPairsR4 d ϑ,
    ofRealFun p.1 ∈ compactC1Real → ofRealFun p.2 ∈ compactC1Real →
      S (ofRealFun p.1) (ofRealFun p.2) ≤
        u d * TestFunctions.uniformNorm p.1 * TestFunctions.uniformNorm p.2
def IsSmallPositiveAtShape (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (ϑ : ℝ) : Prop :=
  ∃ (r : ℝ) (u : ℝ → ℝ), IsSmallPositiveWith S ϑ r u
abbrev temporalClass (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (f : halfSpaceDomain (coordVec 3)) : ReflectedSpace S (coordVec 3) :=
  reflectedClass S (coordVec 3) f
structure IsSpectralFamily (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (ρ : planeReflectionNormals → Measure SpectralPlane) : Prop where
  decay : ∀ m : planeReflectionNormals, RepresentsDecay S φ m (ρ m)
  plate_norm : ∀ m : planeReflectionNormals, RepresentsPlateNorm S φ m (ρ m)
theorem coordVec_three_mem_planeReflectionNormals : coordVec 3 ∈ planeReflectionNormals := by
  refine ⟨Or.inl ⟨3, 1, Or.inl rfl, by simp⟩, ?_⟩
  funext i
  fin_cases i <;> simp [transCoords, coordVec]
def axialMeasure (ρ : planeReflectionNormals → Measure SpectralPlane) : Measure SpectralPlane :=
  ρ ⟨coordVec 3, coordVec_three_mem_planeReflectionNormals⟩
def IsHolomorphicOnOne (O : Set ℂ) (F : ℂ → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
    (Equiv.funUnique (Fin 1) ℂ).symm O F
def rightHalfPlaneLog (w : ℂ) : ℂ :=
  (Real.log ‖w‖ : ℂ) + Complex.I * (Real.arctan (w.im / w.re) : ℂ)
theorem rightHalfPlaneLog_eq_log {w : ℂ} (hw : 0 < w.re) : rightHalfPlaneLog w = Complex.log w := by
  have harg : Real.arctan (w.im / w.re) = Complex.arg w := by
    rw [← Complex.tan_arg w]
    exact Real.arctan_tan (by
      have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
      exact (abs_lt.mp this).1) (by
      have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
      exact (abs_lt.mp this).2)
  rw [rightHalfPlaneLog, harg, Complex.log, mul_comm Complex.I]
end TwoPoints
end YangMills.Construction
end
