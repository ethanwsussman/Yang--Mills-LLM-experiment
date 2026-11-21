import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
abbrev LinkEntry (a : ℝ) : Type := positiveLinkSet a × Fin 2 × Fin 2
def entryRe (e : LinkEntry a) (U : GaugeField a) : ℝ :=
  ((U e.1.1 : Matrices.ComplexMatrix2) e.2.1 e.2.2).re
def entryIm (e : LinkEntry a) (U : GaugeField a) : ℝ :=
  ((U e.1.1 : Matrices.ComplexMatrix2) e.2.1 e.2.2).im
def entryCoord : LinkEntry a ⊕ LinkEntry a → GaugeField a → ℝ :=
  Sum.elim entryRe entryIm
def ratPolyObservables (a : ℝ) : Set (GaugeField a → ℝ) :=
  {F | ∃ p : MvPolynomial (LinkEntry a ⊕ LinkEntry a) ℚ,
    ∀ U, F U = MvPolynomial.aeval (fun g => entryCoord g U) p}
def complexRatPolyObservables (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | ∃ F₁ ∈ ratPolyObservables a, ∃ F₂ ∈ ratPolyObservables a,
    ∀ U, F U = (F₁ U : ℂ) + Complex.I * (F₂ U : ℂ)}
abbrev StateL2 (ν : GaugeFieldProbability a) : Type := Lp ℂ 2 ν.1
def stateL2Norm (ν : GaugeFieldProbability a) (φ : GaugeField a → ℂ) : ℝ :=
  (∫ U, ‖φ U‖ ^ 2 ∂ν.1) ^ (1 / 2 : ℝ)
theorem norm_stateL2 (ν : GaugeFieldProbability a)
    (φ : StateL2 ν) : ‖φ‖ = stateL2Norm ν φ := by
  have h : ‖φ‖ ^ 2 = ∫ U, ‖φ U‖ ^ 2 ∂ν.1 := by
    have hi : ‖φ‖ ^ 2 = RCLike.re ⟪φ, φ⟫_ℂ := norm_sq_eq_re_inner φ
    rw [hi, L2.inner_def]
    have hp : ∀ U, ⟪(φ : GaugeField a → ℂ) U, (φ : GaugeField a → ℂ) U⟫_ℂ =
        ((‖φ U‖ ^ 2 : ℝ) : ℂ) := fun U => by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    simp only [hp]
    rw [integral_complex_ofReal]
    simp
  rw [stateL2Norm, ← h, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
def latticePointOfInt (a : ℝ) (z : Fin 4 → ℤ) : LatticePoint a :=
  ⟨fun μ => (z μ : ℝ) * a, z, fun _ => rfl⟩
open Classical in
def cornerCube (a : ℝ) (n : ℕ) : Finset (LatticePoint a) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (0 : ℤ) ((n : ℤ) - 1)).image (latticePointOfInt a)
theorem card_cornerCube (ha : a ≠ 0) (n : ℕ) : (cornerCube a n).card = n ^ 4 := by
  classical
  have hinj : Function.Injective (latticePointOfInt a) := fun z z' h => by
    funext μ
    have hμ := congrFun (congrArg Subtype.val h) μ
    simpa [latticePointOfInt, ha] using hμ
  rw [cornerCube, Finset.card_image_of_injective _ hinj, Fintype.card_piFinset]
  simp
def cornerCubeAverage (n : ℕ) (F : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => ((n : ℂ) ^ 4)⁻¹ * ∑ y ∈ cornerCube a n, (shift y).actOn F U
end YangMills.Construction.InfiniteLattice
