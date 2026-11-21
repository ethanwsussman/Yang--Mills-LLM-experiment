import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
instance : MeasurableSpace Matrices.ComplexMatrix2 := borel Matrices.ComplexMatrix2
instance : BorelSpace Matrices.ComplexMatrix2 := ⟨rfl⟩
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def dualLatticePoints (L m : ℕ) (j : ℤ) : Set (FourTorus L m) :=
  {x | ∃ k : Fin 4 → ℤ, ∀ μ,
    x μ = ((((k μ : ℝ) + 1 / 2) * meshSize L j : ℝ) : AddCircle (torusSide L m))}
def centerDiagonalPoint (L m : ℕ) : FourTorus L m :=
  fun _ => (((1 / 2 : ℝ) * (L : ℝ) ^ m : ℝ) : AddCircle (torusSide L m))
def plaquetteCost (U : Bond L m j → Matrices.ComplexMatrix2) (p : Plaquette L m j) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re
def wilsonAction (U : Bond L m j → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ p : Plaquette L m j, plaquetteCost U p
def boltzmannWeight (β : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) : ℝ :=
  Real.exp (-β * wilsonAction U)
def productHaarMeasure (L m : ℕ) (j : ℤ) : Measure (Bond L m j → Matrices.ComplexMatrix2) :=
  (gaugeFieldHaar L m j).map gaugeFieldOfPositive
def partitionFunction (L m K : ℕ) (β : ℝ) : ℝ :=
  ∫ U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2, boltzmannWeight β U ∂productHaarMeasure L m (K : ℤ)
def wilsonGibbsMeasure (L m K : ℕ) (β : ℝ) : Measure (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) :=
  (ENNReal.ofReal (partitionFunction L m K β))⁻¹ •
    (productHaarMeasure L m (K : ℤ)).withDensity fun U => ENNReal.ofReal (boltzmannWeight β U)
def gibbsExpectation (L m K : ℕ) (β : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → E) : E :=
  ∫ U, F U ∂wilsonGibbsMeasure L m K β
def IsFlatIsometry (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ x y, TorusMetric.torusEuclidNorm (σ x - σ y) = TorusMetric.torusEuclidNorm (x - y)
def IsSublatticeIsometry (j : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  IsFlatIsometry σ ∧ σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j
def bondPreimage (σ : FourTorus L m ≃ FourTorus L m) (b : Bond L m j) : Bond L m j :=
  open Classical in
  if h : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = σ.symm b.source ∧
      (b'.target : FourTorus L m) = σ.symm b.target then h.choose else b
def transportGaugeField (σ : FourTorus L m ≃ FourTorus L m) (U : Bond L m j → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  fun b => U (bondPreimage σ b)
def transportObservable {E : Type*} (σ : FourTorus L m ≃ FourTorus L m)
    (F : (Bond L m j → Matrices.ComplexMatrix2) → E) : (Bond L m j → Matrices.ComplexMatrix2) → E :=
  fun U => F (transportGaugeField σ.symm U)
def translateBy (v : Site L m j) : FourTorus L m ≃ FourTorus L m := Equiv.addRight (v : FourTorus L m)
def signedCoordinatePerm (L m : ℕ) (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    FourTorus L m ≃ FourTorus L m where
  toFun x μ := (s μ : ℤ) • x (π μ)
  invFun x ν := (s (π.symm ν) : ℤ) • x (π.symm ν)
  left_inv x := by
    funext ν
    simp [smul_smul, ← Units.val_mul]
  right_inv x := by
    funext μ
    simp [smul_smul, ← Units.val_mul]
def hyperoctahedralGroup (L m : ℕ) : Subgroup (Equiv.Perm (FourTorus L m)) where
  carrier := {σ | ∃ π s, σ = signedCoordinatePerm L m π s}
  mul_mem' := by
    rintro _ _ ⟨π, s, rfl⟩ ⟨π', s', rfl⟩
    refine ⟨π' * π, fun μ => s μ * s' (π μ), ?_⟩
    ext x μ
    simp [signedCoordinatePerm, smul_smul]
  one_mem' := ⟨1, fun _ => 1, by ext x μ; simp [signedCoordinatePerm]⟩
  inv_mem' := by
    rintro _ ⟨π, s, rfl⟩
    refine ⟨π⁻¹, fun ν => s (π.symm ν), ?_⟩
    ext x ν
    rfl
end PeriodicLattice
namespace Cumulants
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def momentGeneratingFunction (ν : Measure Ω) (X : Fin n → Ω → ℝ) (t : Fin n → ℂ) : ℂ :=
  ∫ ω, Complex.exp (∑ i, t i * (X i ω : ℂ)) ∂ν
def mixedCumulant (ν : Measure Ω) (X : Fin n → Ω → ℝ) : ℂ :=
  iteratedFDeriv ℂ n (fun t => Complex.log (momentGeneratingFunction ν X t)) 0
    fun i => Pi.single i 1
end Cumulants
namespace PeriodicLattice
def gibbsCumulant (L m K : ℕ) (β : ℝ) {n : ℕ}
    (X : Fin n → (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → ℝ) : ℂ :=
  Cumulants.mixedCumulant (wilsonGibbsMeasure L m K β) X
end PeriodicLattice
end YangMills.Construction
