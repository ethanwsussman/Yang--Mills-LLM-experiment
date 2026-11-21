import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Torus.TransportRadiusAndMotionsOfFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace AxisReflection
open TorusMetric TorusPeriodization
def coordReflect (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x + (2 * (c - x μ)) • (Pi.single μ 1 : Fin 4 → ℝ)
theorem coordReflect_apply_same (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    coordReflect μ c x μ = 2 * c - x μ := by
  simp only [coordReflect, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  ring
theorem coordReflect_apply_ne {μ ν : Fin 4} (hν : ν ≠ μ) (c : ℝ) (x : Fin 4 → ℝ) :
    coordReflect μ c x ν = x ν := by
  simp [coordReflect, Pi.single_eq_of_ne hν]
def axisSigns (μ : Fin 4) : Fin 4 → ℤˣ := Function.update 1 μ (-1)
def axisSignMatrix (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun ν => ((axisSigns μ ν : ℤ) : ℝ)
theorem axisSignMatrix_mulVec (μ : Fin 4) (x : Fin 4 → ℝ) :
    (axisSignMatrix μ).mulVec x = PeriodicLattice.CutoffTorus.signedPermEuclidean 1 (axisSigns μ) x := by
  funext ν
  simp [axisSignMatrix, Matrix.mulVec_diagonal, PeriodicLattice.CutoffTorus.signedPermEuclidean]
theorem coordReflect_eq_affine (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    coordReflect μ c x = (axisSignMatrix μ).mulVec x + (2 * c) • (Pi.single μ 1 : Fin 4 → ℝ) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [coordReflect_apply_same, axisSignMatrix, Matrix.mulVec_diagonal, axisSigns]
    ring
  · simp [coordReflect_apply_ne hν, axisSignMatrix, Matrix.mulVec_diagonal, axisSigns,
      Function.update_of_ne hν, Pi.single_eq_of_ne hν]
theorem coordReflect_involutive (μ : Fin 4) (c : ℝ) : Function.Involutive (coordReflect μ c) := by
  intro x
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [coordReflect_apply_same, coordReflect_apply_same]
    ring
  · rw [coordReflect_apply_ne hν, coordReflect_apply_ne hν]
def coordReflectMotion (μ : Fin 4) (c : ℝ) : euclideanMotions :=
  ⟨(coordReflect_involutive μ c).toPerm, 1, axisSigns μ, (2 * c) • (Pi.single μ 1 : Fin 4 → ℝ), fun x => by
    rw [← axisSignMatrix_mulVec]
    exact coordReflect_eq_affine μ c x⟩
def torusCoordReflect (ℓ : ℝ) (μ : Fin 4) (c : ℝ) : Equiv.Perm (Torus4 ℓ) :=
  torusMotion ℓ (coordReflectMotion μ c)
theorem torusCoordReflect_torusProj (ℓ : ℝ) (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    torusCoordReflect ℓ μ c (torusProj ℓ x) = torusProj ℓ (coordReflect μ c x) :=
  torusMotion_torusProj ℓ (coordReflectMotion μ c) x
def upperHalf (ℓ : ℝ) (μ : Fin 4) (c : ℝ) : Set (Torus4 ℓ) :=
  torusProj ℓ '' {x | c < x μ ∧ x μ < c + ℓ / 2}
theorem torusCoordReflect_eq_reflectEquiv {L m : ℕ} {j : ℤ}
    (M : InfiniteLattice.PeriodicMirror L m j) :
    torusCoordReflect (PeriodicLattice.torusSide L m) M.axis M.level = M.reflectEquiv := by
  ext1 u
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  rw [torusCoordReflect_torusProj, M.reflectEquiv_torusProj]
  congr 1
  funext ν
  simp only [coordReflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
def IsLinkLevel (L K : ℕ) (c : ℝ) : Prop :=
  ∃ q : ℤ, c = PeriodicLattice.meshSize L K * ((q : ℝ) + 1 / 2)
def linkPlanes (L K : ℕ) : Set (Set (Fin 4 → ℝ)) :=
  {H | ∃ (μ : Fin 4) (c : ℝ), IsLinkLevel L K c ∧ H = {x | x μ = c}}
end AxisReflection
end YangMills.Construction
end
