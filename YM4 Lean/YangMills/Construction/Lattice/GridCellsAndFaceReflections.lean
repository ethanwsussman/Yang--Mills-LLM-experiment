import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CellGrid
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def IsLinkPlane (L : ℕ) (κ : ℤ) (S : Set AmbientSpace) : Prop :=
  ∃ (μ : Fin 4) (c : ℝ), (∃ z : ℤ, c = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) ∧
    S = {x | x μ = c}
variable {L : ℕ} {κ : ℤ} (d : CellGrid L κ)
def IsLinkPlaneOfSpace (S : Set d.Space) : Prop :=
  ∃ P, IsLinkPlane L κ P ∧ S = BoxTorus.image d.sideLengths P
def faceLevel (μ : Fin 4) (a : ℤ) : ℝ := d.centre μ + a * d.cellLength
def faceReflect (μ : Fin 4) (a : ℤ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - d.centre μ - a * d.cellLength)) • BoxTorus.basisVector μ
def flipDiag (μ : Fin 4) : Fin 4 → ℝ := Function.update 1 μ (-1)
theorem flipDiag_mul_self (μ i : Fin 4) : flipDiag μ i * flipDiag μ i = 1 := by
  by_cases h : i = μ
  · subst h
    simp [flipDiag]
  · simp [flipDiag, Function.update_of_ne h]
def axisFlip (μ : Fin 4) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  LinearEquiv.ofInvolutive (Matrix.toLin' (Matrix.diagonal (flipDiag μ))) fun x => by
    funext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec_diagonal, ← mul_assoc, flipDiag_mul_self,
      one_mul]
theorem axisFlip_apply (μ : Fin 4) (x : AmbientSpace) (i : Fin 4) :
    axisFlip μ x i = flipDiag μ i * x i := by
  show Matrix.toLin' (Matrix.diagonal (flipDiag μ)) x i = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
def faceReflectEquiv (μ : Fin 4) (a : ℤ) : AmbientSpace ≃ᵃ[ℝ] AmbientSpace :=
  AffineEquiv.mk' (d.faceReflect μ a) (axisFlip μ) 0 fun x => by
    funext i
    by_cases h : i = μ
    · subst h
      simp [faceReflect, axisFlip_apply, flipDiag, BoxTorus.basisVector]
      ring
    · simp [faceReflect, axisFlip_apply, flipDiag, BoxTorus.basisVector,
        Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem coe_faceReflectEquiv (μ : Fin 4) (a : ℤ) :
    ⇑(d.faceReflectEquiv μ a) = d.faceReflect μ a := rfl
def reflectionGroup : Subgroup (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) :=
  Subgroup.closure (range fun p : Fin 4 × ℤ => d.faceReflectEquiv p.1 p.2)
def linearSign (g : d.reflectionGroup) : ℝ :=
  LinearMap.det ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear : AmbientSpace →ₗ[ℝ] AmbientSpace)
theorem linearSign_eq_one_or_neg_one (g : d.reflectionGroup) :
    d.linearSign g = 1 ∨ d.linearSign g = -1 := by
  let φ : (AmbientSpace ≃ᵃ[ℝ] AmbientSpace) →* ℝˣ := LinearEquiv.det.comp AffineEquiv.linearHom
  have hφ : ∀ h : AmbientSpace ≃ᵃ[ℝ] AmbientSpace,
      ((φ h : ℝˣ) : ℝ) = LinearMap.det (h.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) := fun h =>
    LinearEquiv.coe_det _
  have hsq : ∀ h ∈ d.reflectionGroup, φ h ^ 2 = 1 := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem h hh =>
      obtain ⟨⟨μ, a⟩, rfl⟩ := hh
      ext
      have hdet : LinearMap.det
          ((d.faceReflectEquiv μ a).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) = -1 := by
        have hl : ((d.faceReflectEquiv μ a).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
            Matrix.toLin' (Matrix.diagonal (flipDiag μ)) := rfl
        rw [hl, LinearMap.det_toLin', Matrix.det_diagonal]
        fin_cases μ <;> simp [flipDiag, Function.update]
      simp only [Units.val_pow_eq_pow_val, hφ, hdet, Units.val_one]
      norm_num
    | one => simp
    | mul g h _ _ hg hh => rw [map_mul, mul_pow, hg, hh, one_mul]
    | inv g _ hg => rw [map_inv, inv_pow, hg, inv_one]
  have h1 : d.linearSign g ^ 2 = 1 := by
    have := congrArg (fun u : ℝˣ => (u : ℝ)) (hsq g g.2)
    simpa [hφ, linearSign] using this
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h1)
def cellCube (k : Fin 4 → ℤ) : Set AmbientSpace :=
  (fun y : AmbientSpace => d.centre + d.cellLength • (fun μ => (k μ : ℝ)) + y) ''
    Set.pi univ fun _ => Icc 0 d.cellLength
def IsCellCube (S : Set AmbientSpace) : Prop := S ∈ range d.cellCube
def spaceCell (k : Fin 4 → ℤ) : Set d.Space := BoxTorus.image d.sideLengths (d.cellCube k)
def spaceCells : Set (Set d.Space) := range d.spaceCell
def IsInducedMap (gbar : d.Space → d.Space) (g : AmbientSpace → AmbientSpace) : Prop :=
  gbar ∘ BoxTorus.projection d.sideLengths = BoxTorus.projection d.sideLengths ∘ g
def inducedGroupMaps : Set (d.Space → d.Space) :=
  {gbar | ∃ g ∈ d.reflectionGroup, d.IsInducedMap gbar g}
def inducedReflections : Set (d.Space → d.Space) :=
  {gbar | ∃ (μ : Fin 4) (a : ℤ), d.IsInducedMap gbar (d.faceReflect μ a)}
end YangMills.Construction.CellGrid
end
