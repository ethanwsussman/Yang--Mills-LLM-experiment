import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem conj_mem_imaginaryQuaternions (g : UnitQuaternion) (v : imaginaryQuaternions) :
    (g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) ∈ imaginaryQuaternions := by
  have hv : star (v : ℍ[ℝ]) = -(v : ℍ[ℝ]) := by
    have h : (v : ℍ[ℝ]).re = 0 := v.2
    ext <;> simp [h]
  have hs : star (((g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))) =
      -((g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    have e : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
    rw [e, star_mul, star_mul, star_star, hv]
    noncomm_ring
  have h1 := congrArg QuaternionAlgebra.re hs
  change ((g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0
  have h2 : ∀ q : ℍ[ℝ], (star q).re = q.re := fun q => by simp
  have h3 : ∀ q : ℍ[ℝ], (-q).re = -q.re := fun q => rfl
  rw [h2, h3] at h1
  linarith
def adjointMap (g : UnitQuaternion) : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions where
  toFun v := ⟨(g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), conj_mem_imaginaryQuaternions g v⟩
  map_add' u v := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c v := Subtype.ext (by simp)
def IsForwardOriented (m : ℕ) (z : (reflectedFrame F m).Cell) (i : Fin 4) : Prop :=
  reflectCoord m ((z i).valMinAbs + 1) = reflectCoord m (z i).valMinAbs + 1
open Classical in
def sourceBond (m : ℕ) (y : F.Cell) (z : (reflectedFrame F m).Cell) (i : Fin 4) : F.Cell × Fin 4 :=
  if IsForwardOriented m z i then
    (y + siteOfCoords F.top fun l => reflectCoord m (z l).valMinAbs, i)
  else (y + siteOfCoords F.top fun l => reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l), i)
open Classical in
def reflectedDirection (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) (c : F.Cell × Fin 4) (X : imaginaryQuaternions)
    (z : (reflectedFrame F m).Cell) (i : Fin 4) : imaginaryQuaternions :=
  if sourceBond m y z i = c then
    (if IsForwardOriented m z i then X else - adjointMap (V c.1 c.2)⁻¹ X)
  else 0
def ReflectedFieldOfTranslatedTop : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Cell × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ), 0 < m →
    reflectedField m y (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (fun z i => ∑ l, τ l • reflectedDirection m y V (c l) (X l) z i) (reflectedField m y V)
end YangMills.Construction.ColdStepAtMirrorFrames
end
