import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open BlockAverages
def hemispherePoint (y : imaginaryQuaternions) : ℍ[ℝ] :=
  ((Real.sqrt (1 - ‖y‖ ^ 2) : ℝ) : ℍ[ℝ]) + (y : ℍ[ℝ])
open Classical in
def hemisphereUnit (y : imaginaryQuaternions) : UnitQuaternion :=
  if h : hemispherePoint y ∈ unitary ℍ[ℝ] then ⟨hemispherePoint y, h⟩ else 1
def hemisphereDensity (y : imaginaryQuaternions) : ℝ := (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹
def imaginaryPart : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - ((q.re : ℝ) : ℍ[ℝ]), by
    show (q - ((q.re : ℝ) : ℍ[ℝ])).re = 0
    simp⟩
  map_add' p q := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c p := by
    apply Subtype.ext
    ext <;> simp
variable {ι κ S : Type}
def gaugeAtEnd (g : ι → UnitQuaternion) : Option ι → UnitQuaternion
  | none => 1
  | some z => g z
def formAtEnd (χ : ι → imaginaryQuaternions) : Option ι → imaginaryQuaternions
  | none => 0
  | some z => χ z
def gaugeTransform (src tgt : κ → Option ι) (g : ι → UnitQuaternion) (w : κ → UnitQuaternion) :
    κ → UnitQuaternion :=
  fun b => gaugeAtEnd g (src b) * w b * (gaugeAtEnd g (tgt b))⁻¹
def hemisphereChartField (V : κ → UnitQuaternion) (y : κ → imaginaryQuaternions) : κ → UnitQuaternion :=
  fun b => hemisphereUnit (y b) * V b
def gaugeLinearization (src tgt : κ → Option ι) (V : κ → UnitQuaternion) (y : κ → imaginaryQuaternions) :
    (ι → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions) where
  toFun χ b := imaginaryPart ((formAtEnd χ (src b) : ℍ[ℝ]) * hemispherePoint (y b)) -
    imaginaryPart (hemispherePoint (y b) * ((V b : ℍ[ℝ]) * (formAtEnd χ (tgt b) : ℍ[ℝ]) * star (V b : ℍ[ℝ])))
  map_add' χ₁ χ₂ := by
    funext b
    have h : ∀ o : Option ι, ((formAtEnd (χ₁ + χ₂) o : imaginaryQuaternions) : ℍ[ℝ]) =
        (formAtEnd χ₁ o : ℍ[ℝ]) + (formAtEnd χ₂ o : ℍ[ℝ]) := by
      intro o
      cases o <;> simp [formAtEnd]
    simp only [Pi.add_apply, h, add_mul, mul_add, map_add]
    abel
  map_smul' r χ := by
    funext b
    have h : ∀ o : Option ι, ((formAtEnd (r • χ) o : imaginaryQuaternions) : ℍ[ℝ]) =
        r • (formAtEnd χ o : ℍ[ℝ]) := by
      intro o
      cases o <;> simp [formAtEnd]
    simp only [Pi.smul_apply, h, RingHom.id_apply, smul_mul_assoc, mul_smul_comm, map_smul, smul_sub]
def chartLinearization [AddCommGroup S] [Module ℝ S] (src tgt : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (y : κ → imaginaryQuaternions) :
    ((ι → imaginaryQuaternions) × S) →ₗ[ℝ] (κ → imaginaryQuaternions) :=
  (gaugeLinearization src tgt V y).coprod e
def chartJacobian [Fintype κ] [AddCommGroup S] [Module ℝ S] (src tgt : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S)) (y : κ → imaginaryQuaternions) : ℝ :=
  |LinearMap.det (chartLinearization src tgt V e y ∘ₗ Q)| * ∏ b, hemisphereDensity (y b)
end YangMills.Construction.GaugeCharts
end
