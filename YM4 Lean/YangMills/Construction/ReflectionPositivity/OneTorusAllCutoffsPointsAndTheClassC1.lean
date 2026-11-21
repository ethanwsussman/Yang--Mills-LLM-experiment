import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.MirrorsOfOneTorusAtAllRealPositions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.TorusCutoffs
structure TorusData extends Conventions.StandingParameters where
  sharpExponent : ℕ
namespace TorusData
variable (D : TorusData)
def sharpScale : ℝ := (D.L : ℝ) ^ D.sharpExponent
def sharpNorm {E : Type*} [NormedAddCommGroup E] (f : D.Torus → E) : ℝ :=
  TestFunctions.sharpNormTorus D.sharpScale f
end TorusData
variable (s : Conventions.StandingParameters)
def withCutoff (k : ℕ+) : Conventions.StandingParameters := { s with K := k }
def cutoffData (k : ℕ+) (β : ℝ) (hβ : 0 < β) (μ : Fin 4) : CutoffMirrors.MirrorData :=
  { withCutoff s k with
    coupling := β
    coupling_pos := hβ
    dir := μ }
def proj : (Fin 4 → ℝ) → s.Torus := (TorusMirrors.unitCouplingData s 0).proj
def addVec (x : s.Torus) (v : Fin 4 → ℝ) : s.Torus := (TorusMirrors.unitCouplingData s 0).addVec x v
variable {s}
def torusNorm (x : s.Torus) : ℝ := TorusMetric.torusEuclidNorm x
def torusDist (x x' : s.Torus) : ℝ := torusNorm (x - x')
def setDist (A B : Set s.Torus) : ℝ≥0∞ := TorusMetric.setEuclidDist A B
def translateVec (A : Set s.Torus) (v : Fin 4 → ℝ) : Set s.Torus := (fun x => addVec s x v) '' A
def PairwiseSeparated {n : ℕ} (A : Fin n → Set s.Torus) (d : ℝ) : Prop :=
  ∀ l l', l ≠ l' → ENNReal.ofReal d ≤ setDist (A l) (A l')
variable (s)
theorem proj_add (y w : Fin 4 → ℝ) : proj s (y + w) = proj s y + proj s w := by
  funext μ
  rfl
theorem exists_proj_eq (x : s.Torus) : ∃ y, proj s y = x := by
  choose y hy using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨y, funext hy⟩
def lift (x : s.Torus) : Fin 4 → ℝ := Classical.choose (exists_proj_eq s x)
theorem proj_lift (x : s.Torus) : proj s (lift s x) = x :=
  Classical.choose_spec (exists_proj_eq s x)
variable {s}
def IsC1 (f : s.Torus → ℝ) : Prop := TestFunctions.IsC1Torus f
theorem isC1_iff (f : s.Torus → ℝ) : IsC1 f ↔ ContDiff ℝ 1 (f ∘ proj s) := Iff.rfl
def liftGrad (f : s.Torus → ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => fderiv ℝ (f ∘ proj s) y (Pi.single μ 1)
def grad (f : s.Torus → ℝ) (x : s.Torus) : Fin 4 → ℝ := liftGrad f (lift s x)
theorem liftGrad_eq_of_proj_eq (f : s.Torus → ℝ) {y y' : Fin 4 → ℝ}
    (h : proj s y = proj s y') : liftGrad f y = liftGrad f y' := by
  have hw : proj s (y' - y) = 0 := by
    have h1 := proj_add s y (y' - y)
    rw [add_sub_cancel, ← h] at h1
    exact left_eq_add.mp h1
  have hper : (fun z => (f ∘ proj s) (z + (y' - y))) = f ∘ proj s := by
    funext z
    simp [proj_add, hw]
  have hd : fderiv ℝ (f ∘ proj s) y' = fderiv ℝ (f ∘ proj s) y := by
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := f ∘ proj s) (x := y) (y' - y)
    rw [hper, add_sub_cancel] at h2
    exact h2.symm
  funext μ
  simp only [liftGrad, hd]
theorem grad_eq_of_proj_eq (f : s.Torus → ℝ) {x : s.Torus} {y : Fin 4 → ℝ}
    (h : proj s y = x) : grad f x = liftGrad f y :=
  liftGrad_eq_of_proj_eq f ((proj_lift s x).trans h.symm)
def gradSupNorm (f : s.Torus → ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (TorusMetric.euclidNormVec (grad f x))
end ReflectionPositivity.TorusCutoffs
end YangMills.Construction
end
