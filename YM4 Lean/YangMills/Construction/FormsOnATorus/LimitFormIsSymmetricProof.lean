import YangMills.Construction.FormsOnATorus.LimitFormIsSymmetric
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACube
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open BlockAverages TorusFields TorusLumps BoxGaussian
variable {n : ℕ}
private lemma imaginaryComponent_unitI (e : Fin 3) :
    imaginaryComponent e imaginaryUnitI = if e = 0 then 1 else 0 := by
  fin_cases e <;> simp [imaginaryComponent, imaginaryUnitI]
private lemma imaginaryComponent_zero' (e : Fin 3) : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
  fin_cases e <;> simp [imaginaryComponent]
private lemma bilinear_sum_at_unit_bonds (D : TorusBond n → TorusBond n → ℝ) [Fintype (TorusBond n)]
    [DecidableEq (TorusBond n)] (b₀ b₁ : TorusBond n) :
    ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n, D b b' *
        imaginaryComponent e (if b = b₀ then imaginaryUnitI else 0) *
          imaginaryComponent e (if b' = b₁ then imaginaryUnitI else 0) =
      D b₀ b₁ := by
  have h : ∀ (e : Fin 3) (b b' : TorusBond n), D b b' *
      imaginaryComponent e (if b = b₀ then imaginaryUnitI else 0) *
        imaginaryComponent e (if b' = b₁ then imaginaryUnitI else 0) =
      if e = 0 then (if b = b₀ then (if b' = b₁ then D b b' else 0) else 0) else 0 := by
    intro e b b'
    by_cases h1 : b = b₀ <;> by_cases h2 : b' = b₁ <;> by_cases h3 : e = 0 <;>
      simp [h1, h2, h3, imaginaryComponent_unitI, imaginaryComponent_zero']
  simp only [h]
  simp
theorem limitFormSymmetric_of_cubeHessian (hF : cubeHessianStatement) : limitFormSymmetricStatement := by
  intro T hT c C k Q hQ b b'
  obtain ⟨CQ, R₀, -, H⟩ := hF T hT
  have hev : Tendsto (fun R : ℕ => 2 * R) atTop atTop :=
    tendsto_atTop_mono (fun R => by simp only [id]; omega) tendsto_id
  refine tendsto_nhds_unique ((hQ.tendsto b b').comp hev) (((hQ.tendsto b' b).comp hev).congr' ?_)
  filter_upwards [eventually_ge_atTop R₀] with R hR
  simp only [Function.comp]
  unfold cubeEntry
  haveI : NeZero (16 * (2 * R + 1)) := ⟨by omega⟩
  classical
  obtain ⟨-, -, hsym, -, -, -, hent⟩ := H k (16 * (2 * R + 1)) 0 R hR (by omega)
  have e2 : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
  rw [e2]
  have hu := hsym (fun e => if e = bondFrom 0 b' then imaginaryUnitI else 0)
    (fun e => if e = bondFrom 0 b then imaginaryUnitI else 0)
  rw [hent, hent, bilinear_sum_at_unit_bonds, bilinear_sum_at_unit_bonds] at hu
  exact hu
end YangMills.Construction.LimitForms
end
