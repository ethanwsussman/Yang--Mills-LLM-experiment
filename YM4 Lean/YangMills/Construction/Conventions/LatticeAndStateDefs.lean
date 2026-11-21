import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
abbrev Spacing : Type := {a : ℝ // 0 < a}
abbrev Point : Type := Fin 4 → ℝ
abbrev Direction : Type := Fin 4
def timeAxis : Direction := 3
abbrev SpatialDirection : Type := Fin 3
def SpatialDirection.toDirection (j : SpatialDirection) : Direction := j.castSucc
theorem range_toDirection : Set.range SpatialDirection.toDirection = {timeAxis}ᶜ := by
  ext μ
  fin_cases μ <;> simp [SpatialDirection.toDirection, timeAxis, Fin.exists_fin_succ]
def basisVector (μ : Direction) : Point := Pi.single μ 1
def euclidDot (x y : Point) : ℝ := ∑ μ, x μ * y μ
def euclidNorm (x : Point) : ℝ := (euclidDot x x) ^ (1 / 2 : ℝ)
def supNorm (x : Point) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |x μ|
def translateSet (S : Set Point) (v : Point) : Set Point := (fun x => x + v) '' S
theorem euclidNorm_eq_norm (x : Point) : euclidNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, euclidNorm, ← Real.sqrt_eq_rpow]
  simp [euclidDot, pow_two]
theorem supNorm_eq_norm (x : Point) : supNorm x = ‖x‖ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun μ _ => norm_le_pi_norm x μ
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun μ => ?_
    · exact (abs_nonneg _).trans (Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ 0))
    · exact Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
section Functions
variable {X M : Type*}
def conjFun (F : X → ℂ) : X → ℂ := fun x => (starRingEnd ℂ) (F x)
def absFun (F : X → ℂ) : X → ℝ := fun x => ‖F x‖
def constOne [One M] : X → M := fun _ => 1
def indicatorOne [Zero M] [One M] (Y : Set X) : X → M := Y.indicator constOne
end Functions
end LatticeConventions
end YangMills.Construction
end
