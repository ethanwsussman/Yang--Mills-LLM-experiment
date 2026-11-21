import YangMills.Construction.Conventions.LatticeAndStateDefs
import Mathlib
noncomputable section
namespace YangMills.Construction.LatticeConventions
def IsAxialNormal (n : Point) : Prop := ∃ μ : Direction, n = basisVector μ
def IsFaceDiagonalNormal (n : Point) : Prop :=
  ∃ μ ν : Direction, μ ≠ ν ∧
    (n = basisVector μ + basisVector ν ∨ n = basisVector μ - basisVector ν)
structure NormalHyperplane where
  normal : Point
  level : ℝ
  normal_valid : IsAxialNormal normal ∨ IsFaceDiagonalNormal normal
namespace NormalHyperplane
def axial (μ : Direction) (c : ℝ) : NormalHyperplane :=
  ⟨basisVector μ, c, Or.inl ⟨μ, rfl⟩⟩
variable (H : NormalHyperplane)
def carrier : Set Point := {x | euclidDot H.normal x = H.level}
def reflect (x : Point) : Point :=
  x - (2 * (euclidDot H.normal x - H.level) / euclidNorm H.normal ^ 2) • H.normal
def upperHalfSpace : Set Point := {x | H.level ≤ euclidDot H.normal x}
def lowerHalfSpace : Set Point := {x | euclidDot H.normal x ≤ H.level}
def reflectionLinear : Point →ₗ[ℝ] Point where
  toFun w := w - (2 * (euclidNorm H.normal ^ 2)⁻¹ * euclidDot H.normal w) • H.normal
  map_add' v w := by
    have hvw : euclidDot H.normal (v + w) = euclidDot H.normal v + euclidDot H.normal w := by
      simp [euclidDot, mul_add, Finset.sum_add_distrib]
    rw [hvw, mul_add, add_smul]
    abel
  map_smul' s w := by
    have hsw : euclidDot H.normal (s • w) = s * euclidDot H.normal w := by
      simp only [euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    simp only [RingHom.id_apply, smul_sub, smul_smul, hsw]
    congr 2
    ring
def IsLatticeMirror (a : ℝ) : Prop :=
  (IsAxialNormal H.normal → ∃ q : ℤ, H.level = (q : ℝ) * (a / 2)) ∧
    (IsFaceDiagonalNormal H.normal → ∃ q : ℤ, H.level = (q : ℝ) * a)
def mirrorsWithNormal (a : ℝ) (n : Point) : Set NormalHyperplane :=
  {P | P.normal = n ∧ P.IsLatticeMirror a}
def IsVertexMirror (a : ℝ) : Prop :=
  H.IsLatticeMirror a ∧ IsAxialNormal H.normal ∧ ∃ q : ℤ, H.level = (q : ℝ) * a
def IsEdgeMirror (a : ℝ) : Prop :=
  H.IsLatticeMirror a ∧ IsAxialNormal H.normal ∧
    ∃ q : ℤ, H.level = (q : ℝ) * a + a / 2
end NormalHyperplane
end YangMills.Construction.LatticeConventions
end
