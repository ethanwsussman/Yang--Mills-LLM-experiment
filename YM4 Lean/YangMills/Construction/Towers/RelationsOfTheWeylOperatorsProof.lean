import YangMills.Construction.Towers.ExplicitFormOfTheWeylOperators
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2 UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open MagneticWeyl
private theorem meshAt_unit (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
private theorem latticePoint_coord (L : ℕ) (k : Fin 4 → ℤ) (μ : Fin 4) :
    ((latticePoint L k : FullSpace.Vertex L 0 0) : AmbientSpace) μ = (k μ : ℝ) := by
  change (k μ : ℝ) * meshAt L 0 0 = (k μ : ℝ)
  rw [meshAt_unit, mul_one]
private theorem latticePoint_add (L : ℕ) (k k' : Fin 4 → ℤ) :
    latticePoint L (k + k') = latticePoint L k + latticePoint L k' :=
  Subtype.ext (funext fun μ => by
    change (((k + k') μ : ℤ) : ℝ) * meshAt L 0 0 =
      (k μ : ℝ) * meshAt L 0 0 + (k' μ : ℝ) * meshAt L 0 0
    simp [add_mul])
private theorem latticePoint_zero (L : ℕ) : latticePoint L 0 = 0 :=
  Subtype.ext (funext fun μ => by
    change (((0 : Fin 4 → ℤ) μ : ℤ) : ℝ) * meshAt L 0 0 = 0
    simp)
private theorem latticePoint_ne_zero (L : ℕ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    latticePoint L k ≠ 0 := by
  intro h
  refine hk (funext fun μ => ?_)
  have hμ : ((latticePoint L k : FullSpace.Vertex L 0 0) : AmbientSpace) μ = 0 := by
    rw [h]; rfl
  rw [latticePoint_coord] at hμ
  exact_mod_cast hμ
private theorem coord_zero_add_latticePoint (L : ℕ) (x : FullSpace.Vertex L 0 0) (k : Fin 4 → ℤ) :
    ((x + latticePoint L k : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
      (x : AmbientSpace) 0 + (k 0 : ℝ) := by
  change (x : AmbientSpace) 0 + ((latticePoint L k : FullSpace.Vertex L 0 0) : AmbientSpace) 0 = _
  rw [latticePoint_coord]
theorem magneticWeylRelations_holds (hExp : WeylExplicitFormulas) :
    MagneticWeylRelations := by
  intro L φ k k'
  have act := (hExp L φ).2.2.2.2
  have hmul : ∀ (m m' : Fin 4 → ℤ) (w : ScalarL2 L),
      magneticWeyl L φ m (magneticWeyl L φ m' w) =
        Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm m m' : ℂ)) •
          magneticWeyl L φ (m + m') w := by
    intro m m' w
    refine lp.ext (funext fun x => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, act m, act m', act (m + m'), smul_smul, smul_smul,
      latticePoint_add, ← add_assoc, ← Complex.exp_add, ← Complex.exp_add,
      coord_zero_add_latticePoint]
    congr 2
    simp only [symplecticForm, Pi.add_apply]
    push_cast
    ring
  have hzero : ∀ w : ScalarL2 L, magneticWeyl L φ 0 w = w := by
    intro w
    refine lp.ext (funext fun x => ?_)
    rw [act 0, latticePoint_zero, add_zero]
    simp
  have hinv : ∀ ψ : ScalarL2 L, magneticWeyl L φ k (magneticWeyl L φ (-k) ψ) = ψ := by
    intro ψ
    have hω : symplecticForm k (-k) = 0 := by
      simp only [symplecticForm, Pi.neg_apply]
      ring
    rw [hmul, hω, add_neg_cancel, hzero]
    simp
  refine ⟨hmul k k', hzero, fun ψ χ => ?_, fun v => ?_⟩
  · let U : ScalarL2 L →ₗᵢ[ℂ] ScalarL2 L :=
      ⟨magneticWeyl L φ k, (magneticWeyl_isUnitary φ k).2⟩
    calc inner ℂ (magneticWeyl L φ (-k) ψ) χ
        = inner ℂ (U (magneticWeyl L φ (-k) ψ)) (U χ) := (U.inner_map_map _ _).symm
      _ = inner ℂ ψ (magneticWeyl L φ k χ) := by
        change inner ℂ (magneticWeyl L φ k (magneticWeyl L φ (-k) ψ)) _ = _
        rw [hinv]
        rfl
  · rw [act k, vectorAtZero_apply, zero_add]
    by_cases hk : k = 0
    · subst hk
      simp [latticePoint_zero, indicatorAtZero, kronecker]
    · simp [indicatorAtZero, latticePoint_ne_zero L hk, kronecker, hk]
end YangMills.Construction.Tower
end
