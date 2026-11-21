import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def lawsMargin (ϑ : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ 4 * min (9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * ϑ ^ 2)
    ((3 / 4 : ℝ) ^ 4 * (27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * ϑ ^ 4))
structure LevelReadAtScale (ℓ : TorusLumps.StepParameters) (vt C X : ℝ) (K : ℕ+) (β d : ℝ) (sides : Set ℝ)
    (φ ψ : (Fin 4 → ℝ) → ℝ) (k : ℕ) (σ al e : ℝ) : Prop where
  coupling_ge : ∀ j ≤ k, X ≤ (TorusLumps.couplingFlow ℓ β j).1
  al_mem : al ∈ Icc (3 / 4 : ℝ) (5 / 4)
  one_le_sites : 1 ≤ d / levelMesh ℓ.side K k
  e_nonneg : 0 ≤ e
  e_le : e ≤ levelMesh ℓ.side K 0 / d
  margin_le : C * ((TorusLumps.couplingFlow ℓ β k).1 ^ (-(1 / 100 : ℝ)) + e) ≤ lawsMargin vt
  kernel_mem : TestFunctions.inverseEighthKernel φ ψ ∈
    Icc (TestPairs.kernelLowerConst * vt ^ 2) TestPairs.kernelUpperConst
  σ_pos : 0 < σ
  twoPoint_eq : twoPointLimsupAtScale ℓ.side K β sides φ ψ d = ((σ : ℝ) : EReal)
  σ_eq : ∃ e' : ℝ, |e'| ≤ 1 / 4 ∧
    σ = (al / (TorusLumps.couplingFlow ℓ β k).1) ^ 2 *
      (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) * (1 + e')
  coupling_le : (TorusLumps.couplingFlow ℓ β k).1 ≤ 1 / σ
  laws : ∀ m : ℕ, Real.exp (Real.log (TorusLumps.couplingFlow ℓ β k).1 ^ 3) ≤
      PeriodicLattice.torusSide ℓ.side m / levelMesh ℓ.side K k →
    CumulantLawsOnTorus ℓ vt C (TorusLumps.couplingFlow ℓ β k).1 al e β K m d
def levelReadByTwoPointStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => (Tb.stepParameters y).Admissible ∧
    ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∃ βv nv δv C X : ℝ, 1 ≤ nv ∧ 0 < δv ∧ 0 ≤ C ∧ 16 ≤ X ∧
      ∀ (K : ℕ+) (β d : ℝ) (sides : Set ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ),
        (∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ PeriodicLattice.torusSide (Tb.stepParameters y).side m ∈ sides) →
        (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt → TestFunctions.uniformNorm φ = 1 →
        TestFunctions.uniformNorm ψ = 1 →
        βv ≤ β → nv ≤ d / levelMesh (Tb.stepParameters y).side K 0 →
        (∀ d' ∈ Icc (((Tb.stepParameters y).side : ℝ) ^ (β / (4 * (Tb.stepParameters y).B)) *
            levelMesh (Tb.stepParameters y).side K 0) d,
          twoPointLimsupAtScale (Tb.stepParameters y).side K β sides φ ψ d' ≤ ((δv : ℝ) : EReal)) →
        ∃ (k : ℕ) (σ al e : ℝ), LevelReadAtScale (Tb.stepParameters y) vt C X K β d sides φ ψ k σ al e
end YangMills.Construction.FourPointCondition
end
