import YangMills.Construction.Continuum.TuplesOfDisjointSupports
import YangMills.Construction.Lattice.SignedPermutationMatricesAndAffineHypercubicMaps
import YangMills.Construction.TestFunctions.RationalBoxFamilies
import Mathlib
set_option autoImplicit false
open Matrix Set
noncomputable section
namespace YangMills.Construction.DisjointTuples
open YangMills.Construction.TestFunctions YangMills.Construction.PeriodicLattice
def powerDenominators (L : ℕ) : Set ℝ :=
  ⋃ n : ℕ, {x | ∃ k : ℤ, x = (L : ℝ) ^ (-(n : ℤ)) * k}
def iUnionFamily (D : ratBoxUnions → Set RealFun) : Set RealFun := ⋃ Q, D Q
structure IsSymmetricDenseChoice (L : ℕ) (D : ratBoxUnions → Set RealFun) : Prop where
  isDenseFamily : IsDenseFamily D
  pushFun_signedPerm_mem : ∀ φ ∈ iUnionFamily D, ∀ w ∈ signedPermMatrices,
    pushFun (fun x => w *ᵥ x) φ ∈ iUnionFamily D
  pushFun_translate_mem : ∀ φ ∈ iUnionFamily D, ∀ v : Fin 4 → ℝ,
    (∀ μ, v μ ∈ powerDenominators L) → pushFun (translate v) φ ∈ iUnionFamily D
end YangMills.Construction.DisjointTuples
