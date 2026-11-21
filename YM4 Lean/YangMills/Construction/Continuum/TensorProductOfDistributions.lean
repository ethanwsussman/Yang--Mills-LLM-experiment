import YangMills.Construction.Continuum.OrderZeroTestFunctionsOnCoordinateSpacesAndGenerators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Continuum.TensorProduct
open TopologicalSpace YangMills.Construction.ReflectionSpaces.Euclidean
variable {r : ℕ} (n : Fin r → ℕ)
def blockComponent (x : Coord (∑ i, n i)) (i : Fin r) : Coord (n i) :=
  fun a => x (finSigmaFinEquiv ⟨i, a⟩)
def prodOpens (U : ∀ i, Opens (Coord (n i))) : Opens (Coord (∑ i, n i)) where
  carrier := {x | ∀ i, blockComponent n x i ∈ U i}
  is_open' := by
    have hset : {x : Coord (∑ i, n i) | ∀ i, blockComponent n x i ∈ U i} =
        ⋂ i, (fun x => blockComponent n x i) ⁻¹' (U i : Set (Coord (n i))) := by
      ext x
      simp
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (U i).isOpen.preimage (continuous_pi fun a => continuous_apply _)
def tensorFn (φ : ∀ i, Coord (n i) → ℂ) : Coord (∑ i, n i) → ℂ :=
  fun x => ∏ i, φ i (blockComponent n x i)
variable {n}
def IsTensorProduct {U : ∀ i, Opens (Coord (n i))} (u : ∀ i, Distribution (U i))
    (T : Distribution (prodOpens n U)) : Prop :=
  ∀ φ : ∀ i, testFunctionSpace (U i),
    ∃ hφ : tensorFn n (fun i => (φ i : Coord (n i) → ℂ)) ∈
        testFunctionSpace (prodOpens n U),
      T.form ⟨_, hφ⟩ = ∏ i, (u i).form (φ i)
theorem distribution_nonempty {m : ℕ} (W : Opens (Coord m)) : Nonempty (Distribution W) :=
  ⟨⟨0, fun _ _ _ => ⟨0, 0, le_rfl, fun _ _ => by simp⟩⟩⟩
def tensorDist {U : ∀ i, Opens (Coord (n i))} (u : ∀ i, Distribution (U i)) :
    Distribution (prodOpens n U) :=
  haveI := distribution_nonempty (prodOpens n U)
  Classical.epsilon (IsTensorProduct u)
def TensorProductExistsUnique : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ n : Fin r → ℕ, (∀ i, 1 ≤ n i) →
    ∀ (U : ∀ i, Opens (Coord (n i))) (u : ∀ i, Distribution (U i)),
      IsTensorProduct u (tensorDist u) ∧
        ∀ T : Distribution (prodOpens n U), IsTensorProduct u T → T = tensorDist u
end YangMills.Construction.Continuum.TensorProduct
