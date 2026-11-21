import YangMills.Construction.Lattice.ConnectedFunctionsAtArbitraryArguments
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConnectedFunctions.CouplingData
variable (D : CouplingData) {q : ℕ}
def restrictTo (h : Fin q → D.Torus → ℂ) (J : Finset (Fin q)) : Fin J.card → D.Torus → ℂ :=
  fun k => h (J.orderEmbOfFin rfl k)
def centredMomentFn (h : Fin q → D.Torus → ℂ) : ℂ :=
  D.expect fun U => ∏ l, D.centred (h l) U
def centredFunctionalFn (h : Fin q → D.Torus → ℂ) : ℂ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
    D.connected (D.restrictTo h J)
theorem apply_get_ofFn_eq {α β : Type*} (F : (n : ℕ) → (Fin n → α) → β) (h : Fin q → α) :
    F _ (List.ofFn h).get = F q h := by
  have hmain : ∀ (n : ℕ) (hn : n = q) (g : Fin n → α), (∀ i, g i = h (Fin.cast hn i)) →
      F n g = F q h := by
    rintro n rfl g hg
    congr 1
    funext i
    simpa using hg i
  refine hmain _ List.length_ofFn _ fun i => ?_
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  rfl
end YangMills.Construction.ConnectedFunctions.CouplingData
