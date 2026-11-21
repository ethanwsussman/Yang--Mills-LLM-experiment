import YangMills.Construction.EuclideanFunctionals.ReconstructionOfACentredFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.ReflectionPositivity.AxisMirror
open scoped ComplexOrder
def ConnectedSymmetric (S : ConnFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → R4 → ℝ), List.ofFn g ∈ sepN n →
    ∀ π : Equiv.Perm (Fin n),
      Ambient.evalOrZero (S.fn n hn) (List.ofFn (g ∘ π)) = Ambient.evalOrZero (S.fn n hn) (List.ofFn g)
def ConnectedInvariant (S : ConnFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∀ Y ∈ sepN n,
    (∀ u : R4, Ambient.evalOrZero (S.fn n hn) ((EuclidMotion.transl u).actList Y) =
      Ambient.evalOrZero (S.fn n hn) Y) ∧
    ∀ g ∈ hyperoctahedral,
      Ambient.evalOrZero (S.fn n hn) Y = Ambient.evalOrZero (S.fn n hn) (g.actList Y)
def OSPositive (S : ConnFamily) : Prop :=
  ∀ G ∈ finCombIn upperHalf, 0 ≤ osForm S G G
structure EuclidFunctionalWithRecon (s : SharpScale) (S : ConnFamily) where
  symm : ConnectedSymmetric S
  invariant : ConnectedInvariant S
  positive : OSPositive S
  clusterConst : ℕ → ℝ → ℝ → ℝ
  cluster : HasClusterBounds S s clusterConst
  space : Type
  [normedAddCommGroup : NormedAddCommGroup space]
  [innerProductSpace : InnerProductSpace ℂ space]
  [completeSpace : CompleteSpace space]
  recon : OSReconstruction space S
attribute [instance] EuclidFunctionalWithRecon.normedAddCommGroup
  EuclidFunctionalWithRecon.innerProductSpace
  EuclidFunctionalWithRecon.completeSpace
end YangMills.Construction.EuclideanFunctionals
