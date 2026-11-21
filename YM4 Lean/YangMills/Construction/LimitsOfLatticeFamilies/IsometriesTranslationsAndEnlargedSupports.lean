import YangMills.Construction.LimitsOfLatticeFamilies.SpacesOfFunctionsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ModelSpace
variable (s : Conventions.StandingParameters) (Y : ModelSpace)
structure SpaceIsometry where
  toEquiv : Y.Carrier s ≃ Y.Carrier s
  dist_eq : ∀ x y, ModelSpace.dist s Y (toEquiv x) (toEquiv y) = ModelSpace.dist s Y x y
instance : CoeFun (SpaceIsometry s Y) fun _ => Y.Carrier s → Y.Carrier s := ⟨fun r => r.toEquiv⟩
variable {s Y}
def SpaceIsometry.pushFun {Z : Type*} (r : SpaceIsometry s Y) (g : Y.Carrier s → Z) : Y.Carrier s → Z :=
  g ∘ r.toEquiv.symm
def SpaceIsometry.pushTuple {n : ℕ} (r : SpaceIsometry s Y) (g : FunTuple s Y n) : FunTuple s Y n :=
  fun l => r.pushFun (g l)
def shift {Z : Type*} (a : Y.Carrier s) (g : Y.Carrier s → Z) : Y.Carrier s → Z :=
  fun y => g (y - a)
def shiftTuple {n : ℕ} (a : Y.Carrier s) (g : FunTuple s Y n) : FunTuple s Y n :=
  fun l => shift a (g l)
def shiftSet (S : Set (Y.Carrier s)) (a : Y.Carrier s) : Set (Y.Carrier s) := (· + a) '' S
variable (s Y)
variable {s Y}
end YangMills.Construction.LatticeLimits.ModelSpace
end
