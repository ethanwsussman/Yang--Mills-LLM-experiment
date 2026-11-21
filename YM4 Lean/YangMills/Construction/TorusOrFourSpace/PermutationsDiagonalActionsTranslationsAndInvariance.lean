import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.TorusOrFourSpace.QuarterSideOpenBallsDistinctPointsAndBoundedFamilies
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.PeriodicLattice (SignedFrame)
def axisPerm (w : SignedFrame) : Equiv.Perm (Fin 4) := w.1.symm
def axisSign (w : SignedFrame) (μ : Fin 4) : ℤˣ := w.2 (w.1.symm μ)
def frameInv (w : SignedFrame) : SignedFrame := (w.1⁻¹, fun ν => w.2 (w.1.symm ν))
theorem frameInv_actOnVector_actOnVector (w : SignedFrame) (x : Fin 4 → ℝ) :
    (frameInv w).actOnVector (w.actOnVector x) = x := by
  funext ν
  have hsq : (((w.2 (w.1.symm ν) : ℤˣ) : ℤ) : ℝ) * (((w.2 (w.1.symm ν) : ℤˣ) : ℤ) : ℝ) = 1 := by
    exact_mod_cast Int.units_coe_mul_self (w.2 (w.1.symm ν))
  simp only [frameInv, SignedFrame.actOnVector, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rw [← mul_assoc, hsq, one_mul]
variable (D : Params) (E : Kind)
def pickLift (y : E.Pt D) : Fin 4 → ℝ := Classical.epsilon (IsLift D E y)
def frameAct (w : SignedFrame) (y : E.Pt D) : E.Pt D :=
  E.quotMap D (w.actOnVector (pickLift D E y))
def addPt (y v : E.Pt D) : E.Pt D :=
  E.quotMap D (pickLift D E y + pickLift D E v)
def subPt (y v : E.Pt D) : E.Pt D :=
  E.quotMap D (pickLift D E y - pickLift D E v)
inductive TupleMap (D : Params) (E : Kind) (n : ℕ+) where
  | permute (ς : Equiv.Perm (Fin (n : ℕ)))
  | frameDiag (w : SignedFrame)
  | translate (v : E.Pt D)
namespace TupleMap
variable {D E} {n : ℕ+}
def actPts : TupleMap D E n → E.Tuple D n → E.Tuple D n
  | permute ς, y => fun i => y (ς.symm i)
  | frameDiag w, y => fun i => frameAct D E w (y i)
  | translate v, y => fun i => addPt D E (y i) v
def actFns {Z : Type*} :
    TupleMap D E n → (Fin (n : ℕ) → E.Pt D → Z) → Fin (n : ℕ) → E.Pt D → Z
  | permute ς, f => fun i => f (ς.symm i)
  | frameDiag w, f => fun i y => f i (frameAct D E (frameInv w) y)
  | translate v, f => fun i y => f i (subPt D E y v)
def InvariantFunctional {Z : Type*} (ψ : TupleMap D E n)
    (Ψ : sepC1Tuples D E (n : ℕ) → Z) : Prop :=
  ∀ (f : sepC1Tuples D E (n : ℕ)) (h : ψ.actFns f.1 ∈ sepC1Tuples D E (n : ℕ)),
    Ψ ⟨_, h⟩ = Ψ f
def InvariantDistrib (ψ : TupleMap D E n)
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ) : Prop :=
  ∀ (F : Tuple.testFns D E (pairwiseDistinct D E n))
    (h : F.1 ∘ ψ.actPts ∈ Tuple.testFns D E (pairwiseDistinct D E n)),
    T ⟨_, h⟩ = T F
end TupleMap
end YangMills.Construction.PeriodicSpace.Kind
