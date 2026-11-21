import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open PeriodicLattice (SignedFrame)
def adicPoints4 (L : ℕ) : Set (Fin 4 → ℝ) :=
  {a | ∀ μ, a μ ∈ PeriodicLattice.adicGridPoints L}
def translateR4 (a v : Fin 4 → ℝ) : Fin 4 → ℝ := v + a
def adicIsometriesR4 (L : ℕ) : Set ((Fin 4 → ℝ) → Fin 4 → ℝ) :=
  {s | ∃ a ∈ adicPoints4 L, ∃ w : SignedFrame, s = translateR4 a ∘ w.actOnVector}
namespace Kind
variable (P : Params) (K : Kind)
def InducedBy (s : (Fin 4 → ℝ) → Fin 4 → ℝ) (r : K.Pt P → K.Pt P) : Prop :=
  r ∘ K.quotMap P = K.quotMap P ∘ s
def descendedMap (s : (Fin 4 → ℝ) → Fin 4 → ℝ) : K.Pt P → K.Pt P :=
  @Classical.epsilon _ ⟨id⟩ (InducedBy P K s)
def adicIsometriesQ : Set (K.Pt P → K.Pt P) :=
  {r | ∃ s ∈ adicIsometriesR4 P.L, InducedBy P K s r}
def signedFrameMap (w : SignedFrame) : K.Pt P → K.Pt P := descendedMap P K w.actOnVector
def pushFn {Z : Type*} (r : K.Pt P ≃ K.Pt P) (f : K.Pt P → Z) : K.Pt P → Z :=
  f ∘ r.symm
def shiftFn {Z : Type*} (a : K.Pt P) (f : K.Pt P → Z) : K.Pt P → Z :=
  fun p => f (p - a)
def pushTuple {ι Z : Type*} (r : K.Pt P ≃ K.Pt P) (f : ι → K.Pt P → Z) :
    ι → K.Pt P → Z :=
  fun i => pushFn P K r (f i)
def shiftTuple {ι Z : Type*} (a : K.Pt P) (f : ι → K.Pt P → Z) : ι → K.Pt P → Z :=
  fun i => shiftFn P K a (f i)
end Kind
end YangMills.Construction.PeriodicSpace
