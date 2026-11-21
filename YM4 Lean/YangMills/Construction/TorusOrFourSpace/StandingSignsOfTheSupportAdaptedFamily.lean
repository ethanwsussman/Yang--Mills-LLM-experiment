import YangMills.Construction.TorusOrFourSpace.AdicIsometriesInducedMapsAndActions
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SupportAdapted
open PeriodicLattice (SignedFrame)
section Sets
variable {X : Type*}
abbrev imageSet (r : X → X) (A : Set X) : Set X := r '' A
end Sets
section Isometries
variable {X : Type*}
def IsDistPreserving (d : X → X → ℝ) (r : X → X) : Prop := ∀ x x', d (r x) (r x') = d x x'
def IsIsometryGroupFor (d : X → X → ℝ) (G : Set (X → X)) : Prop :=
  (∀ r ∈ G, Function.Bijective r ∧ IsDistPreserving d r) ∧ id ∈ G ∧
    (∀ r ∈ G, ∀ r' ∈ G, r ∘ r' ∈ G) ∧ ∀ r ∈ G, ∃ r' ∈ G, r ∘ r' = id ∧ r' ∘ r = id
end Isometries
abbrev IsEuclidIsometryGroup (G : Set ((Fin 4 → ℝ) → Fin 4 → ℝ)) : Prop :=
  IsIsometryGroupFor InfiniteLattice.euclidDist G
def frameInv (w : SignedFrame) : SignedFrame := (w.1⁻¹, fun μ => w.2 (w.1⁻¹ μ))
theorem actOnVector_frameInv_actOnVector (w : SignedFrame) (v : Fin 4 → ℝ) :
    (frameInv w).actOnVector (w.actOnVector v) = v := by
  funext μ
  have hs : ∀ s : ℤˣ, ((s : ℤ) : ℝ) * ((s : ℤ) : ℝ) = 1 := fun s => by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  simp [frameInv, SignedFrame.actOnVector, ← mul_assoc, hs]
theorem actOnVector_actOnVector_frameInv (w : SignedFrame) (v : Fin 4 → ℝ) :
    w.actOnVector ((frameInv w).actOnVector v) = v := by
  funext μ
  have hs : ∀ s : ℤˣ, ((s : ℤ) : ℝ) * ((s : ℤ) : ℝ) = 1 := fun s => by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  simp [frameInv, SignedFrame.actOnVector, ← mul_assoc, hs]
section OnTheSpace
variable (D : Params) (E : Kind)
abbrev c1EuclidNorm (u : E.Pt D → ℝ) : ℝ≥0∞ := Kind.euclidC1Norm D E u
abbrev c1MaxNorm (u : E.Pt D → ℝ) : ℝ≥0∞ := Kind.c1NormQ D E u
def SupportedIn {Z : Type*} [Zero Z] (f : E.Pt D → Z) (A : Set (E.Pt D)) : Prop :=
  Kind.supportQ D E f ⊆ A
def frameActFn {Z : Type*} (w : SignedFrame) (f : E.Pt D → Z) : E.Pt D → Z :=
  fun y => f (Kind.signedFrameMap D E (frameInv w) y)
def frameActTuple {ι Z : Type*} (w : SignedFrame) (f : ι → E.Pt D → Z) : ι → E.Pt D → Z :=
  fun i => frameActFn D E w (f i)
abbrev IsQuotIsometry (r : E.Pt D → E.Pt D) : Prop := IsDistPreserving (Kind.quotDist D E) r
abbrev IsQuotIsometryGroup (G : Set (E.Pt D → E.Pt D)) : Prop :=
  IsIsometryGroupFor (Kind.quotDist D E) G
end OnTheSpace
section Stable
variable {X : Type*}
abbrev Operation (X : Type*) : Type _ := List X → Set X
def IsStableUnder (op : Operation X) (S : Set X) : Prop :=
  ∀ l : List X, l ≠ [] → (∀ x ∈ l, x ∈ S) → op l ⊆ S
def ofMap (φ : X → X) : Operation X := fun l => {z | ∃ x, l = [x] ∧ z = φ x}
def IsStableUnderAction {G : Type*} (act : G → X → X) (T : Set G) (S : Set X) : Prop :=
  ∀ g ∈ T, IsStableUnder (ofMap (act g)) S
theorem isStableUnder_ofMap_iff (φ : X → X) (S : Set X) :
    IsStableUnder (ofMap φ) S ↔ ∀ x ∈ S, φ x ∈ S := by
  constructor
  · intro h x hx
    exact h [x] (by simp) (by simpa using hx) ⟨x, rfl, rfl⟩
  · rintro h l - hl z ⟨x, rfl, rfl⟩
    exact h x (hl x (by simp))
end Stable
end YangMills.Construction.PeriodicSpace.SupportAdapted
