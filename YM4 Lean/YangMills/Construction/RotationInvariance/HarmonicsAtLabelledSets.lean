import YangMills.Construction.RotationInvariance.HarmonicsAtDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace RealPlane
variable {n : ℕ}
namespace LabelledPoints
def labelVec (c : LabelledPoints n) : Fin n → realLabels :=
  fun i => ⟨c.labels i, c.labels_mem i⟩
def graph (c : LabelledPoints n) : Set (RealPlane × realLabels) :=
  Set.range fun i => (c.points i, c.labelVec i)
end LabelledPoints
structure IsDistinctLabelledSet (n : ℕ) (Y : Set (RealPlane × realLabels)) : Prop where
  card_eq : Y.encard = n
  fst_injOn : Set.InjOn Prod.fst Y
def supportPoints (Y : Set (RealPlane × realLabels)) : Set RealPlane :=
  Prod.fst '' Y
def IsDistinctLabelledSetIn (n : ℕ) (A : Set RealPlane)
    (Y : Set (RealPlane × realLabels)) : Prop :=
  IsDistinctLabelledSet n Y ∧ supportPoints Y ⊆ A
def Enumerates (Y : Set (RealPlane × realLabels)) (c : LabelledPoints n) : Prop :=
  IsDistinctLabelledSet n Y ∧ Y = c.graph
end RealPlane
namespace EuclideanFunctionals
def vacuumHarmonic (h : ℤ) : ℂ := if h = 0 then 1 else 0
def pointHarmonic (S : ConnFamily) (θ : openingAngles) (h : ℤ) :
    (n : ℕ) → (Fin n → realLabels) → (Fin n → RealPlane) → ℂ
  | 0, _, _ => vacuumHarmonic h
  | 1, _, _ => 0
  | _ + 2, φ, y => distinctHarmonic S θ φ h y
def configHarmonic (S : ConnFamily) (θ : openingAngles) (h : ℤ) {n : ℕ}
    (c : LabelledPoints n) : ℂ :=
  pointHarmonic S θ h n c.labelVec c.points
def labelledSetHarmonic (S : ConnFamily) (θ : openingAngles) (h : ℤ) (n : ℕ)
    (Y : Set (RealPlane × realLabels)) : ℂ :=
  Classical.epsilon fun v =>
    ∃ c : LabelledPoints n, Enumerates Y c ∧ configHarmonic S θ h c = v
end EuclideanFunctionals
end YangMills.Construction
end
