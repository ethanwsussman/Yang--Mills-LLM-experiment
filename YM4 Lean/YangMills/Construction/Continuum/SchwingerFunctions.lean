import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace SchwingerFunctions
open PeriodicLattice TestFunctions
variable {n q : ℕ}
def IsTorusTestFamily {L m : ℕ} (f : Fin n → FourTorus L m → ℝ) : Prop :=
  (∀ i, IsBoundedFun (f i)) ∧ (∀ i, Measurable (f i)) ∧ ∃ d : ℝ, HasSeparatedSupportsTorus f d
def connectedSchwinger (L m K : ℕ) (β : ℝ) (f : Fin n → FourTorus L m → ℝ) : ℂ :=
  gibbsCumulant L m K β fun i U => smearedObservable (f i) U
def partitionSum {F : Type*} (T : (n : ℕ) → (Fin n → F) → ℂ) (f : Fin q → F) : ℂ :=
  ∑ π ∈ Finset.univ.filter
      (fun π : Finpartition (Finset.univ : Finset (Fin q)) => ∀ B ∈ π.parts, 2 ≤ B.card),
    ∏ B ∈ π.parts, T B.card fun k => f (B.orderEmbOfFin rfl k)
def centredSchwinger (L m K : ℕ) (β : ℝ) (f : Fin q → FourTorus L m → ℝ) : ℂ :=
  partitionSum (fun _ g => connectedSchwinger L m K β g) f
def IsR4TestFamily (ℓ : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ i, HasCompactSupport (f i)) ∧ (∃ d : ℝ, HasSeparatedSupportsR4 f d) ∧
    ∃ A : Set (Fin 4 → ℝ), ∀ i, IsPeriodizable ℓ A (f i)
def periodizeAll (L m : ℕ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Fin n → FourTorus L m → ℝ :=
  fun i => periodize (torusSide L m) (f i)
def connectedSchwingerR4 (L m K : ℕ) (β : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℂ :=
  connectedSchwinger L m K β (periodizeAll L m f)
def IsC1c (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  IsC1R4 f ∧ HasCompactSupport f
def PairwiseSeparated (C : Fin n → Set (Fin 4 → ℝ)) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ i k, i ≠ k → ENNReal.ofReal d ≤ setDistR4 (C i) (C k)
def IsContinuumSchwingerFamily (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ) : Prop :=
  ∀ n, 2 ≤ n → ∀ C : Fin n → Set (Fin 4 → ℝ), (∀ i, IsCompact (C i)) → PairwiseSeparated C →
    ∀ f : Fin n → (Fin 4 → ℝ) → ℝ, (∀ i, IsC1c (f i) ∧ tsupport (f i) ⊆ C i) →
      ∀ (i : Fin n) (g h : (Fin 4 → ℝ) → ℝ) (a b : ℝ),
        IsC1c g → tsupport g ⊆ C i →
        IsC1c h → tsupport h ⊆ C i →
        S n (Function.update f i (a • g + b • h)) =
          (a : ℂ) * S n (Function.update f i g) + (b : ℂ) * S n (Function.update f i h)
end SchwingerFunctions
end YangMills.Construction
