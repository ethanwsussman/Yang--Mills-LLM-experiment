import YangMills.Construction.ConfigurationSpace.SmoothSubspaces
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
variable {n : ℕ}
abbrev schwartzSet (n : ℕ) : Set (Config n → ℂ) := rapidDecaySet n
def decaySeminorm (k q : ℕ) (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ (α : MultiIdx (CoordIndex n)) (_ : α.order ≤ q), weightedDerivSup k α φ
def sobolevWeightNorm (p : ℕ) (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ (x : Config n) (α : MultiIdx (CoordIndex n)) (_ : α.order ≤ p),
    ENNReal.ofReal ((1 + configNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖configMultiDeriv α φ x‖)
def IsOpenForFamily {ι : Type*} [Nonempty ι] (F : ι → schwartzSet n → ℝ≥0∞)
    (U : Set (schwartzSet n)) : Prop :=
  ∀ φ ∈ U, ∃ (s : ℕ) (p : Fin s → ι) (ε : ℝ), 0 < ε ∧
    ∀ ψ δ : schwartzSet n, δ.1 = ψ.1 - φ.1 →
      (∀ a, F (p a) δ < ENNReal.ofReal ε) → ψ ∈ U
def decaySeminormFamily (n : ℕ) : ℕ × ℕ → schwartzSet n → ℝ≥0∞ :=
  fun kq φ => decaySeminorm kq.1 kq.2 φ.1
def IsSchwartzOpen (U : Set (schwartzSet n)) : Prop :=
  IsOpenForFamily (decaySeminormFamily n) U
def IsSchwartzClosed (U : Set (schwartzSet n)) : Prop :=
  IsSchwartzOpen Uᶜ
def schwartzOpenSets (n : ℕ) : Set (Set (schwartzSet n)) :=
  {U | IsSchwartzOpen U}
def GeneratesSchwartzTopology {ι : Type*} [Nonempty ι]
    (F : ι → schwartzSet n → ℝ≥0∞) : Prop :=
  ∀ U : Set (schwartzSet n), IsOpenForFamily F U ↔ U ∈ schwartzOpenSets n
def flatSchwartzSet (n : ℕ) : Set (Config n → ℂ) :=
  {φ | φ ∈ schwartzSet n ∧
    ∀ x ∈ fatDiagonal n, ∀ α : MultiIdx (CoordIndex n), configMultiDeriv α φ x = 0}
theorem flatSchwartzSet_eq_rapidDecaySet_inter (n : ℕ) :
    flatSchwartzSet n = rapidDecaySet n ∩ flatOnDiagonalSet n := by
  ext φ
  constructor
  · exact fun h => ⟨h.1, h.1.1, h.2⟩
  · exact fun h => ⟨h.1, h.2.2⟩
def IsLinearOnFlatSchwartz (S : flatSchwartzSet n → ℂ) : Prop :=
  (∀ φ ψ χ : flatSchwartzSet n, χ.1 = φ.1 + ψ.1 → S χ = S φ + S ψ) ∧
    ∀ (c : ℂ) (φ χ : flatSchwartzSet n), χ.1 = c • φ.1 → S χ = c * S φ
def flatSchwartzDualSet (n : ℕ) : Set (flatSchwartzSet n → ℂ) :=
  {S | IsLinearOnFlatSchwartz S ∧ ∃ (k q : ℕ) (b : ℝ), 0 ≤ b ∧
    ∀ φ : flatSchwartzSet n, ENNReal.ofReal ‖S φ‖ ≤ ENNReal.ofReal b * decaySeminorm k q φ.1}
def offDiagonalTestSet (n : ℕ) : Set (Config n → ℂ) :=
  {f | f ∈ testFunctionSet (Config n) ∧
    tsupport f ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n}
end YangMills.Construction.ConfigurationSpace
end
