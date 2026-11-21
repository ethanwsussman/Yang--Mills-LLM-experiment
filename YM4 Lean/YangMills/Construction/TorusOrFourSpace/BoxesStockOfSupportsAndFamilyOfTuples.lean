import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicSpace
structure RationalBox where
  lo : Fin 4 → ℚ
  hi : Fin 4 → ℚ
  lo_lt_hi : ∀ μ, lo μ < hi μ
namespace RationalBox
def toSet (b : RationalBox) : Set (Fin 4 → ℝ) :=
  Set.pi Set.univ fun μ => Set.Icc (b.lo μ : ℝ) (b.hi μ : ℝ)
def diam (b : RationalBox) : ℝ :=
  TorusMetric.euclidNormVec fun μ => (b.hi μ : ℝ) - (b.lo μ : ℝ)
end RationalBox
namespace Kind
variable (D : Params)
def AdmitsBox (b : RationalBox) : Kind → Prop
  | .euclidean => True
  | .torus => b.diam < D.side / 2
variable (E : Kind)
def supportStock : Set (Set (E.Pt D)) :=
  {Q | ∃ (r : ℕ) (b : Fin r → RationalBox), (∀ i, E.AdmitsBox D (b i)) ∧
    Q = ⋃ i, E.quotMap D '' (b i).toSet}
def c1VanishingOutside (Q : Set (E.Pt D)) : Set (E.Pt D → ℝ) :=
  {f | f ∈ c1Set D E ∧ ∀ y, y ∉ Q → f y = 0}
def IsDenseWrt (N : (E.Pt D → ℝ) → ℝ≥0∞) (V A : Set (E.Pt D → ℝ)) : Prop :=
  ∀ f ∈ V, ∀ ε : ℝ, 0 < ε → ∃ g ∈ A, N (f - g) < ENNReal.ofReal ε
def IsDenseFamily (F : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Q, (F Q).Countable ∧ F Q ⊆ c1VanishingOutside D E Q ∧
    IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) (F Q)
def IsBuiltFrom (F : supportStock D E → Set (E.Pt D → ℝ)) {n : ℕ}
    (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → supportStock D E) : Prop :=
  Pairwise (fun i j => Disjoint (Q i : Set (E.Pt D)) (Q j : Set (E.Pt D))) ∧
    ∀ i, φ i ∈ F (Q i)
def tupleFamily (F : supportStock D E → Set (E.Pt D → ℝ)) :
    Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  {p | 1 ≤ p.1 ∧ ∃ Q, IsBuiltFrom D E F p.2 Q}
def tupleLen (p : Σ n : ℕ, Fin n → E.Pt D → ℝ) : ℕ := p.1
def tupleFamilyLengthGeTwo (F : supportStock D E → Set (E.Pt D → ℝ)) :
    Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  {p | p ∈ tupleFamily D E F ∧ 2 ≤ tupleLen D E p}
end Kind
end PeriodicSpace
end YangMills.Construction
