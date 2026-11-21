import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusTransport
def subfamilyLength {n : ℕ+} (J : Finset (Fin n)) (hJ : J.Nonempty) : ℕ+ :=
  ⟨J.card, hJ.card_pos⟩
def subfamily {α : Type*} {n : ℕ+} (f : Fin n → α) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    Fin (subfamilyLength J hJ) → α :=
  fun j => f (J.orderEmbOfFin (k := subfamilyLength J hJ) rfl j)
namespace Domain
variable (D : TransportData)
def IsCompactSubset : (Y : Domain) → Set (Y.Point D) → Prop
  | .euclidean, A => IsCompact A
  | .torus, A => D.IsTorusCompact A
def ball : (Y : Domain) → Y.Point D → ℝ → Set (Y.Point D)
  | .euclidean, u, R => ballR4 u R
  | .torus, u, R => D.closedBall u R
abbrev FnFamily (Y : Domain) (n : ℕ+) (E : Type*) : Type _ := Fin n → Y.Point D → E
structure IsSepLipschitz (Y : Domain) {n : ℕ+} (f : Y.FnFamily D n ℝ) : Prop where
  lipschitzOn : ∀ i, Y.LipschitzOn D (f i)
  isCompact_support : ∀ i, Y.IsCompactSubset D (Y.fnSupport D (f i))
  pairwise_disjoint : ∀ i k, i ≠ k → Disjoint (Y.fnSupport D (f i)) (Y.fnSupport D (f k))
def FamilySupportedIn (Y : Domain) {n : ℕ+} (f : Y.FnFamily D n ℝ) (A : Set (Y.Point D)) : Prop :=
  ∀ i, Y.fnSupport D (f i) ⊆ A
def sepC1Families (Y : Domain) (n : ℕ+) : Set (Y.FnFamily D n ℝ) :=
  {f | Y.IsSepLipschitz D f ∧ ∀ i, Y.IsC1On D (f i)}
theorem univ_offDiag_nonempty {n : ℕ+} (hn : 2 ≤ (n : ℕ)) :
    (Finset.univ : Finset (Fin n)).offDiag.Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [Finset.mem_offDiag, Fin.ext_iff]
def supportGap (Y : Domain) {n : ℕ+} (hn : 2 ≤ (n : ℕ)) (f : Y.FnFamily D n ℝ)
    (_hf : Y.IsSepLipschitz D f) : ℝ≥0∞ :=
  (Finset.univ : Finset (Fin n)).offDiag.inf' (univ_offDiag_nonempty hn)
    fun p => Y.setDist D (Y.fnSupport D (f p.1)) (Y.fnSupport D (f p.2))
theorem le_supportGap_iff (Y : Domain) {n : ℕ+} (hn : 2 ≤ (n : ℕ)) {f : Y.FnFamily D n ℝ}
    (hf : Y.IsSepLipschitz D f) {c : ℝ≥0∞} :
    c ≤ Y.supportGap D hn f hf ↔
      ∀ i k, i ≠ k → c ≤ Y.setDist D (Y.fnSupport D (f i)) (Y.fnSupport D (f k)) := by
  simp only [supportGap, Finset.le_inf'_iff, Finset.mem_offDiag, Finset.mem_univ, true_and,
    Prod.forall]
def IsBallSupported (Y : Domain) {n : ℕ+} {E : Type*} [Zero E] (R : ℝ) (_hR : 0 < R)
    (f : Y.FnFamily D n E) : Prop :=
  ∀ i, ∃ u, Y.fnSupport D (f i) ⊆ Y.ball D u R
def RadiusAdmitted : (Y : Domain) → ℝ → Prop
  | .euclidean, _ => True
  | .torus, R => R < D.side / 4
def lipFamilies (Y : Domain) (n : ℕ+) (d R : ℝ) (_hd : 0 < d) (hR : 0 < R)
    (_hY : Y.RadiusAdmitted D R) : Set (Y.FnFamily D n ℝ) :=
  {f | (∀ i, Y.LipschitzOn D (f i)) ∧ Y.IsBallSupported D R hR f ∧
    ∀ i k, i ≠ k → ENNReal.ofReal d ≤ Y.setDist D (Y.fnSupport D (f i)) (Y.fnSupport D (f k))}
end Domain
variable (D : TransportData)
def sepC1FamiliesIn (n : ℕ+) (O : Set (Fin 4 → ℝ)) : Set (Domain.euclidean.FnFamily D n ℝ) :=
  {f | f ∈ Domain.euclidean.sepC1Families D n ∧ Domain.euclidean.FamilySupportedIn D f O}
def IsAdmissibleSets {q : ℕ+} (d R : ℝ) (_hd : 0 < d) (_hR : 0 < R)
    (A : Fin q → Set (Fin 4 → ℝ)) : Prop :=
  (∀ l, ∃ x, A l ⊆ ballR4 x R) ∧
    ∀ l k, l ≠ k → ENNReal.ofReal d ≤ Domain.euclidean.setDist D (A l) (A k)
def FamilyIsAdmissible {n : ℕ+} {E : Type*} [Zero E] (d R : ℝ) (hd : 0 < d) (hR : 0 < R)
    (f : Domain.euclidean.FnFamily D n E) : Prop :=
  IsAdmissibleSets D d R hd hR fun i => Domain.euclidean.fnSupport D (f i)
end TorusTransport
end YangMills.Construction
end
