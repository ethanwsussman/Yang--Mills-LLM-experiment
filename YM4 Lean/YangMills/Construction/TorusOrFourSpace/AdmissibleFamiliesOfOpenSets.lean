import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind) {n : ℕ+}
structure AdmissibleWith (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop where
  radius_pos : 0 < R
  sep_pos : 0 < d
  isOpen_mem : ∀ i, IsOpenQ D E (G i)
  diam_le : ∀ i, setDiam D E (G i) ≤ ENNReal.ofReal (2 * R)
  diam_lt_quarter_of_torus : E = Kind.torus → ∀ i, setDiam D E (G i) < ENNReal.ofReal (D.side / 4)
  sep_le_setInfDist : ∀ i i', i ≠ i' → ENNReal.ofReal d ≤ setInfDist D E (G i) (G i')
def Admissible (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  ∃ R d : ℝ, AdmissibleWith D E R d G
def maxMemberDiam (G : Fin (n : ℕ) → Set (E.Pt D)) : ℝ≥0∞ :=
  Finset.univ.sup' ⟨⟨0, n.pos⟩, Finset.mem_univ _⟩ fun i => setDiam D E (G i)
def memberInter (G G' : Fin (n : ℕ) → Set (E.Pt D)) :
    Fin (n : ℕ) → Set (E.Pt D) :=
  fun i => G i ∩ G' i
end YangMills.Construction.PeriodicSpace.Kind
