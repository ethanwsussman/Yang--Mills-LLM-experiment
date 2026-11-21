import YangMills.Construction.Lattice.HistoriesCreationAndAges
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set ParameterChoice
namespace PeriodicLattice.CubesOfStep
variable {c : ChoiceUpToDegreeConstants} {m K : ℕ} {x : ℕ → ℝ} {D : ℕ → Type}
def bondsAvoiding {k : ℕ} (I : Set (BondAtLevel c.L m K k)) (W : Set (FourTorus c.L m)) :
    Set (BondAtLevel c.L m K k) :=
  {e | e ∈ I ∧ (e.source : FourTorus c.L m) ∉ W ∧ (e.target : FourTorus c.L m) ∉ W}
def regionsDisjointFrom (𝒜 : Set (Set (FourTorus c.L m))) (W : Set (FourTorus c.L m)) :
    Set (Set (FourTorus c.L m)) :=
  {Y | Y ∈ 𝒜 ∧ Disjoint Y W}
structure StepTracesAgreeOutside {k : ℕ} (W W' : Set (FourTorus c.L m))
    (s s' : StepTrace c m K x k) : Prop where
  densityRegion_eq : s.densityRegion \ W = s'.densityRegion \ W'
  plaquetteRegion_eq : s.plaquetteRegion \ W = s'.plaquetteRegion \ W'
  fluctuationRegion_eq : s.fluctuationRegion \ W = s'.fluctuationRegion \ W'
  region_eq : s.outcome.region \ W = s'.outcome.region \ W'
  bonds_eq : bondsAvoiding s.outcome.bonds W = bondsAvoiding s'.outcome.bonds W'
  cubes_eq : regionsDisjointFrom s.outcome.cubes W = regionsDisjointFrom s'.outcome.cubes W'
structure OperationTracesAgreeOutside {E : Type} {k : ℕ} (W W' : Set (FourTorus c.L m))
    (o o' : OperationTrace c m K x E k) : Prop where
  actedOn_eq : regionsDisjointFrom o.actedOn W = regionsDisjointFrom o'.actedOn W'
  complementCarriers_eq : ∀ d, regionsDisjointFrom (o.outcome.complementCarriers d) W =
    regionsDisjointFrom (o'.outcome.complementCarriers d) W'
  classTwo_eq : regionsDisjointFrom o.outcome.classTwo W =
    regionsDisjointFrom o'.outcome.classTwo W'
def unionRepaired {E : Type} {k : ℕ} (W : Set (FourTorus c.L m))
    (o : OperationTrace c m K x E k) :
    Set (FourTorus c.L m) :=
  W ∪ ⋃₀ o.outcome.repaired
def SameResidue : ∀ {k : ℕ}, Set (FourTorus c.L m) → Set (FourTorus c.L m) →
    LabelHistory c m K x D k → LabelHistory c m K x D k → Prop
  | _, _, _, .initial, .initial => True
  | _, U, U', .extend h s o, .extend h' s' o' =>
    StepTracesAgreeOutside (unionRepaired U o) (unionRepaired U' o') s s' ∧
      OperationTracesAgreeOutside (unionRepaired U o) (unionRepaired U' o') o o' ∧
      SameResidue (unionRepaired U o) (unionRepaired U' o') h h'
def SameOutput {k : ℕ} (h h' : LabelHistory c m K x D k) : Prop :=
  h.finalLabel = h'.finalLabel ∧ SameResidue ∅ ∅ h h'
def NoRepairs : ∀ {k : ℕ}, LabelHistory c m K x D k → Prop
  | _, .initial => True
  | _, .extend h _ o => NoRepairs h ∧ o.outcome.repaired = ∅
end PeriodicLattice.CubesOfStep
end YangMills.Construction
