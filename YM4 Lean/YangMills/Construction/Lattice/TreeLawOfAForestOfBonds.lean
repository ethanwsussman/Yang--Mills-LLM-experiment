import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open YangMills.Construction.BorelKernels YangMills.Construction.Matrices
open YangMills.Construction.PeriodicLattice.FaddeevPopov
universe u
variable {L m K : ℕ}
def forestEndpoints (T : Finset (GradedBond L m K)) : Finset (FourTorus L m) :=
  open Classical in T.image OrientedEdgeEnds.src ∪ T.image OrientedEdgeEnds.tgt
def nonRootVertices (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) :
    Finset (FourTorus L m) :=
  open Classical in forestEndpoints T \ R
def IsRootPath (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) (x : FourTorus L m)
    (Γ : List (FourTorus L m)) : Prop :=
  ∃ (r : FourTorus L m) (p : (edgeGraph T).Walk x r), r ∈ R ∧ p.IsPath ∧ p.support = Γ
def rootPath (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) (x : FourTorus L m) :
    List (FourTorus L m) :=
  Classical.epsilon (IsRootPath T R x)
def rootDepth (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m))
    (x : FourTorus L m) : ℕ :=
  (rootPath T R x).length - 1
def forestParent (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) (x : FourTorus L m) :
    FourTorus L m :=
  (rootPath T R x).getD 1 x
instance instNonemptyGradedBond : Nonempty (GradedBond L m K) := ⟨⟨0, Bond.forwardFrom 0 0⟩⟩
def parentBond (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) (x : FourTorus L m) :
    GradedBond L m K :=
  Classical.epsilon fun b => OrientedEdgeEnds.src b = forestParent T R x ∧
    OrientedEdgeEnds.tgt b = x ∧ (b ∈ T ∨ OrientedEdgeEnds.flip b ∈ T)
def parentBonds (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) :
    Finset (GradedBond L m K) :=
  open Classical in (nonRootVertices T R).image (parentBond T R)
abbrev AxialValues (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m)) : Type :=
  parentBonds T R → ComplexMatrix2.specialUnitary
def axialValueAt {T : Finset (GradedBond L m K)} {R : Finset (FourTorus L m)}
    (w : AxialValues T R) (x : FourTorus L m) : ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : parentBond T R x ∈ parentBonds T R then w ⟨_, h⟩ else 1
def gaugeRecursion {𝔅 : Finset (GradedBond L m K)} (T : Finset (GradedBond L m K))
    (R : Finset (FourTorus L m)) (w : AxialValues T R) (v : 𝔅 → ComplexMatrix2.specialUnitary) :
    ℕ → FourTorus L m → ComplexMatrix2.specialUnitary
  | 0, _ => 1
  | n + 1, x => (axialValueAt w x)⁻¹ * gaugeRecursion T R w v n (forestParent T R x) *
      linkValue v (parentBond T R x)
def axialGauge {𝔅 : Finset (GradedBond L m K)} (T : Finset (GradedBond L m K))
    (R : Finset (FourTorus L m)) (w : AxialValues T R) (v : 𝔅 → ComplexMatrix2.specialUnitary) :
    SiteGaugeGroup (nonRootVertices T R) :=
  fun x => gaugeRecursion T R w v (rootDepth T R x) x
variable {𝔅 T : Finset (GradedBond L m K)} {R : Finset (FourTorus L m)} {𝒴 : Type u}
  [MeasurableSpace 𝒴]
def treeLaw (T : Finset (GradedBond L m K)) (R : Finset (FourTorus L m))
    (prescribed : 𝒴 → AdjoinPoint (AxialValues T R)) (ξ : ConfigSpace 𝔅 𝒴) :
    Measure (SiteGaugeGroup (nonRootVertices T R)) :=
  match prescribed ξ.2 with
  | Sum.inl w => pointMass (axialGauge T R w ξ.1)
  | Sum.inr _ => pointMass 1
end YangMills.Construction.PeriodicLattice.ConfigSpaces
