import YangMills.Construction.Cumulants.JointCumulantsOfComplexVariables
import YangMills.Construction.InfiniteLattice.CutoffMotionsAndPlaquetteSquares
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.Lattice.PlaquetteFramesAndCircuits
import YangMills.Construction.Torus.MapOfATorusInducedByAHypercubicMotion
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace CutoffLatticeStates
open InfiniteLattice
section Circuits
variable {L K : ℕ}
def meshSite (e : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ)) :
    LatticePoint (refinedSpacing L K) :=
  ⟨e.1, by
    obtain ⟨μ, h | h⟩ := e.2
    · rw [h]
      exact (axisStep _ μ).2
    · rw [h]
      exact neg_mem (axisStep _ μ).2⟩
def linkAlong (y : LatticePoint (refinedSpacing L K))
    (e : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ)) :
    Link (refinedSpacing L K) where
  initial := y
  terminal := y + meshSite e
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := e.2
    · exact ⟨μ, Or.inl (by rw [add_sub_cancel_left]; exact Subtype.ext h)⟩
    · exact ⟨μ, Or.inr (by rw [add_sub_cancel_left]; exact Subtype.ext h)⟩
def plaquetteOfAxes {a : ℝ} (x : LatticePoint a) (μ ν : Fin 4) (h : μ ≠ ν) :
    ElementaryPlaquette a :=
  if hl : μ < ν then ⟨x, μ, ν, hl⟩ else ⟨x, ν, μ, lt_of_le_of_ne (not_lt.mp hl) h.symm⟩
def squareOfAxes {a : ℝ} (x : LatticePoint a) (μ ν : Fin 4) : Set AmbientSpace :=
  {q | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
    q = (x : AmbientSpace) + s • (Pi.single μ a : AmbientSpace) + t • (Pi.single ν a : AmbientSpace)}
theorem closedSquare_plaquetteOfAxes {a : ℝ} (x : LatticePoint a) (μ ν : Fin 4) (h : μ ≠ ν) :
    (plaquetteOfAxes x μ ν h).closedSquare = squareOfAxes x μ ν := by
  have key : ∀ (s t : ℝ) (κ ρ : Fin 4),
      a • (s • (Pi.single κ 1 : AmbientSpace) + t • (Pi.single ρ 1 : AmbientSpace)) =
        s • (Pi.single κ a : AmbientSpace) + t • (Pi.single ρ a : AmbientSpace) := by
    intro s t κ ρ
    funext σ
    simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> ring
  ext q
  unfold plaquetteOfAxes ElementaryPlaquette.closedSquare squareOfAxes
  split_ifs with hl
  · simp only [mem_ofPred_eq, key, add_assoc]
  · simp only [mem_ofPred_eq, key, add_assoc]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨t, ht, s, hs, by rw [add_comm (s • _)]⟩
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨t, ht, s, hs, by rw [add_comm (s • _)]⟩
def IsFrame (p : ElementaryPlaquette (refinedSpacing L K))
    (e e' : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ)) : Prop :=
  (PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) p.lowAxis ∧
      PeriodicLattice.PlaquetteCircuits.IsAlongAxis e'.1 L (K : ℤ) p.highAxis) ∨
    (PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) p.highAxis ∧
      PeriodicLattice.PlaquetteCircuits.IsAlongAxis e'.1 L (K : ℤ) p.lowAxis)
def frameBase (p : ElementaryPlaquette (refinedSpacing L K))
    (e e' : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ)) : AmbientSpace :=
  p.center - (1 / 2 : ℝ) • e.1 - (1 / 2 : ℝ) • e'.1
def circuitFrom (c : LatticePoint (refinedSpacing L K))
    (e e' : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ)) :
    Fin 4 → Link (refinedSpacing L K) :=
  ![linkAlong c e, linkAlong (c + meshSite e) e', linkAlong (c + meshSite e + meshSite e') (-e),
    linkAlong (c + meshSite e') (-e')]
def IsCircuit (p : ElementaryPlaquette (refinedSpacing L K))
    (γ : Fin 4 → Link (refinedSpacing L K)) : Prop :=
  ∃ e e' : PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ), IsFrame p e e' ∧
    ∃ c : LatticePoint (refinedSpacing L K), (c : AmbientSpace) = frameBase p e e' ∧
      γ = circuitFrom c e e'
def loopHolonomy {a : ℝ} (U : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (γ : Fin 4 → Link a) : Matrices.ComplexMatrix2.specialUnitary :=
  U (γ 0) * U (γ 1) * U (γ 2) * U (γ 3)
end Circuits
section Isometries
variable {a : ℝ}
abbrev refinedLatticeMotions (L K : ℕ) : Set (AmbientSpace → AmbientSpace) :=
  latticeMotions (refinedSpacing L K)
def IsAffineDecomposition (a : ℝ) (r : AmbientSpace → AmbientSpace)
    (p : (AmbientSpace →ₗ[ℝ] AmbientSpace) × AmbientSpace) : Prop :=
  p.1 ∈ hypercubicGroup ∧ p.2 ∈ latticeSubgroup a ∧ ∀ x, r x = p.1 x + p.2
def affineDecomposition (r : latticeMotions a) :
    (AmbientSpace →ₗ[ℝ] AmbientSpace) × AmbientSpace :=
  Classical.epsilon (IsAffineDecomposition a r.1)
theorem isAffineDecomposition_affineDecomposition (r : latticeMotions a) :
    IsAffineDecomposition a r.1 (affineDecomposition r) := by
  obtain ⟨w, hw, v, hv, h⟩ := r.2
  exact Classical.epsilon_spec (p := IsAffineDecomposition a r.1) ⟨(w, v), hw, hv, h⟩
def inducedTorusMap (L m : ℕ) (r : latticeMotions a) :
    PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m :=
  torusAffineMap L m (affineDecomposition r).1 (affineDecomposition r).2
def mapLoop (r : latticeMotions a) (γ : Fin 4 → Link a) : Fin 4 → Link a :=
  fun i => (latticeMotionSymmetry r).linkMap (γ i)
def mapPlaquette (r : latticeMotions a) (p : ElementaryPlaquette a) : ElementaryPlaquette a :=
  open Classical in
  if h : ∃ q : ElementaryPlaquette a, q.closedSquare = p.squareImage r.1 then h.choose else p
def motionInverse (r : latticeMotions a) : AmbientSpace → AmbientSpace := Function.invFun r.1
def pushFunction {E : Type*} (r : latticeMotions a) (f : AmbientSpace → E) : AmbientSpace → E :=
  f ∘ motionInverse r
def pushTuple {E : Type*} {n : ℕ} (r : latticeMotions a) (f : Fin n → AmbientSpace → E) :
    Fin n → AmbientSpace → E :=
  fun i => pushFunction r (f i)
end Isometries
section States
variable {a : ℝ}
def IsState (ν : Measure (GaugeField a)) : Prop := IsProbabilityMeasure ν
def expectation (ν : Measure (GaugeField a)) (F : GaugeField a → ℂ) : ℂ := ∫ U, F U ∂ν
def IsMotionInvariant (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Prop :=
  ∀ r : latticeMotions a, IsLatticeMotionInvariant ν r
end States
def IsWeakLimitPoint (L K : ℕ) (β : ℝ) (ν : Measure (GaugeField (refinedSpacing L K))) : Prop :=
  IsState ν ∧ ∀ (k : ℕ) (F : Fin k → C(GaugeField (refinedSpacing L K), ℂ)) (ε : ℝ), 0 < ε →
    ∀ ℓ₀ ∈ PeriodicLattice.torusSides L, ∃ m' : ℕ, 0 < m' ∧ ℓ₀ ≤ PeriodicLattice.torusSide L m' ∧
      ∀ j, ‖expectation (liftedWilsonMeasure L m' K β) (F j) - expectation ν (F j)‖ < ε
def weakLimitPoints (L K : ℕ) (β : ℝ) : Set (Measure (GaugeField (refinedSpacing L K))) :=
  {ν | IsWeakLimitPoint L K β ν}
section Moments
variable {a : ℝ}
def complexSmearedEnergy (f : AmbientSpace → ℝ) (U : GaugeField a) : ℂ :=
  ((smearedEnergy f U : ℝ) : ℂ)
def connectedFunction {n : ℕ} (ν : Measure (GaugeField a)) (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  Cumulants.complexJointCumulant ν fun i => complexSmearedEnergy (f i)
def centeredMomentAgainst {n : ℕ} (ν' ν : Measure (GaugeField a))
    (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  expectation ν' fun U => ∏ i, (complexSmearedEnergy (f i) U - expectation ν (complexSmearedEnergy (f i)))
def centeredMoment {n : ℕ} (ν : Measure (GaugeField a)) (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  centeredMomentAgainst ν ν f
end Moments
end CutoffLatticeStates
end YangMills.Construction
