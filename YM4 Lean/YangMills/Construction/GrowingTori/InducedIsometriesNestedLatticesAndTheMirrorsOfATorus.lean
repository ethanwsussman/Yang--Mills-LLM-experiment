import YangMills.Construction.GrowingTori.IsometriesMirrorsAndAdicPointsAlongGrowingTori
import YangMills.Construction.Lattice.AdicGridPointsPositive
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GrowingTori.LatticeMotions
open TorusMetric TorusTransport TimeAxisSymbols
def affineMotions_isGroup : Prop :=
  id ∈ affineHyperoctahedral ∧
  (∀ f ∈ affineHyperoctahedral, ∀ g ∈ affineHyperoctahedral, f ∘ g ∈ affineHyperoctahedral) ∧
  (∀ f ∈ affineHyperoctahedral, ∃ g ∈ affineHyperoctahedral, f ∘ g = id ∧ g ∘ f = id) ∧
  (∀ v : Fin 4 → ℝ, ⇑(translationEquiv v) ∈ affineHyperoctahedral) ∧
  (∀ w : hyperoctahedral, ⇑w.1 ∈ affineHyperoctahedral) ∧
  (∀ (i : Fin 4) (c : ℝ), hyperplaneReflect i c ∈ affineHyperoctahedral)
def periodicMotion_isIsometry (L : ℕ) : Prop :=
  ∀ (g : TorusPeriodization.euclideanMotions) (m : ℕ+),
    (∃! F : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
      F ∘ torusProj (PeriodicLattice.torusSide L m) =
        torusProj (PeriodicLattice.torusSide L m) ∘ (g : Equiv.Perm (Fin 4 → ℝ))) ∧
    Function.Bijective (GrowingTori.periodicMotion L m g) ∧
    ∀ p q : PeriodicLattice.FourTorus L m,
      torusEuclidNorm (GrowingTori.periodicMotion L m g p -
        GrowingTori.periodicMotion L m g q) = torusEuclidNorm (p - q)
def meshLattices_nested (L : ℕ) : Prop :=
  ∀ j k : ℕ+, j ≤ k →
    {t : ℝ | ∃ n : ℤ, t = (n : ℝ) * PeriodicLattice.meshSize L ((j : ℕ) : ℤ)} ⊆
      {t : ℝ | ∃ n : ℤ, t = (n : ℝ) * PeriodicLattice.meshSize L ((k : ℕ) : ℤ)}
def adicGridPoints_dense (L : ℕ) : Prop :=
  Dense (PeriodicLattice.adicGridPointsPositive L)
def timeAxisStabilizer_isSubgroup : Prop :=
  (1 : hyperoctahedral).1 timeAxisVec = timeAxisVec ∧
  (∀ w w' : hyperoctahedral, w.1 timeAxisVec = timeAxisVec → w'.1 timeAxisVec = timeAxisVec →
    (w * w').1 timeAxisVec = timeAxisVec) ∧
  (∀ w : hyperoctahedral, w.1 timeAxisVec = timeAxisVec →
    (w⁻¹ : hyperoctahedral).1 timeAxisVec = timeAxisVec)
def timeAxisStabilizer_fixesTime : Prop :=
  ∀ w : timeAxisStabilizer,
    (∀ x : Fin 4 → ℝ, w.1.1 x 3 = x 3) ∧
    ⇑w.1.1 '' {x : Fin 4 → ℝ | 0 < x 3} = {x : Fin 4 → ℝ | 0 < x 3} ∧
    ⇑w.1.1 '' {x : Fin 4 → ℝ | x 3 = 0} = {x : Fin 4 → ℝ | x 3 = 0} ∧
    ⇑w.1.1 ∘ timeReflect = timeReflect ∘ ⇑w.1.1 ∧
    ∀ y : Fin 3 → ℝ,
      w.1.1 (spaceTimePoint y 0) = spaceTimePoint (GrowingTori.spatialAct w y) 0
def torusReflection_eq_mirror (L : ℕ) : Prop :=
  ∀ (K m : ℕ+) (i : Fin 4) (c : ℝ), AxisReflection.IsLinkLevel L K c →
    AxisReflection.IsLinkLevel L K (c + (L : ℝ) ^ (m : ℕ)) ∧
    {x : Fin 4 → ℝ | x i = c} ∈ AxisReflection.linkPlanes L K ∧
    {x : Fin 4 → ℝ | x i = c + (L : ℝ) ^ (m : ℕ)} ∈ AxisReflection.linkPlanes L K ∧
    ∃ M : InfiniteLattice.PeriodicMirror L m ((K : ℕ) : ℤ),
      M.axis = i ∧ M.level = c ∧
      M.planes = torusProj (PeriodicLattice.torusSide L m) ''
        ({x : Fin 4 → ℝ | x i = c} ∪
          {x : Fin 4 → ℝ | x i = c + PeriodicLattice.torusSide L m / 2}) ∧
      GrowingTori.torusReflection L m i c = M.reflectEquiv
def motions_lattices_mirrors : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (affineMotions_isGroup ∧ periodicMotion_isIsometry L) ∧
    meshLattices_nested L ∧
    adicGridPoints_dense L ∧
    (timeAxisStabilizer_isSubgroup ∧ timeAxisStabilizer_fixesTime) ∧
    torusReflection_eq_mirror L
end YangMills.Construction.GrowingTori.LatticeMotions
end
