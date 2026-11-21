import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.TorusMeasureSymmetry
open FixedSpacing (Params)
open LatticeCovering (descend spacingIndex mesh)
open InfiniteLattice (IsBoundedObservable latticeMotions latticeMotionAct liftedWilsonMeasure)
variable (P : Params)
abbrev GaugeConfig : Type := PeriodicLattice.CompactGaugeField P.L P.m (spacingIndex P)
abbrev TorusSymmetry : Type := PeriodicLattice.TorusLatticeSymmetry P.L P.m (P.K : ℕ)
def wilsonMean (Φ : GaugeConfig P → ℂ) : ℂ :=
  open Classical in
  PeriodicLattice.gibbsExpectation P.L P.m P.K P.β fun U =>
    if hU : U ∈ PeriodicLattice.compactGaugeFields P.L P.m (spacingIndex P) then Φ ⟨U, hU⟩ else 0
variable {P}
def ReadsBondImages (g : TorusSymmetry P) : Prop :=
  ∀ e : PeriodicLattice.Bond P.L P.m (spacingIndex P), g.IsBondImage e (g.bondMap e)
def MapsPlaquettes (g : TorusSymmetry P) : Prop :=
  (∀ q : PeriodicLattice.Plaquette P.L P.m (spacingIndex P),
    (g.plaquetteMap q).vertices = g.pointMap '' q.vertices) ∧
    Bijective g.plaquetteMap ∧
    ∀ (U : GaugeConfig P) (q : PeriodicLattice.Plaquette P.L P.m (spacingIndex P)),
      PeriodicLattice.plaquetteCost (g.pullback U).1 q =
        PeriodicLattice.plaquetteCost U.1 (g.plaquetteMap q)
def PreservesWilson (g : TorusSymmetry P) : Prop :=
  ∀ Φ : GaugeConfig P → ℂ, InfiniteLattice.LinkSetFunctions.IsBoundedBorel Φ →
    wilsonMean P (fun U => Φ (g.pullback U)) = wilsonMean P Φ
def PreservesLifted (r : latticeMotions (mesh P)) : Prop :=
  ∀ F : InfiniteLattice.GaugeField (mesh P) → ℂ, IsBoundedObservable F →
    ∫ V, latticeMotionAct r F V ∂liftedWilsonMeasure P.L P.m (P.K : ℕ) P.β =
      ∫ V, F V ∂liftedWilsonMeasure P.L P.m (P.K : ℕ) P.β
def InvarianceStatement : Prop :=
  ∀ (P : Params) (r : latticeMotions (mesh P)),
    (∃ g : TorusSymmetry P, g.toFun = descend P r.1 ∧ ReadsBondImages g ∧
      MapsPlaquettes g ∧ PreservesWilson g) ∧
      PreservesLifted r
end YangMills.Construction.TorusMeasureSymmetry
end
