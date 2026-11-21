import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CopiesOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign)
open Conventions (signedConj)
namespace MirrorGridsAllSides
namespace LiftTransport
variable {D : GridSetup} (g : ReflectionGrid D)
theorem lift_mem_torusCellObservables (hC : TorusCellStructure g) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    D.liftedObservable F ∈ g.torusCellObservables (D.proj '' S) := by
  obtain ⟨k, rfl⟩ := hS
  have hint : g.torusCellInterior (D.proj '' g.cell k) = D.proj '' interior (g.cell k) :=
    (hC.2.2.2.2 k k rfl).2.1
  have hedge : ∀ b ∈ ReflectionGrid.interiorLinks (D := D) (g.cell k),
      D.projLink b ∈ g.torusCellLinks (D.proj '' g.cell k) := by
    intro b hb
    constructor
    · rw [hint]
      exact ⟨b.initial, hb.1, rfl⟩
    · rw [hint]
      exact ⟨b.terminal, hb.2, rfl⟩
  obtain ⟨f, hf, ⟨c, hc⟩, rfl⟩ := hF
  refine ⟨fun u => f fun b => u ⟨D.projLink b.1, hedge b.1 b.2⟩,
    hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨c, fun u => hc _⟩,
    fun U => ?_⟩
  change f (ReflectionGrid.restrictField (g.cell k) (D.liftField U.1)) = _
  refine congrArg f (funext fun b => Subtype.ext ?_)
  exact InfiniteLattice.liftField_apply_of_mem U.2 b.1
theorem lift_actOn (h : ChessboardTori.LiftingRules.Statement) (r : g.reflectionGroup)
    {r' : D.Torus → D.Torus} (hr : D.Descends r.1 r') (F : D.GaugeField → ℂ) :
    EqOn (D.liftedObservable ((g.toLatticeSym r).actOn F))
      (D.pullbackObservable r' (D.liftedObservable F)) D.torusFields := by
  intro U hU
  have hcomm : D.proj ∘ (g.toLatticeSym r).toFun = r' ∘ D.proj := Eq.symm hr
  have hlift := (((h D).2.2.2 (g.toLatticeSym r) r' hcomm).2 U hU).1
  change F ((g.toLatticeSym r).pullbackField (D.liftField U)) =
    F (D.liftField (D.pullbackField r' U))
  rw [hlift]
theorem lift_transportTo (h : ChessboardTori.LiftingRules.Statement)
    (hG : ReflectionGroupActsOnCells g) (hT : TorusGroupActsOnCells g)
    {S S' : Set AmbientSpace} (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet)
    (F : D.GaugeField → ℂ) :
    EqOn (D.liftedObservable (g.transportTo S S' F))
      (g.torusTransportTo (D.proj '' S) (D.proj '' S') (D.liftedObservable F))
      D.torusFields := by
  intro U hU
  obtain ⟨hdesc, -, -, hsign, -, huniq, -, -⟩ := hT
  have hmv : (g.mover S S').1 '' S = S' := by
    obtain ⟨k, rfl⟩ := hS
    obtain ⟨k', rfl⟩ := hS'
    obtain ⟨r, hr, -⟩ := hG.2.1 k k'
    exact Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' g.cell k = g.cell k')
      ⟨r, hr⟩
  obtain ⟨s, hs⟩ := hdesc (g.mover S S').1 (g.mover S S').2
  have hcomm : D.proj ∘ (g.mover S S').1 = s.toFun ∘ D.proj := Eq.symm hs
  have hin : s.toFun ∈ g.inducedTorusMaps := ⟨_, (g.mover S S').2, hcomm⟩
  have himage : s.toFun '' (D.proj '' S) = D.proj '' S' := by
    calc s.toFun '' (D.proj '' S) = (s.toFun ∘ D.proj) '' S := (image_comp _ _ _).symm
      _ = (D.proj ∘ (g.mover S S').1) '' S := by rw [hcomm]
      _ = D.proj '' ((g.mover S S').1 '' S) := image_comp _ _ _
      _ = D.proj '' S' := by rw [hmv]
  have hchoice : g.torusCarrier (D.proj '' S) (D.proj '' S') ∈ g.inducedTorusMaps ∧
      g.torusCarrier (D.proj '' S) (D.proj '' S') '' (D.proj '' S) = D.proj '' S' :=
    Classical.epsilon_spec (p := fun r' : D.Torus → D.Torus =>
      r' ∈ g.inducedTorusMaps ∧ r' '' (D.proj '' S) = D.proj '' S') ⟨s.toFun, hin, himage⟩
  have hcarrier : g.torusCarrier (D.proj '' S) (D.proj '' S') = s.toFun :=
    (huniq _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩).unique hchoice ⟨hin, himage⟩
  have hsgn : g.torusSign s.toFun = orientationSign (g.mover S S').1 :=
    (hsign _ hin _ hcomm).symm
  have hcomm' : D.proj ∘ (g.toLatticeSym (g.mover S S')).toFun = s.toFun ∘ D.proj := hcomm
  have hlift := (((h D).2.2.2 (g.toLatticeSym (g.mover S S')) s.toFun hcomm').2 U hU).1
  change signedConj (orientationSign (g.mover S S').1)
      (F ((g.toLatticeSym (g.mover S S')).pullbackField (D.liftField U))) =
    signedConj (g.torusSign (g.torusCarrier (D.proj '' S) (D.proj '' S')))
      (F (D.liftField (D.pullbackField
        (g.torusCarrier (D.proj '' S) (D.proj '' S')) U)))
  rw [hcarrier, hsgn, hlift]
end LiftTransport
theorem allGridsLiftCompatibleWithTransport_holds
    (h₁ : ChessboardTori.LiftingRules.Statement)
    (h₂ : AllGridsReflectionGroupActsOnCells)
    (h₃ : AllGridsTorusCellStructure)
    (h₄ : AllGridsTorusGroupActsOnCells) :
    AllGridsLiftCompatibleWithTransport := by
  intro D g hg hs S hS F hF
  exact ⟨LiftTransport.lift_mem_torusCellObservables g (h₃ D g hg hs) hS hF,
    fun r r' hr => LiftTransport.lift_actOn g h₁ r hr F,
    fun S' hS' => LiftTransport.lift_transportTo g h₁ (h₂ D g hg)
      (h₄ D g hg hs) hS hS' F⟩
end MirrorGridsAllSides
end YangMills.Construction
end
