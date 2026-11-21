import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsAFunctional
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsGaugeInvariant
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsIsometryInvariant
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.LogNormaliserIsFunctional
open Matrices PeriodicOperators.Tempered Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open Matrices.PowerExpCharts
variable {L n : ℕ}
def gaugeFieldsAt (L n : ℕ) (d : ℤ) : Set (PeriodicLattice.Bond L n d → ComplexMatrix2) :=
  {U | PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U}
def gaugeMapsAt (L n : ℕ) (d : ℤ) : Set (PeriodicLattice.Site L n d → ComplexMatrix2) :=
  {u | PeriodicLattice.IsGaugeMap PeriodicLattice.compactGaugeGroup u}
def fieldOfPositiveValues (d : ℤ) (w : PeriodicLattice.PositivelyOrientedBond L n d → ComplexMatrix2) :
    PeriodicLattice.Bond L n d → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then (w ⟨b.opposite, h'⟩)⁻¹
    else 1
def transportField (d : ℤ) (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (V : PeriodicLattice.Bond L n d → ComplexMatrix2) : PeriodicLattice.Bond L n d → ComplexMatrix2 :=
  fun b => V (Classical.epsilon fun b' : PeriodicLattice.Bond L n d =>
    b'.source = (Classical.epsilon fun x' : PeriodicLattice.Site L n d => f x' = b.source) ∧
      b'.target = (Classical.epsilon fun x' : PeriodicLattice.Site L n d => f x' = b.target))
structure InvarianceConditions (d : ℤ) (F : (PeriodicLattice.Bond L n d → ComplexMatrix2) → ℝ) : Prop where
  analytic : ∃ 𝒰 : Set (PeriodicLattice.Bond L n d → ComplexMatrix2), (fun _ => (1 : ComplexMatrix2)) ∈ 𝒰 ∧
    ∃ _ : Fintype (PeriodicLattice.PositivelyOrientedBond L n d),
      IsSubspaceAnalyticToCoords (R := PeriodicLattice.PositivelyOrientedBond L n d) (S := Empty) (l := 1) ⊥
        {q | fieldOfPositiveValues d (groupComponent q) ∈ 𝒰}
        fun q _ => (F (fieldOfPositiveValues d (groupComponent q)) : ℂ)
  locallyGauge : ∀ᶠ q in 𝓝[gaugeMapsAt L n d] (fun _ => (1 : ComplexMatrix2)) ×ˢ
      𝓝[gaugeFieldsAt L n d] (fun _ => (1 : ComplexMatrix2)),
    F (PeriodicLattice.gaugeTransform q.1 q.2) = F q.2
  globalGauge : ∀ᶠ W in 𝓝[gaugeFieldsAt L n d] (fun _ => (1 : ComplexMatrix2)),
    ∀ v ∈ gaugeMapsAt L n d, (∀ x x', v x = v x') → F (PeriodicLattice.gaugeTransform v W) = F W
  symmetry : ∀ᶠ W in 𝓝[gaugeFieldsAt L n d] (fun _ => (1 : ComplexMatrix2)),
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving f →
      f '' (PeriodicLattice.sublattice L n d : Set (PeriodicLattice.FourTorus L n)) =
        PeriodicLattice.sublattice L n d → F (transportField d f W) = F W
theorem InvarianceConditions.cast {d d' : ℤ} (h : d = d') {F : (PeriodicLattice.Bond L n d → ComplexMatrix2) → ℝ}
    (hF : InvarianceConditions d F) :
    InvarianceConditions d' fun U => F (U ∘ Equiv.cast (congrArg (PeriodicLattice.Bond L n) h)) := by
  subst h
  exact hF
theorem continuous_asGroupFactors {σ : Type} :
    Continuous (asGroupFactors : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p11373 <;> assumption
theorem holomorphicScalar_of_coords_one {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
theorem isAdmissibleMember_of_invariance {F : (UnitEdge L n → ComplexMatrix2) → ℝ}
    (hF : InvarianceConditions (PeriodicLattice.levelDepth 0 0) F)
    (h1 : F (identityField L n) = 0) : IsAdmissibleMember F := by
  obtain ⟨⟨𝒰, h𝒰, inst, ⟨-, O₃, hO₃, hE⟩, hRA⟩, hg, hc, hi⟩ := hF
  have hmem : ∀ {w : PositiveUnitEdge L n → ComplexMatrix2}, w ∈ specialUnitaryPower (PositiveUnitEdge L n) →
      asGroupFactors w ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (PositiveUnitEdge L n) :=
    fun hw => ⟨(Submodule.mem_bot ℝ).2 (funext fun e => e.elim), hw⟩
  have hin : ∀ {w : PositiveUnitEdge L n → ComplexMatrix2},
      w ∈ asGroupFactors ⁻¹' O₃ ∩ specialUnitaryPower (PositiveUnitEdge L n) →
      asGroupFactors w ∈ {q | fieldOfPositiveValues (L := L) (n := n) (PeriodicLattice.levelDepth 0 0)
        (groupComponent q) ∈ 𝒰} := fun hw => by
    rw [hE]
    exact ⟨hw.1, hmem hw.2⟩
  refine
    { analytic := ?_
      map_identity := h1
      locallyGauge := ?_
      globalGauge := hc.mono fun U hU g hgr => hU _ (fun _ => hgr) fun _ _ => rfl
      symmetry := hi.mono fun U hU σ hσ hm => hU σ hσ hm }
  · have hone : (fun _ => (1 : ComplexMatrix2)) ∈ specialUnitaryPower (PositiveUnitEdge L n) :=
      fun _ => Submonoid.one_mem _
    have hfield : fieldOfPositiveValues (L := L) (n := n) (PeriodicLattice.levelDepth 0 0)
        (groupComponent (asGroupFactors fun _ => (1 : ComplexMatrix2))) = fun _ => (1 : ComplexMatrix2) := by
      funext b
      change fieldOfPositiveValues (PeriodicLattice.levelDepth 0 0) (fun _ => (1 : ComplexMatrix2)) b = 1
      simp [fieldOfPositiveValues]
    have hp : asGroupFactors (fun _ => (1 : ComplexMatrix2)) ∈
        {q | fieldOfPositiveValues (L := L) (n := n) (PeriodicLattice.levelDepth 0 0)
          (groupComponent q) ∈ 𝒰} := by
      change fieldOfPositiveValues _ (groupComponent _) ∈ 𝒰
      rw [hfield]
      exact h𝒰
    rw [hE] at hp
    refine ⟨inst, asGroupFactors ⁻¹' O₃ ∩ specialUnitaryPower (PositiveUnitEdge L n),
      ⟨_, hO₃.preimage continuous_asGroupFactors, rfl⟩, ⟨hp.1, hone⟩, fun β x hx => ?_⟩
    obtain ⟨𝒳, hx𝒳, -, -, Φ, hΦ, hEq⟩ := hRA _ (hin hx)
    refine ⟨𝒳, fun q => Φ q 0, hx𝒳, holomorphicScalar_of_coords_one (hΦ β), fun y hy hy𝒳 => ?_⟩
    exact congrFun (hEq ⟨hy𝒳, hmem hy.2⟩) 0
  · obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 hg
    exact ⟨{v | pa v}, hpa, hpb.mono fun U hU v _ hv => hab hv hU⟩
theorem totalNormaliserFunctional_top (hA : LogTotalNormaliserAnalytic)
    (hG : LogTotalNormaliserGaugeInvariant)
    (hI : LogTotalNormaliserSymmetryInvariant)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (i : ℕ) :
    InvarianceConditions (PeriodicLattice.levelDepth (i + 1) (i + 1)) (logTotalNormaliserRatio L n (i + 1)) := by
  obtain ⟨𝒰, h𝒰, -, hra⟩ := hA L n i hS hn
  have hg := hG L n i hS hn
  exact ⟨⟨𝒰, h𝒰.2, hra⟩, hg.1, hg.2,
    Filter.Eventually.mono (hI L n i hS hn) fun W hW f hf hm => hW f ⟨hf, hm⟩⟩
theorem claim_holds (hA : LogTotalNormaliserAnalytic)
    (hG : LogTotalNormaliserGaugeInvariant)
    (hI : LogTotalNormaliserSymmetryInvariant) : Claim := by
  intro L hS k hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  refine ⟨PeriodicLattice.torusSide L 1, ⟨1, Nat.one_pos, rfl⟩, fun s _ _ n hn _ => ?_⟩
  have hd : PeriodicLattice.levelDepth (i + 1) (i + 1) = PeriodicLattice.levelDepth 0 0 := by
    simp [PeriodicLattice.levelDepth]
  have he : topEdgeEquivUnit L n (i + 1) =
      Equiv.cast (congrArg (PeriodicLattice.Bond L n) hd) :=
    (cast_eq_edgeEquivOfVertexEquiv hd _ (topVertexEquivUnit_unitStep L n (i + 1))).symm
  have hfun : logNormaliserFamily L (i + 1) n = fun U =>
      logTotalNormaliserRatio L n (i + 1)
        (U ∘ Equiv.cast (congrArg (PeriodicLattice.Bond L n) hd)) := by
    funext U
    simp only [logNormaliserFamily, logNormaliserOfSide, he]
  change IsAdmissibleMember (logNormaliserFamily L (i + 1) n)
  rw [hfun]
  refine isAdmissibleMember_of_invariance ((totalNormaliserFunctional_top hA hG hI hS hn i).cast hd) ?_
  have htriv : identityField L n ∘
      Equiv.cast (congrArg (PeriodicLattice.Bond L n) hd) =
        trivialField L n (i + 1) (i + 1) := rfl
  simp only [htriv, logTotalNormaliserRatio, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    if_false, sub_self]
end YangMills.Construction.Tower.LogNormaliserIsFunctional
end
