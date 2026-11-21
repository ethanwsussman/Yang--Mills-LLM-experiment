import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice SpinHarmonics
namespace TransferOperators
variable {μ : Fin 4}
theorem coe_pointAtLevel_apply_axis (j : ℤ) (y : SliceSite μ) :
    ((pointAtLevel μ j y : LatticePoint 1) : AmbientSpace) μ = j := by
  have hy : ((y : LatticePoint 1) : AmbientSpace) μ = 0 := y.2
  change ((j • axisStep 1 μ : LatticePoint 1) : AmbientSpace) μ +
    ((y : LatticePoint 1) : AmbientSpace) μ = j
  rw [coe_zsmul_axisStep_apply_self, hy, add_zero]
theorem eq_and_eq_of_spatialLink_eq {j j' : ℤ} {b b' : SliceLink μ}
    (h : (spatialLink μ j b).1 = (spatialLink μ j' b').1) : j = j' ∧ b = b' := by
  have hs : pointAtLevel μ j b.source = pointAtLevel μ j' b'.source := congrArg Link.initial h
  have ht : pointAtLevel μ j b.target = pointAtLevel μ j' b'.target := congrArg Link.terminal h
  have hj : j = j' := by
    have hc := congrFun (congrArg Subtype.val hs) μ
    have hc' : ((pointAtLevel μ j b.source : LatticePoint 1) : AmbientSpace) μ =
      ((pointAtLevel μ j' b'.source : LatticePoint 1) : AmbientSpace) μ := hc
    rw [coe_pointAtLevel_apply_axis, coe_pointAtLevel_apply_axis] at hc'
    exact_mod_cast hc'
  subst hj
  exact ⟨rfl, Subtype.ext (Link.ext (add_left_cancel (a := j • axisStep 1 μ) hs)
    (add_left_cancel (a := j • axisStep 1 μ) ht))⟩
theorem spatialLink_ne_temporalLink (j j' : ℤ) (b : SliceLink μ) (y : SliceSite μ) :
    (spatialLink μ j b).1 ≠ (temporalLink μ j' y).1 := by
  intro h
  have hs : pointAtLevel μ j b.source = pointAtLevel μ j' y := congrArg Link.initial h
  have ht : pointAtLevel μ j b.target = pointAtLevel μ (j' + 1) y := congrArg Link.terminal h
  have cs : ((pointAtLevel μ j b.source : LatticePoint 1) : AmbientSpace) μ =
    ((pointAtLevel μ j' y : LatticePoint 1) : AmbientSpace) μ := congrFun (congrArg Subtype.val hs) μ
  have ct : ((pointAtLevel μ j b.target : LatticePoint 1) : AmbientSpace) μ =
    ((pointAtLevel μ (j' + 1) y : LatticePoint 1) : AmbientSpace) μ :=
    congrFun (congrArg Subtype.val ht) μ
  rw [coe_pointAtLevel_apply_axis, coe_pointAtLevel_apply_axis] at cs ct
  have ds : j = j' := by exact_mod_cast cs
  have dt : j = j' + 1 := by exact_mod_cast ct
  omega
namespace Stack
variable (S : Stack) (v : Set (SliceSite μ))
def indexPairs : Set (ℤ × SliceLink μ) :=
  {p | S.lower ≤ p.1 ∧ p.1 ≤ S.upper ∧ p.2 ∈ linksWithin v}
theorem snd_mem_linksWithin_of_mem_indexPairs : ∀ i ∈ S.indexPairs v, i.2 ∈ linksWithin v :=
  fun _ h => h.2.2
def transportedIndexed (U : GaugeField 1) :
    S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary :=
  fun p => S.transportedLinkVariable μ U p.1.1 p.1.2
def IsTemporalGaugeWith (u : S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField 1) : Prop :=
  (∀ p : S.indexPairs v, spatialLinkVariable μ U p.1.1 p.1.2 = u p) ∧
    ∀ j y, S.lower ≤ j → j < S.upper → y ∈ v → temporalLinkVariable μ U j y = 1
open Classical in
def temporalGaugeFamily (u : S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary) :
    positiveLinks 1 → Matrices.ComplexMatrix2.specialUnitary :=
  fun c => if h : ∃ p : S.indexPairs v, (spatialLink μ p.1.1 p.1.2).1 = c.1 then u h.choose else 1
def temporalGaugeField (u : S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary) :
    GaugeField 1 :=
  gaugeFieldOfPositive one_pos (S.temporalGaugeFamily v u)
theorem isTemporalGaugeWith_temporalGaugeField
    (u : S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary) :
    S.IsTemporalGaugeWith v u (S.temporalGaugeField v u) := by
  have key : ∀ c : positiveLinks 1,
      (S.temporalGaugeField v u) c.1 = S.temporalGaugeFamily v u c := fun c =>
    dif_pos c.2
  refine ⟨fun p => ?_, fun j y _ _ _ => ?_⟩
  · have hm : (spatialLink μ p.1.1 p.1.2).1 ∈ positiveLinks (1 : ℝ) := (spatialLink μ p.1.1 p.1.2).2
    have h : ∃ q : S.indexPairs v, (spatialLink μ q.1.1 q.1.2).1 = (spatialLink μ p.1.1 p.1.2).1 :=
      ⟨p, rfl⟩
    rw [spatialLinkVariable, key ⟨_, hm⟩, temporalGaugeFamily, dif_pos h]
    have h' := eq_and_eq_of_spatialLink_eq h.choose_spec
    have hp : h.choose = p := Subtype.ext (Prod.ext h'.1 h'.2)
    rw [hp]
  · have hm : (temporalLink μ j y).1 ∈ positiveLinks (1 : ℝ) := (temporalLink μ j y).2
    rw [temporalLinkVariable, key ⟨_, hm⟩, temporalGaugeFamily, dif_neg]
    rintro ⟨q, hq⟩
    exact spatialLink_ne_temporalLink _ _ _ _ hq
def temporalGaugeValue (F : GaugeField 1 → ℂ)
    (u : S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  F (S.temporalGaugeField v u)
end Stack
def IsPolynomialInLinkEntries (F : GaugeField 1 → ℂ) : Prop :=
  IsEntryPolynomial fun g : positiveLinks (1 : ℝ) → Matrices.ComplexMatrix2.specialUnitary =>
    F (gaugeFieldOfPositive one_pos g)
namespace TemporalGauge
def ObservableFactorsThroughTransported (S : Stack) (v : Set (SliceSite μ)) : Prop :=
  ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsGaugeInvariantFunction F →
    DependsOnlyOn (Subtype.val '' S.linksOver v) F →
      (∀ u U, S.IsTemporalGaugeWith v u U → F U = S.temporalGaugeValue v F u) ∧
      (∀ U, F U = S.temporalGaugeValue v F (S.transportedIndexed v U)) ∧
      Measurable (S.temporalGaugeValue v F) ∧
      (∃ C : ℝ, ∀ u, ‖S.temporalGaugeValue v F u‖ ≤ C) ∧
      IsDiagonalGaugeInvariant (S.snd_mem_linksWithin_of_mem_indexPairs v)
        (S.temporalGaugeValue v F) ∧
      (Continuous F → Continuous (S.temporalGaugeValue v F)) ∧
      (IsPolynomialInLinkEntries F → IsEntryPolynomial (S.temporalGaugeValue v F))
def TransportedFunctionIsObservable (S : Stack) (v : Set (SliceSite μ)) : Prop :=
  ∀ Φ : (S.indexPairs v → Matrices.ComplexMatrix2.specialUnitary) → ℂ, Measurable Φ →
    (∃ C : ℝ, ∀ u, ‖Φ u‖ ≤ C) →
    IsDiagonalGaugeInvariant (S.snd_mem_linksWithin_of_mem_indexPairs v) Φ →
      IsBoundedObservable (fun U => Φ (S.transportedIndexed v U)) ∧
      IsGaugeInvariantFunction (fun U => Φ (S.transportedIndexed v U)) ∧
      DependsOnlyOn (Subtype.val '' S.linksOver v)
        (fun U => Φ (S.transportedIndexed v U)) ∧
      (Continuous Φ → Continuous fun U => Φ (S.transportedIndexed v U)) ∧
      (IsEntryPolynomial Φ → IsPolynomialInLinkEntries fun U => Φ (S.transportedIndexed v U))
variable (μ) in
def FaceEnergiesInTransported (β : ℝ) (S : Stack) : Prop :=
  ∀ U : GaugeField 1,
    (∀ (j : ℤ) (b : SliceLink μ), S.lower ≤ j → j < S.upper →
      ((faceEnergy U (temporalPlaquette μ j b) : ℝ) : ℂ) =
        1 - (1 / 2 : ℂ) * Matrices.ComplexMatrix2.fullTrace ((S.transportedLinkVariable μ U j b *
          (S.transportedLinkVariable μ U (j + 1) b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2)) ∧
    (∀ (j : ℤ) (p : SlicePlaquette μ), S.lower ≤ j → j ≤ S.upper →
      ((faceEnergy U (shiftedPlaquette μ j p) : ℝ) : ℂ) =
        1 - (1 / 2 : ℂ) * Matrices.ComplexMatrix2.fullTrace ((plaquetteHolonomy p (subset_univ _)
          (S.transportedRestriction μ U j univ) : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2)) ∧
    ∀ (j : ℤ) (B : Block μ), S.lower ≤ j → j ≤ S.upper →
      (β : ℂ) * ∑ᶠ p : B.touchingPlaquettes,
          ((faceEnergy U (shiftedPlaquette μ j p.1) : ℝ) : ℂ) =
        B.sliceEnergy β (S.transportedRestriction μ U j (B.links : Set (SliceLink μ)))
          (S.transportedRestriction μ U j (B.thickened \ (B.links : Set (SliceLink μ))))
variable (μ) in
def GaugeActionOnTransported (S : Stack) : Prop :=
  ∀ (h : GaugeTransform 1) (U : GaugeField 1) (j : ℤ), S.lower ≤ j → j ≤ S.upper →
    (∀ y : SliceSite μ, S.parallelTransport μ (h.act U) j y =
      h.toFun (pointAtLevel μ S.lower y) * S.parallelTransport μ U j y *
        (h.toFun (pointAtLevel μ j y))⁻¹) ∧
    ∀ b : SliceLink μ, S.transportedLinkVariable μ (h.act U) j b =
      h.toFun (pointAtLevel μ S.lower b.source) * S.transportedLinkVariable μ U j b *
        (h.toFun (pointAtLevel μ S.lower b.target))⁻¹
def MainStatement : Prop :=
  ∀ (μ : Fin 4) (S : Stack),
    (∀ (v : Set (SliceSite μ)) [Finite v], (linksWithin v).Nonempty →
      ObservableFactorsThroughTransported S v ∧
        TransportedFunctionIsObservable S v) ∧
    (∀ β : ℝ, 0 < β → FaceEnergiesInTransported μ β S) ∧
    GaugeActionOnTransported μ S
end TemporalGauge
end TransferOperators
end YangMills.Construction
end
