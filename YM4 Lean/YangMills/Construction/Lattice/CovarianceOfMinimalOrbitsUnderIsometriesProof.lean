import YangMills.Construction.Lattice.CombSchemeGaugeLawAndConjugationProof
import YangMills.Construction.Lattice.ConstantSequenceAsADatumOfTheSetting
import YangMills.Construction.Lattice.CovarianceOfMinimalOrbitsUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import YangMills.Construction.Lattice.GluedDataUnderIsometries
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.ObjectsOfSequencesUnderIsometries
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometries
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.MinimalOrbitsUnderIsometries
variable {L m : ℕ} {j : ℤ}
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem coe_source_bondImage (hc : PreservesCells σ j) (b : Bond L m j) :
    ((bondImage σ b).source : FourTorus L m) = σ b.source := by
  rw [(hc.2.2.2.1 b).1]
  exact hc.1 _
theorem coe_target_bondImage (hc : PreservesCells σ j) (b : Bond L m j) :
    ((bondImage σ b).target : FourTorus L m) = σ b.target := by
  rw [(hc.2.2.2.1 b).2]
  exact hc.1 _
theorem bondImage_symm_bondImage (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (b : Bond L m j) :
    bondImage σ.symm (bondImage σ b) = b :=
  Bond.ext (Subtype.ext (by rw [coe_source_bondImage hc', coe_source_bondImage hc,
      Equiv.symm_apply_apply]))
    (Subtype.ext (by rw [coe_target_bondImage hc', coe_target_bondImage hc,
      Equiv.symm_apply_apply]))
theorem bondImage_bondImage_symm (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (b : Bond L m j) :
    bondImage σ (bondImage σ.symm b) = b :=
  bondImage_symm_bondImage (σ := σ.symm) hc' hc b
theorem siteImage_symm_siteImage (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (y : Site L m j) :
    siteImage σ.symm (siteImage σ y) = y :=
  Subtype.ext (by rw [hc'.1, hc.1, Equiv.symm_apply_apply])
theorem transportGaugeField_bondImage (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    transportGaugeField σ U (bondImage σ b) = U b :=
  congrArg U (bondImage_symm_bondImage hc hc' b)
theorem transportGaugeField_symm_transportGaugeField (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U :=
  funext fun b => transportGaugeField_bondImage hc hc' U b
theorem transportGaugeField_transportGaugeField_symm (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ (transportGaugeField σ.symm U) = U :=
  transportGaugeField_symm_transportGaugeField (σ := σ.symm) hc' hc U
theorem transportGaugeField_injective (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) :
    Function.Injective
      (transportGaugeField σ : (Bond L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2) :=
  Function.LeftInverse.injective (transportGaugeField_symm_transportGaugeField hc hc')
theorem transportSiteFunction_transportSiteFunction_symm (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (u : Site L m j → ComplexMatrix2) :
    transportSiteFunction σ (transportSiteFunction σ.symm u) = u :=
  funext fun y => congrArg u (siteImage_symm_siteImage hc' hc y)
theorem transportGaugeField_mem_compactGaugeFields (hc' : PreservesCells σ.symm j)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    transportGaugeField σ U ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => hU.1 _ trivial, fun b _ => ?_⟩
  show U (bondImage σ.symm b.opposite) = (U (bondImage σ.symm b))⁻¹
  rw [hc'.2.2.2.2.1 b]
  exact hU.2 _ trivial
theorem bondsInside_isReversalClosed (X : Set (FourTorus L m)) :
    IsReversalClosed (bondsInside X : Set (Bond L m j)) :=
  fun _ hb => ⟨hb.2, hb.1⟩
theorem bondImage_symm_mem_bondsInside_iff (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (X : Set (FourTorus L m)) (b : Bond L m j) :
    bondImage σ.symm b ∈ (bondsInside X : Set (Bond L m j)) ↔
      b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) := by
  rw [((hc.2.2.2.2.2.2 X).2.2)]
  constructor
  · intro h
    exact ⟨_, h, bondImage_bondImage_symm hc hc' b⟩
  · rintro ⟨b₀, hb₀, rfl⟩
    rwa [bondImage_symm_bondImage hc hc']
theorem extendByOne_transport (hc : PreservesCells σ j)
    (hc' : PreservesCells σ.symm j) (ℬ : Set (Bond L m j))
    (W : Bond L m j → ComplexMatrix2) :
    extendByOne (bondImage σ '' ℬ) (transportGaugeField σ W) =
      transportGaugeField σ (extendByOne ℬ W) := by
  classical
  funext b
  have h : b ∈ bondImage σ '' ℬ ↔ bondImage σ.symm b ∈ ℬ := by
    constructor
    · rintro ⟨b₀, hb₀, rfl⟩
      rwa [bondImage_symm_bondImage hc hc']
    · intro h
      exact ⟨_, h, bondImage_bondImage_symm hc hc' b⟩
  show (if b ∈ bondImage σ '' ℬ then W (bondImage σ.symm b) else 1) =
    if bondImage σ.symm b ∈ ℬ then W (bondImage σ.symm b) else 1
  simp only [h]
end Bonds
section Inner
variable {K : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
theorem extendByOne_of_mem_gaugeFieldsInside {X : Set (FourTorus L m)}
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsInside K X) : extendByOne (bondsInside X) U = U := by
  classical
  funext b
  by_cases hb : b ∈ (bondsInside X : Set (BondAtLevel L m K 0))
  · simp [extendByOne, hb]
  · simp [extendByOne, hb, hU.2 b hb]
theorem mem_compactGaugeFields_of_mem_gaugeFieldsInside {X : Set (FourTorus L m)}
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsInside K X) : U ∈ compactGaugeFields L m (levelDepth K 0) := by
  have h := extendByOne_mem_compactGaugeFields (bondsInside_isReversalClosed X) hU.1
  rwa [extendByOne_of_mem_gaugeFieldsInside hU] at h
theorem transportGaugeField_mem_gaugeFieldsInside (hc : PreservesCells σ (levelDepth K 0))
    (hc' : PreservesCells σ.symm (levelDepth K 0)) {X : Set (FourTorus L m)}
    {U : BondAtLevel L m K 0 → ComplexMatrix2} (hU : U ∈ gaugeFieldsInside K X) :
    transportGaugeField σ U ∈ gaugeFieldsInside K (σ '' X) := by
  have hreal := transportGaugeField_mem_compactGaugeFields hc'
    (mem_compactGaugeFields_of_mem_gaugeFieldsInside hU)
  refine ⟨⟨fun b _ => hreal.1 b trivial, fun b _ => hreal.2 b trivial⟩, fun b hb => ?_⟩
  exact hU.2 _ fun h => hb ((bondImage_symm_mem_bondsInside_iff hc hc' X b).1 h)
end Inner
structure Transports (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop where
  sites : ∀ j, i ≤ j → PreservesCells σ j
  objects : PreservesChainObjects i σ
  blocks : ∀ j, i ≤ j → IsometryInvariance.MapsBlocks σ j
  plaquette : ∀ j, i ≤ j → ∀ U ∈ compactGaugeFields L m j, ∀ p : Plaquette L m j,
    ComplexMatrix2.operatorNorm
        (plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) - 1) =
      ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)
  action : ∀ (K : ℕ) (a : ℤ) (X : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2),
    i ≤ levelDepth K 0 → i ≤ a → IsPartitionRegion a X →
      IsGaugeField compactGaugeGroup (bondsInside X) U →
      actionInside K (σ '' X) (transportGaugeField σ U) = actionInside K X U
  averages : ∀ K : ℕ, BlockFieldEquivariant K i σ
  regions : ∀ j, i ≤ j → ∀ X : Set (FourTorus L m), IsPartitionRegion j (σ '' X) ↔ IsPartitionRegion j X
  twisted : ∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ ℬ : Set (Bond L m j), IsReversalClosed ℬ →
    ∀ V₀ : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ V₀ →
      IsTwistedTransportOn σ ℬ V₀
theorem mem_complexGaugeGroup_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
theorem isGaugeField_complex_of_compact {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U) : IsGaugeField complexGaugeGroup ℬ U :=
  ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hU.1 b hb), hU.2⟩
theorem inv_mul_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) : g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem inv_inv_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem inv_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem inv_mem_unitaryGroup {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 (inv_mem_compact hg)).1
section Critical
variable {K : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
def IsCriticalWithin (K : ℕ) (X : Set (FourTorus L m)) (C : Set (BondAtLevel L m K 0 → ComplexMatrix2))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  U ∈ C ∧ ∀ (δ : ℝ) (c : ℝ → BondAtLevel L m K 0 → ComplexMatrix2), 0 < δ →
    (∀ t ∈ Ioo (-δ) δ, c t ∈ C) →
    (∀ b r s, DifferentiableOn ℝ (fun t => c t b r s) (Ioo (-δ) δ)) → c 0 = U →
    deriv (fun t => actionInside K X (c t)) 0 = 0
theorem isCriticalWithin_transport {X X' : Set (FourTorus L m)}
    {C C' : Set (BondAtLevel L m K 0 → ComplexMatrix2)}
    (hCC : ∀ U ∈ C, transportGaugeField σ U ∈ C')
    (hCC' : ∀ W ∈ C', transportGaugeField σ.symm W ∈ C)
    (hact : ∀ W ∈ C', actionInside K X (transportGaugeField σ.symm W) = actionInside K X' W)
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hTT : transportGaugeField σ.symm (transportGaugeField σ U) = U)
    (hU : IsCriticalWithin K X C U) : IsCriticalWithin K X' C' (transportGaugeField σ U) := by
  refine ⟨hCC U hU.1, fun δ c hδ hc hd h0 => ?_⟩
  have key := hU.2 δ (fun t => transportGaugeField σ.symm (c t)) hδ
    (fun t ht => hCC' _ (hc t ht)) (fun b r s => hd (bondImage σ b) r s)
    (by simp only [h0]; exact hTT)
  have heq : (fun t => actionInside K X (transportGaugeField σ.symm (c t))) =ᶠ[𝓝 0]
      fun t => actionInside K X' (c t) := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with t ht
    exact hact _ (hc t ht)
  rw [← heq.deriv_eq]
  exact key
structure TransportedConstraints (σ : FourTorus L m ≃ FourTorus L m) (X X' : Set (FourTorus L m))
    (C C' : Set (BondAtLevel L m K 0 → ComplexMatrix2)) : Prop where
  forward : ∀ U ∈ C, transportGaugeField σ U ∈ C'
  backward : ∀ W ∈ C', transportGaugeField σ.symm W ∈ C
  left : ∀ U : BondAtLevel L m K 0 → ComplexMatrix2,
    transportGaugeField σ.symm (transportGaugeField σ U) = U
  right : ∀ W : BondAtLevel L m K 0 → ComplexMatrix2,
    transportGaugeField σ (transportGaugeField σ.symm W) = W
  action : ∀ U ∈ C, actionInside K X' (transportGaugeField σ U) = actionInside K X U
theorem TransportedConstraints.action_symm {X X' : Set (FourTorus L m)}
    {C C' : Set (BondAtLevel L m K 0 → ComplexMatrix2)}
    (h : TransportedConstraints σ X X' C C') {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : W ∈ C') :
    actionInside K X (transportGaugeField σ.symm W) = actionInside K X' W := by
  have := h.action _ (h.backward W hW)
  rw [h.right] at this
  exact this.symm
theorem TransportedConstraints.isCriticalWithin_iff {X X' : Set (FourTorus L m)}
    {C C' : Set (BondAtLevel L m K 0 → ComplexMatrix2)} (h : TransportedConstraints σ X X' C C')
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    IsCriticalWithin K X' C' (transportGaugeField σ U) ↔ IsCriticalWithin K X C U := by
  constructor
  · intro hc
    have := isCriticalWithin_transport (σ := σ.symm) (X := X') (X' := X) (C := C') (C' := C)
      h.backward h.forward h.action (h.right _) hc
    rwa [h.left] at this
  · exact isCriticalWithin_transport h.forward h.backward (fun W hW => h.action_symm hW) (h.left U)
theorem TransportedConstraints.criticalRegular_eq_image {X X' : Set (FourTorus L m)}
    {C C' : Set (BondAtLevel L m K 0 → ComplexMatrix2)} (h : TransportedConstraints σ X X' C C')
    {Reg Reg' : (BondAtLevel L m K 0 → ComplexMatrix2) → Prop}
    (hReg : ∀ U ∈ C, Reg' (transportGaugeField σ U) ↔ Reg U) :
    {U | IsCriticalWithin K X' C' U ∧ Reg' U} =
      transportGaugeField σ '' {U | IsCriticalWithin K X C U ∧ Reg U} := by
  ext W
  constructor
  · rintro ⟨hc, hr⟩
    refine ⟨transportGaugeField σ.symm W, ?_, h.right W⟩
    have hc' : IsCriticalWithin K X' C'
        (transportGaugeField σ (transportGaugeField σ.symm W)) := by
      rwa [h.right]
    have hr' : Reg' (transportGaugeField σ (transportGaugeField σ.symm W)) := by
      rwa [h.right]
    exact ⟨(h.isCriticalWithin_iff _).1 hc', (hReg _ (h.backward W hc.1)).1 hr'⟩
  · rintro ⟨U, ⟨hc, hr⟩, rfl⟩
    exact ⟨(h.isCriticalWithin_iff U).2 hc, (hReg U hc.1).2 hr⟩
theorem singleOrbit_transport
    {T : (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2}
    (hT : Function.Injective T) {R R' : Set (BondAtLevel L m K 0 → ComplexMatrix2)}
    {O O' : (BondAtLevel L m K 0 → ComplexMatrix2) → Set (BondAtLevel L m K 0 → ComplexMatrix2)}
    (hR : R' = T '' R) (hO : ∀ U ∈ R, O' (T U) = T '' O U)
    (hOeq : ∀ U, ∀ W ∈ O U, O W = O U) :
    ((∃ U ∈ R', R' = O' U) ↔ ∃ U ∈ R, R = O U) ∧
      ((∃ U ∈ R, R = O U) → ∀ U ∈ R, ∀ U' ∈ R', O' U' = T '' O U) := by
  have hself : ∀ U₀, R = O U₀ → ∀ U ∈ R, O U = R := by
    intro U₀ h U hU
    rw [h] at hU
    rw [h]
    exact hOeq U₀ U hU
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨U', hU', h⟩
    rw [hR] at hU'
    obtain ⟨U, hU, rfl⟩ := hU'
    refine ⟨U, hU, ?_⟩
    rw [hO U hU, hR] at h
    exact (Function.Injective.image_injective hT) h
  · rintro ⟨U, hU, h⟩
    refine ⟨T U, hR ▸ mem_image_of_mem T hU, ?_⟩
    rw [hO U hU, hR, ← h]
  · rintro ⟨U₀, -, h⟩ U hU U' hU'
    rw [hR] at hU'
    obtain ⟨U₁, hU₁, rfl⟩ := hU'
    rw [hO U₁ hU₁, hself U₀ h U₁ hU₁, hself U₀ h U hU]
end Critical
section Regular
variable {K : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem extendByOne_univ (W : Bond L m j → ComplexMatrix2) : extendByOne univ W = W := by
  classical
  funext b
  simp [extendByOne]
theorem yangMillsCurrent_transport (C : Transports i σ) (C' : Transports i σ.symm)
    (hj : -(m : ℤ) < j) (hij : i ≤ j)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) {ξ : ℝ} (hξ : 0 < ξ)
    (b : Bond L m j) :
    yangMillsCurrent ξ (transportGaugeField σ U) b =
      twistedTransportForm σ U (yangMillsCurrent ξ U) b := by
  have hc := C.sites j hij
  have hc' := C'.sites j hij
  have ht := C.twisted j hj hij univ (fun _ _ => trivial) U (isGaugeField_complex_of_compact hU)
  have himg : bondSetTransport σ (univ : Set (Bond L m j)) = univ :=
    eq_univ_of_forall fun b => ⟨bondImage σ.symm b, trivial, bondImage_bondImage_symm hc hc' b⟩
  have hb : b ∈ currentDomain (bondSetTransport σ (univ : Set (Bond L m j))) := by
    rw [himg]
    exact fun p _ c _ => trivial
  have h := ht.current_transport ξ hξ b hb
  rwa [himg, extendByOne_univ, extendByOne_univ] at h
theorem operatorNorm_neg (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (-X) = ComplexMatrix2.operatorNorm X := norm_neg X
theorem twistedFormValue_of_isPositivelyOriented {V₀ A : Bond L m j → ComplexMatrix2}
    {b b' : Bond L m j}
    (hp : bondPreimage σ b' = b) (h : b.IsPositivelyOriented) :
    twistedFormValue σ V₀ A b' = A b := by
  unfold twistedFormValue
  rw [hp, if_pos h]
theorem twistedFormValue_of_not_isPositivelyOriented {V₀ A : Bond L m j → ComplexMatrix2}
    {b b' : Bond L m j}
    (hp : bondPreimage σ b' = b) (h : ¬b.IsPositivelyOriented) :
    twistedFormValue σ V₀ A b' = -ComplexMatrix2.conjugateBy (V₀ b.opposite)⁻¹ (A b.opposite) := by
  unfold twistedFormValue
  rw [hp, if_neg h]
theorem twistedTransportForm_of_isPositivelyOriented {V₀ A : Bond L m j → ComplexMatrix2}
    {b : Bond L m j} (h : b.IsPositivelyOriented) :
    twistedTransportForm σ V₀ A b = twistedFormValue σ V₀ A b :=
  if_pos h
theorem twistedTransportForm_of_not_isPositivelyOriented {V₀ A : Bond L m j → ComplexMatrix2}
    {b : Bond L m j} (h : ¬b.IsPositivelyOriented) :
    twistedTransportForm σ V₀ A b = -twistedFormValue σ V₀ A b.opposite :=
  if_neg h
theorem twistedTransportForm_opposite (hL : 1 < L) (hj : -(m : ℤ) < j)
    (V₀ A : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    twistedTransportForm σ V₀ A b.opposite = -twistedTransportForm σ V₀ A b := by
  have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
  by_cases hp : b.IsPositivelyOriented
  · rw [twistedTransportForm_of_not_isPositivelyOriented
      (Bond.opposite_not_isPositivelyOriented hL hj hp), hrr,
      twistedTransportForm_of_isPositivelyOriented hp]
  · rw [twistedTransportForm_of_not_isPositivelyOriented hp,
      twistedTransportForm_of_isPositivelyOriented (Bond.opposite_isPositivelyOriented hp), neg_neg]
theorem yangMillsCurrent_opposite (hL : 1 < L) (C : Transports i σ) (C' : Transports i σ.symm)
    (hj : -(m : ℤ) < j) (hij : i ≤ j) {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) {ξ : ℝ}
    (hξ : 0 < ξ) (b : Bond L m j) : yangMillsCurrent ξ U b.opposite = -yangMillsCurrent ξ U b := by
  have hc := C.sites j hij
  have hc' := C'.sites j hij
  have hV := transportGaugeField_mem_compactGaugeFields (σ := σ.symm) hc hU
  have e := fun c => yangMillsCurrent_transport C C' hj hij hV hξ c
  rw [transportGaugeField_transportGaugeField_symm hc hc'] at e
  rw [e, e, twistedTransportForm_opposite hL hj]
theorem operatorNorm_twistedTransportForm_bondImage
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hc : PreservesCells σ j) (hc' : PreservesCells σ.symm j)
    {V₀ A : Bond L m j → ComplexMatrix2} (hV : ∀ b, V₀ b ∈ compactGaugeGroup)
    (hA : ∀ b, A b.opposite = -A b) (b : Bond L m j) :
    ComplexMatrix2.operatorNorm (twistedTransportForm σ V₀ A (bondImage σ b)) =
      ComplexMatrix2.operatorNorm (A b) := by
  have hrr : ∀ c : Bond L m j, c.opposite.opposite = c := fun c => Bond.ext rfl rfl
  have hp : bondPreimage σ (bondImage σ b) = b := bondImage_symm_bondImage hc hc' b
  have hr : bondPreimage σ (bondImage σ b).opposite = b.opposite := by
    have : bondImage σ.symm (bondImage σ b).opposite =
        (bondImage σ.symm (bondImage σ b)).opposite :=
      hc'.2.2.2.2.1 _
    rw [bondImage_symm_bondImage hc hc'] at this
    exact this
  have hAd : ∀ c X, ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (V₀ c)⁻¹ X) =
      ComplexMatrix2.operatorNorm X := fun c X =>
    hN.2.1 X _ (inv_mem_unitaryGroup (hV c))
  by_cases h1 : (bondImage σ b).IsPositivelyOriented
  · rw [twistedTransportForm_of_isPositivelyOriented h1]
    by_cases h2 : b.IsPositivelyOriented
    · rw [twistedFormValue_of_isPositivelyOriented hp h2]
    · rw [twistedFormValue_of_not_isPositivelyOriented hp h2, operatorNorm_neg, hAd, hA,
        operatorNorm_neg]
  · rw [twistedTransportForm_of_not_isPositivelyOriented h1, operatorNorm_neg]
    by_cases h2 : b.opposite.IsPositivelyOriented
    · rw [twistedFormValue_of_isPositivelyOriented hr h2, hA, operatorNorm_neg]
    · rw [twistedFormValue_of_not_isPositivelyOriented hr h2, operatorNorm_neg, hrr b]
      exact hAd b (A b)
theorem hasCurrentAt_iff_mem_currentDomain (X : Set (FourTorus L m)) (b : BondAtLevel L m K 0) :
    HasCurrentAt K X b ↔ b ∈ currentDomain (bondsInside X) := by
  constructor
  · intro h p hp c hc
    exact Plaquette.LiesIn.boundaryBonds_liesIn (Z := sitesIn X) (fun c hc => h p hp c hc) c hc
  · intro h p hp
    have hcar : p.BondsWithin (bondsInside X) := h p hp
    have h₀ : Bond.forwardFrom p.origin p.firstAxis ∈ (bondsInside X : Set (BondAtLevel L m K 0)) :=
      hcar _ (by simp [Plaquette.boundaryBonds])
    have h₁ : Bond.forwardFrom (p.origin + unitStep L m (levelDepth K 0) p.firstAxis) p.secondAxis ∈
        (bondsInside X : Set (BondAtLevel L m K 0)) := hcar _ (by simp [Plaquette.boundaryBonds])
    have h₂ : (Bond.forwardFrom p.origin p.secondAxis).opposite ∈
        (bondsInside X : Set (BondAtLevel L m K 0)) := hcar _ (by simp [Plaquette.boundaryBonds])
    rintro c (rfl | rfl | rfl | rfl)
    · exact h₀.1
    · exact h₀.2
    · exact h₁.2
    · exact h₂.1
theorem isRegularField_transport (hL : 1 < L) (hm : 0 < m)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (C : Transports i σ) (C' : Transports i σ.symm) {ε : ℝ} {k : ℕ}
    {Ω Ω' : ℕ → Set (FourTorus L m)}
    (hik : ∀ q ≤ k, i ≤ levelDepth K q) (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q)
    {U : BondAtLevel L m K 0 → ComplexMatrix2} (hU : U ∈ gaugeFieldsInside K (Ω 0))
    (hreg : IsRegularField ε K k Ω U) :
    IsRegularField ε K k Ω' (transportGaugeField σ U) := by
  have hi0 : i ≤ levelDepth K 0 := hik 0 (Nat.zero_le k)
  have hc := C.sites _ hi0
  have hc' := C'.sites _ hi0
  have hj : -(m : ℤ) < levelDepth K 0 := by simp only [levelDepth]; omega
  have h0 : Ω' 0 = σ '' Ω 0 := hΩ 0 (Nat.zero_le k)
  obtain ⟨-, -, -, -, hbond, hplaq, -⟩ := C'.objects K k Ω' Ω hik
    (fun q hq => by rw [hΩ q hq, Equiv.symm_image_image])
  have hreal := mem_compactGaugeFields_of_mem_gaugeFieldsInside hU
  have hsymm : ∀ x ∈ Ω' 0, σ.symm x ∈ Ω 0 := by
    intro x hx
    rw [h0] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rwa [Equiv.symm_apply_apply]
  refine ⟨fun p hp => ?_, fun b' hb' hd => ?_⟩
  · have hq : plaquetteImage σ.symm p ∈
        (plaquettesInside (Ω 0) : Set (PlaquetteAtLevel L m K 0)) := by
      intro c hc₀
      have hmem : (c : FourTorus L m) ∈
          (fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) ''
            (plaquetteImage σ.symm p).vertices :=
        ⟨c, hc₀, rfl⟩
      rw [hc'.2.2.2.2.2.1 p] at hmem
      obtain ⟨_, ⟨c', hc'₀, rfl⟩, he⟩ := hmem
      rw [← he]
      exact hsymm _ (hp c' hc'₀)
    have h1 := hreg.1 _ hq
    have h2 := C'.plaquette _ hi0 _ (transportGaugeField_mem_compactGaugeFields hc' hreal) p
    rw [transportGaugeField_symm_transportGaugeField hc hc'] at h2
    rw [← h2, ← hplaq p]
    exact h1
  · have hbb : bondImage σ (bondImage σ.symm b') = b' := bondImage_bondImage_symm hc hc' b'
    have hξ : 0 < finestMeshInLevelUnits L k := by
      have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      exact zpow_pos this _
    have hbm : bondImage σ.symm b' ∈ (bondsMeeting (Ω 0) : Set (BondAtLevel L m K 0)) := by
      rcases hb' with h | h
      · left
        rw [coe_source_bondImage hc']
        exact hsymm _ h
      · right
        rw [coe_target_bondImage hc']
        exact hsymm _ h
    have hdef : HasCurrentAt K (Ω 0) (bondImage σ.symm b') := by
      have ht := C.twisted _ hj hi0 (bondsInside (Ω 0)) (bondsInside_isReversalClosed _) U
        (isGaugeField_complex_of_compact hU.1)
      have him : bondSetTransport σ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) =
          bondsInside (Ω' 0) := by
        rw [h0]
        exact ((hc.2.2.2.2.2.2 (Ω 0)).2.2).symm
      have hcd := ht.currentDomain_image
      rw [him] at hcd
      have hmem := (hasCurrentAt_iff_mem_currentDomain (Ω' 0) b').1 hd
      rw [hcd] at hmem
      obtain ⟨b₀, hb₀, rfl⟩ := hmem
      rw [bondImage_symm_bondImage hc hc']
      exact (hasCurrentAt_iff_mem_currentDomain _ _).2 hb₀
    have h1 := hreg.2 _ hbm hdef
    have hJ : ComplexMatrix2.operatorNorm
          (yangMillsCurrent (finestMeshInLevelUnits L k) (transportGaugeField σ U) b') =
        ComplexMatrix2.operatorNorm
          (yangMillsCurrent (finestMeshInLevelUnits L k) U (bondImage σ.symm b')) := by
      rw [yangMillsCurrent_transport C C' hj hi0 hreal hξ b']
      conv_lhs => rw [← hbb]
      exact operatorNorm_twistedTransportForm_bondImage hN hc hc' (fun b => hreal.1 b trivial)
        (yangMillsCurrent_opposite hL C C' hj hi0 hreal hξ) _
    rw [hJ, ← hbond b']
    exact h1
theorem isRegularField_transport_iff (hL : 1 < L) (hm : 0 < m)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (C : Transports i σ) (C' : Transports i σ.symm) {ε : ℝ} {k : ℕ}
    {Ω Ω' : ℕ → Set (FourTorus L m)}
    (hik : ∀ q ≤ k, i ≤ levelDepth K q) (hΩ : ∀ q ≤ k, Ω' q = σ '' Ω q)
    {U : BondAtLevel L m K 0 → ComplexMatrix2} (hU : U ∈ gaugeFieldsInside K (Ω 0)) :
    IsRegularField ε K k Ω' (transportGaugeField σ U) ↔ IsRegularField ε K k Ω U := by
  have hi0 : i ≤ levelDepth K 0 := hik 0 (Nat.zero_le k)
  have hc := C.sites _ hi0
  have hc' := C'.sites _ hi0
  refine ⟨fun h => ?_, isRegularField_transport hL hm hN C C' hik hΩ hU⟩
  have hU' : transportGaugeField σ U ∈ gaugeFieldsInside K (Ω' 0) := by
    rw [hΩ 0 (Nat.zero_le k)]
    exact transportGaugeField_mem_gaugeFieldsInside hc hc' hU
  have := isRegularField_transport (σ := σ.symm) hL hm hN C' C hik (Ω := Ω') (Ω' := Ω)
    (fun q hq => by rw [hΩ q hq, Equiv.symm_image_image]) hU' h
  rwa [transportGaugeField_symm_transportGaugeField hc hc'] at this
end Regular
section Orbits
variable {K : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem mem_image_iff_symm_mem {x : FourTorus L m} {A : Set (FourTorus L m)} :
    x ∈ σ '' A ↔ σ.symm x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [Equiv.symm_apply_apply]
  · exact fun h => ⟨_, h, σ.apply_symm_apply x⟩
theorem isEndpointOf_bondSetImage_iff (C : Transports i σ)
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (hlev : ∀ q ∈ B, i ≤ levelDepth K q.1) (x : FourTorus L m) :
    IsEndpointOf (bondSetImage σ B) x ↔ IsEndpointOf B (σ.symm x) := by
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, h⟩
    have hc := C.sites _ (hlev q hq)
    rcases h with h | h
    · have h' : σ q.2.source = x := (coe_source_bondImage hc q.2).symm.trans h
      exact ⟨q, hq, Or.inl (by rw [← h', Equiv.symm_apply_apply])⟩
    · have h' : σ q.2.target = x := (coe_target_bondImage hc q.2).symm.trans h
      exact ⟨q, hq, Or.inr (by rw [← h', Equiv.symm_apply_apply])⟩
  · rintro ⟨q, hq, h⟩
    have hc := C.sites _ (hlev q hq)
    refine ⟨⟨q.1, bondImage σ q.2⟩, ⟨q, hq, rfl⟩, ?_⟩
    rcases h with h | h
    · left
      show ((bondImage σ q.2).source : FourTorus L m) = x
      rw [coe_source_bondImage hc, h, Equiv.apply_symm_apply]
    · right
      show ((bondImage σ q.2).target : FourTorus L m) = x
      rw [coe_target_bondImage hc, h, Equiv.apply_symm_apply]
theorem transportSiteFunction_mem_endpointFixingGaugeGroup
    (hc' : PreservesCells σ.symm (levelDepth K 0))
    {Ω Ω' : ℕ → Set (FourTorus L m)} {B B' : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (h0 : Ω' 0 = σ '' Ω 0) (hn : ∀ x, IsEndpointOf B' x → IsEndpointOf B (σ.symm x))
    {u : SiteAtLevel L m K 0 → ComplexMatrix2} (hu : u ∈ endpointFixingGaugeGroup Ω B) :
    transportSiteFunction σ u ∈ endpointFixingGaugeGroup Ω' B' := by
  have hcoe : ∀ x : SiteAtLevel L m K 0,
      ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) = σ.symm x := fun x => hc'.1 x
  refine ⟨fun x hx => hu.1 _ ?_, fun x hx => hu.2.1 _ ?_, fun x hx => hu.2.2 _ ?_⟩
  · show ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) ∈ Ω 0
    rw [hcoe]
    have hx' : (x : FourTorus L m) ∈ Ω' 0 := hx
    rw [h0] at hx'
    exact mem_image_iff_symm_mem.1 hx'
  · intro h
    have h' : ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) ∈ Ω 0 := h
    rw [hcoe] at h'
    refine hx ?_
    show (x : FourTorus L m) ∈ Ω' 0
    rw [h0]
    exact mem_image_iff_symm_mem.2 h'
  · rw [hcoe]
    exact hn _ hx
theorem endpointFixingGaugeGroup_transport (hc : PreservesCells σ (levelDepth K 0))
    (hc' : PreservesCells σ.symm (levelDepth K 0))
    {Ω Ω' : ℕ → Set (FourTorus L m)} {B B' : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (h0 : Ω' 0 = σ '' Ω 0) (hn : ∀ x, IsEndpointOf B' x ↔ IsEndpointOf B (σ.symm x)) :
    endpointFixingGaugeGroup Ω' B' =
      transportSiteFunction σ '' endpointFixingGaugeGroup Ω B := by
  apply Subset.antisymm
  · intro u hu
    refine ⟨transportSiteFunction σ.symm u, ?_,
      transportSiteFunction_transportSiteFunction_symm hc hc' u⟩
    refine transportSiteFunction_mem_endpointFixingGaugeGroup (σ := σ.symm) hc (Ω := Ω') (Ω' := Ω)
      (B := B') (B' := B) (by rw [h0, Equiv.symm_image_image]) (fun x hx => ?_) hu
    apply (hn _).2
    simpa using hx
  · rintro _ ⟨u, hu, rfl⟩
    exact transportSiteFunction_mem_endpointFixingGaugeGroup hc' h0 (fun x => (hn x).1) hu
theorem transportGaugeField_gaugeTransform (hc' : PreservesCells σ.symm j)
    (u : Site L m j → ComplexMatrix2) (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ (gaugeTransform u U) =
      gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) := by
  funext b
  show u (bondImage σ.symm b).source * U (bondImage σ.symm b) * (u (bondImage σ.symm b).target)⁻¹ =
    u (sitePreimage σ b.source) * U (bondImage σ.symm b) * (u (sitePreimage σ b.target))⁻¹
  rw [(hc'.2.2.2.1 b).1, (hc'.2.2.2.1 b).2]
  rfl
theorem endpointFixingOrbit_transport (hc : PreservesCells σ (levelDepth K 0))
    (hc' : PreservesCells σ.symm (levelDepth K 0))
    {Ω Ω' : ℕ → Set (FourTorus L m)} {B B' : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (h0 : Ω' 0 = σ '' Ω 0)
    (hres : endpointFixingGaugeGroup Ω' B' =
      transportSiteFunction σ '' endpointFixingGaugeGroup Ω B)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    endpointFixingOrbit Ω' B' (transportGaugeField σ U) =
      transportGaugeField σ '' endpointFixingOrbit Ω B U := by
  have hinner : (bondsInside (Ω' 0) : Set (BondAtLevel L m K 0)) =
      bondImage σ '' bondsInside (Ω 0) := by
    rw [h0]
    exact (hc.2.2.2.2.2.2 _).2.2
  have key : ∀ u : SiteAtLevel L m K 0 → ComplexMatrix2,
      extendByOne (bondsInside (Ω' 0))
          (gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U)) =
        transportGaugeField σ (extendByOne (bondsInside (Ω 0)) (gaugeTransform u U)) := by
    intro u
    rw [hinner, ← _root_.YangMills.Construction.PeriodicLattice.MinimalOrbitsUnderIsometries.transportGaugeField_gaugeTransform hc', extendByOne_transport hc hc']
  ext W
  constructor
  · rintro ⟨u', hu', rfl⟩
    rw [hres] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    exact ⟨_, ⟨u, hu, rfl⟩, (key u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, hres ▸ mem_image_of_mem _ hu, (key u).symm⟩
theorem endpointFixingOrbit_eq_of_mem {Ω : ℕ → Set (FourTorus L m)}
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (U W : BondAtLevel L m K 0 → ComplexMatrix2) (hW : W ∈ endpointFixingOrbit Ω B U) :
    endpointFixingOrbit Ω B W = endpointFixingOrbit Ω B U := by
  classical
  obtain ⟨u, hu, rfl⟩ := hW
  ext Y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun x => v x * u x, ⟨fun x hx => mul_mem (hv.1 x hx) (hu.1 x hx),
      fun x hx => by simp [hv.2.1 x hx, hu.2.1 x hx],
      fun x hx => by simp [hv.2.2 x hx, hu.2.2 x hx]⟩, ?_⟩
    funext b
    by_cases hb : b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
    · simp only [extendByOne, if_pos hb, gaugeTransform, Matrix.mul_inv_rev, mul_assoc]
    · simp only [extendByOne, if_neg hb]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun x => w x * (u x)⁻¹,
      ⟨fun x hx => mul_mem (hw.1 x hx) (inv_mem_compact (hu.1 x hx)),
      fun x hx => by simp [hw.2.1 x hx, hu.2.1 x hx],
      fun x hx => by simp [hw.2.2 x hx, hu.2.2 x hx]⟩, ?_⟩
    funext b
    by_cases hb : b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
    · have ht : u b.source ∈ compactGaugeGroup := hu.1 _ hb.1
      have hh : u b.target ∈ compactGaugeGroup := hu.1 _ hb.2
      simp only [extendByOne, if_pos hb, gaugeTransform, Matrix.mul_inv_rev,
        inv_inv_of_mem_compact hh]
      calc w b.source * U b * (w b.target)⁻¹
          = w b.source * (((u b.source)⁻¹ * u b.source) * U b * ((u b.target)⁻¹ * u b.target)) *
              (w b.target)⁻¹ := by
            rw [inv_mul_of_mem_compact ht, inv_mul_of_mem_compact hh, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    · simp only [extendByOne, if_neg hb]
theorem residualGauge_eq_endpointFixingGaugeGroup (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    residualGauge K k Ω = endpointFixingGaugeGroup Ω (determiningBondSet K k Ω) := by
  ext u
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    by_cases hxs : x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0))
    · exact h3 x ⟨hxs, hx⟩
    · exact h2 x hxs
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => h3 x hx.2⟩
theorem residualGaugeOrbit_eq_endpointFixingOrbit (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    residualGaugeOrbit K k Ω U = endpointFixingOrbit Ω (determiningBondSet K k Ω) U := by
  unfold residualGaugeOrbit endpointFixingOrbit
  rw [residualGauge_eq_endpointFixingGaugeGroup]
theorem constrainedFields_eq_linkConstraintSet (ω : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    constrainedFields ω K k Ω V = linkConstraintSet ω Ω (determiningBondSet K k Ω) V := by
  ext U
  exact ⟨fun h => ⟨h.1, fun q hq => h.2 q.1 hq.1 q.2 hq.2⟩,
    fun h => ⟨h.1, fun q hq b hb => h.2 ⟨q, b⟩ ⟨hq, hb⟩⟩⟩
theorem regularCriticalFields_eq_regularConstrainedCriticalSet (ω ε : ℝ) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    regularCriticalFields ω ε K k Ω V =
      regularConstrainedCriticalSet ω ε K k Ω (determiningBondSet K k Ω) V := by
  unfold regularCriticalFields IsCriticalForAction regularConstrainedCriticalSet
    IsConstrainedCritical
  rw [constrainedFields_eq_linkConstraintSet]
end Orbits
section Averages
variable {K : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem blockFieldAtLevel_transport (C : Transports i σ) (C' : Transports i σ.symm) {q : ℕ}
    (hq : q ≤ K) (hi : i ≤ levelDepth K q) {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : W ∈ compactGaugeFields L m (levelDepth K 0)) (c : BondAtLevel L m K q) :
    blockFieldAtLevel (Averaging.smoothingRadius L) q (transportGaugeField σ W) (bondImage σ c) =
      blockFieldAtLevel (Averaging.smoothingRadius L) q W c := by
  rw [C.averages K q hq hi W hW]
  exact transportGaugeField_bondImage (C.sites _ hi) (C'.sites _ hi) _ c
theorem extendByOne_mem_compactGaugeFields_of_mem {ℬ : Set (Bond L m j)}
    (hℬ : IsReversalClosed ℬ) {W : Bond L m j → ComplexMatrix2}
    (hW : W ∈ compactGaugeFields L m j) : extendByOne ℬ W ∈ compactGaugeFields L m j :=
  extendByOne_mem_compactGaugeFields hℬ
    ⟨fun b _ => hW.1 b trivial, fun b _ => hW.2 b trivial⟩
theorem averagingOnDeterminingSet_transport (C : Transports i σ) (C' : Transports i σ.symm)
    {q : ℕ} (hq : q ≤ K)
    (hi : i ≤ levelDepth K q) (hi0 : i ≤ levelDepth K 0) (X : Set (FourTorus L m))
    {W : BondAtLevel L m K 0 → ComplexMatrix2} (hW : W ∈ compactGaugeFields L m (levelDepth K 0))
    (c : BondAtLevel L m K q) :
    averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X) (transportGaugeField σ W) q
        (bondImage σ c) =
      averagingOnDeterminingSet (Averaging.smoothingRadius L) K X W q c := by
  have hc := C.sites _ hi0
  have hc' := C'.sites _ hi0
  unfold averagingOnDeterminingSet
  rw [(hc.2.2.2.2.2.2 X).2.2, extendByOne_transport hc hc']
  exact blockFieldAtLevel_transport C C' hq hi
    (extendByOne_mem_compactGaugeFields_of_mem (bondsInside_isReversalClosed X) hW) c
theorem image_bareBlockPair (C : Transports i σ) {q : ℕ} (hi : i ≤ levelDepth K q)
    (c : BondAtLevel L m K q) : σ '' bareBlockPair c = bareBlockPair (bondImage σ c) := by
  have hc := C.sites _ hi
  have hb := C.blocks _ hi
  show σ '' (refinedBlock (q - 0) c.source ∪ refinedBlock (q - 0) c.target) =
    refinedBlock (q - 0) (bondImage σ c).source ∪ refinedBlock (q - 0) (bondImage σ c).target
  rw [image_union, hb, hb, (hc.2.2.2.1 c).1, (hc.2.2.2.1 c).2]
  rfl
theorem partialBareBlockField_transport (C : Transports i σ) (C' : Transports i σ.symm) {q : ℕ}
    (hq : q ≤ K) (hi : i ≤ levelDepth K q) (hi0 : i ≤ levelDepth K 0)
    {W : BondAtLevel L m K 0 → ComplexMatrix2}
    (hW : W ∈ compactGaugeFields L m (levelDepth K 0)) (c : BondAtLevel L m K q) :
    partialBareBlockField (Averaging.smoothingRadius L) (transportGaugeField σ W) (bondImage σ c) =
      partialBareBlockField (Averaging.smoothingRadius L) W c := by
  have hc := C.sites _ hi0
  have hc' := C'.sites _ hi0
  have hbonds : bareBondsInBlockPair (bondImage σ c) =
      bondImage σ '' bareBondsInBlockPair c := by
    rw [bareBondsInBlockPair, bareBondsInBlockPair, bondsAmong_sitesIn, bondsAmong_sitesIn,
      ← image_bareBlockPair C hi]
    exact (hc.2.2.2.2.2.2 _).2.2
  unfold partialBareBlockField bareBlockPairExtension
  rw [hbonds, extendByOne_transport hc hc']
  exact blockFieldAtLevel_transport C C' hq hi
    (extendByOne_mem_compactGaugeFields_of_mem (bondsAmong_isReversalClosed _) hW) c
end Averages
section Forms
variable {K k : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
structure IsometricChains (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Ω Ω' : ℕ → Set (FourTorus L m)) : Prop where
  one_lt : 1 < L
  m_pos : 0 < m
  norm : ComplexMatrix2.OperatorNormUnderConjugation
  carried : Transports i σ
  carried' : Transports i σ.symm
  level : k ≤ K
  index : i ≤ levelDepth K k
  image : ∀ q ≤ k, Ω' q = σ '' Ω q
  region : ∃ a : ℤ, i ≤ a ∧ IsPartitionRegion a (Ω 0)
variable {Ω Ω' : ℕ → Set (FourTorus L m)}
theorem IsometricChains.index_le (S : IsometricChains i σ K k Ω Ω') {q : ℕ} (hq : q ≤ k) :
    i ≤ levelDepth K q :=
  S.index.trans (by simp only [levelDepth]; omega)
theorem IsometricChains.index_zero (S : IsometricChains i σ K k Ω Ω') : i ≤ levelDepth K 0 :=
  S.index_le (Nat.zero_le k)
theorem IsometricChains.image_zero (S : IsometricChains i σ K k Ω Ω') : Ω' 0 = σ '' Ω 0 :=
  S.image 0 (Nat.zero_le k)
theorem IsometricChains.symm (S : IsometricChains i σ K k Ω Ω') :
    IsometricChains i σ.symm K k Ω' Ω := by
  refine ⟨S.one_lt, S.m_pos, S.norm, S.carried', S.carried, S.level, S.index,
    fun q hq => by rw [S.image q hq, Equiv.symm_image_image], ?_⟩
  obtain ⟨a, ha, hr⟩ := S.region
  refine ⟨a, ha, ?_⟩
  rw [S.image_zero]
  exact (S.carried.regions a ha _).2 hr
theorem IsometricChains.objects (S : IsometricChains i σ K k Ω Ω') :
    determiningBondSet K k Ω' = bondSetImage σ (determiningBondSet K k Ω) ∧
    activeBondSet K k Ω' = bondSetImage σ (activeBondSet K k Ω) ∧
    ∀ q ≤ k, activeBondsAt K k Ω' q = bondImage σ '' activeBondsAt K k Ω q := by
  obtain ⟨h1, -, -, -, -, -, -, h2, h3, -⟩ :=
    S.carried.objects K k Ω Ω' (fun q hq => S.index_le hq) S.image
  exact ⟨h1, h2, h3⟩
theorem IsometricChains.linkConstraintPair (S : IsometricChains i σ K k Ω Ω')
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (hlev : ∀ q ∈ B, q.1 ≤ k) {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ B, V' q.1 (bondImage σ q.2) = V q.1 q.2) :
    TransportedConstraints σ (Ω 0) (Ω' 0)
      (linkConstraintSet (Averaging.smoothingRadius L) Ω B V)
      (linkConstraintSet (Averaging.smoothingRadius L) Ω' (bondSetImage σ B) V') := by
  have hi0 := S.index_zero
  have hc := S.carried.sites _ hi0
  have hc' := S.carried'.sites _ hi0
  have h0 := S.image_zero
  refine ⟨?_, ?_, transportGaugeField_symm_transportGaugeField hc hc',
    transportGaugeField_transportGaugeField_symm hc hc', ?_⟩
  · intro U hU
    refine ⟨by rw [h0]; exact transportGaugeField_mem_gaugeFieldsInside hc hc' hU.1, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hqk := hlev q hq
    show averagingOnDeterminingSet (Averaging.smoothingRadius L) K (Ω' 0)
      (transportGaugeField σ U) q.1 (bondImage σ q.2) = V' q.1 (bondImage σ q.2)
    rw [h0, averagingOnDeterminingSet_transport S.carried S.carried' (hqk.trans S.level)
      (S.index_le hqk) hi0 _ (mem_compactGaugeFields_of_mem_gaugeFieldsInside hU.1), hV q hq]
    exact hU.2 q hq
  · intro W hW
    have hT : transportGaugeField σ.symm W ∈ gaugeFieldsInside K (Ω 0) := by
      have := transportGaugeField_mem_gaugeFieldsInside (σ := σ.symm) hc' hc hW.1
      rwa [h0, Equiv.symm_image_image] at this
    refine ⟨hT, fun q hq => ?_⟩
    have hqk := hlev q hq
    have h1 := hW.2 ⟨q.1, bondImage σ q.2⟩ ⟨q, hq, rfl⟩
    have h2 := averagingOnDeterminingSet_transport S.carried S.carried' (hqk.trans S.level)
      (S.index_le hqk) hi0 (Ω 0) (mem_compactGaugeFields_of_mem_gaugeFieldsInside hT) q.2
    rw [transportGaugeField_transportGaugeField_symm hc hc', ← h0] at h2
    rw [← h2]
    exact h1.trans (hV q hq)
  · intro U hU
    obtain ⟨a, ha, hr⟩ := S.region
    rw [h0]
    exact S.carried.action K a _ U hi0 ha hr hU.1.1
theorem IsometricChains.linkConstraint_transport (S : IsometricChains i σ K k Ω Ω')
    {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (hlev : ∀ q ∈ B, q.1 ≤ k) {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ B, V' q.1 (bondImage σ q.2) = V q.1 q.2) (ε : ℝ) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω' (bondSetImage σ B) V' =
        transportGaugeField σ ''
          regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V ∧
      (HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω' (bondSetImage σ B) V' ↔
        HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω B V) ∧
      (HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω B V →
        ∀ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V,
        ∀ U' ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
            (bondSetImage σ B) V',
          endpointFixingOrbit Ω' (bondSetImage σ B) U' =
            transportGaugeField σ '' endpointFixingOrbit Ω B U) := by
  have hi0 := S.index_zero
  have hc := S.carried.sites _ hi0
  have hc' := S.carried'.sites _ hi0
  have h0 := S.image_zero
  have hR : regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
        (bondSetImage σ B) V' =
      transportGaugeField σ ''
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V :=
    (S.linkConstraintPair hlev hV).criticalRegular_eq_image (Reg := IsRegularField ε K k Ω)
      (Reg' := IsRegularField ε K k Ω')
      (fun U hU => isRegularField_transport_iff S.one_lt S.m_pos S.norm S.carried S.carried'
        (fun q hq => S.index_le hq) S.image hU.1)
  have hres := endpointFixingGaugeGroup_transport (Ω := Ω) (Ω' := Ω') (B := B)
    (B' := bondSetImage σ B) hc hc' h0
    (isEndpointOf_bondSetImage_iff S.carried fun q hq => S.index_le (hlev q hq))
  have hO := singleOrbit_transport (O := endpointFixingOrbit Ω B)
    (O' := endpointFixingOrbit Ω' (bondSetImage σ B))
    (transportGaugeField_injective hc hc') hR
    (fun U _ => endpointFixingOrbit_transport hc hc' h0 hres U) endpointFixingOrbit_eq_of_mem
  exact ⟨hR, hO.1, hO.2⟩
theorem IsometricChains.isCompleteSequence (S : IsometricChains i σ K k Ω Ω')
    (h : IsCompleteSequence K k Ω) : IsCompleteSequence K k Ω' := by
  intro j hj c hc
  rw [S.objects.2.2 j hj] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [← image_bareBlockPair S.carried (S.index_le hj), S.image_zero]
  exact image_mono (h j hj c₀ hc₀)
theorem IsometricChains.activeConstraintPair (S : IsometricChains i σ K k Ω Ω')
    {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ activeBondSet K k Ω, V' q.1 (bondImage σ q.2) = V q.1 q.2) :
    TransportedConstraints σ (Ω 0) (Ω' 0) (activeConstraintSet K k Ω V)
      (activeConstraintSet K k Ω' V') := by
  have hi0 := S.index_zero
  have hc := S.carried.sites _ hi0
  have hc' := S.carried'.sites _ hi0
  have h0 := S.image_zero
  have hlev : ∀ q ∈ activeBondSet K k Ω, q.1 ≤ k := fun q hq => hq.1.1
  refine ⟨?_, ?_, transportGaugeField_symm_transportGaugeField hc hc',
    transportGaugeField_transportGaugeField_symm hc hc', ?_⟩
  · rintro U ⟨hw, hin, hU⟩
    refine ⟨S.isCompleteSequence hw,
      by rw [h0]; exact transportGaugeField_mem_gaugeFieldsInside hc hc' hin, fun q' hq' => ?_⟩
    rw [S.objects.2.1] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    have hqk := hlev q hq
    exact (partialBareBlockField_transport S.carried S.carried' (hqk.trans S.level)
      (S.index_le hqk) hi0 (mem_compactGaugeFields_of_mem_gaugeFieldsInside hin) q.2).trans
      ((hU q hq).trans (hV q hq).symm)
  · rintro W ⟨hw, hin, hW⟩
    have hT : transportGaugeField σ.symm W ∈ gaugeFieldsInside K (Ω 0) := by
      have := transportGaugeField_mem_gaugeFieldsInside (σ := σ.symm) hc' hc hin
      rwa [h0, Equiv.symm_image_image] at this
    refine ⟨S.symm.isCompleteSequence hw, hT, fun q hq => ?_⟩
    have hqk := hlev q hq
    have h1 := hW ⟨q.1, bondImage σ q.2⟩ (by rw [S.objects.2.1]; exact ⟨q, hq, rfl⟩)
    have h2 := partialBareBlockField_transport S.carried S.carried' (hqk.trans S.level)
      (S.index_le hqk) hi0 (mem_compactGaugeFields_of_mem_gaugeFieldsInside hT) q.2
    rw [transportGaugeField_transportGaugeField_symm hc hc'] at h2
    exact h2.symm.trans (h1.trans (hV q hq))
  · rintro U ⟨-, hin, -⟩
    obtain ⟨a, ha, hr⟩ := S.region
    rw [h0]
    exact S.carried.action K a _ U hi0 ha hr hin.1
theorem IsometricChains.active_transport (S : IsometricChains i σ K k Ω Ω')
    {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ activeBondSet K k Ω, V' q.1 (bondImage σ q.2) = V q.1 q.2) (ε : ℝ) :
    (IsCompleteSequence K k Ω' ↔ IsCompleteSequence K k Ω) ∧
      activeConstraintSet K k Ω' V' = transportGaugeField σ '' activeConstraintSet K k Ω V ∧
      endpointFixingGaugeGroup Ω' (activeBondSet K k Ω') =
        transportSiteFunction σ '' endpointFixingGaugeGroup Ω (activeBondSet K k Ω) ∧
      activeRegularCriticalSet ε K k Ω' V' =
        transportGaugeField σ '' activeRegularCriticalSet ε K k Ω V ∧
      (∀ U, IsActiveCritical K k Ω' V' (transportGaugeField σ U) ↔
        IsActiveCritical K k Ω V U) ∧
      (HasMinimalOrbit ε K k Ω' V' ↔ HasMinimalOrbit ε K k Ω V) ∧
      (HasMinimalOrbit ε K k Ω V →
        ∀ U ∈ activeRegularCriticalSet ε K k Ω V,
        ∀ U' ∈ activeRegularCriticalSet ε K k Ω' V',
          endpointFixingOrbit Ω' (activeBondSet K k Ω') U' =
            transportGaugeField σ '' endpointFixingOrbit Ω (activeBondSet K k Ω) U) := by
  have hi0 := S.index_zero
  have hc := S.carried.sites _ hi0
  have hc' := S.carried'.sites _ hi0
  have h0 := S.image_zero
  have hP := S.activeConstraintPair hV
  have hC : activeConstraintSet K k Ω' V' =
      transportGaugeField σ '' activeConstraintSet K k Ω V := by
    apply Subset.antisymm
    · exact fun W hW => ⟨_, hP.backward W hW, hP.right W⟩
    · rintro _ ⟨U, hU, rfl⟩
      exact hP.forward U hU
  have hR : activeRegularCriticalSet ε K k Ω' V' =
      transportGaugeField σ '' activeRegularCriticalSet ε K k Ω V :=
    hP.criticalRegular_eq_image (Reg := IsRegularField ε K k Ω)
      (Reg' := IsRegularField ε K k Ω')
      (fun U hU => isRegularField_transport_iff S.one_lt S.m_pos S.norm S.carried S.carried'
        (fun q hq => S.index_le hq) S.image hU.2.1)
  have hset := S.objects.2.1
  have hres : endpointFixingGaugeGroup Ω' (activeBondSet K k Ω') =
      transportSiteFunction σ '' endpointFixingGaugeGroup Ω (activeBondSet K k Ω) := by
    rw [hset]
    exact endpointFixingGaugeGroup_transport hc hc' h0
      (isEndpointOf_bondSetImage_iff S.carried fun q hq => S.index_le hq.1.1)
  have hO := singleOrbit_transport (O := endpointFixingOrbit Ω (activeBondSet K k Ω))
    (O' := endpointFixingOrbit Ω' (activeBondSet K k Ω')) (transportGaugeField_injective hc hc') hR
    (fun U _ => endpointFixingOrbit_transport hc hc' h0 hres U) endpointFixingOrbit_eq_of_mem
  have hW : IsCompleteSequence K k Ω' ↔ IsCompleteSequence K k Ω :=
    ⟨S.symm.isCompleteSequence, S.isCompleteSequence⟩
  refine ⟨hW, hC, hres, hR, hP.isCriticalWithin_iff, ?_, fun h => hO.2 h.2⟩
  exact and_congr hW hO.1
theorem IsometricChains.activeMinimalOrbitTransports (S : IsometricChains i σ K k Ω Ω')
    {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ activeBondSet K k Ω, V' q.1 (bondImage σ q.2) = V q.1 q.2) {ε : ℝ}
    {U U' : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : HasMinimalOrbit ε K k Ω V → U ∈ activeRegularCriticalSet ε K k Ω V)
    (hU' : HasMinimalOrbit ε K k Ω' V' → U' ∈ activeRegularCriticalSet ε K k Ω' V') :
    ActiveMinimalOrbitTransports σ ε K k Ω Ω' V V' U U' := by
  obtain ⟨-, -, -, -, -, h1, h2⟩ := S.active_transport hV ε
  exact ⟨h1, fun h => h2 h U (hU h) U' (hU' (h1.2 h))⟩
theorem IsometricChains.criticalOrbitTransports (S : IsometricChains i σ K k Ω Ω')
    {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
    (hV : ∀ q ∈ determiningBondSet K k Ω, V' q.1 (bondImage σ q.2) = V q.1 q.2) (ε : ℝ) :
    CriticalOrbitTransports σ ε K k Ω Ω' V V'
      (minimizingField (Averaging.smoothingRadius L) ε K k Ω V)
      (minimizingField (Averaging.smoothingRadius L) ε K k Ω' V') := by
  obtain ⟨-, h1, h2⟩ := S.linkConstraint_transport (fun q hq => hq.1) hV ε
  have hdet := S.objects.1
  have hspec : ∀ {Ω₁ : ℕ → Set (FourTorus L m)}
      {V₁ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2},
      CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω₁ V₁ →
        minimizingField (Averaging.smoothingRadius L) ε K k Ω₁ V₁ ∈
          regularCriticalFields (Averaging.smoothingRadius L) ε K k Ω₁ V₁ := by
    rintro Ω₁ V₁ ⟨U₀, hU₀, -⟩
    exact Classical.epsilon_spec (p := fun U => U ∈
      regularCriticalFields (Averaging.smoothingRadius L) ε K k Ω₁ V₁) ⟨U₀, hU₀⟩
  have hconv : ∀ {Ω₁ : ℕ → Set (FourTorus L m)}
      {V₁ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2},
      CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω₁ V₁ ↔
        HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω₁
          (determiningBondSet K k Ω₁) V₁ := by
    intro Ω₁ V₁
    simp only [CriticalFieldsFormOneOrbit, HasUniqueCriticalOrbit,
      regularCriticalFields_eq_regularConstrainedCriticalSet,
      residualGaugeOrbit_eq_endpointFixingOrbit]
  have h1' : CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω' V' ↔
      CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω V := by
    rw [hconv, hconv, hdet]
    exact h1
  refine ⟨h1', fun h => ?_⟩
  rw [residualGaugeOrbit_eq_endpointFixingOrbit, residualGaugeOrbit_eq_endpointFixingOrbit, hdet]
  have a := hspec h
  have a' := hspec (h1'.2 h)
  rw [regularCriticalFields_eq_regularConstrainedCriticalSet] at a a'
  rw [hdet] at a'
  exact h2 (hconv.1 h) _ a _ a'
end Forms
section Lifts
variable {K k : ℕ} {i : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem mem_liftSupport_univ (hLift : LiftConsistentWithAverages)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) (hkK : k ≤ K)
    (b : BondAtLevel L m K 0) : b ∈ liftSupport 0 (univ : Set (BondAtLevel L m K k)) := by
  have h := ((hLift L m K hS hm hK k hkK (univ : Set (BondAtLevel L m K k)) (fun _ _ => trivial)
    (fun _ => 1) (Or.inl ⟨fun _ _ => Submonoid.one_mem _, fun _ _ => by simp⟩)).1 0
      (Nat.zero_le k)).2 b
  rcases h.1 with h | ⟨c, hc, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, trivial, hc⟩
theorem bareLift_transport (hLift : LiftConsistentWithAverages)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hL : LevelLiftEquivariant K i σ)
    (hc : PreservesCells σ (levelDepth K k))
    (hc' : PreservesCells σ.symm (levelDepth K k))
    (h1 : 1 ≤ k) (hkK : k ≤ K) (hik : i ≤ levelDepth K k)
    {V : BondAtLevel L m K k → ComplexMatrix2}
    (hV : IsGaugeField compactGaugeGroup univ V) :
    bareLift V ∈ compactGaugeFields L m (levelDepth K 0) ∧
      bareLift (transportGaugeField σ V) = transportGaugeField σ (bareLift V) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hK : 0 < K := by omega
  have hclosed : IsReversalClosed (univ : Set (BondAtLevel L m K (k' + 1))) :=
    fun _ _ => trivial
  have hW := (hLift L m K hS hm hK (k' + 1) hkK univ hclosed V (Or.inl hV)).2.2.2.2.2.1 rfl hV
  refine ⟨hW.1, ?_⟩
  have hdata : IsLevelLiftData (K := K) (k := k' + 1) compactGaugeGroup 0 ⟨univ, V⟩ :=
    ⟨Nat.zero_le _, hkK, hclosed, hV⟩
  obtain ⟨-, ⟨-, hag⟩, -⟩ := (hL (k' + 1) 0 hik ⟨univ, V⟩).1 compactGaugeGroup (Or.inl rfl) hdata
  funext b
  refine hag b ?_
  have himg : (transportPartialGaugeField σ (⟨univ, V⟩ : PartialGaugeField L m
      (levelDepth K (k' + 1)))).support = univ :=
    eq_univ_of_forall fun c => ⟨bondImage σ.symm c, trivial, bondImage_bondImage_symm hc hc' c⟩
  show b ∈ liftSupport 0 (transportPartialGaugeField σ (⟨univ, V⟩ : PartialGaugeField L m
      (levelDepth K (k' + 1)))).support
  rw [himg]
  exact mem_liftSupport_univ hLift hS hm hK hkK b
end Lifts
theorem isPartitionRegion_univ (hL : 0 < L) (i : ℤ) :
    IsPartitionRegion i (univ : Set (FourTorus L m)) :=
  ⟨standardCubePartition L m i, Subset.rfl,
    (SeparatedSequence.sUnion_standardCubePartition hL i).symm⟩
theorem equiv_image_univ (σ : FourTorus L m ≃ FourTorus L m) : σ '' univ = univ :=
  by rw [image_univ]; exact σ.surjective.range_eq
theorem shrinkingTower_isPartitionRegion {K n : ℕ} {X : Set (FourTorus L m)} (p : ℕ) :
    IsPartitionRegion (scaledCubeIndex K (p + 1) n) (shrinkingTower K n 0 X (p + 1)) := by
  refine ⟨_, ?_, rfl⟩
  rintro Q ⟨⟨-, hQ⟩, -⟩
  simpa using hQ
theorem transports_of_latticeIsometry (hSites : IsometriesPreserveCells)
    (hObj : IsometryPreservesChainObjects)
    (hBlocks : IsometryInvariance.InvariantUnderIsometries)
    (hHol : IsometryCovariance.Statement)
    (hAvg : AveragingMapsEquivariant)
    (hGroups : LatticeIsometryGroupActionStatement)
    (hTw : TwistedTransportIsometryInvariance)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) : Transports i σ := by
  obtain ⟨e, he⟩ := hHol
  refine ⟨fun j hij => hSites L m i j σ hS hm hi hσ hij, hObj L m i σ hS hm hi hσ,
    fun j hij => ((hBlocks L m hS hm i hi σ hσ).1 j hij).1, fun j hij U hU p => ?_,
    fun K a X U hi0 ha hr hU => (he L m hS hm i hi σ hσ).2 K a X U hi0 ha hr hU,
    fun K => (hAvg L m hS hm i hi σ hσ K).2.1,
    fun j hij => ((hGroups L m i hS hm hi).2.2.2.2 σ hσ j hij).2.1,
    fun j hj hij ℬ hℬ V₀ hV₀ => ((hTw L m i σ hS hm hi hσ).2.2.1 j hj hij ℬ hℬ).2.2.1 V₀ hV₀⟩
  exact ((((he L m hS hm i hi σ hσ).1 j hij).1 univ U (fun _ _ => trivial) hU).2 p
    fun _ _ => trivial).2.2.2
theorem symm_mem_latticeIsometries (hGroups : LatticeIsometryGroupActionStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.symm_mem_latticeIsometries <;> assumption
theorem isometryCovarianceOfMinimalOrbits (hSites : IsometriesPreserveCells)
    (hObj : IsometryPreservesChainObjects)
    (hBlocks : IsometryInvariance.InvariantUnderIsometries)
    (hHol : IsometryCovariance.Statement)
    (hAvg : AveragingMapsEquivariant)
    (hGroups : LatticeIsometryGroupActionStatement)
    (hTw : TwistedTransportIsometryInvariance)
    (hTowers : IsometriesPreserveTowersAndStepCubes)
    (hLift : LiftConsistentWithAverages)
    (hNorm : ComplexMatrix2.OperatorNormUnderConjugation)
    (hGlued : GluedDataEquivariant) :
    IsometryCovarianceOfMinimalOrbits := by
  intro L m K i σ ε hS hm hi hσ hε
  have hL1 : 1 < L := by
    have := hS.2
    omega
  have hL0 : 0 < L := by omega
  have hσ' := symm_mem_latticeIsometries hGroups hS hm hi hσ
  have C := transports_of_latticeIsometry hSites hObj hBlocks hHol hAvg hGroups hTw hS hm hi hσ
  have C' := transports_of_latticeIsometry hSites hObj hBlocks hHol hAvg hGroups hTw hS hm hi hσ'
  have hTow := (hTowers.1 L m i σ hS hm hi hσ)
  have hAvgσ := hAvg L m hS hm i hi σ hσ K
  have hξ : ∀ k : ℕ, 0 < finestMeshInLevelUnits L k := fun k =>
    zpow_pos (by exact_mod_cast hL0) _
  have mk : ∀ (k : ℕ) (Ω Ω' : ℕ → Set (FourTorus L m)), k ≤ K → i ≤ levelDepth K k →
      (∀ q ≤ k, Ω' q = σ '' Ω q) → (∃ a : ℤ, i ≤ a ∧ IsPartitionRegion a (Ω 0)) →
      IsometricChains i σ K k Ω Ω' :=
    fun k Ω Ω' h1 h2 h3 h4 => ⟨hL1, hm, hNorm, C, C', h1, h2, h3, h4⟩
  have hdatum : ∀ (q : ℕ), i ≤ levelDepth K q →
      ∀ (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
      (b : BondAtLevel L m K q), datumImage σ V q (bondImage σ b) = V q b :=
    fun q h V b => transportGaugeField_bondImage (C.sites _ h) (C'.sites _ h) _ b
  have hminspec : ∀ (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
      (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2),
      HasMinimalOrbit ε K k Ω V →
        activeMinimalField ε K k Ω V ∈ activeRegularCriticalSet ε K k Ω V := by
    intro k Ω V h
    obtain ⟨-, U₀, hU₀, -⟩ := id h
    exact (Classical.epsilon_spec (p := IsActiveMinimalField ε K k Ω V) ⟨U₀, h, hU₀⟩).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k Ω V hD _
    obtain ⟨a, ha, ha', -⟩ := hD.2.2 k le_rfl
    obtain ⟨a₀, ha₀, -, hr₀⟩ := hD.2.2 0 (Nat.zero_le k)
    have S := mk k Ω (imageChain σ Ω) hD.1 (ha.trans ha') (fun _ _ => rfl) ⟨a₀, ha₀, hr₀⟩
    have hVd : ∀ q ∈ activeBondSet K k Ω, datumImage σ V q.1 (bondImage σ q.2) = V q.1 q.2 :=
      fun q hq => hdatum _ (S.index_le hq.1.1) V q.2
    obtain ⟨hW, hCs, hres, hR, hcrit, -, -⟩ := S.active_transport hVd ε
    have hj : -(m : ℤ) < levelDepth K 0 := by simp only [levelDepth]; omega
    exact ⟨⟨hW, hCs, hres, hR⟩, fun U hU => ⟨isRegularField_transport_iff hL1 hm hNorm C C'
      (fun q hq => S.index_le hq) S.image hU, hcrit U, fun b _ => yangMillsCurrent_transport C C' hj
      S.index_zero (mem_compactGaugeFields_of_mem_gaugeFieldsInside hU) (hξ k) b⟩,
      S.activeMinimalOrbitTransports hVd (hminspec _ _ _) (hminspec _ _ _)⟩
  · intro k V hk hik _
    have S := mk k (fun _ => univ) (fun _ => univ) hk hik
      (fun _ _ => (equiv_image_univ σ).symm) ⟨i, le_rfl, isPartitionRegion_univ hL0 i⟩
    refine S.criticalOrbitTransports (fun q hq => ?_) ε
    obtain ⟨j, b⟩ := q
    have hjk : j ≤ k := hq.1
    show datumOnLevel K k (transportGaugeField σ V) j (bondImage σ b) =
      datumOnLevel K k V j b
    by_cases h : j = k
    · subst h
      have e : ∀ W : BondAtLevel L m K j → ComplexMatrix2, datumOnLevel K j W j = W :=
        fun W => by simp [datumOnLevel]
      rw [e, e]
      exact transportGaugeField_bondImage (C.sites _ hik) (C'.sites _ hik) V b
    · have e : ∀ W : BondAtLevel L m K k → ComplexMatrix2, datumOnLevel K k W j = fun _ => 1 :=
        fun W => dif_neg h
      rw [e, e]
  · intro k m' c S₀ S' V hIm hD
    obtain ⟨a, ha, ha', -⟩ := hD.2.2 k le_rfl
    obtain ⟨a₀, ha₀, -, hr₀⟩ := hD.2.2 0 (Nat.zero_le k)
    have hdom : ∀ q, domainChain S'.domainSeq q = σ '' domainChain S₀.domainSeq q := by
      intro q
      cases q with
      | zero => exact (equiv_image_univ σ).symm
      | succ p =>
        show S'.domainSeq (p + 1) = σ '' S₀.domainSeq (p + 1)
        unfold ScaleLabel.domainSeq
        by_cases h : p + 1 ∈ Set.Icc 1 k
        · rw [dif_pos h, dif_pos h, hIm ⟨p + 1, h⟩]
          rfl
        · rw [dif_neg h, dif_neg h]
          exact (equiv_image_univ σ).symm
    have S := mk k _ _ hD.1 (ha.trans ha') (fun q _ => hdom q) ⟨a₀, ha₀, hr₀⟩
    exact ⟨fun _ => S.criticalOrbitTransports (fun q hq => hdatum _ (S.index_le hq.1) V q.2) ε,
      fun _ => S.activeMinimalOrbitTransports (fun q hq => hdatum _ (S.index_le hq.1.1) V q.2)
        (hminspec _ _ _) (hminspec _ _ _)⟩
  · intro k n X V hT hV
    obtain ⟨hin, c, hc1, hc2, hcr⟩ := hT
    have hik : i ≤ levelDepth K k := hin.trans (by simp only [scaledCubeIndex]; omega)
    have hsame : IsLevelRegionFrom K n 0 i X := ⟨c, hc1, hc2, hcr⟩
    have hTower : k ≤ K → ∀ p ≤ k,
        shrinkingTower K n 0 (σ '' X) p = σ '' shrinkingTower K n 0 X p :=
      fun hkK => (hTow.1 K k n 0 0 0 k X hkK (by omega) (by omega) hsame).2.2
        (by simpa using hin)
    have mkS : k ≤ K →
        IsometricChains i σ K k (shrinkingTower K n 0 X) (shrinkingTower K n 0 (σ '' X)) :=
      fun hkK => mk k _ _ hkK hik (hTower hkK) ⟨c, hc1, hcr⟩
    have hlift : 1 ≤ k → k ≤ K → _ := fun h1 hkK =>
      bareLift_transport hLift hS hm hAvgσ.2.2.2.2.2.2.1 (C.sites _ hik) (C'.sites _ hik) h1 hkK
        hik hV
    constructor
    · rintro ⟨h1, hkK, -, -⟩
      have S := mkS hkK
      obtain ⟨hreal, hcomm⟩ := hlift h1 hkK
      refine S.criticalOrbitTransports (fun q hq => ?_) ε
      show averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
          (bareLift (transportGaugeField σ V)) q.1 (bondImage σ q.2) =
        averagingOnDeterminingSet (Averaging.smoothingRadius L) K X (bareLift V) q.1 q.2
      rw [hcomm]
      exact averagingOnDeterminingSet_transport C C' (hq.1.trans hkK) (S.index_le hq.1)
        S.index_zero X hreal q.2
    · intro hSet
      obtain ⟨⟨h1, hkK, -, -⟩, hM, hF⟩ := id hSet
      have S := mkS hkK
      obtain ⟨hreal, hcomm⟩ := hlift h1 hkK
      have hK : 0 < K := by omega
      obtain ⟨c', hc'1, hc'2, hc'r⟩ :=
        (hTow.1 K k n 0 0 0 k X hkK (by omega) (by omega) hsame).1
      have hdet : IsDeterminingChain K k (shrinkingTower K n 0 (σ '' X)) := by
        refine ⟨fun q hq => ?_, fun q hq => ?_⟩
        · rw [hTower hkK _ hq, hTower hkK _ hq.le]
          exact image_mono (hF.1.2.1 q hq)
        · cases q with
          | zero =>
            exact ⟨c', hi.trans hc'1, hc'2.trans (by simp only [scaledCubeIndex]; omega), hc'r⟩
          | succ p =>
            refine ⟨scaledCubeIndex K (p + 1) n, ?_, ?_, shrinkingTower_isPartitionRegion p⟩
            · exact (hi.trans hin).trans (by simp only [scaledCubeIndex, levelDepth]; omega)
            · simp only [scaledCubeIndex]; omega
      have hSet' : IsLocalizedBackgroundHyp K k n (σ '' X) univ
          (transportGaugeField σ V) :=
        ⟨⟨h1, hkK, fun _ _ => trivial,
            transportGaugeField_mem_compactGaugeFields (C'.sites _ hik) hV⟩,
          ⟨h1, hkK, ⟨c', hi.trans hc'1, hc'2, hc'r⟩, hM.2.2.2⟩,
          ⟨⟨hkK, hdet⟩, S.isCompleteSequence hF.2.1,
            fun q _ b _ => mem_liftSupport_univ hLift hS hm hK hkK b⟩⟩
      refine ⟨hSet', S.activeMinimalOrbitTransports (fun q hq => ?_) (fun h => ?_) (fun h => ?_)⟩
      · show partialBareBlockField (Averaging.smoothingRadius L)
            (bareLift (transportGaugeField σ V)) (bondImage σ q.2) =
          partialBareBlockField (Averaging.smoothingRadius L) (bareLift V) q.2
        rw [hcomm]
        exact partialBareBlockField_transport C C' (hq.1.1.trans hkK) (S.index_le hq.1.1)
          S.index_zero hreal q.2
      · obtain ⟨-, U₀, hU₀, -⟩ := id h
        exact (Classical.epsilon_spec (p := IsLocalizedBackground ε K k n X univ V)
          ⟨U₀, hSet, h, hU₀⟩).2.2
      · obtain ⟨-, U₀, hU₀, -⟩ := id h
        exact (Classical.epsilon_spec (p := IsLocalizedBackground ε K k n (σ '' X) univ
          (transportGaugeField σ V)) ⟨U₀, hSet', h, hU₀⟩).2.2
  · intro k n j Ω W V hD hj hJ
    obtain ⟨hz, hdat⟩ := hGlued L m K k n j i σ Ω W V hS hm hi hσ hD hj hJ
    obtain ⟨-, hq, hset, -⟩ := hTow.2.2.2.2.1 K k n j Ω W hD hJ.2.1 hj
    obtain ⟨a, ha, ha', -⟩ := hD.2.2 k le_rfl
    have S := mk k (gluedChain K n j Ω W) (gluedChain K n j (imageChain σ Ω) (σ '' W))
      hD.1 (ha.trans ha') hq ⟨_, hj, by rw [hz]; exact hJ.2.1.2.2.1.2⟩
    obtain ⟨-, h1, h2⟩ := S.linkConstraint_transport (B := gluedActiveSet K k n j Ω W)
      (V := gluedBoundaryData K k j Ω V)
      (V' := gluedBoundaryData K k j (imageChain σ Ω) (datumImage σ V))
      (fun q hq => hq.1.1) hdat ε
    rw [← hset] at h1 h2
    have hspec : ∀ (Ω₁ : ℕ → Set (FourTorus L m)) (W₁ : Set (FourTorus L m))
        (V₁ : ∀ q : ℕ, BondAtLevel L m K q → ComplexMatrix2),
        HasGluedCriticalOrbit ε K k n j Ω₁ W₁ V₁ →
        gluedCriticalConfiguration ε K k n j Ω₁ W₁ V₁ ∈
          regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
            (gluedChain K n j Ω₁ W₁)
            (gluedActiveSet K k n j Ω₁ W₁) (gluedBoundaryData K k j Ω₁ V₁) := by
      rintro Ω₁ W₁ V₁ ⟨U₀, hU₀, -⟩
      exact Classical.epsilon_spec (p := fun U => U ∈
        regularConstrainedCriticalSet (Averaging.smoothingRadius L)
        ε K k (gluedChain K n j Ω₁ W₁) (gluedActiveSet K k n j Ω₁ W₁)
        (gluedBoundaryData K k j Ω₁ V₁)) ⟨U₀, hU₀⟩
    exact ⟨h1, fun h => h2 h _ (hspec _ _ _ h) _ (hspec _ _ _ (h1.2 h))⟩
end PeriodicLattice.MinimalOrbitsUnderIsometries
end YangMills.Construction
