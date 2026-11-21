import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
abbrev BlockFrame.ActionTerm (F : BlockFrame) : Type :=
  (F.Site 0 × Fin 4 × Fin 4) ⊕ ((j : ℕ) × (F.Site (j + 1) × Fin 4))
def actionTerms (S : Finset F.Cell) : Finset F.ActionTerm :=
  (innerPlaquettes S 0).disjSum ((Finset.range F.top).sigma fun j => innerBonds S (j + 1))
def patchActionTerms (S : Finset F.Cell) (z : F.Cell) : Finset F.ActionTerm :=
  (patchPlaquettes S z).disjSum ((Finset.range F.top).sigma fun j => patchFitBonds S z j)
def actionTermSite : F.ActionTerm → F.Site 0
  | Sum.inl p => p.1
  | Sum.inr c => baseSite c.2.1
def actionTermValue (a : ℝ) (X : F.FieldChain) (k : F.SiteGauge) : F.ActionTerm → ℝ
  | Sum.inl p => 1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re
  | Sum.inr c => a * gaugedBlockFit (X c.1) (k (c.1 + 1)) (X (c.1 + 1)) c.2
def imaginaryPart (q : ℍ[ℝ]) : imaginaryQuaternions :=
  ⟨pureComponent q, by show (pureComponent q).re = 0; simp [pureComponent]⟩
structure GaugedVariation (F : BlockFrame) where
  bondVariation : (j : ℕ) → F.Site j → Fin 4 → imaginaryQuaternions
  linkVariation : (j : ℕ) → F.Site (j + 1) → imaginaryQuaternions
open Classical in
def variedFieldChain (W : F.FieldChain) (Y : GaugedVariation F) (τ : ℝ) : F.FieldChain :=
  fun j x i => if j < F.top then expUnit (τ • Y.bondVariation j x i) * W j x i else W j x i
def variedGauge (k : F.SiteGauge) (Y : GaugedVariation F) (τ : ℝ) : F.SiteGauge
  | 0 => k 0
  | j + 1 => fun y => expUnit (τ • Y.linkVariation j y) * k (j + 1) y
def firstVariation (a : ℝ) (W : F.FieldChain) (k : F.SiteGauge) (Y : GaugedVariation F) (t : F.ActionTerm) : ℝ :=
  deriv (fun τ : ℝ => actionTermValue a (variedFieldChain W Y τ) (variedGauge k Y τ) t) 0
def relativeDefect (W : F.FieldChain) (X : F.FieldChain) (Γ : F.SiteGauge) (j : ℕ) (x : F.Site j) (i : Fin 4) :
    UnitQuaternion :=
  gaugedChainFields X Γ j x i * (W j x i)⁻¹
def gaugeVariation (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) :
    GaugedVariation F :=
  ⟨fun j x i => imaginaryPart ((relativeDefect W X Γ j x i : UnitQuaternion) : ℍ[ℝ]),
    fun j y => imaginaryPart ((gaugedLink k Γ j y * (kW (j + 1) y)⁻¹ : UnitQuaternion) : ℍ[ℝ])⟩
def relativeEnergyDensity (a : ℝ) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) :
    F.ActionTerm → ℝ
  | Sum.inl p => ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2
  | Sum.inr c => a * ‖((bondMisfit (gaugedChainFields X Γ c.1)
      (balancedLinkAgainst W kW (gaugedChainFields X Γ) c.1)
      (framedUpperField W kW X k Γ c.1) c.2 * (bondMisfit (W c.1) (kW (c.1 + 1)) (W (c.1 + 1)) c.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2
open Classical in
def cellsClearOfHighEnergy (a ε : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) : Finset F.Cell :=
  S.filter fun z => ∀ y ∈ S, ε ^ 2 < patchAction a S y X k → 40 < cellSupDist z y
open Classical in
def patchInnerBonds (S : Finset F.Cell) (z : F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4) :=
  (innerBonds S j).filter fun b =>
    baseSite b.1 ∈ patchBaseSites S z ∧ baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z
def gaugeChange (Γ Γ' : F.SiteGauge) (j : ℕ) (x : F.Site j) : UnitQuaternion := Γ j x * (Γ' j x)⁻¹
def balancedRotation (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) (j : ℕ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  balancedLinkAgainst W kW (gaugedChainFields X Γ) j y * (gaugedLink k Γ j y)⁻¹
open Classical in
def gaugeChangeAbove (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ Γ' : F.SiteGauge) (j : ℕ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  if j = F.depth then balancedRotation W kW X k Γ j y * (balancedRotation W kW X k Γ' j y)⁻¹
  else gaugeChange Γ Γ' (j + 1) y
def criticalFieldChain (S : Finset F.Cell) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (U : ChainChart F) : F.FieldChain :=
  chartChain (referenceFieldChain S V) U (rotatedField v V)
def criticalGauge (S : Finset F.Cell) (V : F.GaugeField F.top) (U : ChainChart F) : F.SiteGauge :=
  chartGauge (referenceFieldChain S V) U
def HasPinnedGaugeAt (a C Cd ε : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) : Prop :=
  IsPinnedGauge a C S z W kW X k Γ ∧ relativeEnergy a S z W kW X k Γ ≤ Cd * ε ^ 2
end BlockAverages
end YangMills.Construction
end
