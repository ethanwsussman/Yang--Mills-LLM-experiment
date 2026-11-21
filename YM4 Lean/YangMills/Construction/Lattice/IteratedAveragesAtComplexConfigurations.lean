import YangMills.Construction.Lattice.ComplexIteratesByTheBondwiseMaps
import YangMills.Construction.Lattice.ConsistencyOfLiftsAndAveragesSetting
import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexIteratedAverages
section Products
variable {ι : Type}
def pointOfIndexedFamily {n : ℕ} (e : ι ≃ Fin n) (X : Fin n → Matrices.ComplexMatrix2) :
    ι ⊕ Empty → Matrices.ComplexMatrix2 :=
  Sum.elim (X ∘ e) fun z => z.elim
def IsHolomorphicInAllNumberings (W : Set (ι ⊕ Empty → Matrices.ComplexMatrix2))
    (F : (ι ⊕ Empty → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∀ (n : ℕ) (e : ι ≃ Fin n) (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
    Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power β (pointOfIndexedFamily e ⁻¹' W)
      (F ∘ pointOfIndexedFamily e)
end Products
def signedPower (σ : ℤˣ) (Y : Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  if σ = 1 then Y else Y⁻¹
variable {L m K q : ℕ}
def fieldOfPoint (B : Set (BondAtLevel L m K q))
    (p : PositiveBondOf B ⊕ Empty → Matrices.ComplexMatrix2) :
    BondAtLevel L m K q → Matrices.ComplexMatrix2 :=
  extendFromPositive B fun b => p (.inl b)
def iteratedAverage (B : Set (BondAtLevel L m K q)) (U : BondAtLevel L m K q → Matrices.ComplexMatrix2)
    (j : ℕ) : PartialGaugeField L m (levelDepth K (q + j)) :=
  complexPartialBlockAverageIter (K := K) q ⟨B, U⟩ j
def iteratedAverageDomain (B : Set (BondAtLevel L m K q)) (j : ℕ) (c : BondAtLevel L m K (q + j)) :
    Set (BondAtLevel L m K q → Matrices.ComplexMatrix2) :=
  {U | IsComplexGaugeField B U ∧ c ∈ (iteratedAverage B U j).support}
def productDomain (B : Set (BondAtLevel L m K q)) (j : ℕ) (c : BondAtLevel L m K (q + j)) :
    Set (PositiveBondOf B ⊕ Empty → Matrices.ComplexMatrix2) :=
  {p | p ∈ Matrices.GroupLieProduct (PositiveBondOf B) Empty ∧
    fieldOfPoint B p ∈ iteratedAverageDomain B j c}
def iteratedValue (B : Set (BondAtLevel L m K q)) (j : ℕ) (c : BondAtLevel L m K (q + j))
    (p : PositiveBondOf B ⊕ Empty → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  (iteratedAverage B (fieldOfPoint B p) j).field c
def fieldComponent {B : Set (BondAtLevel L m K q)} {n : ℕ}
    (p : (PositiveBondOf B ⊕ Fin n) ⊕ Empty → Matrices.ComplexMatrix2) :
    PositiveBondOf B ⊕ Empty → Matrices.ComplexMatrix2 :=
  Sum.elim (fun b => p (.inl (.inl b))) fun z => z.elim
def powerComponent {B : Set (BondAtLevel L m K q)} {n : ℕ}
    (p : (PositiveBondOf B ⊕ Fin n) ⊕ Empty → Matrices.ComplexMatrix2) (i : Fin n) :
    Matrices.ComplexMatrix2 :=
  p (.inl (.inr i))
def productDomainTimesPower (B : Set (BondAtLevel L m K q)) (j : ℕ) (c : BondAtLevel L m K (q + j))
    (n : ℕ) : Set ((PositiveBondOf B ⊕ Fin n) ⊕ Empty → Matrices.ComplexMatrix2) :=
  {p | fieldComponent p ∈ productDomain B j c ∧ ∀ i, powerComponent p i ∈ complexGaugeGroup}
def leftMultipliedValue (B : Set (BondAtLevel L m K q)) (j : ℕ) (c : BondAtLevel L m K (q + j))
    {n : ℕ} (i : Fin n) (σ : ℤˣ) (p : (PositiveBondOf B ⊕ Fin n) ⊕ Empty → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2 :=
  signedPower σ (powerComponent p i) * iteratedValue B j c (fieldComponent p)
structure OpenDomainHolomorphicValue (B : Set (BondAtLevel L m K q))
    [Fintype (PositiveBondOf B)] (j : ℕ) (c : BondAtLevel L m K (q + j)) : Prop where
  isOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct (PositiveBondOf B) Empty) (productDomain B j c)
  value_mem : ∀ U ∈ iteratedAverageDomain B j c, (iteratedAverage B U j).field c ∈ complexGaugeGroup
  holomorphic : ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular β (productDomain B j c) (iteratedValue B j c)
  allNumberings : B.Nonempty →
    IsHolomorphicInAllNumberings (productDomain B j c) (iteratedValue B j c)
structure JointlyHolomorphicValues (B : Set (BondAtLevel L m K q)) [Fintype (PositiveBondOf B)]
    {u : ℕ} (js : Fin u → ℕ) (cs : ∀ s, BondAtLevel L m K (q + js s)) : Prop where
  isOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct (PositiveBondOf B) Empty) (⋂ s, productDomain B (js s) (cs s))
  holomorphic : ∀ (s : Fin u) (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular β (⋂ t, productDomain B (js t) (cs t))
      (iteratedValue B (js s) (cs s))
structure LeftMultipliedValueHolomorphic (B : Set (BondAtLevel L m K q))
    [Fintype (PositiveBondOf B)] (j : ℕ) (c : BondAtLevel L m K (q + j)) {n : ℕ} (i : Fin n)
    (σ : ℤˣ) : Prop where
  isOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct (PositiveBondOf B ⊕ Fin n) Empty) (productDomainTimesPower B j c n)
  holomorphic : ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular β (productDomainTimesPower B j c n)
      (leftMultipliedValue B j c i σ)
  allNumberings : IsHolomorphicInAllNumberings (productDomainTimesPower B j c n)
    (leftMultipliedValue B j c i σ)
structure AgreesWithPartialAverages (B : Set (BondAtLevel L m K q)) (j : ℕ)
    (c : BondAtLevel L m K (q + j)) : Prop where
  domain_eq : iteratedAverageDomain B j c =
    {U | IsComplexGaugeField B U ∧ ComplexPartialDefinedAt (K := K) q ⟨B, U⟩ j c}
  value_eq : ∀ U ∈ iteratedAverageDomain B j c,
    (iteratedAverage B U j).field c = complexPartialValues (K := K) q ⟨B, U⟩ j c
def ComplexIteratedAveragesHolomorphic : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ q : ℕ, q < K →
    ∀ B : Set (BondAtLevel L m K q), IsReversalClosed B →
    ∀ _ : Fintype (PositiveBondOf B),
      (∀ j : ℕ, q + j ≤ K → ∀ c : BondAtLevel L m K (q + j),
        OpenDomainHolomorphicValue B j c ∧
        (∀ n : ℕ, 1 ≤ n → ∀ (i : Fin n) (σ : ℤˣ), LeftMultipliedValueHolomorphic B j c i σ) ∧
        AgreesWithPartialAverages B j c) ∧
      ∀ u : ℕ, 1 ≤ u → ∀ (js : Fin u → ℕ) (cs : ∀ s, BondAtLevel L m K (q + js s)),
        (∀ s, q + js s ≤ K) → JointlyHolomorphicValues B js cs
end YangMills.Construction.PeriodicLattice.ComplexIteratedAverages
