import YangMills.Construction.Lattice.DifferencesBetweenAConfigurationAndTheIdentity
import YangMills.Construction.Lattice.ProductOfAFunctionAndASource
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices PeriodicLattice SeparatedSequences SeparatedRegions
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
structure IsExtensionNearFirstMember (V : Set (FourTorus L m)) (h : V → ℝ)
    (θ : FourTorus L m → ℝ) : Prop where
  isOpen : IsOpen V
  first_subset : Ω 0 ⊆ V
  eq_on : ∀ p : V, θ p = h p
def bondAxisSmul (θ : FourTorus L m → ℝ) (X : FineBond L m S × Fin 4 → ComplexMatrix2) :
    FineBond L m S × Fin 4 → ComplexMatrix2 :=
  fun i => θ (bondAxisAnchor S i) • X i
def commutatorOf {α β : Type*} [Sub β] (a : α → α) (a' : β → β) (T : α → β) (f : α) : β :=
  T (a f) - a' (T f)
def pairCommutatorOf {β : Type*} [Sub β] (θ : FourTorus L m → ℝ) (a' : β → β)
    (t : (FineBond L m S → ComplexMatrix2) → (SiteAtLevel L m S.levels 0 → ComplexMatrix2) → β)
    (A : FineBond L m S → ComplexMatrix2) (v : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : β :=
  t (bondSmul S θ A) (siteSmul S θ v) - a' (t A v)
def covGradCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (g : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  commutatorOf (siteSmul S θ) (bondSmul S θ) (covGradAt S Ω W) g
def siteOpCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (g : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  commutatorOf (siteSmul S θ) (siteSmul S θ) (dirichletLapAt S Ω W) g +
    commutatorOf (siteSmul S θ) (siteSmul S θ) (topAveragingTerm S Ω W) g
def topSiteValuesCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (g : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FourTorus L m → ComplexMatrix2 :=
  commutatorOf (siteSmul S θ) (topSmul θ) (topSiteValues S Ω W) g
def topSiteAdjointCommutator (W : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (σ : FourTorus L m → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  commutatorOf (topSmul θ) (siteSmul S θ) (topSiteAdjoint S Ω W) σ
def axisComponentBase (μ : Fin 4) (x : SiteAtLevel L m S.levels 0) : FourTorus L m :=
  (Bond.forwardFrom x μ).centre
open Classical in
def differenceQuotient (θ : FourTorus L m → ℝ) (base : SiteAtLevel L m S.levels 0 → FourTorus L m)
    (P : Set (SiteAtLevel L m S.levels 0)) (ν : Fin 4) (x : SiteAtLevel L m S.levels 0) : ℝ :=
  if x + unitStep L m (levelDepth S.levels 0) ν ∈ P then
    (S.finestMesh L)⁻¹ *
      (θ (base x + (unitStep L m (levelDepth S.levels 0) ν : FourTorus L m)) - θ (base x))
  else 0
open Classical in
def fluxCommutator (θ : FourTorus L m → ℝ) (base : SiteAtLevel L m S.levels 0 → FourTorus L m)
    (P : Set (SiteAtLevel L m S.levels 0)) (U : FineBond L m S → ComplexMatrix2) (ν : Fin 4)
    (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (x : SiteAtLevel L m S.levels 0) :
    ComplexMatrix2 :=
  if x + unitStep L m (levelDepth S.levels 0) ν ∈ P then
    differenceQuotient S θ base P ν x •
      (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν))
        (f (x + unitStep L m (levelDepth S.levels 0) ν)) + f x)
  else 0
open Classical in
def diagonalCommutator (θ : FourTorus L m → ℝ) (base : SiteAtLevel L m S.levels 0 → FourTorus L m)
    (P : Set (SiteAtLevel L m S.levels 0)) (f : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (x : SiteAtLevel L m S.levels 0) : ComplexMatrix2 :=
  ((S.finestMesh L)⁻¹ * ∑ ν : Fin 4, (differenceQuotient S θ base P ν x -
    if x - unitStep L m (levelDepth S.levels 0) ν ∈ P then
      differenceQuotient S θ base P ν (x - unitStep L m (levelDepth S.levels 0) ν) else 0)) • f x
def diagonalCommutatorSite (θ : FourTorus L m → ℝ) (Y : Set (FourTorus L m))
    (p : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  diagonalCommutator S θ (fun x => (x : FourTorus L m)) (siteIndexSet S Y) p
def fluxCommutatorSite (θ : FourTorus L m → ℝ) (Y : Set (FourTorus L m))
    (U : FineBond L m S → ComplexMatrix2) (p : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun e =>
    fluxCommutator S θ (fun x => (x : FourTorus L m)) (siteIndexSet S Y) U e.axis p e.source)
def fluxCommutatorForm (θ : FourTorus L m → ℝ) (Y : Set (FourTorus L m))
    (U A : FineBond L m S → ComplexMatrix2) : FineBond L m S × Fin 4 → ComplexMatrix2 :=
  (bondAxisIndexSet S Y).indicator fun i =>
    fluxCommutator S θ (axisComponentBase S i.1.axis) (axisBaseSites S Y i.1.axis) U i.2
      (bondFormComponent A i.1.axis) i.1.source
def diagonalCommutatorForm (θ : FourTorus L m → ℝ) (Y : Set (FourTorus L m))
    (A : FineBond L m S → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  bondFormOfPositive ((bondIndexSet S Y).indicator fun e =>
    diagonalCommutator S θ (axisComponentBase S e.axis) (axisBaseSites S Y e.axis)
      (bondFormComponent A e.axis) e.source)
def commMapFirst (U : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (w : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  siteOpCommutator S Ω (firstMemberRestriction S Ω U) θ w
def commMapSite (U : FineBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    SiteTriple L m S → SiteTriple L m S
  | (v, w, σ) =>
    let W := firstMemberRestriction S Ω U
    (siteOpCommutator S Ω W θ v,
      siteOpCommutator S Ω W θ w - topSiteAdjointCommutator S Ω W θ σ,
      topSiteValuesCommutator S Ω W θ v)
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def bondComponentCommutator (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (k : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (A : FineBond L m S → ComplexMatrix2)
    (v w p : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : FineBond L m S → ComplexMatrix2 :=
  let W := firstMemberRestriction S Ω U
  commutatorOf (bondSmul S θ) (bondSmul S θ) (compressedOp S Ω 𝔸 U) A +
    commutatorOf (bondSmul S θ) (bondSmul S θ) (rowAveragingTerm S Ω W) A -
    covGradCommutator S Ω W θ (w + p) -
    commutatorOf (siteSmul S θ) (bondSmul S θ) (currentTerm S Ω W J) v -
    commutatorOf (bondSmul S θ) (bondSmul S θ) (secondOrderOp S Ω W k)
      (A - covGradAt S Ω W v) +
    secondOrderOp S Ω W k (covGradCommutator S Ω W θ v)
def fifthComponentCommutator (U J : FineBond L m S → ComplexMatrix2)
    (k : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (A : FineBond L m S → ComplexMatrix2) (v p : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (r : FourTorus L m → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  let W := firstMemberRestriction S Ω U
  diagonalCommutatorSite S θ (Ω 0) p +
    commutatorOf (siteSmul S θ) (siteSmul S θ) (topAveragingTerm S Ω W) p +
    topSiteAdjointCommutator S Ω W θ r -
    pairCommutatorOf S θ (siteSmul S θ) (siteCurrentSource S Ω W J) A v -
    covDivCommutator S Ω W θ (bondCurrentSource S Ω W J k A v)
def fluxSourceCommutator (U J : FineBond L m S → ComplexMatrix2)
    (k : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ)
    (A : FineBond L m S → ComplexMatrix2) (v p : SiteAtLevel L m S.levels 0 → ComplexMatrix2) :
    FineBond L m S → ComplexMatrix2 :=
  fluxCommutatorSite S θ (Ω 0) U p -
    pairCommutatorOf S θ (bondSmul S θ)
      (bondCurrentSource S Ω (firstMemberRestriction S Ω U) J k) A v
def commutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (k : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    FullTuple L m S → SourceTuple L m S
  | (A, v, w, σ, p, q, r, ω) =>
    let W := firstMemberRestriction S Ω U
    ((bondComponentCommutator S Ω 𝔸 U J k θ A v w p -
          commutatorOf (expansionSmul S θ) (bondSmul S θ) (expansionValuesAdjoint S Ω W) ω,
        siteOpCommutator S Ω W θ v - covDivCommutator S Ω W θ A,
        siteOpCommutator S Ω W θ w - topSiteAdjointCommutator S Ω W θ σ,
        topSiteValuesCommutator S Ω W θ v,
        fifthComponentCommutator S Ω U J k θ A v p r,
        siteOpCommutator S Ω W θ q,
        -topSiteValuesCommutator S Ω W θ q,
        commutatorOf (bondSmul S θ) (expansionSmul S θ) (expansionValuesOfForm S Ω W) A),
      fluxSourceCommutator S Ω U J k θ A v p)
def reducedCommutatorMap (𝔸 : Set (FourTorus L m)) (U J : FineBond L m S → ComplexMatrix2)
    (k : LeveledBond L m S → ComplexMatrix2) (θ : FourTorus L m → ℝ) :
    ReducedTuple L m S → ReducedSourceTuple L m S
  | (A, v, w, σ, p, q, r) =>
    let W := firstMemberRestriction S Ω U
    ((bondComponentCommutator S Ω 𝔸 U J k θ A v w p,
        siteOpCommutator S Ω W θ v - covDivCommutator S Ω W θ A,
        siteOpCommutator S Ω W θ w - topSiteAdjointCommutator S Ω W θ σ,
        topSiteValuesCommutator S Ω W θ v,
        fifthComponentCommutator S Ω U J k θ A v p r,
        siteOpCommutator S Ω W θ q,
        -topSiteValuesCommutator S Ω W θ q),
      fluxSourceCommutator S Ω U J k θ A v p)
end Operators
end SequenceTriples
end YangMills.Construction
end
