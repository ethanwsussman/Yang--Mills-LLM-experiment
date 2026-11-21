import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
instance instCountableSite : Countable (Site L m j) := by
  have hsurj : Function.Surjective (fun n : Fin 4 → ℤ =>
      (⟨fun μ => (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)), ⟨n, fun _ => rfl⟩⟩ :
        Site L m j)) := by
    rintro ⟨x, n, hn⟩
    exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  exact hsurj.countable
instance instCountableBond : Countable (Bond L m j) := by
  have hinj : Function.Injective (fun e : Bond L m j => (e.source, e.target)) := by
    intro e e' he
    exact Bond.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
  exact hinj.countable
def IsReversalClosed (S : Set (Bond L m j)) : Prop := ∀ e ∈ S, e.opposite ∈ S
def IsGaugeField (G : Set ComplexMatrix2) (S : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2) :
    Prop :=
  (∀ e ∈ S, U e ∈ G) ∧ ∀ e ∈ S, U e.opposite = (U e)⁻¹
abbrev compactGaugeGroup : Set ComplexMatrix2 := (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)
abbrev complexGaugeGroup : Set ComplexMatrix2 := ComplexMatrix2.unitDeterminant
def compactGaugeFields (L m : ℕ) (j : ℤ) : Set (Bond L m j → ComplexMatrix2) :=
  {U | IsGaugeField compactGaugeGroup univ U}
abbrev gaugeFieldsAtLevel (L m K k : ℕ) : Set (BondAtLevel L m K k → ComplexMatrix2) :=
  compactGaugeFields L m (levelDepth K k)
abbrev PositivelyOrientedBond (L m : ℕ) (j : ℤ) : Type := {e : Bond L m j // e.IsPositivelyOriented}
def gaugeFieldOfPositive (g : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (e : Bond L m j) : ComplexMatrix2 :=
  open Classical in
  if he : e.IsPositivelyOriented then (g ⟨e, he⟩ : ComplexMatrix2)
  else if he' : e.opposite.IsPositivelyOriented then ((g ⟨e.opposite, he'⟩ : ComplexMatrix2))⁻¹
  else 1
def gaugeFieldHaar (L m : ℕ) (j : ℤ) :
    Measure (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :=
  ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)
def trivialGaugeField : Bond L m j → ComplexMatrix2 := fun _ => 1
def pathHolonomy (U : Bond L m j → ComplexMatrix2) (γ : List (Bond L m j)) : ComplexMatrix2 :=
  (γ.map U).prod
def plaquetteHolonomy (U : Bond L m j → ComplexMatrix2) (P : Plaquette L m j) : ComplexMatrix2 :=
  pathHolonomy U P.boundaryBonds
def IsGaugeMap (G : Set ComplexMatrix2) (g : Site L m j → ComplexMatrix2) : Prop := ∀ x, g x ∈ G
def gaugeTransform (g : Site L m j → ComplexMatrix2) (U : Bond L m j → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  fun e => g e.source * U e * (g e.target)⁻¹
def Site.toSublattice (y : Site L m j) (j' : ℤ) : Site L m j' :=
  Classical.epsilon fun x : Site L m j' => (x : FourTorus L m) = y
def restrictGaugeMap {K k : ℕ} (n : ℕ) (g : SiteAtLevel L m K k → ComplexMatrix2) :
    SiteAtLevel L m K n → ComplexMatrix2 :=
  fun x => g (x.toSublattice (levelDepth K k))
def IsBondForm (V : Set ComplexMatrix2) (A : Bond L m j → ComplexMatrix2) : Prop :=
  (∀ e : Bond L m j, e.IsPositivelyOriented → A e ∈ V) ∧ ∀ e : Bond L m j, A e.opposite = -A e
def bondFormComponent (A : Bond L m j → ComplexMatrix2) (μ : Fin 4) (x : Site L m j) :
    ComplexMatrix2 :=
  A (Bond.forwardFrom x μ)
def bondFormSumAlong (A : Bond L m j → ComplexMatrix2) (γ : List (Bond L m j)) : ComplexMatrix2 :=
  (γ.map A).sum
def IsPlaquetteForm (V : Set ComplexMatrix2) (F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) :
    Prop :=
  (∀ μ ν x, μ < ν → F μ ν x ∈ V) ∧ ∀ μ ν x, F ν μ x = -F μ ν x
def plaquetteFormOf (f : Plaquette L m j → ComplexMatrix2) :
    Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 :=
  fun μ ν x =>
    if h : μ < ν then f ⟨x, μ, ν, h⟩ else if h' : ν < μ then -f ⟨x, ν, μ, h'⟩ else 0
def IsSiteField (V : Set ComplexMatrix2) (f : Site L m j → ComplexMatrix2) : Prop := ∀ x, f x ∈ V
abbrev complexLieAlgebra : Set ComplexMatrix2 := (ComplexMatrix2.traceless : Set ComplexMatrix2)
abbrev compactLieAlgebra : Set ComplexMatrix2 :=
  (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2)
def expTwist (A U : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun e => if e.IsPositivelyOriented then ComplexMatrix2.matExp (Complex.I • A e) * U e
    else (ComplexMatrix2.matExp (Complex.I • A e.opposite) * U e.opposite)⁻¹
def expGaugeField (B : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  fun e => ComplexMatrix2.matExp (Complex.I • B e)
def covDeriv (a : ℝ) (U : Bond L m j → ComplexMatrix2) (μ : Fin 4) (f : Site L m j → ComplexMatrix2)
    (x : Site L m j) : ComplexMatrix2 :=
  ((a⁻¹ : ℝ) : ℂ) •
    (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x μ)) (f (x + unitStep L m j μ)) - f x)
def covDerivNorm (a : ℝ) (U A : Bond L m j → ComplexMatrix2) (x : Site L m j) : ℝ :=
  ⨆ p : Fin 4 × Fin 4,
    ComplexMatrix2.operatorNorm (covDeriv a U p.1 (bondFormComponent A p.2) x)
def covExteriorDeriv (a : ℝ) (U A : Bond L m j → ComplexMatrix2) :
    Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 :=
  fun μ ν x => covDeriv a U μ (bondFormComponent A ν) x -
    covDeriv a U ν (bondFormComponent A μ) x
def siteInner (a : ℝ) (f f' : Site L m j → ComplexMatrix2) : ℂ :=
  ((a ^ 4 : ℝ) : ℂ) * ∑ᶠ x : Site L m j, ComplexMatrix2.halfTrace (f x * f' x)
def bondFormInner (a : ℝ) (A B : Bond L m j → ComplexMatrix2) : ℂ :=
  ((a ^ 4 : ℝ) : ℂ) * ∑ᶠ x : Site L m j, ∑ μ : Fin 4,
    ComplexMatrix2.halfTrace (bondFormComponent A μ x * bondFormComponent B μ x)
def plaquetteFormInner (a : ℝ) (F H : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) : ℂ :=
  ((a ^ 4 : ℝ) : ℂ) * ∑ᶠ x : Site L m j, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
    ComplexMatrix2.halfTrace (F μ ν x * H μ ν x)
def covExteriorDerivAdjoint (a : ℝ) (U : Bond L m j → ComplexMatrix2)
    (F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  Classical.epsilon fun B => IsBondForm complexLieAlgebra B ∧ ∀ A, IsBondForm complexLieAlgebra A →
    bondFormInner a B A = plaquetteFormInner a F (covExteriorDeriv a U A)
def curvatureAt (a : ℝ) (U : Bond L m j → ComplexMatrix2) (P : Plaquette L m j) : ComplexMatrix2 :=
  (((a⁻¹) ^ 2 : ℝ) : ℂ) • ((2 * Complex.I)⁻¹ •
    (plaquetteHolonomy U P - (plaquetteHolonomy U P)⁻¹))
def curvature (a : ℝ) (U : Bond L m j → ComplexMatrix2) :
    Fin 4 → Fin 4 → Site L m j → ComplexMatrix2 :=
  plaquetteFormOf (curvatureAt a U)
def yangMillsCurrent (a : ℝ) (U : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  covExteriorDerivAdjoint a U (curvature a U)
end PeriodicLattice
end YangMills.Construction
