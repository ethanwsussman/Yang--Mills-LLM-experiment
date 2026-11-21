import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open PeriodicLattice Matrices
namespace EffectiveAction
abbrev IntPoint : Type := Fin 4 → ℤ
abbrev IntBond : Type := IntPoint × Fin 4
abbrev BondField : Type := IntBond → ComplexMatrix2
def unitSitePoint (n : IntPoint) : Fin 4 → ℝ := fun μ => (n μ : ℝ)
def fineSitePoint (L j : ℕ) (n : IntPoint) : Fin 4 → ℝ :=
  fun μ => (n μ : ℝ) * finestMeshInLevelUnits L j
def IntBond.endpoint (b : IntBond) : IntPoint := b.1 + Pi.single b.2 1
def cubeAround (M : ℕ) (c : IntPoint) : Set (Fin 4 → ℝ) :=
  {x | ∀ μ, |x μ - (M : ℝ) * (c μ : ℝ)| ≤ (M : ℝ) / 2}
def AdjacentCubes (c c' : IntPoint) : Prop := ∑ μ, |c μ - c' μ| = 1
@[ext]
structure CubeDomain where
  centers : Finset IntPoint
  centers_nonempty : centers.Nonempty
  chain_connected : ∀ c ∈ centers, ∀ c' ∈ centers, ∃ l : List IntPoint,
    (∀ q ∈ l, q ∈ centers) ∧ l.IsChain AdjacentCubes ∧ l.head? = some c ∧ l.getLast? = some c'
def CubeDomain.carrier (M : ℕ) (X : CubeDomain) : Set (Fin 4 → ℝ) :=
  ⋃ c ∈ X.centers, cubeAround M c
def CubeDomain.touchingBonds (L j M : ℕ) (X : CubeDomain) : Set IntBond :=
  {b | fineSitePoint L j b.1 ∈ X.carrier M ∨ fineSitePoint L j (IntBond.endpoint b) ∈ X.carrier M}
abbrev RootedDomain (M : ℕ) : Type :=
  {p : CubeDomain × IntPoint // unitSitePoint p.2 ∈ p.1.carrier M}
def TwiceDiffAtOrigin {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (Fin n → ℝ) → F) : Prop :=
  (∀ᶠ v in 𝓝 0, DifferentiableAt ℝ g v) ∧ DifferentiableAt ℝ (fderiv ℝ g) 0
def TwiceDiffNearOrigin {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (Fin n → ℝ) → F) : Prop :=
  ∀ᶠ v in 𝓝 0, DifferentiableAt ℝ g v ∧ DifferentiableAt ℝ (fderiv ℝ g) v
def expBondField (W : BondField) : BondField := fun b => ComplexMatrix2.matExp (W b)
abbrev LocalFamily : Type := CubeDomain → IntPoint → BondField → BondField → ℂ
def IsComplexTangentChart {n : ℕ} (T : (Fin n → ℝ) →ₗ[ℝ] BondField × BondField) : Prop :=
  ∀ v b, (T v).1 b ∈ ComplexMatrix2.traceless ∧ (T v).2 b ∈ ComplexMatrix2.traceless
structure IsLocalFamily (L j M : ℕ) (E : LocalFamily) : Prop where
  reads_locally : ∀ (p : RootedDomain M) (U U' J J' : BondField),
    (∀ b ∈ p.1.1.touchingBonds L j M, U b = U' b ∧ J b = J' b) →
      E p.1.1 p.1.2 U J = E p.1.1 p.1.2 U' J'
  twice_diff : ∀ (p : RootedDomain M) (n : ℕ)
    (T : (Fin n → ℝ) →ₗ[ℝ] BondField × BondField), IsComplexTangentChart T →
      TwiceDiffAtOrigin fun v => E p.1.1 p.1.2 (expBondField (T v).1) (T v).2
def hessianAtIdentity (f : BondField → BondField → ℂ) (v₁ v₂ : BondField × BondField) : ℂ :=
  deriv (fun s : ℝ => deriv (fun s' : ℝ =>
    f (expBondField (s • v₁.1 + s' • v₂.1)) (s • v₁.2 + s' • v₂.2)) 0) 0
def projectSite (L m K k : ℕ) (n : IntPoint) : SiteAtLevel L m K k :=
  ⟨fun μ => (((n μ : ℝ) * meshSize L (levelDepth K k) : ℝ) : AddCircle (torusSide L m)), n,
    fun _ => rfl⟩
def projectBond (L m K k : ℕ) (q : IntBond) : BondAtLevel L m K k :=
  Bond.forwardFrom (projectSite L m K k q.1) q.2
open Classical in
def singleBondForm {L m : ℕ} {i : ℤ} (x : Bond L m i) (A : ComplexMatrix2) :
    Bond L m i → ComplexMatrix2 :=
  fun b => if b = x then A else if b = x.opposite then -A else 0
def pushForwardForm (L m K j : ℕ) (B : BondField) : BondAtLevel L m K j → ComplexMatrix2 :=
  fun b => ∑ᶠ q : IntBond, singleBondForm (projectBond L m K j q) (B q) b
abbrev MinimizerSelection (L K j : ℕ) : Type :=
  ∀ m : ℕ, (BondAtLevel L m K j → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2
def IsRealTangentChart {L m : ℕ} {i : ℤ} {n : ℕ}
    (T : (Fin n → ℝ) →ₗ[ℝ] (Bond L m i → ComplexMatrix2)) : Prop :=
  ∀ v, IsBondForm compactLieAlgebra (T v)
def IsMinimizerSelection (ε : ℝ) (L K j : ℕ) (R : MinimizerSelection L K j) : Prop :=
  ∀ᶠ m in atTop, R m 0 = trivialGaugeField ∧
    ∀ (n : ℕ) (T : (Fin n → ℝ) →ₗ[ℝ] (BondAtLevel L m K j → ComplexMatrix2)),
      IsRealTangentChart T →
      ∀ᶠ v in 𝓝 0,
        CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K j (fun _ => univ)
          (datumOnLevel K j (expGaugeField (T v))) ∧
        R m (T v) ∈ regularCriticalFields (Averaging.smoothingRadius L) ε K j (fun _ => univ)
          (datumOnLevel K j (expGaugeField (T v))) ∧
        ∀ b, DifferentiableAt ℝ (fun v' => R m (T v') b) v
def fieldVariation {L K j : ℕ} (R : MinimizerSelection L K j) (B : BondField) (b : IntBond)
    (m : ℕ) : ComplexMatrix2 :=
  deriv (fun s : ℝ => R m (s • pushForwardForm L m K j B) (projectBond L m K 0 b)) 0
def currentVariation {L K j : ℕ} (R : MinimizerSelection L K j) (B : BondField) (b : IntBond)
    (m : ℕ) : ComplexMatrix2 :=
  deriv (fun s : ℝ =>
    yangMillsCurrent (finestMeshInLevelUnits L j) (R m (s • pushForwardForm L m K j B))
      (projectBond L m K 0 b)) 0
def IsFinitelySupportedRealForm (B : BondField) : Prop :=
  (Function.support B).Finite ∧ ∀ b, B b ∈ compactLieAlgebra
def HasLinearResponse {L K j : ℕ} (R : MinimizerSelection L K j) : Prop :=
  ∀ B, IsFinitelySupportedRealForm B → ∀ b,
    (∃ l, Tendsto (fieldVariation R B b) atTop (𝓝 l)) ∧
      ∃ l, Tendsto (currentVariation R B b) atTop (𝓝 l)
def linearResponse {L K j : ℕ} (R : MinimizerSelection L K j) (B : BondField) :
    BondField × BondField :=
  (fun b => limUnder atTop (fieldVariation R B b),
    fun b => limUnder atTop (currentVariation R B b))
def basisBondForm (t : Fin 3 → ComplexMatrix2.LieElement) (a : Fin 3) (x : IntBond) : BondField :=
  Pi.single x (t a).toMatrix
def polarizationSummand {L K j : ℕ} (M : ℕ) (R : MinimizerSelection L K j)
    (t : Fin 3 → ComplexMatrix2.LieElement) (E : LocalFamily) (x y : IntBond) (a : Fin 3)
    (p : RootedDomain M) : ℂ :=
  hessianAtIdentity (E p.1.1 p.1.2) (linearResponse R (basisBondForm t a x))
    (linearResponse R (basisBondForm t a y))
def polarization {L K j : ℕ} (M : ℕ) (R : MinimizerSelection L K j)
    (t : Fin 3 → ComplexMatrix2.LieElement) (E : LocalFamily) (x y : IntBond) : ℂ :=
  (1 / 3 : ℂ) * ∑ a, ∑' p : RootedDomain M, polarizationSummand M R t E x y a p
def IsStiffnessWith {L K j : ℕ} (M : ℕ) (R : MinimizerSelection L K j)
    (t : Fin 3 → ComplexMatrix2.LieElement) (E : LocalFamily)
    (P : Fin 4 → Fin 4 → IntPoint → ℂ) (c : ℂ) : Prop :=
  (∀ x y a, Summable (polarizationSummand M R t E x y a)) ∧
    (∀ x y : IntBond, polarization M R t E x y = P x.2 y.2 (y.1 - x.1)) ∧
    ∀ μ ν, μ ≠ ν → Summable (fun u : IntPoint => P μ ν u * (u μ : ℂ) * (u ν : ℂ)) ∧
      ∑' u : IntPoint, P μ ν u * (u μ : ℂ) * (u ν : ℂ) = c
def selectedMinimizers (ε : ℝ) (L K j : ℕ) : MinimizerSelection L K j :=
  Classical.epsilon fun R => IsMinimizerSelection ε L K j R ∧ HasLinearResponse R
def selectedBasis : Fin 3 → ComplexMatrix2.LieElement :=
  Classical.epsilon fun t => Orthonormal ℝ t
def HasStiffness (ε : ℝ) (L K j M : ℕ) (E : LocalFamily) (c : ℂ) : Prop :=
  IsLocalFamily L j M E ∧
    IsMinimizerSelection ε L K j (selectedMinimizers ε L K j) ∧
    HasLinearResponse (selectedMinimizers ε L K j) ∧
    ∃ P, IsStiffnessWith M (selectedMinimizers ε L K j) selectedBasis E P c
def stiffness (ε : ℝ) (L K j M : ℕ) (E : LocalFamily) : ℂ :=
  Classical.epsilon (HasStiffness ε L K j M E)
abbrev TorusFunctional (L K j : ℕ) : Type :=
  ∀ m : ℕ, (BondAtLevel L m K j → ComplexMatrix2) → ℝ
def IsTorusFunctional (L K j : ℕ) (Φ : TorusFunctional L K j) : Prop :=
  ∀ᶠ m in atTop, Φ m trivialGaugeField = 0 ∧
    ∀ (n : ℕ) (T : (Fin n → ℝ) →ₗ[ℝ] (BondAtLevel L m K j → ComplexMatrix2)),
      IsRealTangentChart T →
      TwiceDiffNearOrigin (fun v => Φ m (expGaugeField (T v))) ∧
        ∀ a : SiteAtLevel L m K j, ∀ᶠ v in 𝓝 0,
          Φ m (transportGaugeField (translateBy a) (expGaugeField (T v))) =
            Φ m (expGaugeField (T v))
def torusPolarization {L K j : ℕ} (Φ : TorusFunctional L K j) (m : ℕ)
    (B B' : BondAtLevel L m K j → ComplexMatrix2) : ℝ :=
  deriv (fun s : ℝ => deriv (fun s' : ℝ =>
    Φ m (expGaugeField (s • B + s' • B'))) 0) 0
open Classical in
def HasKernelLimit {L K j : ℕ} (t : Fin 3 → ComplexMatrix2.LieElement)
    (Φ : TorusFunctional L K j) (P : Fin 4 → Fin 4 → IntPoint → ℝ) : Prop :=
  ∀ (x y : IntBond) (a a' : Fin 3),
    Tendsto (fun m => torusPolarization Φ m (singleBondForm (projectBond L m K j x) (t a).toMatrix)
      (singleBondForm (projectBond L m K j y) (t a').toMatrix)) atTop
      (𝓝 (if a = a' then P x.2 y.2 (y.1 - x.1) else 0))
def IsTorusStiffnessWith {L K j : ℕ} (t : Fin 3 → ComplexMatrix2.LieElement)
    (Φ : TorusFunctional L K j) (c : ℝ) : Prop :=
  ∃ P, HasKernelLimit t Φ P ∧ ∀ μ ν, μ ≠ ν →
    Summable (fun u : IntPoint => P μ ν u * (u μ : ℝ) * (u ν : ℝ)) ∧
      ∑' u : IntPoint, P μ ν u * (u μ : ℝ) * (u ν : ℝ) = c
def HasTorusStiffness (L K j : ℕ) (Φ : TorusFunctional L K j) (c : ℝ) : Prop :=
  IsTorusFunctional L K j Φ ∧ IsTorusStiffnessWith selectedBasis Φ c
def torusStiffness (L K j : ℕ) (Φ : TorusFunctional L K j) : ℝ :=
  Classical.epsilon (HasTorusStiffness L K j Φ)
end EffectiveAction
end YangMills.Construction
