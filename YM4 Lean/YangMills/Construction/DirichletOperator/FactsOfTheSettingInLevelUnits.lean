import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.Dirichlet.UnitScaleSetting
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace LevelUnitFacts
variable {d L : ℕ} {aMinus aPlus S : ℝ}
def latticeCalculusOps (d : ℕ) (S ξ : ℝ) :
    Set ((Dirichlet.LatticeSite d S ξ → ℝ) → Dirichlet.LatticeSite d S ξ → ℝ) :=
  {T | ∃ μ : Fin d, T = Dirichlet.translateForward μ ∨ T = Dirichlet.translateBackward μ ∨
    T = Dirichlet.forwardDiff μ ∨ T = Dirichlet.backwardDiff μ}
structure ConstantBounds (d L : ℕ) (aMinus aPlus : ℝ) : Prop where
  coercivity_pos : 0 < WeightedGreen.coercivityConst aMinus
  coercivity_le : WeightedGreen.coercivityConst aMinus ≤ 4
  decayRate_pos : 0 < WeightedGreen.expDecayRate d L aMinus aPlus
  decayRate_le : WeightedGreen.expDecayRate d L aMinus aPlus ≤ 1 / (2 * (d : ℝ) * (L : ℝ) ^ 2)
structure BlockWeightFacts (d L : ℕ) : Prop where
  closed_form : ∀ n : ℕ, 1 ≤ n →
    Dirichlet.blockWeights L n = (1 - ((L : ℝ) ^ 2)⁻¹) / (1 - ((L : ℝ) ^ (2 * n))⁻¹)
  between : ∀ n : ℕ, 1 - ((L : ℝ) ^ 2)⁻¹ ≤ Dirichlet.blockWeights L n ∧
    Dirichlet.blockWeights L n ≤ 1
  admitted : Dirichlet.Parameters d L (1 - ((L : ℝ) ^ 2)⁻¹) 1
  coercivity_eq : WeightedGreen.coercivityConst (1 - ((L : ℝ) ^ 2)⁻¹) = 1 - ((L : ℝ) ^ 2)⁻¹
  decayRate_eq : WeightedGreen.expDecayRate d L (1 - ((L : ℝ) ^ 2)⁻¹) 1 =
    (1 - ((L : ℝ) ^ 2)⁻¹) / (8 * (d : ℝ) * ((L : ℝ) ^ 2 + 1))
structure SettingFacts (𝒮 : Dirichlet.BlockSetting d L aMinus aPlus S) : Prop where
  dist_comm : ∀ p q : Torus.PeriodicTorus d S, 𝒮.blockDist p q = 𝒮.blockDist q p
  dist_triangle : ∀ p q q' : Torus.PeriodicTorus d S,
    𝒮.blockDist p q' ≤ 𝒮.blockDist p q + 𝒮.blockDist q q'
  operators_commute : ∀ T ∈ latticeCalculusOps d S 𝒮.ξ, ∀ T' ∈ latticeCalculusOps d S 𝒮.ξ,
    T ∘ T' = T' ∘ T
  diff_adjoint : ∀ (μ : Fin d) (f g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ),
    Dirichlet.innerSum (Dirichlet.forwardDiff μ f) g =
      Dirichlet.innerSum f (Dirichlet.backwardDiff μ g)
  gradient_adjoint : ∀ (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ) (F : Dirichlet.BondField d S 𝒮.ξ),
    Dirichlet.fieldInnerSum (Dirichlet.grad f) F = Dirichlet.innerSum f (Dirichlet.latticeDiv F)
  doubleGradient_adjoint : ∀ (f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ)
    (Φ : Dirichlet.TwoTensorField d S 𝒮.ξ),
    Dirichlet.twoTensorInner (Dirichlet.secondDiff f) Φ =
      Dirichlet.innerSum f (Dirichlet.twoTensorDiv Φ)
  operator_symmetric : ∀ g h : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) g → Dirichlet.VanishesOff (𝒮.Ω 0) h →
      Dirichlet.innerSum g (𝒮.fullOperator h) = Dirichlet.innerSum (𝒮.fullOperator g) h
  operator_positive : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) f → f ≠ 0 → 0 < Dirichlet.innerSum f (𝒮.fullOperator f)
  green_symmetric : ∀ g h : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) g → Dirichlet.VanishesOff (𝒮.Ω 0) h →
      Dirichlet.innerSum g (𝒮.fullGreen h) = Dirichlet.innerSum (𝒮.fullGreen g) h
  green_positive : ∀ f : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) f → f ≠ 0 → 0 < Dirichlet.innerSum f (𝒮.fullGreen f)
  one_rule : ∀ E : Set (Dirichlet.LatticeBond d S 𝒮.ξ),
    Dirichlet.IsBoundaryRule (𝒮.Ω 0) (𝒮.Ω 0) E ↔ E = Dirichlet.boundaryBonds (𝒮.Ω 0)
  operator_form : ∀ g h : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) g → Dirichlet.VanishesOff (𝒮.Ω 0) h →
      Dirichlet.innerSum g (𝒮.fullOperator h) =
        Dirichlet.fieldInnerSum (Dirichlet.grad g) (Dirichlet.grad h) +
          Dirichlet.innerSum g (𝒮.averagingOp h)
  averaging_form : ∀ g h : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.VanishesOff (𝒮.Ω 0) g → Dirichlet.VanishesOff (𝒮.Ω 0) h →
      Dirichlet.innerSum g (𝒮.averagingOp h) =
        ∑ᶠ y ∈ 𝒮.centres, 𝒮.a (𝒮.centreIndex y) * 𝒮.centreSpacing y ^ ((d : ℤ) - 2) *
          𝒮.cellAverage g y * 𝒮.cellAverage h y
  region_norm : ∀ g : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) g →
    √(Dirichlet.dirichletForm (𝒮.Ω 0) (Dirichlet.boundaryBonds (𝒮.Ω 0)) g) =
      Dirichlet.fieldSiteNorm (Dirichlet.grad g)
  laplacian_eq : ∀ h : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ, Dirichlet.VanishesOff (𝒮.Ω 0) h →
    ∀ x : Dirichlet.LatticeSite d S 𝒮.ξ, (x : Torus.PeriodicTorus d S) ∈ 𝒮.Ω 0 →
      Dirichlet.latticeLaplacian h x = 𝒮.fullOperator h x - 𝒮.averagingOp h x
  sites_of_collar : ∀ y ∈ 𝒮.centres,
    𝒮.collar y ∩ (Torus.spacingLattice d S 𝒮.ξ : Set (Torus.PeriodicTorus d S)) =
      𝒮.siteBox y (((L : ℝ) + 9) * 𝒮.centreSpacing y)
  unitHolder_eq : ∀ σ : ℝ, 0 ≤ σ → σ < 1 → ∀ D : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    Dirichlet.unitScaleHolder σ D = Dirichlet.holderSeminorm σ D
  scaledHolder_mono : ∀ (D : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ) (s : ℝ), 0 < s →
    ∀ σ' σ : ℝ, 0 ≤ σ' → σ' ≤ σ →
      Dirichlet.scaledHolderSeminorm σ' s D ≤ Dirichlet.scaledHolderSeminorm σ s D
  card_cell : ∀ y ∈ 𝒮.centres,
    (((𝒮.cell y ∩ (Torus.spacingLattice d S 𝒮.ξ : Set (Torus.PeriodicTorus d S))).ncard : ℕ) : ℝ) =
      (𝒮.centreSpacing y / 𝒮.ξ) ^ d
  average_sq_le : ∀ y ∈ 𝒮.centres, ∀ v : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    𝒮.centreSpacing y ^ d * |𝒮.cellAverage v y| ^ 2 ≤
      𝒮.centreSpacing y ^ d * 𝒮.cellAverage (fun x => |v x|) y ^ 2
  average_abs_sq_le : ∀ y ∈ 𝒮.centres, ∀ v : Dirichlet.LatticeSite d S 𝒮.ξ → ℝ,
    𝒮.centreSpacing y ^ d * 𝒮.cellAverage (fun x => |v x|) y ^ 2 ≤
      Dirichlet.siteNormOn (𝒮.cell y) v ^ 2
theorem torusSide_ne_zero (hL : 0 < L) (m : ℕ) : PeriodicLattice.torusSide L m ≠ 0 := by apply _root_.YangMills.Construction.Tower.torusSide_ne_zero <;> assumption
theorem unitSide_ne_zero (hL : 0 < L) (m K t : ℕ) : Torus.unitSide L m K t ≠ 0 := by
  have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact mul_ne_zero two_ne_zero (zpow_ne_zero _ hne)
def levelUnitEquiv (hL : 0 < L) (m K t : ℕ) :
    PeriodicLattice.FourTorus L m ≃+ Torus.PeriodicTorus 4 (Torus.unitSide L m K t) :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ (torusSide_ne_zero hL m) (unitSide_ne_zero hL m K t)
def levelScaleData (K t e : ℕ) (ht : t ≤ K) : SeparatedSequences.ScaleData :=
  ⟨K, t, t, e, ht, ht⟩
def levelUnitRegions (hL : 0 < L) {m : ℕ} (K t e : ℕ) (ht : t ≤ K)
    (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) (n : ℕ) :
    Set (Torus.PeriodicTorus 4 (Torus.unitSide L m K t)) :=
  levelUnitEquiv hL m K t '' SeparatedSequences.truncatedMember (levelScaleData K t e ht) Ω n
def LevelUnitEquivSpec (hL : 0 < L) (m K t : ℕ) : Prop :=
  Torus.unitSide L m K t = PeriodicLattice.toLevelUnits L K t (PeriodicLattice.torusSide L m) ∧
    ∀ v : Fin 4 → ℝ,
      levelUnitEquiv hL m K t (Torus.torusProj 4 (PeriodicLattice.torusSide L m) v) =
        Torus.torusProj 4 (Torus.unitSide L m K t) (((L : ℝ) ^ ((K : ℤ) - (t : ℤ))) • v)
def SeparatedSequenceTransfer (hL : 0 < L) (aMinus aPlus : ℝ) (m K t e g : ℕ) (ht : t ≤ K)
    (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) : Prop :=
  Torus.IsSeparatedChain L (Torus.unitSpacing L t) (L ^ e) (L ^ g) t
      (levelUnitRegions hL K t e ht Ω) ∧
    ∀ a : ℕ → ℝ, (∀ n ≤ t, aMinus ≤ a n ∧ a n ≤ aPlus) →
      ∃ 𝒮 : Dirichlet.UnitScaleSetting 4 L aMinus aPlus K m t, 𝒮.M = L ^ e ∧ 𝒮.R₁ = L ^ g ∧
        𝒮.Ω = levelUnitRegions hL K t e ht Ω ∧ 𝒮.a = a
def MainClaim : Prop :=
  (∀ (d L : ℕ) (aMinus aPlus : ℝ), Dirichlet.Parameters d L aMinus aPlus →
    ConstantBounds d L aMinus aPlus ∧ BlockWeightFacts d L ∧
      ∀ (K m level : ℕ) (𝒮 : Dirichlet.UnitScaleSetting d L aMinus aPlus K m level),
        SettingFacts 𝒮.toBlockSetting) ∧
  ∀ (L : ℕ) (aMinus aPlus : ℝ), Dirichlet.Parameters 4 L aMinus aPlus →
    ∀ (hL : 0 < L) (K m t : ℕ) (ht : t ≤ K),
    LevelUnitEquivSpec hL m K t ∧
      ∀ e g : ℕ, L ≤ L ^ e → L ≤ L ^ g → ∀ Ω : ℕ → Set (PeriodicLattice.FourTorus L m),
        SeparatedSequences.IsSeparatedSequence (levelScaleData K t e ht) ((L ^ g : ℕ) : ℝ) Ω →
          (Ω 0).Nonempty →
          SeparatedSequenceTransfer hL aMinus aPlus m K t e g ht Ω
end LevelUnitFacts
end YangMills.Construction
