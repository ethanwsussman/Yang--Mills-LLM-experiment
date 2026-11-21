import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import YangMills.Construction.SeparatedSequences.RatesOfTheInputsAndOfTheExpansion
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences
open scoped ENNReal
noncomputable section
namespace SeparatedFrame
def innerRadius (L : ℕ) : ℝ := 3 * (L : ℝ) + 2
end SeparatedFrame
structure SeparatedFrame (L m : ℕ) where
  L_odd : Odd L
  thirteen_le_L : 13 ≤ L
  m_pos : 0 < m
  K : ℕ
  K_pos : 0 < K
  t : ℕ
  t_le : t ≤ K
  e : ℕ
  r : ℕ
  Ω : ℕ → Set (FourTorus L m)
  isSeparated : IsSeparatedSequence ⟨K, t, t, e, t_le, t_le⟩ ((L : ℝ) ^ r) Ω
  L_le_gap : (L : ℝ) ≤ (L : ℝ) ^ r
  L_four_le_block : (L : ℝ) ^ 4 ≤ (L : ℝ) ^ e
  log_le_gap_mul_block :
    512 * Real.log (L : ℝ) / SeparatedSequences.operatorExpansionRate L ≤ (L : ℝ) ^ r * (L : ℝ) ^ e
namespace SeparatedFrame
variable {L m : ℕ} (F : SeparatedFrame L m)
abbrev scaleData : ScaleData := ⟨F.K, F.t, F.t, F.e, F.t_le, F.t_le⟩
def mesh : ℝ := F.scaleData.finestMesh L
def meshAt (n : ℕ) : ℝ := F.scaleData.levelMesh L n
abbrev layerAt (n : ℕ) : Set (FourTorus L m) := layerSet F.scaleData F.Ω n
abbrev layerSitesAt (n : ℕ) : Set (SiteAtLevel L m F.K n) := layerLatticeSites F.scaleData F.Ω n
abbrev Centre : Type := ↥(layerPoints F.scaleData F.Ω)
variable {F}
def Centre.level (y : F.Centre) : ℕ :=
  sInf {n | n ≤ F.t ∧ ∃ x : SiteAtLevel L m F.K n, x ∈ F.layerSitesAt n ∧ (x : FourTorus L m) = y.1}
def Centre.scale (y : F.Centre) : ℝ := F.meshAt y.level
def Centre.cell (y : F.Centre) : Set (FourTorus L m) :=
  closedSupCube y.1 (meshSize L (levelDepth F.K y.level))
variable (F)
abbrev FineBond : Type :=
  {b : BondAtLevel L m F.K 0 //
    b ∈ (bondsInside (F.Ω 0) : Set (BondAtLevel L m F.K 0)) ∧ b.IsPositivelyOriented}
abbrev FinePlaquette : Type :=
  ↥(plaquettesInside (F.Ω 0) : Set (PlaquetteAtLevel L m F.K 0))
def memberAt (n : ℕ) : Set (BondAtLevel L m F.K n) :=
  {c | c ∈ (bondsInside (F.Ω 0) : Set (BondAtLevel L m F.K n)) ∧
    c ∈ (bondsMeeting (F.Ω n) : Set (BondAtLevel L m F.K n)) ∧
    c ∉ (bondsMeeting (chainWithEmptyTail F.t F.Ω (n + 1)) : Set (BondAtLevel L m F.K n))}
def determiningBonds : Set (Σ n : ℕ, BondAtLevel L m F.K n) :=
  {q | q.1 ≤ F.t ∧ q.2 ∈ F.memberAt q.1}
abbrev DetBond : Type :=
  {q : Σ n : ℕ, BondAtLevel L m F.K n // q ∈ F.determiningBonds ∧ q.2.IsPositivelyOriented}
def IsInnerBond {n : ℕ} (c : BondAtLevel L m F.K n) : Prop :=
  c.source ∈ F.layerSitesAt n ∧ c.target ∈ F.layerSitesAt n
def IsOuterEndpoint {n : ℕ} (c : BondAtLevel L m F.K n) (z : SiteAtLevel L m F.K n) : Prop :=
  (z = c.source ∨ z = c.target) ∧ (z : FourTorus L m) ∉ F.Ω n
variable {F}
def DetBond.level (c : F.DetBond) : ℕ := c.1.1
def DetBond.asBond (c : F.DetBond) : BondAtLevel L m F.K c.level := c.1.2
def DetBond.anchor (c : F.DetBond) : FourTorus L m :=
  open Classical in
  if c.asBond.source ∈ F.layerSitesAt c.level then (c.asBond.source : FourTorus L m)
  else (c.asBond.target : FourTorus L m)
def FineBond.LiesOver (b : F.FineBond) (y : F.Centre) : Prop :=
  (b.1.source : FourTorus L m) ∈ y.cell
def FinePlaquette.LiesOver (p : F.FinePlaquette) (y : F.Centre) : Prop :=
  (p.1.origin : FourTorus L m) ∈ y.cell
variable (F)
abbrev FineForms : Type := F.FineBond → Matrices.ComplexMatrix2.traceless
abbrev DetFields : Type := F.DetBond → Matrices.ComplexMatrix2.traceless
variable {F}
variable (F)
variable {F}
def localFormNorm (A : F.FineForms) (y : F.Centre) : ℝ :=
  ⨆ b : {b : F.FineBond // b.LiesOver y},
    y.scale * Matrices.ComplexMatrix2.operatorNorm (A b.1 : Matrices.ComplexMatrix2)
variable (F)
variable {F}
def supFormNorm (A : F.FineForms) : ℝ := ⨆ y, localFormNorm A y
end SeparatedFrame
end
end YangMills.Construction
