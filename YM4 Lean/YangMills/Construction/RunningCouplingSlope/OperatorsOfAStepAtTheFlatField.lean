import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairing
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.FlatLinearization
variable {n : ℕ}
def contourWeight (L : ℕ) (c : TorusFields.TorusBond n) (b : TorusFields.TorusBond (n * L)) : ℝ :=
  FlatLinearization.contourAverage L (FlatLinearization.indicatorForm b) c
open Classical in
def flatStepOperator (a : ℝ) (L : ℕ) [NeZero n]
    (K : TorusFields.TorusBond (n * L) → TorusFields.TorusBond (n * L) → ℝ)
    (b b' : TorusFields.TorusBond (n * L)) : ℝ :=
  if FlatLinearization.IsBlockTreeBond L b ∨ FlatLinearization.IsBlockTreeBond L b' then (if b = b' then 1 else 0)
  else K b b' + a * ∑ c : TorusFields.TorusBond n, contourWeight L c b * contourWeight L c b'
open Classical in
def flatStepSource (a : ℝ) (L : ℕ) (c : TorusFields.TorusBond n) (x : TorusFields.TorusBond (n * L)) : ℝ :=
  if FlatLinearization.IsBlockTreeBond L x then 0 else a * contourWeight L c x
open Classical in
def responseOfInverse (a : ℝ) (L : ℕ)
    (G : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond (n * L) → ℝ) (n : ℕ)
    (b : TorusFields.TorusBond (n * L)) (c : TorusFields.TorusBond n) : ℝ :=
  if hn : n ≠ 0 ∧ L ≠ 0 then
    haveI : NeZero n := ⟨hn.1⟩
    haveI : NeZero L := ⟨hn.2⟩
    ∑ x : TorusFields.TorusBond (n * L), G n b x * flatStepSource a L c x
  else 0
abbrev LatticeOneForm : Type := TorusLumps.LatticeBond → ℝ
def latticeLineSum (ξ : LatticeOneForm) : (Fin 4 → ℤ) → List BlockAverages.PathStep → ℝ
  | _, [] => 0
  | w, st :: r => (if st.2 then ξ (w, st.1) else - ξ (w - LatticeFractionalIntegration.basisVector st.1, st.1)) +
      latticeLineSum ξ (w + FlatPairing.stepDisplacement st) r
def blockCentreOnLattice (L : ℕ) (y : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * y i
def latticeContourAverage (L : ℕ) (ξ : LatticeOneForm) (c : TorusLumps.LatticeBond) : ℝ :=
  (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ BlockAverages.centredCube L, ∑ π : Equiv.Perm (Fin 4),
    latticeLineSum ξ (blockCentreOnLattice L c.1) (BlockAverages.bondContour L h π c.2)
def latticeBlockOf (L : ℕ) (w : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (w i + ((L : ℤ) - 1) / 2) / (L : ℤ)
def offsetInBlock (L : ℕ) (w : Fin 4 → ℤ) : Fin 4 → ℤ := w - blockCentreOnLattice L (latticeBlockOf L w)
def IsLatticeTreeBond (L : ℕ) (b : TorusLumps.LatticeBond) : Prop :=
  latticeBlockOf L (b.1 + LatticeFractionalIntegration.basisVector b.2) = latticeBlockOf L b.1 ∧
    ∀ l, b.2 < l → offsetInBlock L b.1 l = 0
def VanishesOnLatticeTrees (L : ℕ) (ξ : LatticeOneForm) : Prop := ∀ b, IsLatticeTreeBond L b → ξ b = 0
def latticeContourWeight (L : ℕ) (c b : TorusLumps.LatticeBond) : ℝ :=
  latticeContourAverage L (fun b' => if b' = b then 1 else 0) c
open Classical in
def latticeStepOperator (a : ℝ) (L : ℕ) (hl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ)
    (b b' : TorusLumps.LatticeBond) : ℝ :=
  if IsLatticeTreeBond L b ∨ IsLatticeTreeBond L b' then (if b = b' then 1 else 0)
  else hl b b' + a * ∑' c : TorusLumps.LatticeBond, latticeContourWeight L c b * latticeContourWeight L c b'
open Classical in
def latticeStepSource (a : ℝ) (L : ℕ) (c x : TorusLumps.LatticeBond) : ℝ :=
  if IsLatticeTreeBond L x then 0 else a * latticeContourWeight L c x
def latticeResponseOfInverse (a : ℝ) (L : ℕ) (Gl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ)
    (b c : TorusLumps.LatticeBond) : ℝ :=
  ∑' x : TorusLumps.LatticeBond, Gl b x * latticeStepSource a L c x
def fineLinearPotential (L : ℕ) (b : TorusLumps.LatticeBond) : ℝ :=
  (L : ℝ)⁻¹ ^ 2 * ((b.1 0 : ℤ) : ℝ) * SlopeCoefficient.constantOneForm SlopeCoefficient.secondAxis b
def HasPolynomialGrowth (v : LatticeOneForm) : Prop :=
  ∃ C m : ℝ, ∀ b, |v b| ≤ C * (1 + SlopeCoefficient.offsetNormReal b.1) ^ m
def TendstoLatticeKernel (h : FlatLinearization.BondKernel)
    (hl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ) : Prop :=
  ∀ b c : TorusLumps.LatticeBond,
    Filter.Tendsto (fun m => h m (TorusLumps.bondFrom 0 b) (TorusLumps.bondFrom 0 c)) Filter.atTop (𝓝 (hl b c))
structure IsGreenFamily (a : ℝ) (L : ℕ) (h : FlatLinearization.BondKernel)
    (hl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ)
    (G : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond (n * L) → ℝ)
    (Gl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ) : Prop where
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in Filter.atTop, ∀ b c : TorusFields.TorusBond (n * L),
    |G n b c| ≤ M * Real.exp (-(θ * TorusFields.supDist b.1 c.1))
  right_inv : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L] (b c : TorusFields.TorusBond (n * L)),
    ∑ x, flatStepOperator a L (h (n * L)) b x * G n x c = if b = c then 1 else 0
  left_inv : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L] (b c : TorusFields.TorusBond (n * L)),
    ∑ x, G n b x * flatStepOperator a L (h (n * L)) x c = if b = c then 1 else 0
  tendsto : ∀ b c : TorusLumps.LatticeBond,
    Filter.Tendsto (fun n => G n (TorusLumps.bondFrom 0 b) (TorusLumps.bondFrom 0 c)) Filter.atTop (𝓝 (Gl b c))
  lattice_exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ b c : TorusLumps.LatticeBond,
    |Gl b c| ≤ M * Real.exp (-(θ * SlopeCoefficient.offsetNormReal (b.1 - c.1)))
  lattice_hasSum_inv : ∀ b c : TorusLumps.LatticeBond,
    HasSum (fun x => Gl b x * latticeStepOperator a L hl x c) (if b = c then 1 else 0)
structure IsResponseSequence (a : ℝ) (L : ℕ) (h : FlatLinearization.BondKernel)
    (P : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond n → ℝ)
    (Pl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ) : Prop where
  minimizer_and_pos : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L],
    FlatLinearization.IsMinimizerFamily a L (h (n * L)) (P n) ∧
      FlatLinearization.IsPositiveOnTreeGauge (n := n) a L (h (n * L))
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in Filter.atTop, ∀ (b : TorusFields.TorusBond (n * L)) (c : TorusFields.TorusBond n),
    |P n b c| ≤ M * Real.exp (-(θ * TorusFields.supDist b.1 (SlopeCoefficient.blockCentreSite L c.1)))
  translation_invariant : ∀ᶠ n in Filter.atTop, ∀ (b : TorusFields.TorusBond (n * L)) (c : TorusFields.TorusBond n)
    (u : TorusFields.TorusSite n),
    P n (b.1 + SlopeCoefficient.blockCentreSite L u, b.2) (c.1 + u, c.2) = P n b c
  tendsto : ∀ b c : TorusLumps.LatticeBond,
    Filter.Tendsto (fun n => P n (TorusLumps.bondFrom 0 b) (TorusLumps.bondFrom 0 c)) Filter.atTop (𝓝 (Pl b c))
end YangMills.Construction.FlatLinearization
end
