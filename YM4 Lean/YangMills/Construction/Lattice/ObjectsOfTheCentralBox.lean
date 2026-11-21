import YangMills.Construction.Lattice.ExtendibilityTestOfAComponentOfTheOperation
import YangMills.Construction.Lattice.GaugeNests
import YangMills.Construction.Lattice.OneStepAndLargeFieldOperationsAtAPoint
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice Matrices
namespace PeriodicLattice.CentralBlock
open CubesOfStep
section Minimizer
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (X : Set (FourTorus c.L m))
def IsBoxMinimizer (V W : BondAtLevel c.L m K k → ComplexMatrix2) : Prop :=
  IsInCriticalOrbitOverBox X (S.innerBoxIn c.r x Q X) V
    (HasComponentBackground c.εv (Nat.log c.L c.M₁) X)
    (componentBackground c.εv (Nat.log c.L c.M₁) X) W
def baseDatum (U : BondAtLevel c.L m K 0 → ComplexMatrix2) : AllLevelFields c.L m K :=
  fun j => activeAveragingMap U j
def fluctuationField (V'' V₀ : AllLevelFields c.L m K) : AllLevelFields c.L m K :=
  open Classical in
  fun j b => if (⟨j, b⟩ : Σ q : ℕ, BondAtLevel c.L m K q) ∈ S.nestFixedBonds c.r x Q X
    then V'' j b * (V₀ j b)⁻¹ else 1
end Minimizer
section Frames
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (X : Set (FourTorus c.L m))
def nestTreeInFrame (f : SignedFrame) : Set (IndexedBond c.L m) :=
  rotatedNestGaugeTree f (Thresholds.delayDepth c.L c.r x k + 1) (S.nestShell c.r x Q X)
    (ScaleLabel.shellDepth K k)
def nestTreeOfFrames (ρ : ↥Q → SignedFrame) : Set (IndexedBond c.L m) :=
  ⋃ Y : ↥Q, nestTreeInFrame c S Q Y.1 (ρ Y)
variable {c}
def freeBondsOfTree (B : Set (Σ q : ℕ, BondAtLevel c.L m K q)) (T : Set (IndexedBond c.L m)) :
    Set (Σ q : ℕ, BondAtLevel c.L m K q) :=
  {t | t ∈ B ∧ t.2.IsPositivelyOriented ∧
    (⟨levelDepth K t.1, t.2⟩ : IndexedBond c.L m) ∉ positiveTreeBonds T}
def fieldOffTree (B : Set (Σ q : ℕ, BondAtLevel c.L m K q)) (T : Set (IndexedBond c.L m))
    (w : ↥(freeBondsOfTree B T) → ComplexMatrix2) : AllLevelFields c.L m K :=
  open Classical in
  fun j b =>
    if h : (⟨j, b⟩ : Σ q : ℕ, BondAtLevel c.L m K q) ∈ freeBondsOfTree B T then w ⟨_, h⟩
    else if h' : (⟨j, b.opposite⟩ : Σ q : ℕ, BondAtLevel c.L m K q) ∈ freeBondsOfTree B T
      then (w ⟨_, h'⟩)⁻¹ else 1
def gaugeFixedIntegral (B : Set (Σ q : ℕ, BondAtLevel c.L m K q)) (T : Set (IndexedBond c.L m))
    (F : AllLevelFields c.L m K → ℂ) : ℂ :=
  ∫ w, F (fieldOffTree B T fun e => (w e : ComplexMatrix2))
    ∂ComplexMatrix2.haarPi ↥(freeBondsOfTree B T)
variable (c)
def fluctuationSmallnessIndicator (V' : AllLevelFields c.L m K) : ℝ :=
  open Classical in
  if ∀ t ∈ S.nestFixedBonds c.r x Q X, V' t.1 t.2 ∈ ComplexMatrix2.unitaryLogDomain ∧
      ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.unitaryLog (V' t.1 t.2)) <
        Thresholds.deltaPrimeThreshold c.A₁ c.𝔭₁ x k
  then 1 else 0
end Frames
section OuterShell
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ) (k : ℕ)
def outerShellLevel : ℕ := (lowerLevel c.L c.r x k).toNat
def outerShellIndex : ℤ := densityPartitionIndex c K x (outerShellLevel c x k)
def outerShellThreshold : ℝ :=
  1 / 2 * Thresholds.epsThreshold c.A₀ c.𝔭₀ x (outerShellLevel c x k) *
    ((c.L : ℝ) ^ ((k : ℤ) - lowerLevel c.L c.r x k) * finestMeshInLevelUnits c.L k) ^ 2
variable {K x k}
variable (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (X : Set (FourTorus c.L m))
def trimmedDomainThickenedOnce : Set (FourTorus c.L m) :=
  layerEnlargement
    (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) (ScaleLabel.nestBaseLevel c.L c.r x k))
    (S.trimmedDomain c.r x Q (ScaleLabel.nestBaseLevel c.L c.r x k)) 1
def outerShell : Set (FourTorus c.L m) :=
  cubeMeet K
    (cubeMeet K
      (complementRegion
        (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) (ScaleLabel.nestBaseLevel c.L c.r x k))
        (trimmedDomainThickenedOnce c S Q))
      (S.domainSeq (outerShellLevel c x k)))
    X
def identityOnTrimmedDomain (V : BondAtLevel c.L m K (outerShellLevel c x k) → ComplexMatrix2) :
    BondAtLevel c.L m K (outerShellLevel c x k) → ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ (bondsInside (S.trimmedDomainThickened c.r x Q) :
      Set (BondAtLevel c.L m K (outerShellLevel c x k))) then 1 else V b
def outerShellCubeIndicator (V : BondAtLevel c.L m K (outerShellLevel c x k) → ComplexMatrix2)
    (D : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if DensityTestFieldDefined c K x (outerShellLevel c x k) (identityOnTrimmedDomain c S Q V) D ∧
      PlaquettesNearIdentity c K
        (densityTestField c K x (outerShellLevel c x k) (identityOnTrimmedDomain c S Q V) D)
        (densityCollar c K x (outerShellLevel c x k) D 1) (outerShellThreshold c x k)
  then 1 else 0
def outerShellIndicator (V : BondAtLevel c.L m K (outerShellLevel c x k) → ComplexMatrix2)
    (Y : Set (FourTorus c.L m)) : ℝ :=
  ∏ᶠ D ∈ partitionCubesIn (outerShellIndex c K x k) Y, outerShellCubeIndicator c S Q V D
def outerShellTerm (V : BondAtLevel c.L m K (outerShellLevel c x k) → ComplexMatrix2)
    (R P : Set (FourTorus c.L m)) : ℝ :=
  partitionOfUnityTerm c.L (outerShellIndex c K x k) (outerShellCubeIndicator c S Q V) R P
end OuterShell
end PeriodicLattice.CentralBlock
end YangMills.Construction
