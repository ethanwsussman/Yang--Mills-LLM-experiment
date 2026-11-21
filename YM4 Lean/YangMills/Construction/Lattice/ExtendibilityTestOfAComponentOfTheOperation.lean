import YangMills.Construction.Lattice.CriticalOrbitOverABox
import YangMills.Construction.Lattice.LocalisedBackgroundsOfSetsInForce
import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices
open scoped ENNReal
namespace PeriodicLattice
variable {L m K k : ℕ}
def HasComponentBackground (a₀ : ℝ) (n : ℕ) (X : Set (FourTorus L m))
    (W : BondAtLevel L m K k → ComplexMatrix2) : Prop :=
  ∃ U, IsLocalizedBackground a₀ K k n X (bondsMeeting X) W U
def componentBackground (a₀ : ℝ) (n : ℕ) (X : Set (FourTorus L m))
    (W : BondAtLevel L m K k → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  chosenLocalizedBackground a₀ K k n X (bondsMeeting X) W
namespace ScaleLabel
variable {m' : ℕ} {c : ℕ → ℕ}
variable (a₀ A₀ : ℝ) (𝔭₀ n r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
  (Q : Set (Set (FourTorus L m))) (X : Set (FourTorus L m))
def outerPlaquetteDeviation (W : BondAtLevel L m K k → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ p ∈ (plaquettesInside (complementRegion (coarseCubeIndex K m' k) (S.domainSeq k) ∩ X) :
      Set (PlaquetteAtLevel L m K 0)),
    ENNReal.ofReal (ComplexMatrix2.operatorNorm (plaquetteHolonomy (componentBackground a₀ n X W) p - 1))
def boxVariations (V : BondAtLevel L m K k → ComplexMatrix2) :
    Set (BondAtLevel L m K k → ComplexMatrix2) :=
  fieldsAgreeingOffBox X (S.innerBoxIn r x Q X) V
def extensionInfimum (V : BondAtLevel L m K k → ComplexMatrix2) : ℝ≥0∞ :=
  ⨅ W ∈ S.boxVariations r x Q X V, S.outerPlaquetteDeviation a₀ n X W
def extensionThreshold (A₀ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ) (_S : ScaleLabel L m K m' c k) : ℝ :=
  2 * Thresholds.epsThreshold A₀ 𝔭₀ x k * finestMeshInLevelUnits L k ^ 2
def extensionTest (V : BondAtLevel L m K k → ComplexMatrix2) : ℝ :=
  open Classical in
  if S.extensionInfimum a₀ n r x Q X V < ENNReal.ofReal (S.extensionThreshold A₀ 𝔭₀ x)
  then 1 else 0
def completedExtensionInfimum (V : BondAtLevel L m K k → ComplexMatrix2) : ℝ≥0∞ :=
  ⨅ W ∈ {W | W ∈ S.boxVariations r x Q X V ∧ HasComponentBackground a₀ n X W},
    S.outerPlaquetteDeviation a₀ n X W
def completedExtensionTest (V : BondAtLevel L m K k → ComplexMatrix2) : ℝ :=
  open Classical in
  if S.completedExtensionInfimum a₀ n r x Q X V <
      ENNReal.ofReal (S.extensionThreshold A₀ 𝔭₀ x)
  then 1 else 0
end ScaleLabel
end PeriodicLattice
end YangMills.Construction
