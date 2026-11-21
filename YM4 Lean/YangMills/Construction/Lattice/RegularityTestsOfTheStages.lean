import YangMills.Construction.Lattice.ClassesAndDropOuts
import YangMills.Construction.Lattice.SmallFieldDomainOfAStep
import YangMills.Construction.Lattice.StageBackgrounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set ParameterChoice
namespace PeriodicLattice.CubesOfStep
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
def shellScale (k i : ℕ) : ℝ :=
  Thresholds.epsThreshold c.A₀ c.𝔭₀ x i *
    ((c.L : ℝ) ^ ((k : ℤ) - (i : ℤ)) * finestMeshInLevelUnits c.L k) ^ 2
def flatPower (e : ℤ) : ℝ := (c.LFlat : ℝ) ^ (2 * e.toNat)
def stageBackground (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
    (X : Set (FourTorus c.L m)) (V : ∀ i : ℕ, BondAtLevel c.L m K i → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  S.stageGluedBackground c.εv (Nat.log c.L c.M₁) c.r x Q n X V
def StageBackgroundExists (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
    (X : Set (FourTorus c.L m)) (V : ∀ i : ℕ, BondAtLevel c.L m K i → Matrices.ComplexMatrix2) :
    Prop :=
  HasGluedCriticalOrbit c.εv K k (Nat.log c.L c.M₁) k (S.stagedDomain c.r x Q n) X V
def nestShell (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (i : ℕ) :
    Set (FourTorus c.L m) :=
  open Classical in
  if (i : ℤ) = lowerLevel c.L c.r x k then S.trimmedRegion c.r x Q (i + 1) ∩ S.domainSeq i
  else S.trimmedRegion c.r x Q (i + 1) \ S.trimmedRegion c.r x Q i
def topLevelInterior (S : LabelAtLevel c m K x k) (X : Set (FourTorus c.L m)) :
    Set (FourTorus c.L m) :=
  {y | y ∈ S.domainSeq k ∧
    ENNReal.ofReal (nestedCubeSide c.L c.r x (Nat.log c.L c.M) k k) ≤
      supDistInLevelUnits K k {y} Xᶜ}
def outerShell (S : LabelAtLevel c m K x k) (X : Set (FourTorus c.L m)) (l : ℕ) :
    Set (FourTorus c.L m) :=
  if l = k then topLevelInterior c x S X else S.domainSeq l \ nextMember k S.domainSeq l
def StageBoundsHold (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
    (X : Set (FourTorus c.L m)) (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  let h : ℤ := lowerLevel c.L c.r x k
  let k₀ : ℤ := Thresholds.delayLevel c.L c.r x k
  let j : ℕ := ScaleLabel.collarStepLevel c.L c.r x k n
  let i₀ : ℤ := min k₀ ((j : ℤ) - 1)
  let Ω : ℕ → Set (FourTorus c.L m) := S.domainSeq
  let half : ℝ := 1 - c.βs / 2
  let top : ℝ := if j < k then 1 else 3
  let cl : ℕ → ℝ := fun l => if (j : ℤ) - 1 ≤ (l : ℤ) then top else 1
  let near : Set (FourTorus c.L m) → ℝ → Prop := fun R a => PlaquettesNearIdentity c K U (X ∩ R) a
  (n = 0 → near (Ω h.toNat \ nextMember k Ω h.toNat) (half * shellScale c x k h.toNat)) ∧
  (1 ≤ n →
    (∀ i : ℕ, h ≤ (i : ℤ) → i + 1 ≤ j →
      near (nestShell c x S Q i)
        ((1 - c.βs * (1 - (2 : ℝ) ^ (-((j : ℤ) - (i : ℤ) + 1)))) *
          flatPower c ((i : ℤ) - k₀ - 1) * shellScale c x k i)) ∧
    near ((Ω (i₀ + 1).toNat)ᶜ \ S.trimmedRegion c.r x Q j)
      (half * flatPower c ((j : ℤ) - i₀ - 1) * shellScale c x k j) ∧
    ∀ l : ℕ, i₀ + 1 ≤ (l : ℤ) → l ≤ j →
      near (outerShell c x S X l)
        (cl l * half * flatPower c ((j : ℤ) - (l : ℤ) - 1) * shellScale c x k j))
def stageIndicator (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
    (X : Set (FourTorus c.L m)) (V : ∀ i : ℕ, BondAtLevel c.L m K i → Matrices.ComplexMatrix2) :
    ℝ :=
  open Classical in
  if StageBoundsHold c x S Q n X (stageBackground c x S Q n X V) then 1 else 0
def stageIndicatorOfExists (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m)))
    (n : ℕ) (X : Set (FourTorus c.L m))
    (V : ∀ i : ℕ, BondAtLevel c.L m K i → Matrices.ComplexMatrix2) : ℝ :=
  open Classical in
  if StageBackgroundExists c x S Q n X V ∧
      StageBoundsHold c x S Q n X (stageBackground c x S Q n X V)
  then 1 else 0
end PeriodicLattice.CubesOfStep
end YangMills.Construction
