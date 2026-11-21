import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.MixtureJets
variable {n : ℕ}
abbrev MixedBond (L n : ℕ) : Type := TorusFields.TorusBond (n * L) ⊕ TorusFields.TorusBond n
def mixedBondSite (L : ℕ) : MixedBond L n → TorusFields.TorusSite n :=
  Sum.elim (fun b => TorusLumps.parentBlock L b.1) fun c => c.1
def mixedBondDiam (L : ℕ) {k : ℕ} (c : Fin k → MixedBond L n) : ℕ :=
  Finset.univ.sup fun i : Fin k => Finset.univ.sup fun j : Fin k =>
    TorusFields.supDist (mixedBondSite L (c i)) (mixedBondSite L (c j))
open Classical in
def fineCoordPerturb (L : ℕ) {k : ℕ} (c : Fin k → MixedBond L n) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (σ : Fin k → ℝ) : TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions :=
  fun b => ∑ i, if c i = Sum.inl b then σ i • X i else 0
open Classical in
def coarseFieldPerturb (L : ℕ) {k : ℕ} (c : Fin k → MixedBond L n) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (σ : Fin k → ℝ) : TorusFields.TorusField n :=
  fun x i => BlockAverages.expUnit (∑ j, if c j = Sum.inr (x, i) then σ j • X j else 0)
open Classical in
def bondIndicator {m : ℕ} (b : TorusFields.TorusBond m) : TorusFields.TorusBond m → ℝ :=
  fun b' => if b' = b then 1 else 0
def mixtureIteratedDeriv [NeZero n] (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L] {k : ℕ} (c : Fin k → MixedBond L n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) : ℝ :=
  iteratedFDeriv ℝ k (fun σ : Fin k → ℝ =>
    TwoLevelMixtures.interpChartEnergy a L t θ (fineCoordPerturb L c X σ) (coarseFieldPerturb L c X σ)) 0
      fun i => Pi.single i 1
structure FlatFieldJetBounds (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L] (Cm : ℕ → ℝ) (t n : ℕ)
    [NeZero n] (θ : ℝ) : Prop where
  first_deriv_eq_zero : ∀ b ∈ StepCosts.chartBonds T.L n, ∀ X : BlockAverages.imaginaryQuaternions,
    mixtureIteratedDeriv T.a T.L t θ ![Sum.inl b] ![X] = 0
  second_deriv_eq : ∀ b ∈ StepCosts.chartBonds T.L n, ∀ b' ∈ StepCosts.chartBonds T.L n,
    ∀ X X' : BlockAverages.imaginaryQuaternions,
    mixtureIteratedDeriv T.a T.L t θ ![Sum.inl b, Sum.inl b'] ![X, X'] =
      inner ℝ (X : Quaternion ℝ) (X' : Quaternion ℝ) *
        TwoLevelMixtures.interpForm T.a T.L t θ (bondIndicator b) (bondIndicator b')
  coercive : ∀ f : TorusFields.TorusBond (n * T.L) → ℝ, TwoLevelMixtures.VanishesOnTrees T.L f →
    T.lam * ∑ b, f b ^ 2 ≤ TwoLevelMixtures.interpForm T.a T.L t θ f f
  kernel_decay : ∀ (k : ℕ) (c : Fin k → MixedBond T.L n) (X : Fin k → BlockAverages.imaginaryQuaternions),
    2 ≤ k → BlockAverages.AreUnitVectors X →
    |mixtureIteratedDeriv T.a T.L t θ c X| ≤ Cm k * Real.exp (-(8 * T.chainParams.δ₁ * mixedBondDiam T.L c))
def flatFieldJetBoundsStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ [NeZero T.L], ∃ Cm : ℕ → ℝ,
    ∀ (t n : ℕ) [NeZero n] (θ : ℝ), 64 ≤ n → 0 ≤ θ → θ ≤ 1 → FlatFieldJetBounds T Cm t n θ
end YangMills.Construction.MixtureJets
end
