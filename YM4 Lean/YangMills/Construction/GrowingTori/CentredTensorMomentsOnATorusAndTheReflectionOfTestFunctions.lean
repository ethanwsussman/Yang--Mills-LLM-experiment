import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.Continuum.ReflectionOfTestFunctionsTensorsAndOrderZero
import YangMills.Construction.GrowingTori.TuplesOfFourSpaceAndTheirRestrictionToATorus
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.CentredTensorMoments
open TorusTransport TorusTransport.TestFunctionOrders
open SourcesAndGluing (ballR4)
structure MomentData extends PeriodicSpace.Params where
  K : ℕ+
  β : ℝ
  β_pos : 0 < β
namespace MomentData
variable (D : MomentData)
abbrev atCutoff : ReflectionPositivity.CutoffMirrors.MirrorData where
  L := D.L
  isAdmissible := D.isAdmissible
  K := D.K
  m := D.m
  coupling := D.β
  coupling_pos := D.β_pos
  dir := 0
abbrev BondField : Type := D.atCutoff.BondField
abbrev Plaquette : Type := PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)
def expectation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : D.BondField → E) : E :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.β F
def IsRadius (ρ : ℝ) : Prop := 0 < ρ ∧ ρ ≤ BallPeriodization.ballRadius D.toParams
end MomentData
def tupleTensor : {q : ℕ} → (Fin q → ComplexFun (Fin 4 → ℝ)) → OrderedTestFun q
  | 0, _ => (1 : ℂ)
  | _ + 1, f => prodTensor f
def realTupleTensor {q : ℕ} (X : BallTuples.FnTuple q) : OrderedTestFun q :=
  tupleTensor fun l x => ((X l x : ℝ) : ℂ)
namespace MomentData
variable (D : MomentData)
theorem gibbsFunctional_eq {q : ℕ} (u : Fin q → D.Torus → ℝ) :
    D.atCutoff.gibbsFunctional u =
      D.expectation fun U => ∏ l, D.atCutoff.centredObservable (u l) U :=
  rfl
def functionalOfPeriodized {q : ℕ} (X : BallTuples.FnTuple q) : ℝ :=
  D.atCutoff.gibbsFunctional (BallTuples.periodize D.toParams X)
def projectedBall (ρ : ℝ) : Set D.Torus := TorusMetric.torusProj D.side '' ballR4 ρ
abbrev PlaquetteInBall (ρ : ℝ) : Type := {p : D.Plaquette // p.barycenter ∈ D.projectedBall ρ}
variable {D}
def ballPoint {ρ : ℝ} (p : D.PlaquetteInBall ρ) : Fin 4 → ℝ := p.2.choose
theorem ballPoint_mem {ρ : ℝ} (p : D.PlaquetteInBall ρ) : ballPoint p ∈ ballR4 ρ :=
  p.2.choose_spec.1
theorem torusProj_ballPoint {ρ : ℝ} (p : D.PlaquetteInBall ρ) :
    TorusMetric.torusProj D.side (ballPoint p) = p.1.barycenter :=
  p.2.choose_spec.2
variable (D)
def centredPlaquetteCost (p : D.Plaquette) (U : D.BondField) : ℝ :=
  PeriodicLattice.plaquetteCost U p - D.expectation fun U' => PeriodicLattice.plaquetteCost U' p
def tensorObservable (ρ : ℝ) : {q : ℕ} → OrderedTestFun q → D.BondField → ℂ
  | 0, c, _ => c
  | q + 1, F, U => ∑ᶠ p : Fin (q + 1) → D.PlaquetteInBall ρ,
      F (fun l => ballPoint (p l)) * ∏ l, ((D.centredPlaquetteCost (p l).1 U : ℝ) : ℂ)
def centredTensorMoment (ρ : ℝ) {q : ℕ} (F : OrderedTestFun q) : ℂ :=
  D.expectation (D.tensorObservable ρ F)
end MomentData
def IsBallTensorSum (ρ : ℝ) : (q : ℕ) → OrderedTestFun q → Prop
  | 0, _ => True
  | q + 1, F => ∃ (n : ℕ) (f : Fin n → Fin (q + 1) → ComplexFun (Fin 4 → ℝ)),
      (∀ b l, TestFunctions.IsBoundedFun (f b l) ∧
        SourcesAndGluing.HasCompactSupportIn (f b l) (ballR4 ρ)) ∧
      (F : ComplexFun (Configuration (q + 1))) = ∑ b, prodTensor (f b)
def conjReflectTest (μ : Fin 4) (c : ℝ) :
    {q : ℕ} → OrderedTestFun q → OrderedTestFun q
  | 0, F₀ => conj (F₀ : ℂ)
  | _ + 1, F => fun x =>
      conj (F fun i => (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ)) (x i))
abbrev TestSeq (q₀ : ℕ) : Type := ∀ q : Fin (q₀ + 1), OrderedTestFun q
def conjReflectSeq (μ : Fin 4) (c : ℝ) {q₀ : ℕ} (F : TestSeq q₀) : TestSeq q₀ :=
  fun q => conjReflectTest μ c (F q)
theorem hyperplaneReflection_three_zero (x : Fin 4 → ℝ) :
    (BallPeriodization.hyperplaneReflection 3 0 : Equiv.Perm (Fin 4 → ℝ)) x = timeReflect x := by
  rw [BallPeriodization.hyperplaneReflection_apply]
  funext ν
  by_cases hν : ν = 3
  · subst hν
    simp [timeReflect, hyperplaneReflect, basisVec, PeriodicLattice.coordVec]
    ring
  · simp [timeReflect, hyperplaneReflect, basisVec, PeriodicLattice.coordVec, hν]
namespace MomentData
variable (D : MomentData)
def compPullback {R : Type*} (s : D.atCutoff.Symmetry) (𝔽 : D.BondField → R) :
    D.BondField → R :=
  fun U => 𝔽 (ReflectionPositivity.CutoffMirrors.MirrorData.Symmetry.pullback s U)
def IsReflectionSymmetry (μ : Fin 4) (c : ℝ) (s : D.atCutoff.Symmetry) : Prop :=
  s.toFun = BallPeriodization.torusMap D.toParams (BallPeriodization.hyperplaneReflection μ c)
def ReflectionIsSymmetry (μ : Fin 4) (c : ℝ) : Prop :=
  ∃ s : D.atCutoff.Symmetry, D.IsReflectionSymmetry μ c s
variable {D}
def ReflectionIsSymmetry.toSymmetry {μ : Fin 4} {c : ℝ}
    (h : D.ReflectionIsSymmetry μ c) : D.atCutoff.Symmetry :=
  h.choose
end MomentData
end YangMills.Construction.CentredTensorMoments
end
