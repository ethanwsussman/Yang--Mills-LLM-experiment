import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.RealSystemsAndClassesOfSources
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace TorusBound
structure Setup extends Conventions.StandingParameters where
  cubeExp : ℕ
  β : ℝ
  β_pos : 0 < β
def plusPart (t : ℝ) : ℝ := max t 0
def logPos (t : ℝ) : ℝ := max (Real.log t) 0
namespace Setup
variable (D : Setup)
abbrev cubeSide : ℕ := D.L ^ D.cubeExp
abbrev LinkConfig : Type := PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2
abbrev haarConfig : Measure D.LinkConfig :=
  PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
abbrev gibbs : Measure D.LinkConfig := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β
abbrev expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : D.LinkConfig → E) : E :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.β F
abbrev sharpNorm {E : Type*} [NormedAddCommGroup E] (f : D.Torus → E) : ℝ :=
  TestFunctions.sharpNormTorus (D.cubeSide : ℝ) f
def IsWeight (w : D.Torus → ℂ) : Prop := TestFunctions.IsBoundedFun w
abbrev obs {E : Type*} [AddCommMonoid E] [Module ℝ E] (w : D.Torus → E)
    (U : D.LinkConfig) : E :=
  PeriodicLattice.smearedObservable (j := ((D.K : ℕ) : ℤ)) w U
def partitionFun (w : D.Torus → ℂ) : ℂ :=
  ∫ U : D.LinkConfig,
    Complex.exp (-(D.β : ℂ) * (PeriodicLattice.wilsonAction U : ℂ) + D.obs w U) ∂D.haarConfig
abbrev IsRealFamily {n : ℕ} (f : Fin n → D.Torus → ℝ) : Prop :=
  PeriodicLattice.IsRealLipschitzTuple f
abbrev smear {n : ℕ} (z : Fin n → ℂ) (f : Fin n → D.Torus → ℝ) : D.Torus → ℂ :=
  PeriodicLattice.complexSource f z
abbrev disc (ϱ : ℝ) {n : ℕ} (f : Fin n → D.Torus → ℝ) : Set (Fin n → ℂ) :=
  PeriodicLattice.sourceDisc (D.cubeSide : ℝ) ϱ f
abbrev sources (ϱ : ℝ) : Set (D.Torus → ℂ) :=
  PeriodicLattice.flatSourceClass D.L D.m (D.cubeSide : ℝ) ϱ
theorem mem_sources_iff (ϱ : ℝ) (v : D.Torus → ℂ) :
    v ∈ D.sources ϱ ↔ ∃ (n : ℕ) (f : Fin n → D.Torus → ℝ) (z : Fin n → ℂ),
      D.IsRealFamily f ∧ z ∈ D.disc ϱ f ∧ v = D.smear z f :=
  Iff.rfl
def truncatedCorrelation {n : ℕ} (f : Fin n → D.Torus → ℝ) : ℂ :=
  PeriodicLattice.gibbsCumulant D.L D.m D.K D.β fun i => D.obs (f i)
def ball (y₀ : D.Torus) (R : ℝ) : Set D.Torus :=
  {y | TorusMetric.torusEuclidNorm (y - y₀) ≤ R}
def IsBallOfRadius (R : ℝ) (B : Set D.Torus) : Prop := ∃ y₀, B = D.ball y₀ R
end Setup
end TorusBound
end YangMills.Construction
end
