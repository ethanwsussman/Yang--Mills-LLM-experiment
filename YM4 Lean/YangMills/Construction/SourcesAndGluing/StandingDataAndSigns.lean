import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction
namespace SourcesAndGluing
structure GluingSetup extends Conventions.StandingParameters where
  β : ℝ
  beta_pos : 0 < β
  cubeExp : ℕ
namespace GluingSetup
variable (S : GluingSetup)
def mesh : ℝ := PeriodicLattice.meshSize S.L (S.K : ℕ)
def sideSet : Set ℝ := PeriodicLattice.torusSides S.L
abbrev periodicLattice : AddSubgroup S.Torus := PeriodicLattice.sublattice S.L S.m (S.K : ℕ)
abbrev PeriodicLink : Type := PeriodicLattice.Bond S.L S.m ((S.K : ℕ) : ℤ)
abbrev gaugeFields : Set (S.PeriodicLink → Matrices.ComplexMatrix2) :=
  {U | PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U}
def action (U : S.PeriodicLink → Matrices.ComplexMatrix2) : ℝ := PeriodicLattice.wilsonAction U
def gibbsMeasure : Measure (S.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.wilsonGibbsMeasure S.L S.m S.K S.β
def expectation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (S.PeriodicLink → Matrices.ComplexMatrix2) → E) : E :=
  PeriodicLattice.gibbsExpectation S.L S.m S.K S.β F
def smeared {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : S.Torus → E)
    (U : S.PeriodicLink → Matrices.ComplexMatrix2) : E :=
  PeriodicLattice.smearedObservable f U
def withCutoffAndSide (K' m' : ℕ+) : GluingSetup :=
  ⟨⟨S.L, S.isAdmissible, K', m'⟩, S.β, S.beta_pos, S.cubeExp⟩
theorem side_withCutoffAndSide_mem_sideSet (K' m' : ℕ+) :
    (S.withCutoffAndSide K' m').side ∈ S.sideSet :=
  ⟨m', m'.pos, rfl⟩
def M : ℝ := (S.L : ℝ) ^ S.cubeExp
theorem one_le_M : 1 ≤ S.M := by
  have hL := S.isAdmissible.2
  exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ S.L))
def sharpNormR4 {E : Type*} [NormedAddCommGroup E] (f : (Fin 4 → ℝ) → E) : ℝ :=
  TestFunctions.sharpNormR4 S.M f
def sharpNormTorus {E : Type*} [NormedAddCommGroup E] {ℓ' : ℝ}
    (f : TorusMetric.Torus4 ℓ' → E) : ℝ :=
  TestFunctions.sharpNormTorus S.M f
abbrev gridPoints : AddSubgroup (Fin 4 → ℝ) := InfiniteLattice.latticeSubgroup S.mesh
abbrev GridField : Type := InfiniteLattice.GaugeField S.mesh
def proj : (Fin 4 → ℝ) →+ S.Torus where
  toFun := TorusMetric.torusProj (PeriodicLattice.torusSide S.L S.m)
  map_zero' := by
    funext μ
    simp [TorusMetric.torusProj]
  map_add' x y := by
    funext μ
    simp [TorusMetric.torusProj]
theorem proj_surjective : Function.Surjective S.proj :=
  TestFunctions.torusProj_surjective _
def translateBy (u : S.Torus) (z : Fin 4 → ℝ) : S.Torus := u + S.proj z
section Functions
variable {𝕜 : Type*} [RCLike 𝕜]
def suppR4 (f : (Fin 4 → ℝ) → 𝕜) : Set (Fin 4 → ℝ) := closure {x | f x ≠ 0}
def suppTorus (f : S.Torus → 𝕜) : Set S.Torus :=
  MetricNotions.closureWrt (PeriodicLattice.torusEuclidDist S.L S.m) {u | f u ≠ 0}
def IsC1 (f : S.Torus → 𝕜) : Prop := TestFunctions.IsC1R4 (f ∘ S.proj)
def IsSmooth (f : S.Torus → 𝕜) : Prop := ContDiff ℝ ∞ (f ∘ S.proj)
def partialDeriv (μ : Fin 4) (f : S.Torus → 𝕜) : S.Torus → 𝕜 :=
  TestFunctions.partialDerivTorus μ f
theorem partialDeriv_comp_proj (μ : Fin 4) (f : S.Torus → 𝕜) :
    S.partialDeriv μ f ∘ S.proj =
      TestFunctions.partialDerivR4 μ (f ∘ S.proj) := by
  funext x
  have hshift : ∀ t : ℝ, f (S.proj x +
        TorusMetric.torusProj (PeriodicLattice.torusSide S.L S.m) (t • Pi.single μ (1 : ℝ))) =
      (f ∘ S.proj) (x + t • Pi.single μ (1 : ℝ)) := fun t => by
    rw [Function.comp_apply, S.proj.map_add]
    rfl
  simp only [Function.comp_apply, partialDeriv, TestFunctions.partialDerivTorus,
    TestFunctions.partialDerivR4, hshift]
theorem eq_partialDeriv_of_comp (μ : Fin 4) (f g : S.Torus → 𝕜)
    (hg : g ∘ S.proj = TestFunctions.partialDerivR4 μ (f ∘ S.proj)) :
    g = S.partialDeriv μ f :=
  S.proj_surjective.injective_comp_right
    (hg.trans (S.partialDeriv_comp_proj μ f).symm)
def c1Norm (f : S.Torus → 𝕜) : ℝ :=
  max (TestFunctions.uniformNorm f) (⨆ μ : Fin 4, TestFunctions.uniformNorm (S.partialDeriv μ f))
end Functions
def IsTorusIsometry (r : S.Torus → S.Torus) : Prop :=
  Function.Bijective r ∧ PeriodicLattice.IsTorusIsometry r
end GluingSetup
def IsR4Isometry (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  Function.Bijective r ∧ InfiniteLattice.IsSpaceIsometry r
def euclidNorm (x : Fin 4 → ℝ) : ℝ := TorusMetric.euclidNormVec x
def stdBasis (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
end SourcesAndGluing
end YangMills.Construction
end
