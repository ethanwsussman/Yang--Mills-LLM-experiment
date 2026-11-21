import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.WilsonSpecificationOnObservablesVersionsAndTrivialMeasures
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace MirrorGridsAllSides
abbrev GridSetup : Type := ChessboardTori.ChessboardSetup
def conjFun {X : Type*} (F : X → ℂ) : X → ℂ := fun x => conj (F x)
def transportFun {X E : Type*} (r : X ≃ X) (f : X → E) : X → E := f ∘ r.symm
namespace GridSetup
variable (G : GridSetup)
def withIndices (K' m' : ℕ+) : GridSetup :=
  ⟨⟨G.L, G.isAdmissible, K', m'⟩, G.β, G.beta_pos⟩
abbrev TorusPoint : Type := PeriodicLattice.Site G.L G.m ((G.K : ℕ) : ℤ)
abbrev TorusFace : Type := PeriodicLattice.Plaquette G.L G.m ((G.K : ℕ) : ℤ)
abbrev torusFields : Set (G.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.compactGaugeFields G.L G.m ((G.K : ℕ) : ℤ)
abbrev gibbs : Measure (G.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.wilsonGibbsMeasure G.L G.m G.K G.β
abbrev partition : ℝ := PeriodicLattice.partitionFunction G.L G.m G.K G.β
abbrev expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (G.PeriodicLink → Matrices.ComplexMatrix2) → E) : E :=
  PeriodicLattice.gibbsExpectation G.L G.m G.K G.β F
abbrev mirrors (μ : Fin 4) : ReflectionPositivity.CutoffMirrors.MirrorData :=
  ⟨G.toStandingParameters, G.β, G.beta_pos, μ⟩
def Descends (r' : AmbientSpace → AmbientSpace) (r : G.Torus → G.Torus) : Prop :=
  r ∘ G.proj = G.proj ∘ r'
theorem Descends.unique {G : GridSetup} {r' : AmbientSpace → AmbientSpace}
    {r₁ r₂ : G.Torus → G.Torus} (h₁ : G.Descends r' r₁) (h₂ : G.Descends r' r₂) : r₁ = r₂ := by
  funext y
  have hy : G.proj (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide G.L G.m) y) = y :=
    TestFunctions.torusProj_liftPoint y
  rw [← hy]
  exact (congrFun h₁ _).trans (congrFun h₂ _).symm
theorem descends_reflect (μ : Fin 4) (c : ℝ) :
    G.Descends ((G.mirrors μ).reflectVec c) ((G.mirrors μ).reflect c) :=
  (G.mirrors μ).induces_reflect c
abbrev TorusSymmetry : Type := PeriodicLattice.TorusLatticeSymmetry G.L G.m (G.K : ℕ)
variable {G} in
def TorusSymmetry.pullback (s : G.TorusSymmetry) (U : G.PeriodicLink → Matrices.ComplexMatrix2) :
    G.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun b => U (PeriodicLattice.TorusLatticeSymmetry.bondMap s b)
variable {G} in
def TorusSymmetry.precompose {E : Type*} (s : G.TorusSymmetry)
    (F : (G.PeriodicLink → Matrices.ComplexMatrix2) → E) :
    (G.PeriodicLink → Matrices.ComplexMatrix2) → E :=
  F ∘ TorusSymmetry.pullback s
def IsBoundedMeasurableInLinks (B' : Finset G.Link) (F : G.GaugeField → ℂ) : Prop :=
  ∃ Φ ∈ InfiniteLattice.boundedBorelSpace
      (InfiniteLattice.LinkVariables (B' : Set G.Link)),
    F = InfiniteLattice.observableOfLinks B' Φ
variable {G} in
theorem IsBoundedMeasurableInLinks.isBoundedObservable {B' : Finset G.Link}
    {F : G.GaugeField → ℂ} (h : G.IsBoundedMeasurableInLinks B' F) :
    InfiniteLattice.IsBoundedObservable F := by
  obtain ⟨Φ, hΦ, rfl⟩ := h
  exact InfiniteLattice.isBoundedObservable_observableOfLinks B' hΦ
def periodicGibbs : Set (Measure G.GaugeField) :=
  InfiniteLattice.periodicGibbsSet G.L G.K G.β
def integralOf (ν : Measure G.GaugeField) (A : G.GaugeField → ℂ) : ℂ := ∫ U, A U ∂ν
def splice {𝓛 : Finset G.Link}
    (h𝓛 : (𝓛 : Set G.Link) ⊆ InfiniteLattice.positiveLinkSet G.mesh)
    (u : 𝓛 → Matrices.ComplexMatrix2.specialUnitary) (ξ : G.GaugeField) : G.GaugeField :=
  InfiniteLattice.WilsonOperator.splice G.mesh_pos h𝓛 u ξ
def kernelIntegral {𝓛 : Finset G.Link}
    (h𝓛 : (𝓛 : Set G.Link) ⊆ InfiniteLattice.positiveLinkSet G.mesh)
    (A : G.GaugeField → ℂ) (ξ : G.GaugeField) : ℂ :=
  ∫ u, A (G.splice h𝓛 u ξ) ∂InfiniteLattice.wilsonSpecification G.β 𝓛 ξ
def IsPeriod (ν : Measure G.GaugeField) (p : ℕ) : Prop :=
  IsProbabilityMeasure ν ∧ 1 ≤ p ∧ ∀ v : InfiniteLattice.LatticePoint G.mesh,
    (∃ n : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = (p : ℝ) * G.mesh * (n μ : ℝ)) →
      InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)
theorem projLink_isPositivelyOriented {b : G.Link} (hb : b.IsPositivelyOriented) :
    (G.projLink b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  have h' : InfiniteLattice.projectPoint G.L G.m ((G.K : ℕ) : ℤ) (b.terminal - b.initial) =
      PeriodicLattice.unitStep G.L G.m ((G.K : ℕ) : ℤ) μ :=
    (congrArg (InfiniteLattice.projectPoint G.L G.m ((G.K : ℕ) : ℤ)) h).trans
      (InfiniteLattice.projectPoint_axisStep G.L G.m ((G.K : ℕ) : ℤ) μ)
  exact ⟨μ, (InfiniteLattice.projectPoint_sub G.L G.m ((G.K : ℕ) : ℤ)
    b.terminal b.initial).symm.trans h'⟩
end GridSetup
end MirrorGridsAllSides
end YangMills.Construction
end
