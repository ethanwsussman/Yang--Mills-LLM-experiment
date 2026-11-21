import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.LatticeAtOneSpacingWithItsTorusAndCovering
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice GibbsAtFixedSpacing
namespace FixedSpacing
namespace Setup
variable (D : Setup)
def MeshAndAxisCounts : Prop :=
  D.mesh ≤ 1 ∧ D.side / D.mesh = 2 * (D.L : ℝ) ^ ((D.m : ℕ) + D.level) ∧
    (∃ n : ℤ, D.side / D.mesh = n) ∧ 4 ≤ D.side / D.mesh ∧
    ∀ (x : PeriodicLattice.Site D.L D.m (D.level : ℤ)) (i : Fin 4),
      ((PeriodicLattice.axisLine x i).ncard : ℝ) = D.side / D.mesh
def AgreesInsideOutside {A : Set (Link D.mesh)} (V : LinkVariables A) (W U : D.Fields) : Prop :=
  (∀ e : A, U e = V e) ∧ ∀ e ∈ D.links \ A, U e = W e
def FieldsFormProduct : Prop :=
  CompactSpace D.Fields ∧ TopologicalSpace.MetrizableSpace D.Fields ∧
    D.links.Countable ∧
    (∀ e : Link D.mesh, Xor (e ∈ D.links) (e.opposite ∈ D.links)) ∧
    IsHomeomorph (fun U : D.Fields => restrictField U D.links) ∧
    ∀ A : Set (Link D.mesh), A.Finite → IsLinkSet A →
      (∀ (V : LinkVariables A) (W : D.Fields),
        ∃! U : D.Fields, D.AgreesInsideOutside V W U) ∧
      ∃ g : LinkVariables A × D.Fields → D.Fields, Continuous g ∧
        ∀ (V : LinkVariables A) (W : D.Fields), D.AgreesInsideOutside V W (g (V, W))
def LocalFunctionsDense : Prop :=
  finiteLinkFunctions D.mesh ⊆ continuousFns D.mesh ∧
    (∃ S : Subalgebra ℂ (D.Fields → ℂ),
      (S : Set (D.Fields → ℂ)) = finiteLinkFunctions D.mesh) ∧
    (∀ F ∈ continuousFns D.mesh, ∀ ε : ℝ, 0 < ε →
      ∃ G ∈ finiteLinkFunctions D.mesh, ∀ U, ‖F U - G U‖ ≤ ε) ∧
    (∀ (μ : ℕ → BorelProb D.mesh) (μ₀ : BorelProb D.mesh),
      (∀ F ∈ finiteLinkFunctions D.mesh,
        Tendsto (fun n => (μ n).integral F) atTop (𝓝 (μ₀.integral F))) →
      BorelProb.TendstoWeak μ μ₀) ∧
    ∀ μ μ' : BorelProb D.mesh,
      (∀ F ∈ finiteLinkFunctions D.mesh, μ.integral F = μ'.integral F) → μ = μ'
def WeakTopologyFacts : Prop :=
  (∃ T : Set (D.Fields → ℂ), T.Countable ∧ T ⊆ continuousFns D.mesh ∧
    ∀ F ∈ continuousFns D.mesh, ∀ ε : ℝ, 0 < ε → ∃ G ∈ T, ∀ U, ‖F U - G U‖ ≤ ε) ∧
    CompactSpace (BorelProb D.mesh) ∧ TopologicalSpace.MetrizableSpace (BorelProb D.mesh) ∧
    (∀ (μ : ℕ → BorelProb D.mesh) (μ₀ : BorelProb D.mesh),
      Tendsto μ atTop (𝓝 μ₀) ↔ BorelProb.TendstoWeak μ μ₀) ∧
    (∀ μ : ℕ → BorelProb D.mesh, ∃ μ₀ : BorelProb D.mesh, BorelProb.IsSubseqWeakLimit μ μ₀) ∧
    ∀ (μ : ℕ → BorelProb D.mesh) (μ₀ : BorelProb D.mesh),
      (∀ N ∈ 𝓝 μ₀, {n : ℕ | 1 ≤ n ∧ μ n ∈ N}.Infinite) ↔ BorelProb.IsSubseqWeakLimit μ μ₀
def partialHaarIntegral (A : Set (Link D.mesh)) (Φ : LinkVariables A × D.Fields → ℂ)
    (W : D.Fields) : ℂ :=
  ∫ V, Φ (V, W) ∂LinkVariables.haarMeasure A
def PartialIntegralFacts : Prop :=
  (∀ B : Set (Link D.mesh), B.Finite → IsLinkSet B → ∀ F : D.Fields → ℂ,
    Continuous F → DependsOnlyOnLinks B F → FactorsThroughFinite B F) ∧
    ∀ A : Set (Link D.mesh), A.Finite → IsLinkSet A →
      ∀ Φ : LinkVariables A × D.Fields → ℂ, Continuous Φ →
        (∀ W : D.Fields, Integrable (fun V => Φ (V, W)) (LinkVariables.haarMeasure A)) ∧
        Continuous (D.partialHaarIntegral A Φ) ∧
        BddAbove (range fun z => ‖Φ z‖) ∧
        BddAbove (range fun W => ‖D.partialHaarIntegral A Φ W‖) ∧
        TestFunctions.uniformNorm (D.partialHaarIntegral A Φ) ≤ TestFunctions.uniformNorm Φ ∧
        ∀ B : Set (Link D.mesh), B.Finite → IsLinkSet B →
          (∀ (V : LinkVariables A) (W W' : D.Fields),
            restrictField W B = restrictField W' B → Φ (V, W) = Φ (V, W')) →
          FactorsThroughFinite B (D.partialHaarIntegral A Φ)
def FaceEnergyFacts : Prop :=
  (∀ p : ElementaryPlaquette D.mesh,
    FactorsThroughFinite (CutoffLattice.faceLinks p)
        (fun U : D.Fields => ((InfiniteLattice.faceEnergy U p : ℝ) : ℂ)) ∧
      ∀ U : D.Fields, 0 ≤ InfiniteLattice.faceEnergy U p ∧ InfiniteLattice.faceEnergy U p ≤ 2) ∧
    (∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : ElementaryPlaquette D.mesh | p.center ∈ S}.Finite) ∧
    (∀ f ∈ compactTestFunctions,
      (∃ (P : Finset (ElementaryPlaquette D.mesh)) (c : ElementaryPlaquette D.mesh → ℝ),
        ∀ U : D.Fields, smearedEnergy f U = ∑ p ∈ P, c p * InfiniteLattice.faceEnergy U p) ∧
      (fun U : D.Fields => ((smearedEnergy f U : ℝ) : ℂ)) ∈ finiteLinkFunctions D.mesh) ∧
    (∃ E : Submodule ℝ (AmbientSpace → ℝ), (E : Set (AmbientSpace → ℝ)) = compactTestFunctions) ∧
    ∀ f ∈ compactTestFunctions, ∀ g ∈ compactTestFunctions, ∀ (s t : ℝ) (U : D.Fields),
      smearedEnergy (s • f + t • g) U = s * smearedEnergy f U + t * smearedEnergy g U
end Setup
def BasicFacts : Prop :=
  ∀ D : Setup, D.MeshAndAxisCounts ∧ D.FieldsFormProduct ∧
    D.LocalFunctionsDense ∧ D.WeakTopologyFacts ∧
    D.PartialIntegralFacts ∧ D.FaceEnergyFacts
end FixedSpacing
end YangMills.Construction
