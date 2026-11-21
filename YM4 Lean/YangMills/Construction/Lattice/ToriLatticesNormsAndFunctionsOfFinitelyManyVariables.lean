import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open TorusMetric
variable {L m : ℕ} {j : ℤ}
def liftsOf (y : FourTorus L m) : Set (Fin 4 → ℝ) := torusProj (torusSide L m) ⁻¹' {y}
def translateByVector (y : FourTorus L m) (v : Fin 4 → ℝ) : FourTorus L m :=
  y + torusProj (torusSide L m) v
def torusL1Dist (y y' : FourTorus L m) : ℝ := torusL1Norm (y - y')
def IsMetricOpen (O : Set (FourTorus L m)) : Prop :=
  ∀ y ∈ O, ∃ r : ℝ, 0 < r ∧ {y' : FourTorus L m | torusEuclidNorm (y' - y) < r} ⊆ O
@[reducible] def metricTopology (L m : ℕ) : TopologicalSpace (FourTorus L m) where
  IsOpen := IsMetricOpen
  isOpen_univ := fun _ _ => ⟨1, one_pos, subset_univ _⟩
  isOpen_inter := by
    intro U V hU hV y hy
    obtain ⟨r, hr, hsub⟩ := hU y hy.1
    obtain ⟨r', hr', hsub'⟩ := hV y hy.2
    refine ⟨min r r', lt_min hr hr', fun y' hy' => ?_⟩
    have hlt : torusEuclidNorm (y' - y) < min r r' := hy'
    exact ⟨hsub (lt_of_lt_of_le hlt (min_le_left _ _)),
      hsub' (lt_of_lt_of_le hlt (min_le_right _ _))⟩
  isOpen_sUnion := by
    intro S hS y ⟨U, hU, hy⟩
    obtain ⟨r, hr, hsub⟩ := hS U hU y hy
    exact ⟨r, hr, hsub.trans (subset_sUnion_of_mem hU)⟩
def metricSupport {E : Type*} [Zero E] (f : FourTorus L m → E) : Set (FourTorus L m) :=
  @closure _ (metricTopology L m) {y | f y ≠ 0}
def euclidSupport {E : Type*} [Zero E] (f : (Fin 4 → ℝ) → E) : Set (Fin 4 → ℝ) :=
  closure {x | f x ≠ 0}
def CompactGaugeField (L m : ℕ) (j : ℤ) : Type := ↥(compactGaugeFields L m j)
namespace CompactGaugeField
def linkValue (U : CompactGaugeField L m j) (b : Bond L m j) :
    Matrices.ComplexMatrix2.specialUnitary :=
  ⟨U.1 b, U.2.1 b (mem_univ b)⟩
instance instTopologicalSpace : TopologicalSpace (CompactGaugeField L m j) :=
  ⨅ b : Bond L m j, TopologicalSpace.induced (fun U => linkValue U b) inferInstance
instance instMeasurableSpace : MeasurableSpace (CompactGaugeField L m j) := borel _
instance instBorelSpace : BorelSpace (CompactGaugeField L m j) := ⟨rfl⟩
end CompactGaugeField
section Norms
variable {E : Type*} [NormedAddCommGroup E]
def torusSupNorm (f : FourTorus L m → E) : ℝ≥0∞ := ⨆ y, ENNReal.ofReal ‖f y‖
def euclidSupNorm (f : (Fin 4 → ℝ) → E) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal ‖f x‖
def torusLipConst (f : FourTorus L m → E) : ℝ≥0∞ :=
  ⨆ (y : FourTorus L m) (y' : FourTorus L m) (_ : y ≠ y'),
    ENNReal.ofReal (‖f y - f y'‖ / torusEuclidNorm (y - y'))
end Norms
end PeriodicLattice
namespace SeveralComplexVariables
variable {I : Type*}
def basisVector (q : I) : I → ℂ :=
  open Classical in fun q' => if q' = q then 1 else 0
def IsHolomorphicOnOpen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (W : Set (I → ℂ))
    (h : (I → ℂ) → F) : Prop :=
  IsOpen W ∧ ContinuousOn h W ∧ ∀ c ∈ W, ∀ q : I, ∀ᶠ ζ in 𝓝 (0 : ℂ),
    DifferentiableAt ℂ (fun t : ℂ => h (c + t • basisVector q)) ζ
def partialDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (q : I)
    (h : (I → ℂ) → F) (c : I → ℂ) : F :=
  deriv (fun ζ : ℂ => h (c + ζ • basisVector q)) 0
def IsEntire {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (h : (I → ℂ) → F) : Prop :=
  IsHolomorphicOnOpen univ h
def polydisc (c₀ : I → ℂ) (δ : ℝ) : Set (I → ℂ) := {c | ∀ q, ‖c q - c₀ q‖ < δ}
def disc (u₀ : ℂ) (r : ℝ) : Set ℂ := {u | ‖u - u₀‖ < r}
def logSeries (u : ℂ) : ℂ := -∑' k : ℕ, ((k : ℂ) + 1)⁻¹ * (1 - u) ^ (k + 1)
end SeveralComplexVariables
end YangMills.Construction
