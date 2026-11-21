import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
open InfiniteLattice (GaugeField AmbientSpace smearedEnergy periodicGibbsSet liftedWilsonMeasure)
structure IsFlowDatum (ℓ : StepParameters) (Xi : ℝ) (K : ℕ) (β : ℝ) : Prop where
  two_le : 2 ≤ K
  le_coupling : ∀ j ≤ K, ℓ.y₁ ≤ flowCouplings ℓ β j
  coupling_le_top : flowCouplings ℓ β K ≤ Xi
def minimalCutoff (ℓ : StepParameters) (Xi d : ℝ) : ℕ :=
  max 2 (sInf {i : ℕ | 2 ^ 12 * (clusterRange (Xi + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i})
def lengthInSites (L K k : ℕ) (d : ℝ) : ℝ := d * (L : ℝ) ^ (K - k)
def IsSeparatedAt (ℓ : StepParameters) (β : ℝ) (K : ℕ) (d : ℝ) (k : ℕ) : Prop :=
  2 ^ 12 * (clusterRange (flowCouplings ℓ β k) : ℝ) ≤ lengthInSites ℓ.side K k d
open Classical in
def separationLevel (ℓ : StepParameters) (β : ℝ) (K : ℕ) (d : ℝ) : ℕ :=
  Nat.findGreatest (IsSeparatedAt ℓ β K d) K
def couplingAtSeparation (ℓ : StepParameters) (β : ℝ) (K : ℕ) (d : ℝ) : ℝ :=
  flowCouplings ℓ β (separationLevel ℓ β K d)
def boxRadius (x : ℝ) : ℕ := ⌈x ^ ((1 : ℝ) / 27)⌉₊
def averagingRadius (x : ℝ) : ℕ := boxRadius x / 16
def shiftSet (m : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m
def latticeShift (L K k : ℕ) (v : Fin 4 → ℤ) : AmbientSpace :=
  fun i => (v i : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K)
def translateBy (L K k : ℕ) (v : Fin 4 → ℤ) (f : AmbientSpace → ℝ) : AmbientSpace → ℝ :=
  fun x => f (x - latticeShift L K k v)
structure IsNormalizedTestPair (d vt : ℝ) (f h : AmbientSpace → ℝ) : Prop where
  mem_class : (f, h) ∈ TestFunctions.separatedPairsR4 d vt
  norm_left : TestFunctions.uniformNorm f = 1
  norm_right : TestFunctions.uniformNorm h = 1
abbrev LatticeConfig (L K : ℕ) : Type := GaugeField (PeriodicLattice.meshSize L (K : ℤ))
def smearedObservable (L K : ℕ) (f : AmbientSpace → ℝ) (U : LatticeConfig L K) : ℝ := smearedEnergy f U
def IsAdmissibleState (L K : ℕ) (β : ℝ) (μ : Measure (LatticeConfig L K)) : Prop :=
  μ ∈ periodicGibbsSet L K β ∨ ∃ e : ℕ, μ = liftedWilsonMeasure L e K β
def unitTorusMeasure (L K : ℕ) (β : ℝ) : Measure (LatticeConfig L K) := liftedWilsonMeasure L 0 K β
def unitTorusMean (L K : ℕ) (β : ℝ) (f : AmbientSpace → ℝ) : ℝ :=
  ∫ U, smearedObservable L K f U ∂unitTorusMeasure L K β
def unitTorusCovariance (L K : ℕ) (β : ℝ) (f h : AmbientSpace → ℝ) : ℝ :=
  cov[smearedObservable L K f, smearedObservable L K h; unitTorusMeasure L K β]
def HoldsForShapes (P : ParameterAssignment → ℝ → ResponseParameters → ℝ → ℝ → Prop) : Prop :=
  FreeEnergies.AtResponseParameters fun Tb Kr y => Kr.Admissible (Tb.stepParameters y) →
    ∀ Xi : ℝ, (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Xi →
      ∀ vt : ℝ, 0 < vt → vt ≤ 1 → P Tb y Kr Xi vt
variable {P Q : ParameterAssignment → ℝ → ResponseParameters → ℝ → ℝ → Prop}
theorem HoldsForShapes.and (h₁ : HoldsForShapes P) (h₂ : HoldsForShapes Q) :
    HoldsForShapes fun T y K X v => P T y K X v ∧ Q T y K X v := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  obtain ⟨y₁, G₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLL) T e₁ e₂ hD hS hH (hrt.trans (min_le_left _ _))
    (le_trans (le_max_left _ _) hC) Kr
  obtain ⟨y₂, G₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hLL) T e₁ e₂ hD hS hH (hrt.trans (min_le_right _ _))
    (le_trans (le_max_right _ _) hC) Kr
  exact ⟨max y₁ y₂, fun y hy hR hK Xi hXi vt hv hv1 =>
    ⟨G₁ y (le_trans (le_max_left _ _) hy) hR hK Xi hXi vt hv hv1,
      G₂ y (le_trans (le_max_right _ _) hy) hR hK Xi hXi vt hv hv1⟩⟩
theorem HoldsForShapes.of_holdsOnParameters {R : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies R) :
    HoldsForShapes fun T y _ _ _ => R T y := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, H⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  obtain ⟨y₀, G⟩ := H L hL hLL T e₁ e₂ hD hS hH hrt hC
  exact ⟨y₀, fun y hy hR _ Xi _ vt _ _ => G y hy hR.returns_at hR.wilson_expansion⟩
theorem HoldsForShapes.of_response {R : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (h : FreeEnergies.AtResponseParameters R) :
    HoldsForShapes fun T y K _ _ => R T K y := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, H⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  obtain ⟨y₀, G⟩ := H L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  exact ⟨y₀, fun y hy hR _ Xi _ vt _ _ => G y hy hR⟩
theorem HoldsForShapes.mono (h : HoldsForShapes P) (hPQ : ∀ T y K X v, P T y K X v → Q T y K X v) :
    HoldsForShapes Q := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, H⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  obtain ⟨y₀, G⟩ := H L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  exact ⟨y₀, fun y hy hR hK Xi hXi vt hv hv1 => hPQ _ _ _ _ _ (G y hy hR hK Xi hXi vt hv hv1)⟩
theorem HoldsForShapes.params : HoldsForShapes fun T y Kr Xi vt => T.Admissible ∧ T.floorMin ≤ y ∧
    FreeEnergies.ExpansionHolds (T.stepParameters y) ∧ Kr.Admissible (T.stepParameters y) ∧
    (T.stepParameters y).y₁ + 2 * (T.stepParameters y).B ≤ Xi ∧ 0 < vt ∧ vt ≤ 1 := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL hLL T e₁ e₂ hD hS hH hrt hC Kr
  exact ⟨T.floorMin, fun y hy hR hK Xi hXi vt hv hv1 => ⟨hD, hy, hR, hK, hXi, hv, hv1⟩⟩
end YangMills.Construction.StateLaws
end
