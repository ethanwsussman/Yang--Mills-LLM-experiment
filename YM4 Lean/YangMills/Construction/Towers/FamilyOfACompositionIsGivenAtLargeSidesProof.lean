import YangMills.Construction.Towers.CompositionWithAStepIsAFunctionalProof
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Tower.StepComposition
open PeriodicOperators.Tempered Tower Matrices
variable {L : ℕ}
theorem continuous_transportTotal {X Y : Type} (e : X ≃ Y) :
    Continuous (transportTotal e : (X → ComplexMatrix2) → Y → ComplexMatrix2) :=
  continuous_pi fun y => continuous_apply (e.symm y)
theorem mapsTo_transportTotal_cast_depth (m : ℕ) {d d' : ℤ} (h : d = d') :
    MapsTo (transportTotal (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h)))
      (PeriodicLattice.compactGaugeFields L m d) (PeriodicLattice.compactGaugeFields L m d') := by
  subst h
  exact fun _ hU => hU
theorem mapsTo_topEdgeEquiv (m k : ℕ) :
    MapsTo (transportTotal (topEdgeEquiv L m k)) (fieldSpace L m k k) (fieldSpace L m 0 0) :=
  mapsTo_transportTotal_cast_depth (d := PeriodicLattice.levelDepth k k)
    (d' := PeriodicLattice.levelDepth 0 0) m (by simp [PeriodicLattice.levelDepth])
theorem transportTotal_trans {X Y Z : Type} (e : X ≃ Y) (e' : Y ≃ Z) (f : X → ComplexMatrix2) :
    transportTotal (e.trans e') f = transportTotal e' (transportTotal e f) := rfl
theorem mapsTo_transportTotal_cast_exponent {m m' : ℕ} (h : m = m') :
    MapsTo (transportTotal (Equiv.cast (congrArg (UnitEdge L) h)))
      (fieldSpace L m 0 0) (fieldSpace L m' 0 0) := by
  subst h
  exact fun _ hU => hU
theorem mapsTo_stepEdgeEquiv (hScale : ScalingNearTrivialField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hLpos : 0 < L) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    MapsTo (transportTotal (_root_.YangMills.Construction.PeriodicOperators.Tempered.stepEdgeEquiv hLpos n i)) (fieldSpace L n (i + 1) i)
      (fieldSpace L (n + 1) 0 0) := by
  intro V hV
  have h₀ : ScalingPreservesFieldsAndForms (m := n) hLpos (Nat.le_succ i) i :=
    (hScale L n (i + 1) i i i hLpos (Nat.le_succ i) hL hn le_rfl le_rfl).1
  rw [_root_.YangMills.Construction.PeriodicOperators.Tempered.stepEdgeEquiv, transportTotal_trans, transportTotal_trans]
  exact mapsTo_transportTotal_cast_exponent (L := L) (scaledExponent_succ_self n i)
    (mapsTo_topEdgeEquiv (L := L) (scaledExponent n (i + 1) i) i (h₀.1.mapsTo hV))
theorem mem_nhdsWithin_of_isOpenNhdOfOne
    (hProd : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {n k a : ℕ} (hn : 0 < n) (ha : a ≤ k) {U : Set (Edge L n k a → ComplexMatrix2)}
    (h : IsOpenNhdOfOne U) :
    U ∈ 𝓝[fieldSpace L n k a] trivialField L n k a := by apply _root_.YangMills.Construction.Tower.StepComposition.mem_nhdsWithin_trivialField_of_isOpenNhdOfOne <;> assumption
end Tower.StepComposition
open Tower.StepComposition PeriodicOperators.Tempered Tower Matrices in
theorem PeriodicOperators.Tempered.compStepEventuallyDefined_holds
    (hBranch : CriticalBranchExists)
    (hAnalytic : AnalyticMapsAlongCurves)
    (hProd : BondSetFields.ProductStructureHolds)
    (hScale : ScalingNearTrivialField) :
    CompStepEventuallyDefined := by
  intro L hL F S D hG i
  have hLpos : 0 < L := Nat.lt_of_lt_of_le (by norm_num) hL.2
  have hLone : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ L from hLpos)
  have hpos : ∀ s ∈ sideSet L, 0 < s := by
    rintro s ⟨m, -, rfl⟩
    have : (0 : ℝ) < L := by exact_mod_cast hLpos
    simp only [PeriodicLattice.torusSide]
    positivity
  have hmul : ∀ s ∈ sideSet L, (L : ℝ) * s ∈ sideSet L ∧ s ≤ (L : ℝ) * s := by
    intro s hs
    refine ⟨?_, le_mul_of_one_le_left (hpos s hs).le hLone⟩
    obtain ⟨m, -, rfl⟩ := hs
    exact ⟨m + 1, Nat.succ_pos m, (torusSide_succ L m).symm⟩
  have hsucc : EventuallyForSides L (fun n => n + 1 ∈ S) := by
    obtain ⟨s₀, hs₀, hlarge⟩ := hG.eventually
    refine ⟨s₀, hs₀, fun s hs hle n hn e => ?_⟩
    have hLs := hmul s hs
    refine hlarge ((L : ℝ) * s) hLs.1 (hle.trans hLs.2) (n + 1) (Nat.succ_pos n) ?_
    rw [torusSide_succ, e]
  have hstep : EventuallyForSides L (· ∈ stepIndexSet S) := by
    obtain ⟨s₀, hs₀, hlarge⟩ := hsucc
    exact ⟨s₀, hs₀, fun s hs hle n hn e => ⟨hn, hlarge s hs hle n hn e⟩⟩
  refine ⟨hmul, hsucc, hstep, ?_⟩
  intro n hn P hP
  have hnpos : 0 < n := hn.1
  have hcrit : (chosenCriticalBranch L n (i + 1)).IsCritical :=
    Classical.epsilon_spec (hBranch L n (i + 1) hL hnpos)
  obtain ⟨U, hU, hAn⟩ := hcrit.analytic_prolong i (Nat.lt_succ_self i)
  have hcont : ContinuousOn (chosenProlong L n (i + 1) i) U :=
    ((hAnalytic L n (i + 1) (i + 1) i hL hnpos le_rfl (Nat.le_succ i)).1 U _ hAn).1
  have htriv : chosenProlong L n (i + 1) i (trivialField L n (i + 1) (i + 1)) =
      trivialField L n (i + 1) i :=
    hcrit.prolong_trivial i (Nat.lt_succ_self i)
  have hUmem := mem_nhdsWithin_of_isOpenNhdOfOne hProd hL hnpos le_rfl hU
  have hmaps : MapsTo (scaledProlong hLpos n i) U (fieldSpace L (n + 1) 0 0) :=
    fun W hW => mapsTo_stepEdgeEquiv hScale hL hLpos hnpos i (hAn.2.1 hW)
  have hcw : ContinuousWithinAt (scaledProlong hLpos n i) U
      (trivialField L n (i + 1) (i + 1)) :=
    (continuous_transportTotal (_root_.YangMills.Construction.PeriodicOperators.Tempered.stepEdgeEquiv hLpos n i)).continuousAt.comp_continuousWithinAt
      (hcont _ hU.2)
  have hval : scaledProlong hLpos n i (trivialField L n (i + 1) (i + 1)) =
      fun _ => (1 : ComplexMatrix2) := by
    simp only [scaledProlong, htriv]
    rfl
  have htend : Tendsto (scaledProlong hLpos n i) (𝓝[fieldSpace L n (i + 1) (i + 1)]
      (fun _ => (1 : ComplexMatrix2))) (𝓝[fieldSpace L (n + 1) 0 0] (fun _ => (1 : ComplexMatrix2))) := by
    have h₁ := hcw.tendsto_nhdsWithin hmaps
    rw [hval] at h₁
    exact h₁.mono_left (nhdsWithin_le_of_mem hUmem)
  have hD : EventuallyNearIdentity (fieldSpace L (n + 1) 0 0) (· ∈ D (n + 1)) :=
    hG.nhdsIdentity (n + 1) hn.2 (Nat.succ_pos n)
  have hD' := htend.eventually hD
  have hP' : ∀ᶠ W in 𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)), W ∈ P := hP
  change ∀ᶠ W in 𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)), W ∈ _
  filter_upwards [self_mem_nhdsWithin, hP', hD'] with W h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩
end YangMills.Construction
end
