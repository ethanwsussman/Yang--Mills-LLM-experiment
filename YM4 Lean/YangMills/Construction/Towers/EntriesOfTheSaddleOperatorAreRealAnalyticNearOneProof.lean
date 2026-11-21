import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
import YangMills.Construction.Towers.GradientOfTheFixedFunctionOnAFibre
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranch
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.SecondDerivativeOfARealAnalyticFunctionIsBilinear
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctions
import YangMills.Construction.Towers.TaylorCoefficientsInTheLeftChartAreRealAnalytic
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
set_option autoImplicit false

namespace YangMills.Construction.Tower
def SaddleFormAnalyticNearIdentity : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ i : ℕ, i + 1 ≤ k →
    ∃ 𝒰 : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      ∃ Q : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) →
          edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k i →ₗ[ℝ] ℝ,
        (∀ W ∈ 𝒰, ∀ B B' : edgeFormSpace L n k i, Q W B B' = Q W B' B) ∧
        (∀ W ∈ 𝒰, ∀ B : LinearMap.ker (constraintDifferential L n k i W),
          Q W B.1 B.1 = fibreHessianForm L n k i W B) ∧
        (∀ B B' : edgeFormSpace L n k i, IsAnalyticFieldFunction 𝒰 fun W => Q W B B') ∧
        ∀ (B : edgeFormSpace L n k i) (C : edgeFormSpace L n k (i + 1)),
          IsAnalyticFieldFunction 𝒰 fun W =>
            (edgeFormPairing (C : Edge L n k (i + 1) → Matrices.ComplexMatrix2)
              (constraintDifferential L n k i W B : Edge L n k (i + 1) → Matrices.ComplexMatrix2)).re
end YangMills.Construction.Tower

namespace YangMills.Construction
open Set Filter Matrices Tower
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace Tower.SaddleAnalytic
def reTraceForm (X : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℝ] ℝ where
  toFun Y := (ComplexMatrix2.halfTrace (X * Y)).re
  map_add' Y Y' := by
    simp [ComplexMatrix2.halfTrace, mul_add, Matrix.trace_add]
  map_smul' c Y := by
    simp [ComplexMatrix2.halfTrace, Matrix.trace_smul, ComplexMatrix2.fullTrace]
    ring
def reTracePairing {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ComplexMatrix2) :
    (ι → ComplexMatrix2) →ₗ[ℝ] ℝ :=
  ∑ i, reTraceForm (f i) ∘ₗ LinearMap.proj i
theorem reTracePairing_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (f A : ι → ComplexMatrix2) :
    reTracePairing f A = ∑ i, reTraceForm (f i) (A i) := by
  simp [reTracePairing, LinearMap.sum_apply]
theorem re_traceFinsumPairing {ι : Type*} [Fintype ι] [DecidableEq ι] (f A : ι → ComplexMatrix2) :
    (traceFinsumPairing f A).re = reTracePairing f A := by
  rw [reTracePairing_apply, traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
  rfl
theorem exists_sum_inner_mul_inner {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) :
    ∃ (d : ℕ) (e : Fin d → V), ∀ x y : V,
      c.inner x y = ∑ a, c.inner x (e a) * c.inner (e a) y := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  refine ⟨_, stdOrthonormalBasis ℝ V, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℝ V).sum_inner_mul_inner x y).symm
theorem exists_bilinear_leftSecondDeriv {L m k i : ℕ} {F : (Edge L m k i → ComplexMatrix2) → ℝ}
    {V : Edge L m k i → ComplexMatrix2}
    (h : (∀ B ∈ edgeFormSpace L m k i, ∀ B' ∈ edgeFormSpace L m k i,
          leftSecondDeriv F V B B' = leftSecondDeriv F V B' B) ∧
        ∀ B₁ ∈ edgeFormSpace L m k i, ∀ B₂ ∈ edgeFormSpace L m k i, ∀ B' ∈ edgeFormSpace L m k i,
          ∀ c : ℝ,
          leftSecondDeriv F V (c • B₁ + B₂) B' =
            c * leftSecondDeriv F V B₁ B' + leftSecondDeriv F V B₂ B') :
    ∃ β : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k i →ₗ[ℝ] ℝ,
      ∀ B B' : edgeFormSpace L m k i, β B B' = leftSecondDeriv F V B B' := by
  obtain ⟨hs, hl⟩ := h
  have hadd : ∀ B₁ B₂ B' : edgeFormSpace L m k i,
      leftSecondDeriv F V ((B₁ + B₂ : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) B' =
        leftSecondDeriv F V B₁ B' + leftSecondDeriv F V B₂ B' := by
    intro B₁ B₂ B'
    have := hl B₁ B₁.2 B₂ B₂.2 B' B'.2 1
    rw [one_smul, one_mul] at this
    exact this
  have hzero : ∀ B' : edgeFormSpace L m k i,
      leftSecondDeriv F V (0 : Edge L m k i → ComplexMatrix2) B' = 0 := by
    intro B'
    have h0 := hl 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) B' B'.2 1
    simp only [smul_zero, add_zero, one_mul] at h0
    linarith
  have hsmul : ∀ (c : ℝ) (B B' : edgeFormSpace L m k i),
      leftSecondDeriv F V ((c • B : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) B' =
        c * leftSecondDeriv F V B B' := by
    intro c B B'
    have := hl B B.2 0 (Submodule.zero_mem _) B' B'.2 c
    rw [add_zero, hzero, add_zero] at this
    exact this
  refine ⟨LinearMap.mk₂ ℝ (fun B B' : edgeFormSpace L m k i => leftSecondDeriv F V B B') hadd
    (fun c B B' => by simpa using hsmul c B B') (fun B B₁ B₂ => ?_) (fun c B B' => ?_),
    fun B B' => rfl⟩
  · rw [hs _ B.2 _ (B₁ + B₂).2, hadd, hs _ B₁.2 _ B.2, hs _ B₂.2 _ B.2]
  · rw [hs _ B.2 _ (c • B').2, hsmul, hs _ B'.2 _ B.2]
    rfl
section Sets
variable {L m k j : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < m) (hj : j ≤ k)
    (𝒰 : Set (Edge L m k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L m k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L m k j) 𝒰 := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem exists_isOpenNhdOfOne_of_eventually (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < m) (hj : j ≤ k)
    {𝒰₀ : Set (Edge L m k j → ComplexMatrix2)} {P : (Edge L m k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L m k j) P) :
    ∃ 𝒰 : Set (Edge L m k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by
  have hop := isOpenFieldSet_iff (m := m) (k := k) (j := j) hE hL hn hj
  obtain ⟨-, O₀, hO₀, e₀⟩ := (hop 𝒰₀).1 h.1
  have hne' : {W | P W} ∈ 𝓝[fieldSpace L m k j] (trivialField L m k j) := hne
  obtain ⟨O, hO, h1O, hOs⟩ := mem_nhdsWithin.1 hne'
  have h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup ((O ∩ O₀) ∩ fieldSpace L m k j) :=
    (hop _).2 ⟨inter_subset_right, O ∩ O₀, hO.inter hO₀, rfl⟩
  have hsub : (O ∩ O₀) ∩ fieldSpace L m k j ⊆ 𝒰₀ := fun V hV => by
    rw [e₀]
    exact ⟨hV.1.2, hV.2⟩
  have h2 : trivialField L m k j ∈ O₀ ∩ fieldSpace L m k j := by
    rw [← e₀]
    exact h.2
  exact ⟨_, ⟨h𝒰, ⟨⟨h1O, h2.1⟩, h2.2⟩⟩, hsub, fun V hV => hOs ⟨hV.1.1, hV.2⟩⟩
theorem tendsto_prolong {i : ℕ} (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < m)
    {b : CriticalBranchData L m k} (hb : b.IsCritical) (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1))
      (𝓝[fieldSpace L m k i] trivialField L m k i) := by
  obtain ⟨𝒰, hU, hR⟩ := hb.analytic_prolong i hi
  have hnear : 𝒰 ∈ 𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1) :=
    (hP L m k (i + 1) hL hn hi).2.1 _ hU.1 _ hU.2
  have hc := ((hA L m k (i + 1) i hL hn hi hi.le).1 _ _ hR).1 _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.mem_of_superset hnear fun W hW => hR.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem hnear)
  rwa [hb.prolong_trivial i hi] at h
end Sets
section Gradient
variable {L m k j : ℕ}
theorem edgeFormPairing_leftGradient (hA : AnalyticMapsAlongCurves)
    (hP : diffAtZeroPathsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < m) (hj : j ≤ k)
    [Finite (PositiveEdge L m k j)] {c : InnerProductSpace.Core ℝ (edgeFormSpace L m k j)}
    (hc : ∀ B B' : edgeFormSpace L m k j, edgeFormPairing (B : Edge L m k j → ComplexMatrix2)
      (B' : Edge L m k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    {𝒰 : Set (Edge L m k j → ComplexMatrix2)} {S : (Edge L m k j → ComplexMatrix2) → ℝ}
    (hS : IsAnalyticFieldFunction 𝒰 S) {W : Edge L m k j → ComplexMatrix2}
    (hW : W ∈ 𝒰) {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k j) :
    edgeFormPairing (leftGradient (fieldSpace L m k j) (fun V => (S V : ℂ)) W) B =
      ((leftDeriv S W B : ℝ) : ℂ) := by
  obtain ⟨X, hX, hder⟩ := (hA L m k j j hL hn hj hj).2 𝒰 S hS W hW
  have hWc : W ∈ fieldSpace L m k j := hS.1.1 hW
  have hline : ∀ B ∈ edgeFormSpace L m k j,
      HasDerivAt (fun t : ℝ => S (PeriodicLattice.expTwist ((t : ℂ) • B) W))
        (edgeFormPairing X B).re 0 := by
    intro B hB
    obtain ⟨h₁, h₂, h₃⟩ := (hP L m k j hL hn hj).2.2 W hWc B hB
    have h := hder _ h₁ h₂
    rwa [h₃] at h
  have hreal : ∀ B ∈ edgeFormSpace L m k j,
      edgeFormPairing X B = (((edgeFormPairing X B).re : ℝ) : ℂ) := by
    intro B hB
    have h := hc ⟨X, hX⟩ ⟨B, hB⟩
    change edgeFormPairing X B = _ at h
    rw [h, Complex.ofReal_re]
  have hIs : IsLeftGradient (fieldSpace L m k j) (fun V => (S V : ℂ)) W X := by
    refine ⟨⟨fun b hb => (hX.1 b hb).2, hX.2⟩, fun _ => hX, fun B hB _ => ?_⟩
    rw [hreal B hB]
    exact (hline B hB).ofReal_comp.deriv.symm
  have hspec := Classical.epsilon_spec (⟨X, hIs⟩ : ∃ X, IsLeftGradient (fieldSpace L m k j)
    (fun V => (S V : ℂ)) W X)
  refine (hspec.2.2 B hB (Set.toFinite _)).trans ?_
  rw [← hIs.2.2 B hB (Set.toFinite _), hreal B hB]
  congr 1
  exact (hline B hB).deriv.symm
end Gradient
end Tower.SaddleAnalytic
open Tower.SaddleAnalytic in
theorem Tower.saddleFormAnalyticNearIdentity_holds
    (hT : LeftChartStepExpansion)
    (hH : FibreHessianViaQuadraticExpansion)
    (hGrad : GaugeFixedGradientOnFibre)
    (hFix : ChosenBranchIsCritical)
    (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement)
    (hRA : AnalyticMapsAlongCurves)
    (hE : BondSetFields.ProductStructureHolds)
    (hTay : LeftChartTaylorCoefficientsAnalytic)
    (hBil : LeftSecondDerivBilinear)
    (hAlg : AnalyticFieldFunctionsClosed) :
    SaddleFormAnalyticNearIdentity := by
  classical
  intro L m k hL hn i hi
  have hik : i < k := hi
  obtain ⟨hb, hUall⟩ := hFix L m k hL hn
  have hU := hUall i hik
  obtain ⟨hfin, hfd, -, core, hcore⟩ := hS L m k (i + 1) hL hn hi
  haveI := hfd
  letI : Fintype (PositiveEdge L m k (i + 1)) := Fintype.ofFinite _
  obtain ⟨d, e, hpars⟩ := exists_sum_inner_mul_inner core
  set p := chosenProlong L m k i with hp_def
  set F := chosenGaugeFixedEnergy L m k i with hF_def
  set S := (chosenCriticalBranch L m k).energy (i + 1) with hS_def
  set M := smoothingStep L m k i with hM_def
  set 𝒰₂ := chosenFibreNhd L m k i with h𝒰₂_def
  obtain ⟨𝒰₁, h𝒰₁, hp⟩ := hb.analytic_prolong i hik
  obtain ⟨𝒰₃, h𝒰₃, hS₃⟩ := hb.analytic_energy (i + 1) hi
  obtain ⟨hconst, hsp, hmono, hcongr, hcomp⟩ := hAlg L m k (i + 1) i hL hn hi hik.le
  have h𝒰₂ := hU.isOpenNhd
  have h𝒰₀ : IsOpenNhdOfOne (𝒰₁ ∩ p ⁻¹' 𝒰₂) := by
    refine ⟨(hcomp _ _ _ _ hp ((hAlg L m k i i hL hn hik.le hik.le).1 𝒰₂ 0 h𝒰₂.1)).1, h𝒰₁.2, ?_⟩
    change (chosenCriticalBranch L m k).prolong i _ ∈ 𝒰₂
    rw [hb.prolong_trivial i hik]
    exact h𝒰₂.2
  have hnear₃ : 𝒰₃ ∈ 𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1) :=
    (hP L m k (i + 1) hL hn hi).2.1 _ h𝒰₃.1 _ h𝒰₃.2
  have hlim := tendsto_prolong hP hRA hL hn hb hik
  have htv := hT L m k i hL hn hi
  have hH' := hH L m k hL hn i hi
  have hG' := hGrad L m k hL hn i hi
  obtain ⟨𝒰, h𝒰, hsub, hPW⟩ := exists_isOpenNhdOfOne_of_eventually
    (P := fun W => W ∈ 𝒰₃ ∧
      (StepLogAnalytic (p W) ∧ StepDifferentialIsLinearTerm (p W) ∧
        StepHasQuadraticExpansion (p W)) ∧
      ((∃ q : EdgeFormBilinear L m k i, IsQuadraticExpansion (p W) q) ∧
        ∀ q : EdgeFormBilinear L m k i, IsQuadraticExpansion (p W) q →
        ∀ B : LinearMap.ker (constraintDifferential L m k i W),
          fibreHessianForm L m k i W B = leftSecondDeriv F (p W) B.1.1 B.1.1 -
            (traceFinsumPairing (restrictToPositiveEdges
              ((chosenCriticalBranch L m k).energyGradient (i + 1) W))
              (q B.1 B.1)).re) ∧
      ∃ g : edgeFormSpace L m k (i + 1),
        (g : Edge L m k (i + 1) → ComplexMatrix2) =
          (chosenCriticalBranch L m k).energyGradient (i + 1) W)
    hE hL hn hi h𝒰₀ (by
      unfold EventuallyNearIdentity at htv hH' hG' ⊢
      filter_upwards [hnear₃, hlim.eventually htv, hH', hG'] with W h₁ h₂ h₃ h₄
      obtain ⟨g, hg, -⟩ := h₄
      exact ⟨h₁, h₂, h₃, g, hg⟩)
  have hop := h𝒰.1
  have hβ : ∀ W, ∃ β : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k i →ₗ[ℝ] ℝ, W ∈ 𝒰 →
      ∀ B B' : edgeFormSpace L m k i, β B B' = leftSecondDeriv F (p W) B B' := by
    intro W
    by_cases hW : W ∈ 𝒰
    · obtain ⟨β, h⟩ := exists_bilinear_leftSecondDeriv
        (hBil L m k i hL hn hik.le 𝒰₂ F hU.analytic_gaugeFixedEnergy (p W) (hsub hW).2)
      exact ⟨β, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hW⟩
  choose β hβ using hβ
  have hq : ∀ W, ∃ q : EdgeFormBilinear L m k i, W ∈ 𝒰 → IsQuadraticExpansion (p W) q := by
    intro W
    by_cases hW : W ∈ 𝒰
    · obtain ⟨q, h⟩ := (hPW W hW).2.2.1.1
      exact ⟨q, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hW⟩
  choose q hq using hq
  have hsum : ∀ {ι : Type} (s : Finset ι) (G : ι → (Edge L m k (i + 1) → ComplexMatrix2) → ℝ),
      (∀ a ∈ s, IsAnalyticFieldFunction 𝒰 (G a)) →
      IsAnalyticFieldFunction 𝒰 fun W => ∑ a ∈ s, G a W := by
    intro ι s G h
    induction s using Finset.induction_on with
    | empty => simpa using hconst 𝒰 0 hop
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hsp _ _ _ (h a (Finset.mem_insert_self a s))
        (ih fun b hb' => h b (Finset.mem_insert_of_mem hb'))).1
  have hscale : ∀ (c : ℝ) (G : (Edge L m k (i + 1) → ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction 𝒰 G → IsAnalyticFieldFunction 𝒰 fun W => c * G W :=
    fun c G h => (hsp _ _ _ (hconst 𝒰 c hop) h).2
  have hsub' : ∀ G₁ G₂ : (Edge L m k (i + 1) → ComplexMatrix2) → ℝ, IsAnalyticFieldFunction 𝒰 G₁ →
      IsAnalyticFieldFunction 𝒰 G₂ → IsAnalyticFieldFunction 𝒰 fun W => G₁ W - G₂ W := by
    intro G₁ G₂ h₁ h₂
    refine hcongr _ _ _ (hsp _ _ _ h₁ (hscale (-1) _ h₂)).1 fun W _ => ?_
    change G₁ W + -1 * G₂ W = G₁ W - G₂ W
    ring
  have hpull : ∀ G : (Edge L m k i → ComplexMatrix2) → ℝ, IsAnalyticFieldFunction 𝒰₂ G →
      IsAnalyticFieldFunction 𝒰 fun W => G (p W) := fun G hG =>
    hmono _ _ _ (hcomp _ _ _ _ hp hG) hop hsub
  obtain ⟨hTayF, hTayM⟩ := hTay L m k i (i + 1) hL hn hik.le hi
  have hfirst : ∀ (B : edgeFormSpace L m k i) (c : PositiveEdge L m k (i + 1))
      (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun W => φ (deriv (lineLogarithm M (p W) B c) 0) :=
    fun B c φ => hpull _ (hTayM 𝒰₂ M hU.analytic_smoothing B B.2 c φ).1
  have hsecond : ∀ (B : edgeFormSpace L m k i) (c : PositiveEdge L m k (i + 1))
      (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun W => φ (iteratedDeriv 2 (lineLogarithm M (p W) B c) 0) :=
    fun B c φ => hpull _ (hTayM 𝒰₂ M hU.analytic_smoothing B B.2 c φ).2
  have hdiag : ∀ W ∈ 𝒰, ∀ (B : edgeFormSpace L m k i) (c : PositiveEdge L m k (i + 1)),
      q W B B c = iteratedDeriv 2 (lineLogarithm M (p W) B c) 0 := by
    intro W hW B c
    have h := (((hPW W hW).2.1.2.2).2 (q W) (hq W hW)).1 B c
    have e₁ : taylorCoeffAtZero 2 (stepLog (p W) c) (B : Edge L m k i → ComplexMatrix2) =
        (2 : ℝ)⁻¹ • iteratedDeriv 2 (lineLogarithm M (p W) B c) 0 := by
      unfold taylorCoeffAtZero
      norm_num [Nat.factorial]
      rfl
    rw [e₁, one_div] at h
    exact smul_right_injective _ (inv_ne_zero (two_ne_zero' ℝ)) h
  have hoff : ∀ W ∈ 𝒰, ∀ (B B' : edgeFormSpace L m k i) (c : PositiveEdge L m k (i + 1)),
      q W B B' c = (1 / 2 : ℝ) • (iteratedDeriv 2 (lineLogarithm M (p W)
          ((B + B' : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) c) 0 -
        iteratedDeriv 2 (lineLogarithm M (p W) B c) 0 -
        iteratedDeriv 2 (lineLogarithm M (p W) B' c) 0) := by
    intro W hW B B' c
    rw [← hdiag W hW, ← hdiag W hW, ← hdiag W hW]
    have hs := (hq W hW).1 B' B
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hs]
    module
  have hpq : ∀ (f : PositiveEdge L m k (i + 1) → ComplexMatrix2) (B B' : edgeFormSpace L m k i),
      IsAnalyticFieldFunction 𝒰 fun W => reTracePairing f (q W B B') := by
    intro f B B'
    have h := hsum Finset.univ (fun (c : PositiveEdge L m k (i + 1)) W =>
      (1 / 2 : ℝ) * (reTraceForm (f c) (iteratedDeriv 2
          (lineLogarithm M (p W) ((B + B' : edgeFormSpace L m k i) :
            Edge L m k i → ComplexMatrix2) c) 0) -
        reTraceForm (f c) (iteratedDeriv 2 (lineLogarithm M (p W) B c) 0) -
        reTraceForm (f c) (iteratedDeriv 2 (lineLogarithm M (p W) B' c) 0)))
      fun c _ => hscale _ _ (hsub' _ _ (hsub' _ _ (hsecond _ c _) (hsecond _ c _)) (hsecond _ c _))
    refine hcongr _ _ _ h fun W hW => ?_
    simp only [reTracePairing_apply, hoff W hW, map_smul, map_sub, smul_eq_mul]
  have hgrad : ∀ W ∈ 𝒰, ∀ B B' : edgeFormSpace L m k i,
      reTracePairing (restrictToPositiveEdges
          ((chosenCriticalBranch L m k).energyGradient (i + 1) W)) (q W B B') =
        ∑ a, leftDeriv S W (e a : Edge L m k (i + 1) → ComplexMatrix2) *
          reTracePairing (restrictToPositiveEdges (e a : Edge L m k (i + 1) → ComplexMatrix2))
            (q W B B') := by
    intro W hW B B'
    obtain ⟨hW₃, ⟨-, -, hQ⟩, -, g, hg⟩ := hPW W hW
    have hform := ((hQ.2 (q W) (hq W hW)).2.2 B B')
    set A : edgeFormSpace L m k (i + 1) := ⟨edgeFormOfPositiveValues (q W B B'), hform⟩ with hA
    have hAp : restrictToPositiveEdges (A : Edge L m k (i + 1) → ComplexMatrix2) = q W B B' := by
      funext c
      change edgeFormOfPositiveValues (q W B B') c.1 = _
      simp only [edgeFormOfPositiveValues, dif_pos c.2]
    have hpair : ∀ x : edgeFormSpace L m k (i + 1),
        reTracePairing (restrictToPositiveEdges (x : Edge L m k (i + 1) → ComplexMatrix2))
            (q W B B') =
          core.inner x A := by
      intro x
      rw [← re_traceFinsumPairing, ← hAp]
      have := hcore x A
      change (edgeFormPairing _ _).re = _
      rw [this, Complex.ofReal_re]
    rw [← hg, hpair, hpars]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hpair]
    congr 1
    have h₁ := hcore g (e a)
    rw [hg] at h₁
    have h₂ := edgeFormPairing_leftGradient hRA hP hL hn hi hcore hS₃ hW₃ (e a).2
    have h₃ : ((core.inner g (e a) : ℝ) : ℂ) = ((leftDeriv S W (e a) : ℝ) : ℂ) :=
      h₁.symm.trans h₂
    exact_mod_cast h₃
  refine ⟨𝒰, h𝒰, fun W => β W - (q W).compr₂ (reTracePairing (restrictToPositiveEdges
    ((chosenCriticalBranch L m k).energyGradient (i + 1) W))), ?_, ?_, ?_, ?_⟩
  · intro W hW B B'
    simp only [LinearMap.sub_apply, LinearMap.compr₂_apply]
    rw [hβ W hW, hβ W hW, (hq W hW).1 B B',
      (hBil L m k i hL hn hik.le 𝒰₂ F hU.analytic_gaugeFixedEnergy (p W) (hsub hW).2).1
        B B.2 B' B'.2]
  · intro W hW B
    simp only [LinearMap.sub_apply, LinearMap.compr₂_apply]
    rw [hβ W hW, (hPW W hW).2.2.1.2 (q W) (hq W hW) B, re_traceFinsumPairing]
  · intro B B'
    have h₁ : IsAnalyticFieldFunction 𝒰 fun W => leftSecondDeriv F (p W) B B' :=
      hpull _ ((hTayF 𝒰₂ F hU.analytic_gaugeFixedEnergy B B.2).2 B' B'.2)
    have h₂ : IsAnalyticFieldFunction 𝒰 fun W =>
        ∑ a, leftDeriv S W (e a : Edge L m k (i + 1) → ComplexMatrix2) *
          reTracePairing (restrictToPositiveEdges (e a : Edge L m k (i + 1) → ComplexMatrix2))
            (q W B B') :=
      hsum Finset.univ _ fun a _ => (hsp _ _ _ (hmono _ _ _
        ((hTay L m k (i + 1) (i + 1) hL hn hi hi).1 𝒰₃ S hS₃ (e a) (e a).2).1 hop
        fun W hW => (hPW W hW).1) (hpq _ B B')).2
    refine hcongr _ _ _ (hsub' _ _ h₁ h₂) fun W hW => ?_
    simp only [LinearMap.sub_apply, LinearMap.compr₂_apply]
    rw [hβ W hW, hgrad W hW]
  · intro B C
    have h := hsum Finset.univ (fun (c : PositiveEdge L m k (i + 1)) W =>
      reTraceForm (restrictToPositiveEdges (C : Edge L m k (i + 1) → ComplexMatrix2) c)
        (deriv (lineLogarithm M (p W) B c) 0)) fun c _ => hfirst B c _
    refine hcongr _ _ _ h fun W hW => ?_
    obtain ⟨-, ⟨-, hDiff, -⟩, -⟩ := hPW W hW
    have hspec : ∀ A : edgeFormSpace L m k i,
        (constraintDifferential L m k i W A : Edge L m k (i + 1) → ComplexMatrix2) =
          leftDifferential (smoothingStep L m k i) (chosenProlong L m k i W) A :=
      Classical.epsilon_spec hDiff.2.1
    unfold edgeFormPairing
    rw [re_traceFinsumPairing, reTracePairing_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    have h₁ := (hDiff.2.2 B c).2
    change _ = (constraintDifferential L m k i W B : Edge L m k (i + 1) → ComplexMatrix2) c.1
    rw [hspec B]
    exact h₁
end
end YangMills.Construction
