import YangMills.Construction.RunningCouplingSlope.OtherConstraintAtNoNoise
import YangMills.Construction.RunningCouplingSlope.PlainCovariantStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.PlainIteratesNearOne
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheForms
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace QuietPointGaugeShift
open Tower Matrices
variable {L n k j : ℕ}
private theorem eq_of_eq_on_positive {i : ℕ}
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f g : Edge L n k i → ComplexMatrix2} (hf : ∀ b, f b.opposite = -f b)
    (hg : ∀ b, g b.opposite = -g b)
    (h : ∀ c, c.IsPositivelyOriented → f c = g c) : f = g := by
  funext b
  rcases hX b with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact h b hp
  · have h1 := h _ hp
    rw [hf, hg] at h1
    exact neg_injective h1
abbrev _root_.YangMills.SharedProofs.p26709 := @eq_of_eq_on_positive
private theorem extendOddly_opposite {i : ℕ}
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k i → ComplexMatrix2) (b : Edge L n k i) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.extendOddly_opposite <;> assumption
private theorem extendOddly_of_positive {i : ℕ} (f : Edge L n k i → ComplexMatrix2)
    (b : Edge L n k i) (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
private theorem covDiff_add {i : ℕ} (W : Edge L n k i → ComplexMatrix2)
    (l l' : Vertex L n k i → ComplexMatrix2) :
    covDiff W (l + l') = covDiff W l + covDiff W l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
private theorem covDiff_congr {i : ℕ}
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {W W' : Edge L n k i → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → W b = W' b) (l : Vertex L n k i → ComplexMatrix2) :
    covDiff W l = covDiff W' l := by
  classical
  funext b
  simp only [covDiff, extendOddly]
  split_ifs with h1
  · rw [h b h1]
  · have h2 : b.opposite.IsPositivelyOriented := by
      rcases hX b with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact absurd h3 h1
      · exact h3
    rw [h _ h2]
private theorem covDiff_zero {i : ℕ} (W : Edge L n k i → ComplexMatrix2) :
    covDiff W (0 : Vertex L n k i → ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_zero <;> assumption
private theorem conjugateBy_one (X : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 X = X := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
end QuietPointGaugeShift
open QuietPointGaugeShift Tower Matrices in
theorem shiftedGaugeMapAtQuietPoint_holds (hS : MeanCovariantStepOnForms)
    (hP : MeanDerivOnForms.Claim) (hI : MeanIteratesTendToOne)
    (hLin : Tower.StepMapsComplexLinear.Claim) :
    ShiftedGaugeMapAtQuietPoint := by
  intro L hL k n hk hn
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hX : ∀ i, ∀ b : Edge L n k i, i ≤ k →
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i b hi =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hev : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), ∀ i ∈ Finset.range k,
      (∀ B ∈ complexEdgeForms L n k i, meanCovariantStep (meanIterate U i) B ∈
        complexEdgeForms L n k (i + 1)) ∧
      (∀ B ∈ complexEdgeForms L n k i, ∀ B' ∈ complexEdgeForms L n k i, ∀ w : ℂ,
        meanCovariantStep (meanIterate U i) (w • B + B') =
          w • meanCovariantStep (meanIterate U i) B + meanCovariantStep (meanIterate U i) B') ∧
      (∀ B ∈ edgeFormSpace L n k i, meanCovariantStep (meanIterate U i) B ∈
        edgeFormSpace L n k (i + 1)) ∧
      (∀ B ∈ edgeFormSpace L n k i, ∀ y,
        contourLogDrift (meanIterate U i) B y ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) →
        ∀ y, adjointCubeAverage (meanIterate U i) l y ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        meanCovariantStep (meanIterate U i) (covDiff (meanIterate U i) l) =
          covDiff (normalizedMean (meanIterate U i))
            (adjointCubeAverage (meanIterate U i) l)) ∧
      (∀ B ∈ edgeFormSpace L n k i, holLeftDifferential normalizedMean (meanIterate U i) B ∈
        edgeFormSpace L n k (i + 1)) ∧
      (∀ (B : Edge L n k i → ComplexMatrix2) (c : Edge L n k (i + 1)), c.IsPositivelyOriented →
        leftDifferential normalizedMean (meanIterate U i) B c =
          holLeftDifferential normalizedMean (meanIterate U i) B c) ∧
      ∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        covDiff (meanIterate U i) l ∈ complexEdgeForms L n k i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    have hT := hI L hL k n hn i hik.le
    filter_upwards [hT.eventually (hS L hL n k i hn hk hik), hT.eventually (hP L hL n k i hn hik)]
      with U f g
    obtain ⟨f₁, f₂, f₃, f₄, f₅, -, -, f₈⟩ := f
    obtain ⟨g₁, -, -, -, g₅, g₆, -⟩ := g
    exact ⟨f₁, f₂, f₃, f₄, f₅, f₈, g₅, g₆, fun l hl =>
      ((hLin L hL n k i hn hik _ g₁).2.2.1 l hl).1⟩
  unfold EventuallyNearIdentity
  filter_upwards [hev] with U hU
  set X := quietPoint U with hXdef
  have hone : ∀ (i : Fin k) c, X.noise i c = 1 := fun _ _ => rfl
  have key : ∀ (ξ : LevelForms L n k) (j : ℕ), j ≤ k →
      tangentTransport X ξ j ∈ edgeFormSpace L n k j ∧
        (∀ y, chainDrift X ξ j y ∈ ComplexMatrix2.hermitianTraceless) ∧
        tangentForms U ξ j = tangentTransport X ξ j +
          covDiff (meanIterate U j) (chainDrift X ξ j) := by
    intro ξ j
    induction j with
    | zero =>
      intro _
      refine ⟨ξ.1.2, fun y => ComplexMatrix2.hermitianTraceless.zero_mem, ?_⟩
      simp only [tangentForms, tangentTransport, chainDrift]
      have : covDiff (meanIterate U 0) (0 : Vertex L n k 0 → ComplexMatrix2) = 0 :=
        covDiff_zero _
      simp only [this, add_zero]
    | succ j ih =>
      intro hj
      have hlt : j < k := by omega
      obtain ⟨i₁, i₂, i₃⟩ := ih hlt.le
      obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉⟩ := hU j (Finset.mem_range.2 hlt)
      set V := meanIterate U j with hV
      set m := tangentTransport X ξ j with hm
      set σ := chainDrift X ξ j with hσ
      have hXj : ∀ b : Edge L n k (j + 1),
          Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
        hX (j + 1) b hj
      set ν : Edge L n k (j + 1) → ComplexMatrix2 :=
        (ξ.2 ⟨j, hlt⟩ : Edge L n k (j + 1) → ComplexMatrix2) with hν
      have hνf : ν ∈ edgeFormSpace L n k (j + 1) := (ξ.2 ⟨j, hlt⟩).2
      have hmov : tangentTransport X ξ (j + 1) = holLeftDifferential normalizedMean V m + ν := by
        have hfm := (edgeFormSpace L n k (j + 1)).add_mem (s₇ m i₁) hνf
        refine eq_of_eq_on_positive hXj (fun b => ?_) hfm.2 fun c hc => ?_
        · simp only [tangentTransport, dif_pos hlt]
          exact extendOddly_opposite hXj _ b
        · simp only [tangentTransport, dif_pos hlt]
          rw [extendOddly_of_positive _ _ hc, dif_pos hc, hone, conjugateBy_one]
          simp only [Pi.add_apply]
          rw [show levelField X j = V from rfl, s₈ m c hc]
      have hdrift : chainDrift X ξ (j + 1) = adjointCubeAverage V σ + contourLogDrift V m := rfl
      have hcov : covDiff (meanIterate U (j + 1)) (chainDrift X ξ (j + 1)) =
          covDiff (normalizedMean V) (adjointCubeAverage V σ) +
            covDiff (normalizedMean V) (contourLogDrift V m) := by
        rw [hdrift, ← covDiff_add]
        refine covDiff_congr hXj (fun b hb => ?_) _
        simp only [meanIterate, levelField, dif_pos hlt, fieldOfPositiveValues, dif_pos hb]
        exact one_mul _
      refine ⟨by rw [hmov]; exact (edgeFormSpace L n k (j + 1)).add_mem (s₇ m i₁) hνf,
        fun y => ComplexMatrix2.hermitianTraceless.add_mem (s₅ σ i₂ y) (s₄ m i₁ y), ?_⟩
      have hσc : ∀ x, σ x ∈ ComplexMatrix2.traceless := fun x => (i₂ x).2
      have hmc : m ∈ complexEdgeForms L n k j := ⟨fun b hb => (i₁.1 b hb).2, i₁.2⟩
      have hDc : covDiff V σ ∈ complexEdgeForms L n k j := s₉ σ hσc
      have hadd : meanCovariantStep V (m + covDiff V σ) =
          meanCovariantStep V m + meanCovariantStep V (covDiff V σ) := by
        have := s₂ m hmc _ hDc 1
        simpa using this
      change meanCovariantStep V (tangentForms U ξ j) + (if h : j < k then _ else _) = _
      rw [dif_pos hlt, i₃, hadd, s₆ σ hσc, hmov, hcov]
      simp only [meanCovariantStep]
      abel
  have hmem : ∀ (ξ : LevelForms L n k) (j : ℕ), j ≤ k →
      tangentForms U ξ j ∈ edgeFormSpace L n k j := by
    intro ξ j
    induction j with
    | zero => intro _; exact ξ.1.2
    | succ j ih =>
      intro hj
      have hlt : j < k := by omega
      change meanCovariantStep (meanIterate U j) (tangentForms U ξ j) +
        (if h : j < k then _ else _) ∈ _
      rw [dif_pos hlt]
      exact (edgeFormSpace L n k (j + 1)).add_mem
        ((hU j (Finset.mem_range.2 hlt)).2.2.1 _ (ih hlt.le)) (ξ.2 ⟨j, hlt⟩).2
  have hcm : ∀ {i : ℕ} {B : Edge L n k i → ComplexMatrix2}, B ∈ edgeFormSpace L n k i →
      B ∈ complexEdgeForms L n k i :=
    fun hB => ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  have hlin : ∀ (ξ ξ' : LevelForms L n k) (r : ℝ) (j : ℕ), j ≤ k →
      tangentForms U (r • ξ + ξ') j = (r : ℂ) • tangentForms U ξ j + tangentForms U ξ' j := by
    intro ξ ξ' r j
    induction j with
    | zero =>
      intro _
      funext b
      change r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b + (ξ'.1 : Edge L n k 0 → ComplexMatrix2) b =
        (r : ℂ) • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b + (ξ'.1 : Edge L n k 0 → ComplexMatrix2) b
      rw [Complex.coe_smul]
    | succ j ih =>
      intro hj
      have hlt : j < k := by omega
      change meanCovariantStep (meanIterate U j) (tangentForms U (r • ξ + ξ') j) +
        (if h : j < k then _ else _) =
        (r : ℂ) • (meanCovariantStep (meanIterate U j) (tangentForms U ξ j) +
          (if h : j < k then _ else _)) +
        (meanCovariantStep (meanIterate U j) (tangentForms U ξ' j) + (if h : j < k then _ else _))
      simp only [dif_pos hlt]
      rw [ih hlt.le, (hU j (Finset.mem_range.2 hlt)).2.1 _ (hcm (hmem ξ j hlt.le)) _
        (hcm (hmem ξ' j hlt.le))]
      have e : (((r • ξ + ξ').2 ⟨j, hlt⟩ : edgeFormSpace L n k (j + 1)) :
            Edge L n k (j + 1) → ComplexMatrix2) =
          (r : ℂ) • ((ξ.2 ⟨j, hlt⟩ : edgeFormSpace L n k (j + 1)) :
            Edge L n k (j + 1) → ComplexMatrix2) +
            ((ξ'.2 ⟨j, hlt⟩ : edgeFormSpace L n k (j + 1)) :
              Edge L n k (j + 1) → ComplexMatrix2) := by
        funext b
        change r • ((ξ.2 ⟨j, hlt⟩ : edgeFormSpace L n k (j + 1)) :
            Edge L n k (j + 1) → ComplexMatrix2) b +
          ((ξ'.2 ⟨j, hlt⟩ : edgeFormSpace L n k (j + 1)) :
            Edge L n k (j + 1) → ComplexMatrix2) b = _
        simp only [Pi.add_apply, Pi.smul_apply, Complex.coe_smul]
      rw [e, smul_add]
      abel
  have hzero : tangentForms U (0 : LevelForms L n k) k = 0 := by
    have := hlin 0 0 1 k le_rfl
    simpa using this
  let T : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k k :=
    { toFun := fun ξ => ⟨tangentForms U ξ k, hmem ξ k le_rfl⟩
      map_add' := fun ξ ξ' => by
        apply Subtype.ext
        have := hlin ξ ξ' 1 k le_rfl
        simpa using this
      map_smul' := fun r ξ => by
        apply Subtype.ext
        have := hlin ξ 0 r k le_rfl
        simp only [add_zero, hzero] at this
        simpa [Complex.coe_smul] using this }
  have hT : IsShiftedGaugeMap X T := by
    intro ξ
    exact (key ξ k le_rfl).2.2
  have hspec : IsShiftedGaugeMap X (shiftedGaugeMap X) :=
    Classical.epsilon_spec (p := IsShiftedGaugeMap X) ⟨T, hT⟩
  intro ξ
  refine ⟨fun j hj => hmem ξ j hj, ?_⟩
  rw [hspec ξ]
  exact (key ξ k le_rfl).2.2.symm
end YangMills.Construction.RunningCouplingSlope
end
