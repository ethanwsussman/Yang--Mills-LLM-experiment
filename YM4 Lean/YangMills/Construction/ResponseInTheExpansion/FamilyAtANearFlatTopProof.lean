import YangMills.Construction.ColdStepAtMirrorFrames.EntriesOfTheExpansionNearTheFlatFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsAtTwoFieldsProof
import YangMills.Construction.ColdStepAtMirrorFrames.FirstOrderAtTheFlatFieldProof
import YangMills.Construction.ResponseInTheExpansion.FamilyAtANearFlatTop
import YangMills.Construction.ResponseInTheExpansion.FamilyIsSmoothAboveTheFrame
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.Estimates YangMills.Construction.LinearResponse
def FirstOrderVanishesAtUniform : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame) (y : F.Site F.depth)
    (c : Fin 1 → F.Site F.depth × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 < σ → AreUnitVectors X →
    bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X = 0
namespace FirstOrderSteps
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame}
theorem exists_adjoint_neg (X : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    ∃ g : UnitQuaternion, _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X = -X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.UniformFieldFirstDeriv.exists_adjointAction_eq_neg <;> assumption
theorem plaquetteDefect_leftTranslate_le {j : ℕ} (Z : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) (q : ℝ) (hq : ∀ y i, ‖Z y i‖ ≤ q) :
    plaquetteDefect (leftTranslate Z (uniformField F j)) p ≤ 4 * q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.UniformFieldFirstDeriv.plaquetteDefect_leftTranslate_le <;> assumption
end FirstOrderSteps
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
open FirstOrderSteps
theorem firstOrderVanishesAtUniform_of_gauge (hg : GaugeCovarianceOfFrame) :
    FirstOrderVanishesAtUniform := by
  intro L t n₀ σ δ E E₃ f F y c X hf hF hσ hX
  obtain ⟨g, hgX⟩ := exists_adjoint_neg (X 0) (hX 0)
  let γ : F.Site F.depth → UnitQuaternion := fun _ => g
  have hflat : _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (uniformField F F.depth) = uniformField F F.depth := by
    funext z i
    simp [_root_.YangMills.Construction.BlockAverages.gaugeTransform, YangMills.Construction.ColdStepAtMirrorFrames.uniformField, γ]
  have hball : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), ‖τ‖ < σ / 4 := by
    have := Metric.ball_mem_nhds (0 : Fin 1 → ℝ) (by positivity : 0 < σ / 4)
    exact Filter.eventually_of_mem this fun τ h => by simpa using h
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ),
      subtractTrivial f F y (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ (leftTranslate (bondSpread c X τ) (uniformField F F.depth))) =
      subtractTrivial f F y (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) := by
    refine hball.mono fun τ hτ => ?_
    have hsp : ∀ z i, ‖bondSpread c X τ z i‖ ≤ ‖τ‖ := by
      intro z i
      simp only [bondSpread, Fin.sum_univ_one]
      by_cases e : c 0 = (z, i)
      · rw [if_pos e, norm_smul, hX 0, mul_one]
        exact norm_le_pi_norm τ 0
      · rw [if_neg e, norm_zero]
        exact norm_nonneg _
    have hc : IsSmallCurvature σ (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) := fun p _ =>
      (plaquetteDefect_leftTranslate_le _ p _ hsp).trans_lt (by linarith)
    show f F y _ - _ = f F y _ - _
    rw [hf.gauge_invariant hF y _ γ hc]
  have e1 := hg.2.1 F F.depth 1 (subtractTrivial f F y) (subtractTrivial f F y) (uniformField F F.depth) γ c X hev
  rw [hflat] at e1
  have hX' : (fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (c l).1) (X l)) = -X := by
    funext l
    fin_cases l
    exact hgX
  rw [hX'] at e1
  have hneg : bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c (-X) =
      -bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X := by
    unfold bondDeriv
    have e2 : (fun τ : Fin 1 → ℝ =>
          subtractTrivial f F y (leftTranslate (bondSpread c (-X) τ) (uniformField F F.depth))) =
        fun τ => (fun τ' =>
          subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (-τ) := by
      funext τ
      congr 2
      funext z i
      simp only [bondSpread, Fin.sum_univ_one]
      split_ifs
      · show τ 0 • (-(X 0)) = (-(τ 0)) • X 0
        module
      · rfl
    rw [e2, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
    have e3 := (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ)).comp_right_fderiv
      (f := fun τ' => subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (x := 0)
    have e4 : ((fun τ' => subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) ∘
        (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ))) =
        fun τ => (fun τ' =>
          subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (-τ) := rfl
    rw [e4] at e3
    rw [e3]
    simp
  rw [hneg] at e1
  linarith
def ExpansionDerivNearUniform : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) →
    AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X| ≤
      E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖
def EntryDerivNearUniform : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W c X - bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X| ≤
      3 * E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖
namespace ExpansionDerivSteps
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
variable {F : BlockFrame}
theorem expFlow_zero {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    expFlow B W 0 = W := by
  have h1 : expUnit 0 = 1 := by
    apply Subtype.ext
    show NormedSpace.exp (((0 : imaginaryQuaternions)) : Quaternion ℝ) = 1
    simp
  funext y i
  simp [expFlow, leftTranslate, h1]
theorem bondDeriv_sub_const_sub {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W W' : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - a) W c X - bondDeriv (fun V => G V - a) W' c X =
      bondDeriv G W c X - bondDeriv G W' c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RegularFamilyDerivs.bondDeriv_sub_const_sub <;> assumption
end ExpansionDerivSteps
open ExpansionDerivSteps
theorem expansionDerivNearUniform_of_flow (hflow : DerivBoundAlongFlow) : ExpansionDerivNearUniform := by
  obtain ⟨C₀, hC₀, hfl⟩ := hflow
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro L t n₀ σ δ E E₃ f F T y W B r k h X hf hF hδ hE hEE hT hW hflc hag hk hb hX
  have hW1 := hflc 1 zero_le_one le_rfl
  have hW0 := hflc 0 le_rfl zero_le_one
  rw [expFlow_zero] at hW0
  have h1 := hf.locality hF y W (expFlow B (uniformField F F.depth) 1) r k h X hW hW1 hag hk hb hX
  have hsm : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ContDiffThreeAlongBonds (f F y) (expFlow B (uniformField F F.depth) u) := fun u h0 h1 =>
    hf.smooth hF y _ (hflc u h0 h1)
  have hbd : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site F.depth × Fin 4)
      (Z : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors Z → ‖bondDeriv (f F y) (expFlow B (uniformField F F.depth) u) c Z‖ ≤ E₃ := by
    intro u h0 h1 l c Z hl1 hl3 hZ
    have a := hf.decay hF y _ l c Z (hflc u h0 h1) hl1 hl3 hZ
    rw [Real.norm_eq_abs]
    have hE3 : 0 ≤ E₃ := hE.trans hEE
    have hG := one_le_torusDecayFactor L (x := (bondSpan y c : ℝ)) hδ (by positivity)
    have hc : 0 ≤ (if l = 3 then E₃ else E) := by split_ifs <;> assumption
    have hle : (if l = 3 then E₃ else E) ≤ E₃ := by split_ifs <;> linarith
    refine a.trans ((div_le_self hc hG).trans hle)
  have h2 := hfl ℝ F F.depth T (f F y) (uniformField F F.depth) B (fun _ => E₃) hT (fun _ => hE.trans hEE) hsm hbd
    k (bondsAt y h) X hk hX
  rw [Real.norm_eq_abs] at h2
  have e := bondDeriv_sub_const_sub (f F y) (f F y (uniformField F F.depth))
    (expFlow B (uniformField F F.depth) 1) (uniformField F F.depth) (bondsAt y h) X
  have e' : bondDeriv (subtractTrivial f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X =
      bondDeriv (f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X -
      bondDeriv (f F y) (uniformField F F.depth) (bondsAt y h) X := e
  have h3 := abs_sub_le (bondDeriv (subtractTrivial f F y) W (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X)
  rw [e'] at h3
  have e3 : C₀ * (E₃ + E₃ + E₃) = 3 * C₀ * E₃ := by ring
  rw [e3] at h2
  linarith
namespace EntryDerivSteps
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
variable {F : BlockFrame}
theorem torusDecayFactor_mono (L : ℕ) {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.torusDecayFactor_mono <;> assumption
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (U : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) :
    bondDeriv (fun V => G V - a) U c X = bondDeriv G U c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_sub_const <;> assumption
def offsetSupNorm (o : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun l => (o l).natAbs
theorem add_siteOfCoords_siteOffset (hp : ∀ i, F.period F.depth i ≠ 0) (y z : F.Site F.depth) :
    y + siteOfCoords F.depth (siteOffset y z) = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsNearUniformFieldAux.add_siteOfCoords_siteOffset <;> assumption
theorem siteSupDist_eq_offsetSupNorm (hp : ∀ i, F.period F.depth i ≠ 0) (y z : F.Site F.depth) :
    siteSupDist y z = offsetSupNorm (siteOffset y z) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsNearUniformFieldAux.siteSupDist_eq_offsetSupNorm <;> assumption
end EntryDerivSteps
open EntryDerivSteps
theorem termDerivNearUniform_of_expansion (hrow : ExpansionDerivNearUniform) :
    EntryDerivNearUniform := by
  obtain ⟨C₀, hC₀, hr⟩ := hrow
  refine ⟨C₀, hC₀, ?_⟩
  intro L t n₀ σ δ E E₃ f F T y W B r k c X hf hF hδ hE hEE hT hW hfl hag hk1 hk2 hX
  have hp : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hag.1 i; omega
  have hE3 : 0 ≤ E₃ := hE.trans hEE
  have hextra : 0 ≤ C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖ := by positivity
  have hG := torusDecayFactor_pos L δ (r : ℝ)
  let h : Fin k → (Fin 4 → ℤ) × Fin 4 := fun l => (siteOffset y (c l).1, (c l).2)
  have hbf : bondsAt y h = c := by
    funext l
    show (y + siteOfCoords F.depth (siteOffset y (c l).1), (c l).2) = c l
    rw [add_siteOfCoords_siteOffset hp]
  by_cases hb : ∀ l, BondWithinRadius r (h l)
  · have := hr L t n₀ σ δ E E₃ f F T y W B r k h X hf hF hδ hE hEE hT hW hfl hag hk2 hb hX
    rw [hbf] at this
    refine this.trans (add_le_add_left ?_ _)
    gcongr
    linarith
  · push Not at hb
    obtain ⟨l, hl⟩ := hb
    have hfar : r ≤ bondSpan y c := by
      by_contra hcon
      have h1 : siteSupDist y (c l).1 ≤ bondSpan y c :=
        le_trans (Finset.le_sup (f := fun l : Fin k => siteSupDist y (c l).1) (Finset.mem_univ l)) (le_max_left _ _)
      have h2 : offsetSupNorm (siteOffset y (c l).1) < r := by
        rw [← siteSupDist_eq_offsetSupNorm hp]
        omega
      apply hl
      have hc : ∀ m, ((siteOffset y (c l).1 m).natAbs) ≤ offsetSupNorm (siteOffset y (c l).1) := fun m =>
        Finset.le_sup (f := fun m => (siteOffset y (c l).1 m).natAbs) (Finset.mem_univ m)
      refine ⟨fun m => ?_, fun m => ?_⟩
      · have := hc m
        show |siteOffset y (c l).1 m| ≤ (r : ℤ)
        rw [abs_le]
        omega
      · have := hc m
        show |((siteOffset y (c l).1 + Pi.single (c l).2 1 : Fin 4 → ℤ)) m| ≤ (r : ℤ)
        rw [abs_le]
        by_cases e : m = (c l).2
        · subst e
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
          omega
    have hflat : IsSmallCurvature σ (uniformField F F.depth) := by
      have := hfl 0 le_rfl zero_le_one
      have e0 : expFlow B (uniformField F F.depth) 0 = uniformField F F.depth := by
        have h1 : expUnit 0 = 1 := by
          apply Subtype.ext
          show NormedSpace.exp (((0 : imaginaryQuaternions)) : Quaternion ℝ) = 1
          simp
        funext y' i
        simp [expFlow, leftTranslate, h1]
      rwa [e0] at this
    have hGs : torusDecayFactor L δ r ≤ torusDecayFactor L δ (bondSpan y c) :=
      torusDecayFactor_mono L hδ (by positivity) (by exact_mod_cast hfar)
    have bound : ∀ U : F.GaugeField F.depth, IsSmallCurvature σ U →
        |bondDeriv (subtractTrivial f F y) U c X| ≤ E / torusDecayFactor L δ r := by
      intro U hU
      have e1 : bondDeriv (subtractTrivial f F y) U c X = bondDeriv (f F y) U c X :=
        bondDeriv_sub_const (f F y) _ U c X hk1
      rw [e1]
      have a := hf.decay hF y U k c X hU hk1 (by omega) hX
      rw [if_neg (by omega : k ≠ 3)] at a
      exact a.trans (div_le_div_of_nonneg_left hE hG hGs)
    have a1 := bound W hW
    have a2 := bound _ hflat
    have a3 := abs_sub (bondDeriv (subtractTrivial f F y) W c X)
      (bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X)
    have e : 3 * E / torusDecayFactor L δ r =
        E / torusDecayFactor L δ r + E / torusDecayFactor L δ r + E / torusDecayFactor L δ r := by
      ring
    have a4 : 0 ≤ E / torusDecayFactor L δ r := by positivity
    rw [e]
    linarith
namespace NearUniformTopSteps
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame}
theorem isCubicTorusAbove_of_top {L t n₀ : ℕ} (hL : 0 < L) (h : IsCubicTopTorus L t n₀ F) :
    IsCubicTorusAbove L t n₀ F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.isCubicTorusAbove_of_isCubicTopTorus <;> assumption
theorem isLargeCubicTorus_of_top {L t n₀ : ℕ} (h64 : 64 ≤ n₀) (h : IsCubicTopTorus L t n₀ F) :
    IsLargeCubicTorus F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.isLargeCubicTorus_of_isCubicTopTorus <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem distFromOne_fieldAboveFrame_le (hcover : BlocksCoverLowerLevel) (hfield : ChartedFieldNearOne)
    (hgeo : CubicTorusCellGeometry) {Ct σ : ℝ} {R : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ)
    (hσ : 0 < σ) (hCt : 0 ≤ Ct) (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F)
    (hs : ∀ i, 2 * R + 2 < F.extent i)
    (V : F.GaugeField F.top) (Y : F.Cell) (η : StepVariable (finiteCells F))
    (hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρA m b V‖ ≤ Ct * σ)
    (hη : ∀ b, ‖η b‖ ≤ σ / 64) (hn : IsNearUniformAbout (5 / 4 * σ) R V Y) (b : F.Site F.depth × Fin 4)
    (hb : cellSupDist (enclosingCell b.1) Y + 1 ≤ R) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (fieldAboveFrame star a ρA m V η b.1 b.2) ≤
      (Ct + 5) * (1 + cellSupDist (enclosingCell b.1) Y) * σ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.gap_fieldAboveFrame_le <;> assumption
theorem agreeOnBox_at_site (hgeo : CubicTorusCellGeometry) (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F)
    (hL : 3 ≤ F.blockSide) (W : F.GaugeField F.depth) (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (Y : F.Cell) (y : F.Site F.depth)
    (R₁ r : ℕ) (hy : enclosingCell y = Y) (hr : r + F.blockSide ≤ F.blockSide * R₁)
    (hagree : ∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
      expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2) (hper : ∀ i, 2 * r + 2 < F.period F.depth i) :
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.agreeOnBox_of_flow <;> assumption
def MotionEstimate (K M : ℕ → ℝ) : Prop :=
  ∀ (F : BlockFrame) (s a ρA r : ℝ) (m p : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
      (w : Fin p → Perturbation F),
      (∀ i, F.period F.depth i ≠ 0) → 0 ≤ r → (∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F)) →
      (∀ x i, ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
        (X' : Fin k → imaginaryQuaternions),
        1 ≤ k → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ∃ α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, α 0 x i = 0) ∧
        (∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0) ∧
        (∀ᶠ τ in 𝓝 0, interpolatedField s a ρA m (perturbedTop V w τ) (perturbedVariable η w τ) =
          leftTranslate (α τ) (interpolatedField s a ρA m V η)) ∧
        ∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
          ‖motionComponent α e x i‖ ≤ M q * (w (e l)).decayWeight r x i
theorem motion_of_topPerturbation {K M : ℕ → ℝ} (hm : MotionEstimate K M)
    (hends : interpolationAtEndpoints)
    (star : Bool) (a ρA κ₂ : ℝ) (m p : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (c : Fin p → F.Site F.top × Fin 4) (X : Fin p → imaginaryQuaternions) (hX : AreUnitVectors X)
    (hper : ∀ i, F.period F.depth i ≠ 0) (hκ : 0 ≤ κ₂)
    (hch : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hab : ∀ x i, ‖coordsAboveFrame star a ρA m V η x i‖ ≤ 1)
    (han : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star a ρA m d) V)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions),
      1 ≤ k → AreUnitVectors X' → ‖bondDeriv (stepFrame star a ρA m d) V c' X'‖ ≤
        K k * Real.exp (-(κ₂ * bondListDistance (enclosingCell d.1) c'))) :
    ∃ α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, α 0 x i = 0) ∧
      (∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0) ∧
      (∀ᶠ τ in 𝓝 0, fieldAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η =
        leftTranslate (α τ) (fieldAboveFrame star a ρA m V η)) ∧
      ∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
        ‖motionComponent α e x i‖ ≤ M q * Real.exp (-(κ₂ * cellSupDist (enclosingCell x) (c (e l)).1)) := by
  have hE : ∀ V' : F.GaugeField F.top,
      (∀ b, interpolatedFrame (segmentEnd star) a ρA m b V' = stepFrame star a ρA m b V') ∧
      (∀ η', interpolatedCoords (segmentEnd star) a ρA m V' η' = coordsAboveFrame star a ρA m V' η') ∧
      (∀ η', interpolatedField (segmentEnd star) a ρA m V' η' = fieldAboveFrame star a ρA m V' η') := fun V' => by
    obtain ⟨h1, h2, h3, -⟩ := hends F star a ρA 0 0 0 m V'
    exact ⟨h1, h2, h3⟩
  obtain ⟨α, h0, hc, hid, hp⟩ := hm F (segmentEnd star) a ρA κ₂ m p V η (fun l => Perturbation.top (c l) (X l))
    hper hκ hch
    (fun x i => by rw [(hE V).2.1]; exact hab x i)
    (fun d hd => by
      have : interpolatedFrame (segmentEnd star) a ρA m d = stepFrame star a ρA m d :=
        funext fun V' => (hE V').1 d
      rw [this]; exact han d hd)
    (fun d hd k c' X' hk hX' => by
      have : interpolatedFrame (segmentEnd star) a ρA m d = stepFrame star a ρA m d :=
        funext fun V' => (hE V').1 d
      rw [this]; exact hdec d hd k c' X' hk hX')
    (fun l => hX l)
  refine ⟨α, h0, hc, hid.mono fun τ h => ?_, fun q e x i l hq => ?_⟩
  · have h1 : perturbedVariable η (fun l => Perturbation.top (c l) (X l)) τ = η := by
      simp [perturbedVariable, Perturbation.variableDirection]
    have h2 : perturbedTop V (fun l => Perturbation.top (c l) (X l)) τ = leftTranslate (bondSpread c X τ) V := rfl
    rw [h1, h2, (hE _).2.2, (hE V).2.2] at h
    exact h
  · exact hp q e x i l hq
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (U : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) :
    bondDeriv (fun V => G V - a) U c X = bondDeriv G U c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_sub_const <;> assumption
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem site_comparison (htwo : SecondDerivAlongMotionsClose) (hfl1 : FirstOrderVanishesAtUniform)
    {C₀ : ℝ} (hent : ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W c X - bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X| ≤
      3 * E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖)
    {L t n₀ r : ℕ} {σ δ E E₃ K μ ε : ℝ} {f : LocalFamily} (hf : IsRegularOnTorus L t n₀ σ δ E E₃ f F)
    (hF : IsCubicTorusAbove L t n₀ F) (hσ : 0 < σ) (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hEE : E ≤ E₃) (hK : 0 ≤ K)
    (hμ : 0 ≤ μ) (hT : ∀ b, b ∈ fineBonds F) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hW : IsSmallCurvature σ W) (hflat : IsSmallCurvature σ (uniformField F F.depth))
    (hfl : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u))
    (hag : AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r)
    (hε0 : 0 ≤ ε) (hε : 3 * E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ ε) :
    (∀ α : (Fin 1 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x b, α 0 x b = 0) →
      (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) →
      ∑ b ∈ fineBonds F, ‖motionComponent α ![0] b.1 b.2‖ ≤ K →
      |iteratedFDeriv ℝ 1 (fun τ => subtractTrivial f F y (leftTranslate (α τ) W)) 0 ![Pi.single 0 1]| ≤
        ε * K) ∧
    ∀ α α₀ : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x b, α 0 x b = 0) →
      (∀ x b, α₀ 0 x b = 0) →
      (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) → (∀ x b, ContDiffAt ℝ 3 (fun τ => α₀ τ x b) 0) →
      (∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2‖ ≤ K) →
      (∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α₀ ![l] b.1 b.2‖ ≤ K) →
      ∑ b ∈ fineBonds F, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K →
      (∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖ ≤ μ) →
      |iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (leftTranslate (α τ) W)) 0
          ![Pi.single 0 1, Pi.single 1 1] -
        iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (leftTranslate (α₀ τ) (uniformField F F.depth))) 0
          ![Pi.single 0 1, Pi.single 1 1]| ≤ ε * (K ^ 2 + K) + 2 * E * K * μ := by
  have hsm : ∀ U : F.GaugeField F.depth, IsSmallCurvature σ U →
      ContDiffThreeAlongBonds (subtractTrivial f F y) U := by
    intro U hU k c X
    exact (hf.smooth hF y U hU k c X).sub contDiffAt_const
  refine htwo F F.depth (fineBonds F) (subtractTrivial f F y) W (uniformField F F.depth) ε E K μ hT (hsm W hW)
    (hsm _ hflat) hε0 hE hK hμ
    (fun k c X hk1 hk2 hX => (hent L t n₀ σ δ E E₃ f F (fineBonds F) y W B r k c X hf hF hδ hE hEE hT hW hfl hag
      hk1 hk2 hX).trans hε)
    (fun c X hX => hfl1 L t n₀ σ δ E E₃ f F y c X hf hF hσ hX)
    (fun c X hX => ?_)
  have e1 : bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X =
      bondDeriv (f F y) (uniformField F F.depth) c X :=
    bondDeriv_sub_const (f F y) _ _ c X (by norm_num)
  rw [e1]
  have a := hf.decay hF y _ 2 c X hflat (by norm_num) (by norm_num) hX
  rw [if_neg (by norm_num : (2 : ℕ) ≠ 3)] at a
  exact a.trans (div_le_self hE (one_le_torusDecayFactor L hδ (by positivity)))
theorem bondDeriv_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (a : E) (U : F.GaugeField F.top) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    bondDeriv (fun V => G V + a) U ![e] ![X] = bondDeriv G U ![e] ![X] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_add_const <;> assumption
theorem motionComponent_close {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    {p : ℕ} (w w₀ : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (α α₀ : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (x : F.Site F.depth) (i : Fin 4) (ht : ¬ IsAxialTreeBond (x, i)) (hX : AreUnitVectors X)
    (h0 : ∀ x i, α 0 x i = 0) (h00 : ∀ x i, α₀ 0 x i = 0) (hc : ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hc0 : ContDiffAt ℝ 3 (fun τ => α₀ τ x i) 0)
    (hw : ContDiffAt ℝ 3 (fun τ => w (leftTranslate (bondSpread c X τ) V) x i) 0)
    (hw0 : ContDiffAt ℝ 3 (fun τ => w₀ (leftTranslate (bondSpread c X τ) (uniformField F F.top)) x i) 0)
    (hu : ‖w V x i‖ ≤ 1) (hu0 : w₀ (uniformField F F.top) x i = 0) {K₁ : ℝ}
    (hK : ‖bondDeriv (fun V' => w V' x i) V ![c l] ![X l]‖ ≤ K₁)
    (hid : ∀ᶠ τ in 𝓝 0, chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V))
    (hid0 : ∀ᶠ τ in 𝓝 0, chartedField (w₀ (leftTranslate (bondSpread c X τ) (uniformField F F.top)))
        (leftTranslate (bondSpread c X τ) (uniformField F F.top)) =
      leftTranslate (α₀ τ) (chartedField (w₀ (uniformField F F.top)) (uniformField F F.top))) :
    ‖motionComponent α ![l] x i - motionComponent α₀ ![l] x i‖ ≤ C * ‖w V x i‖ * (K₁ + 1) +
      ‖bondDeriv (fun V' => w V' x i) V ![c l] ![X l] -
        bondDeriv (fun V' => w₀ V' x i) (uniformField F F.top) ![c l] ![X l]‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.motionComponent_sub_le <;> assumption
theorem norm_coordsAboveFrame_le (star : Bool) (a ρ σ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hroom : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρ m b V‖ + σ / 64 ≤ ρ)
    (hη : ∀ b, ‖η b‖ ≤ σ / 64) (x : F.Site F.depth) (i : Fin 4) : ‖coordsAboveFrame star a ρ m V η x i‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.norm_coordsAboveFrame_le <;> assumption
theorem sum_fineBonds_le {κ Cg q : ℝ} (_hκ : 0 < κ) (hq : 0 ≤ q)
    (hCg : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(κ * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (G.blockSide : ℝ) ^ 4)
    (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F) (z : F.Cell) (g : F.Site F.depth × Fin 4 → ℝ)
    (hg : ∀ b, g b ≤ q * Real.exp (-(κ * cellSupDist (enclosingCell b.1) z))) :
    ∑ b ∈ fineBonds F, g b ≤ q * (Cg * (F.blockSide : ℝ) ^ 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.sum_fineBonds_le <;> assumption
theorem motionComponent_tree {C : ℝ}
    (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    {p : ℕ} (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (x : F.Site F.depth) (i : Fin 4) (ht : IsAxialTreeBond (x, i)) (h0 : ∀ x i, α 0 x i = 0)
    (hc : ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hid : ∀ᶠ τ in 𝓝 0, chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V)) : motionComponent α ![l] x i = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.motionComponent_axial_eq_zero <;> assumption
theorem sum_fineBonds_split_le {κ Cg εb M₁ : ℝ} {R₃ : ℕ} (hκ : 0 < κ) (hε : 0 ≤ εb)
    (hM : 0 ≤ M₁)
    (hCg : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(κ / 2 * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (G.blockSide : ℝ) ^ 4)
    (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F) (z : F.Cell) (g : F.Site F.depth × Fin 4 → ℝ)
    (hnear : ∀ b, cellSupDist (enclosingCell b.1) z ≤ R₃ → g b ≤ εb)
    (hfar : ∀ b, g b ≤ 2 * M₁ * Real.exp (-(κ * cellSupDist (enclosingCell b.1) z))) :
    ∑ b ∈ fineBonds F, g b ≤
      (εb * Real.exp (κ / 2 * R₃) + 2 * M₁ * Real.exp (-(κ / 2 * R₃))) * (Cg * (F.blockSide : ℝ) ^ 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.sum_fineBonds_split_le <;> assumption
open Classical in
theorem abs_sum_block_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g : F.Site F.depth → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hg : ∀ y, enclosingCell y = Y → |g y| ≤ q) :
    |∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), g y| ≤
      (F.blockSide : ℝ) ^ 4 * q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.abs_sum_block_le <;> assumption
open Classical in
theorem bondDeriv_cellCentredExpansion {k : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (h : ∀ y : F.Site F.depth, ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => centredExpansion star a ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (cellCentredExpansion star a ρA m f Y η) V c X =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        bondDeriv (centredExpansion star a ρA m f y η) V c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_cellCentredExpansion <;> assumption
structure ComparisonConstants (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (R R₁ R₂ R₃ r : ℕ)
    (Cc A Cg Cg₂ CΘ εR ωb K₁ Kc μ ε₁ : ℝ) (M : ℕ → ℝ) : Prop where
  top_radius : 4 * R + 8 ≤ T.n₀
  top_large : 64 ≤ T.n₀
  side_three : 3 ≤ T.L
  cut_radius : R₂ + 3 ≤ R
  block_radius : 4 * (T.blockIndex + R₃ + 1) ≤ R
  box_inside : r + T.L ≤ T.L * R₁
  inner_le_radius : R₁ ≤ R
  nonneg : 0 ≤ Cc ∧ 0 ≤ CΘ ∧ 0 ≤ εR ∧ 0 ≤ ωb ∧ 0 ≤ K₁ ∧ 0 ≤ Kc ∧ 0 ≤ μ ∧ 0 ≤ ε₁ ∧ (∀ q, 0 ≤ M q) ∧ 0 ≤ T.Ct
  first_deriv : 16 * T.chainParams.Kk 1 ≤ K₁
  first_deriv_nonneg : 0 ≤ T.chainParams.Kk 1
  value_bound : 3 * T.E / torusDecayFactor T.L T.decayRate r + Cc * T.energyRatio * (A * (T.L : ℝ) ^ 4 * T.σ) ≤ ε₁
  motion_bound : (M 1 + M 2) * (Cg * (T.L : ℝ) ^ 4) ≤ Kc
  gap_bound : ((CΘ * ((T.Ct + 1) * T.σ) * (K₁ + 1) + εR + ωb) * Real.exp (T.chainParams.κ₂ / 2 * R₃) +
      2 * (2 * M 1) * Real.exp (-(T.chainParams.κ₂ / 2 * R₃))) * (Cg₂ * (T.L : ℝ) ^ 4) ≤ μ
  zeroth : (T.L : ℝ) ^ 4 * ε₁ ≤ 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex
  first : (T.L : ℝ) ^ 4 * (ε₁ * Kc) ≤ 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)
  second : (T.L : ℝ) ^ 4 * (ε₁ * (Kc ^ 2 + Kc) + 2 * T.E * Kc * μ) ≤
    2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)
structure FrameFacts (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (star : Bool) (V : F.GaugeField F.top) : Prop where
  norm_le : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) b V‖ ≤ T.Ct * T.σ
  norm_add_le : ∀ b ∈ chordBonds (finiteCells F),
    ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) b V‖ + T.σ / 64 ≤ T.chainParams.ρA
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star T.a T.chainParams.ρA (frameRadius x) b) V
  deriv_le : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k →
    AreUnitVectors X → ‖bondDeriv (stepFrame star T.a T.chainParams.ρA (frameRadius x) b) V c X‖ ≤
      16 ^ k * T.chainParams.Kk k * Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell b.1) c))
  small_curvature : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.σ / 64) →
    IsSmallCurvature (3 / 4 * T.σ) (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η)
theorem frameFacts_of_top (hends : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (t : ℕ) (x : ℝ) (star : Bool)
    (V : F.GaugeField F.top) (hx : T.coupling ≤ x) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hfb : InterpolatedFramesControlledAt T t x) (hft : FrameBoundsForParameters T) : FrameFacts T x star V := by
  obtain ⟨Cf, C, _, _, _, _, _, _, _, _, _, _, _, _, _, hFH⟩ := hft
  have hsm := (hFH t x F V hx hF hV).2.1 star
  have hs0 : 0 ≤ segmentEnd star := by unfold segmentEnd; split_ifs <;> norm_num
  have hs1 : segmentEnd star ≤ 1 := by unfold segmentEnd; split_ifs <;> norm_num
  have hbet := (hfb.single F V (segmentEnd star) hF hV hs0 hs1).2
  obtain ⟨h1, -, h3, -⟩ := hends F star T.a T.chainParams.ρA 0 0 0 (frameRadius x) V
  refine ⟨fun b hb => ?_, hsm.norm_add_le, hsm.analytic, hsm.deriv_bound, fun η hη => ?_⟩
  · rw [← h1 b]
    exact hbet.norm_le b hb
  · rw [← h3 η]
    exact hbet.small_curvature_nearby η hη
theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · apply Subtype.ext
    apply Quaternion.ext <;> rfl
  · rfl
theorem fieldAboveFrame_uniform (a ρA : ℝ) (m : ℕ)
    (hz : ∀ b, stepFrame true a ρA m b (uniformField F F.top) = 0) :
    fieldAboveFrame true a ρA m (uniformField F F.top) 0 = uniformField F F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.fieldAboveFrame_uniform <;> assumption
theorem abs_subtractTrivial_le {C₀ : ℝ} (hr : ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) →
    AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X| ≤
      E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖)
    {L t n₀ r : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily} (hf : IsRegularOnTorus L t n₀ σ δ E E₃ f F)
    (hF : IsCubicTorusAbove L t n₀ F) (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hEE : E ≤ E₃)
    (hT : ∀ b, b ∈ fineBonds F) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hW : IsSmallCurvature σ W)
    (hfl : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u))
    (hag : AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r) :
    |subtractTrivial f F y W| ≤ E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ := by
  have h := hr L t n₀ σ δ E E₃ f F (fineBonds F) y W B r 0 Fin.elim0 Fin.elim0 hf hF hδ hE hEE hT hW hfl hag
    (by norm_num) (fun l => l.elim0) (fun l => l.elim0)
  have z : ∀ U : F.GaugeField F.depth,
      bondDeriv (subtractTrivial f F y) U (bondsAt y Fin.elim0) Fin.elim0 = subtractTrivial f F y U := by
    intro U
    unfold bondDeriv
    rw [iteratedFDeriv_zero_apply]
    congr 1
    funext z' i
    have e : bondSpread (bondsAt y Fin.elim0) (Fin.elim0 : Fin 0 → imaginaryQuaternions) 0 z' i = 0 := by
      simp [bondSpread]
    simp only [leftTranslate, e, expUnit_zero, one_mul]
  rw [z, z] at h
  have e0 : subtractTrivial f F y (uniformField F F.depth) = 0 := sub_self _
  rw [e0, sub_zero] at h
  exact h
theorem exists_cutoff_flow (hcover : BlocksCoverLowerLevel) (hfield : ChartedFieldNearOne)
    (hgeo : CubicTorusCellGeometry) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {R R₁ R₂ r : ℕ} {A : ℝ} (hCt : 0 ≤ T.Ct)
    (hσ : 0 < T.σ) (hR2 : R₂ + 3 ≤ R) (hr : r + T.L ≤ T.L * R₁)
    (hcut : ∀ (F : BlockFrame) (W : F.GaugeField F.depth) (Y : F.Cell), Odd F.blockSide → 3 ≤ F.blockSide →
      IsLargeCubicTorus F → IsSmallCurvature (3 / 4 * T.σ) W →
      (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₂ + 2 →
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W b.1 b.2) ≤ (T.Ct + 5) * (1 + cellSupDist (enclosingCell b.1) Y) * T.σ) →
      ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature T.σ (expFlow B (uniformField F F.depth) u)) ∧
        (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
          expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2) ∧
        ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * T.σ)
    (star : Bool) (x : ℝ) (V : F.GaugeField F.top) (Y : F.Cell) (η : StepVariable (finiteCells F))
    (hFL : F.blockSide = T.L) (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) (hcub : IsLargeCubicTorus F)
    (hs : ∀ i, 2 * R + 2 < F.extent i) (hper : ∀ i, 2 * r + 2 < F.period F.depth i)
    (hfacts : FrameFacts T x star V) (hη : ∀ b, ‖η b‖ ≤ T.σ / 64)
    (hn : IsNearUniformAbout (5 / 4 * T.σ) R V Y) :
    ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature T.σ (expFlow B (uniformField F F.depth) u)) ∧
      (∀ y : F.Site F.depth, enclosingCell y = Y →
        AgreeOnBox (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η)
          (expFlow B (uniformField F F.depth) 1) y y r) ∧
      ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * T.σ := by
  have hW := hfacts.small_curvature η hη
  obtain ⟨B, h1, h2, h3⟩ := hcut F _ Y hodd hL3 hcub hW (fun b hb =>
    distFromOne_fieldAboveFrame_le hcover hfield hgeo star T.a T.chainParams.ρA (frameRadius x) hσ hCt hodd hcub hs V Y
      η hfacts.norm_le hη hn b (by omega))
  refine ⟨B, h1, fun y hy => agreeOnBox_at_site hgeo hodd hcub hL3 _ B Y y R₁ r hy
    (by rw [hFL]; exact hr) h2 hper, h3⟩
theorem isSmallCurvature_uniform_top {s : ℝ} (hs : 0 < s) : IsSmallCurvature s (uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
theorem isSmallCurvature_uniform_depth {s : ℝ} (hs : 0 < s) : IsSmallCurvature s (uniformField F F.depth) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.isSmallCurvature_uniformField_fine <;> assumption
theorem exists_motion {M : ℕ → ℝ} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hm : MotionEstimate (fun k => 16 ^ k * T.chainParams.Kk k) M)
    (hends : interpolationAtEndpoints) (hρ0 : 0 ≤ T.chainParams.ρA) (hρ1 : T.chainParams.ρA ≤ 1)
    (hκ : 0 ≤ T.chainParams.κ₂) {x : ℝ} {star : Bool} {V : F.GaugeField F.top} (hfacts : FrameFacts T x star V)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.σ / 64) {p : ℕ}
    (c : Fin p → F.Site F.top × Fin 4) (X : Fin p → imaginaryQuaternions) (hX : AreUnitVectors X)
    (hper : ∀ i, F.period F.depth i ≠ 0) (hch : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F)) :
    ∃ α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, α 0 x i = 0) ∧
      (∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0) ∧
      (∀ᶠ τ in 𝓝 0, fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) (leftTranslate (bondSpread c X τ) V) η =
        leftTranslate (α τ) (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η)) ∧
      ∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
        ‖motionComponent α e x i‖ ≤
          M q * Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell x) (c (e l)).1)) :=
  motion_of_topPerturbation hm hends star T.a T.chainParams.ρA T.chainParams.κ₂ (frameRadius x) p V η c X hX hper hκ hch
    (fun x' i => norm_coordsAboveFrame_le star T.a T.chainParams.ρA T.σ (frameRadius x) V η hρ0 hρ1
      hfacts.norm_add_le hη x' i)
    hfacts.analytic hfacts.deriv_le
theorem bondDeriv_centredExpansion_eq {k : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (α : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hid : ∀ᶠ τ in 𝓝 0, fieldAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η =
      leftTranslate (α τ) (fieldAboveFrame star a ρA m V η)) :
    bondDeriv (centredExpansion star a ρA m f y η) V c X =
      iteratedFDeriv ℝ k (fun τ => subtractTrivial f F y (leftTranslate (α τ) (fieldAboveFrame star a ρA m V η))) 0
        (fun l => Pi.single l 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_centredExpansion_eq <;> assumption
theorem stepFrame_response_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x εR ωb : ℝ} {star : Bool} {V : F.GaugeField F.top}
    {b : F.Site F.depth × Fin 4}
    {e : F.Site F.top × Fin 4} {X : imaginaryQuaternions} (hb : b ∈ chordBonds (finiteCells F)) (hX : ‖X‖ = 1)
    (hfT : FrameFacts T x true V) (hfS : FrameFacts T x star V)
    (hleast : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X' →
      ‖bondDeriv (frameGap T.a T.chainParams.ρA (frameRadius x) b) V c X'‖ ≤ ωb)
    (hresp : ‖bondDeriv (torusCoordinate T.a T.chainParams.ρA b) V ![e] ![X] -
      bondDeriv (torusCoordinate T.a T.chainParams.ρA b) (uniformField F F.top) ![e] ![X]‖ ≤ εR)
    (hω : 0 ≤ ωb) :
    ‖bondDeriv (stepFrame star T.a T.chainParams.ρA (frameRadius x) b) V ![e] ![X] -
      bondDeriv (stepFrame true T.a T.chainParams.ρA (frameRadius x) b) (uniformField F F.top) ![e] ![X]‖ ≤
        εR + ωb := by
  have e0 : stepFrame true T.a T.chainParams.ρA (frameRadius x) b = torusCoordinate T.a T.chainParams.ρA b := rfl
  rw [e0]
  cases star with
  | true =>
    rw [e0]
    linarith
  | false =>
    have hs : stepFrame false T.a T.chainParams.ρA (frameRadius x) b =
        fun V' => stepFrame true T.a T.chainParams.ρA (frameRadius x) b V' +
          frameGap T.a T.chainParams.ρA (frameRadius x) b V' := by
      funext V'
      simp [frameGap]
    have hX1 : AreUnitVectors ![X] := fun l => by
      fin_cases l
      exact hX
    have d1 : DifferentiableAt ℝ (fun τ : Fin 1 → ℝ => stepFrame true T.a T.chainParams.ρA (frameRadius x) b
        (leftTranslate (bondSpread ![e] ![X] τ) V)) 0 :=
      ((hfT.analytic b hb 1 ![e] ![X]).differentiableAt)
    have d2 : DifferentiableAt ℝ (fun τ : Fin 1 → ℝ => stepFrame false T.a T.chainParams.ρA (frameRadius x) b
        (leftTranslate (bondSpread ![e] ![X] τ) V)) 0 :=
      ((hfS.analytic b hb 1 ![e] ![X]).differentiableAt)
    have d3 : DifferentiableAt ℝ (fun τ : Fin 1 → ℝ => frameGap T.a T.chainParams.ρA (frameRadius x) b
        (leftTranslate (bondSpread ![e] ![X] τ) V)) 0 := d2.sub d1
    have hadd : bondDeriv (stepFrame false T.a T.chainParams.ρA (frameRadius x) b) V ![e] ![X] =
        bondDeriv (stepFrame true T.a T.chainParams.ρA (frameRadius x) b) V ![e] ![X] +
          bondDeriv (frameGap T.a T.chainParams.ρA (frameRadius x) b) V ![e] ![X] := by
      rw [hs]
      unfold bondDeriv
      have h1 : ∀ g : (Fin 1 → ℝ) → imaginaryQuaternions, iteratedFDeriv ℝ 1 g 0 (fun l => Pi.single l 1) =
          fderiv ℝ g 0 (Pi.single 0 1) := fun g => iteratedFDeriv_one_apply _
      rw [h1, h1, h1]
      rw [fderiv_fun_add d1 d3]
      rfl
    rw [hadd]
    have a1 := hleast 1 ![e] ![X] le_rfl (by norm_num) hX1
    rw [e0]
    set A := bondDeriv (torusCoordinate T.a T.chainParams.ρA b) V ![e] ![X]
    set B := bondDeriv (frameGap T.a T.chainParams.ρA (frameRadius x) b) V ![e] ![X]
    set A₀ := bondDeriv (torusCoordinate T.a T.chainParams.ρA b) (uniformField F F.top) ![e] ![X]
    have e2 : A + B - A₀ = (A - A₀) + B := by abel
    rw [e2]
    exact (norm_add_le _ _).trans (add_le_add hresp a1)
set_option maxHeartbeats 4000000 in
theorem familyNearUniformTopAt_of_constants (hcover : BlocksCoverLowerLevel) (hfield : ChartedFieldNearOne)
    (hgeo : CubicTorusCellGeometry) (htwo : SecondDerivAlongMotionsClose)
    (hfl1 : FirstOrderVanishesAtUniform) (hends : interpolationAtEndpoints)
    {Cc CΘ Cg Cg₂ A εR ωb K₁ Kc μ ε₁ : ℝ} {R R₁ R₂ R₃ r : ℕ} {M : ℕ → ℝ} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters}
    (hent : ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
      (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
      (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (r k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
      IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
      AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
      |bondDeriv (subtractTrivial f F y) W c X - bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X| ≤
        3 * E / torusDecayFactor L δ r + Cc * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖)
    (hr : ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
      (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
      (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsRegularOnTorus L t n₀ σ δ E E₃ f F → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
      IsSmallCurvature σ W → (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
      AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) →
      AreUnitVectors X →
      |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
        bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X| ≤
        E / torusDecayFactor L δ r + Cc * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖)
    (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        CΘ * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    (hm : MotionEstimate (fun k => 16 ^ k * T.chainParams.Kk k) M)
    (hCg : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) z)) ≤
        Cg * (G.blockSide : ℝ) ^ 4)
    (hCg₂ : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell b.1) z)) ≤
        Cg₂ * (G.blockSide : ℝ) ^ 4)
    (hnum : ComparisonConstants T R R₁ R₂ R₃ r Cc A Cg Cg₂ CΘ εR ωb K₁ Kc μ ε₁ M) (hd : T.IsOrdered)
    (hκ : 0 < T.chainParams.κ₂) (hρ0 : 0 ≤ T.chainParams.ρA) (hρ1 : T.chainParams.ρA ≤ 1)
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x)
    (hft : FrameBoundsForParameters T)
    (hbd : CentredExpansionContDiffAt T) (hω : ∀ x : ℝ, T.coupling ≤ x → frameGapBound T (frameRadius x) ≤ ωb)
    (hcut : ∀ (F : BlockFrame) (W : F.GaugeField F.depth) (Y : F.Cell), Odd F.blockSide → 3 ≤ F.blockSide →
      IsLargeCubicTorus F → IsSmallCurvature (3 / 4 * T.σ) W →
      (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₂ + 2 →
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W b.1 b.2) ≤ (T.Ct + 5) * (1 + cellSupDist (enclosingCell b.1) Y) * T.σ) →
      ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature T.σ (expFlow B (uniformField F F.depth) u)) ∧
        (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
          expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2) ∧
        ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * T.σ)
    (hresp : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), IsBlockTorus T.L F →
      (∀ i, 2 * R + 2 < F.extent i) →
      IsSmallCurvature (5 / 4 * T.σ) V → IsNearUniformAbout (5 / 4 * T.σ) R V Y →
      ∀ (b : F.Site F.depth × Fin 4) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
        b ∈ chordBonds (finiteCells F) → 4 * cellSupDist Y (enclosingCell b.1) ≤ R →
        4 * cellSupDist Y e.1 ≤ R → ‖X‖ = 1 →
        ‖bondDeriv (torusCoordinate T.a T.chainParams.ρA b) V ![e] ![X] -
          bondDeriv (torusCoordinate T.a T.chainParams.ρA b) (uniformField F F.top) ![e] ![X]‖ ≤ εR)
    (hzero : ∀ (F : BlockFrame) (m : ℕ), IsBlockTorus T.L F → ∀ b,
      stepFrame true T.a T.chainParams.ρA m b (uniformField F F.top) = 0) :
    FamilyNearUniformTopAt T R := by
  intro t x f F V hx hf hF hV star Y hn
  obtain ⟨hFL, _, n, hsn, hnn⟩ := id hF
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := hnum.nonneg
  have hn1 := hnum.top_radius
  have hn2 := hnum.top_large
  have hn3 := hnum.side_three
  have hn7 := hnum.inner_le_radius
  have hn6 := hnum.box_inside
  have hodd : Odd F.blockSide := by rw [hFL]; exact hd.odd_L
  have hL3 : 3 ≤ F.blockSide := by rw [hFL]; exact hn3
  have hcub : IsLargeCubicTorus F := isLargeCubicTorus_of_top hn2 hF
  have hlow : IsCubicTorusAbove T.L t T.n₀ F := isCubicTorusAbove_of_top (by omega) hF
  have hs : ∀ i, 2 * R + 2 < F.extent i := fun i => by rw [hsn i]; omega
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hper' : ∀ i, 2 * r + 2 < F.period F.depth i := fun i => by
    rw [period_depth, hsn i, hFL]
    nlinarith
  have hper : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hper' i; omega
  have hT : ∀ b, b ∈ fineBonds F := fun b =>
    Finset.mem_product.mpr ⟨hcover F hodd hpos _, Finset.mem_univ _⟩
  have hch : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d ht => by
    simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hcover F hodd hpos _, hcover F hodd hpos _⟩, ht⟩
  have hσ := hd.σ_pos
  have hE1 := hd.one_le_E
  have hE0 : 0 ≤ T.E := by linarith
  have hδ : 0 ≤ T.decayRate := by
    have := hd.κ_pos
    unfold StepParameters.decayRate
    positivity
  have hEE : T.E ≤ T.energyRatio := by
    unfold StepParameters.energyRatio
    rw [le_div_iff₀ hd.η₃_pos]
    nlinarith [hd.η₃_le_one, hd.η₃_pos]
  have hfac := frameFacts_of_top hends T t x star V hx hF hV (hfb t x hx) hft
  have hfacT := frameFacts_of_top hends T t x true V hx hF hV (hfb t x hx) hft
  have hflat : IsSmallCurvature (5 / 4 * T.σ) (uniformField F F.top) :=
    isSmallCurvature_uniform_top (by positivity)
  have hfac0 := frameFacts_of_top hends T t x true (uniformField F F.top) hx hF hflat (hfb t x hx) hft
  have hflatT : IsSmallCurvature T.σ (uniformField F F.depth) := isSmallCurvature_uniform_depth hσ
  have hchain : IsBlockTorus T.L F := ⟨hFL, hcub⟩
  have hz := hzero F (frameRadius x) hchain
  have hstep0 := fieldAboveFrame_uniform (F := F) T.a T.chainParams.ρA (frameRadius x) hz
  have hdata := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.σ / 64) =>
    exists_cutoff_flow hcover hfield hgeo p10 hσ hnum.cut_radius hn6 hcut star x V Y η hFL hodd hL3 hcub hs hper'
      hfac hη hn
  have hεcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.σ / 64) →
      IsSmallCurvature T.σ (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η) := fun η hη p hp =>
    (hfac.small_curvature η hη p hp).trans (by linarith)
  have hηle : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ b, ‖η b‖ ≤ T.σ / 64 :=
    fun η h b => (h b).le
  have hG0 : ∀ u : ℝ, 0 < torusDecayFactor T.L T.decayRate u := fun u => by
    have h1 : (1 : ℝ) ≤ max 1 ((u / (T.L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
    exact mul_pos (lt_of_lt_of_le one_pos h1) (Real.exp_pos _)
  have hεsum : ∀ (B : F.Site F.depth → Fin 4 → imaginaryQuaternions),
      ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * T.σ →
      3 * T.E / torusDecayFactor T.L T.decayRate r + Cc * T.energyRatio * ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ ε₁ :=
    fun B hB => by
      have hE3 : 0 ≤ T.energyRatio := hE0.trans hEE
      refine le_trans ?_ hnum.value_bound
      rw [hFL] at hB
      gcongr
  have hq : (F.blockSide : ℝ) = T.L := by rw [hFL]
  have hsmooth : ∀ (st : Bool) (V' : F.GaugeField F.top) (_ : IsSmallCurvature (5 / 4 * T.σ) V')
      (y : F.Site F.depth)
      (η : StepVariable (finiteCells F)) (_ : ∀ b, ‖η b‖ ≤ T.ballRadius) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), k ≤ 3 → ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
        centredExpansion st T.a T.chainParams.ρA (frameRadius x) f y η (leftTranslate (bondSpread c X τ) V')) 0 := by
    intro st V' hV' y η hη k c X hk
    have h1 := hbd t x f F V' st hx hf hF hV' y η k c X hη
    have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ((τ, η) : (Fin k → ℝ) × StepVariable (finiteCells F))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h3 := ContDiffAt.comp (0 : Fin k → ℝ) h1 h2
    exact h3.of_le (by exact_mod_cast hk)
  have hM1 : M 1 * (Cg * (F.blockSide : ℝ) ^ 4) ≤ Kc := by
    refine le_trans ?_ hnum.motion_bound
    rw [hq]
    have hCgL : 0 ≤ Cg * (T.L : ℝ) ^ 4 := by
      have := hCg F hodd hcub 0
      rw [hq] at this
      exact (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans this
    nlinarith [p9 2]
  have hM2 : M 2 * (Cg * (F.blockSide : ℝ) ^ 4) ≤ Kc := by
    refine le_trans ?_ hnum.motion_bound
    rw [hq]
    have hCgL : 0 ≤ Cg * (T.L : ℝ) ^ 4 := by
      have := hCg F hodd hcub 0
      rw [hq] at this
      exact (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans this
    nlinarith [p9 1]
  refine ⟨fun η hη => ?_, fun η c X hη hX hdc => ?_, fun η c X hη hX hdc => ?_⟩
  · obtain ⟨B, hB1, hB2, hB3⟩ := hdata η (hηle η hη)
    have hW := hεcold η (hηle η hη)
    unfold cellCentredExpansion
    have h1 := abs_sum_block_le hodd hs2 Y
      (fun y => centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η V) p8
      (fun y hy => by
        have a := abs_subtractTrivial_le hr hf hlow hδ hE0 hEE hT y _ B hW hB1 (hB2 y hy)
        refine a.trans (le_trans ?_ (hεsum B hB3))
        refine add_le_add ?_ le_rfl
        have hg := hG0 (r : ℝ)
        gcongr
        linarith)
    rw [hq] at h1
    exact h1.trans hnum.zeroth
  · obtain ⟨B, hB1, hB2, hB3⟩ := hdata η (hηle η hη)
    have hW := hεcold η (hηle η hη)
    obtain ⟨α, h0, hc, hid, hP⟩ := exists_motion hm hends hρ0 hρ1 hκ.le hfac η (hηle η hη) c X hX hper hch
    have hKα : ∑ b ∈ fineBonds F, ‖motionComponent α ![0] b.1 b.2‖ ≤ Kc :=
      (sum_fineBonds_le hκ (p9 1) hCg hodd hcub (c 0).1 _ fun b => hP 1 ![0] b.1 b.2 0 (by norm_num)).trans hM1
    rw [bondDeriv_cellCentredExpansion star _ _ _ f Y η V c X
      (fun y => hsmooth star V hV y η (fun b => (hη b).le) 1 c X (by norm_num))]
    have h1 := abs_sum_block_le hodd hs2 Y
      (fun y => bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X)
      (mul_nonneg p8 p6) (fun y hy => by
        have a := (site_comparison htwo hfl1 hent hf hlow hσ hδ hE0 hEE p6 p7 hT y _ B hW hflatT hB1 (hB2 y hy) p8
          (hεsum B hB3)).1 α h0 hc hKα
        have e : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
          funext l; fin_cases l; rfl
        show |bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X| ≤ _
        rw [bondDeriv_centredExpansion_eq star _ _ _ f y η V c X α hid, e]
        exact a)
    rw [hq] at h1
    exact h1.trans hnum.first
  · obtain ⟨B, hB1, hB2, hB3⟩ := hdata η (hηle η hη)
    have hW := hεcold η (hηle η hη)
    have hη' := hηle η hη
    have hz0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.σ / 64 := fun b => by
      simp only [Pi.zero_apply, norm_zero]
      positivity
    obtain ⟨α, h0, hc, hid, hP⟩ := exists_motion hm hends hρ0 hρ1 hκ.le hfac η hη' c X hX hper hch
    obtain ⟨α₀, h00, hc0, hid0, hP0⟩ := exists_motion hm hends hρ0 hρ1 hκ.le hfac0 0 hz0 c X hX hper hch
    have hid0' := hid0
    rw [hstep0] at hid0'
    have hKa : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2‖ ≤ Kc := fun l =>
      (sum_fineBonds_le hκ (p9 1) hCg hodd hcub (c l).1 _ fun b => hP 1 ![l] b.1 b.2 0 (by norm_num)).trans hM1
    have hKb : ∀ l, ∑ b ∈ fineBonds F, ‖motionComponent α₀ ![l] b.1 b.2‖ ≤ Kc := fun l =>
      (sum_fineBonds_le hκ (p9 1) hCg hodd hcub (c l).1 _ fun b => hP0 1 ![l] b.1 b.2 0 (by norm_num)).trans hM1
    have hK01 : ∑ b ∈ fineBonds F, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ Kc :=
      (sum_fineBonds_le hκ (p9 2) hCg hodd hcub (c 0).1 _ fun b => hP 2 ![0, 1] b.1 b.2 0 (by norm_num)).trans hM2
    obtain ⟨_, _, hsym, htri, _⟩ := hgeo.1 F hodd hcub
    have hnear : ∀ (l : Fin 2) (b : F.Site F.depth × Fin 4), cellSupDist (enclosingCell b.1) (c l).1 ≤ R₃ →
        ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖ ≤
          CΘ * ((T.Ct + 1) * T.σ) * (K₁ + 1) + εR + ωb := by
      intro l b hD
      obtain ⟨xb, ib⟩ := b
      have hεb0 : 0 ≤ CΘ * ((T.Ct + 1) * T.σ) * (K₁ + 1) + εR + ωb := by positivity
      by_cases ht : IsAxialTreeBond (xb, ib)
      · have z1 := motionComponent_tree hC (fun V' => coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V' η) V
          α c X l xb ib ht h0 (hc xb ib) hid
        have z2 := motionComponent_tree hC (fun V' => coordsAboveFrame true T.a T.chainParams.ρA (frameRadius x) V' 0)
          (uniformField F F.top) α₀ c X l xb ib ht h00 (hc0 xb ib) hid0
        show ‖motionComponent α ![l] xb ib - motionComponent α₀ ![l] xb ib‖ ≤ _
        rw [z1, z2, sub_zero, norm_zero]
        exact hεb0
      · have hb := hch _ ht
        have hw : ContDiffAt ℝ 3 (fun τ => coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x)
            (leftTranslate (bondSpread c X τ) V) η xb ib) 0 :=
          ((hfac.analytic _ hb 2 c X).contDiffAt).add contDiffAt_const
        have hw0 : ContDiffAt ℝ 3 (fun τ => coordsAboveFrame true T.a T.chainParams.ρA (frameRadius x)
            (leftTranslate (bondSpread c X τ) (uniformField F F.top)) 0 xb ib) 0 :=
          ((hfac0.analytic _ hb 2 c X).contDiffAt).add contDiffAt_const
        have hu := norm_coordsAboveFrame_le star T.a T.chainParams.ρA T.σ (frameRadius x) V η hρ0 hρ1
          hfac.norm_add_le
          hη' xb ib
        have hu0 : coordsAboveFrame true T.a T.chainParams.ρA (frameRadius x) (uniformField F F.top) 0 xb ib = 0 := by
          show stepFrame true T.a T.chainParams.ρA (frameRadius x) (xb, ib) (uniformField F F.top) +
            stepCoordinates 0 xb ib = 0
          rw [hz, stepCoordinates_zero, add_zero]
        have eS : bondDeriv (fun V' => coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V' η xb ib) V
            ![c l] ![X l] =
            bondDeriv (stepFrame star T.a T.chainParams.ρA (frameRadius x) (xb, ib)) V ![c l] ![X l] :=
          bondDeriv_add_const _ (stepCoordinates η xb ib) V (c l) (X l)
        have eT : bondDeriv (fun V' => coordsAboveFrame true T.a T.chainParams.ρA (frameRadius x) V' 0 xb ib)
            (uniformField F F.top) ![c l] ![X l] =
            bondDeriv (stepFrame true T.a T.chainParams.ρA (frameRadius x) (xb, ib)) (uniformField F F.top)
              ![c l] ![X l] :=
          bondDeriv_add_const _ (stepCoordinates 0 xb ib) _ (c l) (X l)
        have hX1 : AreUnitVectors ![X l] := fun l' => by
          fin_cases l'
          exact hX l
        have hK : ‖bondDeriv (fun V' => coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V' η xb ib) V
            ![c l] ![X l]‖ ≤ K₁ := by
          rw [eS]
          have a1 := hfac.deriv_le _ hb 1 ![c l] ![X l] le_rfl hX1
          refine a1.trans ?_
          have hexp : Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell (xb, ib).1) ![c l])) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by
              have : 0 ≤ T.chainParams.κ₂ * (bondListDistance (enclosingCell (xb, ib).1) ![c l] : ℝ) := by positivity
              linarith)
          have hk := hnum.first_deriv
          have hk0 := hnum.first_deriv_nonneg
          have e16 : (16 : ℝ) ^ 1 * T.chainParams.Kk 1 = 16 * T.chainParams.Kk 1 := by ring
          rw [e16]
          have : 16 * T.chainParams.Kk 1 *
              Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell (xb, ib).1) ![c l])) ≤
              16 * T.chainParams.Kk 1 * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
          linarith
        have hsz : ‖coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η xb ib‖ ≤ (T.Ct + 1) * T.σ := by
          have e : stepCoordinates η xb ib = toImaginary (η ⟨(xb, ib), hb⟩) := by
            simp only [stepCoordinates]
            rw [dif_pos hb]
          have h1 := hfac.norm_le _ hb
          have h2 : ‖stepCoordinates η xb ib‖ ≤ T.σ / 64 := by rw [e, norm_toImaginary]; exact hη' _
          have h3 := norm_add_le (stepFrame star T.a T.chainParams.ρA (frameRadius x) (xb, ib) V)
            (stepCoordinates η xb ib)
          show ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) (xb, ib) V + stepCoordinates η xb ib‖ ≤ _
          nlinarith
        have key := motionComponent_close p2 hC
          (fun V' => coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V' η)
          (fun V' => coordsAboveFrame true T.a T.chainParams.ρA (frameRadius x) V' 0) V α α₀ c X l xb ib ht hX h0 h00
          (hc xb ib) (hc0 xb ib) hw hw0 hu hu0 hK hid hid0
        have hs0 : 0 ≤ segmentEnd star := by unfold segmentEnd; split_ifs <;> norm_num
        have hs1 : segmentEnd star ≤ 1 := by unfold segmentEnd; split_ifs <;> norm_num
        have hleast : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
            1 ≤ k → k ≤ 3 → AreUnitVectors X' →
            ‖bondDeriv (frameGap T.a T.chainParams.ρA (frameRadius x) (xb, ib)) V c' X'‖ ≤ ωb := by
          intro k c' X' h1 h3 hX'
          have a1 := ((hfb t x hx).single F V (segmentEnd star) hF hV hs0 hs1).1.deriv_decay _ hb k c' X' h1 h3 hX'
          refine a1.trans (le_trans ?_ (hω x hx))
          have hg : 0 ≤ frameGapBound T (frameRadius x) := by
            unfold frameGapBound
            positivity
          refine mul_le_of_le_one_right hg (Real.exp_le_one_iff.mpr ?_)
          have hδ2 : 0 ≤ T.chainParams.δ₂ := hd.chain_admissible.classical.1.2.2.2.1.le
          have : 0 ≤ T.chainParams.δ₂ / 4 * (bondListDistance (enclosingCell (xb, ib).1) c' : ℝ) := by positivity
          linarith
        have hdl : cellSupDist Y (c l).1 ≤ T.blockIndex :=
          le_trans (Finset.le_sup (f := fun l : Fin 2 => cellSupDist Y (c l).1) (Finset.mem_univ l)) hdc
        have hn5 := hnum.block_radius
        have hdist : 4 * cellSupDist Y (enclosingCell xb) ≤ R := by
          have h1 := htri Y (c l).1 (enclosingCell xb)
          have h2 := hsym (c l).1 (enclosingCell xb)
          have h3 : cellSupDist (enclosingCell xb) (c l).1 ≤ R₃ := hD
          omega
        have hrs := hresp F V Y hchain hs hV hn (xb, ib) (c l) (X l) hb hdist (by omega) (hX l)
        have hfr := stepFrame_response_le hb (hX l) hfacT hfac hleast hrs p4
        rw [eS, eT] at key
        have hmul : CΘ * ‖coordsAboveFrame star T.a T.chainParams.ρA (frameRadius x) V η xb ib‖ * (K₁ + 1) ≤
            CΘ * ((T.Ct + 1) * T.σ) * (K₁ + 1) := by gcongr
        show ‖motionComponent α ![l] xb ib - motionComponent α₀ ![l] xb ib‖ ≤ _
        linarith
    have hfar : ∀ (l : Fin 2) (b : F.Site F.depth × Fin 4),
        ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖ ≤
          2 * (2 * M 1) * Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) (c l).1)) := by
      intro l b
      have a1 : ‖motionComponent α ![l] b.1 b.2‖ ≤
          M 1 * Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) (c l).1)) :=
        hP 1 ![l] b.1 b.2 0 (by norm_num)
      have a2 : ‖motionComponent α₀ ![l] b.1 b.2‖ ≤
          M 1 * Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) (c l).1)) :=
        hP0 1 ![l] b.1 b.2 0 (by norm_num)
      have a3 := norm_sub_le (motionComponent α ![l] b.1 b.2) (motionComponent α₀ ![l] b.1 b.2)
      have a4 : 0 ≤ M 1 * Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) (c l).1)) :=
        mul_nonneg (p9 1) (Real.exp_pos _).le
      nlinarith
    have hμ : ∀ l : Fin 2,
        ∑ b ∈ fineBonds F, ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖ ≤ μ := by
      intro l
      have h := sum_fineBonds_split_le (κ := T.chainParams.κ₂) (Cg := Cg₂)
        (εb := CΘ * ((T.Ct + 1) * T.σ) * (K₁ + 1) + εR + ωb)
        (M₁ := 2 * M 1) (R₃ := R₃) hκ (by positivity) (by have := p9 1; positivity) hCg₂ hodd hcub (c l).1
        (fun b => ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖) (hnear l) (hfar l)
      rw [hq] at h
      exact h.trans hnum.gap_bound
    have hzρ : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by
      simp only [Pi.zero_apply, norm_zero]
      unfold StepParameters.ballRadius
      positivity
    rw [bondDeriv_cellCentredExpansion star _ _ _ f Y η V c X
        (fun y => hsmooth star V hV y η (fun b => (hη b).le) 2 c X (by norm_num)),
      bondDeriv_cellCentredExpansion true _ _ _ f Y 0 (uniformField F F.top) c X
        (fun y => hsmooth true _ hflat y 0 hzρ 2 c X (by norm_num)), ← Finset.sum_sub_distrib]
    have e : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l; fin_cases l <;> rfl
    have h1 := abs_sum_block_le hodd hs2 Y
      (fun y => bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X -
        bondDeriv (centredExpansion true T.a T.chainParams.ρA (frameRadius x) f y 0) (uniformField F F.top) c X)
      (q := ε₁ * (Kc ^ 2 + Kc) + 2 * T.E * Kc * μ) (by positivity) (fun y hy => by
        have a := (site_comparison htwo hfl1 hent hf hlow hσ hδ hE0 hEE p6 p7 hT y _ B hW hflatT hB1 (hB2 y hy) p8
          (hεsum B hB3)).2 α α₀ h0 h00 hc hc0 hKa hKb hK01 hμ
        show |bondDeriv (centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η) V c X -
          bondDeriv (centredExpansion true T.a T.chainParams.ρA (frameRadius x) f y 0) (uniformField F F.top) c X| ≤ _
        rw [bondDeriv_centredExpansion_eq star _ _ _ f y η V c X α hid,
          bondDeriv_centredExpansion_eq true _ _ _ f y 0 _ c X α₀ hid0, hstep0, e]
        exact a)
    rw [hq] at h1
    exact h1.trans hnum.second
theorem final_constants {L4 Kc G₁ G₂ E ε₀ : ℝ} (hL : 0 < L4) (hK : 0 ≤ Kc) (hG1 : 0 < G₁) (hG : G₁ ≤ G₂)
    (hE : 0 ≤ E) (hε : ε₀ = 2⁻¹ ^ 14 / (L4 * (1 + Kc) ^ 2 * G₂)) :
    L4 * (ε₀ * E) ≤ 2⁻¹ ^ 8 * E / G₁ ∧ L4 * ((ε₀ * E) * Kc) ≤ 2⁻¹ ^ 10 * E / G₂ ∧
      L4 * ((ε₀ * E) * (Kc ^ 2 + Kc) + 2 * E * Kc * ε₀) ≤ 2⁻¹ ^ 10 * E / G₂ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.final_constants_le <;> assumption
theorem stepFrame_uniform_eq_zero {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hc : c.Admissible a L)
    (F : BlockFrame) (m : ℕ) (hF : IsBlockTorus L F)
    (b : F.Site F.depth × Fin 4) : stepFrame true a c.ρA m b (uniformField F F.top) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.stepFrame_uniform_eq_zero <;> assumption
def ComparisonData (Cc CΘ : ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∃ (R R₁ R₂ R₃ r : ℕ) (A Cg Cg₂ εR ωb K₁ Kc μ ε₁ : ℝ) (M : ℕ → ℝ),
    ComparisonConstants T R R₁ R₂ R₃ r Cc A Cg Cg₂ CΘ εR ωb K₁ Kc μ ε₁ M ∧
    MotionEstimate (fun k => 16 ^ k * T.chainParams.Kk k) M ∧
    (∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) z)) ≤
        Cg * (G.blockSide : ℝ) ^ 4) ∧
    (∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell b.1) z)) ≤
        Cg₂ * (G.blockSide : ℝ) ^ 4) ∧
    (∀ x : ℝ, T.coupling ≤ x → frameGapBound T (frameRadius x) ≤ ωb) ∧
    (∀ (F : BlockFrame) (W : F.GaugeField F.depth) (Y : F.Cell), Odd F.blockSide → 3 ≤ F.blockSide →
      IsLargeCubicTorus F → IsSmallCurvature (3 / 4 * T.σ) W →
      (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₂ + 2 →
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W b.1 b.2) ≤ (T.Ct + 5) * (1 + cellSupDist (enclosingCell b.1) Y) * T.σ) →
      ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature T.σ (expFlow B (uniformField F F.depth) u)) ∧
        (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
          expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2) ∧
        ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * T.σ) ∧
    (∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), IsBlockTorus T.L F →
      (∀ i, 2 * R + 2 < F.extent i) →
      IsSmallCurvature (5 / 4 * T.σ) V → IsNearUniformAbout (5 / 4 * T.σ) R V Y →
      ∀ (b : F.Site F.depth × Fin 4) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
        b ∈ chordBonds (finiteCells F) → 4 * cellSupDist Y (enclosingCell b.1) ≤ R →
        4 * cellSupDist Y e.1 ≤ R → ‖X‖ = 1 →
        ‖bondDeriv (torusCoordinate T.a T.chainParams.ρA b) V ![e] ![X] -
          bondDeriv (torusCoordinate T.a T.chainParams.ρA b) (uniformField F F.top) ![e] ![X]‖ ≤ εR)
theorem exists_exp_tail_le {c q ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ n : ℕ, q * Real.exp (-(c * (n : ℝ))) ≤ ε := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.exists_mul_exp_neg_le <;> assumption
theorem exists_torusDecayFactor_large {L : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hL : 1 ≤ L) :
    ∃ R₁ : ℕ, 4 ≤ R₁ ∧ 3 / torusDecayFactor L δ ((L * (R₁ - 1) : ℕ) : ℝ) ≤ ε := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.exists_torusDecayFactor_large <;> assumption
theorem le_frameRadius (m₀ : ℕ) (x : ℝ) (h : (((2 ^ 11 * m₀ : ℕ) : ℝ)) ^ 100 ≤ x) : m₀ ≤ frameRadius x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.le_frameRadius <;> assumption
theorem value_constant_le {E η G Cc A L4 σ ε : ℝ} (hE : 0 ≤ E) (hη : 0 < η) (hG : 0 < G) (hCc : 0 ≤ Cc)
    (hA : 0 ≤ A) (hL : 0 ≤ L4)
    (hσ : 0 < σ) (hε : 0 < ε) (h1 : 3 / G ≤ ε / 2) (h2 : σ ≤ ε / 2 * η / (Cc * A * L4 + 1)) :
    3 * E / G + Cc * (E / η) * (A * L4 * σ) ≤ ε * E := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.entry_constant_le <;> assumption
theorem gap_constant_le {CΘ Ct σ K₁ ε₃ eR Q t ε₀ : ℝ} (hC : 0 ≤ CΘ) (hCt : 0 ≤ Ct) (hK : 0 ≤ K₁) (hσ : 0 < σ)
    (hε₃ : 0 < ε₃) (he : 0 < eR) (hQ : 0 ≤ Q)
    (h1 : σ ≤ ε₃ / (3 * (CΘ * (Ct + 1) * (K₁ + 1) + 1))) (h2 : ε₃ * (eR * Q) ≤ ε₀ / 2) (h3 : t * Q ≤ ε₀ / 2) :
    ((CΘ * ((Ct + 1) * σ) * (K₁ + 1) + ε₃ / 3 + ε₃ / 3) * eR + t) * Q ≤ ε₀ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.gap_constant_le <;> assumption
set_option maxHeartbeats 4000000 in
theorem eventually_comparisonData (hmot : motionAboveFrameStatement) (hgeo : CubicTorusCellGeometry)
    (hcutS : CutoffNearFlatField) (hrespS : DerivsNearUniformTop) {Cc CΘ : ℝ} (hCc : 0 ≤ Cc)
    (hCΘ : 0 ≤ CΘ) : EventuallyInParameters (ComparisonData Cc CΘ) := by
  intro a ha
  refine ⟨3, fun L hLo hL c hc => ?_⟩
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ₂, hκ₂c, hK, hC1, hKk⟩, _⟩ := hc.classical
  have hκ₂ : 0 < c.κ₂ := by nlinarith
  obtain ⟨M, hM0, hm0⟩ := hmot 3 (fun k => 16 ^ k * c.Kk k) (fun k => mul_nonneg (by positivity) (hKk k).le)
  have hm : MotionEstimate (fun k => 16 ^ k * c.Kk k) M :=
    fun F s a' ρA r m p V η w h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨α, a0, ac, _, ai, ap, _⟩ := hm0 F s a' ρA r m p V η w h1 h2 h3 (fun x i _ => h4 x i) h5 h6 h7
      exact ⟨α, a0, fun x i => by exact_mod_cast ac x i, ai, ap⟩
  obtain ⟨Cg, hCgp, hCg⟩ := hgeo.2 c.κ₂ hκ₂
  obtain ⟨Cg₂, hCg₂p, hCg₂⟩ := hgeo.2 (c.κ₂ / 2) (by positivity)
  have hLp : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  set L4 : ℝ := (L : ℝ) ^ 4 with hL4
  have hL4p : 0 < L4 := by positivity
  set Kc : ℝ := (M 1 + M 2) * (Cg * L4) with hKcdef
  have hKc : 0 ≤ Kc := mul_nonneg (add_nonneg (hM0 1) (hM0 2)) (by positivity)
  set K₁ : ℝ := 16 * c.Kk 1 with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (by norm_num) (hKk 1).le
  refine ⟨0, fun Ct hCt => ?_⟩
  refine ⟨1, one_pos, fun κ hκ _ => ?_⟩
  refine ⟨1, one_pos, fun η₃ hη hη1 _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  have hδ : 0 < κ / 2 ^ 10 := by positivity
  set G₂ : ℝ := torusDecayFactor L (κ / 2 ^ 10) (2 * nss) with hG₂
  have hG₂p : 0 < G₂ := by
    rw [hG₂]
    unfold torusDecayFactor
    have h1 : (1 : ℝ) ≤ max 1 ((2 * (nss : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
    exact mul_pos (lt_of_lt_of_le one_pos h1) (Real.exp_pos _)
  set ε₀ : ℝ := 2⁻¹ ^ 14 / (L4 * (1 + Kc) ^ 2 * G₂) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  obtain ⟨R₃, hR₃⟩ := exists_exp_tail_le (c := c.κ₂ / 2) (q := 2 * (2 * M 1) * (Cg₂ * L4)) (ε := ε₀ / 2)
    (by positivity) (by positivity)
  set eR : ℝ := Real.exp (c.κ₂ / 2 * R₃) with heR
  have heRp : 0 < eR := Real.exp_pos _
  have hCL : 0 ≤ Cg₂ * L4 := by positivity
  set ε₃ : ℝ := ε₀ / (2 * (eR * (Cg₂ * L4) + 1)) with hε₃def
  have hε₃ : 0 < ε₃ := by positivity
  have hε₃b : ε₃ * (eR * (Cg₂ * L4)) ≤ ε₀ / 2 := by
    rw [hε₃def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg heRp.le hCL]
  obtain ⟨R₀, hR₀⟩ := hrespS a L c ha hLo hc (ε₃ / 3) (by positivity)
  obtain ⟨R₁, hR₁4, hR₁G⟩ := exists_torusDecayFactor_large (L := L) hδ (by positivity : 0 < ε₀ / 2) (by omega)
  obtain ⟨R₂, σc, A, hR₁₂, hσc, hA, hcut⟩ := hcutS (Ct + 5) R₁ (by linarith) hR₁4
  set R : ℕ := max R₀ (max (R₂ + 3) (4 * (nss + R₃ + 1))) with hRdef
  obtain ⟨σr, hσr, hresp⟩ := hR₀ R (le_max_left _ _)
  have hN1 : 0 < 2 * (Cc * A * L4 + 1) := by positivity
  have hN2 : 0 < 3 * (CΘ * (Ct + 1) * (K₁ + 1) + 1) := by positivity
  refine ⟨min (min 1 (min σc σr))
      (min (ε₀ / 2 * η₃ / (Cc * A * L4 + 1)) (ε₃ / (3 * (CΘ * (Ct + 1) * (K₁ + 1) + 1)))),
    by positivity, fun σ hσ hσ0 p hp => ?_⟩
  have hσa := hσ0.trans (min_le_right _ _)
  have hσb := hσ0.trans (min_le_left _ _)
  have hσ3 := hσa.trans (min_le_left _ _)
  have hσ4 := hσa.trans (min_le_right _ _)
  have hσ5 := hσb.trans (min_le_right _ _)
  have hσc' := hσ5.trans (min_le_left _ _)
  have hσr' := hσ5.trans (min_le_right _ _)
  refine ⟨0, fun Cs _ E hE => ?_⟩
  refine ⟨max 64 (4 * R + 8), fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  have hE0 : 0 ≤ E := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_exp_tail_le (c := c.δ₂ / 4) (q := Ct) (ε := ε₃ / 3) (by positivity) (by positivity)
  refine ⟨(((2 ^ 11 * m₀ : ℕ) : ℝ)) ^ 100, fun y₁ hy => ?_⟩
  have hn64 : 64 ≤ n₀ := (le_max_left _ _).trans hn₀
  have hn8 : 4 * R + 8 ≤ n₀ := (le_max_right _ _).trans hn₀
  have hR₂R : R₂ + 3 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR₅ : 4 * (nss + R₃ + 1) ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hG1 : 0 < torusDecayFactor L (κ / 2 ^ 10) (nss : ℝ) := by
    unfold torusDecayFactor
    have h1 : (1 : ℝ) ≤ max 1 (((nss : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
    exact mul_pos (lt_of_lt_of_le one_pos h1) (Real.exp_pos _)
  have hGle : torusDecayFactor L (κ / 2 ^ 10) (nss : ℝ) ≤ G₂ := by
    rw [hG₂]
    unfold torusDecayFactor
    have hn : 0 ≤ (L : ℝ) ^ (1 / 640 : ℝ) := by positivity
    have hx : (0 : ℝ) ≤ nss := by positivity
    have h1 : ((nss : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ (2 * (nss : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 :=
      pow_le_pow_left₀ (div_nonneg hx hn) (by gcongr; linarith) _
    have h2 : Real.exp (κ / 2 ^ 10 * nss) ≤ Real.exp (κ / 2 ^ 10 * (2 * nss)) :=
      Real.exp_le_exp.mpr (by gcongr; linarith)
    exact mul_le_mul (max_le_max le_rfl h1) h2 (Real.exp_pos _).le (le_trans zero_le_one (le_max_left _ _))
  obtain ⟨f4, f5, f6⟩ := final_constants (E := E) hL4p hKc hG1 hGle hE0 hε₀def
  have hGr : 0 < torusDecayFactor L (κ / 2 ^ 10) ((L * (R₁ - 1) : ℕ) : ℝ) := by
    unfold torusDecayFactor
    have h1 : (1 : ℝ) ≤ max 1 ((((L * (R₁ - 1) : ℕ) : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
    exact mul_pos (lt_of_lt_of_le one_pos h1) (Real.exp_pos _)
  have he1 := value_constant_le (E := E) (η := η₃) (Cc := Cc) (A := A) (L4 := L4) (σ := σ) (ε := ε₀) hE0 hη hGr
    hCc hA hL4p.le hσ hε₀ hR₁G hσ3
  have he3 := gap_constant_le (CΘ := CΘ) (Ct := Ct) (σ := σ) (K₁ := K₁) (ε₃ := ε₃) (eR := eR) (Q := Cg₂ * L4)
    (t := 2 * (2 * M 1) * Real.exp (-(c.κ₂ / 2 * R₃))) (ε₀ := ε₀) hCΘ hCt hK₁0 hσ hε₃ heRp hCL hσ4 hε₃b
    (by nlinarith [hR₃])
  have hn6 : L * (R₁ - 1) + L ≤ L * R₁ := by
    obtain ⟨q, rfl⟩ : ∃ q, R₁ = q + 1 := ⟨R₁ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_add, Nat.mul_one]
  refine ⟨R, R₁, R₂, R₃, L * (R₁ - 1), A, Cg, Cg₂, ε₃ / 3, ε₃ / 3, K₁, Kc, ε₀, ε₀ * E, M,
    ⟨hn8, hn64, hL, hR₂R, hR₅, hn6, by omega,
      ⟨hCc, hCΘ, by positivity, by positivity, hK₁0, hKc, hε₀.le, by positivity, hM0, hCt⟩,
      le_rfl, (hKk 1).le, he1, le_rfl, he3, f4, f5, f6⟩,
    hm, hCg, hCg₂, fun x hx => ?_, fun F W Y h1 h2 h3 h4 h5 => hcut σ F W Y hσ hσc' h1 h2 h3 h4 h5,
    fun F V Y h1 h2 h3 h4 b e X h5 h6 h7 h8 => hresp σ F V Y hσ hσr' h1 h2 h3 h4 b e X h5 h6 h7 h8⟩
  have hm₁ : m₀ ≤ frameRadius x := le_frameRadius m₀ x (hy.trans hx)
  show Ct * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))) ≤ ε₃ / 3
  refine le_trans ?_ hm₀
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCt
  have : (m₀ : ℝ) ≤ frameRadius x := by exact_mod_cast hm₁
  nlinarith
end NearUniformTopSteps
open NearUniformTopSteps
theorem familyNearUniformTop_proof (hcover : BlocksCoverLowerLevel)
    (hfield : ChartedFieldNearOne) (hgeo : CubicTorusCellGeometry)
    (htwo : SecondDerivAlongMotionsClose) (hg : GaugeCovarianceOfFrame)
    (hends : interpolationAtEndpoints) (hflow : DerivBoundAlongFlow)
    (hfirst : ConjugatedExpFirstOrder)
    (hmot : motionAboveFrameStatement) (hcutS : CutoffNearFlatField)
    (hrespS : DerivsNearUniformTop) (hfb : interpolatedFramesControlled)
    (hft : FrameBoundsEventually) (hbd : CentredExpansionContDiff)
    (hj : EventuallyInParametersCombines) : familyNearUniformTopStatement := by
  have hfl1 := firstOrderVanishesAtUniform_of_gauge hg
  obtain ⟨C₁, hC₁, hent⟩ := termDerivNearUniform_of_expansion (expansionDerivNearUniform_of_flow hflow)
  obtain ⟨C₂, hC₂, hr⟩ := expansionDerivNearUniform_of_flow hflow
  obtain ⟨CΘ, hCΘ, hC⟩ := hfirst
  have hQ := eventually_comparisonData hmot hgeo hcutS hrespS (Cc := C₁ + C₂) (add_nonneg hC₁ hC₂) hCΘ
  refine hj.2 _ _ (fun T hd h => ?_) (hj.1 _ _ hQ (hj.1 _ _ hfb (hj.1 _ _ hft hbd)))
  obtain ⟨⟨R, R₁, R₂, R₃, r, A, Cg, Cg₂, εR, ωb, K₁, Kc, μ, ε₁, M, hn, hm, hCg, hCg₂, hω, hcut, hresp⟩,
    hb, ht, hd'⟩ := h
  obtain ⟨⟨hρ0, hρ1, _, hδ₂, hκ₂c, _⟩, _⟩ := hd.chain_admissible.classical
  have hκ : 0 < T.chainParams.κ₂ := by nlinarith
  refine ⟨R, hn.top_radius, familyNearUniformTopAt_of_constants hcover hfield hgeo htwo hfl1 hends
    (fun L t n₀ σ δ E E₃ f F T' y W B r' k c X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      (hent L t n₀ σ δ E E₃ f F T' y W B r' k c X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (h4.trans h5))
          (Finset.sum_nonneg fun _ _ => norm_nonneg _))))
    (fun L t n₀ σ δ E E₃ f F T' y W B r' k h' X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      (hr L t n₀ σ δ E E₃ f F T' y W B r' k h' X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (h4.trans h5))
          (Finset.sum_nonneg fun _ _ => norm_nonneg _))))
    hC hm hCg hCg₂ hn hd hκ hρ0.le hρ1 hb ht hd' hω hcut hresp
    (fun F m hF b => stepFrame_uniform_eq_zero hd.chain_admissible F m hF b)⟩
end YangMills.Construction.ResponseInTheExpansion
end
