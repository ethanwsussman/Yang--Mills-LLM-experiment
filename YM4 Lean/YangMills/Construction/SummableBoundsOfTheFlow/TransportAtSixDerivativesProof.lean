import YangMills.Construction.SummableBoundsOfTheFlow.TopOrderNearTheBlockProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates YangMills.Construction.SummableBounds
namespace YangMills.Construction.Interpolation
namespace TransportBounds
theorem eventuallyInParameters_map₂ {P Q R : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop} (h : ∀ T, P T → Q T → R T)
    (hP : EventuallyInParameters P) (hQ : EventuallyInParameters Q) : EventuallyInParameters R := by apply _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.eventuallyInParameters_map₂ <;> assumption
structure StandingBounds (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  odd : Odd T.L
  L_ge : 2 ^ 40 ≤ T.L
  admissible : T.chainParams.Admissible T.a T.L
  κ_pos : 0 < T.κ
  κ_le : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂
  σ_pos : 0 < T.σ
  n₀_ge : 64 ≤ T.n₀
theorem eventually_standingBounds : EventuallyInParameters StandingBounds := by
  intro a ha
  refine ⟨2 ^ 40, fun L hodd hL c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hκ₂ : 2 ^ 6 * c.δ₂ ≤ c.κ₂ := hc.classical.1.2.2.2.2.1
  have hpos : 0 < c.κ₂ := by nlinarith
  refine ⟨0, fun Ct _ => ⟨c.κ₂ / 2 ^ 9, by positivity, fun κ hκ hκ₀ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ⟨0, fun y _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨hodd, hL, hc, hκ, ?_, hσ, hn₀⟩
  show 2 ^ 9 * κ ≤ c.κ₂
  have : κ ≤ c.κ₂ / 2 ^ 9 := hκ₀
  nlinarith
theorem exists_decay_threshold (A κ : ℝ) (L : ℕ) (hκ : 0 < κ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    A * Real.exp (-(2 ^ 7 * κ * n)) * torusDecayFactor L (κ / 2 ^ 10) n ≤ 1 / 8 := by
  set δ : ℝ := κ / 2 ^ 10 with hδ
  set b : ℝ := 2 ^ 7 * κ - δ with hb
  have hb0 : 0 < b := by
    simp only [hb, hδ]
    nlinarith
  set n₁ : ℝ := (L : ℝ) ^ (1 / 640 : ℝ) with hn₁
  set c : ℝ := (n₁⁻¹) ^ 16000 with hc
  have t0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb0
  have t1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 16000 b hb0
  have T : Filter.Tendsto (fun x : ℝ => |A| * (x ^ (0 : ℝ) * Real.exp (-b * x) +
      c * (x ^ (16000 : ℝ) * Real.exp (-b * x)))) Filter.atTop (𝓝 0) := by
    simpa using (t0.add (t1.const_mul c)).const_mul |A|
  have hev := T.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  have hev' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev'
  refine ⟨N, fun n hn => ?_⟩
  have h1 : _ < (1 : ℝ) / 8 := hN n hn
  have hr : ((n : ℝ)) ^ (16000 : ℝ) = (n : ℝ) ^ 16000 := by
    rw [show (16000 : ℝ) = ((16000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr, Real.rpow_zero, one_mul] at h1
  have hG : torusDecayFactor L δ n ≤ (1 + c * (n : ℝ) ^ 16000) * Real.exp (δ * n) := by
    rw [torusDecayFactor]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hu : ((n : ℝ) / n₁) ^ 16000 = c * (n : ℝ) ^ 16000 := by
      rw [hc, div_eq_mul_inv, mul_pow, mul_comm]
    have h0 : 0 ≤ c * (n : ℝ) ^ 16000 := by
      rw [← hu]
      exact Even.pow_nonneg (by decide) _
    rw [hu]
    exact max_le (by linarith) (by linarith)
  have hE : Real.exp (-(2 ^ 7 * κ * n)) * Real.exp (δ * n) = Real.exp (-b * n) := by
    rw [← Real.exp_add]
    congr 1
    simp only [hb]
    ring
  have hG0 : 0 ≤ torusDecayFactor L δ n := by
    rw [torusDecayFactor]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
  calc A * Real.exp (-(2 ^ 7 * κ * n)) * torusDecayFactor L δ n
      ≤ |A| * Real.exp (-(2 ^ 7 * κ * n)) * torusDecayFactor L δ n := by
        gcongr
        exact le_abs_self A
    _ ≤ |A| * Real.exp (-(2 ^ 7 * κ * n)) * ((1 + c * (n : ℝ) ^ 16000) * Real.exp (δ * n)) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = |A| * ((1 + c * (n : ℝ) ^ 16000) * (Real.exp (-(2 ^ 7 * κ * n)) * Real.exp (δ * n))) := by ring
    _ = |A| * (Real.exp (-b * n) + c * ((n : ℝ) ^ 16000 * Real.exp (-b * n))) := by rw [hE]; ring
    _ ≤ 1 / 8 := h1.le
variable {F : BlockFrame}
def concatPerturbations {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) : Fin (l + j) → Perturbation F :=
  Fin.addCases (fun p => Perturbation.bulk (b p) (u p)) fun q => Perturbation.top (c q) (X q)
theorem perturbedTop_concatPerturbations {l j : ℕ} (V : F.GaugeField F.top)
    (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) :
    perturbedTop V (concatPerturbations b u c X) τ =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i)) V := by
  simp only [perturbedTop]
  congr 1
  funext y d
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [Fin.sum_univ_add]
  simp [concatPerturbations, Perturbation.topDirection, Perturbation.topBond]
theorem perturbedVariable_concatPerturbations {l j : ℕ} (η : StepVariable (finiteCells F))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) :
    perturbedVariable η (concatPerturbations b u c X) τ =
      displacedPoint η b u fun i => τ (Fin.castAdd j i) := by
  classical
  simp only [perturbedVariable, displacedPoint]
  rw [Fin.sum_univ_add]
  simp [concatPerturbations, Perturbation.variableDirection, Pi.single_smul]
theorem perturbationCells_concatPerturbations {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) :
    perturbationCells (concatPerturbations b u c X) = chordBondCells b ∪ topBondCells c := by
  ext z
  simp only [perturbationCells, chordBondCells, topBondCells, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left p => left; exact ⟨p, by simp [concatPerturbations, Perturbation.cell]⟩
    | right q => right; exact ⟨q, by simp [concatPerturbations, Perturbation.cell]⟩
  · rintro (⟨p, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨Fin.castAdd j p, by simp [concatPerturbations, Perturbation.cell]⟩
    · exact ⟨Fin.natAdd l q, by simp [concatPerturbations, Perturbation.cell]⟩
theorem isUnit_concatPerturbations {l j : ℕ} {b : Fin l → ↥(chordBonds (finiteCells F))}
    {u : Fin l → EuclideanSpace ℝ (Fin 3)} {c : Fin j → F.Site F.top × Fin 4}
    {X : Fin j → imaginaryQuaternions}
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (i : Fin (l + j)) :
    (concatPerturbations b u c X i).IsUnit := by
  induction i using Fin.addCases with
  | left p => simpa [concatPerturbations, Perturbation.IsUnit] using hu p
  | right q => simpa [concatPerturbations, Perturbation.IsUnit] using hX q
theorem jointDisplacement_interpolatedExpansion {l j : ℕ} (s a ρA : ℝ) (m : ℕ) (f : LocalFamily)
    (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) :
    jointDisplacement (interpolatedExpansion s a ρA m f y) η V b u c X =
      fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
        (perturbedField s a ρA m V η (concatPerturbations b u c X) τ) := by
  funext τ
  simp only [jointDisplacement, interpolatedExpansion, perturbedField, perturbedTop_concatPerturbations,
    perturbedVariable_concatPerturbations]
def topPerturbations {j : ℕ} (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) :
    Fin j → Perturbation F :=
  fun q => Perturbation.top (c q) (X q)
theorem interpolatedExpansion_topPerturbations {j : ℕ} (s a ρA : ℝ) (m : ℕ) (f : LocalFamily)
    (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) :
    (fun τ : Fin j → ℝ => interpolatedExpansion s a ρA m f y η
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =
      fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
        (perturbedField s a ρA m V η (topPerturbations c X) τ) := by
  funext τ
  have h1 : perturbedVariable η (topPerturbations c X) τ = η := by
    simp [perturbedVariable, topPerturbations, Perturbation.variableDirection]
  simp only [interpolatedExpansion, perturbedField, h1]
  rfl
theorem bondSpan_le_cellSetDiameter {j : ℕ} (Y : F.Cell) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) :
    bondSpan Y c ≤ cellSetDiameter (insert Y (perturbationCells (topPerturbations c X))) := by
  have hmem : ∀ l, (c l).1 ∈ insert Y (perturbationCells (topPerturbations c X)) := fun l =>
    Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
  have hY : Y ∈ insert Y (perturbationCells (topPerturbations c X)) := Finset.mem_insert_self _ _
  have key : ∀ u ∈ insert Y (perturbationCells (topPerturbations c X)),
      ∀ v ∈ insert Y (perturbationCells (topPerturbations c X)),
      cellSupDist u v ≤ cellSetDiameter (insert Y (perturbationCells (topPerturbations c X))) :=
    fun u hu v hv =>
    (Finset.le_sup (f := fun v => cellSupDist u v) hv).trans
      (Finset.le_sup (f := fun u => (insert Y (perturbationCells (topPerturbations c X))).sup
        fun v => cellSupDist u v) hu)
  refine max_le (Finset.sup_le fun l _ => key _ hY _ (hmem l)) ?_
  exact Finset.sup_le fun l _ => Finset.sup_le fun l' _ => key _ (hmem l) _ (hmem l')
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem norm_interpolatedCoords_le {s a ρA ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ ≤ ρ)
    (hroom : ∀ d ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m d V‖ + ρ ≤ ρA)
    {x : F.Site F.depth} {i : Fin 4} (hd : (x, i) ∈ chordBonds (finiteCells F)) :
    ‖interpolatedCoords s a ρA m V η x i‖ ≤ ρA := by
  classical
  have h1 : stepCoordinates η x i = toImaginary (η ⟨(x, i), hd⟩) := by
    simp [stepCoordinates, hd]
  have h2 := hroom _ hd
  simp only [interpolatedCoords]
  refine (norm_add_le _ _).trans ?_
  rw [h1, norm_toImaginary]
  have := hη ⟨(x, i), hd⟩
  linarith
theorem iteratedFDeriv_finset_sum_zero {k : ℕ} {ι : Type} (u : Finset ι) (g : ι → (Fin k → ℝ) → ℝ)
    (hg : ∀ y ∈ u, ContDiffAt ℝ k (g y) 0) :
    iteratedFDeriv ℝ k (fun τ => ∑ y ∈ u, g y τ) 0 = ∑ y ∈ u, iteratedFDeriv ℝ k (g y) 0 := by apply _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.iteratedFDeriv_finset_sum_apply_zero <;> assumption
theorem runningMax_nonneg {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (p : ℕ) : 0 ≤ runningMax e p := by apply _root_.YangMills.Construction.Estimates.runningMax_nonneg <;> assumption
theorem exp_neg_rate_le_half {κ a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-(2 ^ 7 * κ * b)) ≤ Real.exp (-(2 ^ 6 * κ * a)) := by
  apply Real.exp_le_exp.2
  have h1 : 2 ^ 6 * κ * a ≤ 2 ^ 6 * κ * b := mul_le_mul_of_nonneg_left hab (by positivity)
  have h2 : 0 ≤ 2 ^ 6 * κ * b := mul_nonneg (by positivity) (ha.trans hab)
  linarith
theorem exp_neg_rate_antitone {κ a b : ℝ} (hκ : 0 ≤ κ) (hab : a ≤ b) :
    Real.exp (-(2 ^ 7 * κ * b)) ≤ Real.exp (-(2 ^ 7 * κ * a)) := by
  apply Real.exp_le_exp.2
  have h1 : 2 ^ 7 * κ * a ≤ 2 ^ 7 * κ * b := mul_le_mul_of_nonneg_left hab (by positivity)
  linarith
end TransportBounds
set_option maxHeartbeats 2000000 in
open TransportBounds in
theorem transportBoundsStatement_proof (hB : boundAlongPerturbationsStatement)
    (hD : interpolatedFrameDecayStatement) (hF : interpolatedFramesStatement)
    (hN : topOrderNearBlockStatement) (hcov : BlocksCoverLowerLevel)
    (hgeo : CubicTorusCellGeometry) : transportBoundsStatement := by
  classical
  let K' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T k => |16 ^ k * T.chainParams.Kk k|
  let Cond : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop := fun T =>
    0 < T.κ ∧ 2 ^ 9 * T.κ ≤ T.chainParams.κ₂ ∧ Odd T.L ∧ 2 ^ 40 ≤ T.L
  have hBex := fun (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (h : Cond T) =>
    hB (K' T) T.chainParams.κ₂ T.κ T.L (fun _ => abs_nonneg _) h.1 h.2.1 h.2.2.1 h.2.2.2
  let Cb : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => if h : Cond T then Classical.choose (hBex T h) else 1
  have hCb0 : ∀ T, 0 < Cb T := fun T => by
    by_cases h : Cond T
    · simp only [Cb, dif_pos h]
      exact (Classical.choose_spec (hBex T h)).1
    · simp [Cb, dif_neg h]
  obtain ⟨Cy, hCy, hcount⟩ := hgeo.2 1 one_pos
  let A : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => Cy * (T.L : ℝ) ^ 4
  let Nf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ := fun T =>
    if h : 0 < T.κ then Classical.choose (exists_decay_threshold (A T * Cb T) T.κ T.L h) else 0
  obtain ⟨Cn, hCn, hnear⟩ := hN
  let Ck : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T k => Cn T (Nf T) k + 1
  refine ⟨Cb, Ck, hCb0, fun T k => by have := hCn T (Nf T) k; positivity, ?_⟩
  obtain ⟨Cq, Cz', Cr, hFr⟩ := hF
  obtain ⟨Cz, -, hD'⟩ := hD
  have J := eventuallyInParameters_map₂
    (R := fun T => StandingBounds T ∧ InterpolatedFrameDecay T (Cz T.a T.L T.chainParams))
    (fun T a b => ⟨a, b⟩) eventually_standingBounds hD'
  have J2 := eventuallyInParameters_map₂
    (R := fun T => (StandingBounds T ∧ InterpolatedFrameDecay T (Cz T.a T.L T.chainParams)) ∧
    ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T (Cq (momentParameters T))
      (Cz' (momentParameters T)) (Cr (momentParameters T)) t x)
    (fun T a b => ⟨a, b⟩) J hFr
  refine eventuallyInParameters_map₂ ?_ J2 (hnear Nf)
  rintro T ⟨⟨hb, hd⟩, hfr⟩ hnr
  intro x t k e f F V s η hx hk3 hk6 he hfam htor hcold hs0 hs1 hη
  set T' := rateParameters T with hT'
  have hcond : Cond T' := ⟨hb.κ_pos, hb.κ_le, hb.odd, hb.L_ge⟩
  have hspec := Classical.choose_spec (hBex T' hcond)
  have hCbe : Cb T' = Classical.choose (hBex T' hcond) := dif_pos hcond
  rw [← hCbe] at hspec
  have hκ : 0 < T.κ := hb.κ_pos
  have htor' := htor
  obtain ⟨hFL, htt, n, hside, hn⟩ := htor'
  subst htt
  have hL0 : 0 < T.L := by have := hb.L_ge; omega
  have hcub : IsLargeCubicTorus F := ⟨n, hb.n₀_ge.trans hn, hside⟩
  have hlow : IsCubicTorusAbove T.L F.depth T.n₀ F :=
    ⟨hFL, rfl, n, hside, hn.trans (Nat.le_mul_of_pos_right n hL0)⟩
  have hodd : Odd F.blockSide := hFL ▸ hb.odd
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    rw [hside i]
    have := hb.n₀_ge
    omega
  have hall := hcov F hodd hpos
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd' => by
    simp [chordBonds, innerBonds, hall, hd']
  set m := frameRadius x with hm
  have hdk := hd x F.depth F V s hx htor hcold hs0 hs1
  have hone := (hfr F.depth x hx).one_torus F V s htor hcold hs0 hs1
  have hsm := hone.small
  have hσ := hb.σ_pos
  have hcold0 : IsSmallCurvature T.σ (interpolatedField s T.a T.chainParams.ρA m V η) := fun q hq =>
    (hsm.small_curvature_nearby η hη q hq).trans_le (by linarith)
  have hρ1 : T.chainParams.ρA ≤ 1 := hb.admissible.classical.1.2.1
  have hsmall : ∀ x' i, ¬ IsAxialTreeBond (x', i) →
      ‖interpolatedCoords s T.a T.chainParams.ρA m V η x' i‖ ≤ 1 :=
    fun x' i ht => (norm_interpolatedCoords_le hη hsm.norm_add_le (hchart _ ht)).trans hρ1
  have hana : ∀ d ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (interpolatedFrame s T.a T.chainParams.ρA m d) V :=
    fun d h => (hdk d h).2.1
  have hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s T.a T.chainParams.ρA m d) V c' X'‖ ≤
        K' T' k' * Real.exp (-(T'.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c')) :=
    fun d h k' c' X' h1 hX =>
    ((hdk d h).2.2 k' c' X' h1 hX).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have U : ∀ (p : ℕ) (w : Fin p → Perturbation F) (y : F.Site F.depth), (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ k (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
        (perturbedField s T.a T.chainParams.ρA m V η w τ)) 0 ∧
      (1 ≤ p → p ≤ k →
        |iteratedFDeriv ℝ p (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
          (perturbedField s T.a T.chainParams.ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
          Cb T' * runningMax e p *
            Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w))))) :=
    fun p w y hu => hspec.2 F T.n₀ k p m T.σ s T.a T.chainParams.ρA e f V η w y hFL hcub hlow hk6 he hfam
      hcold0 hsmall hana hdec hu
  have hlE : ∀ j, 0 ≤ runningMax e j := fun j => _root_.YangMills.Construction.Interpolation.TransportBounds.runningMax_nonneg he j
  have hC0 := hCb0 T'
  refine { smooth := ?_, decay := ?_, jointDeriv_le := ?_, blockDeriv_le := ?_ }
  · intro y l j b u c X hu hX
    rw [jointDisplacement_interpolatedExpansion]
    exact (U (l + j) (concatPerturbations b u c X) y (isUnit_concatPerturbations hu hX)).1
  · intro y j c X hj hjk hX
    have hunit : ∀ l, (topPerturbations c X l).IsUnit := fun l => hX l
    have h1 := (U j (topPerturbations c X) y hunit).2 hj hjk
    have heq : bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA m f y η) V c X =
        iteratedFDeriv ℝ j (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
          (perturbedField s T.a T.chainParams.ρA m V η (topPerturbations c X) τ)) 0
          fun l => Pi.single l 1 := by
      simp only [bondDeriv]
      rw [interpolatedExpansion_topPerturbations]
    rw [heq]
    refine h1.trans ?_
    have hspan : ((bondSpan (enclosingCell y) c : ℕ) : ℝ) ≤
        cellSetDiameter (insert (enclosingCell y) (perturbationCells (topPerturbations c X))) := by
      exact_mod_cast bondSpan_le_cellSetDiameter (enclosingCell y) c X
    have hE : Real.exp (-(2 ^ 7 * T.κ *
        cellSetDiameter (insert (enclosingCell y) (perturbationCells (topPerturbations c X))))) ≤
        Real.exp (-(2 ^ 6 * T.κ * bondSpan (enclosingCell y) c)) := exp_neg_rate_le_half hκ.le (Nat.cast_nonneg _) hspan
    have hG : 0 ≤ (torusDecayFactor T.L T.decayRate
        ((T.L : ℝ) * bondSpan (enclosingCell y) c / 16))⁻¹ := by
      apply inv_nonneg.2
      rw [torusDecayFactor]
      exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0.le (hlE j))
    exact hE.trans (le_add_of_nonneg_left hG)
  · intro y l j b u c X h1 hlk hu hX
    simp only [jointMixedDeriv]
    rw [jointDisplacement_interpolatedExpansion]
    have h2 := (U (l + j) (concatPerturbations b u c X) y (isUnit_concatPerturbations hu hX)).2 h1 hlk
    rwa [perturbationCells_concatPerturbations] at h2
  · intro Y c X hX
    have hGpos : 0 < torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
      rw [torusDecayFactor]
      exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
    have hek := he k
    have hek' := hlE (k - 1)
    have hCn' := hCn T' (Nf T') k
    have hCk1 : 1 ≤ Ck T' k := by
      show 1 ≤ Cn T' (Nf T') k + 1
      linarith
    have hCkn : Cn T' (Nf T') k ≤ Ck T' k := by
      show Cn T' (Nf T') k ≤ Cn T' (Nf T') k + 1
      linarith
    by_cases hnN : bondSpan Y c < Nf T'
    · refine (hnr x F.depth k e f F V s η Y c X hx hk3 hk6 he hfam htor hcold hs0 hs1 hη hX hnN).trans ?_
      refine div_le_div_of_nonneg_right ?_ hGpos.le
      have h2 : Cn T' (Nf T') k * runningMax e (k - 1) ≤ Ck T' k * runningMax e (k - 1) :=
        mul_le_mul_of_nonneg_right hCkn hek'
      linarith
    · have hNge : Nf T' ≤ bondSpan Y c := not_lt.1 hnN
      have hκ' : 0 < T'.κ := hκ
      have hNe : Nf T' = Classical.choose (exists_decay_threshold (A T' * Cb T') T'.κ T'.L hκ') :=
        dif_pos hκ'
      have hfl := Classical.choose_spec (exists_decay_threshold (A T' * Cb T') T'.κ T'.L hκ')
      rw [← hNe] at hfl
      have hfl' := hfl (bondSpan Y c) hNge
      have hunit : ∀ l, (topPerturbations c X l).IsUnit := fun l => hX l
      have hk1 : 1 ≤ k := by omega
      let g : F.Site F.depth → (Fin k → ℝ) → ℝ := fun y τ =>
        ColdStepAtMirrorFrames.subtractTrivial f F y
          (perturbedField s T.a T.chainParams.ρA m V η (topPerturbations c X) τ)
      have hfun : (fun τ : Fin k → ℝ => interpolatedBlockExpansion s T.a T.chainParams.ρA m f Y η
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) = fun τ => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter
            (fun y => enclosingCell y = Y), g y τ := by
        funext τ
        simp only [interpolatedBlockExpansion]
        refine Finset.sum_congr rfl fun y _ => ?_
        exact congrFun (interpolatedExpansion_topPerturbations s T.a T.chainParams.ρA m f y η V c X) τ
      have hsum := iteratedFDeriv_finset_sum_zero ((sitesOfCells (finiteCells F) F.depth).filter
        (fun y => enclosingCell y = Y)) g (fun y _ => (U k _ y hunit).1)
      have hd1 : bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA m f Y η) V c X =
          ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
            iteratedFDeriv ℝ k (g y) 0 fun l => Pi.single l 1 := by
        simp only [bondDeriv]
        rw [hfun, hsum, _root_.sum_apply]
      set n := bondSpan Y c with hn'
      have hterm : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
          |iteratedFDeriv ℝ k (g y) 0 fun l => Pi.single l 1| ≤
            Cb T' * runningMax e k * Real.exp (-(2 ^ 7 * T.κ * n)) := by
        intro y hy
        have hyY : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
        refine ((U k _ y hunit).2 hk1 le_rfl).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0.le (hlE k))
        have hspan : (n : ℝ) ≤
            cellSetDiameter (insert (enclosingCell y) (perturbationCells (topPerturbations c X))) := by
          rw [hyY]
          exact_mod_cast bondSpan_le_cellSetDiameter Y c X
        exact exp_neg_rate_antitone hκ.le hspan
      have hcard : (((sitesOfCells (finiteCells F) F.depth).filter
          (fun y => enclosingCell y = Y)).card : ℝ) ≤ A T' := by
        have h1 := hcount F hodd hcub Y
        rw [hFL] at h1
        refine le_trans ?_ h1
        have h2 : ∑ b ∈ ((sitesOfCells (finiteCells F) F.depth).filter
            (fun y => enclosingCell y = Y)).image
            (fun y => (y, (0 : Fin 4))), Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) ≤
            ∑ b ∈ fineBonds F, Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
          intro b hb'
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb'
          simp [fineBonds, hall]
        refine le_trans ?_ h2
        rw [Finset.sum_image (fun y _ y' _ h => congrArg Prod.fst h)]
        have h3 : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
            Real.exp (-(1 * (cellSupDist (enclosingCell y) Y : ℝ))) = 1 := by
          intro y hy
          rw [(Finset.mem_filter.1 hy).2]
          simp [cellSupDist]
        rw [Finset.sum_congr rfl h3]
        simp
      have hbd : |bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA m f Y η) V c X| ≤
          A T' * (Cb T' * runningMax e k * Real.exp (-(2 ^ 7 * T.κ * n))) := by
        rw [hd1]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg hC0.le (hlE k)) (Real.exp_pos _).le)
      have hfl2 : A T' * Cb T' * Real.exp (-(2 ^ 7 * T.κ * n)) ≤
          1 / 8 / torusDecayFactor T.L T.decayRate n := by
        rw [le_div_iff₀ hGpos]
        exact hfl'
      have hsplit : runningMax e k ≤ e k + runningMax e (k - 1) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, runningMax]
        have e2 := hlE k'
        exact max_le (by linarith) (by linarith)
      calc _ ≤ A T' * (Cb T' * runningMax e k * Real.exp (-(2 ^ 7 * T.κ * n))) := hbd
        _ = (A T' * Cb T' * Real.exp (-(2 ^ 7 * T.κ * n))) * runningMax e k := by ring
        _ ≤ (1 / 8 / torusDecayFactor T.L T.decayRate n) * runningMax e k :=
            mul_le_mul_of_nonneg_right hfl2 (hlE k)
        _ = (1 / 8 * runningMax e k) / torusDecayFactor T.L T.decayRate n := by ring
        _ ≤ _ := by
            refine div_le_div_of_nonneg_right ?_ hGpos.le
            have h3 : runningMax e (k - 1) ≤ Ck T' k * runningMax e (k - 1) :=
              le_mul_of_one_le_left hek' hCk1
            nlinarith
end YangMills.Construction.Interpolation
end
