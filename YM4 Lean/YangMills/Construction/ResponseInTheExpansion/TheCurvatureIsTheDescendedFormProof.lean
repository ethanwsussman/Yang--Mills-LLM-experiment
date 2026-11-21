import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClear
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithms
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedForm
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvatureLocally
import YangMills.Construction.ResponseInTheExpansion.TheResponseIsBoundedOnForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps WeightedResponses RenormalizationStepParameters
  TorusBalls TorusContours MarkedIntegrals PeriodicLattice
open Classical
open MeasureTheory
open scoped Quaternion
variable {ℓ : TorusLumps.StepParameters}
private theorem lieFormCurl_sub {m : ℕ} (X Y : TorusBond m → imaginaryQuaternions) (p : TorusPlaquette m) :
    lieFormCurl (fun b => X b - Y b) p = lieFormCurl X p - lieFormCurl Y p := by
  simp only [lieFormCurl]
  abel
private theorem responseOfLieForm_sub (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
    (X Y : TorusBond n → imaginaryQuaternions) (b : TorusBond (n * L)) :
    responseOfLieForm a ρA L u (fun c => X c - Y c) b =
      responseOfLieForm a ρA L u X b - responseOfLieForm a ρA L u Y b := by
  simp only [responseOfLieForm, smul_sub, Finset.sum_sub_distrib]
private theorem norm_responseOfLieForm_le (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
    (B : TorusBond n → imaginaryQuaternions) (b : TorusBond (n * L)) (S : ℝ) (hB : ∀ c, ‖(B c : ℍ[ℝ])‖ ≤ S) :
    ‖(responseOfLieForm a ρA L u B b : ℍ[ℝ])‖ ≤ (∑ c : TorusBond n, |responseKernel a ρA L u b c|) * S := by
  show ‖responseOfLieForm a ρA L u B b‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hB c) (norm_nonneg _)
private theorem norm_curl_responseOfLieForm_le (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
    (p : TorusPlaquette (n * L)) (Zp : Finset (TorusPlaquette n)) (D : TorusBond n → imaginaryQuaternions)
    (Δ S E : ℝ) (hΔ : 0 ≤ Δ) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hcontract : ∀ (A : TorusBond n → ℝ) (s sA : ℝ), (∀ q ∈ Zp, |curl A q| ≤ s) → (∀ b, |A b| ≤ sA) →
      |curl (responseMap a ρA L u A) p| ≤ s / 8 + E * sA)
    (hcurl : ∀ q ∈ Zp, ‖(lieFormCurl D q : ℍ[ℝ])‖ ≤ Δ) (hsup : ∀ b, ‖(D b : ℍ[ℝ])‖ ≤ S) :
    ‖(lieFormCurl (responseOfLieForm a ρA L u D) p : ℍ[ℝ])‖ ≤ Δ / 8 + E * S := by
  set v : ℍ[ℝ] := (lieFormCurl (responseOfLieForm a ρA L u D) p : ℍ[ℝ]) with hv
  let Ψ : imaginaryQuaternions →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ v (x : ℍ[ℝ])
      map_add' := fun x y => by
        simp only [Submodule.coe_add, inner_add_right]
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
  have hΨ : ∀ x : imaginaryQuaternions, |Ψ x| ≤ ‖v‖ * ‖(x : ℍ[ℝ])‖ := fun x => abs_real_inner_le_norm v (x : ℍ[ℝ])
  have hcurlΨ : ∀ {m : ℕ} (X : TorusBond m → imaginaryQuaternions) (q : TorusPlaquette m),
      curl (fun b => Ψ (X b)) q = Ψ (lieFormCurl X q) := by
    intro m X q
    simp only [curl, lieFormCurl, map_add, map_sub]
  have hresp : responseMap a ρA L u (fun b => Ψ (D b)) = fun b => Ψ (responseOfLieForm a ρA L u D b) := by
    funext b
    simp only [responseMap, responseOfLieForm, map_sum, map_smul, smul_eq_mul]
  have h1 := hcontract (fun b => Ψ (D b)) (‖v‖ * Δ) (‖v‖ * S)
    (fun q hq => by
      rw [hcurlΨ]
      exact (hΨ _).trans (mul_le_mul_of_nonneg_left (hcurl q hq) (norm_nonneg _)))
    (fun b => (hΨ _).trans (mul_le_mul_of_nonneg_left (hsup b) (norm_nonneg _)))
  rw [hresp, hcurlΨ] at h1
  have h2 : Ψ (lieFormCurl (responseOfLieForm a ρA L u D) p) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  rw [h2, abs_of_nonneg (by positivity)] at h1
  by_cases h0 : ‖v‖ = 0
  · rw [h0]
    positivity
  · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h3 : ‖v‖ * ‖v‖ ≤ ‖v‖ * (Δ / 8 + E * S) := by nlinarith
    exact le_of_mul_le_mul_left h3 hpos
private def DescentStepAt (T : StageTower ℓ) (m : ℝ) (t : ℕ) {n : ℕ} [NeZero n] (u : MarkedSample ℓ (t + 1) n)
    (o : TorusSite n) : Prop :=
  Disjoint (stageState T (t + 1) n u).2.1 (supBall o m) →
    IsColdOnBall ℓ.threshold u.2.2.1 o m ∧
    (StepAvoids T t m o u →
      (∀ o' : TorusSite (n * ℓ.side), parentBlock ℓ.side o' = o →
        Disjoint (stageState T t (n * ℓ.side) u.1).2.1 (supBall o' m)) ∧
      ∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m),
        b ∉ (show Finset (TorusBond (n * ℓ.side)) from u.2.2.2) ∧
        ‖(stepDeviation T t u.2.2.1 (topField ℓ t (n * ℓ.side) u.1) b : Quaternion ℝ)‖ < ℓ.threshold / 64)
private def DescentHoldsAlong (T : StageTower ℓ) (m : ℝ) (t : ℕ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (t + d) n → TorusSite (fineSide ℓ.side d n) → Prop
  | 0, _, _, _, _ => True
  | d + 1, n, _, u, o =>
    DescentStepAt T m (t + d) u (siteAbove ℓ.side (d + 1) n o) ∧ DescentHoldsAlong T m t d (n * ℓ.side) u.1 o
private def BallClearAlong (T : StageTower ℓ) (m : ℝ) (t : ℕ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (t + d) n → TorusSite (fineSide ℓ.side d n) → Prop
  | 0, _, _, _, _ => True
  | d + 1, n, _, u, o =>
    IsColdOnBall ℓ.threshold u.2.2.1 (siteAbove ℓ.side (d + 1) n o) m ∧
    (∀ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (d + 1) n o) m),
      ‖(stepDeviation T (t + d) u.2.2.1 (topField ℓ (t + d) (n * ℓ.side) u.1) b : Quaternion ℝ)‖ <
        ℓ.threshold / 64) ∧
    BallClearAlong T m t d (n * ℓ.side) u.1 o
private theorem ballClearAlong_of_descentHoldsAlong (T : StageTower ℓ) (m : ℝ) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)),
      DescentHoldsAlong T m t d n u o →
      Disjoint (stageState T (t + d) n u).2.1 (supBall (siteAbove ℓ.side d n o) m) →
      StepsAvoidOrigin T t m d n u o →
      BallClearAlong T m t d n u o ∧
        Disjoint (stageState T t (fineSide ℓ.side d n) (sampleBelow ℓ t d n u)).2.1 (supBall o m) := by
  intro d
  induction d with
  | zero =>
    intro n _ u o _ hd _
    exact ⟨trivial, hd⟩
  | succ d ih =>
    intro n _ u o hg hd hm
    obtain ⟨hdown, hg'⟩ := hg
    obtain ⟨hm', hfree⟩ := hm
    obtain ⟨hcold, hstep⟩ := hdown hd
    obtain ⟨hnext, hb⟩ := hstep hfree
    obtain ⟨hc, hdd⟩ := ih (n * ℓ.side) u.1 o hg' (hnext _ rfl) hm'
    exact ⟨⟨hcold, fun b hbm => (hb b hbm).2, hc⟩, hdd⟩
private theorem ae_of_ae_fst (T : StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n]
    (Q : MarkedSample ℓ s (n * ℓ.side) → Prop)
    (h : ∀ᵐ v ∂(markedSampleLaw T β s (n * ℓ.side)), Q v) :
    ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), Q u.1 := by
  let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  have h1 : ∀ᵐ u ∂((markedSampleLaw T β s (n * ℓ.side)).prod (stepReferenceMeasure ℓ n)), Q u.1 :=
    Measure.quasiMeasurePreserving_fst.ae h
  exact (withDensity_absolutelyContinuous _ _).ae_le h1
private theorem ae_sampleBelow (T : StageTower ℓ) (β : ℝ) (s : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (Q : MarkedSample ℓ s (fineSide ℓ.side d n) → Prop),
      (∀ᵐ v ∂(markedSampleLaw T β s (fineSide ℓ.side d n)), Q v) →
      ∀ᵐ u ∂(markedSampleLaw T β (s + d) n), Q (sampleBelow ℓ s d n u) := by
  intro d
  induction d with
  | zero =>
    intro n _ Q h
    exact h
  | succ d ih =>
    intro n _ Q h
    exact ae_of_ae_fst T β (s + d) n (fun v => Q (sampleBelow ℓ s d (n * ℓ.side) v)) (ih (n * ℓ.side) Q h)
private theorem ae_descentHoldsAlong (T : StageTower ℓ) (β : ℝ) (m : ℝ) (N lo hi : ℕ)
    (H : ∀ (t' n : ℕ) [NeZero n] (o : TorusSite n), lo ≤ t' → t' < hi → N ≤ n → ℓ.side ∣ n →
      ∀ᵐ u ∂(markedSampleLaw T β (t' + 1) n), DescentStepAt T m t' u o) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (o : TorusSite (fineSide ℓ.side d n)), lo ≤ t → t + d ≤ hi → N ≤ n → ℓ.side ∣ n →
      ∀ᵐ u ∂(markedSampleLaw T β (t + d) n), DescentHoldsAlong T m t d n u o := by
  intro d
  induction d with
  | zero =>
    intro n _ o _ _ _ _
    exact Filter.Eventually.of_forall fun _ => trivial
  | succ d ih =>
    intro n _ o hlo hhi hN hdv
    have hL : 1 ≤ ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have h1 := H (t + d) n (siteAbove ℓ.side (d + 1) n o) (by omega) (by omega) hN hdv
    have h2 := ae_of_ae_fst T β (t + d) n (fun v => DescentHoldsAlong T m t d (n * ℓ.side) v o)
      (ih (n * ℓ.side) o hlo (by omega) (hN.trans (Nat.le_mul_of_pos_right _ hL)) (Nat.dvd_mul_left _ _))
    filter_upwards [h1, h2] with u a1 a2
    exact ⟨a1, a2⟩
private theorem mem_plaquettesIn {m : ℕ} [NeZero m] {S : Finset (TorusSite m)} {p : TorusPlaquette m} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
private theorem supDist_add_unitStep_le {m : ℕ} [NeZero m] (x : TorusSite m) (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (x + TorusFields.unitStep m i) x ≤ 1 := by
  simpa using _root_.YangMills.Construction.TorusContours.supDist_sub_unitStep_le (x + TorusFields.unitStep m i) i
abbrev _root_.YangMills.SharedProofs.p63420 := @supDist_add_unitStep_le
private theorem supDist_vertex_le_two {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist z x ≤ 2 := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · simp [_root_.YangMills.Construction.TorusFields.supDist_self]
  · exact (supDist_add_unitStep_le x μ).trans (by norm_num)
  · exact (supDist_add_unitStep_le x ν).trans (by norm_num)
  · exact (_root_.YangMills.Construction.TorusFields.supDist_triangle _ (x + TorusFields.unitStep m μ) _).trans
      (add_le_add (supDist_add_unitStep_le _ ν) (supDist_add_unitStep_le x μ))
abbrev _root_.YangMills.SharedProofs.p38261 := @supDist_vertex_le_two
private theorem vertices_mem {m : ℕ} [NeZero m] {S : Finset (TorusSite m)} {p : TorusPlaquette m}
    (hp : p ∈ plaquettesIn S) :
    p.1 ∈ S ∧ p.1 + TorusFields.unitStep m p.2.1 ∈ S ∧ p.1 + TorusFields.unitStep m p.2.2 ∈ S := by
  have h := (mem_plaquettesIn.1 hp).2
  exact ⟨h _ (by simp [plaquetteVertices]), h _ (by simp [plaquetteVertices]), h _ (by simp [plaquetteVertices])⟩
private theorem norm_lieFormCurl_le {m : ℕ} (X : TorusBond m → imaginaryQuaternions) (p : TorusPlaquette m) (c : ℝ)
    (h1 : ‖(X (p.1, p.2.1) : ℍ[ℝ])‖ ≤ c) (h2 : ‖(X (p.1 + TorusFields.unitStep m p.2.1, p.2.2) : ℍ[ℝ])‖ ≤ c)
    (h3 : ‖(X (p.1 + TorusFields.unitStep m p.2.2, p.2.1) : ℍ[ℝ])‖ ≤ c) (h4 : ‖(X (p.1, p.2.2) : ℍ[ℝ])‖ ≤ c) :
    ‖(lieFormCurl X p : ℍ[ℝ])‖ ≤ 4 * c := by
  show ‖lieFormCurl X p‖ ≤ _
  have h1' : ‖X (p.1, p.2.1)‖ ≤ c := h1
  have h2' : ‖X (p.1 + TorusFields.unitStep m p.2.1, p.2.2)‖ ≤ c := h2
  have h3' : ‖X (p.1 + TorusFields.unitStep m p.2.2, p.2.1)‖ ≤ c := h3
  have h4' : ‖X (p.1, p.2.2)‖ ≤ c := h4
  unfold lieFormCurl
  refine (norm_sub_le _ _).trans ?_
  have := norm_sub_le (X (p.1, p.2.1) + X (p.1 + TorusFields.unitStep m p.2.1, p.2.2))
    (X (p.1 + TorusFields.unitStep m p.2.2, p.2.1))
  have := norm_add_le (X (p.1, p.2.1)) (X (p.1 + TorusFields.unitStep m p.2.1, p.2.2))
  linarith
private theorem norm_minimalLog_le_of_small (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (g : TorusSite n → UnitQuaternion),
      IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
      ∀ b : TorusBond n, b.1 ∈ supBall (siteAbove ℓ.side d n o) (ballRadius ℓ.side nn ρ₀ d) →
        ‖(minimalLog (gaugeTransform g (topField ℓ (k + d) n u) b) : Quaternion ℝ)‖ ≤ s := by
  intro d n _ u o g h
  cases d with
  | zero => exact h
  | succ d => exact h.1
private theorem curvature_le_of_small (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (g : TorusSite n → UnitQuaternion),
      1 ≤ d → IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
      ∀ z ∈ supBall (siteAbove ℓ.side d n o) (ballRadius ℓ.side nn ρ₀ d), ∀ μ ν : Fin 4,
        curvature (topField ℓ (k + d) n u) z μ ν ≤ s := by
  intro d n _ u o g hd h
  cases d with
  | zero => omega
  | succ d => exact h.2.1
private theorem norm_ballLog_le {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r s : ℝ) (hs : 0 ≤ s)
    (h : ∀ b : TorusBond n, b.1 ∈ supBall o r → ‖(minimalLog (gaugeTransform g V b) : Quaternion ℝ)‖ ≤ s)
    (b : TorusBond n) :
    ‖(ballLog g V o r b : ℍ[ℝ])‖ ≤ s := by
  unfold ballLog
  split_ifs with hb
  · exact h b hb
  · simpa using hs
private structure DescentEstimates (T : StageTower ℓ) (k M N : ℕ) (nn ρ₀ s e E C₂ m : ℝ) : Prop where
  logStep : ∀ (d n : ℕ) [NeZero n] (o₁ : TorusSite n) (o' : TorusSite (n * ℓ.side)) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (g : TorusSite n → UnitQuaternion),
    d < M → N ≤ n → parentBlock ℓ.side o' = o₁ → IsColdOnBall ℓ.threshold V o₁ m →
    IsNearIdentity g V o₁ (ballRadius ℓ.side nn ρ₀ (d + 1)) s →
    (∀ b : TorusBond (n * ℓ.side), b.1 ∈ supBall o' (ballRadius ℓ.side nn ρ₀ d) →
      ‖(minimalLog (gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b) :
        Quaternion ℝ)‖ ≤ s) →
    ∀ b : TorusBond (n * ℓ.side), b.1 ∈ supBall o' (ballRadius ℓ.side nn ρ₀ d) →
      ‖((minimalLog (gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b) -
          responseOfLieForm ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d)
            (ballLog g V o₁ (ballRadius ℓ.side nn ρ₀ (d + 1))) b -
          deviationInGauge T (k + d) g (supBall o₁ (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) V W b :
            imaginaryQuaternions) :
          Quaternion ℝ)‖ ≤ e
  contraction : ∀ (d n : ℕ) [NeZero n], d < M → N ≤ n → ∀ (Y : TorusSite n) (A : TorusBond n → ℝ) (sd sA : ℝ),
    (∀ p ∈ plaquettesIn (supBall Y ρ₀), |curl A p| ≤ sd) → (∀ b, |A b| ≤ sA) →
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * ℓ.side))),
      (∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side z) Y ≤ 1) →
      |curl (responseMap ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) A) p| ≤ sd / 8 + E * sA
  rowSum : ∀ (d n : ℕ) [NeZero n], d < M → N ≤ n → ∀ b : TorusBond (n * ℓ.side),
    ∑ c : TorusBond n, |responseKernel ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) b c| ≤ C₂
private theorem curl_descent (T : StageTower ℓ) (k M N : ℕ) (nn ρ₀ s e E C₂ m K ε : ℝ)
    (hF : DescentEstimates T k M N nn ρ₀ s e E C₂ m) (hL : 3 ≤ ℓ.side) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (he : 0 ≤ e)
    (hE : 0 ≤ E) (hK1 : 1 ≤ K) (hK : |C₂| + |ℓ.threshold| ≤ K) (hε : E * (1 + K ^ M) + 4 * e ≤ ε)
    (hgeo : ∀ d, ballRadius ℓ.side nn ρ₀ d / (ℓ.side : ℝ) + 1 + ρ₀ ≤ ballRadius ℓ.side nn ρ₀ (d + 1))
    (hcut : ∀ d, ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀ ≤ m) :
    ∀ (d ex n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (B : TorusBond n → imaginaryQuaternions) (g : TorusSite n → UnitQuaternion),
      d + ex = M → N ≤ n → (∀ b, ‖(B b : ℍ[ℝ])‖ ≤ K ^ ex) →
      (∀ p ∈ plaquettesIn (supBall (siteAbove ℓ.side d n o) (ballRadius ℓ.side nn ρ₀ d)),
        ‖(lieFormCurl (fun b => ballLog g (topField ℓ (k + d) n u) (siteAbove ℓ.side d n o)
            (ballRadius ℓ.side nn ρ₀ d) b - B b) p : ℍ[ℝ])‖ ≤ 2 * ε) →
      BallClearAlong T m k d n u o → IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
      ∀ p ∈ plaquettesIn (supBall o (ballRadius ℓ.side nn ρ₀ 0)),
        ‖(lieFormCurl (fun b => ballLog (gaugeDescent k d n u g) (topField ℓ k _ (sampleBelow ℓ k d n u)) o
            (ballRadius ℓ.side nn ρ₀ 0) b - descendedForm T k nn ρ₀ d n u o B g b) p : ℍ[ℝ])‖ ≤ 2 * ε := by
  have hε0 : 0 ≤ ε := by
    have : 0 ≤ E * (1 + K ^ M) := mul_nonneg hE (by positivity)
    linarith
  have hLpos : (0 : ℝ) < ℓ.side := by
    have : 0 < ℓ.side := by omega
    exact_mod_cast this
  intro d
  induction d with
  | zero =>
    intro ex n _ u o B g _ _ _ hcurl _ _
    exact hcurl
  | succ d ih =>
    intro ex n _ u o B g hd hN hB hcurl hclear hsmall
    obtain ⟨hcold, heta, hclear'⟩ := hclear
    obtain ⟨hlogs, hcurv, hsmall'⟩ := hsmall
    have hdM : d < M := by omega
    have hexM : ex ≤ M := by omega
    have hL1 : 1 ≤ ℓ.side := by omega
    have hN' : N ≤ n * ℓ.side := hN.trans (Nat.le_mul_of_pos_right _ hL1)
    set V : TorusField n := u.2.2.1 with hV
    set W : TorusField (n * ℓ.side) := topField ℓ (k + d) (n * ℓ.side) u.1 with hW
    set o₁ : TorusSite n := siteAbove ℓ.side (d + 1) n o with ho₁
    set o' : TorusSite (n * ℓ.side) := siteAbove ℓ.side d (n * ℓ.side) o with ho'
    set g' : TorusSite (n * ℓ.side) → UnitQuaternion := fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x
      with hg'
    set r₁ : ℝ := ballRadius ℓ.side nn ρ₀ (d + 1) with hr₁
    set r₀ : ℝ := ballRadius ℓ.side nn ρ₀ d with hr₀
    set η : TorusBond (n * ℓ.side) → imaginaryQuaternions :=
      deviationInGauge T (k + d) g (supBall o₁ (r₁ - 3 * ρ₀)) V W with hη
    set R : (TorusBond n → imaginaryQuaternions) → TorusBond (n * ℓ.side) → imaginaryQuaternions :=
      responseOfLieForm ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) with hR
    set B' : TorusBond (n * ℓ.side) → imaginaryQuaternions := fun b => R B b + η b with hB'
    have hKex : (1 : ℝ) ≤ K ^ ex := one_le_pow₀ hK1
    have hηb : ∀ b, ‖(η b : ℍ[ℝ])‖ ≤ |ℓ.threshold| := by
      intro b
      simp only [hη, deviationInGauge]
      split_ifs with hb
      · show ‖ColdStepAtMirrorFrames.adjointAction _ _‖ ≤ _
        rw [Adjoint.norm_adjointAction]
        have hmem : b ∈ chartBondsInBlocks ℓ.side (supBall o₁ m) := by
          refine Finset.mem_filter.2 ⟨hb.2, ?_⟩
          have h1 := (Finset.mem_filter.1 hb.1).2
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1.trans (hcut d)⟩
        have h2 := heta b hmem
        have h3 : ℓ.threshold / 64 ≤ |ℓ.threshold| := by
          have h4 := le_abs_self ℓ.threshold
          have h5 := abs_nonneg ℓ.threshold
          linarith
        exact (le_of_lt h2).trans h3
      · simp
    have hBnext : ∀ b, ‖(B' b : ℍ[ℝ])‖ ≤ K ^ (ex + 1) := by
      intro b
      have h1 : ‖(R B b : ℍ[ℝ])‖ ≤
          (∑ c : TorusBond n, |responseKernel ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) b c|) *
            K ^ ex :=
        norm_responseOfLieForm_le _ _ _ _ B b _ hB
      have h2 : (∑ c : TorusBond n, |responseKernel ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) b c|) *
          K ^ ex ≤ |C₂| * K ^ ex :=
        mul_le_mul_of_nonneg_right ((hF.rowSum d n hdM hN b).trans (le_abs_self _)) (by positivity)
      have h3 : ‖(B' b : ℍ[ℝ])‖ ≤ ‖(R B b : ℍ[ℝ])‖ + ‖(η b : ℍ[ℝ])‖ := norm_add_le (R B b) (η b)
      have h4 := hηb b
      have h5 : |ℓ.threshold| ≤ |ℓ.threshold| * K ^ ex := le_mul_of_one_le_right (abs_nonneg _) hKex
      have h6 : (|C₂| + |ℓ.threshold|) * K ^ ex ≤ K * K ^ ex := mul_le_mul_of_nonneg_right hK (by positivity)
      rw [pow_succ']
      nlinarith
    have hcurlnext : ∀ p ∈ plaquettesIn (supBall o' r₀),
        ‖(lieFormCurl (fun b => ballLog g' W o' r₀ b - B' b) p : ℍ[ℝ])‖ ≤ 2 * ε := by
      intro p hp
      set X : TorusBond n → imaginaryQuaternions := fun b => ballLog g V o₁ r₁ b - B b with hX
      set X' : TorusBond (n * ℓ.side) → imaginaryQuaternions := fun b => ballLog g' W o' r₀ b - B' b with hX'
      set Er : TorusBond (n * ℓ.side) → imaginaryQuaternions := fun b => X' b - R X b with hEr
      have hnear : IsNearIdentity g V o₁ r₁ s :=
        ⟨hlogs, fun q hq => hcurv q.1 (vertices_mem hq).1 q.2.1 q.2.2⟩
      have hlogs' : ∀ b : TorusBond (n * ℓ.side), b.1 ∈ supBall o' r₀ →
          ‖(minimalLog (gaugeTransform g' W b) : Quaternion ℝ)‖ ≤ s :=
        norm_minimalLog_le_of_small T k nn ρ₀ s d (n * ℓ.side) u.1 o g' hsmall'
      have hErb : ∀ b : TorusBond (n * ℓ.side), b.1 ∈ supBall o' r₀ → ‖(Er b : ℍ[ℝ])‖ ≤ e := by
        intro b hb
        have h1 := hF.logStep d n o₁ o' V W g hdM hN rfl hcold hnear hlogs' b hb
        have h2 : Er b = minimalLog (gaugeTransform g' W b) - R (ballLog g V o₁ r₁) b - η b := by
          simp only [hEr, hX', hB', hX, hR, responseOfLieForm_sub]
          simp only [ballLog, if_pos hb]
          abel
        rw [h2]
        exact h1
      have hsplit : lieFormCurl X' p = lieFormCurl (R X) p + lieFormCurl Er p := by
        simp only [lieFormCurl, hEr]
        abel
      have hc := vertices_mem hp
      have hE4 : ‖(lieFormCurl Er p : ℍ[ℝ])‖ ≤ 4 * e :=
        norm_lieFormCurl_le Er p e (hErb _ hc.1) (hErb _ hc.2.1) (hErb _ hc.2.2) (hErb _ hc.1)
      have hY : ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p.1) o₁ : ℕ) : ℝ) ≤ r₀ / (ℓ.side : ℝ) + 1 := by
        have h1 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p.1) o₁ ≤ _root_.YangMills.Construction.TorusFields.supDist p.1 o' / ℓ.side + 1 :=
          _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side p.1 o'
        have h2 : ((_root_.YangMills.Construction.TorusFields.supDist p.1 o' : ℕ) : ℝ) ≤ r₀ := (Finset.mem_filter.1 hc.1).2
        have h3 : ((_root_.YangMills.Construction.TorusFields.supDist p.1 o' / ℓ.side : ℕ) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist p.1 o' : ℝ) / (ℓ.side : ℝ) := Nat.cast_div_le
        have h4 : (_root_.YangMills.Construction.TorusFields.supDist p.1 o' : ℝ) / (ℓ.side : ℝ) ≤ r₀ / (ℓ.side : ℝ) := div_le_div_of_nonneg_right h2 hLpos.le
        have h5 : ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p.1) o₁ : ℕ) : ℝ) ≤ ((_root_.YangMills.Construction.TorusFields.supDist p.1 o' / ℓ.side + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h5
        linarith
      have hsub : ∀ z ∈ supBall (parentBlock ℓ.side p.1) ρ₀, z ∈ supBall o₁ r₁ := by
        intro z hz
        have h1 : ((_root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side p.1) : ℕ) : ℝ) ≤ ρ₀ := (Finset.mem_filter.1 hz).2
        have h2 : _root_.YangMills.Construction.TorusFields.supDist z o₁ ≤ _root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side p.1) + _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p.1) o₁ :=
          _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
        have h3 : ((_root_.YangMills.Construction.TorusFields.supDist z o₁ : ℕ) : ℝ) ≤
            (_root_.YangMills.Construction.TorusFields.supDist z (parentBlock ℓ.side p.1) : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side p.1) o₁ : ℝ) := by
          exact_mod_cast h2
        have h4 := hgeo d
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
      have hXsup : ∀ b, ‖(X b : ℍ[ℝ])‖ ≤ 1 + K ^ M := by
        intro b
        have h1 : ‖(ballLog g V o₁ r₁ b : ℍ[ℝ])‖ ≤ s := norm_ballLog_le g V o₁ r₁ s hs0 hlogs b
        have h2 : ‖(X b : ℍ[ℝ])‖ ≤ ‖(ballLog g V o₁ r₁ b : ℍ[ℝ])‖ + ‖(B b : ℍ[ℝ])‖ :=
          norm_sub_le (ballLog g V o₁ r₁ b) (B b)
        have h3 : K ^ ex ≤ K ^ M := pow_le_pow_right₀ hK1 hexM
        have h4 := hB b
        linarith
      have hcontract := norm_curl_responseOfLieForm_le ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) p
        (plaquettesIn (supBall (parentBlock ℓ.side p.1) ρ₀)) X (2 * ε) (1 + K ^ M) E (by positivity)
          (by positivity) hE
        (fun A sd sA h1 h2 => hF.contraction d n hdM hN (parentBlock ℓ.side p.1) A sd sA h1 h2 p
          (mem_plaquettesIn.2 ⟨(mem_plaquettesIn.1 hp).1, fun _ _ => Finset.mem_univ _⟩)
          (fun z hz => by
            have h3 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side z p.1
            have h4 : _root_.YangMills.Construction.TorusFields.supDist z p.1 / ℓ.side = 0 :=
              Nat.div_eq_of_lt (by have := supDist_vertex_le_two hz; omega)
            omega))
        (fun q hq => hcurl q (mem_plaquettesIn.2 ⟨(mem_plaquettesIn.1 hq).1,
          fun z hz => hsub z ((mem_plaquettesIn.1 hq).2 z hz)⟩))
        hXsup
      rw [hsplit]
      have h5 : ‖(lieFormCurl (R X) p + lieFormCurl Er p : ℍ[ℝ])‖ ≤
          ‖(lieFormCurl (R X) p : ℍ[ℝ])‖ + ‖(lieFormCurl Er p : ℍ[ℝ])‖ := norm_add_le _ _
      have h6 : ‖((lieFormCurl (R X) p + lieFormCurl Er p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          ‖(lieFormCurl (R X) p : ℍ[ℝ])‖ + ‖(lieFormCurl Er p : ℍ[ℝ])‖ := h5
      refine h6.trans ?_
      have h7 : ‖(lieFormCurl (R X) p : ℍ[ℝ])‖ ≤ 2 * ε / 8 + E * (1 + K ^ M) := hcontract
      linarith
    exact ih (ex + 1) (n * ℓ.side) u.1 o B' g' (by omega) hN' hBnext hcurlnext hclear' hsmall'
private theorem eventually_scale_bounds (c K : ℝ) (hc : 0 < c) (hK : 1 ≤ K) :
    ∃ x₁ : ℝ, 1 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x →
      1 ≤ chainDepth x ∧ 16 ≤ ⌊Real.log x ^ 3⌋₊ ∧ (chainDepth x : ℝ) * Real.log K ≤ c * logCubeScale x ∧
      20 * x ^ ((1 : ℝ) / 90) + logCubeScale x ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  set l₀ : ℝ := max 3 (2 * Real.log K / c) with hl₀
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, l₀ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop l₀
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, (60 : ℝ) ≤ x ^ ((7 : ℝ) / 180) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 180)).eventually_ge_atTop 60
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ ((1 : ℝ) / 20) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually_ge_atTop 6
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ (3 : ℝ)‖ ≤ (1 / 3) * ‖x ^ ((1 : ℝ) / 20)‖ :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 20)).def (by norm_num)
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  set l : ℝ := Real.log x with hl
  have hl3 : 3 ≤ l := (le_max_left _ _).trans h1
  have hlK : 2 * Real.log K / c ≤ l := (le_max_right _ _).trans h1
  have hlK' : 2 * Real.log K ≤ c * l := by
    have := (div_le_iff₀ hc).1 hlK
    linarith
  have hl2 : 9 ≤ l ^ 2 := by nlinarith
  have hl3' : 27 ≤ l ^ 3 := by nlinarith
  have hfl : (l ^ 3) - 1 ≤ logCubeScale x := by
    have := Nat.lt_floor_add_one (l ^ 3)
    simp only [logCubeScale]
    linarith
  have hfl' : logCubeScale x ≤ l ^ 3 := Nat.floor_le (by positivity)
  have hd : (chainDepth x : ℝ) ≤ l ^ 2 := Nat.floor_le (by positivity)
  refine ⟨Nat.le_floor (by push_cast; linarith), Nat.le_floor (by push_cast; linarith), ?_, ?_⟩
  · have h6 : (chainDepth x : ℝ) * Real.log K ≤ l ^ 2 * Real.log K := mul_le_mul_of_nonneg_right hd hlogK
    have h7 : l ^ 2 * (2 * Real.log K) ≤ l ^ 2 * (c * l) := mul_le_mul_of_nonneg_left hlK' (by positivity)
    have h8 : c * (l ^ 3 / 2) ≤ c * logCubeScale x := mul_le_mul_of_nonneg_left (by linarith) hc.le
    nlinarith
  · set y : ℝ := x ^ ((1 : ℝ) / 20) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
    have h9 : x ^ ((1 : ℝ) / 90) * x ^ ((7 : ℝ) / 180) = y := by
      rw [← Real.rpow_add hx0]
      norm_num [hy]
    have hz0 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg hx0.le _
    have h10 : 60 * x ^ ((1 : ℝ) / 90) ≤ y := by
      rw [← h9]
      nlinarith
    have h11 : l ^ 3 ≤ (1 / 3) * y := by
      have h12 : ‖Real.log x ^ (3 : ℝ)‖ = l ^ 3 := by
        rw [Real.rpow_ofNat, Real.norm_of_nonneg (by positivity)]
      rw [h12, Real.norm_of_nonneg hy0] at h4
      exact h4
    have h13 : y - 1 ≤ (⌊y⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one y
      linarith
    linarith
private theorem holdsOnParameters_of_four (P₁ P₂ P₃ P₄ R : ParameterAssignment → ℝ → Prop)
    (h₁ : HoldsOnParameterFamilies P₁) (h₂ : HoldsOnParameterFamilies P₂)
    (h₃ : HoldsOnParameterFamilies P₃) (h₄ : HoldsOnParameterFamilies P₄)
    (h : ∀ Tb y, 3 ≤ Tb.side → P₁ Tb y → P₂ Tb y → P₃ Tb y → P₄ Tb y → R Tb y) : HoldsOnParameterFamilies R := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, f₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, C₂, p₂, f₂⟩ := h₂ a ha
  obtain ⟨L₃, r₃, C₃, p₃, f₃⟩ := h₃ a ha
  obtain ⟨L₄, r₄, C₄, p₄, f₄⟩ := h₄ a ha
  refine ⟨max (max (max L₁ L₂) (max L₃ L₄)) 3, fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    max (max C₁ C₂) (max C₃ C₄), fun c => lt_min (lt_min (p₁ c) (p₂ c)) (lt_min (p₃ c) (p₄ c)), ?_⟩
  intro L hodd hL T hTa hTL hD hC hO hrt hCd
  have l0 := (le_max_left _ _).trans hL
  have l3 : 3 ≤ L := (le_max_right _ _).trans hL
  have l12 := (le_max_left _ _).trans l0
  have l34 := (le_max_right _ _).trans l0
  have r12 := hrt.trans (min_le_left _ _)
  have r34 := hrt.trans (min_le_right _ _)
  have c12 := (le_max_left _ _).trans hCd
  have c34 := (le_max_right _ _).trans hCd
  obtain ⟨y₁, g₁⟩ := f₁ L hodd ((le_max_left _ _).trans l12) T hTa hTL hD hC hO (r12.trans (min_le_left _ _))
    ((le_max_left _ _).trans c12)
  obtain ⟨y₂, g₂⟩ := f₂ L hodd ((le_max_right _ _).trans l12) T hTa hTL hD hC hO (r12.trans (min_le_right _ _))
    ((le_max_right _ _).trans c12)
  obtain ⟨y₃, g₃⟩ := f₃ L hodd ((le_max_left _ _).trans l34) T hTa hTL hD hC hO (r34.trans (min_le_left _ _))
    ((le_max_left _ _).trans c34)
  obtain ⟨y₄, g₄⟩ := f₄ L hodd ((le_max_right _ _).trans l34) T hTa hTL hD hC hO (r34.trans (min_le_right _ _))
    ((le_max_right _ _).trans c34)
  refine ⟨max (max y₁ y₂) (max y₃ y₄), fun y hy hrow hw => ?_⟩
  have y12 := (le_max_left _ _).trans hy
  have y34 := (le_max_right _ _).trans hy
  exact h T y (by omega) (g₁ y ((le_max_left _ _).trans y12) hrow hw) (g₂ y ((le_max_right _ _).trans y12) hrow hw)
    (g₃ y ((le_max_left _ _).trans y34) hrow hw) (g₄ y ((le_max_right _ _).trans y34) hrow hw)
private theorem IsLocalChainAbove.mono {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)} {β : ℝ}
    {k N : ℕ} {nn x₀ : ℝ}
    (h : IsLocalChainAbove Tb y T β k N nn x₀) (n : ℕ) (x₁ : ℝ) (hx : x₁ ≤ x₀) (hn : N ≤ n) :
    IsLocalChainAbove Tb y T β k n nn x₁ :=
  ⟨hx.trans h.floor_le, h.coupling_ge, h.onFamily, h.cutoff, h.measurable, h.side_ge.trans (by exact_mod_cast hn),
    h.one_le, h.le_rpow⟩
set_option maxHeartbeats 2000000 in
private theorem curvatureNearDescendedFormAt_of (Tb : ParameterAssignment) (y : ℝ) (hL : 3 ≤ Tb.side)
    (h₁ : logarithmOneStepAt Tb y)
    (h₂ : ResponseLocalCurvatureContractionAt Tb y) (h₃ : descentKeepsBallClearAt Tb y)
    (h₄ : ∃ C₂ : ℝ, ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ b : TorusBond (n * (Tb.stepParameters y).side),
      ∑ c : TorusBond n, |responseKernel Tb.coupling Tb.ρA (Tb.stepParameters y).side u b c| ≤ C₂) :
    curvatureNearDescendedFormAt Tb y := by
  obtain ⟨Ca, ca, xa, hca, H1⟩ := h₁
  obtain ⟨Cb, cb, hcb, H2⟩ := h₂
  obtain ⟨xd, H3⟩ := h₃
  obtain ⟨C₂, H4⟩ := h₄
  set K : ℝ := |C₂| + |(Tb.stepParameters y).threshold| + 1 with hKdef
  have hK1 : 1 ≤ K := by
    have := abs_nonneg C₂
    have := abs_nonneg (Tb.stepParameters y).threshold
    linarith
  obtain ⟨xn, hxn1, hnum⟩ := eventually_scale_bounds (cb / 2) K (by positivity) hK1
  refine ⟨4 * |Cb| + 8 * |Ca|, min ca (cb / 2), max (max xa xd) xn, lt_min hca (by positivity), ?_⟩
  intro T β k N _ nn s o hloc hLN hs hsx
  set x : ℝ := flowCouplings (Tb.stepParameters y) β k with hx
  set ρ₀ : ℝ := localLogScale (Tb.stepParameters y) β k with hρ₀
  set m : ℕ := localBlockSide (Tb.stepParameters y) β k with hm
  set ρ : ℕ := ⌊Real.log x ^ 3⌋₊ with hρ
  have hρρ : ρ₀ = (ρ : ℝ) := rfl
  have hxfl : xn ≤ x := (le_max_right _ _).trans hloc.floor_le
  obtain ⟨hM1, hρ16, hpay, hroom⟩ := hnum x hxfl
  have hx1 : 1 ≤ x := hxn1.trans hxfl
  have hM1' : 1 ≤ (localChainDepth (Tb.stepParameters y) β k) := hM1
  have hpay' : ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * Real.log K ≤ cb / 2 * ρ₀ := hpay
  have hLℓ : 3 ≤ (Tb.stepParameters y).side := hL
  have hLr : (3 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by exact_mod_cast hLℓ
  have hnn1 : 1 ≤ nn := hloc.one_le
  have hnnx : nn ≤ x ^ ((1 : ℝ) / 90) := hloc.le_rpow
  have hxz : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg (by linarith) _
  have hρ₀16 : (16 : ℝ) ≤ ρ₀ := by rw [hρρ]; exact_mod_cast hρ16
  have hρ₀m : ρ₀ ≤ (m : ℝ) := by
    have h1 : 20 * x ^ ((1 : ℝ) / 90) + ρ₀ ≤ (m : ℝ) := hroom
    linarith
  have hρm : ρ ≤ m := by rw [hρρ] at hρ₀m; exact_mod_cast hρ₀m
  have hNside : 2 ^ 10 * m ≤ N := by
    have h1 : (2 : ℝ) ^ 10 * (m : ℝ) ≤ (N : ℝ) := hloc.side_ge
    exact_mod_cast h1
  have h64 : ∀ n : ℕ, N ≤ n → 64 ≤ n := fun n hn => by omega
  have h2ρ : ∀ n : ℕ, N ≤ n → 2 * ρ + 2 < n := fun n hn => by omega
  have hs1 : s ≤ 1 := hsx.trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
  have hrad : ∀ d, d < (localChainDepth (Tb.stepParameters y) β k) → (T.stage (k + d)).anchorRadius = Tb.ρA :=
    fun d hd =>
      (hloc.onFamily.onFamily (k + d)
        (by show k + d ≤ k + 2 * (localChainDepth (Tb.stepParameters y) β k); omega)).anchorRadius_eq
  set E : ℝ := |Cb| * Real.exp (-(cb * ρ₀)) with hE
  set e : ℝ := |Ca| * (s ^ 2 + Real.exp (-(ca * ρ₀))) with he
  have hE0 : 0 ≤ E := by positivity
  have he0 : 0 ≤ e := by positivity
  have hF : DescentEstimates T k (localChainDepth (Tb.stepParameters y) β k) N nn ρ₀ s e E C₂ (m : ℝ) :=
    { logStep := fun d n _ o₁ o' V W g hd hN hb hcold hnear hlogs b hbm =>
        (H1 T β k n nn d o₁ o' V W g s
          (IsLocalChainAbove.mono hloc n xa ((le_max_left _ _).trans (le_max_left _ _)) hN)
          hd hs hsx hb hcold hnear hlogs b hbm).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      contraction := fun d n _ hd hN Y A sd sA hc hb p hp hz => by
        rw [hrad d hd]
        have hsA : 0 ≤ sA := (abs_nonneg _).trans (hb ((0 : TorusSite n), 0))
        have h1 := H2 (k + d) n (h64 n hN) ρ hρ16 (h2ρ n hN) Y A sd sA
          (fun q hq => hc q (mem_plaquettesIn.2 ⟨(mem_plaquettesIn.1 hq).1, fun z hz' => Finset.mem_filter.2
            ⟨Finset.mem_univ _, by
              have h2 := (Finset.mem_filter.1 ((mem_plaquettesIn.1 hq).2 z hz')).2
              rw [hρρ]
              exact_mod_cast h2⟩⟩)) hb p hp hz
        refine h1.trans ?_
        have h3 : Cb * Real.exp (-(cb * (ρ : ℝ))) ≤ E := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        have h4 := mul_le_mul_of_nonneg_right h3 hsA
        linarith
      rowSum := fun d n _ hd hN b => by
        rw [hrad d hd]
        exact H4 (k + d) n (h64 n hN) b }
  have hgeo : ∀ d, ballRadius (Tb.stepParameters y).side nn ρ₀ d / ((Tb.stepParameters y).side : ℝ) + 1 + ρ₀ ≤
      ballRadius (Tb.stepParameters y).side nn ρ₀ (d + 1) := by
    intro d
    simp only [ballRadius]
    have h1 : (20 * nn / ((Tb.stepParameters y).side : ℝ) ^ d + 4 * ρ₀) / ((Tb.stepParameters y).side : ℝ) =
        20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (d + 1) + 4 * ρ₀ / ((Tb.stepParameters y).side : ℝ) := by
      rw [add_div, pow_succ, div_div]
    have h2 : 4 * ρ₀ / ((Tb.stepParameters y).side : ℝ) ≤ 4 * ρ₀ / 3 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hLr
    rw [h1]
    linarith
  have hcut : ∀ d, ballRadius (Tb.stepParameters y).side nn ρ₀ (d + 1) - 3 * ρ₀ ≤ (m : ℝ) := by
    intro d
    simp only [ballRadius]
    have h1 : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (d + 1) ≤ 20 * nn :=
      div_le_self (by linarith) (one_le_pow₀ (by linarith))
    have h2 : 20 * x ^ ((1 : ℝ) / 90) + ρ₀ ≤ (m : ℝ) := hroom
    linarith
  have hHD : ∀ (t' n : ℕ) [NeZero n] (o' : TorusSite n), k ≤ t' →
      t' < k + 2 * (localChainDepth (Tb.stepParameters y) β k) → N ≤ n → (Tb.stepParameters y).side ∣ n →
      ∀ᵐ u ∂(markedSampleLaw T β (t' + 1) n), DescentStepAt T (m : ℝ) t' u o' := by
    intro t' n _ o' hk ht hN hdv
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact H3 T β k n nn j o'
      (IsLocalChainAbove.mono hloc n xd ((le_max_right _ _).trans (le_max_left _ _)) hN) hdv
      (by show j < 2 * (localChainDepth (Tb.stepParameters y) β k); omega)
  have hL1 : 1 ≤ (Tb.stepParameters y).side := by omega
  have hNn₁ : N ≤ fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N := by
    rw [fineSide_eq]
    exact Nat.le_mul_of_pos_right _ (pow_pos hL1 _)
  have hdvn₁ : (Tb.stepParameters y).side ∣
      fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N := by
    rw [fineSide_eq]
    exact hLN.mul_right _
  have g1 : ∀ᵐ u ∂(markedSampleLaw T β
      (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N),
      DescentHoldsAlong T (m : ℝ) (k + (localChainDepth (Tb.stepParameters y) β k))
        (localChainDepth (Tb.stepParameters y) β k) N u
        (siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o) :=
    ae_descentHoldsAlong T β (m : ℝ) N k (k + 2 * (localChainDepth (Tb.stepParameters y) β k)) hHD
      (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N _
      (by omega) (by omega) le_rfl hLN
  have g2 : ∀ᵐ u ∂(markedSampleLaw T β
      (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N),
      DescentHoldsAlong T (m : ℝ) k (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
        (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
          (localChainDepth (Tb.stepParameters y) β k) N u) o :=
    ae_sampleBelow T β (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N
      (fun v => DescentHoldsAlong T (m : ℝ) k (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) v o)
      (ae_descentHoldsAlong T β (m : ℝ) N k (k + 2 * (localChainDepth (Tb.stepParameters y) β k)) hHD k
        (localChainDepth (Tb.stepParameters y) β k) _ o le_rfl (by omega) hNn₁ hdvn₁)
  filter_upwards [g1, g2] with u a1 a2 hlocal hsmall p hp
  obtain ⟨b1, b2, b3⟩ := hlocal
  obtain ⟨_, d1⟩ := ballClearAlong_of_descentHoldsAlong T (m : ℝ) (k + (localChainDepth (Tb.stepParameters y) β k))
    (localChainDepth (Tb.stepParameters y) β k) N u _ a1 b1 b2
  obtain ⟨c2, _⟩ := ballClearAlong_of_descentHoldsAlong T (m : ℝ) k (localChainDepth (Tb.stepParameters y) β k) _
    (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
      (localChainDepth (Tb.stepParameters y) β k) N u) o a2 d1 b3
  set u₁ := sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (localChainDepth (Tb.stepParameters y) β k) N u with hu₁
  set V := topField (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) u₁ with hV
  set o₂ := siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o with ho₂
  set g := axialGaugeAt (Tb.stepParameters y) V o₂ with hg
  set rM : ℝ := ballRadius (Tb.stepParameters y).side nn ρ₀ (localChainDepth (Tb.stepParameters y) β k) with hrM
  have logsTop := norm_minimalLog_le_of_small T k nn ρ₀ s (localChainDepth (Tb.stepParameters y) β k) _ u₁ o g hsmall
  have curvTop := curvature_le_of_small T k nn ρ₀ s (localChainDepth (Tb.stepParameters y) β k) _ u₁ o g hM1' hsmall
  have htop : ∀ b, topLogForm (Tb.stepParameters y) V o₂ rM (x ^ (-(1 / 4 : ℝ))) b = ballLog g V o₂ rM b := by
    intro b
    unfold topLogForm ballLog
    by_cases hb : b.1 ∈ supBall o₂ rM
    · rw [if_pos ⟨hb, fun z hz μ ν => (curvTop z hz μ ν).trans hsx⟩, if_pos hb]
    · rw [if_neg (fun h => hb h.1), if_neg hb]
  set ε : ℝ := E * (1 + K ^ (localChainDepth (Tb.stepParameters y) β k)) + 4 * e with hε
  have hε0 : 0 ≤ ε := by positivity
  have hdesc := curl_descent T k (localChainDepth (Tb.stepParameters y) β k) N nn ρ₀ s e E C₂ (m : ℝ) K ε hF hLℓ
    hs hs1 he0 hE0 hK1 (by linarith) le_rfl hgeo hcut
    (localChainDepth (Tb.stepParameters y) β k) 0 _ u₁ o (topLogForm (Tb.stepParameters y) V o₂ rM (x ^ (-(1 / 4 : ℝ))))
      g (by omega) hNn₁
    (fun b => by
      rw [htop, pow_zero]
      exact (norm_ballLog_le g V o₂ rM s hs logsTop b).trans hs1)
    (fun q _ => by
      have h0 : (fun b => ballLog g V o₂ rM b - topLogForm (Tb.stepParameters y) V o₂ rM (x ^ (-(1 / 4 : ℝ))) b) =
          fun _ => 0 := by
        funext b
        rw [htop, sub_self]
      rw [h0]
      simp [lieFormCurl, hε0])
    c2 hsmall p hp
  rw [lieFormCurl_sub] at hdesc
  refine le_trans hdesc ?_
  set c : ℝ := min ca (cb / 2) with hc
  have hρ₀0 : 0 ≤ ρ₀ := by linarith
  have hEe1 : Real.exp (-(ca * ρ₀)) ≤ Real.exp (-(c * ρ₀)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ₀0))
  have hEe2 : Real.exp (-(cb / 2 * ρ₀)) ≤ Real.exp (-(c * ρ₀)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hρ₀0))
  have hKpos : 0 < K := by linarith
  have hKM : K ^ (localChainDepth (Tb.stepParameters y) β k) ≤ Real.exp (cb / 2 * ρ₀) := by
    have h1 : K ^ (localChainDepth (Tb.stepParameters y) β k) =
        Real.exp (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * Real.log K) := by
      rw [Real.exp_nat_mul, Real.exp_log hKpos]
    rw [h1]
    exact Real.exp_le_exp.2 hpay'
  have hKM1 : 1 ≤ K ^ (localChainDepth (Tb.stepParameters y) β k) := one_le_pow₀ hK1
  have hES : E * (1 + K ^ (localChainDepth (Tb.stepParameters y) β k)) ≤ 2 * |Cb| * Real.exp (-(c * ρ₀)) := by
    have h1 : 1 + K ^ (localChainDepth (Tb.stepParameters y) β k) ≤ 2 * Real.exp (cb / 2 * ρ₀) := by linarith
    have h2 : Real.exp (-(cb * ρ₀)) * Real.exp (cb / 2 * ρ₀) = Real.exp (-(cb / 2 * ρ₀)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc E * (1 + K ^ (localChainDepth (Tb.stepParameters y) β k)) ≤ E * (2 * Real.exp (cb / 2 * ρ₀)) :=
          mul_le_mul_of_nonneg_left h1 hE0
      _ = 2 * |Cb| * (Real.exp (-(cb * ρ₀)) * Real.exp (cb / 2 * ρ₀)) := by rw [hE]; ring
      _ = 2 * |Cb| * Real.exp (-(cb / 2 * ρ₀)) := by rw [h2]
      _ ≤ 2 * |Cb| * Real.exp (-(c * ρ₀)) := mul_le_mul_of_nonneg_left hEe2 (by positivity)
  have hee : e ≤ |Ca| * (s ^ 2 + Real.exp (-(c * ρ₀))) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hP : Real.exp (-(c * ρ₀)) ≤ s ^ 2 + Real.exp (-(c * ρ₀)) := by nlinarith [sq_nonneg s]
  have hCbP : |Cb| * Real.exp (-(c * ρ₀)) ≤ |Cb| * (s ^ 2 + Real.exp (-(c * ρ₀))) :=
    mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  exact show 2 * ε ≤ (4 * |Cb| + 8 * |Ca|) * (s ^ 2 + Real.exp (-(c * ρ₀))) from by
    rw [hε]
    nlinarith
theorem curvatureNearDescendedForm (h₁ : logarithmOneStepStatement)
    (h₂ : responseLocalCurvatureContractionStatement) (h₃ : descentKeepsBallClearStatement)
    (h₄ : responseKernelRowSumBoundedStatement) : curvatureNearDescendedFormStatement :=
  holdsOnParameters_of_four _ _ _ _ _ h₁ h₂ h₃ h₄ curvatureNearDescendedFormAt_of
end YangMills.Construction.ResponseInTheExpansion
end
