import YangMills.Construction.HullsInEveryVolume.ChessboardOnABareGrid
import YangMills.Construction.HullsInEveryVolume.NoisesOfSeparateSetsMultiply
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ChainNoise ChessboardGrids
private theorem isProbabilityMeasure_chainNoiseLaw (ℓ : TorusLumps.StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n) := by apply _root_.YangMills.SharedProofs.p2413 <;> assumption
private theorem noiseAgreeAbove_refl (ℓ : TorusLumps.StepParameters) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (U : ChainNoise.ChainNoise ℓ u n),
      NoiseAgreeAbove ℓ u n Q U U := by
  induction u with
  | zero => intro n _ Q U; trivial
  | succ u ih =>
    intro n _ Q U
    exact ⟨ih _ _ _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
private theorem isCellFunction_noiseExpectation (hBelow : sitesUnderCellStatement) {ℓ : TorusLumps.StepParameters}
    {u n : ℕ} [NeZero n] (hodd : Odd ℓ.side) {g : MirrorGrid} {c : Fin 4 → ℕ}
    {Φ : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n → ℝ} (hin : IsCellObservable ℓ g u n c Φ) :
    IsCellFunction (g.atDepth ℓ.side u) (fineSide ℓ.side u n) c (noiseExpectation ℓ u n Φ) := by
  haveI := isProbabilityMeasure_chainNoiseLaw ℓ u n
  obtain ⟨C, hC⟩ := hin.bounded
  refine ⟨?_, ⟨C, fun W => ?_⟩, fun W => integral_nonneg fun U => hin.nonneg _, fun W W' h => ?_⟩
  · exact (hin.measurable.stronglyMeasurable.integral_prod_right' (ν := chainNoiseLaw ℓ u n)).measurable
  · have := norm_integral_le_of_norm_le_const (μ := chainNoiseLaw ℓ u n) (f := fun U => Φ (W, U)) (C := C)
      (Filter.Eventually.of_forall fun U => by simpa using hC (W, U))
    show |∫ U, Φ (W, U) ∂(chainNoiseLaw ℓ u n)| ≤ C
    simpa using this
  · refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hs := (hBelow ℓ.side u n g c hodd).1 (g.cellSites n c) (Finset.Subset.refl _)
    exact hin.depends W W' U U (fun b h1 h2 => h b (hs h1) (hs h2)) (noiseAgreeAbove_refl ℓ u n _ U)
private theorem cellIndices_atDepth_fineSide {L v n : ℕ} (hL : 0 < L) (gr : MirrorGrid) :
    (gr.atDepth L v).cellIndices (fineSide L v n) = gr.cellIndices n := by
  simp only [MirrorGrid.cellIndices, MirrorGrid.atDepth, fineSide_eq]
  rw [Nat.mul_div_mul_right _ _ (pow_pos hL v)]
theorem separateCellsExpectation_holds (hCh : chessboardEstimateStatement) (hNo : disjointNoisesMultiplyStatement)
    (hBelow : sitesUnderCellStatement) : separateCellsExpectationStatement := by
  classical
  intro ℓ β u n M _ g hodd h16 hβ hn hdeep hgrid ι I c Φ hc hinj hin
  have hL : 0 < ℓ.side := hodd.pos
  have hN : fineSide ℓ.side u n = 2 * ℓ.side ^ (M + u) := by
    calc fineSide ℓ.side u n = n * ℓ.side ^ u := fineSide_eq _ _ _
      _ = (2 * ℓ.side ^ M) * ℓ.side ^ u := by rw [← hn]
      _ = 2 * ℓ.side ^ (M + u) := by rw [pow_add]; ring
  have hgrid' : IsGridOfTorus (g.atDepth ℓ.side u) ℓ.side (M + u) := by
    obtain ⟨p, hp1, hpM, hs⟩ := hgrid
    exact ⟨p + u, by omega, by omega, by
      show g.side * ℓ.side ^ u = ℓ.side ^ (p + u)
      rw [hs, pow_add]⟩
  obtain ⟨h1, h2⟩ := hCh ℓ.side (M + u) (fineSide ℓ.side u n) β (g.atDepth ℓ.side u) hodd h16 hdeep hβ hN hgrid'
  have hind := cellIndices_atDepth_fineSide (v := u) (n := n) hL g
  set F : ι → TorusField (fineSide ℓ.side u n) → ℝ := fun i => noiseExpectation ℓ u n (Φ i) with hF
  have hsplit : ∀ W, noiseExpectation ℓ u n (fun p => ∏ i ∈ I, Φ i p) W = ∏ i ∈ I, F i W := by
    intro W
    refine hNo ℓ u n I (fun i => g.cellSites n (c i)) Φ (fun i hi i' hi' hii => ?_) (fun i hi => ?_) W
    · refine Finset.disjoint_left.2 fun x hx hx' => hii (hinj hi hi' ?_)
      have e1 := (Finset.mem_filter.1 hx).2
      have e2 := (Finset.mem_filter.1 hx').2
      exact e1.symm.trans e2
    · have := hin i hi
      exact ⟨this.measurable, this.bounded, this.depends⟩
  let G : (Fin 4 → ℕ) → TorusField (fineSide ℓ.side u n) → ℝ := fun c' =>
    if h : ∃ i ∈ I, c i = c' then F h.choose else fun _ => 1
  have hG : ∀ i ∈ I, G (c i) = F i := by
    intro i hi
    have h : ∃ i' ∈ I, c i' = c i := ⟨i, hi, rfl⟩
    simp only [G, dif_pos h]
    rw [hinj h.choose_spec.1 hi h.choose_spec.2]
  have hG1 : ∀ c', c' ∉ I.image c → G c' = fun _ => 1 := by
    intro c' hc'
    have h : ¬ ∃ i ∈ I, c i = c' := fun ⟨i, hi, e⟩ => hc' (Finset.mem_image.2 ⟨i, hi, e⟩)
    simp only [G, dif_neg h]
  have hall : ∀ c' ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
      IsCellFunction (g.atDepth ℓ.side u) (fineSide ℓ.side u n) c' (G c') := by
    intro c' _
    by_cases h : c' ∈ I.image c
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      rw [hG i hi]
      exact isCellFunction_noiseExpectation hBelow hodd (hin i hi)
    · rw [hG1 c' h]
      exact ⟨measurable_const, ⟨1, fun _ => by simp⟩, fun _ => zero_le_one, fun _ _ _ => rfl⟩
  have hsub : I.image c ⊆ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n) := by
    rw [hind]
    intro c' h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact hc i hi
  have hprod : ∀ W, ∏ i ∈ I, F i W = ∏ c' ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n), G c' W := by
    intro W
    rw [← Finset.prod_subset hsub (fun c' _ h => by rw [hG1 c' h]), Finset.prod_image hinj]
    exact Finset.prod_congr rfl fun i hi => by rw [hG i hi]
  have hnorm : ∏ i ∈ I, (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) (c i) (F i) =
      ∏ c' ∈ (g.atDepth ℓ.side u).cellIndices (fineSide ℓ.side u n),
        (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) c' (G c') := by
    rw [← Finset.prod_subset hsub (fun c' hc' h => by rw [hG1 c' h]; exact (h2 c' hc').2), Finset.prod_image hinj]
    exact Finset.prod_congr rfl fun i hi => by rw [hG i hi]
  show ∫ W, noiseExpectation ℓ u n (fun p => ∏ i ∈ I, Φ i p) W ∂(wilsonLaw β (fineSide ℓ.side u n)) ≤
    ∏ i ∈ I, (g.atDepth ℓ.side u).chessboardNormAt β (fineSide ℓ.side u n) (c i) (F i)
  rw [hnorm]
  refine le_trans (le_of_eq ?_) (h1 G hall)
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => by
    show noiseExpectation ℓ u n (fun p => ∏ i ∈ I, Φ i p) W = _
    rw [hsplit, hprod])
end YangMills.Construction.MomentLaw
end
