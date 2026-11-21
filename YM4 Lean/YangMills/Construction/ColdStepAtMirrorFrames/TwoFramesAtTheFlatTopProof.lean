import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsACurvatureFamilyProof
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOne
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAtTheFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.MoveOfTheStepField
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.TwoFramesAtTheFlatTop
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem stepCoordinates_zero {F : BlockFrame} {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem bondDeriv_sub_const {F : BlockFrame} {j k : ℕ} (hk : k ≠ 0) (G : F.GaugeField j → ℝ) (v : ℝ)
    (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - v) W c X = bondDeriv G W c X := by apply _root_.YangMills.SharedProofs.p20334 <;> assumption
private theorem contDiffAt_two_and_iteratedFDeriv_sum {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : Finset ι) (g : ι → P → ℝ) (x : P)
    (h : ∀ c ∈ s, ContDiffAt ℝ 2 (g c) x) (u : Fin 2 → P) :
    ContDiffAt ℝ 2 (fun ζ => ∑ c ∈ s, g c ζ) x ∧
      iteratedFDeriv ℝ 2 (fun ζ => ∑ c ∈ s, g c ζ) x u = ∑ c ∈ s, iteratedFDeriv ℝ 2 (g c) x u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨contDiffAt_const, ?_⟩
    rw [iteratedFDeriv_const_of_ne (by norm_num)]
    rfl
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h3 := h a (Finset.mem_insert_self a s)
    have e : (fun ζ => ∑ c ∈ insert a s, g c ζ) = g a + fun ζ => ∑ c ∈ s, g c ζ := by
      funext ζ
      rw [Finset.sum_insert ha]
      rfl
    rw [e, Finset.sum_insert ha]
    refine ⟨h3.add h1, ?_⟩
    rw [iteratedFDeriv_add_apply h3 h1]
    simp only [add_apply, h2]
private theorem card_centredCube_for_two_frames (L : ℕ) (hL : Odd L) : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem card_sites_in_cell_le (hsb : SiteDecomposition) (F : BlockFrame) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      (F.blockSide : ℝ) ^ 4 := by
  classical
  obtain ⟨_, h2, _, _⟩ := hsb F hodd hs
  have hsub : (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y) ⊆
      (centredCube F.blockSide).image fun h => cellCentre F.depth Y + siteOfCoords F.depth h := by
    intro y hy
    obtain ⟨_, hc⟩ := Finset.mem_filter.1 hy
    obtain ⟨e1, e2⟩ := h2 y
    refine Finset.mem_image.2 ⟨cellOffset y, e2, ?_⟩
    rw [← hc]
    exact e1
  have h1 := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := centredCube F.blockSide)
    (f := fun h => cellCentre F.depth Y + siteOfCoords F.depth h)
  have h4 : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      ((centredCube F.blockSide).card : ℝ) := by
    exact_mod_cast h1.trans h3
  rw [card_centredCube_for_two_frames F.blockSide hodd] at h4
  exact h4
private theorem norm_firstDeriv_stepFrame_sub_le {F : BlockFrame} {a ρ δ₂ Cf σ : ℝ} {m : ℕ} (hδ : 0 ≤ δ₂)
    {V : F.GaugeField F.top}
    (hnear : FrameNearMinimizer a ρ δ₂ Cf σ m V) (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F))
    (h1 : IsBondAnalyticAt (stepFrame false a ρ m b) V) (h0 : IsBondAnalyticAt (stepFrame true a ρ m b) V)
    (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (hCf : 0 < Cf) :
    ‖bondDeriv (stepFrame false a ρ m b) V ![e] ![X] - bondDeriv (stepFrame true a ρ m b) V ![e] ![X]‖ ≤
      Cf * Real.exp (-(3 / 8 * δ₂ * m)) * Real.exp (-(δ₂ / 8 * cellSupDist (enclosingCell b.1) e.1)) := by
  have hw := (hnear b hb).2 1 ![e] ![X] le_rfl (by norm_num) (fun l => by fin_cases l; exact hX)
  set p₁ : (Fin 1 → ℝ) → imaginaryQuaternions :=
    fun τ => stepFrame false a ρ m b (leftTranslate (bondSpread ![e] ![X] τ) V) with hp₁
  set p₀ : (Fin 1 → ℝ) → imaginaryQuaternions :=
    fun τ => stepFrame true a ρ m b (leftTranslate (bondSpread ![e] ![X] τ) V) with hp₀
  have hd₁ : DifferentiableAt ℝ p₁ 0 := (h1 1 ![e] ![X]).differentiableAt
  have hd₀ : DifferentiableAt ℝ p₀ 0 := (h0 1 ![e] ![X]).differentiableAt
  have e1 : bondDeriv (frameDeviation a ρ m b) V ![e] ![X] =
      ((bondDeriv (stepFrame false a ρ m b) V ![e] ![X] - bondDeriv (stepFrame true a ρ m b) V ![e] ![X] :
        imaginaryQuaternions) : Quaternion ℝ) := by
    unfold bondDeriv
    simp only [iteratedFDeriv_one_apply]
    have hfn : (fun τ : Fin 1 → ℝ => frameDeviation a ρ m b (leftTranslate (bondSpread ![e] ![X] τ) V)) =
        fun τ => imaginaryQuaternions.subtypeL (p₁ τ) - imaginaryQuaternions.subtypeL (p₀ τ) := rfl
    have c₁ := imaginaryQuaternions.subtypeL.hasFDerivAt.comp (0 : Fin 1 → ℝ) hd₁.hasFDerivAt
    have c₀ := imaginaryQuaternions.subtypeL.hasFDerivAt.comp (0 : Fin 1 → ℝ) hd₀.hasFDerivAt
    have hsub : HasFDerivAt (fun τ => imaginaryQuaternions.subtypeL (p₁ τ) - imaginaryQuaternions.subtypeL (p₀ τ))
        (imaginaryQuaternions.subtypeL.comp (fderiv ℝ p₁ 0) - imaginaryQuaternions.subtypeL.comp (fderiv ℝ p₀ 0)) 0 :=
      c₁.sub c₀
    rw [hfn, hsub.fderiv]
    rfl
  have hn : ‖bondDeriv (stepFrame false a ρ m b) V ![e] ![X] - bondDeriv (stepFrame true a ρ m b) V ![e] ![X]‖ =
      ‖bondDeriv (frameDeviation a ρ m b) V ![e] ![X]‖ := by
    rw [e1]
    rfl
  rw [hn]
  refine hw.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hCf.le
  apply Real.exp_le_exp.2
  have hd : (cellSupDist (enclosingCell b.1) e.1 : ℝ) ≤ (bondListDistance (enclosingCell b.1) ![e] : ℝ) := by
    have : cellSupDist (enclosingCell b.1) e.1 ≤ bondListDistance (enclosingCell b.1) ![e] := by
      unfold bondListDistance
      exact Finset.le_sup (f := fun l : Fin 1 => cellSupDist (enclosingCell b.1) ((![e] : Fin 1 → _) l).1)
        (Finset.mem_univ 0)
    exact_mod_cast this
  have hm : (m : ℝ) ≤ max (m : ℝ) (bondListDistance (enclosingCell b.1) ![e] : ℝ) := le_max_left _ _
  have hl : (bondListDistance (enclosingCell b.1) ![e] : ℝ) ≤
      max (m : ℝ) (bondListDistance (enclosingCell b.1) ![e] : ℝ) := le_max_right _ _
  have hmain : 3 / 2 * (m : ℝ) + (cellSupDist (enclosingCell b.1) e.1 : ℝ) / 2 ≤
      (m : ℝ) + max (m : ℝ) (bondListDistance (enclosingCell b.1) ![e] : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ δ₂ / 4)
  push_cast at hmul ⊢
  linarith
theorem twoFramesAtUniformTop (hmove : fieldAboveFrameMoveStatement) (hnear : SecondOrderNearCritical)
    (hfirst : FirstDerivAtTrivialVanishes) (hgeo : CubicTorusCellGeometry)
    (hflatT : stepFramesAtUniformTop) (hcover : BlocksCoverLowerLevel)
    (hsb : SiteDecomposition) (hjet : FormCompositionJet) : twoFramesAtUniformTopStatement := by
  classical
  obtain ⟨C₀, hC₀, hmv⟩ := hmove
  obtain ⟨_, hsum⟩ := hgeo
  have hchoose : ∀ r : ℝ, ∃ c : ℝ, 0 ≤ c ∧ (0 < r → ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F →
      ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) z)) ≤ c * (F.blockSide : ℝ) ^ 4) := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨C, hC, h⟩ := hsum r hr
      exact ⟨C, hC.le, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hr⟩
  choose Cg hCg0 hCg using hchoose
  refine ⟨fun d => 2 * C₀ * Cg (d / 4) * Cg (d / 8), fun r => ?_, ?_⟩
  · have := hCg0 (r / 4)
    have := hCg0 (r / 8)
    positivity
  intro T Cf Cw hd hn₀ hCf hCw hCwσ t x f hx hm hrow hfr b b' X X' hX hX'
  have hδ : 0 < T.chainParams.δ₂ := hd.chain_admissible.classical.1.2.2.2.1
  have hσ : 0 < T.σ := hd.σ_pos
  have hE : 0 < T.E := by linarith [hd.one_le_E]
  set m := frameRadius x with hmdef
  filter_upwards [eventually_ge_atTop (max T.n₀ (max 64 (4 * m + 6)))] with n hn
  have hnn : T.n₀ ≤ n := le_trans (le_max_left _ _) hn
  have h64 : 64 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hbign : 4 * m + 6 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hfH := hfr n hnn
  set F := cubicTorusFrame T.L t n with hF
  have hodd : Odd F.blockSide := hd.odd_L
  have hside : ∀ i, F.extent i = n := fun _ => rfl
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hcub : IsLargeCubicTorus F := ⟨n, h64, hside⟩
  have hsite : ∀ z : F.Site F.depth, z ∈ sitesOfCells (finiteCells F) F.depth :=
    fun z => hcover F hodd (fun i => by rw [hside]; omega) z
  set B := fineBonds F with hBdef
  have hB : ∀ b : F.Site F.depth × Fin 4, b ∈ B := fun b => Finset.mem_product.2 ⟨hsite _, Finset.mem_univ _⟩
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ innerBonds (finiteCells F) F.depth := by
    intro b
    unfold innerBonds
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hsite _, Finset.mem_univ _⟩, hsite _⟩
  have hchart : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → b ∈ chordBonds (finiteCells F) :=
    fun b h => Finset.mem_filter.2 ⟨hbond b, h⟩
  set V₀ := uniformField F F.top with hV₀
  set W₀ := uniformField F F.depth with hW₀
  have hflat := fun o => hflatT T.a T.L T.chainParams m hd.one_le_a hd.odd_L hd.chain_admissible hm F o
    ⟨rfl, n, h64, hside⟩
  have hfb : ∀ o, StepFrameBounds o T.a T.chainParams.ρA T.chainParams.δ₂ Cw T.σ m V₀ := fun o =>
    ⟨(hfH.small o).norm_le, (hfH.small o).analytic, (hfH.small o).deriv_decay⟩
  set c : Fin 2 → F.Site F.top × Fin 4 := bondsAt 0 ![b, b'] with hc
  set Xs : Fin 2 → imaginaryQuaternions := ![X, X'] with hXs
  have hunit : AreUnitVectors Xs := by
    intro l
    fin_cases l
    · exact hX
    · exact hX'
  have hη : ∀ e, ‖(0 : StepVariable (finiteCells F)) e‖ ≤ 0 := by
    intro e
    simp
  obtain ⟨A, hA⟩ := hmv F false T.a T.chainParams.ρA T.chainParams.δ₂ Cw T.σ 0 m V₀ 0 2 c Xs B hB hchart hunit hCw
    hδ.le le_rfl (hfb false) (by linarith) hη
  obtain ⟨A₀, hA₀⟩ := hmv F true T.a T.chainParams.ρA T.chainParams.δ₂ Cw T.σ 0 m V₀ 0 2 c Xs B hB hchart hunit hCw
    hδ.le le_rfl (hfb true) (by linarith) hη
  set Kc : ℝ := C₀ * (Cw + 2) ^ 3 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set r : ℝ := T.chainParams.δ₂ / 4 with hr
  have hr0 : 0 < r := by positivity
  have hL0 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := by positivity
  have hsumB : ∀ (ρ : ℝ), 0 < ρ → ∀ z : F.Cell,
      ∑ b : ↥B, Real.exp (-(ρ * cellSupDist (enclosingCell b.1.1) z)) ≤ Cg ρ * (F.blockSide : ℝ) ^ 4 := by
    intro ρ hρ z
    rw [Finset.sum_coe_sort B (fun b => Real.exp (-(ρ * cellSupDist (enclosingCell b.1) z)))]
    exact hCg ρ hρ F hodd hcub z
  set S : ℝ := Kc * (Cg r * (F.blockSide : ℝ) ^ 4) with hS
  have hS0 : 0 ≤ S := mul_nonneg hKc0 (mul_nonneg (hCg0 r) hL0)
  have hone : ∀ (A' : (Fin 2 → ℝ) → ↥B → imaginaryQuaternions), MoveDerivDecay c Kc r A' → ∀ i : Fin 2,
      ∑ b, firstDerivNorm A' (slotBasisVector i) b ≤ S := by
    intro A' hdc i
    calc ∑ b, firstDerivNorm A' (slotBasisVector i) b ≤
          ∑ b : ↥B, Kc * Real.exp (-(r * cellSupDist (enclosingCell b.1.1) (c i).1)) :=
          Finset.sum_le_sum fun b _ => hdc.first i b
      _ = Kc * ∑ b : ↥B, Real.exp (-(r * cellSupDist (enclosingCell b.1.1) (c i).1)) := by rw [Finset.mul_sum]
      _ ≤ S := mul_le_mul_of_nonneg_left (hsumB r hr0 _) hKc0
  have htwo : ∑ b, secondDerivNorm A (slotBasisVector (0 : Fin 2)) (slotBasisVector (1 : Fin 2)) b ≤ S := by
    calc ∑ b, secondDerivNorm A (slotBasisVector (0 : Fin 2)) (slotBasisVector (1 : Fin 2)) b ≤
          ∑ b : ↥B, Kc * Real.exp (-(r * cellSupDist (enclosingCell b.1.1) (c 0).1)) :=
          Finset.sum_le_sum fun b _ => hA.decays.second 0 1 0 b (by decide) (Or.inl rfl)
      _ = Kc * ∑ b : ↥B, Real.exp (-(r * cellSupDist (enclosingCell b.1.1) (c 0).1)) := by rw [Finset.mul_sum]
      _ ≤ S := mul_le_mul_of_nonneg_left (hsumB r hr0 _) hKc0
  set e₀ : ℝ := Real.exp (-(3 / 8 * T.chainParams.δ₂ * m)) with he₀
  set Δ : ℝ := Cf * e₀ * (Cg (T.chainParams.δ₂ / 8) * (F.blockSide : ℝ) ^ 4) with hΔ
  have habove : ∀ (o : Bool) (b₁ : F.Site F.depth × Fin 4),
      coordsAboveFrame o T.a T.chainParams.ρA m V₀ (0 : StepVariable (finiteCells F)) b₁.1 b₁.2 = 0 := by
    intro o b₁
    unfold coordsAboveFrame
    rw [stepCoordinates_zero, add_zero]
    exact (hflat o).1 (b₁.1, b₁.2)
  have hbig : ∀ i, 4 * m + 5 < F.extent i := fun i => by rw [hside]; omega
  have hgap : ∀ i : Fin 2, firstDerivGap A A₀ (slotBasisVector i) ≤ Δ := by
    intro i
    unfold firstDerivGap
    have hp : 0 < T.chainParams.δ₂ / 8 := by positivity
    calc ∑ b, ‖iteratedFDeriv ℝ 1 (fun τ => A τ b) 0 ![slotBasisVector i] -
          iteratedFDeriv ℝ 1 (fun τ => A₀ τ b) 0 ![slotBasisVector i]‖
        ≤ ∑ b : ↥B, Cf * e₀ * Real.exp (-(T.chainParams.δ₂ / 8 * cellSupDist (enclosingCell b.1.1) (c i).1)) := by
          refine Finset.sum_le_sum fun b _ => ?_
          by_cases ht : IsAxialTreeBond b.1
          · have e1 : (fun τ => A τ b) = fun _ => 0 := funext fun τ => hA.tree_bond b τ ht
            have e2 : (fun τ => A₀ τ b) = fun _ => 0 := funext fun τ => hA₀.tree_bond b τ ht
            rw [e1, e2, sub_self]
            simp only [norm_zero]
            positivity
          · have n1 := hA.first_deriv_near i b ht
            have n0 := hA₀.first_deriv_near i b ht
            rw [habove, norm_zero, mul_zero] at n1 n0
            have e1 := sub_eq_zero.1 (norm_le_zero_iff.1 n1)
            have e0 := sub_eq_zero.1 (norm_le_zero_iff.1 n0)
            rw [e1, e0, add_sub_add_right_eq_sub]
            exact norm_firstDeriv_stepFrame_sub_le hδ.le (hfH.near hbig) b.1 (hchart _ ht)
              ((hfH.small false).analytic _ (hchart _ ht))
              ((hfH.small true).analytic _ (hchart _ ht)) (c i) (Xs i) (hunit i) hCf
      _ = Cf * e₀ * ∑ b : ↥B, Real.exp (-(T.chainParams.δ₂ / 8 * cellSupDist (enclosingCell b.1.1) (c i).1)) := by
          rw [Finset.mul_sum]
      _ ≤ Δ := mul_le_mul_of_nonneg_left (hsumB _ hp _) (by positivity)
  have hΔ0 : 0 ≤ Δ := mul_nonneg (by positivity) (mul_nonneg (hCg0 _) hL0)
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨rfl, rfl, n, hside, le_trans hnn (Nat.le_mul_of_pos_right n hd.odd_L.pos)⟩
  have hcoldW : IsSmallCurvature T.σ W₀ := by
    intro p _
    have : plaquetteHolonomy W₀ p = 1 := by
      simp [plaquetteHolonomy, pathHolonomy, linkValue, hW₀, uniformField]
    unfold plaquetteDefect
    rw [this]
    simpa using hσ
  let Wf : Bool → (Fin 2 → ℝ) → F.GaugeField F.depth := fun o τ =>
    fieldAboveFrame o T.a T.chainParams.ρA m (leftTranslate (bondSpread c Xs τ) V₀) 0
  have hmovesF : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), Wf false τ = leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (A τ)) W₀ :=
    hA.eventually_eq.mono fun τ h => by
      have h' := h
      rw [(hflat false).2] at h'
      exact h'
  have hmovesT : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), Wf true τ = leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (A₀ τ)) W₀ :=
    hA₀.eventually_eq.mono fun τ h => by
      have h' := h
      rw [(hflat true).2] at h'
      exact h'
  set u : Fin 2 → ℝ := slotBasisVector (0 : Fin 2) with hu
  set v : Fin 2 → ℝ := slotBasisVector (1 : Fin 2) with hv
  have hy : ∀ y : F.Site F.depth,
      ContDiffAt ℝ 2 (fun τ => subtractTrivial f F y (Wf false τ)) 0 ∧
      ContDiffAt ℝ 2 (fun τ => subtractTrivial f F y (Wf true τ)) 0 ∧
      |iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (Wf false τ)) 0 ![u, v] -
        iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (Wf true τ)) 0 ![u, v]| ≤ 2 * T.E * S * Δ := by
    intro y
    set Gy := subtractTrivial f F y with hGy
    have hsG : ContDiffThreeAlongBonds Gy W₀ := by
      intro k c' X'
      exact (hrow.smooth F hlow y W₀ hcoldW k c' X').sub contDiffAt_const
    have hcomp : ∀ (A' : (Fin 2 → ℝ) → ↥B → imaginaryQuaternions) (o : Bool), ContDiffAt ℝ 3 A' 0 → A' 0 = 0 →
        (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), Wf o τ = leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (A' τ)) W₀) →
        ContDiffAt ℝ 2 (fun τ => Gy (Wf o τ)) 0 := by
      intro A' o h1 h2 h3
      have hj := (hjet ℝ F F.depth B Gy W₀ hsG).1
      rw [← h2] at hj
      have h4 : ContDiffAt ℝ 3 (fun τ => formComposition B Gy W₀ (A' τ)) 0 := hj.comp 0 h1
      refine (h4.of_le (by norm_num)).congr_of_eventuallyEq ?_
      filter_upwards [h3] with τ hτ
      show Gy (Wf o τ) = Gy (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (A' τ)) W₀)
      rw [hτ]
    refine ⟨hcomp A false hA.smooth hA.map_zero hmovesF, hcomp A₀ true hA₀.smooth hA₀.map_zero hmovesT, ?_⟩
    have hres := (hnear F F.depth B Gy Gy W₀ W₀ (Fin 2 → ℝ) (Wf false) (Wf true) A A₀ 0 T.E S Δ u v hsG hsG
      hA.smooth hA.map_zero hmovesF
      hA₀.smooth hA₀.map_zero hmovesT le_rfl hE.le hS0 (fun _ _ _ => by simp) (fun _ _ _ => by simp) ?_ ?_
      (hone A hA.decays 0) (hone A hA.decays 1) (hone A₀ hA₀.decays 1) (hone A₀ hA₀.decays 0) htwo
      (hgap 0) (hgap 1)).1
    · refine hres.trans (le_of_eq ?_)
      ring
    · intro c' X' _
      rw [hGy]
      have e := bondDeriv_sub_const (by norm_num : (1 : ℕ) ≠ 0) (f F y) (f F y (uniformField F F.depth)) W₀
        (fun l => (c' l).1) X'
      show bondDeriv (fun V => f F y V - f F y (uniformField F F.depth)) W₀ (fun l => (c' l).1) X' = 0
      rw [e]
      exact hfirst T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F hrow hσ hlow y _ X'
    · intro c' X' hX2
      have e := bondDeriv_sub_const (by norm_num : (2 : ℕ) ≠ 0) (f F y) (f F y (uniformField F F.depth)) W₀
        (fun l => (c' l).1) X'
      show |bondDeriv (fun V => f F y V - f F y (uniformField F F.depth)) W₀ (fun l => (c' l).1) X'| ≤ _
      rw [e]
      refine (hrow.decay F hlow y W₀ 2 _ X' hcoldW (by norm_num) (by norm_num) hX2).trans ?_
      have hw : 1 ≤ torusDecayFactor T.L T.decayRate (bondSpan y fun l => (c' l).1) := by
        unfold torusDecayFactor
        have h1 : (1 : ℝ) ≤
            max 1 (((bondSpan y fun l => (c' l).1 : ℕ) / (T.L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
          le_max_left _ _
        have hδ0 : 0 ≤ T.decayRate := by
          show 0 ≤ T.κ / 2 ^ 10
          have := hd.κ_pos
          positivity
        have h2 : (1 : ℝ) ≤ Real.exp (T.decayRate * (bondSpan y fun l => (c' l).1 : ℕ)) :=
          Real.one_le_exp (by positivity)
        nlinarith
      simp only [show (2 : ℕ) ≠ 3 by norm_num, if_false]
      exact div_le_self hE.le hw
  have hunits : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![u, v] := by
    funext l
    fin_cases l <;> rfl
  set blk := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = (0 : F.Cell)) with hblk
  have hval : ∀ o : Bool, secondDerivAtUniform (expansionAtFrameFamily T o x f) T.L t n b b' X X' =
      ∑ y ∈ blk, iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (Wf o τ)) 0 ![u, v] := by
    intro o
    have hs := contDiffAt_two_and_iteratedFDeriv_sum blk (fun y τ => subtractTrivial f F y (Wf o τ)) 0
      (fun y _ => by
        cases o
        · exact (hy y).1
        · exact (hy y).2.1) ![u, v]
    rw [← hs.2, ← hunits]
    rfl
  rw [hval, hval, ← Finset.sum_sub_distrib]
  have hcnt := card_sites_in_cell_le hsb F hodd hs2 (0 : F.Cell)
  have hsumb : |∑ y ∈ blk, (iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (Wf false τ)) 0 ![u, v] -
      iteratedFDeriv ℝ 2 (fun τ => subtractTrivial f F y (Wf true τ)) 0 ![u, v])| ≤
        (F.blockSide : ℝ) ^ 4 * (2 * T.E * S * Δ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_card_nsmul _ _ _ fun y _ => (hy y).2.2).trans ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcnt (by positivity)
  refine hsumb.trans ?_
  have hFL : (F.blockSide : ℝ) = (T.L : ℝ) := rfl
  unfold twoFramesGapBound
  rw [hS, hΔ, hKc, hFL, he₀]
  have hc2 : (1 : ℝ) ≤ Cw + 2 := by linarith
  have hp : (Cw + 2) ^ 3 ≤ (Cw + 2) ^ 6 := pow_le_pow_right₀ hc2 (by norm_num)
  have hg0 : 0 ≤ Cg (T.chainParams.δ₂ / 4) := hCg0 _
  have hg1 : 0 ≤ Cg (T.chainParams.δ₂ / 8) := hCg0 _
  have hbase : 0 ≤ 2 * C₀ * Cg (T.chainParams.δ₂ / 4) * Cg (T.chainParams.δ₂ / 8) * (T.L : ℝ) ^ 12 * T.E * Cf *
      Real.exp (-(3 / 8 * T.chainParams.δ₂ * m)) := by positivity
  have := mul_le_mul_of_nonneg_left hp hbase
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
