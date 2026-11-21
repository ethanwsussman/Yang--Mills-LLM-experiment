import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansionProof
import YangMills.Construction.LawByMomentsOfTheFlow.FormIsCarried
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.ResponseInTheExpansion.SumAgainstTwoGaugedResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
namespace PullbackBound
private theorem valMinAbs_intCast_cast {a b : ℕ} [NeZero a] (h : a = b) (u : ZMod a) :
    (((u.cast : ℤ) : ZMod b)).valMinAbs = u.valMinAbs := by
  subst h
  rw [ZMod.intCast_zmod_cast]
private theorem siteSupDist_eq_torus {F : BlockAverages.BlockFrame} {j N : ℕ} [NeZero N]
    (hp : ∀ i, F.period j i = N) (x y : F.Site j) :
    ColdStepAtMirrorFrames.siteSupDist x y =
      TorusFields.supDist (TorusLumps.toTorusSite N x) (TorusLumps.toTorusSite N y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.frameSupDist_eq_supDist <;> assumption
private theorem norm_unitGenerator : ‖WeightedResponses.unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
section Forms
variable {m : ℕ} [NeZero m]
private theorem bilinearEval_add_left (q : BondBilinear m) (A B C : TorusFields.TorusBond m → ℝ) :
    bilinearEval q (fun b => A b + B b) C = bilinearEval q A C + bilinearEval q B C := by
  simp only [bilinearEval, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_add_right (q : BondBilinear m) (A B C : TorusFields.TorusBond m → ℝ) :
    bilinearEval q A (fun b => B b + C b) = bilinearEval q A B + bilinearEval q A C := by
  simp only [bilinearEval, mul_add, Finset.sum_add_distrib]
private theorem bilinearEval_add_gradients {q : BondBilinear m} (hq : AnnihilatesGradients q)
    (A C : TorusFields.TorusBond m → ℝ) (φ ψ : TorusFields.TorusSite m → ℝ) :
    bilinearEval q (fun b => A b + latticeGradient φ b) (fun b => C b + latticeGradient ψ b) =
      bilinearEval q A C := by
  rw [bilinearEval_add_left q A (latticeGradient φ) _, (hq φ _).1, add_zero,
    bilinearEval_add_right q A C (latticeGradient ψ), (hq ψ A).2, add_zero]
private theorem abs_bilinearEval_le {q : BondBilinear m} {sz : ℝ}
    {w : TorusFields.TorusBond m → TorusFields.TorusBond m → ℝ} (h : ∀ b b', |q b b'| ≤ sz / w b b')
    (A C : TorusFields.TorusBond m → ℝ) :
    |bilinearEval q A C| ≤ sz * ∑ b, ∑ b', (w b b')⁻¹ * |A b| * |C b'| := by
  unfold bilinearEval
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (h b b') (abs_nonneg (A b))
  have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (C b'))
  calc _ ≤ |A b| * (sz / w b b') * |C b'| := h2
    _ = _ := by rw [div_eq_mul_inv]; ring
end Forms
set_option maxHeartbeats 4000000 in
private theorem pullback_sum_bound_on_frame {a ρ del Ca δ : ℝ} {L L₀ : ℕ} [NeZero L] (hodd : Odd L)
    (hL₀ : L₀ ≤ L) (hδ : 0 < δ) (hδd : δ ≤ del / 64)
    (hS : ∀ (F : BlockAverages.BlockFrame) (δ : ℝ) (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4)
      (B : Fin 2 → ColdStepAtMirrorFrames.FormChain F) (W : Fin 2 → ColdStepAtMirrorFrames.LevelForm F F.depth),
      Odd F.blockSide → L₀ ≤ F.blockSide → BlockAverages.IsLargeCubicTorus F → 0 < δ → δ ≤ del / 64 →
      (∀ i, ColdStepAtMirrorFrames.IsFlatChain a (c i) (B i)) →
      (∀ i, ColdStepAtMirrorFrames.IsAxialResponse (c i) (B i) (W i)) →
      ∑ y ∈ ColdStepAtMirrorFrames.blockFineSites Y, ∑ b₁ ∈ ColdStepAtMirrorFrames.fineBonds F,
        ∑ b₂ ∈ ColdStepAtMirrorFrames.fineBonds F,
        (BlockAverages.torusDecayFactor F.blockSide δ (ColdStepAtMirrorFrames.bondSpan y ![b₁, b₂]))⁻¹ *
          |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
          |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| ≤
        Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) /
          BlockAverages.torusDecayFactor F.blockSide δ (ColdStepAtMirrorFrames.bondSpan Y c))
    (hT : ∀ (F : BlockAverages.BlockFrame) (b : F.Site F.top × Fin 4) (X : BlockAverages.imaginaryQuaternions),
      F.blockSide = L → BlockAverages.IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : ColdStepAtMirrorFrames.FormChain F, ColdStepAtMirrorFrames.IsFlatChain a b B ∧
        ColdStepAtMirrorFrames.IsAxialResponse b B (ColdStepAtMirrorFrames.minimizerResponse a ρ b X))
    (u n : ℕ) [NeZero n] (h64 : 64 ≤ n) (Y : TorusFields.TorusSite n) (sz : ℝ) (hsz : 0 ≤ sz)
    (qs : TorusFields.TorusSite (n * L) → BondBilinear (n * L))
    (hk : ∀ y ∈ TorusLumps.sitesInBlocks L {Y}, AnnihilatesGradients (qs y))
    (hq : ∀ y ∈ TorusLumps.sitesInBlocks L {Y}, ∀ b b',
      |qs y b b'| ≤ sz / BlockAverages.torusDecayFactor L δ (tripleDiam y b b'))
    (c₁ c₂ : TorusFields.TorusBond n) :
    |∑ y ∈ TorusLumps.sitesInBlocks L {Y}, pullbackForm a ρ L u (qs y) c₁ c₂| ≤
      Ca * (L : ℝ) ^ (50 / 640 : ℝ) * sz / BlockAverages.torusDecayFactor L δ (tripleDiam Y c₁ c₂) := by
  classical
  let F : BlockAverages.BlockFrame := TorusFields.torusFrame L u n
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hp : ∀ i, F.period F.depth i = n * L := fun i => TopLevelSites.period_depth_of_extent hn i
  have hpn : ∀ i, F.period F.top i = n := fun i => TopLevelSites.period_top_of_extent hn i
  have hs : ∀ i, 0 < F.extent i := fun i => by
    rw [hn]
    omega
  have hoddF : Odd F.blockSide := hodd
  let ι : TorusFields.TorusSite (n * L) → F.Site F.depth := StepCosts.torusSiteInFrame F F.depth
  have hleft : ∀ x, TorusLumps.toTorusSite (n * L) (ι x) = x := fun x =>
    TopLevelSites.toTorusSite_torusSiteInFrame hp x
  have hright : ∀ x : F.Site F.depth, ι (TorusLumps.toTorusSite (n * L) x) = x := fun x =>
    TopLevelSites.torusSiteInFrame_toTorusSite hp x
  let cc : Fin 2 → TorusFields.TorusBond n := ![c₁, c₂]
  let Y' : F.Cell := StepCosts.torusSiteInFrame F F.top Y
  let c' : Fin 2 → F.Site F.top × Fin 4 := fun i => (StepCosts.torusSiteInFrame F F.top (cc i).1, (cc i).2)
  have hcub : BlockAverages.IsLargeCubicTorus F := ⟨n, h64, hn⟩
  choose Bc hflat htree using fun i => hT F (c' i) WeightedResponses.unitGenerator rfl hcub norm_unitGenerator
  let W : Fin 2 → ColdStepAtMirrorFrames.LevelForm F F.depth := fun i =>
    ColdStepAtMirrorFrames.minimizerResponse a ρ (c' i) WeightedResponses.unitGenerator
  have hW : ∀ i (b : TorusFields.TorusBond (n * L)),
      W i (ι b.1) b.2 = WeightedResponses.responseKernel a ρ L u b (cc i) := fun i b => rfl
  let φ : Fin 2 → F.Site F.depth → F.Site F.depth → ℝ := fun i y z =>
    ColdStepAtMirrorFrames.smoothCutoff (Real.sqrt L) y z *
      (-ColdStepAtMirrorFrames.pathSum (W i) y
        (BlockAverages.axisPath (ColdStepAtMirrorFrames.siteOffset y z) 1))
  let G : Fin 2 → TorusFields.TorusSite (n * L) → TorusFields.TorusBond (n * L) → ℝ := fun i y b =>
    WeightedResponses.responseKernel a ρ L u b (cc i) + latticeGradient (fun z => φ i (ι y) (ι z)) b
  have hadd : ∀ (x : TorusFields.TorusSite (n * L)) (e : Fin 4),
      ι (x + TorusFields.unitStep (n * L) e) = ι x + BlockAverages.unitStep F.depth e := by
    intro x e
    show StepCosts.torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * L) e) = _
    rw [TopLevelSites.torusSiteInFrame_add hp]
    congr 1
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_unitStep hp]
  have hG : ∀ i y (b : TorusFields.TorusBond (n * L)),
      ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt L) (ι y) (W i) (ι b.1) b.2 = G i y b := by
    intro i y b
    show W i (ι b.1) b.2 + (φ i (ι y) (ι b.1 + BlockAverages.unitStep F.depth b.2) - φ i (ι y) (ι b.1)) = _
    rw [hW, ← hadd]
    rfl
  have hdist : ∀ x z : TorusFields.TorusSite (n * L),
      ColdStepAtMirrorFrames.siteSupDist (ι x) (ι z) = TorusFields.supDist x z := fun x z => by
    rw [siteSupDist_eq_torus hp, hleft, hleft]
  have hspanY : ColdStepAtMirrorFrames.bondSpan Y' c' = tripleDiam Y c₁ c₂ := by
    unfold ColdStepAtMirrorFrames.bondSpan tripleDiam TorusFields.supportDiam
    simp only [siteSupDist_eq_torus hpn, Y', c']
    simp only [TopLevelSites.toTorusSite_torusSiteInFrame hpn]
    rfl
  have hsp : ∀ (y : TorusFields.TorusSite (n * L)) (b b' : TorusFields.TorusBond (n * L)),
      ColdStepAtMirrorFrames.bondSpan (ι y) ![(ι b.1, b.2), (ι b'.1, b'.2)] = tripleDiam y b b' := by
    intro y b b'
    have e : (![(ι b.1, b.2), (ι b'.1, b'.2)] : Fin 2 → F.Site F.depth × Fin 4) =
        fun l => (ι ((![b, b'] : Fin 2 → TorusFields.TorusBond (n * L)) l).1,
          ((![b, b'] : Fin 2 → TorusFields.TorusBond (n * L)) l).2) := by
      funext l
      fin_cases l <;> rfl
    rw [e]
    unfold ColdStepAtMirrorFrames.bondSpan tripleDiam TorusFields.supportDiam
    simp only [hdist]
  have hmem : ∀ x : F.Site F.depth,
      x ∈ BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells F) F.depth := fun x =>
    (GaugeFixing.mem_sitesOfCells_depth hs hoddF _ x).2 (TopLevelSites.mem_finiteCells hs _)
  have : NeZero (n * F.blockSide) := inferInstanceAs (NeZero (n * L))
  have hblock : ∀ y : TorusFields.TorusSite (n * L),
      BlockAverages.enclosingCell (ι y) = StepCosts.torusSiteInFrame F F.top (TorusLumps.parentBlock L y) :=
    fun y => TopLevelSites.enclosingCell_torusSiteInFrame hn y
  have hEq : ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, ∑ b : TorusFields.TorusBond (n * L),
      ∑ b' : TorusFields.TorusBond (n * L),
      (BlockAverages.torusDecayFactor L δ (tripleDiam y b b'))⁻¹ * |G 0 y b| * |G 1 y b'| =
      ∑ y ∈ ColdStepAtMirrorFrames.blockFineSites Y', ∑ b₁ ∈ ColdStepAtMirrorFrames.fineBonds F,
        ∑ b₂ ∈ ColdStepAtMirrorFrames.fineBonds F,
        (BlockAverages.torusDecayFactor F.blockSide δ (ColdStepAtMirrorFrames.bondSpan y ![b₁, b₂]))⁻¹ *
          |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
          |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| := by
    refine Finset.sum_nbij' ι (TorusLumps.toTorusSite (n * L)) ?_ ?_ (fun y _ => hleft y)
      (fun x _ => hright x) ?_
    · intro y hy
      have hyY : TorusLumps.parentBlock L y = Y := by simpa [TorusLumps.sitesInBlocks] using hy
      refine Finset.mem_filter.2 ⟨hmem _, ?_⟩
      rw [hblock, hyY]
    · intro x hx
      have hxY : BlockAverages.enclosingCell x = Y' := (Finset.mem_filter.1 hx).2
      have h2 := hblock (TorusLumps.toTorusSite (n * L) x)
      rw [hright, hxY] at h2
      have h3 : Y = TorusLumps.parentBlock L (TorusLumps.toTorusSite (n * L) x) := by
        have h4 := congrArg (TorusLumps.toTorusSite n) h2
        rwa [TopLevelSites.toTorusSite_torusSiteInFrame hpn,
          TopLevelSites.toTorusSite_torusSiteInFrame hpn] at h4
      simp [TorusLumps.sitesInBlocks, ← h3]
    · intro y _
      refine Finset.sum_nbij' (fun b => (ι b.1, b.2))
        (fun b' => (TorusLumps.toTorusSite (n * L) b'.1, b'.2)) ?_ ?_ ?_ ?_ ?_
      · intro b _
        exact Finset.mem_product.2 ⟨hmem _, Finset.mem_univ _⟩
      · intro b' _
        exact Finset.mem_univ _
      · intro b _
        exact Prod.ext (hleft _) rfl
      · intro b' _
        exact Prod.ext (hright _) rfl
      · intro b _
        refine Finset.sum_nbij' (fun b => (ι b.1, b.2))
          (fun b' => (TorusLumps.toTorusSite (n * L) b'.1, b'.2)) ?_ ?_ ?_ ?_ ?_
        · intro b _
          exact Finset.mem_product.2 ⟨hmem _, Finset.mem_univ _⟩
        · intro b' _
          exact Finset.mem_univ _
        · intro b _
          exact Prod.ext (hleft _) rfl
        · intro b' _
          exact Prod.ext (hright _) rfl
        · intro b' _
          show _ = (BlockAverages.torusDecayFactor L δ
              (ColdStepAtMirrorFrames.bondSpan (ι y) ![(ι b.1, b.2), (ι b'.1, b'.2)]))⁻¹ *
            |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt L) (ι y) (W 0) (ι b.1) b.2| *
            |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt L) (ι y) (W 1) (ι b'.1) b'.2|
          rw [hsp, hG, hG]
  have hSum : ∑ y ∈ ColdStepAtMirrorFrames.blockFineSites Y', ∑ b₁ ∈ ColdStepAtMirrorFrames.fineBonds F,
      ∑ b₂ ∈ ColdStepAtMirrorFrames.fineBonds F,
      (BlockAverages.torusDecayFactor F.blockSide δ (ColdStepAtMirrorFrames.bondSpan y ![b₁, b₂]))⁻¹ *
        |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |ColdStepAtMirrorFrames.localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| ≤
      Ca * (L : ℝ) ^ (50 / 640 : ℝ) / BlockAverages.torusDecayFactor L δ (tripleDiam Y c₁ c₂) := by
    have h := hS F δ Y' c' Bc W hoddF hL₀ hcub hδ hδd hflat htree
    rw [hspanY] at h
    exact h
  have hsite : ∀ y ∈ TorusLumps.sitesInBlocks L {Y}, |pullbackForm a ρ L u (qs y) c₁ c₂| ≤
      sz * ∑ b : TorusFields.TorusBond (n * L), ∑ b' : TorusFields.TorusBond (n * L),
        (BlockAverages.torusDecayFactor L δ (tripleDiam y b b'))⁻¹ * |G 0 y b| * |G 1 y b'| := by
    intro y hy
    have e : pullbackForm a ρ L u (qs y) c₁ c₂ = bilinearEval (qs y) (G 0 y) (G 1 y) :=
      (bilinearEval_add_gradients (hk y hy) (fun b => WeightedResponses.responseKernel a ρ L u b c₁)
        (fun b => WeightedResponses.responseKernel a ρ L u b c₂)
        (fun z => φ 0 (ι y) (ι z)) (fun z => φ 1 (ι y) (ι z))).symm
    rw [e]
    exact abs_bilinearEval_le (hq y hy) _ _
  calc |∑ y ∈ TorusLumps.sitesInBlocks L {Y}, pullbackForm a ρ L u (qs y) c₁ c₂|
      ≤ ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, |pullbackForm a ρ L u (qs y) c₁ c₂| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, sz * ∑ b : TorusFields.TorusBond (n * L),
        ∑ b' : TorusFields.TorusBond (n * L),
        (BlockAverages.torusDecayFactor L δ (tripleDiam y b b'))⁻¹ * |G 0 y b| * |G 1 y b'| :=
        Finset.sum_le_sum hsite
    _ = sz * ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, ∑ b : TorusFields.TorusBond (n * L),
        ∑ b' : TorusFields.TorusBond (n * L),
        (BlockAverages.torusDecayFactor L δ (tripleDiam y b b'))⁻¹ * |G 0 y b| * |G 1 y b'| := by
        rw [Finset.mul_sum]
    _ ≤ sz * (Ca * (L : ℝ) ^ (50 / 640 : ℝ) / BlockAverages.torusDecayFactor L δ (tripleDiam Y c₁ c₂)) :=
        mul_le_mul_of_nonneg_left (by rw [hEq]; exact hSum) hsz
    _ = Ca * (L : ℝ) ^ (50 / 640 : ℝ) * sz / BlockAverages.torusDecayFactor L δ (tripleDiam Y c₁ c₂) := by
        ring
private theorem mul_rpow_le_sqrt {Ca : ℝ} {L : ℕ} (hL : ⌈(max Ca 1) ^ 3⌉₊ ≤ L) :
    Ca * (L : ℝ) ^ (50 / 640 : ℝ) ≤ (L : ℝ) ^ ((1 : ℝ) / 2) := by
  set M : ℝ := max Ca 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := by linarith
  have hLM : M ^ 3 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have hL1 : (1 : ℝ) ≤ L := by
    have : (1 : ℝ) ≤ M ^ 3 := one_le_pow₀ hM1
    linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hroot : M ≤ (L : ℝ) ^ ((1 : ℝ) / 3) := by
    have h1 : (M ^ 3) ^ ((1 : ℝ) / 3) ≤ (L : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    have h2 : (M ^ 3) ^ ((1 : ℝ) / 3) = M := by
      rw [← Real.rpow_natCast M 3, ← Real.rpow_mul hM0]
      norm_num
    rwa [h2] at h1
  have hpos : 0 ≤ (L : ℝ) ^ (50 / 640 : ℝ) := Real.rpow_nonneg hL0 _
  calc Ca * (L : ℝ) ^ (50 / 640 : ℝ) ≤ M * (L : ℝ) ^ (50 / 640 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ (L : ℝ) ^ ((1 : ℝ) / 3) * (L : ℝ) ^ (50 / 640 : ℝ) := mul_le_mul_of_nonneg_right hroot hpos
    _ = (L : ℝ) ^ ((1 : ℝ) / 3 + 50 / 640) := (Real.rpow_add (by linarith) _ _).symm
    _ ≤ (L : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
private theorem torusDecayFactor_nonneg (L : ℕ) (δ x : ℝ) : 0 ≤ BlockAverages.torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.torusDecayWeight_nonneg <;> assumption
end PullbackBound
open PullbackBound in
theorem pullbackFormBound_holds (h₁ : WeightedResponses.TwoGaugedResponseSumBound)
    (h₂ : ColdStepAtMirrorFrames.AxialResponseOfMinimizers) : pullbackFormBoundStatement := by
  intro a ha
  obtain ⟨del, Ca, hdel, hCa, L₀, hS⟩ := h₁ a ha
  refine ⟨max L₀ ⌈(max Ca 1) ^ 3⌉₊, fun _ => del, 0, fun _ => hdel, ?_⟩
  intro L hodd hL T hTa hTL hD hCS _ hrt _
  subst hTa hTL
  refine ⟨0, fun z _ _ _ => ?_⟩
  obtain ⟨cn, _, hTies, _⟩ := hCS
  have hc : cn.Admissible T.coupling T.side := hTies.2.2.2.2.2.2.2
  have hρ : cn.ρA = T.ρA := hTies.2.2.1
  have hδ : 0 < T.rt / 2 ^ 10 := by
    have := hD.rt_pos
    positivity
  have hδd : T.rt / 2 ^ 10 ≤ del / 64 := by
    have h : T.rt ≤ del := hrt
    linarith
  have h64 : ∀ n : ℕ, (T.stepParameters z).n₀ ≤ n → 64 ≤ n := fun n hn => by
    have h1 : 4096 ≤ T.n₀ := hD.n₀_ge
    have h2 : T.n₀ ≤ n := hn
    omega
  intro u n _ hn Y sz hsz qs hqs c₁ c₂
  have hcore := pullback_sum_bound_on_frame (a := T.coupling) (ρ := T.ρA) (del := del) (Ca := Ca)
    (δ := T.rt / 2 ^ 10) (L := T.side) (L₀ := L₀)
    hD.L_odd ((le_max_left _ _).trans hL) hδ hδd hS
    (fun F b X hF hcub hX => by
      have h := h₂ T.coupling ha T.side hD.L_odd cn hc F b X hF hcub hX
      rwa [hρ] at h)
    u n (h64 n hn) Y sz hsz qs (fun y hy => (hqs y hy).1) (fun y hy b b' => (hqs y hy).2 b b') c₁ c₂
  refine hcore.trans ?_
  have hroot := mul_rpow_le_sqrt (Ca := Ca) (L := T.side) ((le_max_right _ _).trans hL)
  show Ca * (T.side : ℝ) ^ (50 / 640 : ℝ) * sz /
      BlockAverages.torusDecayFactor T.side (T.rt / 2 ^ 10) (tripleDiam Y c₁ c₂) ≤
    (T.side : ℝ) ^ ((1 : ℝ) / 2) * sz /
      BlockAverages.torusDecayFactor T.side (T.rt / 2 ^ 10) (tripleDiam Y c₁ c₂)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hsz) (torusDecayFactor_nonneg _ _ _)
end YangMills.Construction.MomentLaw
end
