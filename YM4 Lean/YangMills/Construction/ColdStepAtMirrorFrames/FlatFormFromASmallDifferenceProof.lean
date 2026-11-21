import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAtTheLeastFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifference
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open Filter Topology
open BlockAverages (imaginaryQuaternions BlockFrame)
open TorusLumps (offsetSupNorm offsetTriangleDiameter centered secondDerivLimitOnMultiples flatSecondDeriv
  curvatureAlong HasPolynomialGrowth SecondOrderOnMultiplesOfSide)
open TorusFields (torusFrame)
private abbrev IntPoint : Type := Fin 4 → ℤ
private abbrev IntBond : Type := (Fin 4 → ℤ) × Fin 4
private theorem natAbs_le_offsetSupNorm (u : IntPoint) (i : Fin 4) : (u i).natAbs ≤ offsetSupNorm u := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private def polyExpWeight (b : ℝ) (p : ℕ) (u : IntBond) : ℝ :=
  (1 + (offsetSupNorm u.1 : ℝ)) ^ p * Real.exp (-b * offsetSupNorm u.1)
private theorem polyExpWeight_nonneg (b : ℝ) (p : ℕ) (u : IntBond) : 0 ≤ polyExpWeight b p u := by
  unfold polyExpWeight
  positivity
private theorem summable_prod_coord (w : ℤ → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : Summable w) :
    Summable fun x : IntPoint => ∏ i, w (x i) := by
  classical
  refine summable_of_sum_le (c := (∑' k, w k) ^ 4) (fun x => Finset.prod_nonneg fun i _ => hw _) ?_
  intro s
  let U : Finset ℤ := s.biUnion fun x => Finset.univ.image x
  have hsub : s ⊆ Fintype.piFinset fun _ : Fin 4 => U := by
    intro x hx
    exact Fintype.mem_piFinset.2 fun i =>
      Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  calc ∑ x ∈ s, ∏ i, w (x i) ≤ ∑ x ∈ Fintype.piFinset fun _ : Fin 4 => U, ∏ i, w (x i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => Finset.prod_nonneg fun i _ => hw _
    _ = ∏ _i : Fin 4, ∑ k ∈ U, w k := by rw [Finset.prod_univ_sum]
    _ = (∑ k ∈ U, w k) ^ 4 := by simp
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hw k) (hs.sum_le_tsum U fun k _ => hw k) 4
abbrev _root_.YangMills.DeltaSharedProofs.p500462 := @summable_prod_coord
private theorem summable_geometric_natAbs {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun k : ℤ => ρ ^ k.natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_pow_natAbs <;> assumption
private theorem summable_polyExpWeight {b : ℝ} (hb : 0 < b) (p : ℕ) : Summable (polyExpWeight b p) := by
  set ρ : ℝ := Real.exp (-(b / 8)) with hρ
  have h0 : 0 ≤ ρ := (Real.exp_pos _).le
  have h1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    linarith
  have hs := summable_prod_coord (fun k => ρ ^ k.natAbs) (fun k => by positivity)
    (summable_geometric_natAbs h0 h1)
  set K : ℝ := (p.factorial : ℝ) * (2 / b) ^ p * Real.exp (b / 2) with hK
  have hKp : 0 < K := by positivity
  have hbd : ∀ u : IntPoint, (1 + (offsetSupNorm u : ℝ)) ^ p * Real.exp (-b * offsetSupNorm u) ≤
      K * ∏ i, ρ ^ (u i).natAbs := by
    intro u
    set s : ℝ := (offsetSupNorm u : ℝ) with hsdef
    have e1 : (1 + s) ^ p ≤ K * Real.exp (b / 2 * s) := by
      have h2 := Real.pow_div_factorial_le_exp (x := b / 2 * (1 + s)) (by positivity) p
      have hf : (0 : ℝ) < p.factorial := by positivity
      rw [div_le_iff₀ hf, mul_pow, show b / 2 * (1 + s) = b / 2 + b / 2 * s by ring, Real.exp_add] at h2
      have h3 : (2 / b) ^ p * (b / 2) ^ p = 1 := by
        rw [← mul_pow]
        have : 2 / b * (b / 2) = 1 := by field_simp
        rw [this, one_pow]
      calc (1 + s) ^ p = (2 / b) ^ p * ((b / 2) ^ p * (1 + s) ^ p) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ (2 / b) ^ p * (Real.exp (b / 2) * Real.exp (b / 2 * s) * (p.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = K * Real.exp (b / 2 * s) := by
            rw [hK]
            ring
    have e2 : Real.exp (-(b / 2) * s) ≤ ∏ i, ρ ^ (u i).natAbs := by
      have : ∏ i, ρ ^ (u i).natAbs = Real.exp (∑ i, (-(b / 8)) * ((u i).natAbs : ℝ)) := by
        rw [Real.exp_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hρ, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [this]
      apply Real.exp_le_exp.2
      have h4 : ∑ i, ((u i).natAbs : ℝ) ≤ 4 * s := by
        calc ∑ i, ((u i).natAbs : ℝ) ≤ ∑ _i : Fin 4, s :=
              Finset.sum_le_sum fun i _ => by rw [hsdef]; exact_mod_cast natAbs_le_offsetSupNorm u i
          _ = 4 * s := by simp
      rw [← Finset.mul_sum]
      nlinarith
    calc (1 + s) ^ p * Real.exp (-b * s) ≤ (K * Real.exp (b / 2 * s)) * Real.exp (-b * s) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = K * Real.exp (-(b / 2) * s) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 hKp.le
  have h2 : Summable fun u : IntBond => (K * ∏ i, ρ ^ (u.1 i).natAbs) * 1 :=
    Summable.mul_of_nonneg (f := fun u : IntPoint => K * ∏ i, ρ ^ (u i).natAbs) (g := fun _ : Fin 4 => (1 : ℝ))
      (hs.mul_left K) (hasSum_fintype (fun _ : Fin 4 => (1 : ℝ))).summable
      (fun u => by positivity) (fun _ => by simp)
  exact Summable.of_nonneg_of_le (polyExpWeight_nonneg b p) (fun u => by rw [mul_one]; exact hbd u.1) h2
abbrev _root_.YangMills.DeltaSharedProofs.p500449 := @summable_polyExpWeight
private theorem eventually_large_side (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (n₁ : ℕ) :
    ∀ᶠ n : ℕ in atTop, n₁ ≤ n ∧ 2 ≤ n ∧ 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 < γ₀ ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤ 1 ∧
      4 * Real.log (1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2)) ^ 2 + 4 < (n : ℝ) := by apply _root_.YangMills.SharedProofs.p36503 <;> assumption
private theorem constantPlaneCurvature_eq (X : imaginaryQuaternions) (μ ν : Fin 4) :
    constantPlaneCurvature X μ ν = curvatureAlong X (planeUnitForm μ ν) := by apply _root_.YangMills.SharedProofs.p53264 <;> assumption
private theorem planeUnitForm_antisymm (μ ν : Fin 4) (hμν : μ < ν) (i j : Fin 4) :
    planeUnitForm μ ν i j = - planeUnitForm μ ν j i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.planeUnitForm_antisymm <;> assumption
private theorem summable_bondWeight {r : ℝ} (hr : 0 < r) : Summable (bondWeight r) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.summable_latticeBondWeight <;> assumption
private theorem bondDeriv_two_smul (hjet : FormCompositionJet) {F : BlockFrame} {j : ℕ}
    (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (hs : ContDiffThreeAlongBonds G W) (c : Fin 2 → F.Site j × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (r : Fin 2 → ℝ) :
    bondDeriv G W c (fun l => r l • X l) = (∏ l, r l) * bondDeriv G W c X := by
  classical
  set B : Finset (F.Site j × Fin 4) := Finset.univ.image c with hB
  have hmem : ∀ l, c l ∈ B := fun l => Finset.mem_image_of_mem _ (Finset.mem_univ l)
  obtain ⟨_, h2, _⟩ := hjet ℝ F j B G W hs
  let c' : Fin 2 → ↥B := fun l => ⟨c l, hmem l⟩
  have e1 := h2 2 c' (fun l => r l • X l) (by norm_num)
  have e2 := h2 2 c' X (by norm_num)
  have hc : (fun l => (c' l).1) = c := rfl
  rw [hc] at e1 e2
  rw [← e1, ← e2]
  have hform : (fun l => singleBondForm (c' l) (r l • X l)) = fun l => r l • singleBondForm (c' l) (X l) := by
    funext l
    unfold singleBondForm
    rw [Pi.single_smul]
  rw [hform, ContinuousMultilinearMap.map_smul_univ]
  rfl
private theorem linearPotential_growth {Fm : Fin 4 → Fin 4 → imaginaryQuaternions}
    {B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions}
    (hB : IsLinearPotential Fm B) : HasPolynomialGrowth B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.hasPolynomialGrowth_of_linearPotential <;> assumption
private theorem exp_le_weight (ℓ : TorusLumps.StepParameters) (m : ℕ) :
    Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by
  unfold TorusLumps.StepParameters.weight
  have : (1 : ℝ) ≤ max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) := le_max_left _ _
  nlinarith [Real.exp_pos (ℓ.weightRate * m)]
abbrev _root_.YangMills.SharedProofs.p47115 := @exp_le_weight
theorem flatLimitFromSmallDifference_holds (hsec : SecondOrderOnMultiplesOfSide)
    (hform : FlatLimitFromExpansion) (htop : ConstantCurvatureTopOnTorus)
    (hread : TopFamilyOnTori) (hjet : FormCompositionJet) :
    flatLimitFromSmallDifference := by
  intro ℓ t C w g g₀ hfits hC hw hcf hcf₀ hs hs₀ hflat₀ hdiff
  have hr : 0 < ℓ.weightRate := by
    unfold TorusLumps.StepParameters.weightRate
    have := hfits.rt_pos
    positivity
  have hr6 : 0 < ℓ.weightRate / 6 := by positivity
  have hlw := summable_bondWeight hr6
  have hlw0 : ∀ u, 0 ≤ bondWeight (ℓ.weightRate / 6) u := by
    intro u
    unfold bondWeight
    positivity
  set e : ℝ := flatLimitDifferenceConstant (ℓ.weightRate / 6) * C ^ (1 / 3 : ℝ) * w ^ (2 / 3 : ℝ) with he
  have hC3 : 0 ≤ C ^ (1 / 3 : ℝ) := Real.rpow_nonneg hC _
  have hw3 : 0 ≤ w ^ (2 / 3 : ℝ) := Real.rpow_nonneg hw _
  have he0 : 0 ≤ e := by
    rw [he]
    unfold flatLimitDifferenceConstant
    positivity
  refine hform ℓ t C e g hfits he0 hcf ?_
  intro X μ ν hX hμν ε hε
  set h := densityOfTopFamily ℓ.side t g with hh
  set h₀ := densityOfTopFamily ℓ.side t g₀ with hh₀
  obtain ⟨hlim, hbd, _, hsum, _, _, hwide, _⟩ := hsec ℓ hfits 1 one_pos C h hcf
  obtain ⟨hlim₀, hbd₀, _, hsum₀, _, _, _, _⟩ := hsec ℓ hfits 1 one_pos C h₀ hcf₀
  have hflatOf : ∀ (g' : TopLevelFamily) (b b' : IntBond) (Y Y' : imaginaryQuaternions), ∀ᶠ n : ℕ in atTop,
      flatSecondDeriv (densityOfTopFamily ℓ.side t g') (1 * n) b b' Y Y' =
        secondDerivAtUniform g' ℓ.side t n b b' Y Y' := by
    intro g' b b' Y Y'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : NeZero n := ⟨hn.ne'⟩
    rw [one_mul]
    exact ((hread ℓ.side t 1 0 g' one_pos).2.2.2.2 n b b' Y Y').symm
  have hq : ∀ (b b' : IntBond) (Y Y' : imaginaryQuaternions),
      Tendsto (fun n => secondDerivAtUniform g ℓ.side t n b b' Y Y') atTop
        (𝓝 (secondDerivLimitOnMultiples 1 h b b' Y Y')) :=
    fun b b' Y Y' => (hlim b b' Y Y').congr' (hflatOf g b b' Y Y')
  have hq₀ : ∀ (b b' : IntBond) (Y Y' : imaginaryQuaternions),
      Tendsto (fun n => secondDerivAtUniform g₀ ℓ.side t n b b' Y Y') atTop
        (𝓝 (secondDerivLimitOnMultiples 1 h₀ b b' Y Y')) :=
    fun b b' Y Y' => (hlim₀ b b' Y Y').congr' (hflatOf g₀ b b' Y Y')
  have hhom : ∀ (g' : TopLevelFamily) (q' : BondBilinearForm),
      (∀ n, ℓ.n₀ ≤ n → ContDiffThreeAlongBonds (g' (torusFrame ℓ.side t n) 0) (uniformField _ _)) →
      (∀ (b b' : IntBond) (Y Y' : imaginaryQuaternions),
        Tendsto (fun n => secondDerivAtUniform g' ℓ.side t n b b' Y Y') atTop (𝓝 (q' b b' Y Y'))) →
      ∀ (b b' : IntBond) (r r' : ℝ), q' b b' (r • X) (r' • X) = r * r' * q' b b' X X := by
    intro g' q' hsm hl b b' r r'
    refine tendsto_nhds_unique (hl b b' _ _) (((hl b b' X X).const_mul (r * r')).congr' ?_)
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    have h1 := bondDeriv_two_smul hjet (g' (torusFrame ℓ.side t n) 0) (uniformField _ _) (hsm n hn)
      (bondsAt 0 ![b, b']) ![X, X] ![r, r']
    have h2 : (fun l => (![r, r'] : Fin 2 → ℝ) l • (![X, X] : Fin 2 → imaginaryQuaternions) l) =
        ![r • X, r' • X] := by
      funext l
      fin_cases l <;> rfl
    rw [h2] at h1
    have h3 : ∏ l, (![r, r'] : Fin 2 → ℝ) l = r * r' := by
      simp [Fin.prod_univ_two]
    rw [h3] at h1
    exact h1.symm
  set ω := planeUnitForm μ ν with hω
  have hωa : ∀ i j, ω i j = - ω j i := planeUnitForm_antisymm μ ν hμν
  have hω1 : ∀ a b, |ω a b| ≤ 1 := by
    intro a b
    rw [hω]
    unfold planeUnitForm
    split_ifs <;> simp
  let β : IntBond → ℝ := fun c => (1 / 2) * ∑ ν', ((c.1 ν' : ℤ) : ℝ) * ω ν' c.2
  let A : Fin 4 → Fin 4 → imaginaryQuaternions := fun i j => ((1 / 2 : ℝ) * ω j i) • X
  let B : IntBond → imaginaryQuaternions := fun c => β c • X
  have hBform : ∀ x i, B (x, i) = (∑ ν', ((x ν' : ℤ) : ℝ) • A i ν') + (0 : Fin 4 → imaginaryQuaternions) i := by
    intro x i
    apply Subtype.ext
    show (β (x, i)) • (X : Quaternion ℝ) = _
    simp only [Pi.zero_apply, add_zero, A, β, AddSubmonoidClass.coe_finset_sum]
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun ν' _ => ?_
    show _ = ((x ν' : ℤ) : ℝ) • (((1 / 2 : ℝ) * ω ν' i) • (X : Quaternion ℝ))
    rw [smul_smul]
    congr 1
    ring
  have hB' : IsLinearPotential (curvatureAlong X ω) B := by
    refine ⟨A, 0, hBform, fun a b => ?_⟩
    apply Subtype.ext
    show ((1 / 2 : ℝ) * ω a b) • (X : Quaternion ℝ) - ((1 / 2 : ℝ) * ω b a) • (X : Quaternion ℝ) =
      ω a b • (X : Quaternion ℝ)
    rw [← sub_smul]
    congr 1
    rw [hωa b a]
    ring
  have hB : IsLinearPotential (constantPlaneCurvature X μ ν) B := by
    rw [constantPlaneCurvature_eq]; exact hB'
  have hg := linearPotential_growth hB
  obtain ⟨Q, hQ1, hQ2⟩ := hflat₀
  have hQ : ∀ (b b' : IntBond) (Y Y' : imaginaryQuaternions), Q b b' Y Y' = secondDerivLimitOnMultiples 1 h₀ b b' Y Y' :=
    fun b b' Y Y' => tendsto_nhds_unique (hQ1 b b' Y Y') (hq₀ b b' Y Y')
  obtain ⟨v₀, hv₀, hv₀0⟩ := hQ2 X μ ν B hX hμν hB
  have hv₀z : v₀ = 0 := by
    have := abs_nonpos_iff.1 hv₀0
    exact this
  rw [hv₀z] at hv₀
  simp only [hQ] at hv₀
  have hS := (hsum B B hg hg).hasSum
  set S := ∑' cc : IntBond × IntBond, secondDerivLimitOnMultiples 1 h cc.1 cc.2 (B cc.1) (B cc.2) with hSdef
  have hdf := hS.sub hv₀
  rw [sub_zero] at hdf
  have hSbound : |S| ≤ e := by
    have hprod : HasSum (fun cc : IntBond × IntBond =>
        bondWeight (ℓ.weightRate / 6) cc.1 * bondWeight (ℓ.weightRate / 6) cc.2)
        ((∑' u, bondWeight (ℓ.weightRate / 6) u) * ∑' u, bondWeight (ℓ.weightRate / 6) u) :=
      hlw.hasSum.mul hlw.hasSum (Summable.mul_of_nonneg hlw hlw hlw0 hlw0)
    have hG := hprod.mul_left (8 * C ^ (1 / 3 : ℝ) * w ^ (2 / 3 : ℝ))
    have hval : 8 * C ^ (1 / 3 : ℝ) * w ^ (2 / 3 : ℝ) *
        ((∑' u, bondWeight (ℓ.weightRate / 6) u) * ∑' u, bondWeight (ℓ.weightRate / 6) u) = e := by
      rw [he]
      unfold flatLimitDifferenceConstant
      ring
    rw [hval] at hG
    have hnorm := tsum_of_norm_bounded hG (f := fun cc : IntBond × IntBond =>
      secondDerivLimitOnMultiples 1 h cc.1 cc.2 (B cc.1) (B cc.2) -
        secondDerivLimitOnMultiples 1 h₀ cc.1 cc.2 (B cc.1) (B cc.2)) ?_
    · rw [hdf.tsum_eq, Real.norm_eq_abs] at hnorm
      exact hnorm
    · rintro ⟨c, c'⟩
      dsimp only
      have e1 := hhom g (secondDerivLimitOnMultiples 1 h) hs hq c c' (β c) (β c')
      have e0 := hhom g₀ (secondDerivLimitOnMultiples 1 h₀) hs₀ hq₀ c c' (β c) (β c')
      show ‖secondDerivLimitOnMultiples 1 h c c' (β c • X) (β c' • X) -
        secondDerivLimitOnMultiples 1 h₀ c c' (β c • X) (β c' • X)‖ ≤ _
      rw [e1, e0, Real.norm_eq_abs]
      set D := secondDerivLimitOnMultiples 1 h c c' X X - secondDerivLimitOnMultiples 1 h₀ c c' X X with hD
      have hex : β c * β c' * secondDerivLimitOnMultiples 1 h c c' X X -
          β c * β c' * secondDerivLimitOnMultiples 1 h₀ c c' X X = β c * β c' * D := by
        rw [hD]; ring
      rw [hex, abs_mul, abs_mul]
      have hDw : |D| ≤ w := by
        refine le_of_tendsto (((hq c c' X X).sub (hq₀ c c' X X)).abs) ?_
        exact hdiff c c' X X hX hX
      set W := ℓ.weight (offsetTriangleDiameter c.1 c'.1) with hW
      have hWpos : 0 < W := lt_of_lt_of_le (Real.exp_pos _) (exp_le_weight ℓ _)
      have hDC : |D| ≤ 2 * C / W := by
        have h1 := hbd c c' X X
        have h2 := hbd₀ c c' X X
        rw [hX, one_mul, one_mul] at h1 h2
        have h3 := abs_sub (secondDerivLimitOnMultiples 1 h c c' X X) (secondDerivLimitOnMultiples 1 h₀ c c' X X)
        rw [hD]
        have : 2 * C / W = C / W + C / W := by ring
        rw [this]
        linarith
      set s : ℝ := (offsetSupNorm c.1 : ℝ) with hs'
      set s' : ℝ := (offsetSupNorm c'.1 : ℝ) with hs''
      have hβ : ∀ u : IntBond, |β u| ≤ 2 * (1 + (offsetSupNorm u.1 : ℝ)) := by
        intro u
        show |(1 / 2) * ∑ ν', ((u.1 ν' : ℤ) : ℝ) * ω ν' u.2| ≤ _
        rw [abs_mul]
        have h1 : |∑ ν', ((u.1 ν' : ℤ) : ℝ) * ω ν' u.2| ≤ ∑ _ν' : Fin 4, (offsetSupNorm u.1 : ℝ) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν' _ => ?_)
          rw [abs_mul]
          have h2 : |((u.1 ν' : ℤ) : ℝ)| ≤ (offsetSupNorm u.1 : ℝ) := by
            rw [Int.cast_abs.symm, Int.abs_eq_natAbs]
            exact_mod_cast natAbs_le_offsetSupNorm u.1 ν'
          have h3 := hω1 ν' u.2
          have h4 : 0 ≤ (offsetSupNorm u.1 : ℝ) := by positivity
          calc |((u.1 ν' : ℤ) : ℝ)| * |ω ν' u.2| ≤ (offsetSupNorm u.1 : ℝ) * 1 :=
                mul_le_mul h2 h3 (abs_nonneg _) h4
            _ = _ := mul_one _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        have h5 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [h5]
        push_cast at h1
        have h6 : 0 ≤ (offsetSupNorm u.1 : ℝ) := by positivity
        nlinarith
      have hmin : |D| ≤ w ^ (2 / 3 : ℝ) * (2 * C / W) ^ (1 / 3 : ℝ) := by
        have hD0 := abs_nonneg D
        have e : |D| = |D| ^ (2 / 3 : ℝ) * |D| ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_add_of_nonneg hD0 (by norm_num) (by norm_num)]
          norm_num
        rw [e]
        exact mul_le_mul (Real.rpow_le_rpow hD0 hDw (by norm_num)) (Real.rpow_le_rpow hD0 hDC (by norm_num))
          (Real.rpow_nonneg hD0 _) hw3
      have hspan : (s + s') / 2 ≤ (offsetTriangleDiameter c.1 c'.1 : ℝ) := by
        have h1 : (offsetSupNorm c.1 : ℝ) ≤ (offsetTriangleDiameter c.1 c'.1 : ℝ) := by
          unfold offsetTriangleDiameter
          exact_mod_cast (le_max_left _ _ : _ ≤ _).trans' (le_max_left _ _)
        have h2 : (offsetSupNorm c'.1 : ℝ) ≤ (offsetTriangleDiameter c.1 c'.1 : ℝ) := by
          unfold offsetTriangleDiameter
          exact_mod_cast (le_max_left _ _ : _ ≤ _).trans' (le_max_right _ _)
        linarith
      have hW3 : (2 * C / W) ^ (1 / 3 : ℝ) ≤
          2 * C ^ (1 / 3 : ℝ) * (Real.exp (-(ℓ.weightRate / 6 * s)) * Real.exp (-(ℓ.weightRate / 6 * s'))) := by
        have h1 : 2 * C / W ≤ 2 * C * Real.exp (-(ℓ.weightRate * (offsetTriangleDiameter c.1 c'.1 : ℝ))) := by
          rw [Real.exp_neg, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) (exp_le_weight ℓ _)
        have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
        refine h2.trans ?_
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, Real.mul_rpow (by norm_num) hC,
          ← Real.exp_mul, ← Real.exp_add]
        have h3 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 3 : ℝ) ≤ 1)
          simpa using this
        have h4 : Real.exp (-(ℓ.weightRate * (offsetTriangleDiameter c.1 c'.1 : ℝ)) * (1 / 3)) ≤
            Real.exp (-(ℓ.weightRate / 6 * s) + -(ℓ.weightRate / 6 * s')) := by
          apply Real.exp_le_exp.2
          nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_right h3 hC3) h4 (Real.exp_pos _).le (by positivity)
      have hb1 := hβ c
      have hb2 := hβ c'
      have hmain : |D| ≤ w ^ (2 / 3 : ℝ) * (2 * C ^ (1 / 3 : ℝ) *
          (Real.exp (-(ℓ.weightRate / 6 * s)) * Real.exp (-(ℓ.weightRate / 6 * s')))) :=
        hmin.trans (mul_le_mul_of_nonneg_left hW3 hw3)
      have hpr : |β c| * |β c'| ≤ (2 * (1 + s)) * (2 * (1 + s')) :=
        mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      have hfin := mul_le_mul hpr hmain (abs_nonneg _) (by positivity)
      refine hfin.trans (le_of_eq ?_)
      unfold bondWeight
      ring
  obtain ⟨γ₀, hγ₀, hw'⟩ := hwide ω hωa ε hε
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (eventually_large_side γ₀ hγ₀ 0)
  refine ⟨n₁, fun n _ hn => ?_⟩
  obtain ⟨_, h2, h3, h4, h5⟩ := hn₁ n hn
  set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
  have hγpos : 0 < γ := by
    rw [hγ]
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    simp only [Nat.cast_one, mul_one]
    positivity
  have hab := htop (torusFrame ℓ.side t n) X μ ν n 1 hfits.L_odd (fun _ => rfl) (by omega) hX hμν h4
  have h6 := hw' γ hγpos h3 n (one_dvd n) h5 X (constantCurvatureTop ℓ.side t n X μ ν) B hX hab hB' 0
  have h7 : |centered h n 0 (constantCurvatureTop ℓ.side t n X μ ν)| ≤
      |centered h n 0 (constantCurvatureTop ℓ.side t n X μ ν) - γ ^ 2 / 2 * S| + |γ ^ 2 / 2 * S| := by
    have := abs_add_le (centered h n 0 (constantCurvatureTop ℓ.side t n X μ ν) - γ ^ 2 / 2 * S) (γ ^ 2 / 2 * S)
    simpa using this
  have h8 : |γ ^ 2 / 2 * S| ≤ γ ^ 2 / 2 * e := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left hSbound (by positivity)
  refine h7.trans ?_
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
