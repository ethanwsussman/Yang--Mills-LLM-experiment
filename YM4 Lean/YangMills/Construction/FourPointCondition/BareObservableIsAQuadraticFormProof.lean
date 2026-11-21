import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.FourPointCondition.BareObservableIsAQuadraticForm
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChain
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedForm
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfTheDerivativesOfTheCutProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open scoped Quaternion
open MeasureTheory
open ResponseInTheExpansion WeightedResponses TorusFields
open BlockAverages LumpContours TopLevelSites
open Classical
namespace FourPointCondition
namespace BareObservable
variable {ℓ : TorusLumps.StepParameters}
private theorem norm_minimalLog_descent_le (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion),
      IsGaugeSmallAlong T k nn ρ₀ s d n u o g → ∀ b : TorusBond (fineSide ℓ.side d n),
        b.1 ∈ supBall o (ballRadius ℓ.side nn ρ₀ 0) →
        ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (gaugeDescent k d n u g) (topField ℓ k _ (sampleBelow ℓ k d n u)) b) : ℍ[ℝ])‖ ≤ s := by
  induction d with
  | zero =>
    intro n _ u o g h b hb
    exact h b hb
  | succ d ih =>
    intro n _ u o g h b hb
    exact ih (n * ℓ.side) u.1 o _ h.2.2 b hb
private theorem sum_imaginaryComponent_sq (w : imaginaryQuaternions) :
    ∑ e : Fin 3, imaginaryComponent e w ^ 2 = ‖(w : ℍ[ℝ])‖ ^ 2 := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have h := Quaternion.normSq_eq_norm_mul_self (w : ℍ[ℝ])
  rw [Quaternion.normSq_def'] at h
  rw [Fin.sum_univ_three, sq ‖(w : ℍ[ℝ])‖, ← h, hre]
  simp [imaginaryComponent]
private def plaquetteEnergyConst (B : ℝ) : ℝ := 14 * (10 + B) + 2 * (10 + B) ^ 2
private theorem plaquetteEnergyConst_bound {s ε B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B) :
    (10 + B) * (s ^ 2 + ε) * (28 * s + (10 + B) * (s ^ 2 + ε)) / 2 ≤ plaquetteEnergyConst B * (s ^ 3 + ε) := by
  have h1 : ε * s ≤ ε := mul_le_of_le_one_right hε0 hs1
  have hτs : (s ^ 2 + ε) * s ≤ s ^ 3 + ε := by
    have e : (s ^ 2 + ε) * s = s ^ 3 + ε * s := by ring
    rw [e]
    linarith
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  have h4 : s ^ 2 * s ^ 2 ≤ s ^ 3 := by
    have e : s ^ 2 * s ^ 2 = s ^ 3 * s := by ring
    rw [e]
    exact mul_le_of_le_one_right hs3 hs1
  have h5 : s ^ 2 * ε ≤ ε := mul_le_of_le_one_left hε0 (pow_le_one₀ hs0 hs1)
  have h6 : ε * ε ≤ ε := mul_le_of_le_one_left hε0 hε1
  have hττ : (s ^ 2 + ε) * (s ^ 2 + ε) ≤ 3 * (s ^ 3 + ε) := by
    have e : (s ^ 2 + ε) * (s ^ 2 + ε) = s ^ 2 * s ^ 2 + 2 * (s ^ 2 * ε) + ε * ε := by ring
    rw [e]
    linarith
  have hD : 0 ≤ 10 + B := by linarith
  have hD2 : 0 ≤ (10 + B) ^ 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hτs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14) hD)
  have a2 := mul_le_mul_of_nonneg_left hττ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hD2)
  have hX : 0 ≤ (10 + B) ^ 2 * (s ^ 3 + ε) / 2 := by positivity
  have e : (10 + B) * (s ^ 2 + ε) * (28 * s + (10 + B) * (s ^ 2 + ε)) / 2 =
      14 * (10 + B) * ((s ^ 2 + ε) * s) + 1 / 2 * (10 + B) ^ 2 * ((s ^ 2 + ε) * (s ^ 2 + ε)) := by ring
  have e2 : plaquetteEnergyConst B * (s ^ 3 + ε) =
      14 * (10 + B) * (s ^ 3 + ε) + 1 / 2 * (10 + B) ^ 2 * (3 * (s ^ 3 + ε)) + (10 + B) ^ 2 * (s ^ 3 + ε) / 2 := by
    unfold plaquetteEnergyConst
    ring
  rw [e, e2]
  linarith
private theorem abs_plaquetteEnergy_sub_half_sq_le {m : ℕ} [NeZero m] (W : TorusField m) (g : TorusSite m → UnitQuaternion)
    (o : TorusSite m) (R s B ε : ℝ) (p : TorusPlaquette m)
    (G : imaginaryQuaternions) (hp : p ∈ plaquettesIn (supBall o R)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hlog : ∀ b : TorusBond m, b.1 ∈ supBall o R → ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    (hG : ‖((lieFormCurl (ballLog g W o R) p - G : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ B * (s ^ 2 + ε)) :
    |plaquetteEnergyOf W p - (1 / 2) * ∑ e : Fin 3, imaginaryComponent e G ^ 2| ≤ plaquetteEnergyConst B * (s ^ 3 + ε) := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.mp hp).2.2
  have hx : x ∈ supBall o R := hc x (by simp [plaquetteVertices])
  have hxμ : x + TorusFields.unitStep m μ ∈ supBall o R := hc _ (by simp [plaquetteVertices])
  have hxν : x + TorusFields.unitStep m ν ∈ supBall o R := hc _ (by simp [plaquetteVertices])
  set a₁ : imaginaryQuaternions := minimalLog (ResponseInTheExpansion.gaugeTransform g W (x, μ)) with ha₁
  set a₂ : imaginaryQuaternions := minimalLog (ResponseInTheExpansion.gaugeTransform g W (x + TorusFields.unitStep m μ, ν)) with ha₂
  set a₃ : imaginaryQuaternions := minimalLog (ResponseInTheExpansion.gaugeTransform g W (x + TorusFields.unitStep m ν, μ)) with ha₃
  set a₄ : imaginaryQuaternions := minimalLog (ResponseInTheExpansion.gaugeTransform g W (x, ν)) with ha₄
  have n₁ : ‖a₁‖ ≤ s := hlog (x, μ) hx
  have n₂ : ‖a₂‖ ≤ s := hlog (x + TorusFields.unitStep m μ, ν) hxμ
  have n₃ : ‖a₃‖ ≤ s := hlog (x + TorusFields.unitStep m ν, μ) hxν
  have n₄ : ‖a₄‖ ≤ s := hlog (x, ν) hx
  have hcurl : lieFormCurl (ballLog g W o R) (x, μ, ν) = a₁ + a₂ - a₃ - a₄ := by
    simp only [lieFormCurl, ballLog, if_pos hx, if_pos hxμ, if_pos hxν]
    rfl
  have hplaq : holonomy (TorusFields.gaugeTransform g W) x μ ν =
      ColdStepAtMirrorFrames.SmallUnits.scaledPlaquette a₁ a₂ a₃ a₄ 1 1 1 1 := by
    simp only [ColdStepAtMirrorFrames.SmallUnits.scaledPlaquette, one_smul, ha₁, ha₂, ha₃, ha₄, expUnit_minimalLog]
    rfl
  have hlin := ColdStepAtMirrorFrames.SmallUnits.norm_scaledPlaquette_sub_linear_le a₁ a₂ a₃ a₄ 1 1 1 1 s hs1 n₁ n₂ n₃ n₄
    (by simp) (by simp) (by simp) (by simp)
  rw [← hplaq] at hlin
  simp only [one_smul] at hlin
  set Q : ℍ[ℝ] := ((holonomy (TorusFields.gaugeTransform g W) x μ ν : UnitQuaternion) : ℍ[ℝ]) - 1 with hQ
  set D : ℍ[ℝ] := (a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ]) - (a₃ : ℍ[ℝ]) - (a₄ : ℍ[ℝ]) with hDdef
  have hGD : ‖D - (G : ℍ[ℝ])‖ ≤ B * (s ^ 2 + ε) := by
    rw [hcurl] at hG
    exact hG
  have hDn : ‖D‖ ≤ 4 * s := by
    have m₁ : ‖(a₁ : ℍ[ℝ])‖ ≤ s := n₁
    have m₂ : ‖(a₂ : ℍ[ℝ])‖ ≤ s := n₂
    have m₃ : ‖(a₃ : ℍ[ℝ])‖ ≤ s := n₃
    have m₄ : ‖(a₄ : ℍ[ℝ])‖ ≤ s := n₄
    have t₁ := norm_sub_le ((a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ]) - (a₃ : ℍ[ℝ])) (a₄ : ℍ[ℝ])
    have t₂ := norm_sub_le ((a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ])) (a₃ : ℍ[ℝ])
    have t₃ := norm_add_le (a₁ : ℍ[ℝ]) (a₂ : ℍ[ℝ])
    linarith
  have hs2 : s ^ 2 ≤ s := by
    rw [sq]
    exact mul_le_of_le_one_left hs0 hs1
  have hτ0 : 0 ≤ s ^ 2 + ε := by positivity
  have hD10 : 0 ≤ 10 + B := by linarith
  have ht0 : 0 ≤ (10 + B) * (s ^ 2 + ε) := mul_nonneg hD10 hτ0
  have hQG : ‖Q - (G : ℍ[ℝ])‖ ≤ (10 + B) * (s ^ 2 + ε) := by
    have e : Q - (G : ℍ[ℝ]) = (Q - D) + (D - (G : ℍ[ℝ])) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have e2 : (10 + B) * (s ^ 2 + ε) = 10 * s ^ 2 + 10 * ε + B * (s ^ 2 + ε) := by ring
    rw [e2]
    linarith
  have hQn : ‖Q‖ ≤ 14 * s := by
    have e : Q = (Q - D) + D := by abel
    have h3 := norm_add_le (Q - D) D
    rw [← e] at h3
    linarith
  have hGn : ‖(G : ℍ[ℝ])‖ ≤ ‖Q‖ + (10 + B) * (s ^ 2 + ε) := by
    have e : (G : ℍ[ℝ]) = Q - (Q - (G : ℍ[ℝ])) := by abel
    have h3 := norm_sub_le Q (Q - (G : ℍ[ℝ]))
    rw [← e] at h3
    linarith
  have hdiff : |‖Q‖ - ‖(G : ℍ[ℝ])‖| ≤ (10 + B) * (s ^ 2 + ε) := (abs_norm_sub_norm_le _ _).trans hQG
  have hen : plaquetteEnergyOf W (x, μ, ν) = ‖Q‖ ^ 2 / 2 := by
    show plaquetteEnergy W x μ ν = _
    rw [← _root_.YangMills.Construction.TorusFields.plaquetteEnergy_gaugeTransform g, plaquetteEnergy_eq_curvature_sq]
    rfl
  rw [hen, sum_imaginaryComponent_sq]
  have e : ‖Q‖ ^ 2 / 2 - 1 / 2 * ‖(G : ℍ[ℝ])‖ ^ 2 = (‖Q‖ - ‖(G : ℍ[ℝ])‖) * (‖Q‖ + ‖(G : ℍ[ℝ])‖) / 2 := by ring
  rw [e, abs_div, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg Q) (norm_nonneg (G : ℍ[ℝ]))),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum : ‖Q‖ + ‖(G : ℍ[ℝ])‖ ≤ 28 * s + (10 + B) * (s ^ 2 + ε) := by linarith
  have hprod : |‖Q‖ - ‖(G : ℍ[ℝ])‖| * (‖Q‖ + ‖(G : ℍ[ℝ])‖) ≤
      (10 + B) * (s ^ 2 + ε) * (28 * s + (10 + B) * (s ^ 2 + ε)) :=
    mul_le_mul hdiff hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) ht0
  have harith := plaquetteEnergyConst_bound hs0 hs1 hε0 hε1 hB
  linarith
private def quadFormConst (B : ℝ) : ℝ := 16 * 27 ^ 4 * plaquetteEnergyConst B
private theorem quadFormConst_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ quadFormConst B := by
  unfold quadFormConst plaquetteEnergyConst
  positivity
private theorem card_supBall_le {m : ℕ} [NeZero m] (o : TorusSite m) (r : ℕ) :
    ((supBall o (r : ℝ)).card : ℝ) ≤ (2 * (r : ℝ) + 1) ^ 4 := by
  have hmaps : Set.MapsTo (fun z : TorusSite m => fun i => (z i - o i).valMinAbs) (supBall o (r : ℝ) : Set (TorusSite m))
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r : Finset (Fin 4 → ℤ)) := by
    intro z hz
    have hz' : (supDist z o : ℝ) ≤ r := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
    have hz'' : supDist z o ≤ r := by exact_mod_cast hz'
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have h1 : ((z i - o i).valMinAbs).natAbs ≤ supDist z o :=
      Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 := h1.trans hz''
    rw [Finset.mem_Icc]
    show -(r : ℤ) ≤ (z i - o i).valMinAbs ∧ (z i - o i).valMinAbs ≤ r
    omega
  have hinj : Set.InjOn (fun z : TorusSite m => fun i => (z i - o i).valMinAbs) (supBall o (r : ℝ) : Set (TorusSite m)) := by
    intro z _ w _ hzw
    funext i
    have h := congrFun hzw i
    have h' := congrArg (fun a : ℤ => (a : ZMod m)) h
    simp only [ZMod.coe_valMinAbs] at h'
    exact sub_left_injective h'
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Fintype.card_piFinset] at h1
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
  rw [h2] at h1
  exact_mod_cast h1
abbrev _root_.YangMills.SharedProofs.p88713 := @card_supBall_le
private theorem card_plaquettesIn_le {m : ℕ} [NeZero m] (S : Finset (TorusSite m)) :
    ((plaquettesIn S).card : ℝ) ≤ 16 * (S.card : ℝ) := by
  have hsub : plaquettesIn S ⊆ S ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2.2
    refine Finset.mem_product.mpr ⟨hc p.1 (by simp [plaquetteVertices]), Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product] at h1
  have h2 : (Finset.univ : Finset (Fin 4 × Fin 4)).card = 16 := by simp
  rw [h2] at h1
  have h3 : ((plaquettesIn S).card : ℝ) ≤ ((S.card * 16 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith
private theorem card_plaquettesIn_supBall_le {m : ℕ} [NeZero m] (o : TorusSite m) {nn : ℝ} (hnn : 1 ≤ nn) :
    ((plaquettesIn (supBall o (12 * nn))).card : ℝ) ≤ 16 * 27 ^ 4 * nn ^ 4 := by
  have hsub : supBall o (12 * nn) ⊆ supBall o ((⌈12 * nn⌉₊ : ℕ) : ℝ) := by
    intro z hz
    have := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.trans (Nat.le_ceil _)⟩
  have h1 : ((supBall o (12 * nn)).card : ℝ) ≤ ((supBall o ((⌈12 * nn⌉₊ : ℕ) : ℝ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 := card_supBall_le o ⌈12 * nn⌉₊
  have h3 : ((⌈12 * nn⌉₊ : ℕ) : ℝ) ≤ 13 * nn := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 12 * nn)).le
    linarith
  have h4 : (2 * ((⌈12 * nn⌉₊ : ℕ) : ℝ) + 1) ^ 4 ≤ (27 * nn) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have h5 := card_plaquettesIn_le (supBall o (12 * nn))
  calc ((plaquettesIn (supBall o (12 * nn))).card : ℝ) ≤ 16 * ((supBall o (12 * nn)).card : ℝ) := h5
    _ ≤ 16 * (27 * nn) ^ 4 := by linarith
    _ = 16 * 27 ^ 4 * nn ^ 4 := by ring
private theorem abs_le_weightSup {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (p : OrientedPlaquette m) :
    |h p.1| ≤ weightSup h :=
  le_ciSup (f := fun p : OrientedPlaquette m => |h p.1|) (Set.finite_range _).bddAbove p
private theorem abs_curvatureObservable_sub_quadForm_le {m : ℕ} [NeZero m] (W : TorusField m)
    (g : TorusSite m → UnitQuaternion) (o : TorusSite m) (R s B ε nn : ℝ)
    (h : PlaquetteWeight m) (G : TorusPlaquette m → imaginaryQuaternions) (hnn : 1 ≤ nn) (hR : 12 * nn ≤ R) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B) (hh : weightSup h ≤ 1)
    (hz : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), p ∉ plaquettesIn (supBall o (12 * nn)) → h p = 0)
    (hlog : ∀ b : TorusBond m, b.1 ∈ supBall o R → ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    (hG : ∀ p ∈ plaquettesIn (supBall o R),
      ‖((lieFormCurl (ballLog g W o R) p - G p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ B * (s ^ 2 + ε)) :
    |curvatureObservable h W -
        (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ, h p * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2| ≤
      quadFormConst B * nn ^ 4 * (s ^ 3 + ε) := by
  have hsub : plaquettesIn (supBall o (12 * nn)) ⊆ plaquettesIn (Finset.univ : Finset (TorusSite m)) := by
    intro p hp
    have := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨this.1, this.2.1, fun _ _ => Finset.mem_univ _⟩
  have hsub' : plaquettesIn (supBall o (12 * nn)) ⊆ plaquettesIn (supBall o R) := by
    intro p hp
    have := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨this.1, this.2.1, fun z hz' => ?_⟩
    have h2 := (Finset.mem_filter.mp (this.2.2 z hz')).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.trans hR⟩
  have e : curvatureObservable h W -
        (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ, h p * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2 =
      ∑ p ∈ plaquettesIn (supBall o (12 * nn)),
        h p * (plaquetteEnergyOf W p - (1 / 2) * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2) := by
    have e1 : curvatureObservable h W -
          (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ, h p * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2 =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
          h p * (plaquetteEnergyOf W p - (1 / 2) * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2) := by
      unfold curvatureObservable
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [e1]
    refine (Finset.sum_subset hsub fun p hp hp' => ?_).symm
    rw [hz p hp hp', zero_mul]
  rw [e]
  have hK : 0 ≤ plaquetteEnergyConst B := by
    unfold plaquetteEnergyConst
    positivity
  have hbound : ∀ p ∈ plaquettesIn (supBall o (12 * nn)),
      |h p * (plaquetteEnergyOf W p - (1 / 2) * ∑ e : Fin 3, imaginaryComponent e (G p) ^ 2)| ≤
        plaquetteEnergyConst B * (s ^ 3 + ε) := by
    intro p hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    have h1 : |h p| ≤ 1 := (abs_le_weightSup h ⟨p, hlt⟩).trans hh
    have h2 := abs_plaquetteEnergy_sub_half_sq_le W g o R s B ε p (G p) (hsub' hp) hs0 hs1 hε0 hε1 hB hlog (hG p (hsub' hp))
    rw [abs_mul]
    calc |h p| * _ ≤ 1 * (plaquetteEnergyConst B * (s ^ 3 + ε)) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul _ _ _ hbound)
  rw [nsmul_eq_mul] at hsum
  have hc := card_plaquettesIn_supBall_le o hnn
  have hs3 : 0 ≤ s ^ 3 + ε := by positivity
  calc _ ≤ ((plaquettesIn (supBall o (12 * nn))).card : ℝ) * (plaquetteEnergyConst B * (s ^ 3 + ε)) := hsum
    _ ≤ (16 * 27 ^ 4 * nn ^ 4) * (plaquetteEnergyConst B * (s ^ 3 + ε)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hK hs3)
    _ = _ := by
        unfold quadFormConst
        ring
private theorem lintegral_indicator_le_of_ae {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E A : Set Ω) (F g : Ω → ℝ) {K : ℝ}
    (hg : Integrable (A.indicator g) μ) (hg0 : ∀ u, 0 ≤ g u)
    (hle : ∀ᵐ u ∂μ, u ∈ E → u ∈ A ∧ F u ≤ g u) (hK : ∫ u, A.indicator g u ∂μ ≤ K) :
    ∫⁻ u, ENNReal.ofReal (E.indicator F u) ∂μ ≤ ENNReal.ofReal K := by
  have hnn : 0 ≤ᵐ[μ] A.indicator g :=
    Filter.Eventually.of_forall fun u => Set.indicator_nonneg (fun v _ => hg0 v) u
  calc ∫⁻ u, ENNReal.ofReal (E.indicator F u) ∂μ ≤ ∫⁻ u, ENNReal.ofReal (A.indicator g u) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle] with u hu
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hE : u ∈ E
        · obtain ⟨hA, hl⟩ := hu hE
          rw [Set.indicator_of_mem hE, Set.indicator_of_mem hA]
          exact hl
        · rw [Set.indicator_of_notMem hE]
          exact Set.indicator_nonneg (fun v _ => hg0 v) u
    _ = ENNReal.ofReal (∫ u, A.indicator g u ∂μ) := (ofReal_integral_eq_lintegral_ofReal hg hnn).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hK
private theorem add_pow_le_two_pow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by apply _root_.YangMills.Construction.Interpolation.CutoffDerivatives.add_pow_le_two_pow_mul <;> assumption
private theorem lintegral_moment_le_of_cubic {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E A : Set Ω) (X a : Ω → ℝ)
    {P ε v w Cm : ℝ} (q : ℕ) (hq : 1 ≤ q) (hP : 0 ≤ P) (hε : 0 ≤ ε) (hv : 0 ≤ v) (hw : v ^ 3 = w) (hεw : ε ≤ w)
    (hae : ∀ᵐ u ∂μ, u ∈ E → u ∈ A ∧ |X u| ≤ P * (|a u| ^ 3 + ε))
    (i6 : Integrable (A.indicator fun u => a u ^ (6 * q)) μ) (i0 : Integrable (A.indicator fun _ => (1 : ℝ)) μ)
    (m6 : ∫ u, A.indicator (fun u => a u ^ (6 * q)) u ∂μ ≤ (Cm * v) ^ (6 * q))
    (m0 : ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂μ ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (E.indicator (fun u => |X u| ^ (2 * q)) u) ∂μ ≤
      ENNReal.ofReal ((2 * P * (|Cm| ^ 3 + 1) * w) ^ (2 * q)) := by
  have hw0 : 0 ≤ w := hε.trans hεw
  set c : ℝ := (2 * P) ^ (2 * q) with hc
  have hc0 : 0 ≤ c := by positivity
  have hev : Even (6 * q) := ⟨3 * q, by ring⟩
  have ha6 : ∀ u, 0 ≤ a u ^ (6 * q) := fun u => hev.pow_nonneg _
  set g : Ω → ℝ := fun u => c * a u ^ (6 * q) + c * ε ^ (2 * q) * 1 with hg
  have hg0 : ∀ u, 0 ≤ g u := fun u => by
    have := ha6 u
    have h2 : 0 ≤ ε ^ (2 * q) := by positivity
    simp only [hg]
    positivity
  have hind : A.indicator g = fun u => c * A.indicator (fun u => a u ^ (6 * q)) u +
      c * ε ^ (2 * q) * A.indicator (fun _ => (1 : ℝ)) u := by
    funext u
    by_cases hu : u ∈ A
    · simp only [Set.indicator_of_mem hu, hg]
    · simp only [Set.indicator_of_notMem hu, mul_zero, add_zero]
  have hint : Integrable (A.indicator g) μ := by
    rw [hind]
    exact (i6.const_mul c).add (i0.const_mul _)
  refine lintegral_indicator_le_of_ae μ E A _ g hint hg0 ?_ ?_
  · filter_upwards [hae] with u hu hE
    obtain ⟨hA, hb⟩ := hu hE
    refine ⟨hA, ?_⟩
    have h1 : |X u| ^ (2 * q) ≤ (P * (|a u| ^ 3 + ε)) ^ (2 * q) := pow_le_pow_left₀ (abs_nonneg _) hb _
    have h2 : (|a u| ^ 3 + ε) ^ (2 * q) ≤ 2 ^ (2 * q) * ((|a u| ^ 3) ^ (2 * q) + ε ^ (2 * q)) :=
      add_pow_le_two_pow_mul (by positivity) hε _
    have h3 : (|a u| ^ 3) ^ (2 * q) = a u ^ (6 * q) := by
      rw [← pow_mul, show 3 * (2 * q) = 6 * q by ring]
      exact hev.pow_abs _
    rw [h3] at h2
    calc |X u| ^ (2 * q) ≤ (P * (|a u| ^ 3 + ε)) ^ (2 * q) := h1
      _ = P ^ (2 * q) * (|a u| ^ 3 + ε) ^ (2 * q) := mul_pow _ _ _
      _ ≤ P ^ (2 * q) * (2 ^ (2 * q) * (a u ^ (6 * q) + ε ^ (2 * q))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = g u := by
          simp only [hg, hc, mul_pow]
          ring
  · rw [hind, integral_add (i6.const_mul c) (i0.const_mul _), integral_const_mul, integral_const_mul]
    set J : ℝ := |Cm| ^ 3 with hJ
    have hJ0 : 0 ≤ J := by positivity
    have e6 : (Cm * v) ^ (6 * q) = (J * w) ^ (2 * q) := by
      have h1 : (Cm * v) ^ (6 * q) = |Cm * v| ^ (6 * q) := (hev.pow_abs _).symm
      rw [h1, abs_mul, abs_of_nonneg hv, show 6 * q = 3 * (2 * q) by ring, pow_mul, mul_pow, hw]
    have hn : 2 * q ≠ 0 := by omega
    have h1 : (J * w) ^ (2 * q) + w ^ (2 * q) ≤ (J * w + w) ^ (2 * q) :=
      pow_add_pow_le (by positivity) hw0 hn
    have h2 : ε ^ (2 * q) ≤ w ^ (2 * q) := pow_le_pow_left₀ hε hεw _
    have hε2 : 0 ≤ ε ^ (2 * q) := by positivity
    calc c * ∫ u, A.indicator (fun u => a u ^ (6 * q)) u ∂μ + c * ε ^ (2 * q) * ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂μ
        ≤ c * (J * w) ^ (2 * q) + c * ε ^ (2 * q) * 1 := by
          rw [← e6]
          exact add_le_add (mul_le_mul_of_nonneg_left m6 hc0) (mul_le_mul_of_nonneg_left m0 (by positivity))
      _ ≤ c * ((J * w) ^ (2 * q) + w ^ (2 * q)) := by nlinarith [mul_le_mul_of_nonneg_left h2 hc0]
      _ ≤ c * (J * w + w) ^ (2 * q) := mul_le_mul_of_nonneg_left h1 hc0
      _ = (2 * P * (J + 1) * w) ^ (2 * q) := by
          rw [hc, ← mul_pow]
          congr 1
          ring
private theorem lintegral_moment_le_of_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E A : Set Ω) (X : Ω → ℝ)
    {Q : ℝ} (q : ℕ) (hQ : 0 ≤ Q) (hae : ∀ᵐ u ∂μ, u ∈ E → u ∈ A ∧ |X u| ≤ Q)
    (i0 : Integrable (A.indicator fun _ => (1 : ℝ)) μ) (m0 : ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂μ ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (E.indicator (fun u => |X u| ^ (2 * q)) u) ∂μ ≤ ENNReal.ofReal (Q ^ (2 * q)) := by
  have hc0 : 0 ≤ Q ^ (2 * q) := by positivity
  have hind : A.indicator (fun _ => Q ^ (2 * q)) = fun u => Q ^ (2 * q) * A.indicator (fun _ => (1 : ℝ)) u := by
    funext u
    by_cases hu : u ∈ A
    · simp only [Set.indicator_of_mem hu, mul_one]
    · simp only [Set.indicator_of_notMem hu, mul_zero]
  have hint : Integrable (A.indicator fun _ => Q ^ (2 * q)) μ := by
    rw [hind]
    exact i0.const_mul _
  refine lintegral_indicator_le_of_ae μ E A _ (fun _ => Q ^ (2 * q)) hint (fun _ => hc0) ?_ ?_
  · filter_upwards [hae] with u hu hE
    obtain ⟨hA, hb⟩ := hu hE
    exact ⟨hA, pow_le_pow_left₀ (abs_nonneg _) hb _⟩
  · rw [hind, integral_const_mul]
    calc Q ^ (2 * q) * ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂μ ≤ Q ^ (2 * q) * 1 :=
          mul_le_mul_of_nonneg_left m0 hc0
      _ = Q ^ (2 * q) := mul_one _
private theorem ae_bound_cubic_of_rational {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Loc : Ω → Prop)
    (Small : ℝ → Ω → Prop) (a X : Ω → ℝ)
    {s₀ ε P : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hP : 0 ≤ P)
    (hS : ∀ s : ℝ, s < 1 → ∀ᵐ u ∂μ, Loc u → a u ≤ s → Small s u)
    (hD : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → ∀ᵐ u ∂μ, Loc u → Small s u → |X u| ≤ P * (s ^ 3 + ε)) :
    ∀ᵐ u ∂μ, Loc u → Small s₀ u → |X u| ≤ 5 * P * (|a u| ^ 3 + ε) ∧ |X u| ≤ P * (s₀ ^ 3 + ε) := by
  have all : ∀ᵐ u ∂μ, ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ s₀ →
      (Loc u → a u ≤ r → Small r u) ∧ (Loc u → Small r u → |X u| ≤ P * ((r : ℝ) ^ 3 + ε)) := by
    rw [ae_all_iff]
    intro r
    by_cases h : 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ s₀
    · filter_upwards [hS r (lt_of_le_of_lt h.2 hs₁), hD r h.1 h.2] with u h1 h2 _ _
      exact ⟨h1, h2⟩
    · exact Filter.Eventually.of_forall fun u h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [all, hD s₀ hs₀.le le_rfl] with u hall h₀ hL hsm
  have b0 := h₀ hL hsm
  refine ⟨?_, b0⟩
  have hA0 : 0 ≤ |a u| ^ 3 := by positivity
  by_cases hc : a u < s₀
  · have hlt : max (a u) 0 < min s₀ (max (a u) 0 + ε) :=
      lt_min (max_lt hc hs₀) (by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    have r0 : 0 ≤ (r : ℝ) := (le_max_right _ _).trans hr1.le
    have rs : (r : ℝ) ≤ s₀ := hr2.le.trans (min_le_left _ _)
    have hsr := (hall r r0 rs).1 hL ((le_max_left _ _).trans hr1.le)
    have bd := (hall r r0 rs).2 hL hsr
    have hb : max (a u) 0 ≤ |a u| := max_le (le_abs_self _) (abs_nonneg _)
    have hrr : (r : ℝ) ≤ |a u| + ε := (hr2.le.trans (min_le_right _ _)).trans (by linarith)
    have h3 : (r : ℝ) ^ 3 ≤ (|a u| + ε) ^ 3 := pow_le_pow_left₀ r0 hrr 3
    have h4 : (|a u| + ε) ^ 3 ≤ 4 * (|a u| ^ 3 + ε ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg (abs_nonneg (a u)) hε.le) (sq_nonneg (|a u| - ε))]
    have h5 : ε ^ 3 ≤ ε := by
      have : ε ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h6 : (r : ℝ) ^ 3 + ε ≤ 5 * (|a u| ^ 3 + ε) := by linarith
    calc |X u| ≤ P * ((r : ℝ) ^ 3 + ε) := bd
      _ ≤ P * (5 * (|a u| ^ 3 + ε)) := mul_le_mul_of_nonneg_left h6 hP
      _ = 5 * P * (|a u| ^ 3 + ε) := by ring
  · have h1 : s₀ ≤ |a u| := (not_lt.mp hc).trans (le_abs_self _)
    have h3 : s₀ ^ 3 ≤ |a u| ^ 3 := pow_le_pow_left₀ hs₀.le h1 3
    have h6 : s₀ ^ 3 + ε ≤ 5 * (|a u| ^ 3 + ε) := by linarith
    calc |X u| ≤ P * (s₀ ^ 3 + ε) := b0
      _ ≤ P * (5 * (|a u| ^ 3 + ε)) := mul_le_mul_of_nonneg_left h6 hP
      _ = 5 * P * (|a u| ^ 3 + ε) := by ring
private theorem exists_exp_neg_logCubeScale_le (c : ℝ) (hc : 0 < c) : ∃ x₂ : ℝ, 2 ≤ x₂ ∧ ∀ x : ℝ, x₂ ≤ x →
    Real.exp (-(c * logCubeScale x)) ≤ x ^ (-(3 / 2 : ℝ)) := by
  have hΛ : 2 ≤ 2 + 3 / c := by
    have : 0 < 3 / c := by positivity
    linarith
  refine ⟨Real.exp (2 + 3 / c), ?_, fun x hx => ?_⟩
  · have := Real.add_one_le_exp (2 + 3 / c)
    linarith
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl : 2 + 3 / c ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  set l := Real.log x with hldef
  have hl2 : 2 ≤ l := hΛ.trans hl
  have hcl : 3 ≤ c * l := by
    have h1 : 3 / c ≤ l := by linarith
    have := (div_le_iff₀ hc).mp h1
    linarith
  have hfl : l ^ 3 - 1 ≤ logCubeScale x := by
    have h1 := Nat.lt_floor_add_one (l ^ 3)
    show l ^ 3 - 1 ≤ ((⌊Real.log x ^ 3⌋₊ : ℕ) : ℝ)
    linarith
  have h3 : l ^ 3 / 2 ≤ l ^ 3 - 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ l - 2) (by positivity : 0 ≤ l ^ 2)]
  have h4 : (3 / 2) * l ≤ c * (l ^ 3 / 2) := by
    have : c * l ^ 3 = (c * l) * l ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_right hcl (by positivity : 0 ≤ l ^ 2)]
  have h5 : c * (l ^ 3 / 2) ≤ c * logCubeScale x := mul_le_mul_of_nonneg_left (h3.trans hfl) hc.le
  linarith
private def quadFormRemainder (T : StageTower ℓ) (β x nn : ℝ) (M N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (h : PlaquetteWeight (fineSide ℓ.side 0 (fineSide ℓ.side M (fineSide ℓ.side M N))))
    (u : MarkedSample ℓ (0 + M + M) N) : ℝ :=
  WeightedResponses.response T β (fun _ => 1) 0 _ h (sampleBelow ℓ 0 M _ (sampleBelow ℓ (0 + M) M N u)) -
    (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ,
      h p * ∑ e : Fin 3, imaginaryComponent e (sampledCurvature T 0 M nn x N u o p) ^ 2
private def axialTopGauge (M N : ℕ) [NeZero N] (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (u : MarkedSample ℓ (0 + M + M) N) : TorusSite (fineSide ℓ.side M N) → UnitQuaternion :=
  axialGaugeAt ℓ (topField ℓ (0 + M) (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u))
    (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
private def IsSmallAt (T : StageTower ℓ) (nn ρ s : ℝ) (M N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (u : MarkedSample ℓ (0 + M + M) N) : Prop :=
  IsGaugeSmallAlong T 0 nn ρ s M (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u) o (axialTopGauge M N o u)
private def chainSizeAt (T : StageTower ℓ) (C₁ c₁ nn ρ : ℝ) (M' M N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (u : MarkedSample ℓ (0 + M + M) N) : ℝ :=
  widenedChainSize T C₁ c₁ M' 0 nn ρ M (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u) o
private theorem ae_abs_quadFormRemainder_le (T : StageTower ℓ) (β x nn ρ m : ℝ) (M' M N : ℕ) [NeZero N]
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (h : PlaquetteWeight (fineSide ℓ.side 0 (fineSide ℓ.side M (fineSide ℓ.side M N))))
    {C₁ c₁ C ε s₀ : ℝ} (hnn : 1 ≤ nn) (hρ : 0 ≤ ρ) (hs₀ : 0 < s₀) (hs₁ : s₀ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hh : weightSup h ≤ 1)
    (hsup : ∀ (z : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (p), z ∉ supBall o (12 * nn) →
      IsPlaquetteAt ℓ.side 0 z p → h p = 0)
    (hSm : ∀ s : ℝ, s < 1 → ∀ᵐ u ∂(markedSampleLaw T β (0 + M + M) N), IsLocalEvent T 0 M m N u o →
      chainSizeAt T C₁ c₁ nn ρ M' M N o u ≤ s → IsSmallAt T nn ρ s M N o u)
    (hCu : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → ∀ᵐ u ∂(markedSampleLaw T β (0 + M + M) N), IsLocalEvent T 0 M m N u o →
      IsSmallAt T nn ρ s M N o u →
      ∀ p ∈ plaquettesIn (supBall o (ballRadius ℓ.side nn ρ 0)),
        ‖((lieFormCurl (ballLog (gaugeDescent 0 M (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u) (axialTopGauge M N o u))
            (topField ℓ 0 _ (sampleBelow ℓ 0 M _ (sampleBelow ℓ (0 + M) M N u))) o (ballRadius ℓ.side nn ρ 0)) p -
          sampledCurvature T 0 M nn x N u o p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ C * (s ^ 2 + ε)) :
    ∀ᵐ u ∂(markedSampleLaw T β (0 + M + M) N), IsLocalEvent T 0 M m N u o → IsSmallAt T nn ρ s₀ M N o u →
      |quadFormRemainder T β x nn M N o h u| ≤
          5 * (quadFormConst |C| * nn ^ 4) * (|chainSizeAt T C₁ c₁ nn ρ M' M N o u| ^ 3 + ε) ∧
        |quadFormRemainder T β x nn M N o h u| ≤ quadFormConst |C| * nn ^ 4 * (s₀ ^ 3 + ε) := by
  have hB : 0 ≤ |C| := abs_nonneg C
  have hP : 0 ≤ quadFormConst |C| * nn ^ 4 := mul_nonneg (quadFormConst_nonneg hB) (by positivity)
  have hR : 12 * nn ≤ ballRadius ℓ.side nn ρ 0 := by
    simp only [ballRadius, pow_zero, div_one]
    nlinarith
  have hz : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))),
      p ∉ plaquettesIn (supBall o (12 * nn)) → h p = 0 := by
    intro p hp hp'
    have hlt := (Finset.mem_filter.mp hp).2.1
    by_contra hne
    apply hp'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun z hz' => ?_⟩
    by_contra hzb
    exact hne (hsup z p hzb ⟨hlt, z, hz', by
      simp only [fineBlock]
      exact Finset.mem_singleton_self z⟩)
  refine ae_bound_cubic_of_rational _ (fun u => IsLocalEvent T 0 M m N u o) (fun s u => IsSmallAt T nn ρ s M N o u)
    (chainSizeAt T C₁ c₁ nn ρ M' M N o) (quadFormRemainder T β x nn M N o h) hs₀ hs₁ hε hε1 hP hSm ?_
  intro s hs0 hss
  filter_upwards [hCu s hs0 hss] with u hu hL hS
  have hc := hu hL hS
  have hlogs := norm_minimalLog_descent_le T 0 nn ρ s M (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u) o
    (axialTopGauge M N o u) hS
  refine abs_curvatureObservable_sub_quadForm_le (topField ℓ 0 _ (sampleBelow ℓ 0 M _ (sampleBelow ℓ (0 + M) M N u)))
    (gaugeDescent 0 M (fineSide ℓ.side M N) (sampleBelow ℓ (0 + M) M N u) (axialTopGauge M N o u)) o
    (ballRadius ℓ.side nn ρ 0) s |C| ε nn h
    (fun p => sampledCurvature T 0 M nn x N u o p) hnn hR hs0 (hss.trans hs₁.le) hε.le hε1 hB hh hz hlogs ?_
  intro p hp
  refine (hc p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
end BareObservable
open BareObservable in
theorem bareObservableQuadraticFormStatement_holds (hSz : localChainSizeStatement)
    (hDs : curvatureNearDescendedFormStatement) : bareObservableQuadraticFormStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := hSz a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, H₂⟩ := hDs a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), max C₁ C₂, fun c => lt_min (hrt₁ c) (hrt₂ c),
    fun L hL hL₀ Tb hTa hTL hDr hC hO hr hC₀ => ?_⟩
  obtain ⟨y₁, Hy₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hL₀) Tb hTa hTL hDr hC hO (le_trans hr (min_le_left _ _))
    (le_trans (le_max_left _ _) hC₀)
  obtain ⟨y₂, Hy₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hL₀) Tb hTa hTL hDr hC hO (le_trans hr (min_le_right _ _))
    (le_trans (le_max_right _ _) hC₀)
  refine ⟨max y₁ y₂, fun y hy hR hW => ?_⟩
  obtain ⟨K₁, c₁, hK₁, -, hq⟩ := Hy₁ y (le_trans (le_max_left _ _) hy) hR hW
  obtain ⟨C, c, xd, hc, hDesc⟩ := Hy₂ y (le_trans (le_max_right _ _) hy) hR hW
  choose Cm xm hm using hq
  obtain ⟨x₂, hx₂, hfl⟩ := exists_exp_neg_logCubeScale_le c hc
  have hB : 0 ≤ |C| := abs_nonneg C
  have hA : 0 ≤ quadFormConst |C| := quadFormConst_nonneg hB
  refine ⟨fun q => 10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) +
      2 * quadFormConst |C| * (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ), max (max xd (xm 0)) x₂, ?_⟩
  intro Tw β N _ nn o h hOn hdvd hh hsup q hq1
  beta_reduce
  have hxf : max (max xd (xm 0)) x₂ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := hOn.floor_le
  have hxd : xd ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxf
  have hx0 : xm 0 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxf
  have hxx : x₂ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := le_trans (le_max_right _ _) hxf
  have hOnD : IsLocalChainAbove Tb y Tw β 0 N nn xd := { hOn with floor_le := hxd }
  have hOn0 : IsLocalChainAbove Tb y Tw β 0 N nn (xm 0) := { hOn with floor_le := hx0 }
  have hnn : 1 ≤ nn := hOn.one_le
  have hn0 : 0 ≤ nn ^ 4 := by positivity
  obtain ⟨h1, ⟨i0, m0⟩, -⟩ := hm 0 Tw β 0 N nn 0 (localChainDepth (Tb.stepParameters y) β 0)
    (localChainDepth (Tb.stepParameters y) β 0) o hOn0 hdvd le_rfl rfl rfl
  simp only [Nat.sub_self, pow_zero, div_one] at h1 i0 m0
  have hx2 : 2 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := hx₂.trans hxx
  have hx1 : 1 < (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := by linarith
  have hx00 : 0 < (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := by linarith
  have hs₀ : 0 < (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx00 _
  have hs₁ : (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 (by norm_num)
  have hρ : 0 ≤ logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 := Nat.cast_nonneg _
  have hε : 0 < Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)) := Real.exp_pos _
  have hε1 : Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc.le hρ))
  have hpt := ae_abs_quadFormRemainder_le Tw β (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 nn
    (logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
    (localBoxRadius (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) (localChainDepth (Tb.stepParameters y) β 0)
    (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o h
    (C₁ := K₁) (c₁ := c₁) (C := C) hnn hρ hs₀ hs₁ hε hε1 hh hsup h1
    (fun s hs0 hss => hDesc Tw β 0 N nn s o hOnD hdvd hs0 hss)
  have hP0 : 0 ≤ quadFormConst |C| * nn ^ 4 := mul_nonneg hA hn0
  have hw0 : 0 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
    Real.rpow_nonneg hx00.le _
  have hv0 : 0 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 2 : ℝ) + 2 / 1000) :=
    Real.rpow_nonneg hx00.le _
  have hvw : ((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 3 =
      (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx00.le]
    congr 1
    norm_num
  have hle : (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ)) ≤
      (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hεw : Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)) ≤
      (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
    (hfl (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 hxx).trans hle
  have hXp : 0 ≤ (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (le_max_of_le_right (by norm_num)) _
  have hJ : 0 ≤ |Cm (6 * q)| ^ 3 + 1 := by positivity
  have hT1 : 0 ≤ 10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) * nn ^ 4 *
      (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hJ) hn0) hw0
  have hT2 : 0 ≤ 2 * quadFormConst |C| * (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) * nn ^ 4 *
      (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hXp) hn0) hw0
  by_cases hxq : max (xm (6 * q)) 2 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1
  · have hOn6 : IsLocalChainAbove Tb y Tw β 0 N nn (xm (6 * q)) :=
      { hOn with floor_le := (le_max_left _ _).trans hxq }
    obtain ⟨-, ⟨i6, m6⟩, -⟩ := hm (6 * q) Tw β 0 N nn 0 (localChainDepth (Tb.stepParameters y) β 0)
      (localChainDepth (Tb.stepParameters y) β 0) o hOn6 hdvd le_rfl rfl rfl
    simp only [Nat.sub_self, pow_zero, div_one] at i6 m6
    have big := lintegral_moment_le_of_cubic
      (markedSampleLaw Tw β (0 + chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N)
      {u | IsLocalEvent Tw 0 (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
          (localBoxRadius (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N u o ∧
        IsSmallAt Tw nn (logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
          ((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ)))
          (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o u}
      {u | IsLocalEventFrom Tw 0 (localChainDepth (Tb.stepParameters y) β 0) (localChainDepth (Tb.stepParameters y) β 0)
        (localBlockSide (Tb.stepParameters y) β 0) N u o}
      (quadFormRemainder Tw β (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 nn
        (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o h)
      (chainSizeAt Tw K₁ c₁ nn (logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
        (localChainDepth (Tb.stepParameters y) β 0) (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o)
      (P := 5 * (quadFormConst |C| * nn ^ 4))
      (ε := Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)))
      (v := (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 2 : ℝ) + 2 / 1000))
      (w := (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000)) (Cm := Cm (6 * q)) q hq1
      (by linarith) hε.le hv0 hvw hεw
      (by
        filter_upwards [hpt] with u hu hE
        exact ⟨hE.1, (hu hE.1 hE.2).1⟩)
      i6 i0 m6 m0
    refine big.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ?_ ?_ _))
    · exact mul_nonneg (mul_nonneg (by linarith) hJ) hw0
    · have e1 : 2 * (5 * (quadFormConst |C| * nn ^ 4)) * (|Cm (6 * q)| ^ 3 + 1) *
            (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) =
          10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) * nn ^ 4 *
            (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) := by ring
      have e2 : (10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) +
          2 * quadFormConst |C| * (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ)) * nn ^ 4 *
            (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) =
          10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) * nn ^ 4 *
            (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) +
          2 * quadFormConst |C| * (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) * nn ^ 4 *
            (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) := by ring
      rw [e1, e2]
      linarith
  · have hxq' : (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ≤ max (xm (6 * q)) 2 := (not_le.mp hxq).le
    have big := lintegral_moment_le_of_bound
      (markedSampleLaw Tw β (0 + chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 +
        chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N)
      {u | IsLocalEvent Tw 0 (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
          (localBoxRadius (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N u o ∧
        IsSmallAt Tw nn (logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)
          ((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ)))
          (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o u}
      {u | IsLocalEventFrom Tw 0 (localChainDepth (Tb.stepParameters y) β 0) (localChainDepth (Tb.stepParameters y) β 0)
        (localBlockSide (Tb.stepParameters y) β 0) N u o}
      (quadFormRemainder Tw β (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 nn
        (chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1) N o h)
      (Q := 2 * (quadFormConst |C| * nn ^ 4)) q (by linarith)
      (by
        filter_upwards [hpt] with u hu hE
        refine ⟨hE.1, (hu hE.1 hE.2).2.trans ?_⟩
        have hs3 : ((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ))) ^ 3 ≤ 1 :=
          pow_le_one₀ hs₀.le hs₁.le
        have : ((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ))) ^ 3 +
            Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)) ≤ 2 := by linarith
        calc quadFormConst |C| * nn ^ 4 * (((TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ))) ^ 3 +
              Real.exp (-(c * logCubeScale (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1)))
            ≤ quadFormConst |C| * nn ^ 4 * 2 := mul_le_mul_of_nonneg_left this hP0
          _ = 2 * (quadFormConst |C| * nn ^ 4) := by ring)
      i0 m0
    refine big.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) ?_ _))
    have a1 : (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (3 / 2 : ℝ) ≤ (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hx00.le hxq' (by norm_num)
    have a3 : (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (3 / 2 : ℝ) *
        (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx00]
      simp
    have a4 : 1 ≤ (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) *
        (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) := by
      rw [← a3]
      exact mul_le_mul a1 hle (Real.rpow_nonneg hx00.le _) hXp
    have a5 := mul_le_mul_of_nonneg_left a4 (mul_nonneg (by linarith : 0 ≤ 2 * quadFormConst |C|) hn0)
    have e2 : (10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) +
        2 * quadFormConst |C| * (max (xm (6 * q)) 2) ^ (3 / 2 : ℝ)) * nn ^ 4 *
          (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) =
        10 * quadFormConst |C| * (|Cm (6 * q)| ^ 3 + 1) * nn ^ 4 *
          (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000) +
        2 * quadFormConst |C| * nn ^ 4 * ((max (xm (6 * q)) 2) ^ (3 / 2 : ℝ) *
          (TorusLumps.couplingFlow (Tb.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000)) := by ring
    rw [e2]
    linarith
end FourPointCondition
end YangMills.Construction
end
