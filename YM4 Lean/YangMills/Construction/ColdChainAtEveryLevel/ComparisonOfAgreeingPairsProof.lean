import YangMills.Construction.ColdChainAtEveryLevel.AnalyticCoordinatesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticVanishingOnRealPoints
import YangMills.Construction.ColdChainAtEveryLevel.BareDistanceOfCells
import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfAgreeingPairs
import YangMills.Construction.ColdChainAtEveryLevel.CriticalAlongTheSliceUnderAnyTop
import YangMills.Construction.ColdChainAtEveryLevel.CutsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.GaugeDifferenceNearACell
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.LocalFirstVariation
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfAHolomorphicFunction
import YangMills.Construction.ColdChainAtEveryLevel.NormsOnBoxesAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.RealPointsOfAComplexFamily
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.SitesAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.SliceProjectionOfAForm
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsOfTheTotal
import YangMills.Construction.ColdChainAtEveryLevel.TermsNearSomeCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Filter Topology
namespace YangMills.Construction.BlockAverages
namespace AgreeingPairs
open CoordinateSeminorms ChartCoordinates SpanVariations ComplexFamilies TwistedTops Offsets CoordinateCutoffs CellDistances
variable {F F' : BlockFrame}
theorem abs_le_of_withinCellRadius {L n ρ j : ℕ} (hL : 0 < L) (hj : j ≤ n) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius L n ρ j p) (i : Fin 4) :
    |p i| ≤ (ρ : ℤ) * (L : ℤ) ^ (n - j) := by
  have h1 := hp i
  have e : (L : ℤ) ^ n = (L : ℤ) ^ j * (L : ℤ) ^ (n - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e] at h1
  have h0 : (0 : ℤ) < (L : ℤ) ^ j := by positivity
  have h2 : (L : ℤ) ^ j * |p i| ≤ (L : ℤ) ^ j * ((ρ : ℤ) * (L : ℤ) ^ (n - j)) := by
    refine h1.trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_left h2 h0
theorem baseDistance_siteAtOffset_le (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) {ρ : ℕ}
    {p : Fin 4 → ℤ} (hp : WithinCellRadius F.blockSide F.top ρ j p) :
    (baseDistance (siteAtOffset j Y p) (cellCentre 0 Y) : ℤ) ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top := by
  have hsup : baseDistance (siteAtOffset j Y p) (cellCentre 0 Y) ≤ (ρ * F.blockSide ^ F.top : ℕ) := by
    refine Finset.sup_le fun i _ => ?_
    have e : (baseSite (siteAtOffset j Y p) - cellCentre 0 Y : F.Site 0) i =
        ((((F.blockSide : ℤ) ^ j * p i : ℤ)) : ZMod (F.period 0 i)) := by
      unfold siteAtOffset
      rw [baseSite_add j hj, baseSite_cellCentre j hj]
      simp [siteOfCoords]
    rw [e]
    refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
    have h1 := hp i
    have h2 : (((F.blockSide : ℤ) ^ j * p i).natAbs : ℤ) ≤ ((ρ * F.blockSide ^ F.top : ℕ) : ℤ) := by
      rw [← Int.abs_eq_natAbs, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j)]
      push_cast
      exact h1
    exact_mod_cast h2
  exact_mod_cast hsup
theorem translateSite_siteAtOffset (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) (Y' : F'.Cell)
    {ρ : ℕ} (hs : ∀ i, F.extent i = 0 ∨ 2 * ρ + 2 < F.extent i) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius F.blockSide F.top ρ j p) :
    translateSite Y Y' (siteAtOffset j Y p) = siteAtOffset j Y' p := by
  unfold translateSite siteAtOffset
  congr 1
  have e : (fun i => ((cellCentre j Y + siteOfCoords j p - cellCentre j Y : F.Site j) i).valMinAbs) = p := by
    funext i
    have h1 : (cellCentre j Y + siteOfCoords j p - cellCentre j Y : F.Site j) i =
        ((p i : ℤ) : ZMod (F.period j i)) := by
      simp [siteOfCoords]
    rw [h1]
    apply valMinAbs_intCast_of_small
    have hper : (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
      simp [BlockFrame.period]
    rcases hs i with h0 | h0
    · left
      simp [BlockFrame.period, h0]
    · right
      rw [hper]
      have h1 := abs_le_of_withinCellRadius hL hj hp i
      have hLp : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by
        have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
        positivity
      have h2 : ((2 * ρ + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast h0
      push_cast at h2
      nlinarith
  rw [e]
theorem chartsAgree_chartTranslate (hL : 0 < F.blockSide) (Y : F.Cell) (Y' : F'.Cell) {ρ : ℕ}
    (hs : ∀ i, F.extent i = 0 ∨ 2 * ρ + 2 < F.extent i)
    (A' : ChainChart F') : ChartsAgreeAtOffsets Y Y' ρ (chartTranslate Y Y' A') A' where
  fine p i hp := by
    show A'.fine (translateSite Y Y' (siteAtOffset 0 Y p)) i = _
    rw [translateSite_siteAtOffset hL (Nat.zero_le _) Y Y' hs hp]
  coarse j p i hj hp := by
    show A'.coarse j (translateSite Y Y' (siteAtOffset (j + 1) Y p)) i = _
    rw [translateSite_siteAtOffset hL (by omega) Y Y' hs hp]
theorem tentCutoff_eq_one (hL : 0 < F.blockSide) (Y : F.Cell) {ρ : ℝ} {j : ℕ} {x : F.Site j}
    (h : (baseDistance x (cellCentre 0 Y) : ℝ) ≤ (ρ - 1) * (F.blockSide : ℝ) ^ F.top) :
    tentCutoff F Y ρ j x = 1 := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
    positivity
  unfold tentCutoff
  have h1 : 1 ≤ ρ - (baseDistance x (cellCentre 0 Y) : ℝ) / (F.blockSide : ℝ) ^ F.top := by
    have := (div_le_iff₀ hN).2 h
    linarith
  rw [min_eq_left h1]
  exact max_eq_right zero_le_one
theorem tentCutoff_eq_zero (hL : 0 < F.blockSide) (Y : F.Cell) {ρ : ℝ} {j : ℕ} {x : F.Site j}
    (h : ρ * (F.blockSide : ℝ) ^ F.top ≤ (baseDistance x (cellCentre 0 Y) : ℝ)) : tentCutoff F Y ρ j x = 0 := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
    positivity
  unfold tentCutoff
  have h1 : ρ - (baseDistance x (cellCentre 0 Y) : ℝ) / (F.blockSide : ℝ) ^ F.top ≤ 0 := by
    have := (le_div_iff₀ hN).2 h
    linarith
  exact max_eq_left ((min_le_right _ _).trans h1)
section General
variable {S : Finset F.Cell}
theorem neg_one_smul_imag (x : imaginaryQuaternions) : (-1 : ℝ) • x = -x := neg_one_smul ℝ x
theorem linearizedCurl_congr (R : F.GaugeField 0) (u u' : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (q : F.Site 0 × Fin 4 × Fin 4)
    (h1 : u q.1 q.2.1 = u' q.1 q.2.1)
    (h2 : u (q.1 + unitStep 0 q.2.1) q.2.2 = u' (q.1 + unitStep 0 q.2.1) q.2.2)
    (h3 : u (q.1 + unitStep 0 q.2.2) q.2.1 = u' (q.1 + unitStep 0 q.2.2) q.2.1) (h4 : u q.1 q.2.2 = u' q.1 q.2.2) :
    linearizedCurl R u q = linearizedCurl R u' q := by
  simp only [linearizedCurl, h1, h2, h3, h4]
theorem localNorm_congr (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    {A A' : ChainChart F} (w : F.SiteWeights) (z : F.Cell)
    (h1 : ∀ b ∈ bondsOver S (cellBall S z 4) 0, A.fine b.1 b.2 = A'.fine b.1 b.2)
    (h2 : ∀ j, j + 1 < F.top → ∀ b ∈ bondsOver S (cellBall S z 4) (j + 1), A.coarse j b.1 b.2 = A'.coarse j b.1 b.2) :
    localNorm S R A w z = localNorm S R A' w z := by
  classical
  have hBD : cellBall S z 3 ⊆ cellBall S z 4 := fun y hy => by
    have h := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨h.1, h.2.trans (by norm_num)⟩
  have e1 : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 =
      ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖A'.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_congr rfl fun b hb => by
      obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
      rw [h1 b (mem_bondsOver.2 ⟨a1, hBD a2⟩)]
  have e2 : ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 =
      ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) A'.fine p‖) ^ 2 :=
    Finset.sum_congr rfl fun q hq => by
      obtain ⟨a1, a2⟩ := mem_plaquettesOver.1 hq
      have hq' : q ∈ plaquettesOver S {enclosingCell q.1} 0 := mem_plaquettesOver.2 ⟨a1, by simp⟩
      obtain ⟨b1, b2, b3, b4⟩ := PlaquettesNearCell.plaquette_bonds_mem_innerBonds hamb hodd hq'
      have hsub : ∀ {b : F.Site 0 × Fin 4}, b ∈ innerBonds (cellBall S (enclosingCell q.1) 1) 0 →
          b ∈ bondsOver S (cellBall S z 4) 0 := by
        intro b hb
        refine mem_bondsOver.2 ⟨BlockLines.innerBonds_mono (BlockLines.cellBall_subset S _ 1) 0 hb, ?_⟩
        have hc : enclosingCell b.1 ∈ cellBall S (enclosingCell q.1) 1 :=
          CoordinateSeminorms.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
        have hy := Finset.mem_filter.1 hc
        have hzq := (Finset.mem_filter.1 a2).2
        refine Finset.mem_filter.2 ⟨hy.1, ?_⟩
        have := CoordinateSeminorms.cellSupDist_triangle z (enclosingCell q.1) (enclosingCell b.1)
        omega
      rw [linearizedCurl_congr (R 0) A.fine A'.fine q (h1 _ (hsub b1)) (h1 _ (hsub b2)) (h1 _ (hsub b3))
        (h1 _ (hsub b4))]
  have e3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖A'.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => by
      obtain ⟨a1, a2⟩ := mem_bondsOver.1 hc
      have hj' : j + 1 < F.top := by
        have := Finset.mem_range.1 hj
        omega
      rw [h2 j hj' c (mem_bondsOver.2 ⟨a1, hBD a2⟩)]
  unfold localNorm localNormSq
  rw [e1, e2, e3]
theorem localNorm_zeroChart (R : F.FieldChain) (w : F.SiteWeights) (z : F.Cell) :
    localNorm S R (zeroChart F) w z = 0 := by
  unfold localNorm localNormSq
  simp [zeroChart, linearizedCurl, _root_.YangMills.Construction.BlockAverages.adjointAction]
theorem localNorm_decay_le (δ : ℝ) (hdel : 0 ≤ δ) (R : F.FieldChain) (A : ChainChart F) (y z : F.Cell) :
    localNorm S R A (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) z ≤
      Real.exp (3 * δ - δ * (cellSupDist z y : ℝ)) * localNorm S R A (constOneWeights F) z := by
  refine localNorm_le_of_weights_le S R A (constOneWeights F) _ z _ (Real.exp_pos _).le fun j x hx => ?_
  rw [CoordinateCutoffs.classWeight_zero]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  show Real.exp (-δ * (cellSupDist (enclosingCell x) y : ℝ)) ≤ Real.exp (3 * δ - δ * (cellSupDist z y : ℝ)) * 1
  rw [mul_one]
  apply Real.exp_le_exp.2
  have h1 := abs_mul_cellSupDist_sub_le δ hdel y z (enclosingCell x)
  have h2 : (cellSupDist z (enclosingCell x) : ℝ) ≤ 3 := by exact_mod_cast hx
  have h3 := (abs_le.1 h1).2
  nlinarith
theorem localNorm_le_decay (δ : ℝ) (hdel : 0 ≤ δ) (R : F.FieldChain) (A : ChainChart F) (y z : F.Cell) :
    localNorm S R A (constOneWeights F) z ≤ Real.exp (3 * δ + δ * (cellSupDist z y : ℝ)) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) := by
  refine (localNorm_le_of_weights_le S R A (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0)
    (constOneWeights F) z (Real.exp (3 * δ + δ * (cellSupDist z y : ℝ))) (Real.exp_pos _).le
    fun j x hx => ⟨zero_le_one, ?_⟩).trans ?_
  · show (1 : ℝ) ≤ Real.exp (3 * δ + δ * (cellSupDist z y : ℝ)) *
      classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0 j x
    rw [CoordinateCutoffs.classWeight_zero, ← Real.exp_add]
    apply Real.one_le_exp
    have h1 := abs_mul_cellSupDist_sub_le δ hdel y (enclosingCell x) z
    have h2 : (cellSupDist (enclosingCell x) z : ℝ) ≤ 3 := by
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact_mod_cast hx
    have h3 := (abs_le.1 h1).2
    have h4 := mul_le_mul_of_nonneg_left h2 hdel
    linarith
  · exact mul_le_mul_of_nonneg_left (localNorm_le_weightedNorm S R A _ z) (Real.exp_pos _).le
theorem localNorm_le_growing (δ : ℝ) (hdel : 0 ≤ δ) (R : F.FieldChain) (A : ChainChart F) (y z : F.Cell) :
    localNorm S R A (constOneWeights F) z ≤ Real.exp (3 * δ - δ * (cellSupDist z y : ℝ)) *
      localNorm S R A (classWeight F (fun x => δ * (cellSupDist x y : ℝ)) 0 0) z := by
  refine localNorm_le_of_weights_le S R A (classWeight F (fun x => δ * (cellSupDist x y : ℝ)) 0 0)
    (constOneWeights F) z (Real.exp (3 * δ - δ * (cellSupDist z y : ℝ))) (Real.exp_pos _).le
    fun j x hx => ⟨zero_le_one, ?_⟩
  show (1 : ℝ) ≤ Real.exp (3 * δ - δ * (cellSupDist z y : ℝ)) *
    classWeight F (fun x => δ * (cellSupDist x y : ℝ)) 0 0 j x
  rw [CoordinateCutoffs.classWeight_zero, ← Real.exp_add]
  apply Real.one_le_exp
  have h1 := abs_mul_cellSupDist_sub_le δ hdel y z (enclosingCell x)
  have h2 : (cellSupDist z (enclosingCell x) : ℝ) ≤ 3 := by exact_mod_cast hx
  have h3 := (abs_le.1 h1).2
  have h4 := mul_le_mul_of_nonneg_left h2 hdel
  linarith
theorem localNorm_baseOnlyChart_le (R : F.FieldChain) (A : ChainChart F) (z : F.Cell) :
    localNorm S R (baseOnlyChart A.fine) (constOneWeights F) z ≤ localNorm S R A (constOneWeights F) z := by
  unfold localNorm
  refine Real.sqrt_le_sqrt ?_
  unfold localNormSq
  simp only [baseOnlyChart, constOneWeights, one_mul]
  have h0 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      ‖(0 : imaginaryQuaternions)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 :=
    Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => by
      simp
  linarith
end General
section First
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {k : ℕ} {b : Fin k → F.Site F.top × Fin 4}
  {X : Fin k → imaginaryQuaternions} {a θ δ Ca c C s : ℝ}
theorem complexFirstVariation_add (hB : TwistedTotalBounds a θ δ Ca c C s S V b X) {W : ComplexChainChart F}
    {ζ : Fin k → ℂ} (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (hζ : ∑ l, ‖ζ l‖ ≤ c)
    (A₁ A₂ : ChainChart F) :
    complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) (chartMove A₁ A₂ 1) =
      complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A₁ +
        complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A₂ := by
  set A' : Fin 4 → ChainChart F := ![W.re, W.im, A₁, A₂] with hA'
  set f : (Fin 4 → ℂ) × (Fin k → ℂ) → ℂ := fun q =>
    complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' q.1) (complexTwistedTop b X q.2 V) with hf
  have hsp : ∀ τ₁ τ₂ : ℂ, complexSpan A' ![1, Complex.I, τ₁, τ₂] =
      complexChartMove (complexChartMove W A₁ τ₁) A₂ τ₂ := by
    intro τ₁ τ₂
    unfold complexSpan complexChartMove
    congr 1
    · apply chainChart_ext
      · funext p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_four, hA', add_assoc]
      · funext j p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_four, hA', add_assoc]
    · apply chainChart_ext
      · funext p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_four, hA', add_assoc]
      · funext j p i
        simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_four, hA', add_assoc]
  have h00 : complexSpan A' ![1, Complex.I, 0, 0] = W := by
    rw [hsp, complexChartMove_zero, complexChartMove_zero]
  set t : Fin 4 → ℂ := ![1, Complex.I, 0, 0] with ht
  have hana := hB.analytic 4 A' t ζ (by rw [h00]; exact hW) hζ
  have hd : HasFDerivAt f (fderiv ℂ f (t, ζ)) (t, ζ) := hana.differentiableAt.hasFDerivAt
  have line : ∀ v : Fin 4 → ℂ, HasDerivAt (fun τ : ℂ => f (t + τ • v, ζ)) (fderiv ℂ f (t, ζ) (v, 0)) 0 := by
    intro v
    have hl : HasDerivAt (fun τ : ℂ => (((t + τ • v, ζ)) : (Fin 4 → ℂ) × (Fin k → ℂ))) (v, 0) 0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
      have := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add t
      simpa using this
    have e0 : (((t + (0 : ℂ) • v, ζ)) : (Fin 4 → ℂ) × (Fin k → ℂ)) = (t, ζ) := by simp
    have hf' : HasFDerivAt f (fderiv ℂ f (t, ζ)) (t + (0 : ℂ) • v, ζ) := by
      rw [e0]
      exact hd
    exact hf'.comp_hasDerivAt (0 : ℂ) hl
  have e1 : complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A₁ =
      fderiv ℂ f (t, ζ) (![0, 0, 1, 0], 0) := by
    have eq : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A₁ τ)
        (complexTwistedTop b X ζ V)) = fun τ : ℂ => f (t + τ • ![0, 0, 1, 0], ζ) := by
      funext τ
      have e : t + τ • ![0, 0, 1, 0] = ![1, Complex.I, τ, 0] := by
        funext i
        fin_cases i <;> simp [ht]
      show _ = complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' (t + τ • ![0, 0, 1, 0]))
        (complexTwistedTop b X ζ V)
      rw [e, hsp, complexChartMove_zero]
    unfold complexFirstVariation
    rw [eq]
    exact (line _).deriv
  have e2 : complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A₂ =
      fderiv ℂ f (t, ζ) (![0, 0, 0, 1], 0) := by
    have eq : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A₂ τ)
        (complexTwistedTop b X ζ V)) = fun τ : ℂ => f (t + τ • ![0, 0, 0, 1], ζ) := by
      funext τ
      have e : t + τ • ![0, 0, 0, 1] = ![1, Complex.I, 0, τ] := by
        funext i
        fin_cases i <;> simp [ht]
      show _ = complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' (t + τ • ![0, 0, 0, 1]))
        (complexTwistedTop b X ζ V)
      rw [e, hsp, complexChartMove_zero]
    unfold complexFirstVariation
    rw [eq]
    exact (line _).deriv
  have hsum : ∀ τ : ℂ, complexChartMove (complexChartMove W A₁ τ) A₂ τ =
      complexChartMove W (chartMove A₁ A₂ 1) τ := by
    intro τ
    have hm : ∀ (U : ChainChart F) (c : ℝ), chartMove (chartMove U A₁ c) A₂ c = chartMove U (chartMove A₁ A₂ 1) c := by
      intro U c
      apply chainChart_ext
      · funext p i
        simp [chartMove, add_assoc]
      · funext j p i
        simp [chartMove, add_assoc]
    simp only [complexChartMove, hm]
  have e3 : complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) (chartMove A₁ A₂ 1) =
      fderiv ℂ f (t, ζ) (![0, 0, 1, 1], 0) := by
    have eq : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V)
        (complexChartMove W (chartMove A₁ A₂ 1) τ) (complexTwistedTop b X ζ V)) =
        fun τ : ℂ => f (t + τ • ![0, 0, 1, 1], ζ) := by
      funext τ
      have e : t + τ • ![0, 0, 1, 1] = ![1, Complex.I, τ, τ] := by
        funext i
        fin_cases i <;> simp [ht]
      show _ = complexTotalOverTop a S (referenceFieldChain S V) (complexSpan A' (t + τ • ![0, 0, 1, 1]))
        (complexTwistedTop b X ζ V)
      rw [e, hsp, hsum]
    unfold complexFirstVariation
    rw [eq]
    exact (line _).deriv
  rw [e1, e2, e3, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;> simp
  · simp
end First
section Critical
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {k : ℕ} {b : Fin k → F.Site F.top × Fin 4}
  {X : Fin k → imaginaryQuaternions} {a θ δ Ca c C C₀ rL r' s c₁ : ℝ}
  {Wf : (Fin k → ℂ) → ComplexChainChart F}
theorem chartValues_chartOfValues (S : Finset F.Cell) (U : ChainChart F) (e : ChartValues S) :
    chartValues S (chartOfValues S U e) = e := by apply _root_.YangMills.Construction.BlockAverages.ColdTopSecondVariation.chartValues_chartOfValues <;> assumption
theorem chartAgreeOn_of_chartValues_eq {A A' : ChainChart F} (h : chartValues S A = chartValues S A') :
    ChartEqOnBonds S A A' := by
  refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
  · exact congrFun (congrArg Prod.fst h) ⟨x, hx⟩
  · have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    exact congrFun (congrFun (congrArg Prod.snd h) ⟨j, hj'⟩) ⟨x, hx⟩
theorem chartValues_chartShiftMulti {m : ℕ} (A : Fin m → ChainChart F) (x : Fin m → ℝ) :
    chartValues S (chartShiftMulti (zeroChart F) A x) = ∑ i, x i • chartValues S (A i) := by
  refine Prod.ext ?_ ?_
  · funext y
    simp [chartValues, chartShiftMulti, zeroChart, Prod.fst_sum, Finset.sum_apply]
  · funext j y
    simp [chartValues, chartShiftMulti, zeroChart, Prod.snd_sum, Finset.sum_apply]
theorem complexSpan_snoc {m : ℕ} (A : Fin m → ChainChart F) (B : ChainChart F) (t : Fin m → ℂ) (τ : ℂ) :
    complexSpan (Fin.snoc A B : Fin (m + 1) → ChainChart F) (Fin.snoc t τ : Fin (m + 1) → ℂ) =
      complexChartMove (complexSpan A t) B τ := by
  unfold complexSpan complexChartMove
  congr 1
  · apply chainChart_ext
    · funext p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_castSucc]
    · funext j p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_castSucc]
  · apply chainChart_ext
    · funext p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_castSucc]
    · funext j p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_castSucc]
theorem analyticAt_complexFirstVariation (hL : Odd F.blockSide) (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hrc : rL ≤ c) (hr'r : r' ≤ rL)
    (B : ChainChart F) {ζ₀ : Fin k → ℂ} (hζ₀ : ∑ l, ‖ζ₀ l‖ < r') :
    AnalyticAt ℂ (fun ζ => complexFirstVariation a S (referenceFieldChain S V) (Wf ζ)
      (complexTwistedTop b X ζ V) B) ζ₀ := by
  classical
  set bs := Module.finBasis ℝ (ChartValues S) with hbs
  set m := Module.finrank ℝ (ChartValues S) with hm
  set A : Fin m → ChainChart F := fun i => chartOfValues S (zeroChart F) (bs i) with hA
  set t : (Fin k → ℂ) → Fin m → ℂ := fun ζ i =>
    ((bs.coord i) (chartValues S (Wf ζ).re) : ℂ) + Complex.I * ((bs.coord i) (chartValues S (Wf ζ).im) : ℂ) with ht
  have hread : ∀ i, chartValues S (A i) = bs i := fun i => chartValues_chartOfValues S _ _
  have hsum : ∀ v : ChartValues S, ∑ i, (bs.coord i v) • bs i = v := fun v => by
    simp [bs.sum_repr v]
  have hsame : ∀ ζ, ChartEqOnBonds S (Wf ζ).re (complexSpan A (t ζ)).re ∧
      ChartEqOnBonds S (Wf ζ).im (complexSpan A (t ζ)).im := by
    intro ζ
    constructor
    · refine chartAgreeOn_of_chartValues_eq ?_
      show _ = chartValues S (chartShiftMulti (zeroChart F) A (Analytic.realParts (t ζ)))
      rw [chartValues_chartShiftMulti]
      have e : ∀ i, Analytic.realParts (t ζ) i = bs.coord i (chartValues S (Wf ζ).re) := fun i => by
        simp [Analytic.realParts, ht]
      simp only [e, hread]
      exact (hsum _).symm
    · refine chartAgreeOn_of_chartValues_eq ?_
      show _ = chartValues S (chartShiftMulti (zeroChart F) A (Analytic.imagParts (t ζ)))
      rw [chartValues_chartShiftMulti]
      have e : ∀ i, Analytic.imagParts (t ζ) i = bs.coord i (chartValues S (Wf ζ).im) := fun i => by
        simp [Analytic.imagParts, ht]
      simp only [e, hread]
      exact (hsum _).symm
  set Ap : Fin (m + 1) → ChainChart F := Fin.snoc A B with hAp
  set Φ : (Fin (m + 1) → ℂ) × (Fin k → ℂ) → ℂ := fun q =>
    complexTotalOverTop a S (referenceFieldChain S V) (complexSpan Ap q.1) (complexTwistedTop b X q.2 V) with hΦ
  set P : (Fin k → ℂ) → (Fin (m + 1) → ℂ) × (Fin k → ℂ) := fun ζ => (Fin.snoc (t ζ) 0, ζ) with hP
  have hΩ : IsOpen {ζ : Fin k → ℂ | ∑ l, ‖ζ l‖ < r'} := isOpen_lt (by fun_prop) continuous_const
  have hta : ∀ ζ, ∑ l, ‖ζ l‖ < r' → AnalyticAt ℂ t ζ := by
    intro ζ hζ
    rw [analyticAt_pi_iff]
    intro i
    exact hfam.analytic ζ hζ (bs.coord i)
  have hPa : ∀ ζ, ∑ l, ‖ζ l‖ < r' → AnalyticAt ℂ P ζ := by
    intro ζ hζ
    refine AnalyticAt.prod ?_ analyticAt_id
    rw [analyticAt_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
      exact analyticAt_const
    · simp only [Fin.snoc_castSucc]
      exact (analyticAt_pi_iff.1 (hta ζ hζ)) i
  have hsupP : ∀ ζ, ∑ l, ‖ζ l‖ < r' →
      complexSupWeightedNorm S δ (referenceFieldChain S V) (complexSpan Ap (P ζ).1) ≤ c := by
    intro ζ hζ
    have e2 : complexSpan Ap (P ζ).1 = complexSpan A (t ζ) := by
      show complexSpan (Fin.snoc A B) (Fin.snoc (t ζ) 0) = _
      rw [complexSpan_snoc, complexChartMove_zero]
    rw [e2]
    obtain ⟨h1, h2⟩ := hsame ζ
    have hs := (hfam.small ζ hζ).trans hrc
    have n1 : supWeightedNorm S δ (referenceFieldChain S V) (complexSpan A (t ζ)).re =
        supWeightedNorm S δ (referenceFieldChain S V) (Wf ζ).re := by
      unfold supWeightedNorm
      congr 1
      funext y
      exact (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_congr S _ _ _ _ h1).symm
    have n2 : supWeightedNorm S δ (referenceFieldChain S V) (complexSpan A (t ζ)).im =
        supWeightedNorm S δ (referenceFieldChain S V) (Wf ζ).im := by
      unfold supWeightedNorm
      congr 1
      funext y
      exact (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_congr S _ _ _ _ h2).symm
    show supWeightedNorm S δ (referenceFieldChain S V) (complexSpan A (t ζ)).re +
      supWeightedNorm S δ (referenceFieldChain S V) (complexSpan A (t ζ)).im ≤ c
    rw [n1, n2]
    exact hs
  have hc' : r' ≤ c := hr'r.trans hrc
  have hΦa : ∀ ζ, ∑ l, ‖ζ l‖ < r' → AnalyticAt ℂ Φ (P ζ) := fun ζ hζ =>
    hB.analytic (m + 1) Ap (P ζ).1 ζ (hsupP ζ hζ) (hζ.le.trans hc')
  set e : (Fin (m + 1) → ℂ) × (Fin k → ℂ) := (Pi.single (Fin.last m) 1, 0) with he
  have hfd : AnalyticAt ℂ (fun ζ => fderiv ℂ Φ (P ζ) e) ζ₀ :=
    ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt _).comp
      (AnalyticAt.comp (g := fderiv ℂ Φ) (hΦa ζ₀ hζ₀).fderiv (hPa ζ₀ hζ₀))
  refine hfd.congr ?_
  filter_upwards [hΩ.mem_nhds hζ₀] with ζ hζ
  have hd := (hΦa ζ hζ).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun τ : ℂ => P ζ + τ • e) e 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add (P ζ)
    simpa using this
  have e0 : P ζ + (0 : ℂ) • e = P ζ := by simp
  have hd' : HasFDerivAt Φ (fderiv ℂ Φ (P ζ)) (P ζ + (0 : ℂ) • e) := by
    rw [e0]
    exact hd
  have hc := hd'.comp_hasDerivAt (0 : ℂ) hl
  have hline : (Φ ∘ fun τ : ℂ => P ζ + τ • e) = fun τ : ℂ =>
      complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove (complexSpan A (t ζ)) B τ)
        (complexTwistedTop b X ζ V) := by
    funext τ
    have e2 : (P ζ + τ • e).1 = Fin.snoc (t ζ) τ := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [hP, he]
      · simp [hP, he, Fin.snoc_castSucc]
    have e3 : (P ζ + τ • e).2 = ζ := by
      simp [hP, he]
    show complexTotalOverTop a S (referenceFieldChain S V) (complexSpan Ap (P ζ + τ • e).1)
      (complexTwistedTop b X (P ζ + τ • e).2 V) = _
    rw [e2, e3, hAp, complexSpan_snoc]
  rw [hline] at hc
  obtain ⟨h1, h2⟩ := hsame ζ
  have e4 : complexFirstVariation a S (referenceFieldChain S V) (Wf ζ) (complexTwistedTop b X ζ V) B =
      complexFirstVariation a S (referenceFieldChain S V) (complexSpan A (t ζ)) (complexTwistedTop b X ζ V) B :=
    complexFirstVariation_congr_point hL _ _ B h1 h2
  rw [e4]
  exact hc.deriv.symm
theorem complexFirstVariation_eq_zero (hL : Odd F.blockSide) (hdel : 0 < δ)
    (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hrc : rL ≤ c) (hr'r : r' ≤ rL) (hrc₁ : rL < c₁)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U)
    (hAny : ∀ (W : F.GaugeField F.top) (U : ChainChart F), supWeightedNorm S δ (referenceFieldChain S V) U ≤ rL →
      (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
        IsStationaryAlong a S (referenceFieldChain S V) W U A) →
      ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) W U A)
    (hvan : Analytic.vanishingOnRealPointsStatement) (B : ChainChart F)
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ < r') :
    complexFirstVariation a S (referenceFieldChain S V) (Wf ζ) (complexTwistedTop b X ζ V) B = 0 := by
  refine hvan k r' _ (fun ζ hζ => analyticAt_complexFirstVariation hL hB hfam hrc hr'r B hζ) (fun x hx => ?_) ζ hζ
  have hxc : ∑ l, ‖((x l : ℝ) : ℂ)‖ < r' := by
    simpa [Complex.norm_real] using hx
  set U := (Wf fun l => (x l : ℂ)).re with hU
  have hsupU : supWeightedNorm S δ (referenceFieldChain S V) U ≤ rL := by
    have h1 : supWeightedNorm S δ (referenceFieldChain S V) U ≤
        complexSupWeightedNorm S δ (referenceFieldChain S V) (Wf fun l => (x l : ℂ)) :=
      le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _)
    exact h1.trans (hfam.small _ hxc)
  have hsum : ∑ l, |x l| ≤ c := hx.le.trans (hr'r.trans hrc)
  have hcong : ∀ A : ChainChart F, complexFirstVariation a S (referenceFieldChain S V) (realChart U)
      (complexTwistedTop b X (fun l => (x l : ℂ)) V) A =
      complexFirstVariation a S (referenceFieldChain S V) (Wf fun l => (x l : ℂ))
        (complexTwistedTop b X (fun l => (x l : ℂ)) V) A := by
    intro A
    refine complexFirstVariation_congr_point hL _ _ A ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ?_
    have := hfam.real x hx
    exact ⟨fun y hy => (this.1 y hy).symm, fun j hj y hy => (this.2 j hj y hy).symm⟩
  have hreal : ∀ A : ChainChart F, _ := fun A =>
    hasDerivAt_chartAction_of_complexFirstVariation (ζ := x) hL hdel.le hB hreg hsum U A (hsupU.trans hrc)
      (lt_of_le_of_lt hsupU hrc₁)
  have hcr := hAny (rotatedField (bondSpread b X x) V) U hsupU (fun A hA => by
    have h1 := (hreal A).1
    rw [hcong A, hfam.critical _ hxc A hA] at h1
    unfold IsStationaryAlong
    simpa using h1)
  have h2 := hreal B
  rw [hcong B] at h2
  have h3 : HasDerivAt (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U B τ)
      (rotatedField (bondSpread b X x) V)) 0 0 := hcr B
  have h4 := h2.1.unique h3
  exact Complex.ext h4 h2.2
end Critical
section Sizes
variable {S : Finset F.Cell} {S' : Finset F'.Cell}
theorem localNorm_le_supWeightedNorm (hL : 0 < F.blockSide) (δ : ℝ) (hdel : 0 ≤ δ) (R : F.FieldChain)
    (A : ChainChart F) (z : F.Cell) :
    localNorm S R A (constOneWeights F) z ≤ Real.exp (3 * δ) * supWeightedNorm S δ R A := by
  have h := localNorm_le_decay (S := S) δ hdel R A z z
  rw [CoordinateSeminorms.cellSupDist_self] at h
  simp only [Nat.cast_zero, mul_zero, add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_decay_le_supWeightedNorm S hL δ hdel R A z)
    (Real.exp_pos _).le)
theorem cellSupDist_mul_le_baseDistance (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) :
    (cellSupDist (enclosingCell x) Y : ℤ) * (F.blockSide : ℤ) ^ F.top ≤
      baseDistance x (cellCentre 0 Y) + (F.blockSide : ℤ) ^ F.top := by
  have h := cellSupDist_mul_le_baseDistance_add hodd (baseSite x) Y
  rw [VariationRates.enclosingCell_baseSite hodd hj hx] at h
  have e : baseDistance (baseSite x) (cellCentre 0 Y) = baseDistance x (cellCentre 0 Y) := by
    simp only [baseDistance, PlaquettesNearCell.baseSite_zero]
  rwa [e] at h
theorem tentCutoff_eq_zero_of_far (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) {ρ : ℝ}
    (h : ρ + 1 ≤ (cellSupDist (enclosingCell x) Y : ℝ)) : tentCutoff F Y ρ j x = 0 := by
  refine tentCutoff_eq_zero hodd.pos Y ?_
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hodd.pos
    positivity
  have h1 := cellSupDist_mul_le_baseDistance hodd hj hx Y
  have h2 : (cellSupDist (enclosingCell x) Y : ℝ) * (F.blockSide : ℝ) ^ F.top ≤
      (baseDistance x (cellCentre 0 Y) : ℝ) + (F.blockSide : ℝ) ^ F.top := by
    exact_mod_cast h1
  have h3 := mul_le_mul_of_nonneg_right h hN.le
  linarith
theorem tentCutoff_siteAtOffset_eq_one (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) {ρ : ℝ}
    {ρ' : ℕ} {p : Fin 4 → ℤ}
    (hρ : (ρ' : ℝ) ≤ ρ - 1) (hp : WithinCellRadius F.blockSide F.top ρ' j p) :
    tentCutoff F Y ρ j (siteAtOffset j Y p) = 1 := by
  refine tentCutoff_eq_one hL Y ?_
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
    positivity
  have h1 := baseDistance_siteAtOffset_le hL hj Y hp
  have h2 : (baseDistance (siteAtOffset j Y p) (cellCentre 0 Y) : ℝ) ≤ (ρ' : ℝ) * (F.blockSide : ℝ) ^ F.top := by
    exact_mod_cast h1
  exact h2.trans (mul_le_mul_of_nonneg_right hρ hN.le)
theorem chartsAgree_chartSmul (hL : 0 < F.blockSide) (Y : F.Cell) (Y' : F'.Cell) {ρ' : ℕ} {ρ : ℝ}
    (hs : ∀ i, F.extent i = 0 ∨ 2 * ρ' + 2 < F.extent i) (hρ : (ρ' : ℝ) ≤ ρ - 1) (A' : ChainChart F') :
    ChartsAgreeAtOffsets Y Y' ρ' (Offsets.chartSmul (tentCutoff F Y ρ) (chartTranslate Y Y' A')) A' where
  fine p i hp := by
    have h1 := (chartsAgree_chartTranslate hL Y Y' hs A').fine p i hp
    show tentCutoff F Y ρ 0 (siteAtOffset 0 Y p) • (chartTranslate Y Y' A').fine (siteAtOffset 0 Y p) i = _
    rw [tentCutoff_siteAtOffset_eq_one hL (Nat.zero_le _) Y hρ hp, one_smul, h1]
  coarse j p i hj hp := by
    have h1 := (chartsAgree_chartTranslate hL Y Y' hs A').coarse j p i hj hp
    show tentCutoff F Y ρ (j + 1) (siteAtOffset (j + 1) Y p) •
      (chartTranslate Y Y' A').coarse j (siteAtOffset (j + 1) Y p) i = _
    rw [tentCutoff_siteAtOffset_eq_one hL (by omega) Y hρ hp, one_smul, h1]
theorem localNormSq_cellBall_le (S' : Finset F'.Cell) (R' : F'.FieldChain) (A' : ChainChart F') (z' : F'.Cell)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, localNorm S' R' A' (constOneWeights F') y ≤ M) :
    localNormSq S' (cellBall S' z' 4) R' A' (constOneWeights F') ≤ 6561 * M ^ 2 := by
  classical
  refine (localNormSq_le_sum_singletons S' _ R' A' _).trans ?_
  have h1 : ∀ y ∈ cellBall S' z' 4, localNormSq S' {y} R' A' (constOneWeights F') ≤ M ^ 2 := by
    intro y hy
    have hyS : y ∈ S' := (Finset.mem_filter.1 hy).1
    have h2 : localNormSq S' {y} R' A' (constOneWeights F') ≤
        localNormSq S' (cellBall S' y 3) R' A' (constOneWeights F') :=
      localNormSq_mono_cells S' (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact mem_cellBall_self hyS) R' A' _
    refine h2.trans ?_
    have h3 := pow_le_pow_left₀ (localNorm_nonneg _ _ _ _ _) (hM y) 2
    unfold localNorm at h3
    rwa [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)] at h3
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h4 := PatchLocality.card_le_of_cellSupDist_le z' 4 (cellBall S' z' 4) (fun y hy => by
    have h := (Finset.mem_filter.1 hy).2
    rw [CoordinateSeminorms.cellSupDist_comm]
    exact h)
  have h5 : (cellBall S' z' 4).card ≤ 6561 := h4.trans (le_of_eq (by norm_num))
  have h6 : ((cellBall S' z' 4).card : ℝ) ≤ 6561 := by exact_mod_cast h5
  exact mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
theorem localNorm_chartSmul_le (hodd : Odd F.blockSide) (hamb : IsAdmissibleAmbient F) {R : F.FieldChain}
    {R' : F'.FieldChain} {Y : F.Cell} {Y' : F'.Cell}
    {r : ℕ} (hr : 1000 ≤ r) (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hN : ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' (r - 100) A A' →
      ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)) →
        localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) R A (constOneWeights F) =
          localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) R' A' (constOneWeights F'))
    (A' : ChainChart F') {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, localNorm S' R' A' (constOneWeights F') y ≤ M)
    (z : F.Cell) :
    localNorm S R (Offsets.chartSmul (tentCutoff F Y ((r : ℝ) - 200)) (chartTranslate Y Y' A')) (constOneWeights F) z ≤
      11700 * M := by
  set g : Fin 4 → ℤ := fun i => ((z - Y : F.Cell) i).valMinAbs with hg
  have hz : z = Y + siteOfCoords F.top g := by
    funext i
    simp only [Pi.add_apply, siteOfCoords, hg, ZMod.coe_valMinAbs]
    simp
  by_cases hin : ∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)
  · have hs' : ∀ i, F.extent i = 0 ∨ 2 * (r - 100) + 2 < F.extent i := fun i =>
      (hs i).imp id fun h => by omega
    have e := hN _ A' (chartsAgree_chartTranslate hodd.pos Y Y' hs' A') g hin
    rw [← hz] at e
    have h1 := localNormSq_chartSmul_le hamb hodd S R (tentCutoff_isCutoff hodd.pos Y ((r : ℝ) - 200))
      (chartTranslate Y Y' A') z
    have h2 := localNormSq_cellBall_le S' R' A' (Y' + siteOfCoords F'.top g) hM0 hM
    rw [e] at h1
    unfold localNorm
    refine Real.sqrt_le_iff.2 ⟨by positivity, h1.trans ?_⟩
    have h3 : 20737 * localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) R' A' (constOneWeights F') ≤
        20737 * (6561 * M ^ 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    refine h3.trans ?_
    have h4 : 0 ≤ M ^ 2 := sq_nonneg _
    nlinarith
  · push_neg at hin
    obtain ⟨i, hi⟩ := hin
    have hle : (g i).natAbs ≤ cellSupDist z Y :=
      Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have hd : (r : ℤ) - 104 ≤ (cellSupDist z Y : ℤ) := by
      have h1 : ((r - 100 : ℕ) : ℤ) = (r : ℤ) - 100 := by omega
      rw [h1] at hi
      have h2 : |g i| = ((g i).natAbs : ℤ) := Int.abs_eq_natAbs _
      have h3 : ((g i).natAbs : ℤ) ≤ (cellSupDist z Y : ℤ) := by exact_mod_cast hle
      omega
    have hfar : ∀ {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}, x ∈ sitesOfCells S j →
        enclosingCell x ∈ cellBall S z 4 → tentCutoff F Y ((r : ℝ) - 200) j x = 0 := by
      intro j hj x hx hc
      refine tentCutoff_eq_zero_of_far hodd hj hx Y ?_
      have h1 : cellSupDist z (enclosingCell x) ≤ 4 := (Finset.mem_filter.1 hc).2
      have h2 := CoordinateSeminorms.cellSupDist_triangle z (enclosingCell x) Y
      have h3 : (r : ℤ) - 108 ≤ (cellSupDist (enclosingCell x) Y : ℤ) := by omega
      have h4 : (r : ℝ) - 108 ≤ (cellSupDist (enclosingCell x) Y : ℝ) := by exact_mod_cast h3
      linarith
    have h0 := localNorm_congr (S := S) hamb hodd R (A := Offsets.chartSmul (tentCutoff F Y ((r : ℝ) - 200))
      (chartTranslate Y Y' A')) (A' := zeroChart F) (constOneWeights F) z (fun b hb => by
        obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
        show tentCutoff F Y ((r : ℝ) - 200) 0 b.1 • _ = 0
        rw [hfar (Nat.zero_le _) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, zero_smul])
      (fun j hj b hb => by
        obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
        show tentCutoff F Y ((r : ℝ) - 200) (j + 1) b.1 • _ = 0
        rw [hfar (by omega) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, zero_smul])
    rw [h0, localNorm_zeroChart]
    positivity
end Sizes
section Sums
variable {S : Finset F.Cell}
def cellL4 (S : Finset F.Cell) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) : ℝ :=
  Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} 0, ‖f b.1 b.2‖ ^ 4))
theorem cellwiseL4Norm_sq_classWeight (φ : F.Cell → ℝ) (p : F.Site 0) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    cellwiseL4Norm S (classWeight F φ 0 p 0) f ^ 2 = ∑ z ∈ S, Real.exp (2 * φ z) * cellL4 S f z ^ 2 := by
  unfold cellwiseL4Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e : ∀ b ∈ bondsOver S {z} 0, (classWeight F φ 0 p 0 b.1 * ‖f b.1 b.2‖) ^ 4 =
      (Real.exp (2 * φ z)) ^ 2 * ‖f b.1 b.2‖ ^ 4 := by
    intro b hb
    have hc : enclosingCell b.1 = z := by simpa using (mem_bondsOver.1 hb).2
    rw [CoordinateCutoffs.classWeight_zero, hc, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
  unfold cellL4
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
theorem cellwiseL4Norm_le {δ K Cd₂ : ℝ} (hK : 0 ≤ K) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (y : F.Cell)
    (hQ : ∀ z ∈ S, cellL4 S f z ≤ K)
    (hCd : ∑ z ∈ S, Real.exp (-(2 * δ) * cellSupDist z y) ≤ Cd₂) :
    cellwiseL4Norm S (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0 0) f ≤ K * Real.sqrt Cd₂ := by
  have h1 := cellwiseL4Norm_sq_classWeight (S := S) (fun x => -δ * (cellSupDist x y : ℝ)) 0 f
  have h2 : cellwiseL4Norm S (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0 0) f ^ 2 ≤ K ^ 2 * Cd₂ := by
    rw [h1]
    refine le_trans (Finset.sum_le_sum fun z hz => ?_) (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hCd (sq_nonneg K))
    have e : 2 * (-δ * (cellSupDist z y : ℝ)) = -(2 * δ) * cellSupDist z y := by ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hQ z hz) 2) (Real.exp_pos _).le
  have h4 := Real.le_sqrt_of_sq_le h2
  refine h4.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
theorem cellwiseL4Norm_le_of_vanish {δ K Cd₁ : ℝ} {R : ℕ} (hdel : 0 ≤ δ) (hK : 0 ≤ K)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (y : F.Cell)
    (hQ : ∀ z ∈ S, cellL4 S f z ≤ K) (hQ0 : ∀ z ∈ S, cellSupDist z y ≤ R → cellL4 S f z = 0)
    (hCd : ∑ z ∈ S, Real.exp (-δ * cellSupDist z y) ≤ Cd₁) :
    cellwiseL4Norm S (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0 0) f ≤
      K * Real.sqrt Cd₁ * Real.exp (-δ * R / 2) := by
  have h1 := cellwiseL4Norm_sq_classWeight (S := S) (fun x => -δ * (cellSupDist x y : ℝ)) 0 f
  have hterm : ∀ z ∈ S, Real.exp (2 * (-δ * (cellSupDist z y : ℝ))) * cellL4 S f z ^ 2 ≤
      K ^ 2 * Real.exp (-δ * R) * Real.exp (-δ * cellSupDist z y) := by
    intro z hz
    by_cases hd : cellSupDist z y ≤ R
    · rw [hQ0 z hz hd]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · have hd' : (R : ℝ) ≤ cellSupDist z y := by
        have : R ≤ cellSupDist z y := by omega
        exact_mod_cast this
      have e1 : Real.exp (2 * (-δ * (cellSupDist z y : ℝ))) ≤
          Real.exp (-δ * R) * Real.exp (-δ * cellSupDist z y) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hd' hdel
        nlinarith
      have e2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hQ z hz) 2
      calc Real.exp (2 * (-δ * (cellSupDist z y : ℝ))) * cellL4 S f z ^ 2
          ≤ (Real.exp (-δ * R) * Real.exp (-δ * cellSupDist z y)) * K ^ 2 :=
            mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
        _ = K ^ 2 * Real.exp (-δ * R) * Real.exp (-δ * cellSupDist z y) := by ring
  have h2 : cellwiseL4Norm S (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0 0) f ^ 2 ≤
      (K * Real.sqrt Cd₁ * Real.exp (-δ * R / 2)) ^ 2 := by
    rw [h1]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hCd0 : 0 ≤ Cd₁ := le_trans (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hCd
    have e : (K * Real.sqrt Cd₁ * Real.exp (-δ * R / 2)) ^ 2 = K ^ 2 * Real.exp (-δ * R) * Cd₁ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCd0, ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (-δ * R / 2) = -δ * R := by
        push_cast
        ring
      rw [this]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hCd (by positivity)
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) (by norm_num)).1 h2
end Sums
structure ComparisonData (a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ) (S : Finset F.Cell)
    (S' : Finset F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    {k : ℕ} (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions)
    (Wf : (Fin k → ℂ) → ComplexChainChart F)
    (Wf' : (Fin k → ℂ) → ComplexChainChart F') : Prop where
  odd_blockSide : Odd F.blockSide
  blockSide_eq : F'.blockSide = F.blockSide
  depth_eq : F'.depth = F.depth
  ambient : IsAdmissibleAmbient F
  ambient' : IsAdmissibleAmbient F'
  delta_pos : 0 < δ
  delta_le : δ ≤ 1 / 8
  C_pos : 0 < C
  C₀_pos : 0 < C₀
  CT_pos : 0 < CT
  Cl_pos : 0 < Cl
  Kp_pos : 0 < Kp
  Kg_pos : 0 < Kg
  s_pos : 0 < s
  r'_pos : 0 < r'
  r'_le : r' ≤ rL
  rL_le : rL ≤ c
  radius_ge : 1000 ≤ r
  extent_large : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
  extent_large' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i
  top_agree : ∀ (ζ : Fin k → ℂ) (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top (r - 202) F.top p →
    complexTwistedTop (offsetBonds Y h) X ζ V (siteAtOffset F.top Y p) i =
      complexTwistedTop (offsetBonds Y' h) X ζ V' (siteAtOffset F'.top Y' p) i
  twistedBounds : TwistedTotalBounds a θ δ Ca c C s S V (offsetBonds Y h) X
  taylorBounds : ActionTaylorBounds a θ δ Ct cT CT s S V
  family : IsComplexCriticalFamily a θ δ C₀ rL r' s S V (offsetBonds Y h) X Wf
  family' : IsComplexCriticalFamily a θ δ C₀ rL r' s S' V' (offsetBonds Y' h) X Wf'
  critical' : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' → ∀ B' : ChainChart F',
    complexFirstVariation a S' (referenceFieldChain S' V') (Wf' ζ) (complexTwistedTop (offsetBonds Y' h) X ζ V') B' = 0
  projection : ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions, ∃ v : F.Site 0 → Fin 4 → imaginaryQuaternions,
    GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (fun x i => u x i - v x i) ∧
    ∀ (φ : F.Cell → ℝ) (δ' : ℝ) (p : F.Site 0), 0 ≤ δ' → δ' ≤ 1 / 8 →
      (∀ y y', |φ y - φ y'| ≤ δ' * cellSupDist y y') →
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (baseOnlyChart v) (classWeight F φ 0 p) ≤
        Kp * cellwiseL4Norm S (classWeight F φ 0 p 0) (covariantDiff (referenceFieldChain S V 0)
          (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun x i => u x i))
  gaugeDiff : ∀ (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z₀ : F.Cell), z₀ ∈ S →
    cellL4 S (covariantDiff (referenceFieldChain S V 0)
      (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun x i => u x i)) z₀ ≤
      Kg * ∑ z ∈ cellBall S z₀ 22, localNorm S (referenceFieldChain S V) (baseOnlyChart u) (constOneWeights F) z
  firstVariation : ∀ (W : ComplexChainChart F) (W' : ComplexChainChart F') (T : F.ComplexField F.top)
    (T' : F'.ComplexField F'.top) (B : ChainChart F) (B' : ChainChart F'),
    ChartsAgreeAtOffsets Y Y' (r - 202) W.re W'.re → ChartsAgreeAtOffsets Y Y' (r - 202) W.im W'.im →
    (∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top (r - 202) F.top p →
      T (siteAtOffset F.top Y p) i = T' (siteAtOffset F'.top Y' p) i) →
    ChartsAgreeAtOffsets Y Y' (r - 202) B B' → SupportedNear S Y (r - 202 - 10) B →
    SupportedNear S' Y' (r - 202 - 10) B' →
    complexFirstVariation a S (referenceFieldChain S V) W T B =
      complexFirstVariation a S' (referenceFieldChain S' V') W' T' B'
  gaugeMap_agree : ∀ (u : F.Site 0 → Fin 4 → ℍ[ℝ]) (u' : F'.Site 0 → Fin 4 → ℍ[ℝ]),
    (∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top (r - 202) 0 p →
      u (siteAtOffset 0 Y p) i = u' (siteAtOffset 0 Y' p) i) →
    ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (r - 202 - 30) 0 q → siteAtOffset 0 Y q ∈ sitesOfCells S 0 →
      GaugeMap.gaugeMap S V (referenceFieldChain S V 0) u (siteAtOffset 0 Y q) =
        GaugeMap.gaugeMap S' V' (referenceFieldChain S' V' 0) u' (siteAtOffset 0 Y' q)
  sites_iff : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (r - 202 - 30) 0 q →
    (siteAtOffset 0 Y q ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' q ∈ sitesOfCells S' 0)
  localNormSq_eq : ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' (r - 100) A A' →
    ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)) →
      localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) (referenceFieldChain S V) A (constOneWeights F) =
        localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) (referenceFieldChain S' V') A'
          (constOneWeights F')
  localVariation : ∀ (W : ComplexChainChart F) (ζ : Fin k → ℂ) (B : ChainChart F),
    complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ rL → ∑ l, ‖ζ l‖ ≤ rL →
    ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop (offsetBonds Y h) X ζ V) B‖ ≤
      Cl * ∑ z ∈ S, firstVariationCellWeight S (referenceFieldChain S V) s W (offsetBonds Y h) ζ z *
        localNorm S (referenceFieldChain S V) B (constOneWeights F) z
  sumExp₁ : ∀ y : F.Cell, ∑ z ∈ S, Real.exp (-δ * cellSupDist z y) ≤ Cd₁
  sumExp₂ : ∀ y : F.Cell, ∑ z ∈ S, Real.exp (-(2 * δ) * cellSupDist z y) ≤ Cd₂
section Core
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
def cutTranslate (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (A' : ChainChart F') : ChainChart F :=
  Offsets.chartSmul (tentCutoff F Y ((r : ℝ) - 200)) (chartTranslate Y Y' A')
theorem cutTranslate_agree (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    (A' : ChainChart F') : ChartsAgreeAtOffsets Y Y' (r - 202) (cutTranslate Y Y' r A') A' := by
  have hr := t.radius_ge
  refine chartsAgree_chartSmul t.odd_blockSide.pos Y Y' (fun i => (t.extent_large i).imp id fun e => by omega) ?_ A'
  have : ((r - 202 : ℕ) : ℝ) = (r : ℝ) - 202 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [this]
  linarith
theorem localNorm_cutTranslate_le
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ M) (z : F.Cell) :
    localNorm S (referenceFieldChain S V) (cutTranslate Y Y' r A') (constOneWeights F) z ≤ 11700 * M :=
  localNorm_chartSmul_le t.odd_blockSide t.ambient t.radius_ge t.extent_large t.localNormSq_eq A' hM0 hM z
theorem gaugeMap_cutTranslate_eq_zero
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} (hsl : GaugeMap.InGaugeSlice S' V' (referenceFieldChain S' V' 0) A'.fine) {x : F.Site 0}
    (hx : x ∈ sitesOfCells S 0)
    (hb : (baseDistance x (cellCentre 0 Y) : ℤ) ≤ ((r - 202 - 30 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top) :
    GaugeMap.gaugeMap S V (referenceFieldChain S V 0) (fun y i => (cutTranslate Y Y' r A').fine y i) x = 0 := by
  set q : Fin 4 → ℤ := fun i => ((x - cellCentre 0 Y : F.Site 0) i).valMinAbs with hq
  have hxq : x = siteAtOffset 0 Y q := by
    unfold siteAtOffset
    have h1 : siteOfCoords 0 q = x - cellCentre 0 Y := (eq_siteOfCoords_valMinAbs (x - cellCentre 0 Y : F.Site 0)).symm
    rw [h1]
    abel
  have hw : WithinCellRadius F.blockSide F.top (r - 202 - 30) 0 q := by
    intro i
    have h1 := WeightedAverages.Chains.natAbs_le_baseDistance x (cellCentre 0 Y) i
    rw [PlaquettesNearCell.baseSite_zero] at h1
    have h2 : |q i| ≤ (baseDistance x (cellCentre 0 Y) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    show (F.blockSide : ℤ) ^ 0 * |q i| ≤ _
    rw [pow_zero, one_mul]
    exact h2.trans hb
  have hagree := cutTranslate_agree t A'
  rw [hxq] at hx ⊢
  rw [t.gaugeMap_agree _ (fun x i => (A'.fine x i : ℍ[ℝ])) (fun p i hp => by rw [hagree.fine p i hp]) q hw hx]
  exact hsl _ ((t.sites_iff q hw).1 hx)
theorem cellL4_cutTranslate_eq_zero
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} (hsl : GaugeMap.InGaugeSlice S' V' (referenceFieldChain S' V' 0) A'.fine) {z : F.Cell}
    (hz : cellSupDist z Y ≤ r - 236) :
    cellL4 S (covariantDiff (referenceFieldChain S V 0)
      (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun y i => (cutTranslate Y Y' r A').fine y i)) z = 0 := by
  have hr := t.radius_ge
  have hodd := t.odd_blockSide
  have hN0 : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by
    have h0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    exact pow_pos h0 _
  unfold cellL4
  have hzero : ∀ b ∈ bondsOver S {z} 0, covariantDiff (referenceFieldChain S V 0)
      (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun y i => (cutTranslate Y Y' r A').fine y i) b.1 b.2 = 0 := by
    intro b hb
    obtain ⟨hbS, hc⟩ := mem_bondsOver.1 hb
    have hcz : enclosingCell b.1 = z := by simpa using hc
    have hb' := Finset.mem_filter.1 hbS
    have h1 : b.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 hb'.1).1
    have h2 : b.1 + unitStep 0 b.2 ∈ sitesOfCells S 0 := hb'.2
    have h3 := baseDistance_le_cellSupDist_add_one_mul hodd h1 Y
    rw [hcz] at h3
    obtain ⟨h4, -⟩ := PlaquettesNearCell.baseDistance_add_unitStep b.1 b.2 (cellCentre 0 Y)
    have hcast : ((r - 202 - 30 : ℕ) : ℤ) = (r : ℤ) - 232 := by omega
    have hz' : ((cellSupDist z Y + 1 : ℕ) : ℤ) ≤ (r : ℤ) - 235 := by
      push_cast
      omega
    have h5 : ((cellSupDist z Y + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top ≤
        ((r : ℤ) - 235) * (F.blockSide : ℤ) ^ F.top :=
      mul_le_mul_of_nonneg_right hz' hN0.le
    have h6 : (baseDistance b.1 (cellCentre 0 Y) : ℤ) ≤ ((r - 202 - 30 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top := by
      rw [hcast]
      nlinarith
    have h7 : (baseDistance (b.1 + unitStep 0 b.2) (cellCentre 0 Y) : ℤ) ≤
        ((r - 202 - 30 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top := by
      have : (baseDistance (b.1 + unitStep 0 b.2) (cellCentre 0 Y) : ℤ) ≤
          (baseDistance b.1 (cellCentre 0 Y) : ℤ) + 1 := by
        exact_mod_cast h4
      rw [hcast]
      nlinarith
    simp only [covariantDiff]
    rw [gaugeMap_cutTranslate_eq_zero t hsl h1 h6, gaugeMap_cutTranslate_eq_zero t hsl h2 h7]
    simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  rw [Finset.sum_eq_zero fun b hb => by rw [hzero b hb]; simp]
  simp
end Core
section Core2
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
theorem nonneg_of_sum_exp_le {Cd : ℝ} {ε : ℝ} (S : Finset F.Cell) (y : F.Cell)
    (h : ∑ z ∈ S, Real.exp (-ε * cellSupDist z y) ≤ Cd) :
    0 ≤ Cd := le_trans (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) h
theorem exists_slice_projection
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} (hsl : GaugeMap.InGaugeSlice S' V' (referenceFieldChain S' V' 0) A'.fine) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ y, localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ M) :
    ∃ v : F.Site 0 → Fin 4 → imaginaryQuaternions,
      GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (fun x i => (cutTranslate Y Y' r A').fine x i - v x i) ∧
      (∀ y, _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (baseOnlyChart v)
        (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) ≤
          Kp * (Kg * 45 ^ 4 * (11700 * M) * Real.sqrt Cd₂)) ∧
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (baseOnlyChart v)
        (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤
        Kp * (Kg * 45 ^ 4 * (11700 * M) * Real.sqrt Cd₁ * Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2)) := by
  classical
  obtain ⟨v, hs, hp⟩ := t.projection (cutTranslate Y Y' r A').fine
  refine ⟨v, hs, ?_⟩
  have hKp := t.Kp_pos
  have hKg := t.Kg_pos
  set f := covariantDiff (referenceFieldChain S V 0)
    (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun y i => (cutTranslate Y Y' r A').fine y i) with hf
  have hK0 : 0 ≤ Kg * 45 ^ 4 * (11700 * M) := by positivity
  have hQ : ∀ z ∈ S, cellL4 S f z ≤ Kg * 45 ^ 4 * (11700 * M) := by
    intro z hz
    refine (t.gaugeDiff _ z hz).trans ?_
    have h1 : ∑ y ∈ cellBall S z 22, localNorm S (referenceFieldChain S V)
        (baseOnlyChart (cutTranslate Y Y' r A').fine) (constOneWeights F) y ≤
        ((cellBall S z 22).card : ℝ) * (11700 * M) := by
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun y _ => ?_
      exact (localNorm_baseOnlyChart_le _ _ y).trans (localNorm_cutTranslate_le t hM0 hM y)
    have h2 := PatchLocality.card_le_of_cellSupDist_le z 22 (cellBall S z 22) (fun y hy => by
      have h := (Finset.mem_filter.1 hy).2
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact h)
    have h3 : ((cellBall S z 22).card : ℝ) ≤ 45 ^ 4 := by
      have : (cellBall S z 22).card ≤ 45 ^ 4 := h2.trans (le_of_eq (by norm_num))
      exact_mod_cast this
    have h4 : ((cellBall S z 22).card : ℝ) * (11700 * M) ≤ 45 ^ 4 * (11700 * M) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    calc Kg * ∑ y ∈ cellBall S z 22, localNorm S (referenceFieldChain S V)
          (baseOnlyChart (cutTranslate Y Y' r A').fine) (constOneWeights F) y
        ≤ Kg * (45 ^ 4 * (11700 * M)) := mul_le_mul_of_nonneg_left (h1.trans h4) hKg.le
      _ = Kg * 45 ^ 4 * (11700 * M) := by ring
  have hdel := t.delta_pos
  refine ⟨fun y => ?_, ?_⟩
  · refine (hp (fun x => -δ * (cellSupDist x y : ℝ)) δ 0 hdel.le t.delta_le
      (fun z z' => abs_neg_mul_cellSupDist_sub_le δ hdel.le y z z')).trans ?_
    exact mul_le_mul_of_nonneg_left (cellwiseL4Norm_le hK0 f y hQ (t.sumExp₂ y)) hKp.le
  · refine (hp (fun x => -δ * (cellSupDist x Y : ℝ)) δ 0 hdel.le t.delta_le
      (fun z z' => abs_neg_mul_cellSupDist_sub_le δ hdel.le Y z z')).trans ?_
    exact mul_le_mul_of_nonneg_left (cellwiseL4Norm_le_of_vanish hdel.le hK0 f Y hQ
      (fun z _ hz => cellL4_cutTranslate_eq_zero t hsl hz) (t.sumExp₁ Y)) hKp.le
theorem weightedNorm_cutTranslate_le
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ M) (y : F.Cell) :
    _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (cutTranslate Y Y' r A')
      (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) ≤
      Real.exp (3 * δ) * (11700 * M) * Real.sqrt Cd₂ := by
  have hdel := t.delta_pos
  have hCd : 0 ≤ Cd₂ := nonneg_of_sum_exp_le S y (t.sumExp₂ y)
  have hterm : ∀ z ∈ S, localNorm S (referenceFieldChain S V) (cutTranslate Y Y' r A')
      (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) z ^ 2 ≤
      (Real.exp (3 * δ) * (11700 * M)) ^ 2 * Real.exp (-(2 * δ) * cellSupDist z y) := by
    intro z _
    have h1 := (localNorm_decay_le (S := S) δ hdel.le (referenceFieldChain S V) (cutTranslate Y Y' r A') y z).trans
      (mul_le_mul_of_nonneg_left (localNorm_cutTranslate_le t hM0 hM z) (Real.exp_pos _).le)
    have h2 := pow_le_pow_left₀ (localNorm_nonneg _ _ _ _ _) h1 2
    refine h2.trans (le_of_eq ?_)
    have e : Real.exp (3 * δ - δ * (cellSupDist z y : ℝ)) ^ 2 =
        Real.exp (3 * δ) ^ 2 * Real.exp (-(2 * δ) * cellSupDist z y) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [mul_pow, e, mul_pow]
    ring
  have hsq : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (cutTranslate Y Y' r A')
      (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0) ^ 2 ≤
      (Real.exp (3 * δ) * (11700 * M) * Real.sqrt Cd₂) ^ 2 := by
    unfold _root_.YangMills.Construction.BlockAverages.weightedNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, mul_pow _ (Real.sqrt Cd₂), Real.sq_sqrt hCd]
    exact mul_le_mul_of_nonneg_left (t.sumExp₂ y) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (by positivity) (by norm_num)).1 hsq
end Core2
section Directions
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
def innerCut (Y : F.Cell) (r : ℕ) (A : ChainChart F) : ChainChart F :=
  Offsets.chartSmul (tentCutoff F Y ((r : ℝ) - 230)) A
def outerCut (Y : F.Cell) (r : ℕ) (A : ChainChart F) : ChainChart F :=
  Offsets.chartSmul (fun j x => 1 - tentCutoff F Y ((r : ℝ) - 230) j x) A
theorem chartMove_innerCut_outerCut (Y : F.Cell) (r : ℕ) (A : ChainChart F) :
    chartMove (innerCut Y r A) (outerCut Y r A) 1 = A := by
  apply chainChart_ext
  · funext x i
    simp only [chartMove, innerCut, outerCut, Offsets.chartSmul, one_smul, ← add_smul]
    simp
  · funext j x i
    simp only [chartMove, innerCut, outerCut, Offsets.chartSmul, one_smul, ← add_smul]
    simp
theorem baseDistance_siteAtOffset_eq (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) {ρ : ℕ}
    (hs : ∀ i, F.extent i = 0 ∨ 2 * ρ + 2 < F.extent i) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius F.blockSide F.top ρ j p) :
    baseDistance (siteAtOffset j Y p) (cellCentre 0 Y) =
      Finset.univ.sup fun i => ((F.blockSide : ℤ) ^ j * p i).natAbs := by
  unfold baseDistance
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : (baseSite (siteAtOffset j Y p) - cellCentre 0 Y : F.Site 0) i =
      ((((F.blockSide : ℤ) ^ j * p i : ℤ)) : ZMod (F.period 0 i)) := by
    unfold siteAtOffset
    rw [baseSite_add j hj, baseSite_cellCentre j hj]
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_small]
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
  have hper : (F.period 0 i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ F.top := by
    simp [BlockFrame.period]
  rcases hs i with h0 | h0
  · left
    simp [BlockFrame.period, h0]
  · right
    rw [hper]
    have h1 := hp i
    have hN : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := pow_pos hLz _
    have h2 : ((2 * ρ + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast h0
    push_cast at h2
    rw [abs_mul, abs_of_pos (pow_pos hLz j)]
    nlinarith
theorem baseDistance_le_of_mem (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) :
    (baseDistance x (cellCentre 0 Y) : ℤ) ≤ (cellSupDist (enclosingCell x) Y + 1 : ℕ) * (F.blockSide : ℤ) ^ F.top := by
  have h := baseDistance_le_cellSupDist_add_one_mul hodd (VariationRates.baseSite_mem_sitesOfCells hodd hj hx) Y
  rw [VariationRates.enclosingCell_baseSite hodd hj hx] at h
  have e : baseDistance (baseSite x) (cellCentre 0 Y) = baseDistance x (cellCentre 0 Y) := by
    simp only [baseDistance, PlaquettesNearCell.baseSite_zero]
  rwa [e] at h
theorem tentCutoff_eq_one_of_near (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) {ρ : ℝ}
    (h : (cellSupDist (enclosingCell x) Y : ℝ) + 2 ≤ ρ) : tentCutoff F Y ρ j x = 1 := by
  refine tentCutoff_eq_one hodd.pos Y ?_
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have h0 : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hodd.pos
    exact pow_pos h0 _
  have h1 := baseDistance_le_of_mem hodd hj hx Y
  have h2 : (baseDistance x (cellCentre 0 Y) : ℝ) ≤
      ((cellSupDist (enclosingCell x) Y : ℝ) + 1) * (F.blockSide : ℝ) ^ F.top := by
    exact_mod_cast h1
  refine h2.trans (mul_le_mul_of_nonneg_right ?_ hN.le)
  linarith
theorem localNorm_outerCut_eq_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (A : ChainChart F) {z : F.Cell}
    (hr : 1000 ≤ r) (hz : cellSupDist z Y ≤ r - 236) :
    localNorm S R (outerCut Y r A) (constOneWeights F) z = 0 := by
  have hfar : ∀ {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}, x ∈ sitesOfCells S j →
      enclosingCell x ∈ cellBall S z 4 → tentCutoff F Y ((r : ℝ) - 230) j x = 1 := by
    intro j hj x hx hc
    refine tentCutoff_eq_one_of_near hodd hj hx Y ?_
    have h1 : cellSupDist z (enclosingCell x) ≤ 4 := (Finset.mem_filter.1 hc).2
    have h2 := CoordinateSeminorms.cellSupDist_triangle (enclosingCell x) z Y
    rw [CoordinateSeminorms.cellSupDist_comm (enclosingCell x) z] at h2
    have h3 : cellSupDist (enclosingCell x) Y + 232 ≤ r := by omega
    have h4 : (cellSupDist (enclosingCell x) Y : ℝ) + 232 ≤ r := by exact_mod_cast h3
    linarith
  have h0 := localNorm_congr (S := S) hamb hodd R (A := outerCut Y r A) (A' := zeroChart F)
    (constOneWeights F) z (fun b hb => by
      obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
      show (1 - tentCutoff F Y ((r : ℝ) - 230) 0 b.1) • _ = 0
      rw [hfar (Nat.zero_le _) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, sub_self, zero_smul])
    (fun j hj b hb => by
      obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
      show (1 - tentCutoff F Y ((r : ℝ) - 230) (j + 1) b.1) • _ = 0
      rw [hfar (by omega) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, sub_self, zero_smul])
  rw [h0, localNorm_zeroChart]
theorem supportedNear_innerCut (hodd : Odd F.blockSide) (hr : 1000 ≤ r) (A : ChainChart F) :
    SupportedNear S Y (r - 202 - 10) (innerCut Y r A) where
  fine b hb hd := by
    have hx : b.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    show tentCutoff F Y ((r : ℝ) - 230) 0 b.1 • _ = 0
    rw [tentCutoff_eq_zero_of_far hodd (Nat.zero_le _) hx Y ?_, zero_smul]
    have h1 : r - 211 ≤ cellSupDist (enclosingCell b.1) Y := by omega
    have h2 : r ≤ cellSupDist (enclosingCell b.1) Y + 211 := by omega
    have h3 : (r : ℝ) ≤ (cellSupDist (enclosingCell b.1) Y : ℝ) + 211 := by exact_mod_cast h2
    linarith
  coarse j hj b hb hd := by
    have hx : b.1 ∈ sitesOfCells S (j + 1) := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    show tentCutoff F Y ((r : ℝ) - 230) (j + 1) b.1 • _ = 0
    rw [tentCutoff_eq_zero_of_far hodd (by omega) hx Y ?_, zero_smul]
    have h2 : r ≤ cellSupDist (enclosingCell b.1) Y + 211 := by omega
    have h3 : (r : ℝ) ≤ (cellSupDist (enclosingCell b.1) Y : ℝ) + 211 := by exact_mod_cast h2
    linarith
theorem tentCutoff_translate_eq
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf') {j : ℕ}
    (hj : j ≤ F.top) {p : Fin 4 → ℤ} (hp : WithinCellRadius F.blockSide F.top (r - 202) j p) :
    tentCutoff F Y ((r : ℝ) - 230) j (siteAtOffset j Y p) =
      tentCutoff F' Y' ((r : ℝ) - 230) j (siteAtOffset j Y' p) := by
  have hr := t.radius_ge
  have hL := t.odd_blockSide.pos
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [t.depth_eq]
  have hs : ∀ i, F.extent i = 0 ∨ 2 * (r - 202) + 2 < F.extent i := fun i =>
    (t.extent_large i).imp id fun e => by omega
  have hs' : ∀ i, F'.extent i = 0 ∨ 2 * (r - 202) + 2 < F'.extent i := fun i =>
    (t.extent_large' i).imp id fun e => by omega
  have hp' : WithinCellRadius F'.blockSide F'.top (r - 202) j p := by
    rw [t.blockSide_eq, hn]
    exact hp
  have e1 := baseDistance_siteAtOffset_eq hL hj Y hs hp
  have e2 := baseDistance_siteAtOffset_eq (t.blockSide_eq ▸ hL) (hn ▸ hj) Y' hs' hp'
  unfold tentCutoff
  rw [e1, e2, t.blockSide_eq, hn]
theorem innerCut_agree
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    (A : ChainChart F) :
    ChartsAgreeAtOffsets Y Y' (r - 202) (innerCut Y r A) (innerCut Y' r (chartTranslate Y' Y A)) := by
  have hr := t.radius_ge
  have hL := t.odd_blockSide.pos
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [t.depth_eq]
  have hs' : ∀ i, F'.extent i = 0 ∨ 2 * (r - 202) + 2 < F'.extent i := fun i =>
    (t.extent_large' i).imp id fun e => by omega
  have hr' : ∀ {j : ℕ} {p : Fin 4 → ℤ}, WithinCellRadius F.blockSide F.top (r - 202) j p →
      WithinCellRadius F'.blockSide F'.top (r - 202) j p := by
    intro j p hp
    rw [t.blockSide_eq, hn]
    exact hp
  refine ⟨fun p i hp => ?_, fun j p i hj hp => ?_⟩
  · show tentCutoff F Y ((r : ℝ) - 230) 0 (siteAtOffset 0 Y p) • A.fine (siteAtOffset 0 Y p) i =
      tentCutoff F' Y' ((r : ℝ) - 230) 0 (siteAtOffset 0 Y' p) • A.fine (translateSite Y' Y (siteAtOffset 0 Y' p)) i
    rw [translateSite_siteAtOffset (t.blockSide_eq ▸ hL) (Nat.zero_le _) Y' Y hs' (hr' hp),
      tentCutoff_translate_eq t (Nat.zero_le _) hp]
  · have hj' : j + 1 ≤ F.top := by omega
    show tentCutoff F Y ((r : ℝ) - 230) (j + 1) (siteAtOffset (j + 1) Y p) •
        A.coarse j (siteAtOffset (j + 1) Y p) i =
      tentCutoff F' Y' ((r : ℝ) - 230) (j + 1) (siteAtOffset (j + 1) Y' p) •
        A.coarse j (translateSite Y' Y (siteAtOffset (j + 1) Y' p)) i
    rw [translateSite_siteAtOffset (t.blockSide_eq ▸ hL) (hn ▸ hj') Y' Y hs' (hr' hp), tentCutoff_translate_eq t hj' hp]
theorem complexFirstVariation_innerCut_eq_zero
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ < r') (A : ChainChart F) :
    complexFirstVariation a S (referenceFieldChain S V)
      ⟨cutTranslate Y Y' r (Wf' ζ).re, cutTranslate Y Y' r (Wf' ζ).im⟩
      (complexTwistedTop (offsetBonds Y h) X ζ V) (innerCut Y r A) = 0 := by
  have hodd' : Odd F'.blockSide := t.blockSide_eq ▸ t.odd_blockSide
  have hr'' := supportedNear_innerCut (S := S') (Y := Y') hodd' t.radius_ge (chartTranslate Y' Y A)
  rw [t.firstVariation _ (Wf' ζ) _ (complexTwistedTop (offsetBonds Y' h) X ζ V') _
    (innerCut Y' r (chartTranslate Y' Y A))
    (cutTranslate_agree t _) (cutTranslate_agree t _) (fun p i hp => t.top_agree ζ p i hp) (innerCut_agree t A)
    (supportedNear_innerCut t.odd_blockSide t.radius_ge A) hr'']
  exact t.critical' ζ hζ _
theorem sum_localNorm_le_of_vanish {δ Cd₁ : ℝ} {R : ℕ} (hdel : 0 ≤ δ) (Rc : F.FieldChain) (B : ChainChart F)
    (Y : F.Cell)
    (hzero : ∀ z ∈ S, cellSupDist z Y ≤ R → localNorm S Rc B (constOneWeights F) z = 0)
    (hCd : ∑ z ∈ S, Real.exp (-δ * cellSupDist z Y) ≤ Cd₁) :
    ∑ z ∈ S, localNorm S Rc B (constOneWeights F) z ≤ Real.exp (3 * δ) * Real.sqrt Cd₁ * Real.exp (-δ * R / 2) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S Rc B (classWeight F (fun x => δ * (cellSupDist x Y : ℝ)) 0 0) := by
  classical
  set g := classWeight F (fun x => δ * (cellSupDist x Y : ℝ)) 0 0 with hg
  set aw : F.Cell → ℝ := fun z =>
    if R < cellSupDist z Y then Real.exp (3 * δ - δ * (cellSupDist z Y : ℝ)) else 0 with haw
  have hle : ∀ z ∈ S, localNorm S Rc B (constOneWeights F) z ≤ aw z * localNorm S Rc B g z := by
    intro z hz
    simp only [haw]
    split_ifs with hd
    · exact localNorm_le_growing δ hdel Rc B Y z
    · rw [hzero z hz (by omega), zero_mul]
  refine (Finset.sum_le_sum hle).trans ?_
  refine (Real.sum_mul_le_sqrt_mul_sqrt S aw fun z => localNorm S Rc B g z).trans ?_
  have hsa : ∑ z ∈ S, aw z ^ 2 ≤ (Real.exp (3 * δ) * Real.exp (-δ * R / 2)) ^ 2 * Cd₁ := by
    have hterm : ∀ z ∈ S, aw z ^ 2 ≤ (Real.exp (3 * δ) * Real.exp (-δ * R / 2)) ^ 2 *
        Real.exp (-δ * cellSupDist z Y) := by
      intro z _
      simp only [haw]
      split_ifs with hd
      · have hd' : (R : ℝ) ≤ cellSupDist z Y := by
          have : R ≤ cellSupDist z Y := hd.le
          exact_mod_cast this
        rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hd' hdel
        push_cast
        nlinarith
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hCd (by positivity)
  have h1 : Real.sqrt (∑ z ∈ S, aw z ^ 2) ≤ Real.exp (3 * δ) * Real.sqrt Cd₁ * Real.exp (-δ * R / 2) := by
    refine (Real.sqrt_le_sqrt hsa).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  have h2 : Real.sqrt (∑ z ∈ S, localNorm S Rc B g z ^ 2) = _root_.YangMills.Construction.BlockAverages.weightedNorm S Rc B g := rfl
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
end Directions
section Core3
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
def nearConst (δ C₀ : ℝ) : ℝ := Real.exp (3 * δ) * C₀
def gaugeDiffConst (Kg δ C₀ : ℝ) : ℝ := Kg * 45 ^ 4 * (11700 * nearConst δ C₀)
def supConst (Kp Kg Cd₂ δ C₀ : ℝ) : ℝ :=
  Kp * (gaugeDiffConst Kg δ C₀ * Real.sqrt Cd₂) + Real.exp (3 * δ) * (11700 * nearConst δ C₀) * Real.sqrt Cd₂
def formConst (Kp Kg Cd₁ δ C₀ : ℝ) : ℝ := Kp * (gaugeDiffConst Kg δ C₀ * Real.sqrt Cd₁)
def cutConst : ℝ := Real.exp 1 * (20737 * 6561)
def dualConst (Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL : ℝ) : ℝ :=
  (2 * formConst Kp Kg Cd₁ δ C₀ * (CT + C * (3 * rL))) * cutConst +
    Cl * (1 + 2 * Real.exp (3 * δ) * supConst Kp Kg Cd₂ δ C₀) * (Real.exp (3 * δ) * Real.sqrt Cd₁) * cutConst
def finalConst (Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL : ℝ) : ℝ :=
  Real.exp (6 * δ) * (C₀ * dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL + formConst Kp Kg Cd₁ δ C₀)
theorem chartMove_baseOnly_eq (A : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    chartMove (chartMove A (baseOnlyChart v) (-1)) A (-1) = chartMove (zeroChart F) (baseOnlyChart v) (-1) := by
  apply chainChart_ext
  · funext x i
    simp only [chartMove, zeroChart, baseOnlyChart, neg_one_smul_imag]
    abel
  · funext j x i
    simp only [chartMove, zeroChart, baseOnlyChart, neg_one_smul_imag]
    abel
theorem chartMove_split (W A : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    chartMove W A (-1) = chartMove (chartMove W (chartMove A (baseOnlyChart v) (-1)) (-1)) (baseOnlyChart v) (-1) := by
  apply chainChart_ext
  · funext x i
    simp only [chartMove, baseOnlyChart, neg_one_smul_imag]
    abel
  · funext j x i
    simp only [chartMove, baseOnlyChart, neg_one_smul_imag]
    abel
theorem localNorm_diff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hdel : 0 ≤ δ) (hr : 1000 ≤ r)
    (Rc : F.FieldChain)
    (W U : ChainChart F) (A' : ChainChart F') (v : F.Site 0 → Fin 4 → imaginaryQuaternions) {z : F.Cell}
    (hz : cellSupDist z Y ≤ 3) (hU : U = chartMove (cutTranslate Y Y' r A') (baseOnlyChart v) (-1)) {P Q : ℝ}
    (h1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S Rc (chartMove W U (-1)) (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤ P)
    (h2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S Rc (baseOnlyChart v) (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤ Q) :
    localNorm S Rc (chartMove W (chartTranslate Y Y' A') (-1)) (constOneWeights F) z ≤ Real.exp (6 * δ) * (P + Q) := by
  have hone : ∀ {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}, x ∈ sitesOfCells S j →
      enclosingCell x ∈ cellBall S z 4 → tentCutoff F Y ((r : ℝ) - 200) j x = 1 := by
    intro j hj x hx hc
    refine tentCutoff_eq_one_of_near hodd hj hx Y ?_
    have h3 : cellSupDist z (enclosingCell x) ≤ 4 := (Finset.mem_filter.1 hc).2
    have h4 := CoordinateSeminorms.cellSupDist_triangle (enclosingCell x) z Y
    rw [CoordinateSeminorms.cellSupDist_comm (enclosingCell x) z] at h4
    have h5 : cellSupDist (enclosingCell x) Y + 202 ≤ r := by omega
    have h6 : (cellSupDist (enclosingCell x) Y : ℝ) + 202 ≤ r := by exact_mod_cast h5
    linarith
  have e1 : localNorm S Rc (chartMove W (chartTranslate Y Y' A') (-1)) (constOneWeights F) z =
      localNorm S Rc (chartMove W (cutTranslate Y Y' r A') (-1)) (constOneWeights F) z := by
    refine localNorm_congr hamb hodd Rc _ z (fun b hb => ?_) (fun j hj b hb => ?_)
    · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
      show _ + (-1 : ℝ) • (chartTranslate Y Y' A').fine b.1 b.2 =
        _ + (-1 : ℝ) • (tentCutoff F Y ((r : ℝ) - 200) 0 b.1 • (chartTranslate Y Y' A').fine b.1 b.2)
      rw [hone (Nat.zero_le _) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, one_smul]
    · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hb
      show _ + (-1 : ℝ) • (chartTranslate Y Y' A').coarse j b.1 b.2 =
        _ + (-1 : ℝ) • (tentCutoff F Y ((r : ℝ) - 200) (j + 1) b.1 • (chartTranslate Y Y' A').coarse j b.1 b.2)
      rw [hone (by omega) (Finset.mem_product.1 (Finset.mem_filter.1 a1).1).1 a2, one_smul]
  rw [e1, chartMove_split W (cutTranslate Y Y' r A') v, ← hU]
  have h3 := localNorm_chartMove_le S Rc (chartMove W U (-1)) (baseOnlyChart v) (-1) (constOneWeights F)
    (fun _ _ => zero_le_one) z
  simp only [abs_neg, abs_one, one_mul] at h3
  refine h3.trans ?_
  have hd : (cellSupDist z Y : ℝ) ≤ 3 := by exact_mod_cast hz
  have hexp : Real.exp (3 * δ + δ * (cellSupDist z Y : ℝ)) ≤ Real.exp (6 * δ) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hd hdel
    linarith
  have hb : ∀ B : ChainChart F, localNorm S Rc B (constOneWeights F) z ≤ Real.exp (6 * δ) *
      _root_.YangMills.Construction.BlockAverages.weightedNorm S Rc B (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) := fun B =>
    (localNorm_le_decay δ hdel Rc B Y z).trans (mul_le_mul_of_nonneg_right hexp (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _))
  have e2 := (hb _).trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
  have e3 := (hb (baseOnlyChart v)).trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  rw [mul_add]
  exact add_le_add e2 e3
end Core3
section Core4
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
structure IsProjectedCut (Kp Kg Cd₁ Cd₂ δ C₀ κ E : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (Y : F.Cell)
    (Y' : F'.Cell) (r : ℕ) (A' : ChainChart F') (U : ChainChart F)
    (v : F.Site 0 → Fin 4 → imaginaryQuaternions) : Prop where
  eq_chartMove : U = chartMove (cutTranslate Y Y' r A') (baseOnlyChart v) (-1)
  mem_slice : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine
  supWeightedNorm_le : supWeightedNorm S δ (referenceFieldChain S V) U ≤ supConst Kp Kg Cd₂ δ C₀ * κ
  supWeightedNorm_cut_le : supWeightedNorm S δ (referenceFieldChain S V) (cutTranslate Y Y' r A') ≤
    supConst Kp Kg Cd₂ δ C₀ * κ
  weightedNorm_le : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (baseOnlyChart v)
    (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤ formConst Kp Kg Cd₁ δ C₀ * κ * E
theorem exists_isProjectedCut
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {A' : ChainChart F'} (hsl : GaugeMap.InGaugeSlice S' V' (referenceFieldChain S' V' 0) A'.fine) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hM : ∀ y, localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ nearConst δ C₀ * κ) :
    ∃ (U : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions),
      IsProjectedCut Kp Kg Cd₁ Cd₂ δ C₀ κ (Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2)) S V Y Y' r A' U v := by
  have hC₀ := t.C₀_pos
  have hKp := t.Kp_pos
  have hKg := t.Kg_pos
  have hM0 : 0 ≤ nearConst δ C₀ := by
    unfold nearConst
    positivity
  have hM00 : 0 ≤ nearConst δ C₀ * κ := mul_nonneg hM0 hκ
  obtain ⟨v, hs, hy, hY⟩ := exists_slice_projection t hsl hM00 hM
  have hcut := fun y => _root_.YangMills.Construction.BlockAverages.AgreeingPairs.weightedNorm_cutTranslate_le t hM00 hM y
  have hpos : 0 ≤ Kp * (Kg * 45 ^ 4 * (11700 * (nearConst δ C₀ * κ)) * Real.sqrt Cd₂) := by positivity
  have hNs : supConst Kp Kg Cd₂ δ C₀ * κ = Kp * (Kg * 45 ^ 4 * (11700 * (nearConst δ C₀ * κ)) * Real.sqrt Cd₂) +
      Real.exp (3 * δ) * (11700 * (nearConst δ C₀ * κ)) * Real.sqrt Cd₂ := by
    simp only [supConst, gaugeDiffConst]
    ring
  refine ⟨chartMove (cutTranslate Y Y' r A') (baseOnlyChart v) (-1), v, ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
  · have e : (chartMove (cutTranslate Y Y' r A') (baseOnlyChart v) (-1)).fine =
        fun x i => (cutTranslate Y Y' r A').fine x i - v x i := by
      funext x i
      simp only [chartMove, baseOnlyChart, neg_one_smul_imag, sub_eq_add_neg]
    rw [e]
    exact hs
  · refine supWeightedNorm_le S δ _ _ _ fun y => ?_
    have h1 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_chartMove_le S (referenceFieldChain S V) (cutTranslate Y Y' r A') (baseOnlyChart v) (-1)
      (classWeight F (fun x => -δ * (cellSupDist x y : ℝ)) 0 0)
      (fun j x => by rw [CoordinateCutoffs.classWeight_zero]; exact (Real.exp_pos _).le)
    simp only [abs_neg, abs_one, one_mul] at h1
    refine h1.trans ?_
    rw [hNs]
    linarith [hcut y, hy y]
  · refine supWeightedNorm_le S δ _ _ _ fun y => ?_
    refine (hcut y).trans ?_
    rw [hNs]
    linarith
  · refine hY.trans (le_of_eq ?_)
    simp only [formConst, gaugeDiffConst]
    ring
theorem norm_complexFirstVariation_le
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ < r') {U₁ U₂ : ChainChart F}
    {v₁ v₂ : F.Site 0 → Fin 4 → imaginaryQuaternions}
    {κ E : ℝ} (hκ0 : 0 ≤ κ) (hE0 : 0 ≤ E) (hκ : κ = s + ∑ l, ‖ζ l‖)
    (hE : E = Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2))
    (p₁ : IsProjectedCut Kp Kg Cd₁ Cd₂ δ C₀ κ E S V Y Y' r (Wf' ζ).re U₁ v₁)
    (p₂ : IsProjectedCut Kp Kg Cd₁ Cd₂ δ C₀ κ E S V Y Y' r (Wf' ζ).im U₂ v₂)
    (hsz : 2 * (supConst Kp Kg Cd₂ δ C₀ * κ) ≤ rL) (A : ChainChart F) :
    ‖complexFirstVariation a S (referenceFieldChain S V) ⟨U₁, U₂⟩ (complexTwistedTop (offsetBonds Y h) X ζ V) A‖ ≤
      (dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E) *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0)) := by
  have hdel := t.delta_pos
  have hC := t.C_pos
  have hCT := t.CT_pos
  have hCl := t.Cl_pos
  have hodd := t.odd_blockSide
  have hamb := t.ambient
  have hrL : 0 ≤ rL := t.r'_pos.le.trans t.r'_le
  set w := classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0 with hw
  set g := classWeight F (fun x => δ * (cellSupDist x Y : ℝ)) 0 0 with hg
  have hwg : invertedWeights w = g := by
    rw [hw, invertedWeights_classWeight, hg]
    congr 1
    funext x
    ring
  have hlipw : ∀ y y', |(-δ * (cellSupDist y Y : ℝ)) - (-δ * (cellSupDist y' Y : ℝ))| ≤ δ * cellSupDist y y' :=
    fun y y' => abs_neg_mul_cellSupDist_sub_le δ hdel.le Y y y'
  have hlipg : ∀ y y', |(δ * (cellSupDist y Y : ℝ)) - (δ * (cellSupDist y' Y : ℝ))| ≤ δ * cellSupDist y y' :=
    fun y y' => abs_mul_cellSupDist_sub_le δ hdel.le Y y y'
  set Q := _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A g with hQ
  rw [hwg]
  set T := complexTwistedTop (offsetBonds Y h) X ζ V with hT
  set Ns := supConst Kp Kg Cd₂ δ C₀ * κ with hNs
  set Nf := formConst Kp Kg Cd₁ δ C₀ * κ * E with hNf
  have hNf0 : 0 ≤ Nf := (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _).trans p₁.weightedNorm_le
  have hζr : ∑ l, ‖ζ l‖ ≤ rL := hζ.le.trans t.r'_le
  have hζc : ∑ l, ‖ζ l‖ ≤ c := hζr.trans t.rL_le
  set W2 : ComplexChainChart F := ⟨U₁, U₂⟩ with hW2
  set Wc : ComplexChainChart F := ⟨cutTranslate Y Y' r (Wf' ζ).re, cutTranslate Y Y' r (Wf' ζ).im⟩ with hWc
  have hsup2 : complexSupWeightedNorm S δ (referenceFieldChain S V) W2 ≤ rL := by
    show supWeightedNorm S δ (referenceFieldChain S V) U₁ + supWeightedNorm S δ (referenceFieldChain S V) U₂ ≤ rL
    have := add_le_add p₁.supWeightedNorm_le p₂.supWeightedNorm_le
    linarith
  have hsupc : complexSupWeightedNorm S δ (referenceFieldChain S V) Wc ≤ rL := by
    show supWeightedNorm S δ (referenceFieldChain S V) (cutTranslate Y Y' r (Wf' ζ).re) +
      supWeightedNorm S δ (referenceFieldChain S V) (cutTranslate Y Y' r (Wf' ζ).im) ≤ rL
    have := add_le_add p₁.supWeightedNorm_cut_le p₂.supWeightedNorm_cut_le
    linarith
  have hsum := complexFirstVariation_add t.twistedBounds (hsup2.trans t.rL_le) hζc (innerCut Y r A) (outerCut Y r A)
  rw [chartMove_innerCut_outerCut] at hsum
  rw [hsum]
  have hq1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (innerCut Y r A) g ≤ cutConst * Q :=
    _root_.YangMills.Construction.CoordinateCutoffs.weightedNorm_chartSmul_le hamb hodd S _ (tentCutoff_isCutoff hodd.pos Y _) A _ 0 hdel.le t.delta_le hlipg
  have hq2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (outerCut Y r A) g ≤ cutConst * Q :=
    _root_.YangMills.Construction.CoordinateCutoffs.weightedNorm_chartSmul_le hamb hodd S _ (IsCutoff.one_sub (tentCutoff_isCutoff hodd.pos Y _)) A _ 0 hdel.le
      t.delta_le hlipg
  have hin := complexFirstVariation_innerCut_eq_zero t hζ A
  have hlip := t.twistedBounds.lipschitz W2 Wc ζ (hsup2.trans t.rL_le) (hsupc.trans t.rL_le) hζc _ 0 0
    (Or.inr (Or.inl rfl)) hlipw (innerCut Y r A)
  rw [hin, sub_zero, hwg] at hlip
  have hD1 : chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1) = chartMove (zeroChart F) (baseOnlyChart v₁) (-1) := by
    rw [p₁.eq_chartMove]
    exact chartMove_baseOnly_eq _ _
  have hD2 : chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1) = chartMove (zeroChart F) (baseOnlyChart v₂) (-1) := by
    rw [p₂.eq_chartMove]
    exact chartMove_baseOnly_eq _ _
  have hwpos : ∀ j (x : F.Site j), 0 ≤ w j x := fun j x => by
    rw [hw, CoordinateCutoffs.classWeight_zero]
    exact (Real.exp_pos _).le
  have hN1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1)) w ≤ Nf := by
    rw [hD1, _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_smul S _ _ _ _ hwpos, abs_neg, abs_one, one_mul]
    exact p₁.weightedNorm_le
  have hN2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1)) w ≤ Nf := by
    rw [hD2, _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_smul S _ _ _ _ hwpos, abs_neg, abs_one, one_mul]
    exact p₂.weightedNorm_le
  have hcO : complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W2 Wc) w ≤ 2 * Nf := by
    show _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1)) w +
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1)) w ≤ 2 * Nf
    linarith
  have hcO0 : 0 ≤ complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W2 Wc) w :=
    add_nonneg (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
  set qi := _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (innerCut Y r A) g with hqi
  have hqi0 : 0 ≤ qi := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _
  have hform : ‖complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W2 Wc) (innerCut Y r A)‖ ≤
      CT * (2 * Nf) * qi := by
    have f1 := t.taylorBounds.hessian_le _ 0 0 ⟨Or.inr (Or.inl rfl), hlipw⟩
      (chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1)) (innerCut Y r A)
    have f2 := t.taylorBounds.hessian_le _ 0 0 ⟨Or.inr (Or.inl rfl), hlipw⟩
      (chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1)) (innerCut Y r A)
    rw [hwg] at f1 f2
    have e : complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W2 Wc) (innerCut Y r A) =
        ((referenceSecondDeriv a S (referenceFieldChain S V) V (chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1))
          (innerCut Y r A) : ℝ) : ℂ) +
        Complex.I * ((referenceSecondDeriv a S (referenceFieldChain S V) V
          (chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1)) (innerCut Y r A) : ℝ) : ℂ) := rfl
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have g1 : CT * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₁ (cutTranslate Y Y' r (Wf' ζ).re) (-1)) w * qi ≤
        CT * Nf * qi :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1 hCT.le) hqi0
    have g2 : CT * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove U₂ (cutTranslate Y Y' r (Wf' ζ).im) (-1)) w * qi ≤
        CT * Nf * qi :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 hCT.le) hqi0
    have e2 : CT * (2 * Nf) * qi = CT * Nf * qi + CT * Nf * qi := by ring
    rw [e2]
    exact add_le_add (f1.trans g1) (f2.trans g2)
  have hX : complexSupWeightedNorm S δ (referenceFieldChain S V) W2 + complexSupWeightedNorm S δ (referenceFieldChain S V) Wc +
      ∑ l, ‖ζ l‖ ≤ 3 * rL := by
    linarith
  have hinner : ‖complexFirstVariation a S (referenceFieldChain S V) W2 T (innerCut Y r A)‖ ≤
      (2 * Nf * (CT + C * (3 * rL))) * (cutConst * Q) := by
    have e : complexFirstVariation a S (referenceFieldChain S V) W2 T (innerCut Y r A) =
        (complexFirstVariation a S (referenceFieldChain S V) W2 T (innerCut Y r A) -
          complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W2 Wc) (innerCut Y r A)) +
        complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W2 Wc) (innerCut Y r A) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have l2 : C * (complexSupWeightedNorm S δ (referenceFieldChain S V) W2 +
        complexSupWeightedNorm S δ (referenceFieldChain S V) Wc + ∑ l, ‖ζ l‖) *
        complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W2 Wc) w * qi ≤
        C * (3 * rL) * (2 * Nf) * qi := by
      refine mul_le_mul_of_nonneg_right ?_ hqi0
      exact mul_le_mul (mul_le_mul_of_nonneg_left hX hC.le) hcO hcO0 (by positivity)
    have l4 : 2 * Nf * (CT + C * (3 * rL)) * qi ≤ 2 * Nf * (CT + C * (3 * rL)) * (cutConst * Q) :=
      mul_le_mul_of_nonneg_left hq1 (by positivity)
    have e2 : 2 * Nf * (CT + C * (3 * rL)) * qi = C * (3 * rL) * (2 * Nf) * qi + CT * (2 * Nf) * qi := by ring
    linarith
  have hnear2 : ∀ z, localNorm S (referenceFieldChain S V) U₁ (constOneWeights F) z ≤ Real.exp (3 * δ) * Ns := fun z =>
    (localNorm_le_supWeightedNorm hodd.pos δ hdel.le _ U₁ z).trans
      (mul_le_mul_of_nonneg_left p₁.supWeightedNorm_le (Real.exp_pos _).le)
  have hnear3 : ∀ z, localNorm S (referenceFieldChain S V) U₂ (constOneWeights F) z ≤ Real.exp (3 * δ) * Ns := fun z =>
    (localNorm_le_supWeightedNorm hodd.pos δ hdel.le _ U₂ z).trans
      (mul_le_mul_of_nonneg_left p₂.supWeightedNorm_le (Real.exp_pos _).le)
  set Sz := (1 + 2 * Real.exp (3 * δ) * supConst Kp Kg Cd₂ δ C₀) * κ with hSz
  have hsize : ∀ z, firstVariationCellWeight S (referenceFieldChain S V) s W2 (offsetBonds Y h) ζ z ≤ Sz := by
    intro z
    have h1 : ∑ l, (if cellSupDist z (offsetBonds Y h l).1 ≤ 1 then ‖ζ l‖ else 0) ≤ ∑ l, ‖ζ l‖ :=
      Finset.sum_le_sum fun l _ => by
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _
    show s + localNorm S (referenceFieldChain S V) U₁ (constOneWeights F) z +
      localNorm S (referenceFieldChain S V) U₂ (constOneWeights F) z + _ ≤ Sz
    have e : Sz = (s + ∑ l, ‖ζ l‖) + 2 * Real.exp (3 * δ) * Ns := by
      rw [hSz, hNs, hκ]
      ring
    rw [e]
    linarith [hnear2 z, hnear3 z]
  have hSz0 : 0 ≤ Sz := by
    have hn : 0 ≤ supConst Kp Kg Cd₂ δ C₀ := by
      unfold supConst gaugeDiffConst nearConst
      have := t.Kp_pos
      have := t.Kg_pos
      have := t.C₀_pos
      positivity
    positivity
  have hfs := sum_localNorm_le_of_vanish (S := S) (R := r - 236) hdel.le (referenceFieldChain S V) (outerCut Y r A) Y
    (fun z _ hz => localNorm_outerCut_eq_zero hamb hodd _ A t.radius_ge hz) (t.sumExp₁ Y)
  rw [← hE] at hfs
  have houter : ‖complexFirstVariation a S (referenceFieldChain S V) W2 T (outerCut Y r A)‖ ≤
      Cl * Sz * (Real.exp (3 * δ) * Real.sqrt Cd₁ * E * (cutConst * Q)) := by
    refine (t.localVariation W2 ζ _ hsup2 hζr).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCl.le
    have h1 : ∑ z ∈ S, firstVariationCellWeight S (referenceFieldChain S V) s W2 (offsetBonds Y h) ζ z *
        localNorm S (referenceFieldChain S V) (outerCut Y r A) (constOneWeights F) z ≤
        Sz * ∑ z ∈ S, localNorm S (referenceFieldChain S V) (outerCut Y r A) (constOneWeights F) z := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hsize z) (localNorm_nonneg _ _ _ _ _)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hSz0)
    exact hfs.trans (mul_le_mul_of_nonneg_left hq2 (by positivity))
  refine (norm_add_le _ _).trans ((add_le_add hinner houter).trans (le_of_eq ?_))
  simp only [dualConst, hNf, hSz]
  ring
end Core4
section Core5
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
set_option maxHeartbeats 800000 in
theorem localNorm_diff_le_of_large
    (t : ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ < r') (hsz : 2 * (supConst Kp Kg Cd₂ δ C₀ * (s + ∑ l, ‖ζ l‖)) ≤ rL)
    {z : F.Cell} (hz : cellSupDist z Y ≤ 3) :
    localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1))
        (constOneWeights F) z ≤
        finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * (s + ∑ l, ‖ζ l‖) * Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2) ∧
      localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1))
        (constOneWeights F) z ≤
        finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * (s + ∑ l, ‖ζ l‖) * Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2) := by
  have hdel := t.delta_pos
  have hs := t.s_pos
  have hC₀ := t.C₀_pos
  set κ := s + ∑ l, ‖ζ l‖ with hκ
  have hκ0 : 0 ≤ κ := add_nonneg hs.le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  set E := Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hL' : 0 < F'.blockSide := t.blockSide_eq.symm ▸ t.odd_blockSide.pos
  have hsz' := t.family'.norm_le ζ hζ
  have hnear : ∀ (A' : ChainChart F'), supWeightedNorm S' δ (referenceFieldChain S' V') A' ≤
      complexSupWeightedNorm S' δ (referenceFieldChain S' V') (Wf' ζ) → ∀ y,
      localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ nearConst δ C₀ * κ := by
    intro A' hA y
    refine (localNorm_le_supWeightedNorm hL' δ hdel.le _ A' y).trans ?_
    have := mul_le_mul_of_nonneg_left (hA.trans hsz') (Real.exp_pos (3 * δ)).le
    refine this.trans (le_of_eq ?_)
    simp only [nearConst]
    ring
  have h1 := hnear (Wf' ζ).re (le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _))
  have h2 := hnear (Wf' ζ).im (le_add_of_nonneg_left (supWeightedNorm_nonneg _ _ _ _))
  obtain ⟨U₁, v₁, p₁⟩ := exists_isProjectedCut t (t.family'.mem_slice ζ hζ).1 hκ0 h1
  obtain ⟨U₂, v₂, p₂⟩ := exists_isProjectedCut t (t.family'.mem_slice ζ hζ).2 hκ0 h2
  have hlipw : ∀ y y', |(-δ * (cellSupDist y Y : ℝ)) - (-δ * (cellSupDist y' Y : ℝ))| ≤ δ * cellSupDist y y' :=
    fun y y' => abs_neg_mul_cellSupDist_sub_le δ hdel.le Y y y'
  have hsup2 : complexSupWeightedNorm S δ (referenceFieldChain S V) (⟨U₁, U₂⟩ : ComplexChainChart F) ≤ rL := by
    show supWeightedNorm S δ (referenceFieldChain S V) U₁ + supWeightedNorm S δ (referenceFieldChain S V) U₂ ≤ rL
    have := add_le_add p₁.supWeightedNorm_le p₂.supWeightedNorm_le
    linarith
  have hbound := norm_complexFirstVariation_le (C := C) (CT := CT) (Cl := Cl) t hζ hκ0 hE0 hκ hE p₁ p₂ hsz
  have hβ0 : 0 ≤ dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E := by
    have hBe : 0 ≤ dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL := by
      have := t.Kp_pos
      have := t.Kg_pos
      have := t.CT_pos
      have := t.C_pos
      have := t.Cl_pos
      have hrL : 0 ≤ rL := t.r'_pos.le.trans t.r'_le
      unfold dualConst formConst supConst gaugeDiffConst nearConst cutConst
      positivity
    positivity
  have hst := t.family.stable _ 0 0 (Or.inr (Or.inl rfl)) hlipw ζ (Wf ζ) ⟨U₁, U₂⟩ _ hζ hβ0
    (t.family.mem_slice ζ hζ).1 (t.family.mem_slice ζ hζ).2 p₁.mem_slice p₂.mem_slice (t.family.small ζ hζ) hsup2
    (fun A hA => by
      rw [t.family.critical ζ hζ A hA, zero_sub, norm_neg]
      exact hbound A)
  have hst1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf ζ).re U₁ (-1))
      (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤
        C₀ * (dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E) :=
    le_trans (le_add_of_nonneg_right (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)) hst
  have hst2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf ζ).im U₂ (-1))
      (classWeight F (fun x => -δ * (cellSupDist x Y : ℝ)) 0 0) ≤
        C₀ * (dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E) :=
    le_trans (le_add_of_nonneg_left (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)) hst
  have e : Real.exp (6 * δ) * (C₀ * (dualConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E) +
      formConst Kp Kg Cd₁ δ C₀ * κ * E) =
      finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * E := by
    simp only [finalConst]
    ring
  refine ⟨?_, ?_⟩
  · rw [← e]
    exact localNorm_diff_le t.ambient t.odd_blockSide hdel.le t.radius_ge _ _ _ _ v₁ hz p₁.eq_chartMove hst1
      p₁.weightedNorm_le
  · rw [← e]
    exact localNorm_diff_le t.ambient t.odd_blockSide hdel.le t.radius_ge _ _ _ _ v₂ hz p₂.eq_chartMove hst2
      p₂.weightedNorm_le
end Core5
section Readers
variable {a θ δ C₀ rL r' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {k : ℕ}
  {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
def realFamilyChart (Wf : (Fin k → ℂ) → ComplexChainChart F) (x : Fin k → ℝ) : ChainChart F := (Wf (ofRealVec x)).re
theorem linear_chartValues_real (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf)
    (ℓ : ChartValues S →ₗ[ℝ] ℝ) {x : Fin k → ℝ} (hx : ∑ l, |x l| < r') :
    (ℓ (chartValues S (Wf fun l => (x l : ℂ)).re) : ℂ) +
        Complex.I * (ℓ (chartValues S (Wf fun l => (x l : ℂ)).im) : ℂ) =
      (ℓ (chartValues S (realFamilyChart Wf x)) : ℂ) := by
  have e : chartValues S (Wf fun l => (x l : ℂ)).im = 0 := (chartValues_congr (hfam.real x hx)).trans rfl
  rw [e, map_zero]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rfl
theorem analyticAt_linear_chartValues (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hr' : 0 < r')
    (ℓ : ChartValues S →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun x : Fin k → ℝ => ℓ (chartValues S (realFamilyChart Wf x))) 0 := by
  set ιL : (Fin k → ℝ) →L[ℝ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun l => Complex.ofRealCLM.comp (ContinuousLinearMap.proj l) with hιL
  have h0 : ∑ l, ‖(0 : Fin k → ℂ) l‖ < r' := by simpa using hr'
  have hg := hfam.analytic 0 h0 ℓ
  have hg' : AnalyticAt ℂ (fun ζ' => (ℓ (chartValues S (Wf ζ').re) : ℂ) +
      Complex.I * (ℓ (chartValues S (Wf ζ').im) : ℂ)) (ιL 0) := by
    rw [map_zero]
    exact hg
  have h1 : AnalyticAt ℝ (fun x => ((ℓ (chartValues S (Wf (ιL x)).re) : ℂ) +
      Complex.I * (ℓ (chartValues S (Wf (ιL x)).im) : ℂ)).re) 0 :=
    (Complex.reCLM.analyticAt _).comp ((hg'.restrictScalars).comp (ιL.analyticAt 0))
  refine h1.congr ?_
  have hcont : Continuous fun x : Fin k → ℝ => ∑ l, |x l| := by fun_prop
  have hev : ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < r' :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hr')
  filter_upwards [hev] with x hx
  have e := linear_chartValues_real hfam ℓ hx
  have e2 : ιL x = fun l => ((x l : ℝ) : ℂ) := rfl
  simp only [e2]
  rw [e]
  simp
def imagCoordLinear (e : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun := imagCoord e
  map_add' x y := by
    fin_cases e <;> simp [imagCoord]
  map_smul' t x := by
    fin_cases e <;> simp [imagCoord]
def imagUnit (e : Fin 3) : imaginaryQuaternions :=
  ⟨![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] e, by
    show (![(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] e).re = 0
    fin_cases e <;> simp⟩
theorem eq_sum_imagCoord_smul (w : imaginaryQuaternions) : w = ∑ e, imagCoord e w • imagUnit e := by
  have h0 : (w : ℍ[ℝ]).re = 0 := w.2
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [Fin.sum_univ_three, Submodule.coe_smul]
  ext
  · show (w : ℍ[ℝ]).re = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0
    simp [h0]
  · show (w : ℍ[ℝ]).imI = (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0
    ring
  · show (w : ℍ[ℝ]).imJ = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0
    ring
  · show (w : ℍ[ℝ]).imK = (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1
    ring
theorem analyticAt_of_imagCoord {f : (Fin k → ℝ) → imaginaryQuaternions}
    (hf : ∀ e, AnalyticAt ℝ (fun ζ => imagCoord e (f ζ)) 0) :
    AnalyticAt ℝ f 0 := by
  have e : f = fun ζ => ∑ e, imagCoord e (f ζ) • imagUnit e := by
    funext ζ
    exact eq_sum_imagCoord_smul _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact (hf i).smul analyticAt_const
def realFamilyValues (S : Finset F.Cell) (Wf : (Fin k → ℂ) → ComplexChainChart F) (x : Fin k → ℝ) :
    ChartValues S :=
  chartValues S (realFamilyChart Wf x)
theorem analyticAt_realFamilyValues (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hr' : 0 < r') :
    AnalyticAt ℝ (realFamilyValues S Wf) 0 := by
  refine AnalyticAt.prod ?_ ?_
  · rw [analyticAt_pi_iff]
    intro x
    exact analyticAt_of_imagCoord fun e => analyticAt_linear_chartValues hfam hr'
      ((imagCoordLinear e).comp ((LinearMap.proj x).comp (LinearMap.fst ℝ _ _)))
  · rw [analyticAt_pi_iff]
    intro j
    rw [analyticAt_pi_iff]
    intro x
    exact analyticAt_of_imagCoord fun e => analyticAt_linear_chartValues hfam hr'
      ((imagCoordLinear e).comp ((LinearMap.proj x).comp
        ((LinearMap.proj (φ := fun j : Fin F.depth => ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions) j).comp
          (LinearMap.snd ℝ _ _))))
theorem chartValues_chartMixedDeriv (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hr' : 0 < r')
    {m : ℕ} (e : Fin m ↪ Fin k) :
    chartValues S (chartMixedDeriv (realFamilyChart Wf) e) =
      iteratedFDeriv ℝ m (realFamilyValues S Wf) 0 (fun l => Pi.single (e l) 1) := by
  have hc : ContDiffAt ℝ (m : WithTop ℕ∞) (realFamilyValues S Wf) 0 :=
    (analyticAt_realFamilyValues hfam hr').contDiffAt
  refine Prod.ext ?_ ?_
  · funext x
    have hp := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(innerBonds S 0) => imaginaryQuaternions) x).comp
      (ContinuousLinearMap.fst ℝ (↥(innerBonds S 0) → imaginaryQuaternions)
        ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions))).iteratedFDeriv_comp_left hc
      (i := m) le_rfl
    have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
    exact this
  · funext j x
    have hp := ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(innerBonds S (j.val + 1)) => imaginaryQuaternions) x).comp
      ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun j : Fin F.depth => ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions) j).comp
      (ContinuousLinearMap.snd ℝ (↥(innerBonds S 0) → imaginaryQuaternions)
        ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions)))).iteratedFDeriv_comp_left hc
      (i := m) le_rfl
    have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
    exact this
theorem linear_chartValues_chartMixedDeriv (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf)
    (hr' : 0 < r') {m : ℕ} (e : Fin m ↪ Fin k) (ℓ : ChartValues S →ₗ[ℝ] ℝ) :
    ℓ (chartValues S (chartMixedDeriv (realFamilyChart Wf) e)) =
      iteratedFDeriv ℝ m (fun x => ℓ (chartValues S (realFamilyChart Wf x))) 0 (fun l => Pi.single (e l) 1) := by
  have hc : ContDiffAt ℝ (m : WithTop ℕ∞) (realFamilyValues S Wf) 0 :=
    (analyticAt_realFamilyValues hfam hr').contDiffAt
  have hp := (LinearMap.toContinuousLinearMap ℓ).iteratedFDeriv_comp_left hc (i := m) le_rfl
  have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hp
  rw [chartValues_chartMixedDeriv hfam hr' e]
  exact this.symm
end Readers
section Mixed
variable {a θ δ C₀ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top}
  {k : ℕ} {b : Fin k → F.Site F.top × Fin 4} {b' : Fin k → F'.Site F'.top × Fin 4} {X : Fin k → imaginaryQuaternions}
  {Wf : (Fin k → ℂ) → ComplexChainChart F} {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
def restrictValues (S D : Finset F.Cell) : ChartValues S →ₗ[ℝ] ChartValues S := by
  classical exact
  { toFun := fun e => (fun x => if enclosingCell x.1.1 ∈ D then e.1 x else 0,
      fun j x => if enclosingCell x.1.1 ∈ D then e.2 j x else 0)
    map_add' := fun e e' => by
      refine Prod.ext ?_ ?_
      · funext x
        simp only [Prod.fst_add, Pi.add_apply]
        split_ifs <;> simp
      · funext j x
        simp only [Prod.snd_add, Pi.add_apply]
        split_ifs <;> simp
    map_smul' := fun t e => by
      refine Prod.ext ?_ ?_
      · funext x
        simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp
      · funext j x
        simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
theorem localNorm_restrictValues (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (A : ChainChart F) (z : F.Cell) :
    localNorm S R (chartOfValues S (zeroChart F) (restrictValues S (cellBall S z 4) (chartValues S A)))
        (constOneWeights F) z =
      localNorm S R A (constOneWeights F) z := by
  classical
  refine localNorm_congr hamb hodd R _ z (fun x hx => ?_) (fun j hj x hx => ?_)
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    simp only [chartOfValues]
    rw [dif_pos (show (x.1, x.2) ∈ innerBonds S 0 from a1)]
    show (if enclosingCell x.1 ∈ cellBall S z 4 then _ else _) = _
    rw [if_pos a2]
    rfl
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartOfValues]
    rw [dif_pos hj', dif_pos (show (x.1, x.2) ∈ innerBonds S (j + 1) from a1)]
    show (if enclosingCell x.1 ∈ cellBall S z 4 then _ else _) = _
    rw [if_pos a2]
    rfl
theorem localNorm_sub_restrictValues (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (A : ChainChart F) (z : F.Cell) :
    localNorm S R (chartMove A (chartOfValues S (zeroChart F) (restrictValues S (cellBall S z 4) (chartValues S A)))
      (-1)) (constOneWeights F) z = 0 := by
  classical
  have h0 := localNorm_congr (S := S) hamb hodd R
    (A := chartMove A (chartOfValues S (zeroChart F) (restrictValues S (cellBall S z 4) (chartValues S A))) (-1))
    (A' := zeroChart F) (constOneWeights F) z (fun x hx => ?_) (fun j hj x hx => ?_)
  · rw [h0, localNorm_zeroChart]
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    simp only [chartMove, chartOfValues, neg_one_smul_imag]
    rw [dif_pos (show (x.1, x.2) ∈ innerBonds S 0 from a1)]
    have e : (restrictValues S (cellBall S z 4) (chartValues S A)).1 ⟨(x.1, x.2), a1⟩ = A.fine x.1 x.2 := by
      show (if enclosingCell x.1 ∈ cellBall S z 4 then _ else _) = _
      rw [if_pos a2]
      rfl
    rw [e]
    simp [zeroChart]
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartMove, chartOfValues, neg_one_smul_imag]
    rw [dif_pos hj', dif_pos (show (x.1, x.2) ∈ innerBonds S (j + 1) from a1)]
    have e : (restrictValues S (cellBall S z 4) (chartValues S A)).2 ⟨j, hj'⟩ ⟨(x.1, x.2), a1⟩ =
        A.coarse j x.1 x.2 := by
      show (if enclosingCell x.1 ∈ cellBall S z 4 then _ else _) = _
      rw [if_pos a2]
      rfl
    rw [e]
    simp [zeroChart]
theorem exists_linear_translate_values (Y : F.Cell) (Y' : F'.Cell) (D : Finset F.Cell)
    (h0 : ∀ x ∈ innerBonds S 0, enclosingCell x.1 ∈ D → (translateSite Y Y' x.1, x.2) ∈ innerBonds S' 0)
    (h1 : ∀ (j : ℕ), j < F.depth → ∀ x ∈ innerBonds S (j + 1), enclosingCell x.1 ∈ D → j < F'.depth ∧
      (translateSite Y Y' x.1, x.2) ∈ innerBonds S' (j + 1)) :
    ∃ Tr : ChartValues S' →ₗ[ℝ] ChartValues S, ∀ A' : ChainChart F',
      Tr (chartValues S' A') = restrictValues S D (chartValues S (chartTranslate Y Y' A')) := by
  classical
  have hu : ∀ (e : ChartValues S') (x : F'.Site 0 × Fin 4) (hx : x ∈ innerBonds S' 0),
      (chartOfValues S' (zeroChart F') e).fine x.1 x.2 = e.1 ⟨x, hx⟩ := by
    intro e x hx
    simp only [chartOfValues]
    rw [dif_pos (show (x.1, x.2) ∈ innerBonds S' 0 from hx)]
  have hm : ∀ (e : ChartValues S') (j : ℕ) (hj : j < F'.depth) (x : F'.Site (j + 1) × Fin 4)
      (hx : x ∈ innerBonds S' (j + 1)),
      (chartOfValues S' (zeroChart F') e).coarse j x.1 x.2 = e.2 ⟨j, hj⟩ ⟨x, hx⟩ := by
    intro e j hj x hx
    simp only [chartOfValues]
    rw [dif_pos hj, dif_pos (show (x.1, x.2) ∈ innerBonds S' (j + 1) from hx)]
  refine ⟨{ toFun := fun e => (fun x => if enclosingCell x.1.1 ∈ D then
              (chartOfValues S' (zeroChart F') e).fine (translateSite Y Y' x.1.1) x.1.2 else 0,
            fun j x => if enclosingCell x.1.1 ∈ D then
              (chartOfValues S' (zeroChart F') e).coarse j.val (translateSite Y Y' x.1.1) x.1.2 else 0)
            map_add' := fun e e' => ?_
            map_smul' := fun c e => ?_ }, fun A' => ?_⟩
  · refine Prod.ext ?_ ?_
    · funext x
      simp only [Prod.fst_add, Pi.add_apply]
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc, if_pos hc]
        have hb := h0 x.1 x.2 hc
        rw [hu _ _ hb, hu _ _ hb, hu _ _ hb]
        rfl
      · rw [if_neg hc, if_neg hc, if_neg hc, add_zero]
    · funext j x
      simp only [Prod.snd_add, Pi.add_apply]
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc, if_pos hc]
        obtain ⟨hj, hb⟩ := h1 j.val j.2 x.1 x.2 hc
        rw [hm _ _ hj _ hb, hm _ _ hj _ hb, hm _ _ hj _ hb]
        rfl
      · rw [if_neg hc, if_neg hc, if_neg hc, add_zero]
  · refine Prod.ext ?_ ?_
    · funext x
      simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc]
        have hb := h0 x.1 x.2 hc
        rw [hu _ _ hb, hu _ _ hb]
        rfl
      · rw [if_neg hc, if_neg hc, smul_zero]
    · funext j x
      simp only [Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc]
        obtain ⟨hj, hb⟩ := h1 j.val j.2 x.1 x.2 hc
        rw [hm _ _ hj _ hb, hm _ _ hj _ hb]
        rfl
      · rw [if_neg hc, if_neg hc, smul_zero]
  · refine Prod.ext ?_ ?_
    · funext x
      show (if enclosingCell x.1.1 ∈ D then _ else _) = (if enclosingCell x.1.1 ∈ D then _ else _)
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc]
        have hb := h0 x.1 x.2 hc
        rw [hu _ _ hb]
        rfl
      · rw [if_neg hc, if_neg hc]
    · funext j x
      show (if enclosingCell x.1.1 ∈ D then _ else _) = (if enclosingCell x.1.1 ∈ D then _ else _)
      by_cases hc : enclosingCell x.1.1 ∈ D
      · rw [if_pos hc, if_pos hc]
        obtain ⟨hj, hb⟩ := h1 j.val j.2 x.1 x.2 hc
        rw [hm _ _ hj _ hb]
        rfl
      · rw [if_neg hc, if_neg hc]
end Mixed
section Mixed2
variable {a θ δ C₀ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top}
  {k : ℕ} {b : Fin k → F.Site F.top × Fin 4} {b' : Fin k → F'.Site F'.top × Fin 4} {X : Fin k → imaginaryQuaternions}
  {Wf : (Fin k → ℂ) → ComplexChainChart F} {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
theorem linear_chartValues_chartMove (ℓ : ChartValues S →ₗ[ℝ] ℝ) (U U' : ChainChart F) (t : ℝ) :
    ℓ (chartValues S (chartMove U U' t)) = ℓ (chartValues S U) + t * ℓ (chartValues S U') := by
  have e : chartValues S (chartMove U U' t) = chartValues S U + t • chartValues S U' := rfl
  rw [e, map_add, map_smul, smul_eq_mul]
theorem localNorm_mixedDeriv_diff_le (hMix : Analytic.CauchyMixedDerivativeDifferenceProperty)
    (hodd : Odd F.blockSide) (hamb : IsAdmissibleAmbient F)
    (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf)
    (hfam' : IsComplexCriticalFamily a θ δ C₀ rL r' s S' V' b' X Wf') (hr' : 0 < r') (R : F.FieldChain)
    (Y : F.Cell) (Y' : F'.Cell) (z : F.Cell)
    (h0 : ∀ x ∈ innerBonds S 0, enclosingCell x.1 ∈ cellBall S z 4 → (translateSite Y Y' x.1, x.2) ∈ innerBonds S' 0)
    (h1 : ∀ (j : ℕ), j < F.depth → ∀ x ∈ innerBonds S (j + 1), enclosingCell x.1 ∈ cellBall S z 4 → j < F'.depth ∧
      (translateSite Y Y' x.1, x.2) ∈ innerBonds S' (j + 1))
    {Bd : ℝ}
    (hBd : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' →
      localNorm S R (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1)) (constOneWeights F) z +
        localNorm S R (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1)) (constOneWeights F) z ≤ Bd)
    {m : ℕ} (e : Fin m ↪ Fin k) (hm : 1 ≤ m) :
    localNorm S R (chartMove (chartMixedDeriv (realFamilyChart Wf) e)
        (chartTranslate Y Y' (chartMixedDeriv (realFamilyChart Wf') e)) (-1))
        (constOneWeights F) z ≤ 2 * Bd * (((m : ℝ) + 1) / r') ^ m := by
  classical
  set A₀ := chartMove (chartMixedDeriv (realFamilyChart Wf) e)
    (chartTranslate Y Y' (chartMixedDeriv (realFamilyChart Wf') e)) (-1) with hA₀
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_linear_chartValues_le_localNorm (S := S) R (constOneWeights F)
    (fun _ _ => zero_le_one) z A₀
  obtain ⟨Tr, hTr⟩ := exists_linear_translate_values (S := S) (S' := S') Y Y' (cellBall S z 4) h0 h1
  set π := restrictValues S (cellBall S z 4) with hπ
  set ℓ₁ : ChartValues S →ₗ[ℝ] ℝ := ℓ.comp π with hℓ₁
  set ℓ₂ : ChartValues S' →ₗ[ℝ] ℝ := ℓ.comp Tr with hℓ₂
  have hℓ₂r : ∀ A' : ChainChart F', ℓ₂ (chartValues S' A') = ℓ₁ (chartValues S (chartTranslate Y Y' A')) :=
    fun A' => by
      simp only [hℓ₂, hℓ₁, LinearMap.comp_apply, hTr]
  have hle : ∀ B : ChainChart F, |ℓ₁ (chartValues S B)| ≤ localNorm S R B (constOneWeights F) z := by
    intro B
    have h2 := hℓ2 (chartOfValues S (zeroChart F) (π (chartValues S B)))
    rw [chartValues_chartOfValues, localNorm_restrictValues hamb hodd R B z] at h2
    exact h2
  have hval : ℓ₁ (chartValues S A₀) = localNorm S R A₀ (constOneWeights F) z := by
    have h2 := hℓ2 (chartMove A₀ (chartOfValues S (zeroChart F) (π (chartValues S A₀))) (-1))
    rw [localNorm_sub_restrictValues hamb hodd R A₀ z, linear_chartValues_chartMove, chartValues_chartOfValues] at h2
    have h3 := abs_nonpos_iff.1 h2
    have h4 : ℓ (chartValues S A₀) = ℓ₁ (chartValues S A₀) := by
      simp only [hℓ₁, LinearMap.comp_apply]
      linarith
    rw [← h4, hℓ1]
  set g : (Fin k → ℂ) → ℂ := fun ζ =>
    ((ℓ₁ (chartValues S (Wf ζ).re) : ℂ) + Complex.I * (ℓ₁ (chartValues S (Wf ζ).im) : ℂ)) -
      ((ℓ₂ (chartValues S' (Wf' ζ).re) : ℂ) + Complex.I * (ℓ₂ (chartValues S' (Wf' ζ).im) : ℂ)) with hg
  set hh : (Fin k → ℝ) → ℝ := fun x =>
    ℓ₁ (chartValues S (realFamilyChart Wf x)) - ℓ₂ (chartValues S' (realFamilyChart Wf' x)) with hhd
  have hgn : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' → ‖g ζ‖ ≤ Bd := by
    intro ζ hζ
    have e1 : g ζ = ((ℓ₁ (chartValues S (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1))) : ℝ) : ℂ) +
        Complex.I * ((ℓ₁ (chartValues S (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1))) : ℝ) : ℂ) := by
      simp only [hg, linear_chartValues_chartMove, hℓ₂r]
      push_cast
      ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (add_le_add (hle _) (hle _)).trans (hBd ζ hζ)
  have hcont : Continuous fun x : Fin k → ℝ => ∑ l, |x l| := by fun_prop
  have hev : ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < r' :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hr')
  set i₀ : Fin m := ⟨0, hm⟩ with hi₀
  have hmix := hMix k m (fun l => e l) i₀ g hh r' (2 * Bd) hr'
    (fun ζ hζ => (hfam.analytic ζ hζ ℓ₁).sub (hfam'.analytic ζ hζ ℓ₂))
    (by
      filter_upwards [hev] with x hx
      simp only [hg, hhd]
      rw [linear_chartValues_real hfam ℓ₁ hx, linear_chartValues_real hfam' ℓ₂ hx]
      push_cast
      rfl)
    (fun ζ hζ => by
      have hup : ∑ l, ‖Function.update ζ (e i₀) 0 l‖ < r' := by
        refine lt_of_le_of_lt (Finset.sum_le_sum fun l _ => ?_) hζ
        by_cases hl : l = e i₀
        · subst hl
          simp
        · simp [hl]
      refine (norm_sub_le _ _).trans ?_
      have := hgn ζ hζ
      have := hgn _ hup
      linarith)
  have hc1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => ℓ₁ (chartValues S (realFamilyChart Wf x))) 0 :=
    (analyticAt_linear_chartValues hfam hr' ℓ₁).contDiffAt
  have hc2 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => ℓ₂ (chartValues S' (realFamilyChart Wf' x))) 0 :=
    (analyticAt_linear_chartValues hfam' hr' ℓ₂).contDiffAt
  have hsub := iteratedFDeriv_sub_apply (i := m) (x := (0 : Fin k → ℝ)) hc1 hc2
  have hsub' : iteratedFDeriv ℝ m hh 0 (fun l => Pi.single (e l) 1) =
      iteratedFDeriv ℝ m (fun x => ℓ₁ (chartValues S (realFamilyChart Wf x))) 0 (fun l => Pi.single (e l) 1) -
        iteratedFDeriv ℝ m (fun x => ℓ₂ (chartValues S' (realFamilyChart Wf' x))) 0 (fun l => Pi.single (e l) 1) := by
    have := congrArg (fun M => M (fun l => (Pi.single (e l) 1 : Fin k → ℝ))) hsub
    exact this
  rw [hsub', ← linear_chartValues_chartMixedDeriv hfam hr' e ℓ₁, ← linear_chartValues_chartMixedDeriv hfam' hr' e ℓ₂,
    hℓ₂r] at hmix
  have e2 : ℓ₁ (chartValues S A₀) = ℓ₁ (chartValues S (chartMixedDeriv (realFamilyChart Wf) e)) -
      ℓ₁ (chartValues S (chartTranslate Y Y' (chartMixedDeriv (realFamilyChart Wf') e))) := by
    rw [hA₀, linear_chartValues_chartMove]
    ring
  rw [hval.symm, e2]
  exact (le_abs_self _).trans hmix
end Mixed2
section Across
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r : ℕ}
theorem exists_siteAtOffset (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) {d : ℕ}
    (hd : cellSupDist (enclosingCell x) Y ≤ d) :
    ∃ p : Fin 4 → ℤ, x = siteAtOffset j Y p ∧ WithinCellRadius F.blockSide F.top (d + 1) j p := by
  classical
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  have hc : enclosingCell x = y := by
    rw [e]
    exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd y h hh
  rw [hc] at hd
  set o : Fin 4 → ℤ := fun i => (y i - Y i).valMinAbs with ho
  have hyY : y = Y + siteOfCoords F.top o := by
    funext i
    simp only [Pi.add_apply, siteOfCoords, ho, ZMod.coe_valMinAbs]
    abel
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hP : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := pow_pos hL0 _
  refine ⟨(fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h, ?_, fun i => ?_⟩
  · unfold siteAtOffset
    rw [e, hyY, cellCentre_add j hj, siteOfCoords_add, add_assoc]
  · have hle : |o i| ≤ (d : ℤ) := by
      have h1 := Finset.le_sup (f := fun i => ((y i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
      have h2 : ((y i - Y i).valMinAbs).natAbs ≤ d := h1.trans hd
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
    have hcube := (LatticePaths.mem_centredCube_iff _ _).1 hh i
    have e3 : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = (F.blockSide : ℤ) ^ (F.top - j) := by simp
    rw [e3] at hcube
    have h2 : |h i| ≤ (F.blockSide : ℤ) ^ (F.top - j) := by
      rw [abs_le]
      constructor <;> omega
    have h3 : |((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) i| ≤
        ((d : ℤ) + 1) * (F.blockSide : ℤ) ^ (F.top - j) := by
      simp only [Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hP]
      nlinarith
    have hn : (F.blockSide : ℤ) ^ F.top = (F.blockSide : ℤ) ^ j * (F.blockSide : ℤ) ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hn]
    have h4 := mul_le_mul_of_nonneg_left h3 (pow_pos hL0 j).le
    push_cast
    refine h4.trans (le_of_eq ?_)
    ring
theorem withinCellRadius_add_single (hL : 0 < F.blockSide) {j ρ : ℕ} (hj : j ≤ F.top) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius F.blockSide F.top ρ j p) (i : Fin 4) :
    WithinCellRadius F.blockSide F.top (ρ + 1) j (p + Pi.single i 1) := by
  intro l
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
  have h1 := hp l
  have h2 : |(p + (Pi.single i 1 : Fin 4 → ℤ)) l| ≤ |p l| + 1 := by
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans ?_
    have : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
      by_cases h : l = i
      · subst h
        simp
      · simp [h]
    linarith
  have h3 : (F.blockSide : ℤ) ^ j ≤ (F.blockSide : ℤ) ^ F.top := pow_le_pow_right₀ (by omega) hj
  have h4 := mul_le_mul_of_nonneg_left h2 (pow_pos hL0 j).le
  push_cast
  nlinarith
theorem translate_mem_innerBonds (hodd : Odd F.blockSide) (hL' : F'.blockSide = F.blockSide)
    (ht' : F'.depth = F.depth) {j : ℕ} (hj : j ≤ F.top) {d : ℕ}
    (hside : ∀ i, F.extent i = 0 ∨ 2 * (d + 2) + 2 < F.extent i)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 2) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    {x : F.Site j × Fin 4} (hx : x ∈ innerBonds S j) (hd : cellSupDist (enclosingCell x.1) Y ≤ d) :
    (translateSite Y Y' x.1, x.2) ∈ innerBonds S' j := by
  have hx' := Finset.mem_filter.1 hx
  have h1 : x.1 ∈ sitesOfCells S j := (Finset.mem_product.1 hx'.1).1
  have h2 : x.1 + unitStep j x.2 ∈ sitesOfCells S j := hx'.2
  obtain ⟨p, e, hp⟩ := exists_siteAtOffset hodd hj h1 Y hd
  have hp2 := withinCellRadius_add_single hodd.pos hj hp x.2
  have hmono : ∀ {q : Fin 4 → ℤ} {ρ ρ' : ℕ}, ρ ≤ ρ' → WithinCellRadius F.blockSide F.top ρ j q →
      WithinCellRadius F.blockSide F.top ρ' j q := by
    intro q ρ ρ' h hq i
    refine (hq i).trans ?_
    have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (pow_pos hL0 _).le
  have hs' : ∀ i, F.extent i = 0 ∨ 2 * (d + 1) + 2 < F.extent i := fun i => (hside i).imp id fun h => by omega
  have e1 : translateSite Y Y' x.1 = siteAtOffset j Y' p := by
    rw [e]
    exact translateSite_siteAtOffset hodd.pos hj Y Y' hs' hp
  have e2 : x.1 + unitStep j x.2 = siteAtOffset j Y (p + Pi.single x.2 1) := by
    rw [e]
    unfold siteAtOffset
    rw [siteOfCoords_add, add_assoc]
    rfl
  have e3 : siteAtOffset j Y' p + unitStep j x.2 = siteAtOffset j Y' (p + Pi.single x.2 1) := by
    unfold siteAtOffset
    rw [siteOfCoords_add, add_assoc]
    rfl
  rw [e] at h1
  rw [e2] at h2
  rw [e1]
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨(hS p (hmono (by omega) hp)).1 h1, ?_⟩
  rw [e3]
  exact (hS _ (hmono (by omega) hp2)).1 h2
end Across
section Same
variable {a θ δ Ca c C C₀ rL r' s c₁ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {k : ℕ}
  {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
theorem chartAgreeOn_realFamilyChart (hL : Odd F.blockSide) (hdel : 0 < δ)
    (hB : TwistedTotalBounds a θ δ Ca c C s S V b X)
    (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf) (hrc : rL ≤ c) (hr'r : r' ≤ rL) (hrc₁ : rL < c₁)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U)
    {x : Fin k → ℝ} (hx : ∑ l, |x l| < r') {U' : ChainChart F}
    (hsl : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U'.fine)
    (hU' : supWeightedNorm S δ (referenceFieldChain S V) U' ≤ rL)
    (hcr : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) (rotatedField (bondSpread b X x) V) U' A) :
    ChartEqOnBonds S (realFamilyChart Wf x) U' := by
  have hxc : ∑ l, ‖ofRealVec x l‖ < r' := by
    simpa [SpanVariations.ofRealVec, Complex.norm_real] using hx
  have hsl0 : GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0)
      (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F).fine :=
    fun s' _ => CoordinateSeminorms.gaugeMap_zero S V (referenceFieldChain S V 0) s'
  have hsum : ∑ l, |x l| ≤ c := hx.le.trans (hr'r.trans hrc)
  have hstable := hfam.stable (fun _ => 0) 0 0 (Or.inr (Or.inl rfl)) (fun y y' => by
      simp only [sub_self, abs_zero]
      exact mul_nonneg hdel.le (Nat.cast_nonneg _)) (ofRealVec x) (Wf (ofRealVec x)) (realChart U') 0 hxc le_rfl
    (hfam.mem_slice _ hxc).1 (hfam.mem_slice _ hxc).2 hsl hsl0 (hfam.small _ hxc)
    (by rw [complexSupWeightedNorm_realChart hL.pos]; exact hU') (fun A hA => by
      have hr := hasDerivAt_chartAction_of_complexFirstVariation hL hdel.le hB hreg x hsum U' A (hU'.trans hrc)
        (lt_of_le_of_lt hU' hrc₁)
      have hcA : HasDerivAt (fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U' A τ)
          (rotatedField (bondSpread b X x) V)) 0 0 := hcr A
      have e0 := hr.1.unique hcA
      have e1 : complexFirstVariation a S (referenceFieldChain S V) (realChart U')
          (complexTwistedTop b X (fun l => (x l : ℂ)) V) A = 0 :=
        Complex.ext e0 hr.2
      have e2 := hfam.critical (ofRealVec x) hxc A hA
      have e3 : complexFirstVariation a S (referenceFieldChain S V) (realChart U')
          (complexTwistedTop b X (ofRealVec x) V) A = 0 := e1
      rw [e2, e3]
      simp)
  rw [mul_zero] at hstable
  have h1 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec x)).re U' (-1))
      (classWeight F (fun _ => 0) 0 0) = 0 := by
    have h2 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec x)).re U' (-1))
        (classWeight F (fun _ => 0) 0 0) ≤ 0 := by
      have h5 : _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) (chartMove (Wf (ofRealVec x)).re U' (-1))
          (classWeight F (fun _ => 0) 0 0) + _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V)
          (chartMove (Wf (ofRealVec x)).im (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) (-1))
          (classWeight F (fun _ => 0) 0 0) ≤ 0 := hstable
      have h6 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg S (referenceFieldChain S V)
          (chartMove (Wf (ofRealVec x)).im (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) (-1))
          (classWeight F (fun _ => 0) 0 0)
      linarith
    exact le_antisymm h2 (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
  rw [CoordinateSeminorms.classWeight_zero] at h1
  have h3 := chartEq_zero_of_weightedNorm_eq_zero S hL _ _ _ (fun _ _ => one_pos) h1
  refine ⟨fun y hy => ?_, fun j hj y hy => ?_⟩
  · have h4 := h3.1 y hy
    simp only [chartMove, neg_one_smul_imag, zeroChart] at h4
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h4)
  · have h4 := h3.2 j hj y hy
    simp only [chartMove, neg_one_smul_imag, zeroChart] at h4
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h4)
end Same
section Claim
variable {a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
theorem localNorm_chartMove_neg_le (Rc : F.FieldChain) (A B : ChainChart F) (z : F.Cell) :
    localNorm S Rc (chartMove A B (-1)) (constOneWeights F) z ≤
      localNorm S Rc A (constOneWeights F) z + localNorm S Rc B (constOneWeights F) z := by
  have h := localNorm_chartMove_le S Rc A B (-1) (constOneWeights F) (fun _ _ => zero_le_one) z
  simpa using h
theorem localNorm_chartTranslate_le (hodd : Odd F.blockSide) {R : F.FieldChain} {R' : F'.FieldChain} (hr : 108 ≤ r)
    (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hN : ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' (r - 100) A A' →
      ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)) →
        localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) R A (constOneWeights F) =
          localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) R' A' (constOneWeights F'))
    (A' : ChainChart F') {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, localNorm S' R' A' (constOneWeights F') y ≤ M)
    {z : F.Cell} (hz : cellSupDist z Y ≤ 3) :
    localNorm S R (chartTranslate Y Y' A') (constOneWeights F) z ≤ 81 * M := by
  set g : Fin 4 → ℤ := fun i => ((z - Y : F.Cell) i).valMinAbs with hg
  have hzg : z = Y + siteOfCoords F.top g := by
    funext i
    simp only [Pi.add_apply, siteOfCoords, hg, ZMod.coe_valMinAbs]
    simp
  have hin : ∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ) := by
    intro i
    have hle : (g i).natAbs ≤ cellSupDist z Y :=
      Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : |g i| = ((g i).natAbs : ℤ) := Int.abs_eq_natAbs _
    omega
  have hs' : ∀ i, F.extent i = 0 ∨ 2 * (r - 100) + 2 < F.extent i := fun i => (hs i).imp id fun e => by omega
  have e := hN _ A' (chartsAgree_chartTranslate hodd.pos Y Y' hs' A') g hin
  rw [← hzg] at e
  have h1 : localNormSq S (cellBall S z 3) R (chartTranslate Y Y' A') (constOneWeights F) ≤
      localNormSq S (cellBall S z 4) R (chartTranslate Y Y' A') (constOneWeights F) :=
    localNormSq_mono_cells S (fun y hy => by
      have hy' := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨hy'.1, hy'.2.trans (by norm_num)⟩) R _ _
  have h2 := localNormSq_cellBall_le S' R' A' (Y' + siteOfCoords F'.top g) hM0 hM
  unfold localNorm
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [e] at h1
  nlinarith
def claimConst (Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL : ℝ) : ℝ :=
  2 * finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL + 2 * (82 * nearConst δ C₀ * Real.exp (250 * δ))
theorem localNorm_diff_le_claim (hodd : Odd F.blockSide) (hL' : 0 < F'.blockSide) (hdel : 0 < δ) (hs : 0 < s)
    (hC₀ : 0 < C₀) (hr : 108 ≤ r)
    (hKf : 0 ≤ finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL)
    (hfam : IsComplexCriticalFamily a θ δ C₀ rL r' s S V (offsetBonds Y h) X Wf)
    (hfam' : IsComplexCriticalFamily a θ δ C₀ rL r' s S' V' (offsetBonds Y' h) X Wf')
    (hside : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hN : ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' (r - 100) A A' →
      ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)) →
        localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) (referenceFieldChain S V) A (constOneWeights F) =
          localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) (referenceFieldChain S' V') A'
            (constOneWeights F'))
    (hTwo : 1000 ≤ r →
      ComparisonData a θ δ Ca c C C₀ Ct cT CT Cl Kp Kg Cd₁ Cd₂ rL r' s S S' V V' Y Y' r h X Wf Wf')
    {ζ : Fin k → ℂ} (hζ : ∑ l, ‖ζ l‖ < r') (hsz : 2 * (supConst Kp Kg Cd₂ δ C₀ * (s + ∑ l, ‖ζ l‖)) ≤ rL)
    {z : F.Cell} (hz : cellSupDist z Y ≤ 3) :
    localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1))
        (constOneWeights F) z +
      localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1))
        (constOneWeights F) z ≤
      claimConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * (s + ∑ l, ‖ζ l‖) * Real.exp (-δ * r / 4) := by
  set κ := s + ∑ l, ‖ζ l‖ with hκ
  have hκ0 : 0 ≤ κ := add_nonneg hs.le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hM0 : 0 ≤ nearConst δ C₀ := by
    unfold nearConst
    positivity
  by_cases hbig : 1000 ≤ r
  · obtain ⟨e1, e2⟩ := localNorm_diff_le_of_large (hTwo hbig) hζ hsz hz
    have hE : Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2) ≤ Real.exp (-δ * r / 4) := by
      apply Real.exp_le_exp.2
      have h1 : ((r - 236 : ℕ) : ℝ) = (r : ℝ) - 236 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have h2 : (1000 : ℝ) ≤ r := by exact_mod_cast hbig
      rw [h1]
      nlinarith
    have h3 : finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * ((r - 236 : ℕ) : ℝ) / 2) ≤
        finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hKf hκ0)
    have h4 : 0 ≤ 2 * (82 * nearConst δ C₀ * Real.exp (250 * δ)) * κ * Real.exp (-δ * r / 4) := by positivity
    have e3 : claimConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4) =
        2 * (finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4)) +
          2 * (82 * nearConst δ C₀ * Real.exp (250 * δ)) * κ * Real.exp (-δ * r / 4) := by
      simp only [claimConst]
      ring
    rw [e3]
    linarith
  · have hsmall : (r : ℝ) ≤ 1000 := by
      have : r ≤ 1000 := by omega
      exact_mod_cast this
    have hone : 1 ≤ Real.exp (250 * δ) * Real.exp (-δ * r / 4) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hsize := hfam.norm_le ζ hζ
    have hsize' := hfam'.norm_le ζ hζ
    have hnearW : ∀ A : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) A ≤
        complexSupWeightedNorm S δ (referenceFieldChain S V) (Wf ζ) →
        localNorm S (referenceFieldChain S V) A (constOneWeights F) z ≤ nearConst δ C₀ * κ := by
      intro A hA
      refine (localNorm_le_supWeightedNorm hodd.pos δ hdel.le _ A z).trans ?_
      have := mul_le_mul_of_nonneg_left (hA.trans hsize) (Real.exp_pos (3 * δ)).le
      refine this.trans (le_of_eq ?_)
      simp only [nearConst]
      ring
    have hnear' : ∀ A' : ChainChart F', supWeightedNorm S' δ (referenceFieldChain S' V') A' ≤
        complexSupWeightedNorm S' δ (referenceFieldChain S' V') (Wf' ζ) → ∀ y,
        localNorm S' (referenceFieldChain S' V') A' (constOneWeights F') y ≤ nearConst δ C₀ * κ := by
      intro A' hA y
      refine (localNorm_le_supWeightedNorm hL' δ hdel.le _ A' y).trans ?_
      have := mul_le_mul_of_nonneg_left (hA.trans hsize') (Real.exp_pos (3 * δ)).le
      refine this.trans (le_of_eq ?_)
      simp only [nearConst]
      ring
    have hM : 0 ≤ nearConst δ C₀ * κ := mul_nonneg hM0 hκ0
    have h1 := (localNorm_chartMove_neg_le (S := S) (referenceFieldChain S V) (Wf ζ).re
      (chartTranslate Y Y' (Wf' ζ).re) z).trans
      (add_le_add (hnearW _ (le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _)))
        (localNorm_chartTranslate_le hodd hr hside hN _ hM
          (hnear' _ (le_add_of_nonneg_right (supWeightedNorm_nonneg _ _ _ _))) hz))
    have h2 := (localNorm_chartMove_neg_le (S := S) (referenceFieldChain S V) (Wf ζ).im
      (chartTranslate Y Y' (Wf' ζ).im) z).trans
      (add_le_add (hnearW _ (le_add_of_nonneg_left (supWeightedNorm_nonneg _ _ _ _)))
        (localNorm_chartTranslate_le hodd hr hside hN _ hM
          (hnear' _ (le_add_of_nonneg_left (supWeightedNorm_nonneg _ _ _ _))) hz))
    have h3 : nearConst δ C₀ * κ + 81 * (nearConst δ C₀ * κ) ≤
        82 * nearConst δ C₀ * Real.exp (250 * δ) * κ * Real.exp (-δ * r / 4) := by
      have e : 82 * nearConst δ C₀ * Real.exp (250 * δ) * κ * Real.exp (-δ * r / 4) =
          (82 * (nearConst δ C₀ * κ)) * (Real.exp (250 * δ) * Real.exp (-δ * r / 4)) := by ring
      rw [e]
      nlinarith
    have e3 : claimConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4) =
        2 * finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4) +
          2 * (82 * nearConst δ C₀ * Real.exp (250 * δ) * κ * Real.exp (-δ * r / 4)) := by
      simp only [claimConst]
      ring
    rw [e3]
    have h4 : 0 ≤ 2 * finalConst Kp Kg Cd₁ Cd₂ δ C₀ C CT Cl rL * κ * Real.exp (-δ * r / 4) := by positivity
    linarith
end Claim
section Final
variable {a θ δ Ca c C C₀ rL r' s : ℝ} {S : Finset F.Cell} {S' : Finset F'.Cell}
  {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
  {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} {Wf : (Fin k → ℂ) → ComplexChainChart F}
  {Wf' : (Fin k → ℂ) → ComplexChainChart F'}
theorem criticalFamily_of_le {ρ : ℝ} {b : Fin k → F.Site F.top × Fin 4}
    (hf : IsComplexCriticalFamily a θ δ C₀ rL ρ s S V b X Wf) (hr : r' ≤ ρ) :
    IsComplexCriticalFamily a θ δ C₀ rL r' s S V b X Wf where
  mem_slice ζ hζ := hf.mem_slice ζ (hζ.trans_le hr)
  norm_le ζ hζ := hf.norm_le ζ (hζ.trans_le hr)
  small ζ hζ := hf.small ζ (hζ.trans_le hr)
  critical ζ hζ := hf.critical ζ (hζ.trans_le hr)
  analytic ζ hζ := hf.analytic ζ (hζ.trans_le hr)
  real ζ hζ := hf.real ζ (hζ.trans_le hr)
  solve := hf.solve
  stable φ θ' p h1 h2 ζ W W' β hζ := hf.stable φ θ' p h1 h2 ζ W W' β (hζ.trans_le hr)
theorem siteOfCoords_injective_of_small {F : BlockFrame} {r : ℕ} (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    {a b : Fin 4 → ℤ}
    (ha : ∀ i, |a i| ≤ r) (hb : ∀ i, |b i| ≤ r) (h : siteOfCoords (F := F) F.top a = siteOfCoords F.top b) :
    a = b := by apply _root_.YangMills.Construction.BlockAverages.AnalyticChart.siteOfCoords_injOn_ball <;> assumption
theorem complexTwistedTop_translate_eq (hL : 0 < F.blockSide) (hLeq : F'.blockSide = F.blockSide)
    (hteq : F'.depth = F.depth) (hr : 1000 ≤ r)
    (hagree : AgreeOnBall S V S' V' Y Y' r) (hh : ∀ l, BondWithinRadius (r / 2) (h l)) (ζ : Fin k → ℂ)
    (p : Fin 4 → ℤ) (i : Fin 4) (hp : WithinCellRadius F.blockSide F.top (r - 202) F.top p) :
    complexTwistedTop (offsetBonds Y h) X ζ V (siteAtOffset F.top Y p) i =
      complexTwistedTop (offsetBonds Y' h) X ζ V' (siteAtOffset F'.top Y' p) i := by
  obtain ⟨hs, hs', -, hV⟩ := hagree
  have hpb : ∀ l, |p l| ≤ ((r - 202 : ℕ) : ℤ) := by
    intro l
    have := abs_le_of_withinCellRadius hL le_rfl hp l
    rw [Nat.sub_self, pow_zero, mul_one] at this
    exact this
  have hpr : ∀ l, |p l| ≤ (r : ℤ) := fun l => by
    have := hpb l
    omega
  have hhb : ∀ (l : Fin k) (q : Fin 4), |(h l).1 q| ≤ (r : ℤ) := fun l q => by
    have := (hh l).1 q
    have h2 : ((r / 2 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.div_le_self r 2
    omega
  have e1 : siteAtOffset F.top Y p = Y + siteOfCoords F.top p := by
    unfold siteAtOffset
    rw [cellCentre_top]
  have e2 : siteAtOffset F'.top Y' p = Y' + siteOfCoords F'.top p := by
    unfold siteAtOffset
    rw [cellCentre_top]
  have hcond : ∀ l, (offsetBonds Y h l = (siteAtOffset F.top Y p, i)) ↔
      (offsetBonds Y' h l = (siteAtOffset F'.top Y' p, i)) := by
    intro l
    rw [e1, e2]
    simp only [offsetBonds, Prod.mk.injEq, add_right_inj]
    constructor
    · rintro ⟨a1, a2⟩
      have := siteOfCoords_injective_of_small hs (hhb l) hpr a1
      rw [this]
      exact ⟨rfl, a2⟩
    · rintro ⟨a1, a2⟩
      have := siteOfCoords_injective_of_small hs' (hhb l) hpr a1
      rw [this]
      exact ⟨rfl, a2⟩
  have hVb : V (siteAtOffset F.top Y p) i = V' (siteAtOffset F'.top Y' p) i := by
    rw [e1, e2]
    refine hV (p, i) ⟨hpr, fun q => ?_⟩
    show |(p + (Pi.single i 1 : Fin 4 → ℤ)) q| ≤ (r : ℤ)
    have h1 := hpb q
    have h2 : |(p + (Pi.single i 1 : Fin 4 → ℤ)) q| ≤ |p q| + 1 := by
      simp only [Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      have : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) q| ≤ 1 := by
        by_cases hq : q = i
        · subst hq
          simp
        · simp [hq]
      linarith
    omega
  simp only [complexTwistedTop, hVb]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hc : offsetBonds Y h l = (siteAtOffset F.top Y p, i)
  · rw [if_pos hc, if_pos ((hcond l).1 hc)]
  · rw [if_neg hc, if_neg fun h' => hc ((hcond l).2 h')]
end Final
section Last
variable {S : Finset F.Cell} {Y : F.Cell} {Y' : F'.Cell}
theorem rotatedField_zero {k : ℕ} (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) :
    rotatedField (bondSpread b X 0) V = V := by
  funext y i
  have h1 : bondSpread b X 0 y i = 0 := by
    simp [bondSpread]
  have h2 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp [rotatedField, h1, h2]
theorem chartAgreeOn_chartMixedDeriv {k : ℕ} {T T₂ : (Fin k → ℝ) → ChainChart F}
    (hev : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), ChartEqOnBonds S (T x) (T₂ x)) {m : ℕ} (e : Fin m ↪ Fin k) :
    ChartEqOnBonds S (chartMixedDeriv T e) (chartMixedDeriv T₂ e) := by
  refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
  · have h1 : (fun ζ => (T ζ).fine x.1 x.2) =ᶠ[𝓝 0] fun ζ => (T₂ ζ).fine x.1 x.2 := by
      filter_upwards [hev] with ζ hζ
      exact hζ.1 x hx
    show iteratedFDeriv ℝ m (fun ζ => (T ζ).fine x.1 x.2) 0 _ = iteratedFDeriv ℝ m (fun ζ => (T₂ ζ).fine x.1 x.2) 0 _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h1 m).self_of_nhds]
  · have h1 : (fun ζ => (T ζ).coarse j x.1 x.2) =ᶠ[𝓝 0] fun ζ => (T₂ ζ).coarse j x.1 x.2 := by
      filter_upwards [hev] with ζ hζ
      exact hζ.2 j hj x hx
    show iteratedFDeriv ℝ m (fun ζ => (T ζ).coarse j x.1 x.2) 0 _ =
      iteratedFDeriv ℝ m (fun ζ => (T₂ ζ).coarse j x.1 x.2) 0 _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h1 m).self_of_nhds]
theorem localNorm_translate_congr (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (Rc : F.FieldChain)
    (z : F.Cell) {S' : Finset F'.Cell}
    {A₁ A₂ : ChainChart F} {B₁ B₂ : ChainChart F'} (hA : ChartEqOnBonds S A₁ A₂)
    (hB : ChartEqOnBonds S' B₁ B₂)
    (h0 : ∀ x ∈ innerBonds S 0, enclosingCell x.1 ∈ cellBall S z 4 → (translateSite Y Y' x.1, x.2) ∈ innerBonds S' 0)
    (h1 : ∀ (j : ℕ), j + 1 < F.top → ∀ x ∈ innerBonds S (j + 1), enclosingCell x.1 ∈ cellBall S z 4 →
      (translateSite Y Y' x.1, x.2) ∈ innerBonds S' (j + 1))
    (hn : F'.top = F.top) :
    localNorm S Rc (chartMove A₁ (chartTranslate Y Y' B₁) (-1)) (constOneWeights F) z =
      localNorm S Rc (chartMove A₂ (chartTranslate Y Y' B₂) (-1)) (constOneWeights F) z := by
  refine localNorm_congr hamb hodd Rc _ z (fun x hx => ?_) (fun j hj x hx => ?_)
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    show A₁.fine x.1 x.2 + (-1 : ℝ) • B₁.fine (translateSite Y Y' x.1) x.2 =
      A₂.fine x.1 x.2 + (-1 : ℝ) • B₂.fine (translateSite Y Y' x.1) x.2
    rw [hA.1 x a1, hB.1 (translateSite Y Y' x.1, x.2) (h0 x a1 a2)]
  · obtain ⟨a1, a2⟩ := mem_bondsOver.1 hx
    show A₁.coarse j x.1 x.2 + (-1 : ℝ) • B₁.coarse j (translateSite Y Y' x.1) x.2 =
      A₂.coarse j x.1 x.2 + (-1 : ℝ) • B₂.coarse j (translateSite Y Y' x.1) x.2
    rw [hA.2 j hj x a1, hB.2 j (by omega) (translateSite Y Y' x.1, x.2) (h1 j hj x a1 a2)]
end Last
end AgreeingPairs
open AgreeingPairs CoordinateSeminorms ChartCoordinates SpanVariations ComplexFamilies TwistedTops Offsets
  CoordinateCutoffs in
set_option maxHeartbeats 4000000 in
theorem agreeingPairsComparison (hC0 : complexCriticalFamiliesStatement)
    (hT : actionTaylorBoundStatement) (hProj : sliceProjectionStatement)
    (hGd : gaugeMapDifferenceNearCellStatement) (hFV : firstVariationAcrossFramesStatement)
    (hGA : gaugeMapAcrossFramesStatement) (hNm : localNormSqOnBallsAcrossFramesStatement)
    (hSt : sitesOfCellsAcrossFramesStatement) (hLF : localFirstVariationStatement)
    (hVan : Analytic.vanishingOnRealPointsStatement)
    (hMix : Analytic.CauchyMixedDerivativeDifferenceProperty) (hAny : sliceCriticalImpliesCriticalStatement)
    (hR : smallChartIsRegularStatement) : agreeingPairsComparisonStatement := by
  intro a θ δ Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hEl
  obtain ⟨Ca, hCa, L₂, hC0'⟩ := hC0 a θ δ Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hEl
  obtain ⟨Ct, L₃, hCt, hT'⟩ := hT a θ δ ha hθ.le hθ8 hdel hdel8
  obtain ⟨L₅, hP'⟩ := hProj
  obtain ⟨cg, Kg, L₆, hcg, hKg, hG'⟩ := hGd
  obtain ⟨cf, hcf, hFV'⟩ := hFV
  obtain ⟨ca, hca, hGA'⟩ := hGA
  obtain ⟨cn, hcn, hNm'⟩ := hNm
  obtain ⟨L₇, hLF'⟩ := hLF a δ ha hdel hdel8
  obtain ⟨L₈, hAny'⟩ := hAny a δ ha hdel hdel8
  obtain ⟨L₉, hR'⟩ := hR
  obtain ⟨Cd₁, hCd₁, hcd₁⟩ := _root_.YangMills.Construction.CoordinateCutoffs.exists_sum_exp_neg_cellSupDist_le hdel
  obtain ⟨Cd₂, hCd₂, hcd₂⟩ := _root_.YangMills.Construction.CoordinateCutoffs.exists_sum_exp_neg_cellSupDist_le (ε := 2 * δ) (by positivity)
  refine ⟨max (max (max (max L₂ L₃) (max L₅ L₆)) (max (max L₇ L₈) L₉)) 3, fun L hL hLge₀ => ?_⟩
  have hLge : max (max (max L₂ L₃) (max L₅ L₆)) (max (max L₇ L₈) L₉) ≤ L := le_trans (le_max_left _ _) hLge₀
  have hL3₀ : 3 ≤ L := le_trans (le_max_right _ _) hLge₀
  have hA1 : max (max L₂ L₃) (max L₅ L₆) ≤ L := le_trans (le_max_left _ _) hLge
  have hA2 : max (max L₇ L₈) L₉ ≤ L := le_trans (le_max_right _ _) hLge
  have hL2 : L₂ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hA1)
  have hL3 : L₃ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hA1)
  have hL5 : L₅ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hA1)
  have hL6 : L₆ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hA1)
  have hL7 : L₇ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hA2)
  have hL8 : L₈ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hA2)
  have hL9 : L₉ ≤ L := le_trans (le_max_right _ _) hA2
  obtain ⟨c₀, C, hc₀, hC, hFam⟩ := hC0' L hL hL2
  obtain ⟨cT, CT, hcT, hCT, hTL⟩ := hT' L hL hL3
  obtain ⟨cp, Kp, hcp, hKp, hPL⟩ := hP' L hL hL5
  obtain ⟨cl, Cl, hcl, hCl, hLFL⟩ := hLF' L hL hL7
  obtain ⟨c₄, hc₄, hAnyL⟩ := hAny' L hL hL8
  obtain ⟨c₁, hc₁, hRL⟩ := hR' L hL hL9 δ hdel hdel8
  refine ⟨min (min (c₀ / 2) (c₁ / 2)) (min c₄ cl), lt_min (lt_min (by positivity) (by positivity)) (lt_min hc₄ hcl),
    fun rL hrL hrLc => ?_⟩
  have hrc₀ : rL ≤ c₀ / 2 := hrLc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrc₁ : rL ≤ c₁ / 2 := hrLc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrc₄ : rL ≤ c₄ := hrLc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrcl : rL ≤ cl := hrLc.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r₀, s₁, hr₀, hr₀r, hs₁, hFamL⟩ := hFam rL hrL (by linarith)
  set Ns := supConst Kp Kg Cd₂ δ C with hNsd
  have hNs0 : 0 ≤ Ns := by
    simp only [hNsd, supConst, gaugeDiffConst, nearConst]
    positivity
  set e₀ : ℝ := rL / (4 * Ns + 4) with he₀
  have he₀0 : 0 < e₀ := by positivity
  set r' : ℝ := min r₀ e₀ with hr'd
  have hr'0 : 0 < r' := lt_min hr₀ he₀0
  have hr'r₀ : r' ≤ r₀ := min_le_left _ _
  have hr'e : r' ≤ e₀ := min_le_right _ _
  have hr'r : r' ≤ rL := hr'r₀.trans hr₀r
  set KA := claimConst Kp Kg Cd₁ Cd₂ δ C C CT Cl rL with hKA
  have hKf : 0 ≤ finalConst Kp Kg Cd₁ Cd₂ δ C C CT Cl rL := by
    simp only [finalConst, dualConst, formConst, supConst, gaugeDiffConst, nearConst, cutConst]
    positivity
  have hKA0 : 0 < KA := by
    simp only [hKA, claimConst, nearConst]
    positivity
  set s₀ : ℝ := min (min s₁ e₀) (min (min cT cp) (min (min cg cl) (min (min cf ca) (min cn (min c₁ (min c₄ 1))))))
    with hs₀
  have hs₀0 : 0 < s₀ := lt_min (lt_min hs₁ he₀0) (lt_min (lt_min hcT hcp) (lt_min (lt_min hcg hcl)
    (lt_min (lt_min hcf hca) (lt_min hcn (lt_min hc₁ (lt_min hc₄ one_pos))))))
  refine ⟨s₀, KA, fun m' => 2 * (KA * (1 + r')) * (((m' : ℝ) + 1) / r') ^ m' + 1, hs₀0, hKA0,
    fun m' => by positivity, ?_⟩
  intro F F' m S S' hFL hFL' ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs hsle hcold hcold' hr hagree U U' hU hU'
  have hLF₁ : Odd F.blockSide := hFL ▸ hL
  have hLeq : F'.blockSide = F.blockSide := hFL'.trans hFL.symm
  have hLF₂ : Odd F'.blockSide := hFL' ▸ hL
  have g1 : s ≤ s₁ := hsle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have g2 : s ≤ e₀ := hsle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hR1 := min_le_right (min s₁ e₀)
    (min (min cT cp) (min (min cg cl) (min (min cf ca) (min cn (min c₁ (min c₄ 1))))))
  have g3 : s ≤ cT := hsle.trans (hR1.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have g4 : s ≤ cp := hsle.trans (hR1.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hR2 := (hsle.trans hR1).trans (min_le_right _ _)
  have g5 : s ≤ cg := hR2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have g6 : s ≤ cl := hR2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hR3 := hR2.trans (min_le_right _ _)
  have g7 : s ≤ cf := hR3.trans ((min_le_left _ _).trans (min_le_left _ _))
  have g8 : s ≤ ca := hR3.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hR4 := hR3.trans (min_le_right _ _)
  have g9 : s ≤ cn := hR4.trans (min_le_left _ _)
  have hR5 := hR4.trans (min_le_right _ _)
  have g10 : s ≤ c₁ := hR5.trans (min_le_left _ _)
  have hR6 := hR5.trans (min_le_right _ _)
  have g11 : s ≤ c₄ := hR6.trans (min_le_left _ _)
  have g12 : s ≤ 1 := hR6.trans (min_le_right _ _)
  have hrc : rL < c₀ := by linarith
  have hrc₁' : rL < c₁ := by linarith
  have hreg₁ : ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c₁ →
      ChartIsRegular S (referenceFieldChain S V) U := fun U hU =>
    (hRL F m S hFL hamb hm hreg s V hs g10 hcold U hU).1
  have hreg₂ : ∀ U : ChainChart F', supWeightedNorm S' δ (referenceFieldChain S' V') U ≤ c₁ →
      ChartIsRegular S' (referenceFieldChain S' V') U := fun U hU =>
    (hRL F' m S' hFL' hamb' hm hreg' s V' hs g10 hcold' U hU).1
  have hAny₂ : ∀ (W : F'.GaugeField F'.top) (U : ChainChart F'),
      supWeightedNorm S' δ (referenceFieldChain S' V') U ≤ rL →
      (∀ A : ChainChart F', GaugeMap.InGaugeSlice S' V' (referenceFieldChain S' V' 0) A.fine →
        IsStationaryAlong a S' (referenceFieldChain S' V') W U A) →
      ∀ A : ChainChart F', IsStationaryAlong a S' (referenceFieldChain S' V') W U A := fun W U hU hc =>
    hAnyL F' m S' hFL' hamb' hm hreg' s V' W hs g11 hcold' U (hU.trans hrc₄) hc
  have hside := hagree.1
  have hside' := hagree.2.1
  have hNmP : ∀ (A : ChainChart F) (A' : ChainChart F'), ChartsAgreeAtOffsets Y Y' (r - 100) A A' →
      ∀ g : Fin 4 → ℤ, (∀ i, |g i| + 5 ≤ ((r - 100 : ℕ) : ℤ)) →
        localNormSq S (cellBall S (Y + siteOfCoords F.top g) 4) (referenceFieldChain S V) A (constOneWeights F) =
          localNormSq S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) (referenceFieldChain S' V') A'
            (constOneWeights F') :=
    fun A A' hA g hg => hNm' F F' m S S' s V V' Y Y' r (r - 100) hLeq ht hLF₁ hamb hamb' hm hreg hreg' hs g9 hcold
      hcold' hagree (by omega) A A' hA g hg
  have hTp := hTL F m S hFL hamb hm hreg s V hs g3 hcold
  have hkey : ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      (∀ l, BondWithinRadius (r / 2) (h l)) →
      ∃ (Wf : (Fin k → ℂ) → ComplexChainChart F) (Wf' : (Fin k → ℂ) → ComplexChainChart F'),
        TwistedTotalBounds a θ δ Ca c₀ C s S V (offsetBonds Y h) X ∧
        TwistedTotalBounds a θ δ Ca c₀ C s S' V' (offsetBonds Y' h) X ∧
        IsComplexCriticalFamily a θ δ C rL r' s S V (offsetBonds Y h) X Wf ∧
        IsComplexCriticalFamily a θ δ C rL r' s S' V' (offsetBonds Y' h) X Wf' ∧
        ∀ (ζ : Fin k → ℂ), ∑ l, ‖ζ l‖ < r' → ∀ z : F.Cell, cellSupDist z Y ≤ 3 →
          localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1))
              (constOneWeights F) z +
            localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1))
              (constOneWeights F) z ≤
            KA * (s + ∑ l, ‖ζ l‖) * Real.exp (-δ * r / 4) := by
    intro k h X hX hh
    obtain ⟨hB, Wf, hfam₀⟩ := hFamL F m S hFL hamb hm hreg s V hs g1 hcold k (offsetBonds Y h) X hX
    obtain ⟨hB', Wf', hfam₀'⟩ := hFamL F' m S' hFL' hamb' hm hreg' s V' hs g1 hcold' k (offsetBonds Y' h) X hX
    have hfam := criticalFamily_of_le hfam₀ hr'r₀
    have hfam' := criticalFamily_of_le hfam₀' hr'r₀
    refine ⟨Wf, Wf', hB, hB', hfam, hfam', fun ζ hζ z hz => ?_⟩
    have hsz : 2 * (Ns * (s + ∑ l, ‖ζ l‖)) ≤ rL := by
      have h1 : s + ∑ l, ‖ζ l‖ ≤ 2 * e₀ := by linarith [hζ.le.trans hr'e]
      have h2 : Ns * (s + ∑ l, ‖ζ l‖) ≤ Ns * (2 * e₀) := mul_le_mul_of_nonneg_left h1 hNs0
      have h3 : e₀ * (4 * Ns + 4) = rL := by
        rw [he₀]
        field_simp
      nlinarith
    refine localNorm_diff_le_claim (Ca := Ca) (c := c₀) (Ct := Ct) (cT := cT) hLF₁ hLF₂.pos hdel hs hC hr hKf hfam
      hfam' hside hNmP (fun hbig => ?_) hζ hsz hz
    exact {
      odd_blockSide := hLF₁, blockSide_eq := hLeq, depth_eq := ht, ambient := hamb, ambient' := hamb',
      delta_pos := hdel, delta_le := hdel8, C_pos := hC,
      C₀_pos := hC, CT_pos := hCT, Cl_pos := hCl, Kp_pos := hKp, Kg_pos := hKg, s_pos := hs, r'_pos := hr'0,
      r'_le := hr'r, rL_le := hrc.le,
      radius_ge := hbig, extent_large := hside, extent_large' := hside',
      top_agree := fun ζ p i hp => complexTwistedTop_translate_eq hLF₁.pos hLeq ht hbig hagree hh ζ p i hp
      twistedBounds := hB, taylorBounds := hTp, family := hfam, family' := hfam'
      critical' := fun ζ hζ B' => complexFirstVariation_eq_zero hLF₂ hdel hB' hfam' hrc.le hr'r hrc₁' hreg₂ hAny₂
        hVan B' hζ
      projection := fun u => hPL F m S hFL hamb hm hreg s V hs g4 hcold u
      gaugeDiff := fun u z₀ hz₀ => hG' F m S hLF₁ (by omega) hamb hm hreg s V hs g5 hcold u z₀ hz₀
      firstVariation := fun W W' T T' B B' h1 h2 h3 h4 h5 h6 => hFV' F F' a m S S' s V V' Y Y' r (r - 202) hLeq ht
        hLF₁ (by rw [hFL]; exact hL3₀) hamb hamb' hm
        hreg hreg' hs g7 hcold hcold' hagree (by omega) (by omega) W W' T T' B B' h1 h2 h3 h4 h5 h6
      gaugeMap_agree := fun u u' h1 q h2 h3 => hGA' F F' m S S' s V V' Y Y' r (r - 202) hLeq ht hLF₁ hamb hamb' hm
        hreg hreg' hs g8 hcold hcold' hagree (by omega) (by omega) u u' h1 q h2 h3
      sites_iff := fun q hq => hSt F F' S S' V V' Y Y' r (r - 202 - 30) 0 hLeq ht hLF₁ (Nat.zero_le _) hagree
        (by omega) q hq
      localNormSq_eq := hNmP
      localVariation := fun W ζ B h1 h2 => hLFL F m S hFL hamb hm hreg s V hs g6 hcold k (offsetBonds Y h) X hX W ζ B
        (h1.trans hrcl) (h2.trans hrcl)
      sumExp₁ := fun y => by
        simpa using hcd₁ F S y
      sumExp₂ := fun y => hcd₂ F S y }
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [ht]
  have hside9 : ∀ i, F.extent i = 0 ∨ 2 * (7 + 2) + 2 < F.extent i := fun i => (hside i).imp id fun e => by omega
  have hac : ∀ {j : ℕ}, j ≤ F.top → ∀ {x : F.Site j × Fin 4}, x ∈ innerBonds S j →
      cellSupDist (enclosingCell x.1) Y ≤ 7 →
      (translateSite Y Y' x.1, x.2) ∈ innerBonds S' j := fun {j} hj {x} hx hd =>
    translate_mem_innerBonds hLF₁ hLeq ht hj hside9
      (fun q hq => hSt F F' S S' V V' Y Y' r (7 + 2) j hLeq ht hLF₁ hj hagree (by omega) q hq) hx hd
  have hcell : ∀ {z : F.Cell}, cellSupDist z Y ≤ 3 → ∀ {j : ℕ} {x : F.Site j}, enclosingCell x ∈ cellBall S z 4 →
      cellSupDist (enclosingCell x) Y ≤ 7 := by
    intro z hz j x hc
    have h1 : cellSupDist z (enclosingCell x) ≤ 4 := (Finset.mem_filter.1 hc).2
    have h2 := CoordinateSeminorms.cellSupDist_triangle (enclosingCell x) z Y
    rw [CoordinateSeminorms.cellSupDist_comm (enclosingCell x) z] at h2
    omega
  have hexp : 0 < Real.exp (-δ * r / 4) := Real.exp_pos _
  refine ⟨fun z hz => ?_, fun k h X ρ hk hρ hh hX T T' hT hT' m' e z hm' hz => ?_⟩
  · show localNorm S (referenceFieldChain S V) (chartMove U (chartTranslate Y Y' U') (-1)) (constOneWeights F) z ≤ _
    obtain ⟨W₀, W₀', hB₀, hB₀', f₀, f₀', hc₀⟩ := hkey 0 (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0)
      (fun l => l.elim0)
    have hx0 : ∑ l : Fin 0, |(0 : Fin 0 → ℝ) l| < r' := by simpa using hr'0
    have s₁' := chartAgreeOn_realFamilyChart hLF₁ hdel hB₀ f₀ hrc.le hr'r hrc₁' hreg₁ hx0 hU.mem_slice hU.norm_le
      (by rw [rotatedField_zero]; exact hU.critical)
    have s₂' := chartAgreeOn_realFamilyChart hLF₂ hdel hB₀' f₀' hrc.le hr'r hrc₁' hreg₂ hx0 hU'.mem_slice hU'.norm_le
      (by rw [rotatedField_zero]; exact hU'.critical)
    have hζ0 : ∑ l : Fin 0, ‖(ofRealVec (0 : Fin 0 → ℝ)) l‖ < r' := by simpa using hr'0
    have hclaim := hc₀ (ofRealVec 0) hζ0 z hz
    have hsum0 : ∑ l : Fin 0, ‖(ofRealVec (0 : Fin 0 → ℝ)) l‖ = 0 := by simp
    rw [hsum0, add_zero] at hclaim
    have hsymm : ∀ {F₁ : BlockFrame} {S₁ : Finset F₁.Cell} {A B : ChainChart F₁}, ChartEqOnBonds S₁ A B →
        ChartEqOnBonds S₁ B A := fun hAB =>
      ⟨fun x hx => (hAB.1 x hx).symm, fun j hj x hx => (hAB.2 j hj x hx).symm⟩
    have htr := localNorm_translate_congr (Y := Y) (Y' := Y') hamb hLF₁ (referenceFieldChain S V) z (hsymm s₁')
      (hsymm s₂')
      (fun x hx hc => hac (Nat.zero_le _) hx (hcell hz hc))
      (fun j hj x hx hc => hac (by omega) hx (hcell hz hc)) hn
    rw [htr]
    have hnn := localNorm_nonneg S (referenceFieldChain S V) (chartMove (W₀ (ofRealVec 0)).im
      (chartTranslate Y Y' (W₀' (ofRealVec 0)).im) (-1)) (constOneWeights F) z
    exact show localNorm S (referenceFieldChain S V)
        (chartMove (realFamilyChart W₀ 0) (chartTranslate Y Y' (realFamilyChart W₀' 0)) (-1))
        (constOneWeights F) z ≤ KA * s * Real.exp (-δ * r / 4) from by
      have : localNorm S (referenceFieldChain S V)
          (chartMove (W₀ (ofRealVec 0)).re (chartTranslate Y Y' (W₀' (ofRealVec 0)).re) (-1))
          (constOneWeights F) z ≤ KA * s * Real.exp (-δ * r / 4) := by linarith
      exact this
  · show localNorm S (referenceFieldChain S V) (chartMove (chartMixedDeriv T e)
      (chartTranslate Y Y' (chartMixedDeriv T' e)) (-1)) (constOneWeights F) z ≤ _
    obtain ⟨Wf, Wf', hB, hB', f, f', hc⟩ := hkey k h X hX hh
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hev0 : ∀ {K : ℝ}, 0 < K → ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < K := by
      intro K hK
      have hcont : Continuous fun x : Fin k → ℝ => ∑ l, |x l| := by fun_prop
      exact hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hK)
    have hρk : 0 < ρ / k := by positivity
    have hev1 : ∀ᶠ x : Fin k → ℝ in 𝓝 0, ∑ l, |x l| < r' ∧ ∀ l, |x l| < ρ / k := by
      filter_upwards [hev0 hr'0, hev0 hρk] with x h1 h2
      refine ⟨h1, fun l => lt_of_le_of_lt ?_ h2⟩
      exact Finset.single_le_sum (f := fun l => |x l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have hs₁ : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), ChartEqOnBonds S (T x) (realFamilyChart Wf x) := by
      filter_upwards [hev1] with x hx
      have := chartAgreeOn_realFamilyChart hLF₁ hdel hB f hrc.le hr'r hrc₁' hreg₁ hx.1 (hT.mem_gaugeSlice x hx.2)
        (hT.norm_le x hx.2) (hT.stationary x hx.2)
      exact ⟨fun y hy => (this.1 y hy).symm, fun j hj y hy => (this.2 j hj y hy).symm⟩
    have hs₂ : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), ChartEqOnBonds S' (T' x) (realFamilyChart Wf' x) := by
      filter_upwards [hev1] with x hx
      have := chartAgreeOn_realFamilyChart hLF₂ hdel hB' f' hrc.le hr'r hrc₁' hreg₂ hx.1 (hT'.mem_gaugeSlice x hx.2)
        (hT'.norm_le x hx.2) (hT'.stationary x hx.2)
      exact ⟨fun y hy => (this.1 y hy).symm, fun j hj y hy => (this.2 j hj y hy).symm⟩
    have htr := localNorm_translate_congr (Y := Y) (Y' := Y') hamb hLF₁ (referenceFieldChain S V) z
      (chartAgreeOn_chartMixedDeriv hs₁ e)
      (chartAgreeOn_chartMixedDeriv hs₂ e) (fun x hx hc => hac (Nat.zero_le _) hx (hcell hz hc))
      (fun j hj x hx hc => hac (by omega) hx (hcell hz hc)) hn
    rw [htr]
    have hBd : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r' →
        localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).re (chartTranslate Y Y' (Wf' ζ).re) (-1))
          (constOneWeights F) z +
        localNorm S (referenceFieldChain S V) (chartMove (Wf ζ).im (chartTranslate Y Y' (Wf' ζ).im) (-1))
          (constOneWeights F) z ≤
        KA * (1 + r') * Real.exp (-δ * r / 4) := by
      intro ζ hζ
      refine (hc ζ hζ z hz).trans (mul_le_mul_of_nonneg_right ?_ hexp.le)
      refine mul_le_mul_of_nonneg_left ?_ hKA0.le
      linarith
    have hmb := localNorm_mixedDeriv_diff_le hMix hLF₁ hamb f f' hr'0 (referenceFieldChain S V) Y Y' z
      (fun x hx hc => hac (Nat.zero_le _) hx (hcell hz hc))
      (fun j hj x hx hc => ⟨by omega, hac (by
        have hn' : F.top = F.depth + 1 := rfl
        omega) hx (hcell hz hc)⟩) hBd e hm'
    refine hmb.trans ?_
    have hq : 0 ≤ (((m' : ℝ) + 1) / r') ^ m' := by positivity
    have e1 : 2 * (KA * (1 + r') * Real.exp (-δ * r / 4)) * (((m' : ℝ) + 1) / r') ^ m' =
        (2 * (KA * (1 + r')) * (((m' : ℝ) + 1) / r') ^ m') * Real.exp (-δ * r / 4) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) hexp.le
end YangMills.Construction.BlockAverages
end
