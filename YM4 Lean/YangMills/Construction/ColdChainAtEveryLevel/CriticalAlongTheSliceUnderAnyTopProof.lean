import YangMills.Construction.ColdChainAtEveryLevel.CriticalAlongTheSliceUnderAnyTop
import YangMills.Construction.ColdChainAtEveryLevel.GaugeDirectionsOfARegularChainProof
import YangMills.Construction.ColdChainAtEveryLevel.KernelOfTheGaugeDirections
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SliceCriticality
open BlockAverages GaugeMap GaugeMotions GaugeMapLinear NearCellNorms GaugeDirectionKernel
variable {F : BlockFrame} {S : Finset F.Cell}
theorem gaugeGeneratorAtLevel_add (R : F.FieldChain) (U : ChainChart F) (ξ ξ' : F.Site 0 → imaginaryQuaternions) :
    ∀ (j : ℕ) (y : F.Site j), gaugeGeneratorAtLevel R U (ξ + ξ') j y =
      gaugeGeneratorAtLevel R U ξ j y + gaugeGeneratorAtLevel R U ξ' j y := by
  intro j
  induction j with
  | zero =>
    intro y
    rfl
  | succ j ih =>
    intro y
    simp only [gaugeGeneratorAtLevel, ih, mul_add, add_mul, Finset.sum_add_distrib, smul_add, pureComponent_add]
theorem gaugeGeneratorAtLevel_smul (R : F.FieldChain) (U : ChainChart F) (t : ℝ) (ξ : F.Site 0 → imaginaryQuaternions) :
    ∀ (j : ℕ) (y : F.Site j), gaugeGeneratorAtLevel R U (t • ξ) j y = t • gaugeGeneratorAtLevel R U ξ j y := by
  intro j
  induction j with
  | zero =>
    intro y
    rfl
  | succ j ih =>
    intro y
    simp only [gaugeGeneratorAtLevel, ih, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum, pureComponent_smul]
    rw [smul_comm t, smul_comm t]
theorem re_gaugeGeneratorAtLevel (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions) (j : ℕ)
    (y : F.Site j) : (gaugeGeneratorAtLevel R U ξ j y).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.re_gaugeGeneratorAtLevel <;> assumption
def cellValuesExtend (S : Finset F.Cell) : (↥S → imaginaryQuaternions) →ₗ[ℝ] (F.Cell → ℍ[ℝ]) := by
  classical exact
  { toFun := fun b y => if h : y ∈ S then (b ⟨y, h⟩ : ℍ[ℝ]) else 0
    map_add' := fun b b' => by
      funext y
      by_cases h : y ∈ S <;> simp [h]
    map_smul' := fun t b => by
      funext y
      by_cases h : y ∈ S <;> simp [h] }
def cellBumpLinear (S : Finset F.Cell) (V : F.GaugeField F.top) : (F.Cell → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) where
  toFun := cellBumpSection S V
  map_add' b b' := by
    funext s
    simp only [cellBumpSection, Pi.add_apply, PlaquetteLinearization.adjointAction_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' t b := by
    funext s
    simp only [cellBumpSection, Pi.smul_apply, PlaquetteLinearization.adjointAction_smul, RingHom.id_apply,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
theorem re_cellBumpSection (V : F.GaugeField F.top) (b : F.Cell → ℍ[ℝ]) (hb : ∀ y, (b y).re = 0) (s : F.Site 0) :
    (cellBumpSection S V b s).re = 0 := by
  have : quaternionReLinear (cellBumpSection S V b s) = 0 := by
    simp only [cellBumpSection, map_sum, map_smul]
    refine Finset.sum_eq_zero fun y _ => ?_
    have e : quaternionReLinear (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y s) (b y)) = 0 := by
      show (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y s) (b y)).re = 0
      rw [PlaquetteLinearization.adjointAction_re, hb y]
    rw [e, smul_zero]
  exact this
theorem re_cellValuesExtend (b : ↥S → imaginaryQuaternions) (y : F.Cell) : (cellValuesExtend S b y).re = 0 := by
  classical
  show (if h : y ∈ S then ((b ⟨y, h⟩ : imaginaryQuaternions) : ℍ[ℝ]) else 0).re = 0
  by_cases h : y ∈ S
  · rw [dif_pos h]
    exact (b ⟨y, h⟩).2
  · rw [dif_neg h]
    rfl
def sectionCoeLinear (F : BlockFrame) : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) :=
  LinearMap.compLeft imaginaryQuaternions.subtype _
def formCoeLinear (F : BlockFrame) :
    (F.Site 0 → Fin 4 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → ℍ[ℝ]) :=
  LinearMap.compLeft (LinearMap.compLeft imaginaryQuaternions.subtype _) _
def sectionPureLinear (F : BlockFrame) : (F.Site 0 → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → imaginaryQuaternions) :=
  LinearMap.compLeft (pureComponentCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions).toLinearMap _
def topGeneratorLinear (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.FieldChain) (U : ChainChart F) :
    (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (↥S → imaginaryQuaternions) where
  toFun ξ y := pureComponentCLM (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
    (gaugeGeneratorAtLevel R U ξ F.top y))
  map_add' ξ ξ' := by
    funext y
    simp only [Pi.add_apply]
    rw [← map_add, gaugeGeneratorAtLevel_add, PlaquetteLinearization.adjointAction_add]
  map_smul' t ξ := by
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul, gaugeGeneratorAtLevel_smul, PlaquetteLinearization.adjointAction_smul]
section LocalNorm
variable (R : F.FieldChain) (U : ChainChart F)
theorem localNormSq_nonneg (B : Finset F.Cell) :
    0 ≤ localNormSq S B R U (oneSiteWeights F) := by
  unfold localNormSq
  positivity
theorem localNorm_sq {z : F.Cell} :
    localNorm S R U (oneSiteWeights F) z ^ 2 = localNormSq S (cellBall S z 3) R U (oneSiteWeights F) := by
  unfold localNorm
  exact Real.sq_sqrt (localNormSq_nonneg R U _)
theorem mem_cellBall_self {z : F.Cell} (hz : z ∈ S) : z ∈ cellBall S z 3 := by apply _root_.YangMills.Construction.GaugedCriticality.mem_cellBall_self <;> assumption
theorem sum_fine_rpow_le_localNorm {z : F.Cell} (hz : z ∈ S) :
    ∑ c ∈ bondsOver S {z} 0, ‖U.fine c.1 c.2‖ ^ (4 : ℝ) ≤ localNorm S R U (oneSiteWeights F) z ^ (4 : ℝ) := by
  classical
  set N := localNorm S R U (oneSiteWeights F) z with hN
  have hsq := localNorm_sq (S := S) R U (z := z)
  set Q := ∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 with hQ
  have h1 : Real.sqrt Q ≤ N ^ 2 := by
    rw [hsq]
    unfold localNormSq
    have a : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have b : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have h2 : Q ≤ N ^ 4 := by
    have := (Real.sqrt_le_left (by positivity)).1 h1
    have e := Real.sqrt_le_sqrt (h := (le_refl Q))
    have h3 := Real.sqrt_le_iff.1 h1
    calc Q ≤ (N ^ 2) ^ 2 := h3.2
      _ = N ^ 4 := by ring
  have hsub : bondsOver S {z} 0 ⊆ bondsOver S (cellBall S z 3) 0 := by
    intro b hb
    simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hb ⊢
    exact ⟨hb.1, by rw [hb.2]; exact mem_cellBall_self hz⟩
  have h3 : ∑ c ∈ bondsOver S {z} 0, ‖U.fine c.1 c.2‖ ^ (4 : ℝ) ≤ Q := by
    have e : ∀ c ∈ bondsOver S {z} 0,
        ‖U.fine c.1 c.2‖ ^ (4 : ℝ) = (oneSiteWeights F 0 c.1 * ‖U.fine c.1 c.2‖) ^ 4 := by
      intro c _
      rw [show oneSiteWeights F 0 c.1 = 1 from rfl, one_mul]
      exact_mod_cast Real.rpow_natCast _ 4
    rw [Finset.sum_congr rfl e]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have e4 : N ^ (4 : ℝ) = N ^ 4 := by exact_mod_cast Real.rpow_natCast N 4
  rw [e4]
  linarith
theorem finLpNorm_curl_le_localNorm {z : F.Cell} (hz : z ∈ S) :
    finLpNorm (plaquettesOver S {z} 0) 2 (fun p => ‖linearizedCurl (R 0) U.fine p‖) ≤
      localNorm S R U (oneSiteWeights F) z := by
  classical
  set N := localNorm S R U (oneSiteWeights F) z with hN
  have h0 : 0 ≤ N := Real.sqrt_nonneg _
  refine finLpNorm_le_of_sum_rpow_le _ (by norm_num) (fun _ _ => norm_nonneg _) h0 ?_
  have e2 : N ^ (2 : ℝ) = N ^ 2 := by exact_mod_cast Real.rpow_natCast N 2
  rw [e2, localNorm_sq]
  unfold localNormSq
  have hsub : plaquettesOver S {z} 0 ⊆ plaquettesOver S (cellBall S z 3) 0 := by
    intro b hb
    simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton] at hb ⊢
    exact ⟨hb.1, by rw [hb.2]; exact mem_cellBall_self hz⟩
  have e : ∀ c ∈ plaquettesOver S {z} 0, ‖linearizedCurl (R 0) U.fine c‖ ^ (2 : ℝ) =
      (oneSiteWeights F 0 c.1 * ‖linearizedCurl (R 0) U.fine c‖) ^ 2 := by
    intro c _
    rw [show oneSiteWeights F 0 c.1 = 1 from rfl, one_mul]
    exact_mod_cast Real.rpow_natCast _ 2
  rw [Finset.sum_congr rfl e]
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun c => (oneSiteWeights F 0 c.1 * ‖linearizedCurl (R 0) U.fine c‖) ^ 2) fun _ _ _ => by positivity
  have a : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have b : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem norm_coarse_le_localNorm {z : F.Cell} (hz : z ∈ S) {j : ℕ} (hj : j + 1 < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ bondsOver S {z} (j + 1)) :
    ‖U.coarse j c.1 c.2‖ ≤ localNorm S R U (oneSiteWeights F) z := by
  classical
  set N := localNorm S R U (oneSiteWeights F) z with hN
  have h0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsq := localNorm_sq (S := S) R U (z := z)
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [hsq]
  unfold localNormSq
  have hjr : j ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
  have hin : c ∈ bondsOver S (cellBall S z 3) (j + 1) := by
    simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hc ⊢
    exact ⟨hc.1, by rw [hc.2]; exact mem_cellBall_self hz⟩
  have h1 : (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.single_le_sum
      (f := fun c : F.Site (j + 1) × Fin 4 => (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
      (fun _ _ => by positivity) hin
  have h2 := Finset.single_le_sum (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hjr
  have a : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have b : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
      (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have e : (oneSiteWeights F (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 = ‖U.coarse j c.1 c.2‖ ^ 2 := by
    rw [show oneSiteWeights F (j + 1) c.1 = 1 from rfl, one_mul]
  linarith
end LocalNorm
theorem coe_pureComponentCLM_of_re (x : ℍ[ℝ]) (h : x.re = 0) :
    ((pureComponentCLM x : imaginaryQuaternions) : ℍ[ℝ]) = x := by
  rw [coe_pureComponentCLM, _root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero h]
theorem re_covariantDiff (R0 : F.GaugeField 0) (η : F.Site 0 → imaginaryQuaternions) (x : F.Site 0) (i : Fin 4) :
    (covariantDiff R0 (fun x => (η x : ℍ[ℝ])) x i).re = 0 := by apply _root_.YangMills.Construction.GaugeDirections.re_covariantDiff <;> assumption
def directionLinear (R0 : F.GaugeField 0)
    (H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions)) :
    (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → ℍ[ℝ]) :=
  formCoeLinear F ∘ₗ H - covariantDiffLinear R0 ∘ₗ sectionCoeLinear F
theorem directionLinear_apply (R0 : F.GaugeField 0)
    (H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions))
    (η : F.Site 0 → imaginaryQuaternions) (x : F.Site 0) (i : Fin 4) :
    directionLinear R0 H η x i = - covariantDiff R0 (fun x => (η x : ℍ[ℝ])) x i + H η x i := by
  show ((H η x i : imaginaryQuaternions) : ℍ[ℝ]) - covariantDiff R0 (fun x => (η x : ℍ[ℝ])) x i = _
  abel
theorem exists_gauge_direction (hodd : Odd F.blockSide) (V : F.GaugeField F.top) (R : F.FieldChain)
    (hR0 : R 0 = referenceFieldChain S V 0) (U : ChainChart F)
    (H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions))
    (hMF : ∀ u : F.Site 0 → Fin 4 → ℍ[ℝ], CellMeanFree S V (gaugeMap S V (R 0) u))
    (hker : ∀ (σ β η : F.Site 0 → imaginaryQuaternions) (b : F.Cell → ℍ[ℝ]),
      (∀ x, ((β x : imaginaryQuaternions) : ℍ[ℝ]) = cellBumpSection S V b x) →
      (∀ x, ((η x : imaginaryQuaternions) : ℍ[ℝ]) = σ x + β x) →
      CellMeanFree S V (fun x => (σ x : ℍ[ℝ])) → (∀ y ∈ S, gaugeGeneratorAtLevel R U η F.top y = 0) →
      (∀ x ∈ sitesOfCells S 0, gaugeMap S V (R 0) (directionLinear (R 0) H η) x = 0) →
      (∀ x ∈ sitesOfCells S 0, ((σ x : imaginaryQuaternions) : ℍ[ℝ]) = 0) ∧ ∀ y ∈ S, b y = 0)
    (u₀ : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    ∃ η : F.Site 0 → imaginaryQuaternions, (∀ y ∈ S, gaugeGeneratorAtLevel R U η F.top y = 0) ∧
      ∀ x ∈ sitesOfCells S 0, gaugeMap S V (R 0) (directionLinear (R 0) H η) x =
        gaugeMap S V (R 0) (fun x i => u₀ x i) x := by
  classical
  set A₀ := sitesOfCells S 0 with hA₀
  set Z := meanFreeSubmodule S V hodd with hZ
  set secL : (↥Z × (↥S → imaginaryQuaternions)) →ₗ[ℝ] (F.Site 0 → imaginaryQuaternions) :=
    sectionPureLinear F ∘ₗ (_root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ ∘ₗ Z.subtype ∘ₗ LinearMap.fst ℝ _ _ +
      cellBumpLinear S V ∘ₗ cellValuesExtend S ∘ₗ LinearMap.snd ℝ _ _) with hsec
  set f₁ : (↥Z × (↥S → imaginaryQuaternions)) →ₗ[ℝ] (↥A₀ → ℍ[ℝ]) :=
    restrictToSites A₀ ∘ₗ gaugeMapLinear S V (R 0) ∘ₗ directionLinear (R 0) H ∘ₗ secL with hf₁
  have hpure : ∀ (g : F.Site 0 → Fin 4 → ℍ[ℝ]), (∀ x i, (g x i).re = 0) →
      restrictToSites A₀ (gaugeMapLinear S V (R 0) g) ∈ Z := by
    intro g hg
    refine ⟨?_, fun a => re_gaugeMap S V (R 0) g hg a⟩
    refine cellMeanFree_congr S V hodd _ _ ?_ (hMF g)
    intro y hy
    exact (extendByZero_apply_mem A₀ (restrictToSites A₀ (gaugeMapLinear S V (R 0) g)) ⟨y, hy⟩).symm
  have hformre : ∀ (η : F.Site 0 → imaginaryQuaternions) x i, (directionLinear (R 0) H η x i).re = 0 := by
    intro η x i
    rw [directionLinear_apply]
    have h1 := re_covariantDiff (R 0) η x i
    have h2 : ((H η x i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (H η x i).2
    have e : ∀ p q : ℍ[ℝ], (-p + q).re = -p.re + q.re := fun _ _ => rfl
    rw [e, h1, h2]
    simp
  have hmem : ∀ p, f₁ p ∈ Z := fun p => hpure _ (hformre (secL p))
  set Φ : (↥Z × (↥S → imaginaryQuaternions)) →ₗ[ℝ] (↥Z × (↥S → imaginaryQuaternions)) :=
    (LinearMap.codRestrict Z f₁ hmem).prod (topGeneratorLinear S V R U ∘ₗ secL) with hΦ
  have hcoe : ∀ (p : ↥Z × (↥S → imaginaryQuaternions)) x, ((secL p x : imaginaryQuaternions) : ℍ[ℝ]) =
      _root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 x + cellBumpSection S V (cellValuesExtend S p.2) x := by
    intro p x
    have h1 : (_root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 x).re = 0 := re_extendByZero A₀ p.1.1 p.1.2.2 x
    have h2 := re_cellBumpSection (S := S) V (cellValuesExtend S p.2) (re_cellValuesExtend p.2) x
    have e : ∀ a b : ℍ[ℝ], (a + b).re = a.re + b.re := fun _ _ => rfl
    show ((pureComponentCLM (_root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 x + cellBumpSection S V (cellValuesExtend S p.2) x) :
      imaginaryQuaternions) : ℍ[ℝ]) = _
    exact coe_pureComponentCLM_of_re _ (by rw [e, h1, h2, add_zero])
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro p hp
    have h1 : LinearMap.codRestrict Z f₁ hmem p = 0 := congrArg Prod.fst hp
    have h2 : topGeneratorLinear S V R U (secL p) = 0 := congrArg Prod.snd hp
    set σ : F.Site 0 → imaginaryQuaternions := fun x => pureComponentCLM (_root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 x) with hσ
    set β : F.Site 0 → imaginaryQuaternions :=
      fun x => pureComponentCLM (cellBumpSection S V (cellValuesExtend S p.2) x) with hβ
    have hσc : ∀ x, ((σ x : imaginaryQuaternions) : ℍ[ℝ]) = _root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 x := fun x =>
      coe_pureComponentCLM_of_re _ (re_extendByZero A₀ p.1.1 p.1.2.2 x)
    have hβc : ∀ x, ((β x : imaginaryQuaternions) : ℍ[ℝ]) = cellBumpSection S V (cellValuesExtend S p.2) x :=
      fun x => coe_pureComponentCLM_of_re _ (re_cellBumpSection V _ (re_cellValuesExtend p.2) x)
    have hσf : (fun x => ((σ x : imaginaryQuaternions) : ℍ[ℝ])) = _root_.YangMills.Construction.GaugeMapLinear.extendByZero A₀ p.1.1 := funext hσc
    have hgen : ∀ y ∈ S, gaugeGeneratorAtLevel R U (secL p) F.top y = 0 := by
      intro y hy
      have h3 := congrFun h2 ⟨y, hy⟩
      have h4 : pureComponent (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
          (gaugeGeneratorAtLevel R U (secL p) F.top y)) = 0 :=
        congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) h3
      have hre : (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
          (gaugeGeneratorAtLevel R U (secL p) F.top y)).re = 0 := by
        rw [PlaquetteLinearization.adjointAction_re]
        exact re_gaugeGeneratorAtLevel R U _ _ _
      rw [_root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero hre] at h4
      have h5 := GaugeMapLinear.adjointAction_inv_adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
        (gaugeGeneratorAtLevel R U (secL p) F.top y)
      rw [h4, inv_inv] at h5
      simpa [_root_.YangMills.Construction.BlockAverages.adjointAction] using h5.symm
    have hmap : ∀ x ∈ sitesOfCells S 0, gaugeMap S V (R 0) (directionLinear (R 0) H (secL p)) x = 0 := by
      intro x hx
      have h3 := congrArg (fun w : ↥Z => w.1 ⟨x, hx⟩) h1
      exact h3
    obtain ⟨k1, k2⟩ := hker σ β (secL p) (cellValuesExtend S p.2) hβc
      (fun x => by rw [hcoe, hσc, hβc]) (by rw [hσf]; exact p.1.2.1) hgen hmap
    refine Prod.ext (Subtype.ext (funext fun a => ?_)) (funext fun y => Subtype.ext ?_)
    · have := k1 a a.2
      rw [hσc, extendByZero_apply_mem A₀ p.1.1 a] at this
      exact this
    · have h3 := k2 y y.2
      have e : cellValuesExtend S p.2 y = ((p.2 y : imaginaryQuaternions) : ℍ[ℝ]) := by
        show (if h : (y : F.Cell) ∈ S then ((p.2 ⟨y, h⟩ : imaginaryQuaternions) : ℍ[ℝ]) else 0) = _
        rw [dif_pos y.2]
      rw [e] at h3
      exact h3
  have hsurj : Function.Surjective Φ := LinearMap.injective_iff_surjective.1 hinj
  have htarget : restrictToSites A₀ (gaugeMapLinear S V (R 0) (fun x i => u₀ x i)) ∈ Z :=
    hpure _ fun x i => (u₀ x i).2
  obtain ⟨p, hp⟩ := hsurj (⟨_, htarget⟩, 0)
  have h1 : LinearMap.codRestrict Z f₁ hmem p = ⟨_, htarget⟩ := congrArg Prod.fst hp
  have h2 : topGeneratorLinear S V R U (secL p) = 0 := congrArg Prod.snd hp
  refine ⟨secL p, ?_, ?_⟩
  · intro y hy
    have h3 := congrFun h2 ⟨y, hy⟩
    have h4 : pureComponent (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
        (gaugeGeneratorAtLevel R U (secL p) F.top y)) = 0 :=
      congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) h3
    have hre : (_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
        (gaugeGeneratorAtLevel R U (secL p) F.top y)).re = 0 := by
      rw [PlaquetteLinearization.adjointAction_re]
      exact re_gaugeGeneratorAtLevel R U _ _ _
    rw [_root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero hre] at h4
    have h5 := GaugeMapLinear.adjointAction_inv_adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
      (gaugeGeneratorAtLevel R U (secL p) F.top y)
    rw [h4, inv_inv] at h5
    simpa [_root_.YangMills.Construction.BlockAverages.adjointAction] using h5.symm
  · intro x hx
    have h3 := congrArg (fun w : ↥Z => w.1 ⟨x, hx⟩) h1
    exact h3
theorem isChartCurve_chartMove (S : Finset F.Cell) (U A A' : ChainChart F) (h : ChartEqOnBonds S A A') :
    IsChartCurve S (chartMove U A) U A' := by
  refine ⟨⟨fun b _ => by simp [chartMove], fun j _ b _ => by simp [chartMove]⟩, fun b hb => ?_, fun j hj b hb => ?_⟩
  · have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const (A.fine b.1 b.2)).const_add (U.fine b.1 b.2)
    rw [← h.1 b hb]
    simpa [chartMove] using h1
  · have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const (A.coarse j b.1 b.2)).const_add (U.coarse j b.1 b.2)
    rw [← h.2 j hj b hb]
    simpa [chartMove] using h1
theorem isCriticalAlong_of_gauge {a : ℝ} {V W : F.GaugeField F.top} {R : F.FieldChain} {U : ChainChart F}
    (D : ChainChart F → ℝ) (hDadd : ∀ A A' : ChainChart F, D (chartSum A A') = D A + D A')
    (hDc : ∀ (C : ℝ → ChainChart F) (A : ChainChart F), IsChartCurve S C U A →
      HasDerivAt (fun τ => chartAction a S R (C τ) W) (D A) 0)
    (hcrit : ∀ A : ChainChart F, InGaugeSlice S V (R 0) A.fine → IsStationaryAlong a S R W U A)
    (H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions))
    (η : F.Site 0 → imaginaryQuaternions) (AG : ChainChart F)
    (hAG : ∀ b ∈ innerBonds S 0, ((AG.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      directionLinear (R 0) H η b.1 b.2)
    (hAGc : IsStationaryAlong a S R W U AG) (A : ChainChart F)
    (hsame : ∀ x ∈ sitesOfCells S 0, gaugeMap S V (R 0) (directionLinear (R 0) H η) x =
      gaugeMap S V (R 0) (fun x i => A.fine x i) x) :
    IsStationaryAlong a S R W U A := by
  have hre : ∀ x i, (directionLinear (R 0) H η x i).re = 0 := by
    intro x i
    rw [directionLinear_apply]
    have h1 := re_covariantDiff (R 0) η x i
    have h2 : ((H η x i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (H η x i).2
    have e : ∀ p q : ℍ[ℝ], (-p + q).re = -p.re + q.re := fun _ _ => rfl
    rw [e, h1, h2]
    simp
  set G : F.Site 0 → Fin 4 → imaginaryQuaternions := fun x i => pureComponentCLM (directionLinear (R 0) H η x i)
    with hG
  have hGc : ∀ x i, ((G x i : imaginaryQuaternions) : ℍ[ℝ]) = directionLinear (R 0) H η x i :=
    fun x i => coe_pureComponentCLM_of_re _ (hre x i)
  set A'' : ChainChart F := ⟨G, AG.coarse⟩ with hA''
  set A' : ChainChart F := ⟨fun x i => A.fine x i - G x i, fun j y i => A.coarse j y i - AG.coarse j y i⟩ with hA'
  have hslice : InGaugeSlice S V (R 0) A'.fine := by
    intro s hs
    have e : (fun x i => ((A'.fine x i : imaginaryQuaternions) : ℍ[ℝ])) =
        fun x i => (1 : ℝ) • ((A.fine x i : imaginaryQuaternions) : ℍ[ℝ]) +
          (-1 : ℝ) • directionLinear (R 0) H η x i := by
      funext x i
      show ((A.fine x i - G x i : imaginaryQuaternions) : ℍ[ℝ]) = _
      rw [Submodule.coe_sub, hGc]
      simp [sub_eq_add_neg]
    rw [e, gaugeMap_linComb]
    simp only [one_smul, neg_one_smul]
    rw [hsame s hs]
    abel
  have d1 : D A' = 0 :=
    (hDc (chartMove U A') A' (isChartCurve_chartMove S U A' A' ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩)).unique
      (hcrit A' hslice)
  have hs'' : ChartEqOnBonds S A'' AG :=
    ⟨fun b hb => Subtype.ext (by
      show ((G b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) = _
      rw [hGc, hAG b hb]), fun _ _ _ _ => rfl⟩
  have d2 : D AG = 0 :=
    (hDc (chartMove U AG) AG (isChartCurve_chartMove S U AG AG ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩)).unique hAGc
  have d3 : D A'' = D AG :=
    (hDc (chartMove U A'') A'' (isChartCurve_chartMove S U A'' A'' ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩)).unique
      (hDc (chartMove U A'') AG (isChartCurve_chartMove S U A'' AG hs''))
  have e : chartSum A' A'' = A := by
    unfold chartSum chartMove
    simp only [one_smul, hA', hA'', sub_add_cancel]
  have d4 : D A = 0 := by
    rw [← e, hDadd, d1, d3, d2, add_zero]
  have := hDc (chartMove U A) A (isChartCurve_chartMove S U A A ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩)
  rw [d4] at this
  exact this
theorem exists_small_constant {c₀ C₀ C₃ C₄ C₅ Cm c₁ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hC₃ : 0 < C₃)
    (hC₄ : 0 < C₄) (hC₅ : 0 < C₅) (hCm : 0 < Cm) (hc₁ : 0 < c₁) :
    ∃ c : ℝ, 0 < c ∧ c ≤ c₁ ∧ 2 * c ≤ c₀ ∧ ∀ s β : ℝ, 0 ≤ s → s ≤ c → 0 ≤ β → β ≤ c →
      Cm * (s + β) * C₅ ≤ 1 / 2 ∧ 2 * (Cm * (s + β) * C₄) ≤ 1 ∧ s ≤ 1 ∧ 2 * β ≤ 1 ∧ C₄ * s ≤ 1 / 8 ∧
      (C₃ * (C₅ * 2) + C₅) * (2 * (Cm * (s + β) * C₄)) ≤ 1 / 8 ∧
      (C₃ + 1) * (1356 * C₀ * (2 * β) * (C₄ + C₅ + 1)) ≤ 1 / 8 := by
  set K₂ : ℝ := C₃ * (C₅ * 2) + C₅ with hK₂
  set Gc : ℝ := C₄ + C₅ + 1 with hGc
  set M : ℝ := 8 + 2 / c₀ + 4 * Cm * C₅ + 4 * Cm * C₄ + 8 * C₄ + 32 * K₂ * Cm * C₄ +
    16 * 1356 * (C₃ + 1) * C₀ * Gc with hMdef
  have hK₂0 : 0 ≤ K₂ := by positivity
  have t2 : 0 ≤ 2 / c₀ := by positivity
  have t3 : 0 ≤ 4 * Cm * C₅ := by positivity
  have t4 : 0 ≤ 4 * Cm * C₄ := by positivity
  have t5 : 0 ≤ 8 * C₄ := by positivity
  have t6 : 0 ≤ 32 * K₂ * Cm * C₄ := by positivity
  have t7 : 0 ≤ 16 * 1356 * (C₃ + 1) * C₀ * Gc := by positivity
  have hMpos : 0 < M := by rw [hMdef]; linarith
  set c : ℝ := min c₁ (1 / M) with hc
  have hc0 : 0 < c := lt_min hc₁ (by positivity)
  have hcM1 : c * M ≤ 1 := by
    have : c ≤ 1 / M := min_le_right _ _
    calc c * M ≤ 1 / M * M := mul_le_mul_of_nonneg_right this hMpos.le
      _ = 1 := by field_simp
  have hX : ∀ X : ℝ, 0 ≤ X → X ≤ M → X * c ≤ 1 := fun X h0 h1 =>
    calc X * c ≤ M * c := mul_le_mul_of_nonneg_right h1 hc0.le
      _ = c * M := mul_comm _ _
      _ ≤ 1 := hcM1
  have x1 : 8 * c ≤ 1 := hX 8 (by norm_num) (by rw [hMdef]; linarith)
  have x2 : 2 / c₀ * c ≤ 1 := hX _ t2 (by rw [hMdef]; linarith)
  have x3 : 4 * Cm * C₅ * c ≤ 1 := hX _ t3 (by rw [hMdef]; linarith)
  have x4 : 4 * Cm * C₄ * c ≤ 1 := hX _ t4 (by rw [hMdef]; linarith)
  have x5 : 8 * C₄ * c ≤ 1 := hX _ t5 (by rw [hMdef]; linarith)
  have x6 : 32 * K₂ * Cm * C₄ * c ≤ 1 := hX _ t6 (by rw [hMdef]; linarith)
  have x7 : 16 * 1356 * (C₃ + 1) * C₀ * Gc * c ≤ 1 := hX _ t7 (by rw [hMdef]; linarith)
  have c2c : 2 * c ≤ c₀ := by
    have : 2 / c₀ * c = 2 * c / c₀ := by ring
    rw [this, div_le_one hc₀] at x2
    exact x2
  refine ⟨c, hc0, min_le_left _ _, c2c, fun s β hs hsc hβ hβc => ?_⟩
  set e : ℝ := s + β with he
  have he2 : e ≤ 2 * c := by rw [he]; linarith
  have hCmC : 0 ≤ Cm * C₅ := by positivity
  have hCmD : 0 ≤ Cm * C₄ := by positivity
  have n1 : Cm * e * C₅ ≤ 1 / 2 := by
    have : (Cm * C₅) * e ≤ (Cm * C₅) * (2 * c) := mul_le_mul_of_nonneg_left he2 hCmC
    linarith
  have n2 : Cm * e * C₄ ≤ Cm * C₄ * (2 * c) := by
    have : (Cm * C₄) * e ≤ (Cm * C₄) * (2 * c) := mul_le_mul_of_nonneg_left he2 hCmD
    linarith
  have n3 : 2 * (Cm * e * C₄) ≤ 1 := by linarith
  have n4 : s ≤ 1 := by linarith
  have n5 : 2 * β ≤ 1 := by linarith
  have n6 : C₄ * s ≤ 1 / 8 := by
    have : C₄ * s ≤ C₄ * c := mul_le_mul_of_nonneg_left hsc hC₄.le
    linarith
  have n7 : K₂ * (2 * (Cm * e * C₄)) ≤ 1 / 8 := by
    have : K₂ * (2 * (Cm * e * C₄)) ≤ K₂ * (2 * (Cm * C₄ * (2 * c))) :=
      mul_le_mul_of_nonneg_left (by linarith) hK₂0
    linarith
  have n8 : (C₃ + 1) * (1356 * C₀ * (2 * β) * Gc) ≤ 1 / 8 := by
    have hA2 : 2 * β ≤ 2 * c := by linarith
    have hp : 0 ≤ (C₃ + 1) * (1356 * C₀ * Gc) := by positivity
    have : ((C₃ + 1) * (1356 * C₀ * Gc)) * (2 * β) ≤ ((C₃ + 1) * (1356 * C₀ * Gc)) * (2 * c) :=
      mul_le_mul_of_nonneg_left hA2 hp
    linarith
  exact ⟨n1, n3, n4, n5, n6, n7, n8⟩
theorem isCriticalAlong_of_sliceHypotheses (hodd : Odd F.blockSide) {a s e Cm C₀ C₃ C₄ C₅ A₀ : ℝ}
    {V W : F.GaugeField F.top} {U : ChainChart F}
    (hs : 0 ≤ s) (he : 0 ≤ e) (hCm : 0 ≤ Cm) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    (hA0 : 0 ≤ A₀) (facts : GaugeSliceHypotheses S V s C₃ C₄ C₅)
    (hu : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, ‖U.fine b.1 b.2‖ ^ (4 : ℝ) ≤ A₀ ^ (4 : ℝ))
    (hcu : ∀ z ∈ S, finLpNorm (plaquettesOver S {z} 0) 2
      (fun p => ‖linearizedCurl (referenceFieldChain S V 0) U.fine p‖) ≤ A₀)
    (D : ChainChart F → ℝ) (hDadd : ∀ A A' : ChainChart F, D (chartSum A A') = D A + D A')
    (hDc : ∀ (C : ℝ → ChainChart F) (A : ChainChart F), IsChartCurve S C U A →
      HasDerivAt (fun τ => chartAction a S (referenceFieldChain S V) (C τ) W) (D A) 0)
    (H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions))
    (hGd : ∀ ξ : F.Site 0 → imaginaryQuaternions,
        (∀ y ∈ S, gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ F.top y = 0) →
        ∃ A : ChainChart F, (∀ b ∈ innerBonds S 0, ((A.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
            - covariantDiff (referenceFieldChain S V 0) (fun x => ξ x) b.1 b.2 + H ξ b.1 b.2) ∧
          IsStationaryAlong a S (referenceFieldChain S V) W U A)
    (hHb : ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ b ∈ innerBonds S 0, ‖H ξ b.1 b.2‖ ≤
        C₀ * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖))
    (hHc : ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ p ∈ innerPlaquettes S 0,
        ‖linearizedCurl (referenceFieldChain S V 0) (H ξ) p‖ ≤
        C₀ * ((‖linearizedCurl (referenceFieldChain S V 0) U.fine p‖ +
            plaquetteBondSum (fun x i => ‖U.fine x i‖) p ^ 2) *
            plaquetteCornerSum (fun x => ‖ξ x‖) p +
          plaquetteBondSum (fun x i => ‖U.fine x i‖) p *
            plaquetteBondSum (fun x i => ‖covariantDiff (referenceFieldChain S V 0) (fun x => ξ x) x i‖) p))
    (hMF : ∀ u : F.Site 0 → Fin 4 → ℍ[ℝ], CellMeanFree S V (gaugeMap S V (referenceFieldChain S V 0) u))
    (hCom : ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ y ∈ S,
        ‖_root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (cellCentre 0 y))⁻¹
            (gaugeGeneratorAtLevel (referenceFieldChain S V) U ξ F.top y) -
            frameCellMean S V y (fun x => ξ x)‖ ≤
          Cm * e * (cellSiteNorm 4 S (fun _ => 1) (fun x => ξ x) y / (cellSideLength F : ℝ)))
    (n1 : Cm * e * C₅ ≤ 1 / 2) (n3 : 2 * (Cm * e * C₄) ≤ 1) (n4 : s ≤ 1) (n5 : A₀ ≤ 1) (n6 : C₄ * s ≤ 1 / 8)
    (n7 : (C₃ * (C₅ * 2) + C₅) * (2 * (Cm * e * C₄)) ≤ 1 / 8)
    (n8 : (C₃ + 1) * (1356 * C₀ * A₀ * (C₄ + C₅ + 1)) ≤ 1 / 8)
    (hcrit : ∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
      IsStationaryAlong a S (referenceFieldChain S V) W U A) (A : ChainChart F) :
    IsStationaryAlong a S (referenceFieldChain S V) W U A := by
  have hker : ∀ (σ β η : F.Site 0 → imaginaryQuaternions) (b : F.Cell → ℍ[ℝ]),
      (∀ x, ((β x : imaginaryQuaternions) : ℍ[ℝ]) = cellBumpSection S V b x) →
      (∀ x, ((η x : imaginaryQuaternions) : ℍ[ℝ]) = σ x + β x) →
      CellMeanFree S V (fun x => (σ x : ℍ[ℝ])) →
      (∀ y ∈ S, gaugeGeneratorAtLevel (referenceFieldChain S V) U η F.top y = 0) →
      (∀ x ∈ sitesOfCells S 0, gaugeMap S V (referenceFieldChain S V 0)
        (directionLinear (referenceFieldChain S V 0) H η) x = 0) →
      (∀ x ∈ sitesOfCells S 0, ((σ x : imaginaryQuaternions) : ℍ[ℝ]) = 0) ∧ ∀ y ∈ S, b y = 0 := by
    intro σ β η b hβ hη hσ hgen hmap
    refine eq_zero_of_mem_kernel hodd hs he hCm hC₀ hC₃ hC₄ hC₅ hA0 facts σ β η b hβ hη hσ (H η) U.fine
      (fun c' hc' => hHb η c' hc') (fun p hp => hHc η p hp) hu hcu ?_ ?_ n1 n3 n4 n5 n6 n7 n8
    · intro y hy
      have h1 := hCom η y hy
      rw [hgen y hy] at h1
      simpa [_root_.YangMills.Construction.BlockAverages.adjointAction, norm_sub_rev] using h1
    · intro x hx
      have e1 : (fun x i => - covariantDiff (referenceFieldChain S V 0) (fun x => (η x : ℍ[ℝ])) x i +
          (H η x i : ℍ[ℝ])) = directionLinear (referenceFieldChain S V 0) H η := by
        funext y i
        rw [directionLinear_apply]
      rw [e1]
      exact hmap x hx
  obtain ⟨η, hg, hsame⟩ := exists_gauge_direction hodd V (referenceFieldChain S V) rfl U H hMF hker A.fine
  obtain ⟨AG, hAGu, hAGc⟩ := hGd η hg
  exact isCriticalAlong_of_gauge D hDadd hDc hcrit H η AG (fun b hb => by rw [hAGu b hb, directionLinear_apply])
    hAGc A hsame
set_option maxHeartbeats 1000000 in
theorem sliceCriticalImpliesCritical (hV : regularChainFirstVariationStatement)
    (hG : regularChainGaugeDirectionsStatement) (hR : smallChartIsRegularStatement)
    (hM : compositeMeanStatement) (hB : cellBumpBoundsStatement)
    (hC : gaugeMapCurlBoundStatement) (hD : gaugeMapOnDifferencesStatement) :
    sliceCriticalImpliesCriticalStatement := by
  classical
  obtain ⟨c₀, C₀, hc₀, hC₀, hG⟩ := hG
  obtain ⟨LR, hR⟩ := hR
  obtain ⟨LM, hM⟩ := hM
  obtain ⟨cB, C₅, LB, hcB, hC₅, hB⟩ := hB
  obtain ⟨cC, C₃, LC, hcC, hC₃, hC⟩ := hC
  obtain ⟨cD, C₄, LD, hcD, hC₄, hD⟩ := hD
  intro a del ha hd hd8
  refine ⟨max (max LR LM) (max LB (max LC LD)), fun L hodd hge => ?_⟩
  have g1 : LR ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hge
  have g2 : LM ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hge
  have g3 : LB ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hge
  have g4 : LC ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hge
  have g5 : LD ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hge
  obtain ⟨cR, hcR, hR'⟩ := hR L hodd g1 del hd hd8
  obtain ⟨cM, Cm, hcM, hCm, hM'⟩ := hM L hodd g2 del hd hd8
  obtain ⟨c, hc0, hc1, c2c, hnum⟩ := exists_small_constant (c₁ := min (min cR cM) (min cB (min cC cD)))
    hc₀ hC₀ hC₃ hC₄ hC₅ hCm (lt_min (lt_min hcR hcM) (lt_min hcB (lt_min hcC hcD)))
  have q1 : c ≤ cR := hc1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have q2 : c ≤ cM := hc1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have q3 : c ≤ cB := hc1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have q4 : c ≤ cC := hc1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have q5 : c ≤ cD := hc1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c, hc0, ?_⟩
  intro F m S hFL hamb hm hreg s V W hs hsc hcold U hU hcrit A
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  obtain ⟨hregU, hnear⟩ := hR' F m S hFL hamb hm hreg s V hs (hsc.trans q1) hcold U (hU.trans q1)
  have hβ0 : 0 ≤ supWeightedNorm S del (referenceFieldChain S V) U :=
    Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hL1 : ∀ x : ℕ, x ≤ L → x ≤ F.blockSide := fun x hx => hFL ▸ hx
  have hA0 : 0 ≤ 2 * supWeightedNorm S del (referenceFieldChain S V) U := by positivity
  have hu : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, ‖U.fine b.1 b.2‖ ^ (4 : ℝ) ≤
      (2 * supWeightedNorm S del (referenceFieldChain S V) U) ^ (4 : ℝ) := fun z hz =>
    (sum_fine_rpow_le_localNorm (referenceFieldChain S V) U hz).trans
      (Real.rpow_le_rpow (Real.sqrt_nonneg _) (hnear z hz) (by norm_num))
  have hcu : ∀ z ∈ S, finLpNorm (plaquettesOver S {z} 0) 2
      (fun p => ‖linearizedCurl (referenceFieldChain S V 0) U.fine p‖) ≤
        2 * supWeightedNorm S del (referenceFieldChain S V) U :=
    fun z hz => (finLpNorm_curl_le_localNorm (referenceFieldChain S V) U hz).trans (hnear z hz)
  have hub : ∀ b ∈ innerBonds S 0, ‖U.fine b.1 b.2‖ ≤ c₀ := by
    intro b hb
    have hz : enclosingCell b.1 ∈ S := enclosingCell_mem S hodd' _ (ChartCoordinates.innerBonds_ends hb).1
    have hin : b ∈ bondsOver S {enclosingCell b.1} 0 := mem_bondsOver_singleton_of hb rfl
    have h1 := Finset.single_le_sum (f := fun c : F.Site 0 × Fin 4 => ‖U.fine c.1 c.2‖ ^ (4 : ℝ))
      (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hin
    have h2 := h1.trans (hu _ hz)
    have h3 : ‖U.fine b.1 b.2‖ ≤ 2 * supWeightedNorm S del (referenceFieldChain S V) U :=
      (Real.rpow_le_rpow_iff (norm_nonneg _) hA0 (by norm_num)).1 h2
    linarith
  have hmub : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ‖U.coarse j b.1 b.2‖ ≤ c₀ := by
    intro j hj b hb
    have hz : enclosingCell b.1 ∈ S := by
      obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 (ChartCoordinates.innerBonds_ends hb).1
      rw [e, GaugeMapLinear.enclosingCell_cellCentre_add hodd' y h hh]
      exact hy
    have hin : b ∈ bondsOver S {enclosingCell b.1} (j + 1) := by
      simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton]
      exact ⟨hb, trivial⟩
    have h1 := (norm_coarse_le_localNorm (referenceFieldChain S V) U hz hj hin).trans (hnear _ hz)
    linarith
  obtain ⟨D, hDadd, _, hDc⟩ := hV F a S (referenceFieldChain S V) U W hodd' hregU
  obtain ⟨H, hGd, hHb, hHc⟩ := hG F a S (referenceFieldChain S V) U W hodd' hregU hub hmub
  have hCmain := fun (u : F.Site 0 → Fin 4 → imaginaryQuaternions) =>
    (hC F m S hodd' (hL1 _ g4) hamb hm hreg s V hs (hsc.trans q4) hcold u).2
  have hDmain := hD F m S hodd' (hL1 _ g5) hamb hm hreg s V hs (hsc.trans q5) hcold
  have hBmain := fun (b : F.Cell → ℍ[ℝ]) (B : ℝ) (h : ∀ y ∈ S, ‖b y‖ ≤ B) =>
    hB F m S hodd' (hL1 _ g3) hamb hm hreg s V hs (hsc.trans q3) hcold b B h
  have facts : GaugeSliceHypotheses S V s C₃ C₄ C₅ := by
    refine ⟨hCmain, fun ξ hξ B hB' => ((hDmain.2 ξ hξ).2.2.1 B hB'),
      fun ξ hξ z hz => ((hDmain.2 ξ hξ).2.2.2 z hz).2,
      fun b y hy => ?_, fun b z hz => ?_, fun b z hz => ?_, fun b B h z hz => (hBmain b B h).2.2.2.1 z hz,
      fun b B h z hz => (hBmain b B h).2.2.2.2 z hz⟩
    · exact (hBmain b _ (fun y hy =>
        Finset.single_le_sum (f := fun y => ‖b y‖) (fun _ _ => norm_nonneg _) hy)).1 y hy
    · exact (hBmain b _ (fun y hy =>
        Finset.single_le_sum (f := fun y => ‖b y‖) (fun _ _ => norm_nonneg _) hy)).2.1 z hz
    · exact (hBmain b _ (fun y hy =>
        Finset.single_le_sum (f := fun y => ‖b y‖) (fun _ _ => norm_nonneg _) hy)).2.2.1 z hz
  obtain ⟨n1, n3, n4, n5, n6, n7, n8⟩ :=
    hnum s (supWeightedNorm S del (referenceFieldChain S V) U) hs.le hsc hβ0 hU
  exact isCriticalAlong_of_sliceHypotheses hodd' hs.le (by positivity) hCm.le hC₀.le hC₃.le hC₄.le hC₅.le hA0 facts
    hu hcu D hDadd hDc H hGd hHb hHc hDmain.1
    (fun ξ y hy => hM' F m S hFL hamb hm hreg s V hs (hsc.trans q2) hcold U (hU.trans q2) ξ y hy)
    n1 n3 n4 n5 n6 n7 n8 hcrit A
end YangMills.Construction.SliceCriticality
end
