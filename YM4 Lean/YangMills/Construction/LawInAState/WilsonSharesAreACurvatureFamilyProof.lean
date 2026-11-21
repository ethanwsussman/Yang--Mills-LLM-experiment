import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmoothProof
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamily
import YangMills.Construction.ResponseInTheExpansion.EnergyOfAPlaquetteAlongMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.ShareFamilies
open TorusFields hiding supDist_add_siteOfInt_le
open TorusLumps hiding quaternionI
open BlockAverages hiding unitStep
open LatticeSums WeightedResponses FlatHessian StepCosts
namespace WilsonShares
private def cornerOffset (μ ν k : Fin 4) : Fin 4 → ℤ :=
  ![0, Pi.single μ 1, Pi.single ν 1, Pi.single μ 1 + Pi.single ν 1] k
private def plaquetteSlots : Finset (Fin 4 × Fin 4 × Fin 4) := Finset.univ.filter fun q => q.1 < q.2.1
variable {n : ℕ}
private theorem count_vertices_eq (x y : TorusSite n) (μ ν : Fin 4) :
    (((plaquetteVertices x μ ν).count y : ℕ) : ℝ) = ∑ k : Fin 4, if x + siteOfInt (cornerOffset μ ν k) = y then 1 else 0 := by
  have o0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
    funext i
    simp [siteOfInt]
  have e0 : x + siteOfInt (cornerOffset μ ν 0) = x := by
    simp [cornerOffset, o0]
  have e1 : x + siteOfInt (cornerOffset μ ν 1) = x + unitStep n μ := by
    simp [cornerOffset, siteOfInt_single]
  have e2 : x + siteOfInt (cornerOffset μ ν 2) = x + unitStep n ν := by
    simp [cornerOffset, siteOfInt_single]
  have e3 : x + siteOfInt (cornerOffset μ ν 3) = x + unitStep n μ + unitStep n ν := by
    simp [cornerOffset, siteOfInt_add_eq, siteOfInt_single, add_assoc]
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  simp only [plaquetteVertices, List.count_cons, List.count_nil, beq_iff_eq]
  push_cast
  ring
variable [NeZero n]
private theorem levelShare_eq_sum (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) :
    levelShare a L 0 Finset.univ y W =
      ∑ q ∈ plaquetteSlots, (1 / 4) * plaquetteEnergy W (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1 := by
  have h1 : levelShare a L 0 Finset.univ y W = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 * plaquetteEnergy W p.1 p.2.1 p.2.2 := rfl
  rw [h1]
  have h2 : plaquettesIn (Finset.univ : Finset (TorusSite n)) = Finset.univ.filter fun p : TorusPlaquette n => p.2.1 < p.2.2 := by
    ext p
    simp [plaquettesIn]
  rw [h2, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have h3 : ∑ q ∈ plaquetteSlots, (1 / 4) * plaquetteEnergy W (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1 =
      ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ k : Fin 4, if μ < ν then (1 / 4) * plaquetteEnergy W (y - siteOfInt (cornerOffset μ ν k)) μ ν else 0 := by
    unfold plaquetteSlots
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
  rw [h3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hμν : μ < ν
  · simp only [hμν, if_true, count_vertices_eq, Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single (y - siteOfInt (cornerOffset μ ν k))]
    · simp
    · intro x _ hx
      have : x + siteOfInt (cornerOffset μ ν k) ≠ y := fun e => hx (by rw [← e]; abel)
      simp [this]
    · simp
  · simp [hμν]
private theorem family_eq_sum (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) :
    levelShareFamily a L 0 n y W = ∑ q ∈ plaquetteSlots, (1 / 4) * plaquetteEnergy W (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1 := by
  simp only [levelShareFamily, dif_neg (NeZero.ne n)]
  exact levelShare_eq_sum a L y W
private theorem card_plaquetteSlots : plaquetteSlots.card = 24 := by decide
private theorem offsetSupNorm_cornerOffset_le {μ ν : Fin 4} (h : μ < ν) (k : Fin 4) : offsetSupNorm (cornerOffset μ ν k) ≤ 1 := by
  have hne : μ ≠ ν := ne_of_lt h
  refine Finset.sup_le fun i _ => ?_
  fin_cases k
  · simp [cornerOffset]
  · simp only [cornerOffset]
    by_cases a : i = μ
    · subst a
      simp
    · simp [Pi.single_eq_of_ne a]
  · simp only [cornerOffset]
    by_cases a : i = ν
    · subst a
      simp
    · simp [Pi.single_eq_of_ne a]
  · simp only [cornerOffset]
    by_cases a : i = μ
    · subst a
      simp [Pi.single_eq_of_ne hne]
    · by_cases b : i = ν
      · subst b
        simp [Pi.single_eq_of_ne a]
      · simp [Pi.single_eq_of_ne a, Pi.single_eq_of_ne b]
private theorem supDist_sub_corner_le (y : TorusSite n) {μ ν : Fin 4} (h : μ < ν) (k : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (y - siteOfInt (cornerOffset μ ν k)) y ≤ 1 := by
  have e : y - siteOfInt (cornerOffset μ ν k) = y + siteOfInt (-cornerOffset μ ν k) := by
    rw [sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt]
  rw [e]
  refine (_root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt_le y _).trans ?_
  have h1 : offsetSupNorm (-cornerOffset μ ν k) = offsetSupNorm (cornerOffset μ ν k) := by
    simp [offsetSupNorm]
  rw [h1]
  exact offsetSupNorm_cornerOffset_le h k
private theorem lt_of_mem_plaquetteSlots {q : Fin 4 × Fin 4 × Fin 4} (h : q ∈ plaquetteSlots) : q.1 < q.2.1 := by
  simpa [plaquetteSlots] using h
private theorem contDiffAt_energy (hE : PlaquetteEnergySmoothBound) {k : ℕ} (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => plaquetteEnergy (TorusFields.perturb c X σ W) x μ ν) 0 := by
  obtain ⟨M, -, h⟩ := hE
  exact ((h n k W x μ ν c X).1.of_le le_top).contDiffAt
private theorem family_contDiffThree (hE : PlaquetteEnergySmoothBound) (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) :
    ContDiffThreeAt (levelShareFamily a L 0 n y) W := by
  intro k c X
  simp only [family_eq_sum]
  refine ContDiffAt.sum fun q _ => contDiffAt_const.mul (contDiffAt_energy hE W _ _ _ c X)
private theorem mixedDeriv_family (hE : PlaquetteEnergySmoothBound) (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (levelShareFamily a L 0 n y) W c X = ∑ q ∈ plaquetteSlots, (1 / 4) *
      mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1) W c X := by
  have hs : ∀ q : Fin 4 × Fin 4 × Fin 4, ContDiffAt ℝ k (fun σ : Fin k → ℝ =>
      plaquetteEnergy (TorusFields.perturb c X σ W) (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1) 0 := fun q =>
    (contDiffAt_energy hE W _ _ _ c X).of_le (by exact_mod_cast hk)
  unfold mixedDeriv
  simp only [family_eq_sum]
  let F : Fin 4 × Fin 4 × Fin 4 → (Fin k → ℝ) → ℝ := fun q => (1 / 4 : ℝ) • fun σ' : Fin k → ℝ =>
    plaquetteEnergy (TorusFields.perturb c X σ' W) (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1
  have e : (fun σ : Fin k → ℝ => ∑ q ∈ plaquetteSlots, (1 / 4 : ℝ) *
      plaquetteEnergy (TorusFields.perturb c X σ W) (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1) =
      fun σ => ∑ q ∈ plaquetteSlots, F q σ := by
    funext σ
    simp [F]
  have hF : ∀ q, ContDiffAt ℝ k (F q) 0 := fun q => (hs q).const_smul (1 / 4 : ℝ)
  have key := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := k) (x := (0 : Fin k → ℝ)) (u := plaquetteSlots) (f := F)
    (fun q _ => hF q)
  rw [e, key]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hs q)]
  simp
private theorem abs_mixedDeriv_family_le (hE : PlaquetteEnergySmoothBound) {M : ℝ}
    (hM : ∀ (n k : ℕ) (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X| ≤ M)
    (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |mixedDeriv (levelShareFamily a L 0 n y) W c X| ≤ 6 * M := by
  rw [mixedDeriv_family hE a L y W hk]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _q ∈ plaquetteSlots, (1 / 4) * M := Finset.sum_le_sum fun q _ => by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        exact mul_le_mul_of_nonneg_left (hM n k W _ _ _ c X hk hX) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const, card_plaquetteSlots]
      simp
      ring
private theorem supDist_add_unitStep (y x : TorusSite n) (i : Fin 4) : _root_.YangMills.Construction.TorusFields.supDist (x + unitStep n i) y ≤ _root_.YangMills.Construction.TorusFields.supDist x y + 1 :=
  (_root_.YangMills.Construction.TorusFields.supDist_triangle _ x _).trans (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x i; omega)
private theorem mixedDeriv_family_of_far (hE : PlaquetteEnergySmoothBound) (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (l : Fin k) (hl : 2 < _root_.YangMills.Construction.TorusFields.supDist (c l).1 y) :
    mixedDeriv (levelShareFamily a L 0 n y) W c X = 0 := by
  rw [mixedDeriv_family hE a L y W hk]
  obtain ⟨M, -, h⟩ := hE
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' := lt_of_mem_plaquetteSlots hq
  set x := y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2) with hx
  have hd : _root_.YangMills.Construction.TorusFields.supDist x y ≤ 1 := supDist_sub_corner_le y hq' _
  have hv := (h n k W x q.1 q.2.1 c X).2.2 l (fun i e => by
    have s1 := supDist_add_unitStep y x q.1
    have s2 := supDist_add_unitStep y x q.2.1
    have : _root_.YangMills.Construction.TorusFields.supDist (plaquetteEdges x q.1 q.2.1 i).1 y ≤ 2 := by
      fin_cases i
      · simp only [plaquetteEdges]
        simp
        omega
      · simp only [plaquetteEdges]
        simp
        omega
      · simp only [plaquetteEdges]
        simp
        omega
      · simp only [plaquetteEdges]
        simp
        omega
    rw [e] at this
    omega)
  rw [hv, mul_zero]
private theorem weight_pos {ℓ : StepParameters} (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem weight_mono {ℓ : StepParameters} (hfit : ℓ.Admissible) {m m' : ℕ} (h : m ≤ m') : ℓ.weight m ≤ ℓ.weight m' := by
  have hr : 0 < ℓ.weightRate := by
    have := hfit.rt_pos
    unfold StepParameters.weightRate
    positivity
  have hn := hfit.n₁_pos
  have hmr : (m : ℝ) ≤ m' := by exact_mod_cast h
  unfold StepParameters.weight
  refine mul_le_mul ?_ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmr hr.le)) (Real.exp_pos _).le (by positivity)
  refine max_le_max le_rfl (pow_le_pow_left₀ (by positivity) ?_ _)
  exact div_le_div_of_nonneg_right hmr hn.le
abbrev _root_.YangMills.SharedProofs.p24433 := @weight_mono
private theorem supportDiam_le_four {y : TorusSite n} {k : ℕ} {c : Fin k → TorusBond n} (h : ∀ l, _root_.YangMills.Construction.TorusFields.supDist (c l).1 y ≤ 2) : supportDiam y c ≤ 4 := by
  unfold supportDiam
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have := h l
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    omega
  · have h1 := h l
    have h2 := h l'
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (c l).1 y (c l').1
    have h4 : _root_.YangMills.Construction.TorusFields.supDist y (c l').1 = _root_.YangMills.Construction.TorusFields.supDist (c l').1 y := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    omega
private theorem mixedDeriv_family_decay (hE : PlaquetteEnergySmoothBound) {ℓ : StepParameters} (hfit : ℓ.Admissible) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (n k : ℕ) (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X| ≤ M)
    (y : TorusSite n) (W : TorusField n) {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 n y) W c X| ≤ 6 * M * ℓ.weight 4 / ℓ.weight (supportDiam y c) := by
  have hw := weight_pos (ℓ := ℓ) (supportDiam y c)
  have hw4 := weight_pos (ℓ := ℓ) 4
  by_cases hfar : ∃ l, 2 < _root_.YangMills.Construction.TorusFields.supDist (c l).1 y
  · obtain ⟨l, hl⟩ := hfar
    rw [mixedDeriv_family_of_far hE _ _ y W hk c X l hl, abs_zero]
    exact div_nonneg (mul_nonneg (by linarith) hw4.le) hw.le
  · have hall : ∀ l, _root_.YangMills.Construction.TorusFields.supDist (c l).1 y ≤ 2 := fun l => not_lt.1 fun h => hfar ⟨l, h⟩
    have hd := weight_mono hfit (supportDiam_le_four hall)
    rw [le_div_iff₀ hw]
    have hb := abs_mixedDeriv_family_le hE hM ℓ.coupling ℓ.side y W hk c X hX
    calc _ ≤ 6 * M * ℓ.weight (supportDiam y c) := mul_le_mul_of_nonneg_right hb hw.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
private theorem mixedDeriv_zero_order (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n) (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by
  have e : ∀ σ : Fin 0 → ℝ, TorusFields.perturb c X σ W = W := by
    intro σ
    funext x i
    simp [TorusFields.perturb, TorusFields.expUnit_zero]
  simp [mixedDeriv, e]
abbrev _root_.YangMills.SharedProofs.p46649 := @mixedDeriv_zero_order
private theorem family_trivialField (a : ℝ) (L : ℕ) (y : TorusSite n) : levelShareFamily a L 0 n y (trivialField n) = 0 := by
  rw [family_eq_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp [plaquetteEnergy, holonomy_trivialField]
private theorem centered_family (a : ℝ) (L : ℕ) (y : TorusSite n) : centered (levelShareFamily a L 0) n y = levelShareFamily a L 0 n y := by
  funext W
  simp [centered, family_trivialField]
private theorem abs_family_le (a : ℝ) (L : ℕ) (y : TorusSite n) (W : TorusField n) : |levelShareFamily a L 0 n y W| ≤ 12 := by
  rw [family_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _q ∈ plaquetteSlots, (1 / 2 : ℝ) := Finset.sum_le_sum fun q _ => by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (plaquetteEnergy_nonneg _ _ _ _))]
        have := TorusFrame.plaquetteEnergy_le_two W (y - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1
        linarith
    _ = 12 := by
      rw [Finset.sum_const, card_plaquetteSlots]
      norm_num
private theorem offsetSupNorm_le_of_inBox {m : ℕ} {e : LatticeBond} (h : TorusFields.BondOffsetInBox m e) : offsetSupNorm e.1 ≤ m := by
  refine Finset.sup_le fun i _ => ?_
  have := h.1 i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
abbrev _root_.YangMills.DeltaSharedProofs.p502589 := @offsetSupNorm_le_of_inBox
private theorem inBox_of_offsetSupNorm {m : ℕ} {e : LatticeBond} (h : offsetSupNorm e.1 + 1 ≤ m) : TorusFields.BondOffsetInBox m e := by apply _root_.YangMills.Construction.AbelianSecondOrder.bondOffsetInBox_of_le <;> assumption
variable {n' : ℕ} [NeZero n']
private theorem perturb_agree {k m : ℕ} {b : Fin k → LatticeBond} (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) {W : TorusField n} {W' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'} (hag : FieldsAgreeNear W W' y y' m) (h1 : 2 * m + 2 < n) (h2 : 2 * m + 2 < n')
    (hb : ∀ l, TorusFields.BondOffsetInBox m (b l)) {e : LatticeBond} (he : TorusFields.BondOffsetInBox m e) :
    TorusFields.perturb (fun l => bondFrom y (b l)) X σ W (bondFrom y e).1 (bondFrom y e).2 =
      TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W' (bondFrom y' e).1 (bondFrom y' e).2 := by
  have hes := offsetSupNorm_le_of_inBox he
  have c1 : ∀ l, (bondFrom y (b l) = ((bondFrom y e).1, (bondFrom y e).2)) ↔ b l = e := fun l => by
    have hs := offsetSupNorm_le_of_inBox (hb l)
    exact ⟨fun h => bondFrom_inj_of_small y (by omega) (by omega) h, fun h => by rw [h]⟩
  have c2 : ∀ l, (bondFrom y' (b l) = ((bondFrom y' e).1, (bondFrom y' e).2)) ↔ b l = e := fun l => by
    have hs := offsetSupNorm_le_of_inBox (hb l)
    exact ⟨fun h => bondFrom_inj_of_small y' (by omega) (by omega) h, fun h => by rw [h]⟩
  simp only [TorusFields.perturb, c1, c2]
  rw [hag e he]
private theorem holonomy_agree {k m : ℕ} {b : Fin k → LatticeBond} (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) {W : TorusField n} {W' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'} (hag : FieldsAgreeNear W W' y y' m) (h1 : 2 * m + 2 < n) (h2 : 2 * m + 2 < n')
    (hb : ∀ l, TorusFields.BondOffsetInBox m (b l)) {o : Fin 4 → ℤ} (ho : offsetSupNorm o + 3 ≤ m) (μ ν : Fin 4) :
    holonomy (TorusFields.perturb (fun l => bondFrom y (b l)) X σ W) (y + siteOfInt o) μ ν =
      holonomy (TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W') (y' + siteOfInt o) μ ν := by
  have sz : ∀ i : Fin 4, offsetSupNorm (o + Pi.single i 1) ≤ offsetSupNorm o + 1 := fun i => by
    refine Finset.sup_le fun j _ => ?_
    have hj := natAbs_le_offsetSupNorm o j
    by_cases h : j = i
    · subst h
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
      omega
  have t : ∀ {p : ℕ} (w : TorusSite p) (i : Fin 4), w + siteOfInt (o + Pi.single i 1) = w + siteOfInt o + unitStep p i := fun w i => by
    rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
  have a1 : TorusFields.perturb (fun l => bondFrom y (b l)) X σ W (y + siteOfInt o) μ =
      TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W' (y' + siteOfInt o) μ :=
    perturb_agree X σ hag h1 h2 hb (e := (o, μ)) (inBox_of_offsetSupNorm (by simp only; omega))
  have a4 : TorusFields.perturb (fun l => bondFrom y (b l)) X σ W (y + siteOfInt o) ν =
      TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W' (y' + siteOfInt o) ν :=
    perturb_agree X σ hag h1 h2 hb (e := (o, ν)) (inBox_of_offsetSupNorm (by simp only; omega))
  have a2 : TorusFields.perturb (fun l => bondFrom y (b l)) X σ W (y + siteOfInt (o + Pi.single μ 1)) ν =
      TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W' (y' + siteOfInt (o + Pi.single μ 1)) ν :=
    perturb_agree X σ hag h1 h2 hb (e := (o + Pi.single μ 1, ν)) (inBox_of_offsetSupNorm (by have := sz μ; simp only; omega))
  have a3 : TorusFields.perturb (fun l => bondFrom y (b l)) X σ W (y + siteOfInt (o + Pi.single ν 1)) μ =
      TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W' (y' + siteOfInt (o + Pi.single ν 1)) μ :=
    perturb_agree X σ hag h1 h2 hb (e := (o + Pi.single ν 1, μ)) (inBox_of_offsetSupNorm (by have := sz ν; simp only; omega))
  rw [t, t] at a2 a3
  simp only [holonomy]
  rw [a1, a2, a3, a4]
private theorem family_agree {a : ℝ} {L k m : ℕ} {b : Fin k → LatticeBond} (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) {W : TorusField n} {W' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'} (hag : FieldsAgreeNear W W' y y' m) (h1 : 2 * m + 2 < n) (h2 : 2 * m + 2 < n')
    (hb : ∀ l, TorusFields.BondOffsetInBox m (b l)) (hm : 4 ≤ m) :
    levelShareFamily a L 0 n y (TorusFields.perturb (fun l => bondFrom y (b l)) X σ W) =
      levelShareFamily a L 0 n' y' (TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W') := by
  rw [family_eq_sum, family_eq_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := lt_of_mem_plaquetteSlots hq
  have e : ∀ {p : ℕ} (w : TorusSite p), w - siteOfInt (cornerOffset q.1 q.2.1 q.2.2) = w + siteOfInt (-cornerOffset q.1 q.2.1 q.2.2) := fun w => by
    rw [sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt]
  have hs : offsetSupNorm (-cornerOffset q.1 q.2.1 q.2.2) + 3 ≤ m := by
    have h1 : offsetSupNorm (-cornerOffset q.1 q.2.1 q.2.2) = offsetSupNorm (cornerOffset q.1 q.2.1 q.2.2) := by
      simp [offsetSupNorm]
    have := offsetSupNorm_cornerOffset_le hq' q.2.2
    omega
  simp only [plaquetteEnergy, e]
  rw [holonomy_agree X σ hag h1 h2 hb hs]
private theorem isCurvatureFamily_of_admissible (hE : PlaquetteEnergySmoothBound) {ℓ : StepParameters} (hfit : ℓ.Admissible) :
    ∃ C : ℝ, 0 ≤ C ∧ IsCurvatureFamily ℓ C (levelShareFamily ℓ.coupling ℓ.side 0) := by
  obtain ⟨M, hM0, hh⟩ := id hE
  have hM : ∀ (n k : ℕ) (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X| ≤ M := fun n k W x μ ν c X h1 h2 => (hh n k W x μ ν c X).2.1 h1 h2
  have hw4 := weight_pos (ℓ := ℓ) 4
  refine ⟨2 * (12 + 6 * M) * ℓ.weight 4, by positivity, ?_⟩
  refine ⟨fun n _ _ y W _ => family_contDiffThree hE _ _ y W, ?_, ?_, ?_, ?_⟩
  · intro n _ _ y g W _
    simp only [family_eq_sum, _root_.YangMills.Construction.TorusFields.plaquetteEnergy_gaugeTransform]
  · intro n _ _ y u W _
    simp only [family_eq_sum, plaquetteEnergy_translate]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    abel
  · intro n _ _ y W _ k c X _ hk hX
    refine (mixedDeriv_family_decay hE hfit hM0 hM y W hk c X hX).trans (div_le_div_of_nonneg_right ?_ (weight_pos _).le)
    refine mul_le_mul_of_nonneg_right ?_ hw4.le
    linarith
  · intro n n' _ _ _ _ y y' W W' m h1 h2 _ _ hag k b X hk hb hX
    rw [centered_family, centered_family]
    by_cases hm : 4 ≤ m
    · have e : (fun σ : Fin k → ℝ => levelShareFamily ℓ.coupling ℓ.side 0 n y (TorusFields.perturb (fun l => bondFrom y (b l)) X σ W)) =
          fun σ => levelShareFamily ℓ.coupling ℓ.side 0 n' y' (TorusFields.perturb (fun l => bondFrom y' (b l)) X σ W') := by
        funext σ
        exact family_agree X σ hag h1 h2 hb hm
      have e2 : mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 n y) W (fun l => bondFrom y (b l)) X =
          mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 n' y') W' (fun l => bondFrom y' (b l)) X := by
        unfold mixedDeriv
        rw [e]
      rw [e2, sub_self, abs_zero]
      exact div_nonneg (by positivity) (weight_pos _).le
    · have hm3 : m ≤ 4 := by omega
      have hbd : ∀ {p : ℕ} [NeZero p] (w : TorusSite p) (V : TorusField p) (c : Fin k → TorusBond p),
          |mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 p w) V c X| ≤ 12 + 6 * M := by
        intro p _ w V c
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          rw [mixedDeriv_zero_order]
          have := abs_family_le ℓ.coupling ℓ.side w V
          linarith
        · have := abs_mixedDeriv_family_le hE hM ℓ.coupling ℓ.side w V (by omega : k ≤ 3) c X hX
          linarith
      have h3 := abs_sub (mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 n y) W (fun l => bondFrom y (b l)) X)
        (mixedDeriv (levelShareFamily ℓ.coupling ℓ.side 0 n' y') W' (fun l => bondFrom y' (b l)) X)
      have h4 := hbd y W (fun l => bondFrom y (b l))
      have h5 := hbd y' W' (fun l => bondFrom y' (b l))
      have hw := weight_pos (ℓ := ℓ) m
      rw [le_div_iff₀ hw]
      have hw' := weight_mono hfit hm3
      have p0 : 0 ≤ 12 + 6 * M := by positivity
      calc _ ≤ (2 * (12 + 6 * M)) * ℓ.weight m := mul_le_mul_of_nonneg_right (by linarith) hw.le
        _ ≤ _ := by
          have : (2 * (12 + 6 * M)) * ℓ.weight m ≤ (2 * (12 + 6 * M)) * ℓ.weight 4 :=
            mul_le_mul_of_nonneg_left hw' (by positivity)
          linarith
private def plaquetteEdgeOffset (q : Fin 4 × Fin 4 × Fin 4) : Fin 4 → LatticeBond :=
  ![(-cornerOffset q.1 q.2.1 q.2.2, q.1), (-cornerOffset q.1 q.2.1 q.2.2 + Pi.single q.1 1, q.2.1),
    (-cornerOffset q.1 q.2.1 q.2.2 + Pi.single q.2.1 1, q.1), (-cornerOffset q.1 q.2.1 q.2.2, q.2.1)]
private def edgeSign : Fin 4 → ℝ := ![1, 1, -1, -1]
private def curlCoeff (q : Fin 4 × Fin 4 × Fin 4) (c : LatticeBond) : ℝ := ∑ i, edgeSign i * (if c = plaquetteEdgeOffset q i then 1 else 0)
private theorem expUnit_smul_mul (v : imaginaryQuaternions) (p r : ℝ) : BlockAverages.expUnit (p • v) * BlockAverages.expUnit (r • v) = BlockAverages.expUnit ((p + r) • v) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
private theorem expUnit_inv (v : imaginaryQuaternions) : (BlockAverages.expUnit v)⁻¹ = BlockAverages.expUnit ((-1 : ℝ) • v) := by
  have h := expUnit_smul_mul v 1 (-1)
  have h0 : BlockAverages.expUnit (((1 : ℝ) + -1) • v) = 1 := by
    apply Subtype.ext
    change NormedSpace.exp ((((1 : ℝ) + -1) • v : imaginaryQuaternions) : ℍ[ℝ]) = 1
    simp
  rw [h0, one_smul] at h
  exact inv_eq_of_mul_eq_one_right h
abbrev _root_.YangMills.SharedProofs.p44810 := @expUnit_inv
private theorem norm_quaternionI : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.norm_coe_imaginaryUnit <;> assumption
private theorem perturb_trivial_bond {c : Fin 2 → LatticeBond} (hs : ∀ l, 2 * offsetSupNorm (c l).1 < n) (σ : Fin 2 → ℝ) {e : LatticeBond}
    (he : 2 * offsetSupNorm e.1 < n) :
    TorusFields.perturb (fun l => bondFrom (0 : TorusSite n) (c l)) (fun _ => quaternionI) σ (trivialField n) (bondFrom (0 : TorusSite n) e).1 (bondFrom (0 : TorusSite n) e).2 =
      BlockAverages.expUnit ((∑ l, σ l * (if c l = e then 1 else 0)) • quaternionI) := by
  simp only [TorusFields.perturb, trivialField, mul_one]
  congr 1
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = e
  · simp [h]
  · have h2 : ¬ (bondFrom (0 : TorusSite n) (c l) = ((bondFrom (0 : TorusSite n) e).1, (bondFrom (0 : TorusSite n) e).2)) :=
      fun a => h (bondFrom_inj_of_small 0 (hs l) he a)
    simp [h, h2]
private theorem offsetSupNorm_neg_corner_le {μ ν : Fin 4} (h : μ < ν) (k : Fin 4) : offsetSupNorm (-cornerOffset μ ν k) ≤ 1 := by
  have h1 : offsetSupNorm (-cornerOffset μ ν k) = offsetSupNorm (cornerOffset μ ν k) := by
    simp [offsetSupNorm]
  rw [h1]
  exact offsetSupNorm_cornerOffset_le h k
private theorem offsetSupNorm_add_single_le (o : Fin 4 → ℤ) (i : Fin 4) : offsetSupNorm (o + Pi.single i 1) ≤ offsetSupNorm o + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
private theorem energy_along_abelian {c : Fin 2 → LatticeBond} {q : Fin 4 × Fin 4 × Fin 4} (hq : q ∈ plaquetteSlots)
    (hs : ∀ l, 2 * offsetSupNorm (c l).1 < n) (hn : 6 < n) (σ : Fin 2 → ℝ) :
    plaquetteEnergy (TorusFields.perturb (fun l => bondFrom (0 : TorusSite n) (c l)) (fun _ => quaternionI) σ (trivialField n))
        (0 - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1 = 1 - Real.cos (∑ l, σ l * curlCoeff q (c l)) := by
  have hq' := lt_of_mem_plaquetteSlots hq
  set o := -cornerOffset q.1 q.2.1 q.2.2 with ho
  have hos : offsetSupNorm o ≤ 1 := offsetSupNorm_neg_corner_le hq' _
  have ex : (0 : TorusSite n) - siteOfInt (cornerOffset q.1 q.2.1 q.2.2) = 0 + siteOfInt o := by
    rw [ho, sub_eq_add_neg]
    congr 1
    funext i
    simp [siteOfInt]
  have t : ∀ i : Fin 4, (0 : TorusSite n) + siteOfInt (o + Pi.single i 1) = 0 + siteOfInt o + unitStep n i := fun i => by
    rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
  have s1 := offsetSupNorm_add_single_le o q.1
  have s2 := offsetSupNorm_add_single_le o q.2.1
  have b0 := perturb_trivial_bond hs σ (e := (o, q.1)) (by simp only; omega)
  have b1 := perturb_trivial_bond hs σ (e := (o + Pi.single q.1 1, q.2.1)) (by simp only; omega)
  have b2 := perturb_trivial_bond hs σ (e := (o + Pi.single q.2.1 1, q.1)) (by simp only; omega)
  have b3 := perturb_trivial_bond hs σ (e := (o, q.2.1)) (by simp only; omega)
  change TorusFields.perturb _ _ σ (trivialField n) (0 + siteOfInt o) q.1 = _ at b0
  change TorusFields.perturb _ _ σ (trivialField n) (0 + siteOfInt (o + Pi.single q.1 1)) q.2.1 = _ at b1
  change TorusFields.perturb _ _ σ (trivialField n) (0 + siteOfInt (o + Pi.single q.2.1 1)) q.1 = _ at b2
  change TorusFields.perturb _ _ σ (trivialField n) (0 + siteOfInt o) q.2.1 = _ at b3
  rw [t] at b1 b2
  rw [ex]
  simp only [plaquetteEnergy, holonomy]
  rw [b0, b1, b2, b3, expUnit_inv, expUnit_inv, smul_smul, smul_smul, expUnit_smul_mul, expUnit_smul_mul, expUnit_smul_mul,
    GaugeFixing.re_coe_expUnit]
  have hn1 : ∀ r : ℝ, ‖((r • quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = |r| := fun r => by
    rw [Submodule.coe_smul, norm_smul, norm_quaternionI, mul_one, Real.norm_eq_abs]
  rw [hn1, Real.cos_abs]
  congr 2
  have d0 : plaquetteEdgeOffset q 0 = (o, q.1) := rfl
  have d1 : plaquetteEdgeOffset q 1 = (o + Pi.single q.1 1, q.2.1) := rfl
  have d2 : plaquetteEdgeOffset q 2 = (o + Pi.single q.2.1 1, q.1) := rfl
  have d3 : plaquetteEdgeOffset q 3 = (o, q.2.1) := rfl
  have g0 : edgeSign 0 = 1 := rfl
  have g1 : edgeSign 1 = 1 := rfl
  have g2 : edgeSign 2 = -1 := rfl
  have g3 : edgeSign 3 = -1 := rfl
  simp only [curlCoeff, Fin.sum_univ_four, Fin.sum_univ_two, d0, d1, d2, d3, g0, g1, g2, g3]
  ring
private theorem iteratedFDeriv_two_one_sub_cos (α : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => 1 - Real.cos (∑ l, σ l * α l)) 0 (fun l => Pi.single l 1) = α 0 * α 1 := by
  let L : (Fin 2 → ℝ) →L[ℝ] ℝ := α 0 • ContinuousLinearMap.proj 0 + α 1 • ContinuousLinearMap.proj 1
  let h : ℝ → ℝ := fun x => 1 - Real.cos x
  have e : (fun σ : Fin 2 → ℝ => 1 - Real.cos (∑ l, σ l * α l)) = h ∘ L := by
    funext σ
    simp [h, L, Fin.sum_univ_two, mul_comm]
  have hh : ContDiff ℝ 2 h := contDiff_const.sub Real.contDiff_cos
  have d1 : deriv h = Real.sin := by
    funext x
    have := ((Real.hasDerivAt_cos x).const_sub 1).deriv
    simpa [h] using this
  have d2 : iteratedDeriv 2 h 0 = 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
    simp [Real.deriv_sin]
  rw [e, L.iteratedFDeriv_comp_right hh 0 le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, d2]
  simp [L, Fin.prod_univ_two]
private theorem mixedDeriv_energy_trivial {c c' : LatticeBond} {q : Fin 4 × Fin 4 × Fin 4} (hq : q ∈ plaquetteSlots)
    (hs : 2 * offsetSupNorm c.1 < n) (hs' : 2 * offsetSupNorm c'.1 < n) (hn : 6 < n) :
    mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' (0 - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1) (trivialField n)
        ![bondFrom 0 c, bondFrom 0 c'] ![quaternionI, quaternionI] = curlCoeff q c * curlCoeff q c' := by
  have hs2 : ∀ l, 2 * offsetSupNorm ((![c, c'] : Fin 2 → LatticeBond) l).1 < n := fun l => by
    fin_cases l
    · exact hs
    · exact hs'
  have e1 : (![bondFrom 0 c, bondFrom 0 c'] : Fin 2 → TorusBond n) = fun l => bondFrom 0 ((![c, c'] : Fin 2 → LatticeBond) l) := by
    funext l
    fin_cases l <;> rfl
  have e2 : (![quaternionI, quaternionI] : Fin 2 → imaginaryQuaternions) = fun _ => quaternionI := by
    funext l
    fin_cases l <;> rfl
  unfold mixedDeriv
  rw [e1, e2]
  have e3 : (fun σ : Fin 2 → ℝ => plaquetteEnergy (TorusFields.perturb (fun l => bondFrom (0 : TorusSite n) ((![c, c'] : Fin 2 → LatticeBond) l))
      (fun _ => quaternionI) σ (trivialField n)) (0 - siteOfInt (cornerOffset q.1 q.2.1 q.2.2)) q.1 q.2.1) =
      fun σ => 1 - Real.cos (∑ l, σ l * curlCoeff q ((![c, c'] : Fin 2 → LatticeBond) l)) := by
    funext σ
    exact energy_along_abelian hq hs2 hn σ
  rw [e3, iteratedFDeriv_two_one_sub_cos]
  rfl
private theorem secondDerivLimit_quaternionI {ℓ : StepParameters} {C : ℝ} (hE : PlaquetteEnergySmoothBound) (hS : SecondOrderAtAbelianFields)
    (hℓ : ℓ.Admissible) (hf : IsCurvatureFamily ℓ C (levelShareFamily ℓ.coupling ℓ.side 0)) (c c' : LatticeBond) :
    secondDerivLimit (levelShareFamily ℓ.coupling ℓ.side 0) c c' quaternionI quaternionI = ∑ q ∈ plaquetteSlots, (1 / 4) * (curlCoeff q c * curlCoeff q c') := by
  obtain ⟨hlim, -⟩ := hS ℓ hℓ C _ hf
  refine tendsto_nhds_unique (hlim c c' quaternionI quaternionI) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (2 * offsetSupNorm c.1 + 2 * offsetSupNorm c'.1 + 6)] with k hk
  haveI : NeZero k := ⟨by omega⟩
  rw [mixedDeriv_family hE _ _ 0 (trivialField k) (by norm_num)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mixedDeriv_energy_trivial hq (by omega) (by omega) (by omega)]
private theorem linearPotential_step (A : Fin 4 → Fin 4 → imaginaryQuaternions) (o : Fin 4 → ℤ) (ρ κ : Fin 4) :
    ((linearPotential A (o + Pi.single ρ 1, κ) : imaginaryQuaternions) : ℍ[ℝ]) =
      (linearPotential A (o, κ) : imaginaryQuaternions) + (1 / 2 : ℝ) • ((A ρ κ : imaginaryQuaternions) : ℍ[ℝ]) := by
  have e : ∀ l : Fin 4, (((o + Pi.single ρ 1 : Fin 4 → ℤ) l : ℤ) : ℝ) • ((A l κ : imaginaryQuaternions) : ℍ[ℝ]) =
      ((o l : ℤ) : ℝ) • ((A l κ : imaginaryQuaternions) : ℍ[ℝ]) + (if l = ρ then ((A l κ : imaginaryQuaternions) : ℍ[ℝ]) else 0) := by
    intro l
    by_cases h : l = ρ
    · subst h
      simp [add_smul]
    · simp [h]
  simp only [linearPotential, Submodule.coe_smul, Submodule.coe_sum, e, Finset.sum_add_distrib, smul_add]
  simp
private theorem curl_linearPotential {A : Fin 4 → Fin 4 → imaginaryQuaternions} (hA : ∀ μ ν, A μ ν = - A ν μ) (o : Fin 4 → ℤ) (μ ν : Fin 4) :
    ((A μ ν : imaginaryQuaternions) : ℍ[ℝ]) = (linearPotential A (o, μ) : imaginaryQuaternions) + (linearPotential A (o + Pi.single μ 1, ν) : imaginaryQuaternions) -
      (linearPotential A (o + Pi.single ν 1, μ) : imaginaryQuaternions) - (linearPotential A (o, ν) : imaginaryQuaternions) := by
  rw [linearPotential_step, linearPotential_step]
  have h : ((A ν μ : imaginaryQuaternions) : ℍ[ℝ]) = -((A μ ν : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [hA ν μ]
    rfl
  rw [h]
  module
private theorem hasCurvatureForm_wilson {ℓ : StepParameters} {C : ℝ} (hE : PlaquetteEnergySmoothBound) (hS : SecondOrderAtAbelianFields)
    (hH : HessianAtTrivialFieldStatement) (hℓ : ℓ.Admissible) (hf : IsCurvatureFamily ℓ C (levelShareFamily ℓ.coupling ℓ.side 0)) :
    HasCurvatureForm (levelShareFamily ℓ.coupling ℓ.side 0) 1 := by
  obtain ⟨hlim, -⟩ := hS ℓ hℓ C _ hf
  refine ⟨fun c c' X X' => ⟨_, hlim c c' X X'⟩, fun A A' hA hA' => ?_⟩
  have hgen : ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions), secondDerivLimit (levelShareFamily ℓ.coupling ℓ.side 0) c c' X X' =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * secondDerivLimit (levelShareFamily ℓ.coupling ℓ.side 0) c c' quaternionI quaternionI := by
    intro c c' X X'
    have t1 := hlim c c' X X'
    have t2 := (hlim c c' quaternionI quaternionI).const_mul (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]))
    refine tendsto_nhds_unique_of_eventuallyEq t1 t2 ?_
    filter_upwards [eventually_ge_atTop (max ℓ.n₀ 1)] with k hk
    haveI : NeZero k := ⟨by have := le_max_right ℓ.n₀ 1; omega⟩
    exact (hH ℓ hℓ C _ hf k ((le_max_left _ _).trans hk) 0 (bondFrom 0 c) (bondFrom 0 c')).1 X X'
  set v : Fin 4 × Fin 4 × Fin 4 → Fin 4 → Fin 4 → ℝ := fun q i j => (1 / 4) * (edgeSign i * edgeSign j) *
    inner ℝ ((linearPotential A (plaquetteEdgeOffset q i) : imaginaryQuaternions) : ℍ[ℝ]) ((linearPotential A' (plaquetteEdgeOffset q j) : imaginaryQuaternions) : ℍ[ℝ]) with hv
  have hterm : ∀ cc : LatticeBond × LatticeBond, limitFormTerm (levelShareFamily ℓ.coupling ℓ.side 0) A A' cc =
      ∑ q ∈ plaquetteSlots, ∑ i, ∑ j, if cc = (plaquetteEdgeOffset q i, plaquetteEdgeOffset q j) then v q i j else 0 := by
    rintro ⟨c, c'⟩
    simp only [limitFormTerm]
    rw [hgen, secondDerivLimit_quaternionI hE hS hℓ hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [curlCoeff]
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : c = plaquetteEdgeOffset q i
    · by_cases h2 : c' = plaquetteEdgeOffset q j
      · subst h1 h2
        simp only [if_true, hv]
        ring
      · have : ¬ ((c, c') = (plaquetteEdgeOffset q i, plaquetteEdgeOffset q j)) := fun e => h2 (Prod.ext_iff.1 e).2
        simp [h2, this]
    · have : ¬ ((c, c') = (plaquetteEdgeOffset q i, plaquetteEdgeOffset q j)) := fun e => h1 (Prod.ext_iff.1 e).1
      simp [h1, this]
  have hsum : HasSum (fun cc : LatticeBond × LatticeBond => ∑ q ∈ plaquetteSlots, ∑ i, ∑ j, if cc = (plaquetteEdgeOffset q i, plaquetteEdgeOffset q j) then v q i j else 0)
      (∑ q ∈ plaquetteSlots, ∑ i, ∑ j, v q i j) :=
    hasSum_sum fun q _ => hasSum_sum fun i _ => hasSum_sum fun j _ => hasSum_ite_eq _ _
  have hval : ∑ q ∈ plaquetteSlots, ∑ i, ∑ j, v q i j = 1 * curvaturePairing A A' := by
    have per : ∀ q : Fin 4 × Fin 4 × Fin 4, ∑ i, ∑ j, v q i j =
        (1 / 4) * inner ℝ ((A q.1 q.2.1 : imaginaryQuaternions) : ℍ[ℝ]) ((A' q.1 q.2.1 : imaginaryQuaternions) : ℍ[ℝ]) := by
      intro q
      rw [curl_linearPotential hA (-cornerOffset q.1 q.2.1 q.2.2) q.1 q.2.1, curl_linearPotential hA' (-cornerOffset q.1 q.2.1 q.2.2) q.1 q.2.1]
      have g0 : edgeSign 0 = 1 := rfl
      have g1 : edgeSign 1 = 1 := rfl
      have g2 : edgeSign 2 = -1 := rfl
      have g3 : edgeSign 3 = -1 := rfl
      have d0 : plaquetteEdgeOffset q 0 = (-cornerOffset q.1 q.2.1 q.2.2, q.1) := rfl
      have d1 : plaquetteEdgeOffset q 1 = (-cornerOffset q.1 q.2.1 q.2.2 + Pi.single q.1 1, q.2.1) := rfl
      have d2 : plaquetteEdgeOffset q 2 = (-cornerOffset q.1 q.2.1 q.2.2 + Pi.single q.2.1 1, q.1) := rfl
      have d3 : plaquetteEdgeOffset q 3 = (-cornerOffset q.1 q.2.1 q.2.2, q.2.1) := rfl
      simp only [hv, Fin.sum_univ_four, g0, g1, g2, g3, d0, d1, d2, d3, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      ring
    rw [Finset.sum_congr rfl fun q _ => per q]
    unfold plaquetteSlots curvaturePairing
    rw [Finset.sum_filter, Fintype.sum_prod_type, one_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ν _ => ?_
    by_cases h : μ < ν
    · simp only [h, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    · simp [h]
  rw [← hval, funext hterm]
  exact hsum
end WilsonShares
theorem wilsonSharesFormCurvatureFamily_holds (hE : PlaquetteEnergySmoothBound)
    (hS : SecondOrderAtAbelianFields) (hH : HessianAtTrivialFieldStatement) :
    WilsonSharesFormCurvatureFamily := by
  intro ℓ hℓ
  obtain ⟨C, hC, hf⟩ := WilsonShares.isCurvatureFamily_of_admissible hE hℓ
  exact ⟨C, hC, hf, WilsonShares.hasCurvatureForm_wilson hE hS hH hℓ hf⟩
end YangMills.Construction.ShareFamilies
end
