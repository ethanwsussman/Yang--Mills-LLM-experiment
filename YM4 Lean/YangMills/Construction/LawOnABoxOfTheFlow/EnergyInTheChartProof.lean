import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.EnergyInTheChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusFrame LevelAction BlockAverages ResponseInTheExpansion RenormalizationStepParameters TorusLumps
section Geometry
variable {n : ℕ} [NeZero n]
private theorem plaquette_edges_mem_bondsWithin {S : Finset (TorusSite n)} {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn S) :
    (p.1, p.2.1) ∈ bondsWithin S ∧ (p.1 + TorusFields.unitStep n p.2.1, p.2.2) ∈ bondsWithin S ∧
      (p.1 + TorusFields.unitStep n p.2.2, p.2.1) ∈ bondsWithin S ∧ (p.1, p.2.2) ∈ bondsWithin S := by apply _root_.YangMills.SharedProofs.p50589 <;> assumption
private theorem plaquetteEnergy_congr {S : Finset (TorusSite n)} {W W' : TorusField n}
    (h : ∀ b ∈ bondsWithin S, W b.1 b.2 = W' b.1 b.2) {p : TorusPlaquette n} (hp : p ∈ plaquettesIn S) :
    plaquetteEnergy W p.1 p.2.1 p.2.2 = plaquetteEnergy W' p.1 p.2.1 p.2.2 := by
  obtain ⟨e1, e2, e3, e4⟩ := plaquette_edges_mem_bondsWithin hp
  have a1 := h _ e1
  have a2 := h _ e2
  have a3 := h _ e3
  have a4 := h _ e4
  simp only at a1 a2 a3 a4
  simp only [plaquetteEnergy, holonomy, a1, a2, a3, a4]
private theorem actionAtLevel_congr (a : ℝ) (L t : ℕ) (S : Finset (TorusSite n)) {W W' : TorusField n}
    (h : ∀ b ∈ bondsWithin S, W b.1 b.2 = W' b.1 b.2) :
    actionAtLevel a L t S W = actionAtLevel a L t S W' := by
  cases t with
  | zero => exact Finset.sum_congr rfl fun p hp => plaquetteEnergy_congr h hp
  | succ t =>
    show (⨅ U : (torusFrame L t n).GaugeField t, (minimalAction a (cellsOfSites (torusFrame L t n) S) t U +
        a * ∑ c ∈ innerBonds (cellsOfSites (torusFrame L t n) S) (t + 1),
          blockFit U (readAtLevel (torusFrame L t n) (t + 1) W) c)) =
      ⨅ U : (torusFrame L t n).GaugeField t, (minimalAction a (cellsOfSites (torusFrame L t n) S) t U +
        a * ∑ c ∈ innerBonds (cellsOfSites (torusFrame L t n) S) (t + 1),
          blockFit U (readAtLevel (torusFrame L t n) (t + 1) W') c)
    refine iInf_congr fun U => ?_
    congr 2
    refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2
    have c1 : c.1 ∈ sitesOfCells (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).top :=
      (Finset.mem_product.mp h1).1
    have c2 : c.1 + BlockAverages.unitStep (torusFrame L t n).top c.2 ∈
        sitesOfCells (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).top := h2
    have d1 : siteOfCell c.1 ∈ S :=
      mem_cellsOfSites_torusFrame.mp ((mem_sitesOfCells_torusFrame _ _).mp c1)
    have d2 : siteOfCell (c.1 + BlockAverages.unitStep (torusFrame L t n).top c.2) ∈ S :=
      mem_cellsOfSites_torusFrame.mp ((mem_sitesOfCells_torusFrame _ _).mp c2)
    have d3 : siteOfCell (L := L) (t := t) (m := n)
        (c.1 + BlockAverages.unitStep (torusFrame L t n).top c.2) =
        siteOfCell c.1 + TorusFields.unitStep n c.2 :=
      (siteOfCell_add (L := L) (t := t) (m := n) c.1
        (BlockAverages.unitStep (torusFrame L t n).top c.2)).trans
        (by rw [siteOfCell_unitStep])
    rw [d3] at d2
    have hb : ((siteOfCell c.1, c.2) : TorusBond n) ∈ bondsWithin S := by
      simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨d1, d2⟩
    have e : readAtLevel (torusFrame L t n) (t + 1) W c.1 c.2 =
        readAtLevel (torusFrame L t n) (t + 1) W' c.1 c.2 :=
      h _ hb
    unfold blockFit
    rw [e]
private theorem minimalAction_nonneg {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (U : F.GaugeField j), 0 ≤ minimalAction a S j U
  | 0, U => by
    refine Finset.sum_nonneg fun p _ => ?_
    have h := le_of_abs_le (abs_re_le_norm ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]))
    rw [norm_unitQuaternion] at h
    linarith
  | j + 1, V => by
    have : Nonempty (F.GaugeField j) := ⟨fun _ _ => 1⟩
    exact le_ciInf fun W => add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => by
        have h := le_of_abs_le
          (abs_re_le_norm (_root_.YangMills.Construction.BlockAverages.contourAverage W c * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])))
        rw [norm_mul, norm_unitQuaternion, mul_one] at h
        unfold blockFit
        linarith))
private theorem actionAtLevel_nonneg {a : ℝ} (ha : 0 ≤ a) (L t : ℕ) (S : Finset (TorusSite n))
    (W : TorusField n) : 0 ≤ actionAtLevel a L t S W := by
  cases t with
  | zero => exact Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg W _ _ _
  | succ t => exact minimalAction_nonneg ha _ _ _
private theorem mem_supBall_iff (o z : TorusSite n) (m : ℕ) :
    z ∈ supBall o (2 * (m : ℝ)) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ 2 * m := by
  unfold supBall
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact_mod_cast Iff.rfl
private theorem supBall_isRegularRegion (o : TorusSite n) (R : ℕ) (hR : 1024 ≤ R) (hn : 16 * R < n) :
    IsRegularRegion (supBall o (2 * (R : ℝ))) 1024 := by
  intro z
  refine ⟨fun i => if 0 ≤ (z i - o i).valMinAbs then -1 else 1, fun i => ?_, fun q hq hd h hs hb => ?_⟩
  · by_cases hi : 0 ≤ (z i - o i).valMinAbs <;> simp [hi]
  rw [mem_supBall_iff] at hq ⊢
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff] at hq hd ⊢
  intro i
  have hqi := hq i
  have hdi := hd i
  have hzi : ((z i - o i).valMinAbs).natAbs ≤ n / 2 := ZMod.natAbs_valMinAbs_le _
  have hsi := hs i
  have hbi := abs_le.mp (hb i)
  set ez := (z i - o i).valMinAbs with hez
  set eq' := (q i - o i).valMinAbs with heq
  set et := (q i - z i).valMinAbs with het
  have c1 : ((ez : ℤ) : ZMod n) = z i - o i := ZMod.coe_valMinAbs _
  have c2 : ((eq' : ℤ) : ZMod n) = q i - o i := ZMod.coe_valMinAbs _
  have c3 : ((et : ℤ) : ZMod n) = q i - z i := ZMod.coe_valMinAbs _
  have hz0 : ((eq' - ez - et : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [c1, c2, c3]
    ring
  have hdvd : (n : ℤ) ∣ eq' - ez - et := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0
  have hzero : eq' - ez - et = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [abs_lt]
    omega
  have hval : (q + siteOfInt h : TorusSite n) i - o i = ((eq' + h i : ℤ) : ZMod n) := by
    push_cast
    rw [c2]
    simp only [siteOfInt, Pi.add_apply]
    ring
  rw [hval]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  by_cases hi : 0 ≤ ez
  · simp only [hez.symm, hi, if_true] at hsi
    omega
  · simp only [hez.symm, hi, if_false] at hsi
    omega
end Geometry
section Moves
variable {n : ℕ} [NeZero n] {N : ℕ}
private theorem perturb_apply (e : TorusBond n ≃ Fin N) (X : Fin N → imaginaryQuaternions) (σ : Fin N → ℝ)
    (W : TorusField n) (x : TorusSite n) (i : Fin 4) :
    perturb (fun l => e.symm l) X σ W x i = expUnit (σ (e (x, i)) • X (e (x, i))) * W x i := by
  show expUnit (∑ l, if e.symm l = (x, i) then σ l • X l else 0) * W x i = _
  congr 2
  rw [Finset.sum_eq_single (e (x, i))]
  · simp
  · intro l _ hl
    rw [if_neg]
    intro h
    apply hl
    rw [← h]
    simp
  · simp
private def pullbackCLM {k : ℕ} (f : Fin k → Fin N) : (Fin k → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    ∑ m, if f m = l then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) m else 0
private theorem pullbackCLM_apply {k : ℕ} (f : Fin k → Fin N) (σ : Fin k → ℝ) (l : Fin N) :
    pullbackCLM f σ l = ∑ m, if f m = l then σ m else 0 := by
  simp only [pullbackCLM, ContinuousLinearMap.coe_pi', FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp
private theorem pullbackCLM_single {k : ℕ} (f : Fin k → Fin N) (m : Fin k) :
    pullbackCLM f (Pi.single m 1) = Pi.single (f m) 1 := by
  funext l
  rw [pullbackCLM_apply, Finset.sum_eq_single m]
  · by_cases h : f m = l
    · subst h
      simp
    · have h' : l ≠ f m := fun e => h e.symm
      simp [h, h']
  · intro m' _ hm
    simp [hm]
  · simp
private theorem perturb_pullback (e : TorusBond n ≃ Fin N) {k : ℕ} (f : Fin k → Fin N)
    (X : Fin N → imaginaryQuaternions) (σ : Fin k → ℝ) (W : TorusField n) :
    perturb (fun m => e.symm (f m)) (fun m => X (f m)) σ W =
      perturb (fun l => e.symm l) X (pullbackCLM f σ) W := by
  funext x i
  rw [perturb_apply]
  show expUnit (∑ m, if e.symm (f m) = (x, i) then σ m • X (f m) else 0) * W x i = _
  congr 2
  rw [pullbackCLM_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : f m = e (x, i)
  · have h2 : e.symm (f m) = (x, i) := by rw [h]; simp
    rw [if_pos h2, if_pos h, h]
  · have h2 : e.symm (f m) ≠ (x, i) := fun h' => h (by rw [← h']; simp)
    rw [if_neg h2, if_neg h, zero_smul]
private theorem iteratedFDeriv_comp_clm {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (g : E →L[ℝ] E') {f : E' → ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 3 f (g x₀)) {i : ℕ} (hi : i ≤ 3) :
    iteratedFDeriv ℝ i (f ∘ g) x₀ =
      (iteratedFDeriv ℝ i f (g x₀)).compContinuousLinearMap fun _ => g := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨v, hvu, hv, hxv⟩ := mem_nhds_iff.mp hu
  have hfv := hfu.mono hvu
  have hpre : IsOpen (g ⁻¹' v) := hv.preimage g.continuous
  have key := g.iteratedFDerivWithin_comp_right hfv hv.uniqueDiffOn hpre.uniqueDiffOn hxv (i := i)
    (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen i hpre (show x₀ ∈ g ⁻¹' v from hxv),
    iteratedFDerivWithin_of_isOpen i hv hxv] at key
  exact key
private def perturbLine (e : TorusBond n ≃ Fin N) (G : TorusField n → ℝ) (X : Fin N → imaginaryQuaternions)
    (W : TorusField n) (σ : Fin N → ℝ) : ℝ :=
  G (perturb (fun l => e.symm l) X σ W)
private theorem mixedDeriv_eq_iteratedFDeriv (e : TorusBond n ≃ Fin N) {k : ℕ} (hk : k ≤ 3)
    (G : TorusField n → ℝ) (W : TorusField n) (X : Fin N → imaginaryQuaternions) (f : Fin k → Fin N)
    (hC : ContDiffAt ℝ 3 (perturbLine e G X W) 0) :
    mixedDeriv G W (fun m => e.symm (f m)) (fun m => X (f m)) =
      iteratedFDeriv ℝ k (perturbLine e G X W) 0 (fun m => Pi.single (f m) 1) := by
  have h1 : (fun σ : Fin k → ℝ => G (perturb (fun m => e.symm (f m)) (fun m => X (f m)) σ W)) =
      perturbLine e G X W ∘ pullbackCLM f := by
    funext σ
    simp only [Function.comp, perturbLine, perturb_pullback]
  have hC' : ContDiffAt ℝ 3 (perturbLine e G X W) (pullbackCLM f 0) := by simpa using hC
  unfold mixedDeriv
  rw [h1, iteratedFDeriv_comp_clm (pullbackCLM f) hC' hk]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, pullbackCLM_single]
private def diagScaleCLM (a : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun l => a l • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) l
private theorem diagScaleCLM_apply (a σ : Fin N → ℝ) (l : Fin N) : diagScaleCLM a σ l = a l * σ l := by
  simp [diagScaleCLM]
private theorem diagScaleCLM_single (a : Fin N → ℝ) (l : Fin N) :
    diagScaleCLM a (Pi.single l 1) = a l • Pi.single l (1 : ℝ) := by
  funext m
  rw [diagScaleCLM_apply]
  by_cases h : m = l
  · subst h
    simp
  · simp [h]
private theorem perturbLine_scale (e : TorusBond n ≃ Fin N) (G : TorusField n → ℝ) (a : Fin N → ℝ)
    (U : Fin N → imaginaryQuaternions) (W : TorusField n) :
    perturbLine e G (fun l => a l • U l) W = perturbLine e G U W ∘ diagScaleCLM a := by
  funext σ
  simp only [Function.comp, perturbLine]
  congr 1
  funext x i
  rw [perturb_apply, perturb_apply, diagScaleCLM_apply, smul_smul, mul_comm]
private theorem norm_imaginaryUnitI : ‖imaginaryUnitI‖ = 1 := by apply _root_.YangMills.SharedProofs.p16675 <;> assumption
private theorem third_deriv_term_bound (e : TorusBond n ≃ Fin N) {G : TorusField n → ℝ} {W : TorusField n}
    (hC : ContDiffThreeAt G W) {C δ : ℝ}
    (hb : ∀ (c : Fin 3 → TorusBond n) (Xs : Fin 3 → imaginaryQuaternions), AreUnitVectors Xs →
      |mixedDeriv G W c Xs| ≤ C * Real.exp (-δ * bondListSpread c))
    (X : Fin N → imaginaryQuaternions) (r : Fin 3 → Fin N) :
    |iteratedFDeriv ℝ 3 (perturbLine e G X W) 0 (fun m => Pi.single (r m) 1)| ≤
      (∏ m, ‖X (r m)‖) * (C * Real.exp (-δ * bondListSpread (fun m => e.symm (r m)))) := by
  classical
  set U : Fin N → imaginaryQuaternions := fun l => if X l = 0 then imaginaryUnitI else ‖X l‖⁻¹ • X l
    with hUdef
  have hU : ∀ l, ‖U l‖ = 1 := by
    intro l
    by_cases h : X l = 0
    · simp only [hUdef, if_pos h]
      exact norm_imaginaryUnitI
    · have h' : ‖X l‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp only [hUdef, if_neg h]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h']
  have hX : (fun l => ‖X l‖ • U l) = X := by
    funext l
    by_cases h : X l = 0
    · simp [h]
    · have h' : ‖X l‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp only [hUdef, if_neg h]
      rw [smul_smul, mul_inv_cancel₀ h', one_smul]
  have hCU : ContDiffAt ℝ 3 (perturbLine e G U W) 0 := hC N _ U
  have hCU' : ContDiffAt ℝ 3 (perturbLine e G U W) (diagScaleCLM (fun l => ‖X l‖) 0) := by simpa using hCU
  have hH : perturbLine e G X W = perturbLine e G U W ∘ diagScaleCLM (fun l => ‖X l‖) := by
    rw [← perturbLine_scale]
    rw [hX]
  have hd := mixedDeriv_eq_iteratedFDeriv e (le_refl 3) G W U r hCU
  have hu : AreUnitVectors (fun m => U (r m)) := fun m => hU _
  have hbound := hb (fun m => e.symm (r m)) (fun m => U (r m)) hu
  rw [hd] at hbound
  rw [hH, iteratedFDeriv_comp_clm _ hCU' (le_refl 3)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, diagScaleCLM_single]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun _ _ => norm_nonneg _)
private def tripleEquivFun (ι : Type) : ι × ι × ι ≃ (Fin 3 → ι) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun r := (r 0, r 1, r 2)
  left_inv t := rfl
  right_inv r := by
    funext i
    fin_cases i <;> rfl
private theorem sum_fun_fin_three {ι : Type} [Fintype ι] (F : (Fin 3 → ι) → ℝ) :
    ∑ r : Fin 3 → ι, F r = ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
  classical
  rw [← (tripleEquivFun ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl
private theorem sum_fun_fin_two {ι : Type} [Fintype ι] (F : (Fin 2 → ι) → ℝ) :
    ∑ r : Fin 2 → ι, F r = ∑ a, ∑ b, F ![a, b] := by
  classical
  rw [← (finTwoArrowEquiv ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl
private def bondExpMass (δ : ℝ) : ℝ := 4 * (2 / (1 - Real.exp (-(δ / 2) / 4))) ^ 4
private theorem sum_exp_supDist_le_bondExpMass (e : TorusBond n ≃ Fin N) {δ : ℝ} (hδ : 0 < δ) (l : Fin N) :
    ∑ l', Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (e.symm l).1 (e.symm l').1) ≤ bondExpMass δ := by
  have h1 : ∑ l', Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (e.symm l).1 (e.symm l').1) =
      ∑ b : TorusBond n, Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist b.1 (e.symm l).1) := by
    rw [← e.symm.sum_comp (fun b : TorusBond n => Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist b.1 (e.symm l).1))]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  rw [h1, Fintype.sum_prod_type]
  have h2 := sum_exp_neg_mul_supDist_le (n := n) (β := δ / 2) (by positivity) (e.symm l).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  unfold bondExpMass
  push_cast
  linarith
private theorem sum_weighted_pairs_le {ι : Type} [Fintype ι] {φ : ι → ℝ} {w : ι → ι → ℝ} {Q : ℝ}
    (hφ : ∀ l, 0 ≤ φ l) (hw : ∀ l l', 0 ≤ w l l') (hQ : ∀ l, ∑ l', w l l' ≤ Q) :
    ∑ a, ∑ b, ∑ c, φ a * (w a b * w a c) ≤ Q ^ 2 * ∑ a, φ a := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hs : ∑ b, ∑ c, φ a * (w a b * w a c) = φ a * ((∑ b, w a b) * ∑ c, w a c) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [hs]
  have h0 : 0 ≤ ∑ b, w a b := Finset.sum_nonneg fun b _ => hw a b
  have h1 := hQ a
  have h2 : (∑ b, w a b) * ∑ c, w a c ≤ Q ^ 2 := by nlinarith
  nlinarith [hφ a]
private theorem schur_triple_bound (e : TorusBond n ≃ Fin N) {δ s : ℝ} (hδ : 0 < δ) {a : Fin N → ℝ}
    (ha : ∀ l, 0 ≤ a l) (hs : ∀ l, a l ≤ s) :
    ∑ r : Fin 3 → Fin N, (∏ m, a (r m)) * Real.exp (-δ * bondListSpread (fun m => e.symm (r m))) ≤
      s * bondExpMass δ ^ 2 * ∑ l, a l ^ 2 := by
  set w : Fin N → Fin N → ℝ := fun l l' => Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (e.symm l).1 (e.symm l').1)
    with hw
  have hw0 : ∀ l l', 0 ≤ w l l' := fun _ _ => (Real.exp_pos _).le
  have hQ : ∀ l, ∑ l', w l l' ≤ bondExpMass δ := sum_exp_supDist_le_bondExpMass e hδ
  have hterm : ∀ x y z : Fin N, (∏ m, a ((![x, y, z] : Fin 3 → Fin N) m)) *
      Real.exp (-δ * bondListSpread (fun m => e.symm ((![x, y, z] : Fin 3 → Fin N) m))) ≤
      s / 2 * (a x ^ 2 * (w x y * w x z)) + s / 2 * (a y ^ 2 * (w y x * w y z)) := by
    intro x y z
    set c : Fin 3 → TorusBond n := fun m => e.symm ((![x, y, z] : Fin 3 → Fin N) m) with hc
    have hd : ∀ i j : Fin 3, _root_.YangMills.Construction.TorusFields.supDist (c i).1 (c j).1 ≤ bondListSpread c := by
      intro i j
      have h1 := Finset.le_sup (f := fun l' : Fin 3 => _root_.YangMills.Construction.TorusFields.supDist (c i).1 (c l').1) (Finset.mem_univ j)
      have h2 := Finset.le_sup
        (f := fun l : Fin 3 => Finset.univ.sup fun l' : Fin 3 => _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c l').1)
        (Finset.mem_univ i)
      exact h1.trans h2
    have hE : ∀ i j k : Fin 3, Real.exp (-δ * bondListSpread c) ≤
        Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c i).1 (c j).1) * Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c i).1 (c k).1) := by
      intro i j k
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : (_root_.YangMills.Construction.TorusFields.supDist (c i).1 (c j).1 : ℝ) ≤ bondListSpread c := by exact_mod_cast hd i j
      have h2 : (_root_.YangMills.Construction.TorusFields.supDist (c i).1 (c k).1 : ℝ) ≤ bondListSpread c := by exact_mod_cast hd i k
      nlinarith
    have e1 := hE 0 1 2
    have e2 := hE 1 0 2
    have ax := ha x
    have ay := ha y
    have az := ha z
    have hprod : ∏ m, a ((![x, y, z] : Fin 3 → Fin N) m) = a x * a y * a z := by
      simp [Fin.prod_univ_three]
    rw [hprod]
    have hw1 : w x y * w x z = Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
      Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 2).1) := rfl
    have hw2 : w y x * w y z = Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 1).1 (c 0).1) *
      Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 1).1 (c 2).1) := rfl
    rw [← hw1] at e1
    rw [← hw2] at e2
    have hE0 : 0 ≤ Real.exp (-δ * bondListSpread c) := (Real.exp_pos _).le
    have hs0 : 0 ≤ s := ax.trans (hs x)
    have hz : a z ≤ s := hs z
    have hxy : a x * a y ≤ (a x ^ 2 + a y ^ 2) / 2 := by nlinarith [sq_nonneg (a x - a y)]
    have h3 : a x * a y * a z ≤ s / 2 * a x ^ 2 + s / 2 * a y ^ 2 := by
      have : a x * a y * a z ≤ a x * a y * s := mul_le_mul_of_nonneg_left hz (mul_nonneg ax ay)
      nlinarith
    calc a x * a y * a z * Real.exp (-δ * bondListSpread c)
        ≤ (s / 2 * a x ^ 2 + s / 2 * a y ^ 2) * Real.exp (-δ * bondListSpread c) :=
          mul_le_mul_of_nonneg_right h3 hE0
      _ = s / 2 * a x ^ 2 * Real.exp (-δ * bondListSpread c) +
          s / 2 * a y ^ 2 * Real.exp (-δ * bondListSpread c) := by ring
      _ ≤ s / 2 * a x ^ 2 * (w x y * w x z) + s / 2 * a y ^ 2 * (w y x * w y z) := by
          refine add_le_add (mul_le_mul_of_nonneg_left e1 (by positivity))
            (mul_le_mul_of_nonneg_left e2 (by positivity))
      _ = _ := by ring
  have hs0 : 0 ≤ s ∨ IsEmpty (Fin N) := by
    by_cases h : Nonempty (Fin N)
    · obtain ⟨l⟩ := h
      exact Or.inl ((ha l).trans (hs l))
    · exact Or.inr (not_nonempty_iff.mp h)
  rw [sum_fun_fin_three]
  have hA := sum_weighted_pairs_le (φ := fun l => a l ^ 2) (fun l => sq_nonneg _) hw0 hQ
  have hB : ∑ x, ∑ y, ∑ z, a y ^ 2 * (w y x * w y z) ≤ bondExpMass δ ^ 2 * ∑ l, a l ^ 2 := by
    rw [Finset.sum_comm]
    exact hA
  calc _ ≤ ∑ x, ∑ y, ∑ z, (s / 2 * (a x ^ 2 * (w x y * w x z)) + s / 2 * (a y ^ 2 * (w y x * w y z))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ => hterm x y z
    _ = s / 2 * (∑ x, ∑ y, ∑ z, a x ^ 2 * (w x y * w x z)) +
        s / 2 * (∑ x, ∑ y, ∑ z, a y ^ 2 * (w y x * w y z)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ s * bondExpMass δ ^ 2 * ∑ l, a l ^ 2 := by
        rcases hs0 with h0 | h0
        · have := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ s / 2)
          have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ s / 2)
          nlinarith
        · simp [Finset.univ_eq_empty]
private theorem third_deriv_bound (e : TorusBond n ≃ Fin N) {G : TorusField n → ℝ} {W : TorusField n}
    (hC : ContDiffThreeAt G W) {C δ s : ℝ} (hC0 : 0 ≤ C) (hδ : 0 < δ)
    (hb : ∀ (c : Fin 3 → TorusBond n) (Xs : Fin 3 → imaginaryQuaternions), AreUnitVectors Xs →
      |mixedDeriv G W c Xs| ≤ C * Real.exp (-δ * bondListSpread c))
    (X : Fin N → imaginaryQuaternions) (hs : ∀ l, ‖X l‖ ≤ s) :
    |iteratedFDeriv ℝ 3 (perturbLine e G X W) 0 (fun _ => fun _ => 1)| ≤
      C * (s * bondExpMass δ ^ 2 * ∑ l, ‖X l‖ ^ 2) := by
  have h1 : (fun _ : Fin N => (1 : ℝ)) = ∑ l, Pi.single l (1 : ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1, ContinuousMultilinearMap.map_sum (iteratedFDeriv ℝ 3 (perturbLine e G X W) 0)
    (fun _ (l : Fin N) => (Pi.single l (1 : ℝ) : Fin N → ℝ))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ r : Fin 3 → Fin N,
        (∏ m, ‖X (r m)‖) * (C * Real.exp (-δ * bondListSpread (fun m => e.symm (r m)))) :=
        Finset.sum_le_sum fun r _ => third_deriv_term_bound e hC hb X r
    _ = C * ∑ r : Fin 3 → Fin N,
        (∏ m, ‖X (r m)‖) * Real.exp (-δ * bondListSpread (fun m => e.symm (r m))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (schur_triple_bound e hδ (fun l => norm_nonneg _) hs) hC0
end Moves
section Line
variable {n : ℕ} [NeZero n] {N : ℕ}
private def constCLM : ℝ →L[ℝ] (Fin N → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ (fun _ => 1)
private theorem constCLM_apply (τ : ℝ) (l : Fin N) : (constCLM τ : Fin N → ℝ) l = τ := by
  simp [constCLM]
private def expLineField (e : TorusBond n ≃ Fin N) (X : Fin N → imaginaryQuaternions) (τ : ℝ) :
    TorusField n :=
  perturb (fun l => e.symm l) X (constCLM τ) (trivialField n)
private theorem expLineField_apply (e : TorusBond n ≃ Fin N) (X : Fin N → imaginaryQuaternions) (τ : ℝ)
    (x : TorusSite n) (i : Fin 4) :
    expLineField e X τ x i = expUnit (τ • X (e (x, i))) := by
  rw [expLineField, perturb_apply, constCLM_apply]
  simp [trivialField]
private theorem perturb_expLineField (e : TorusBond n ≃ Fin N) (X : Fin N → imaginaryQuaternions) (τ : ℝ)
    (σ : Fin N → ℝ) :
    perturb (fun l => e.symm l) X σ (expLineField e X τ) =
      perturb (fun l => e.symm l) X (σ + constCLM τ) (trivialField n) := by
  funext x i
  rw [perturb_apply, expLineField_apply, perturb_apply, expUnit_smul_mul]
  simp [trivialField, constCLM_apply]
private theorem taylor_action_bound (e : TorusBond n ≃ Fin N) (X : Fin N → imaginaryQuaternions)
    {G : TorusField n → ℝ} {B : ℝ}
    (hnn : ∀ W, 0 ≤ G W) (h0 : G (trivialField n) = 0)
    (hC : ∀ τ : ℝ, -1 < τ → τ < 2 → ContDiffThreeAt G (expLineField e X τ))
    (hB : ∀ τ : ℝ, 0 < τ → τ < 1 →
      |iteratedFDeriv ℝ 3 (perturbLine e G X (expLineField e X τ)) 0 (fun _ => fun _ => 1)| ≤ B) :
    |G (expLineField e X 1) -
        1 / 2 * iteratedFDeriv ℝ 2 (perturbLine e G X (trivialField n)) 0 (fun _ => fun _ => 1)| ≤
      B / 6 := by
  set H := perturbLine e G X (trivialField n) with hH
  set g : ℝ → ℝ := H ∘ (constCLM : ℝ →L[ℝ] (Fin N → ℝ)) with hg
  have hgval : ∀ τ, g τ = G (expLineField e X τ) := fun τ => rfl
  have hshift : ∀ τ : ℝ, perturbLine e G X (expLineField e X τ) = fun σ => H (σ + constCLM τ) := by
    intro τ
    funext σ
    simp only [perturbLine, hH, perturb_expLineField]
  have hHC : ∀ τ : ℝ, -1 < τ → τ < 2 → ContDiffAt ℝ 3 H (constCLM τ) := by
    intro τ h1 h2
    have h := hC τ h1 h2 N (fun l => e.symm l) X
    have h' : ContDiffAt ℝ 3 (fun σ => H (σ + constCLM τ)) (constCLM τ - constCLM τ) := by
      rw [sub_self, ← hshift]
      exact h
    have hsb : ContDiffAt ℝ 3 (fun σ : Fin N → ℝ => σ - constCLM τ) (constCLM τ) :=
      contDiffAt_id.sub contDiffAt_const
    have h3 := ContDiffAt.comp (f := fun σ : Fin N → ℝ => σ - constCLM τ) (constCLM τ : Fin N → ℝ) h' hsb
    have h4 : ((fun σ => H (σ + constCLM τ)) ∘ fun σ : Fin N → ℝ => σ - constCLM τ) = H := by
      funext σ
      simp
    rwa [h4] at h3
  have hgC : ∀ τ : ℝ, -1 < τ → τ < 2 → ContDiffAt ℝ 3 g τ := fun τ h1 h2 =>
    (hHC τ h1 h2).comp τ (ContinuousLinearMap.contDiff _).contDiffAt
  have h01 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hgOn : ContDiffOn ℝ ((2 : ℕ) + 1) g (Set.uIcc 0 1) := by
    intro τ hτ
    rw [h01] at hτ
    have : ContDiffAt ℝ ((2 : ℕ) + 1) g τ := by
      have := hgC τ (by linarith [hτ.1]) (by linarith [hτ.2])
      norm_num
      exact this
    exact this.contDiffWithinAt
  obtain ⟨ξ, hξ, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (x₀ := 0) (x := 1)
    (by norm_num) hgOn
  have hξ' : 0 < ξ ∧ ξ < 1 := by
    have : Set.uIoo (0 : ℝ) 1 = Set.Ioo 0 1 := Set.uIoo_of_le zero_le_one
    rw [this] at hξ
    exact hξ
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by rw [h01]; exact ⟨le_rfl, zero_le_one⟩
  have hg0 := hgC 0 (by norm_num) (by norm_num)
  have hwithin : ∀ k : ℕ, k ≤ 3 → iteratedDerivWithin k g (Set.uIcc 0 1) 0 = iteratedDeriv k g 0 := by
    intro k hk
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_eq_iteratedFDeriv hu (hg0.of_le (by exact_mod_cast hk)) hmem]
  have hl0 : expLineField e X 0 = trivialField n := by
    funext x i
    rw [expLineField_apply]
    simp [trivialField, expUnit_zero]
  have hgz : g 0 = 0 := by rw [hgval, hl0, h0]
  have hd1 : iteratedDeriv 1 g 0 = 0 := by
    rw [iteratedDeriv_one]
    have hmin : IsLocalMin g 0 := Filter.Eventually.of_forall fun y => by
      rw [hgz, hgval]
      exact hnn _
    exact hmin.deriv_eq_zero
  have hone : ((constCLM : ℝ →L[ℝ] (Fin N → ℝ)) 1) = fun _ => 1 := by
    funext l
    exact constCLM_apply 1 l
  have hd2 : iteratedDeriv 2 g 0 = iteratedFDeriv ℝ 2 H 0 (fun _ => fun _ => 1) := by
    have hCH : ContDiffAt ℝ 3 H (constCLM (0 : ℝ)) := hHC 0 (by norm_num) (by norm_num)
    rw [iteratedDeriv_eq_iteratedFDeriv, hg, iteratedFDeriv_comp_clm _ hCH (by norm_num)]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, hone]
  have hd3 : iteratedDeriv 3 g ξ =
      iteratedFDeriv ℝ 3 (perturbLine e G X (expLineField e X ξ)) 0 (fun _ => fun _ => 1) := by
    have hCH : ContDiffAt ℝ 3 H (constCLM ξ) := hHC ξ (by linarith [hξ'.1]) (by linarith [hξ'.2])
    rw [iteratedDeriv_eq_iteratedFDeriv, hg, iteratedFDeriv_comp_clm _ hCH (le_refl 3), hshift,
      iteratedFDeriv_comp_add_right 3 (constCLM ξ : Fin N → ℝ) 0, zero_add]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, hone]
  rw [taylor_within_apply] at hT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hT
  rw [hwithin 0 (by norm_num), hwithin 1 (by norm_num), hwithin 2 (by norm_num), hd1, hd2, hd3,
    iteratedDeriv_zero, hgz] at hT
  have hfin : g 1 - 1 / 2 * iteratedFDeriv ℝ 2 H 0 (fun _ => fun _ => 1) =
      iteratedFDeriv ℝ 3 (perturbLine e G X (expLineField e X ξ)) 0 (fun _ => fun _ => 1) / 6 := by
    norm_num [Nat.factorial] at hT
    linarith
  rw [← hgval, hfin, abs_div]
  have := hB ξ hξ'.1 hξ'.2
  norm_num
  linarith
private theorem second_deriv_eq_sum (e : TorusBond n ≃ Fin N) (v : TorusBond n → imaginaryQuaternions)
    {G : TorusField n → ℝ}
    (hC : ContDiffAt ℝ 3 (perturbLine e G (fun l => v (e.symm l)) (trivialField n)) 0) :
    iteratedFDeriv ℝ 2 (perturbLine e G (fun l => v (e.symm l)) (trivialField n)) 0 (fun _ => fun _ => 1) =
      ∑ b : TorusBond n, ∑ b' : TorusBond n, mixedDeriv G (trivialField n) ![b, b'] ![v b, v b'] := by
  have h1 : (fun _ : Fin N => (1 : ℝ)) = ∑ l, Pi.single l (1 : ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1, ContinuousMultilinearMap.map_sum
    (iteratedFDeriv ℝ 2 (perturbLine e G (fun l => v (e.symm l)) (trivialField n)) 0)
    (fun _ (l : Fin N) => (Pi.single l (1 : ℝ) : Fin N → ℝ))]
  rw [sum_fun_fin_two (fun r => iteratedFDeriv ℝ 2
    (perturbLine e G (fun l => v (e.symm l)) (trivialField n)) 0
    (fun i => Pi.single (r i) (1 : ℝ)))]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l' _ => ?_
  have h := mixedDeriv_eq_iteratedFDeriv e (k := 2) (by norm_num) G (trivialField n)
    (fun l => v (e.symm l)) ![l, l'] hC
  rw [← h]
  congr 1
  · funext m
    fin_cases m <;> rfl
  · funext m
    fin_cases m <;> rfl
private theorem sum_injOn_le {P : Finset (TorusPlaquette n)} {B : Finset (TorusBond n)}
    (f : TorusPlaquette n → TorusBond n × Fin 4)
    (hinj : Set.InjOn f P) (hmap : ∀ p ∈ P, (f p).1 ∈ B) (g : TorusBond n → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ p ∈ P, g (f p).1 ≤ 4 * ∑ b ∈ B, g b := by
  classical
  have h1 : ∑ p ∈ P, g (f p).1 = ∑ q ∈ P.image f, g q.1 :=
    (Finset.sum_image (f := fun q : TorusBond n × Fin 4 => g q.1) hinj).symm
  have h2 : ∑ q ∈ P.image f, g q.1 ≤ ∑ q ∈ B ×ˢ (Finset.univ : Finset (Fin 4)), g q.1 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => hg _
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨hmap p hp, Finset.mem_univ _⟩
  have h3 : ∑ q ∈ B ×ˢ (Finset.univ : Finset (Fin 4)), g q.1 = 4 * ∑ b ∈ B, g b := by
    rw [Finset.sum_product]
    simp [Finset.mul_sum]
  linarith
private theorem curlNormSq_le (S : Finset (TorusSite n)) (D : TorusBond n → imaginaryQuaternions) :
    curlNormSq S D ≤ 64 * bondNormSq S D := by
  classical
  set g : TorusBond n → ℝ := fun b => ‖D b‖ ^ 2 with hgdef
  have hg : ∀ b, 0 ≤ g b := fun b => sq_nonneg _
  have hterm : ∀ p : TorusPlaquette n, ‖lieFormCurl D p‖ ^ 2 ≤
      4 * (g (p.1, p.2.1) + g (p.1 + TorusFields.unitStep n p.2.1, p.2.2) +
        g (p.1 + TorusFields.unitStep n p.2.2, p.2.1) + g (p.1, p.2.2)) := by
    intro p
    have h : ‖lieFormCurl D p‖ ≤ ‖D (p.1, p.2.1)‖ + ‖D (p.1 + TorusFields.unitStep n p.2.1, p.2.2)‖ +
        ‖D (p.1 + TorusFields.unitStep n p.2.2, p.2.1)‖ + ‖D (p.1, p.2.2)‖ := by
      unfold lieFormCurl
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    have h0 := norm_nonneg (lieFormCurl D p)
    simp only [hgdef]
    set a := ‖D (p.1, p.2.1)‖
    set b := ‖D (p.1 + TorusFields.unitStep n p.2.1, p.2.2)‖
    set c := ‖D (p.1 + TorusFields.unitStep n p.2.2, p.2.1)‖
    set d := ‖D (p.1, p.2.2)‖
    have h1 : ‖lieFormCurl D p‖ ^ 2 ≤ (a + b + c + d) ^ 2 := pow_le_pow_left₀ h0 h 2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d)]
  have i1 := sum_injOn_le (P := plaquettesIn S) (B := bondsWithin S)
    (fun p => ((p.1, p.2.1), p.2.2))
    (fun p _ q _ h => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.mp h1
      exact Prod.ext h3 (Prod.ext h4 h2))
    (fun p hp => (plaquette_edges_mem_bondsWithin hp).1) g hg
  have i2 := sum_injOn_le (P := plaquettesIn S) (B := bondsWithin S)
    (fun p => ((p.1 + TorusFields.unitStep n p.2.1, p.2.2), p.2.1))
    (fun p _ q _ h => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.mp h1
      simp only at h2 h3 h4
      have h5 : p.1 = q.1 := by
        rw [h2] at h3
        exact add_right_cancel h3
      exact Prod.ext h5 (Prod.ext h2 h4))
    (fun p hp => (plaquette_edges_mem_bondsWithin hp).2.1) g hg
  have i3 := sum_injOn_le (P := plaquettesIn S) (B := bondsWithin S)
    (fun p => ((p.1 + TorusFields.unitStep n p.2.2, p.2.1), p.2.2))
    (fun p _ q _ h => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.mp h1
      simp only at h2 h3 h4
      have h5 : p.1 = q.1 := by
        rw [h2] at h3
        exact add_right_cancel h3
      exact Prod.ext h5 (Prod.ext h4 h2))
    (fun p hp => (plaquette_edges_mem_bondsWithin hp).2.2.1) g hg
  have i4 := sum_injOn_le (P := plaquettesIn S) (B := bondsWithin S)
    (fun p => ((p.1, p.2.2), p.2.1))
    (fun p _ q _ h => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.mp h1
      exact Prod.ext h3 (Prod.ext h2 h4))
    (fun p hp => (plaquette_edges_mem_bondsWithin hp).2.2.2) g hg
  simp only at i1 i2 i3 i4
  calc curlNormSq S D ≤ ∑ p ∈ plaquettesIn S, 4 * (g (p.1, p.2.1) +
        g (p.1 + TorusFields.unitStep n p.2.1, p.2.2) +
        g (p.1 + TorusFields.unitStep n p.2.2, p.2.1) + g (p.1, p.2.2)) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = 4 * (∑ p ∈ plaquettesIn S, g (p.1, p.2.1) +
        ∑ p ∈ plaquettesIn S, g (p.1 + TorusFields.unitStep n p.2.1, p.2.2) +
        ∑ p ∈ plaquettesIn S, g (p.1 + TorusFields.unitStep n p.2.2, p.2.1) +
        ∑ p ∈ plaquettesIn S, g (p.1, p.2.2)) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
    _ ≤ 64 * bondNormSq S D := by
        have : bondNormSq S D = ∑ b ∈ bondsWithin S, g b := rfl
        rw [this]
        linarith
private theorem psd_quadratic_diff_le {V : Type} [AddCommGroup V] [Module ℝ V] (q : V → V → ℝ)
    (hsym : ∀ u v, q u v = q v u) (hlin : ∀ (c : ℝ) (u u' v : V), q (c • u + u') v = c * q u v + q u' v)
    (hpsd : ∀ v, 0 ≤ q v v) (u D : V) {t : ℝ} (ht : 0 < t) :
    |q (u + D) (u + D) - q u u| ≤ t * q u u + q D D / t + q D D := by
  have hadd : ∀ c : ℝ, q (c • u + D) (c • u + D) = c ^ 2 * q u u + 2 * c * q u D + q D D := by
    intro c
    have a1 : q (c • u + D) (c • u + D) = c * q u (c • u + D) + q D (c • u + D) := hlin _ _ _ _
    have a2 : q u (c • u + D) = c * q u u + q D u := by rw [hsym u, hlin]
    have a3 : q D (c • u + D) = c * q u D + q D D := by rw [hsym D, hlin]
    rw [a1, a2, a3, hsym D u]
    ring
  have h1 := hadd 1
  have p1 := hpsd (t • u + D)
  have p2 := hpsd ((-t) • u + D)
  rw [hadd] at p1 p2
  rw [one_smul] at h1
  rw [h1]
  have hD : q D D / t * t = q D D := div_mul_cancel₀ _ ht.ne'
  set w := q D D / t with hw
  have b1 : 2 * q u D ≤ t * q u u + w := by
    have : t * (t * q u u + w - 2 * q u D) ≥ 0 := by nlinarith
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith
  have b2 : -(2 * q u D) ≤ t * q u u + w := by
    have : t * (t * q u u + w + 2 * q u D) ≥ 0 := by nlinarith
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith [hpsd D]
private theorem eventually_boxRadius_cube_le {κ₀ : ℝ} (h0 : 0 < κ₀) (h2 : κ₀ ≤ 1 / 21) (R₁ : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ xf : ℝ, 1 < xf ∧ ∀ x, xf ≤ x →
      R₁ ≤ boxRadius κ₀ x ∧ (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x ≤ ε := by
  have ea : ∀ᶠ x : ℝ in Filter.atTop, (R₁ : ℝ) ≤ x ^ κ₀ :=
    (tendsto_rpow_atTop h0).eventually_ge_atTop _
  have eb : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ ε / 16 * ‖x ^ (5 / 14 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 14)).def (by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (ea.and eb)
  refine ⟨max x₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  have hxa : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨ha, hb⟩ := hx₁ x hxa
  have hR : x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) := Nat.le_ceil _
  have hR' : (boxRadius κ₀ x : ℝ) ≤ x ^ κ₀ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  refine ⟨by exact_mod_cast ha.trans hR, ?_⟩
  have hx1 : 1 ≤ x ^ κ₀ := Real.one_le_rpow (by linarith) h0.le
  have hRle : (boxRadius κ₀ x : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by
    have : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h2
    linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hb' : Real.log x ≤ ε / 16 * x ^ (5 / 14 : ℝ) := by
    have hp : 0 < x ^ (5 / 14 : ℝ) := by positivity
    rwa [Real.norm_of_nonneg hlog.le, Real.norm_of_nonneg hp.le] at hb
  have hR3 : (boxRadius κ₀ x : ℝ) ^ 3 ≤ 8 * x ^ (1 / 7 : ℝ) := by
    have h3 : (x ^ (1 / 21 : ℝ)) ^ 3 = x ^ (1 / 7 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    calc (boxRadius κ₀ x : ℝ) ^ 3 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hRle 3
      _ = 8 * x ^ (1 / 7 : ℝ) := by rw [mul_pow, h3]; norm_num
  have hδ0 : 0 ≤ boxScale x := by
    unfold boxScale
    positivity
  have hprod : x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 14 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  calc (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x ≤ 8 * x ^ (1 / 7 : ℝ) * boxScale x :=
        mul_le_mul_of_nonneg_right hR3 hδ0
    _ = 16 * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ))) * Real.log x := by
        unfold boxScale
        ring
    _ ≤ 16 * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ))) * (ε / 16 * x ^ (5 / 14 : ℝ)) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = ε * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (5 / 14 : ℝ)) := by ring
    _ = ε := by rw [hprod, mul_one]
end Line
section Main
private theorem expLineField_zero {n : ℕ} [NeZero n] {N : ℕ} (e : TorusBond n ≃ Fin N)
    (X : Fin N → imaginaryQuaternions) :
    expLineField e X 0 = trivialField n := by
  funext x i
  rw [expLineField_apply]
  simp [trivialField, expUnit_zero]
theorem chartEnergyStatement_holds (hF : cubeHessianStatement) (hB : ellipsoidBoundsStatement)
    (hA : LevelAction.ActionSmoothAlongMoves) : chartEnergyStatement := by
  intro Tb hT κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨CQ, R₀, hCQ, hF'⟩ := hF Tb hT
  obtain ⟨K₁, xs₁, hK₁, hB'⟩ := hB Tb hT κ₀ hκ1 hκ2 C₀ hC₀
  obtain ⟨CA, hCA, hA'⟩ := hA Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N
    (by linarith [hT.a_ge]) hT.L_odd hT.chain
  have hσ : 0 < Tb.σA := hT.chain.2.2.2.2.2.1
  have hδ₁ : 0 < Tb.δ₁ := hT.δ₁_pos
  have hK₁0 : 0 < K₁ := by linarith
  have hε : 0 < min 1 (Tb.σA / (16 * K₁)) := lt_min one_pos (by positivity)
  obtain ⟨xf, hxf1, hxf⟩ := eventually_boxRadius_cube_le (by linarith : 0 < κ₀) hκ2 (max 1024 R₀) hε
  refine ⟨8 * (CA * K₁ ^ 2 * bondExpMass Tb.δ₁ ^ 2 / 6 + C₀ / 2 + 64 * CQ * K₁), max xs₁ xf, ?_⟩
  intro x R k n _ o A hx hR hn hfill ζ hζ W hW
  classical
  have hxs₁ : xs₁ ≤ x := (le_max_left _ _).trans hx
  have hxfx : xf ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := hxf1.trans_le hxfx
  have hx0 : 0 < x := by linarith
  obtain ⟨hRbig, hT3⟩ := hxf x hxfx
  rw [← hR] at hRbig hT3
  have hR1024 : 1024 ≤ R := (le_max_left _ _).trans hRbig
  have hRR₀ : R₀ ≤ R := (le_max_right _ _).trans hRbig
  have hR1 : (1 : ℝ) ≤ R := by
    have : (1024 : ℝ) ≤ R := by exact_mod_cast hR1024
    linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hδ : 0 < boxScale x := by
    unfold boxScale
    have := Real.log_pos hx1
    positivity
  have hBk := hB' x R k n o A hxs₁ hR hn
  have hFk := hF' k n o R hRR₀ hn
  set δ : ℝ := boxScale x with hδdef
  have hn64 : 64 ≤ n := by omega
  have hreg := supBall_isRegularRegion o R hR1024 hn
  obtain ⟨-, hb⟩ := hBk hfill
  obtain ⟨-, -, -, hchart⟩ := hb ζ hζ
  obtain ⟨v, β, hv, hvsq, hβsq, -⟩ := hchart W hW
  obtain ⟨hflat0, -, hsym, hlin, hbd, -, -⟩ := hFk
  set S : Finset (TorusSite n) := supBall o (2 * (R : ℝ)) with hSdef
  set v' : TorusBond n → imaginaryQuaternions := fun b => if b ∈ bondsWithin S then v b else 0 with hv'
  let e : TorusBond n ≃ Fin (Fintype.card (TorusBond n)) := Fintype.equivFin (TorusBond n)
  set X : Fin (Fintype.card (TorusBond n)) → imaginaryQuaternions := fun l => v' (e.symm l) with hXdef
  set G : TorusField n → ℝ := actionAtLevel Tb.coupling Tb.side k S with hG
  set s : ℝ := K₁ * (R : ℝ) ^ 3 * δ with hs
  have hs0 : 0 ≤ s := by positivity
  have hXs : ∀ l, ‖X l‖ ≤ s := by
    intro l
    by_cases h : e.symm l ∈ bondsWithin S
    · simp only [hXdef, hv', if_pos h]
      exact (hv _ h).2.2.2
    · simp only [hXdef, hv', if_neg h, norm_zero]
      exact hs0
  have hsum : ∑ l, ‖X l‖ ^ 2 = bondNormSq S v := by
    have h1 : ∑ l, ‖X l‖ ^ 2 = ∑ b : TorusBond n, ‖v' b‖ ^ 2 :=
      e.symm.sum_comp (fun b => ‖v' b‖ ^ 2)
    have h2 : ∀ b, ‖v' b‖ ^ 2 = if b ∈ bondsWithin S then ‖v b‖ ^ 2 else 0 := by
      intro b
      by_cases h : b ∈ bondsWithin S <;> simp [hv', h]
    rw [h1]
    simp only [h2, Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  have hs8 : 8 * s < Tb.σA := by
    have h1 : (R : ℝ) ^ 3 * δ ≤ Tb.σA / (16 * K₁) := hT3.trans (min_le_right _ _)
    have h2 : s ≤ K₁ * (Tb.σA / (16 * K₁)) := by
      rw [hs, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hK₁0.le
    have h3 : K₁ * (Tb.σA / (16 * K₁)) = Tb.σA / 16 := by
      field_simp
    rw [h3] at h2
    linarith
  have hcold : ∀ τ : ℝ, -1 < τ → τ < 2 → IsColdOn Tb.σA S (expLineField e X τ) := by
    intro τ h1 h2 p _
    have hc := curvature_le_add (expLineField e X τ) (trivialField n) p.1 p.2.1 p.2.2
    have hflat : curvature (trivialField n) p.1 p.2.1 p.2.2 = 0 := by
      simp [curvature, holonomy, trivialField]
    have hbond : ∀ (y : TorusSite n) (i : Fin 4),
        ‖((expLineField e X τ y i : UnitQuaternion) : ℍ[ℝ]) - (trivialField n y i : UnitQuaternion)‖ ≤
          2 * s := by
      intro y i
      rw [expLineField_apply]
      have h3 := norm_expUnit_sub_one_le (τ • X (e (y, i)))
      have h4 : ‖((τ • X (e (y, i)) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * s := by
        show ‖τ • X (e (y, i))‖ ≤ 2 * s
        rw [norm_smul, Real.norm_eq_abs]
        have h5 : |τ| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        exact mul_le_mul h5 (hXs _) (norm_nonneg _) (by norm_num)
      simpa [trivialField] using h3.trans h4
    have b1 := hbond p.1 p.2.1
    have b2 := hbond (p.1 + TorusFields.unitStep n p.2.1) p.2.2
    have b3 := hbond (p.1 + TorusFields.unitStep n p.2.2) p.2.1
    have b4 := hbond p.1 p.2.2
    rw [hflat] at hc
    linarith
  have hfacts := fun (τ : ℝ) (h1 : -1 < τ) (h2 : τ < 2) =>
    hA' k n hn64 S (expLineField e X τ) hreg (hcold τ h1 h2)
  have hthird : ∀ τ : ℝ, 0 < τ → τ < 1 →
      |iteratedFDeriv ℝ 3 (perturbLine e G X (expLineField e X τ)) 0 (fun _ => fun _ => 1)| ≤
        CA * (s * bondExpMass Tb.δ₁ ^ 2 * (K₁ * (R : ℝ) ^ 6 * δ ^ 2)) := by
    intro τ h1 h2
    obtain ⟨hc3, hder, -⟩ := hfacts τ (by linarith) (by linarith)
    have h3 := third_deriv_bound e hc3 hCA.le hδ₁
      (fun c Xs hu => hder 3 c Xs (by norm_num) le_rfl hu) X hXs
    refine h3.trans ?_
    rw [hsum]
    have hQ0 : 0 ≤ s * bondExpMass Tb.δ₁ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvsq hQ0) hCA.le
  have htay := taylor_action_bound e X (G := G)
    (fun W' => actionAtLevel_nonneg (by linarith [hT.a_ge]) _ _ _ W')
    hflat0 (fun τ h1 h2 => (hfacts τ h1 h2).1) hthird
  have hl1 : G (expLineField e X 1) = G W := by
    refine actionAtLevel_congr _ _ _ _ fun b hb => ?_
    rw [expLineField_apply, one_smul]
    have hX : X (e (b.1, b.2)) = v b := by
      simp [hXdef, hv', hb]
    rw [hX]
    exact (hv b hb).1.symm
  have hC0 : ContDiffAt ℝ 3 (perturbLine e G (fun l => v' (e.symm l)) (trivialField n)) 0 := by
    have h1 := (hfacts 0 (by norm_num) (by norm_num)).1
    rw [expLineField_zero] at h1
    exact h1 _ _ _
  have hsec := second_deriv_eq_sum e v' hC0
  rw [hl1] at htay
  rw [show iteratedFDeriv ℝ 2 (perturbLine e G X (trivialField n)) 0 (fun _ => fun _ => 1) =
    hessianForm Tb.coupling Tb.side k S v' v' from hsec] at htay
  set u : TorusBond n → imaginaryQuaternions := A + ζ with hu
  set Dd : TorusBond n → imaginaryQuaternions := v' - u with hDd
  have hvu : u + Dd = v' := by simp [hDd]
  have hpsd : ∀ w : TorusBond n → imaginaryQuaternions, 0 ≤ hessianForm Tb.coupling Tb.side k S w w :=
    fun w => le_trans (mul_nonneg (mul_nonneg (by norm_num) hT.cK_pos.le)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (hbd w).1
  have ht : 0 < (R : ℝ) ^ 3 * δ := by positivity
  have hps := psd_quadratic_diff_le (hessianForm Tb.coupling Tb.side k S) hsym hlin hpsd u Dd ht
  rw [hvu] at hps
  have hbsq : bondNormSq S Dd = bondNormSq S β := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have h2 : Dd b = β b := by
      have h1 := (hv b hb).2.1
      simp only [hDd, hv', Pi.sub_apply, if_pos hb, hu, Pi.add_apply]
      rw [h1]
      abel
    rw [h2]
  have hCQ0 : 0 ≤ CQ := by linarith
  have hDD : hessianForm Tb.coupling Tb.side k S Dd Dd ≤ 64 * CQ * K₁ * (R : ℝ) ^ 12 * δ ^ 4 := by
    have h1 := (hbd Dd).2
    have h2 := curlNormSq_le S Dd
    rw [hbsq] at h2
    have h3 := h2.trans (mul_le_mul_of_nonneg_left hβsq (by norm_num))
    calc _ ≤ CQ * curlNormSq S Dd := h1
      _ ≤ CQ * (64 * (K₁ * (R : ℝ) ^ 12 * δ ^ 4)) := mul_le_mul_of_nonneg_left h3 hCQ0
      _ = _ := by ring
  have huu : hessianForm Tb.coupling Tb.side k S u u ≤ C₀ * (R : ℝ) ^ 4 * δ ^ 2 := hζ.2
  have hT1 : (R : ℝ) ^ 3 * δ ≤ 1 := hT3.trans (min_le_left _ _)
  set P : ℝ := (R : ℝ) ^ 9 * δ ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have e1 : (R : ℝ) ^ 3 * δ * hessianForm Tb.coupling Tb.side k S u u ≤ C₀ * P := by
    have h1 : (R : ℝ) ^ 7 ≤ (R : ℝ) ^ 9 := pow_le_pow_right₀ hR1 (by norm_num)
    calc _ ≤ (R : ℝ) ^ 3 * δ * (C₀ * (R : ℝ) ^ 4 * δ ^ 2) := mul_le_mul_of_nonneg_left huu ht.le
      _ = C₀ * δ ^ 3 * (R : ℝ) ^ 7 := by ring
      _ ≤ C₀ * δ ^ 3 * (R : ℝ) ^ 9 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [hP]; ring
  have e2 : hessianForm Tb.coupling Tb.side k S Dd Dd / ((R : ℝ) ^ 3 * δ) ≤ 64 * CQ * K₁ * P := by
    rw [div_le_iff₀ ht]
    refine hDD.trans (le_of_eq ?_)
    rw [hP]
    ring
  have e3 : hessianForm Tb.coupling Tb.side k S Dd Dd ≤ 64 * CQ * K₁ * P := by
    have h1 : 64 * CQ * K₁ * (R : ℝ) ^ 12 * δ ^ 4 = 64 * CQ * K₁ * P * ((R : ℝ) ^ 3 * δ) := by
      rw [hP]
      ring
    rw [h1] at hDD
    have h2 : 0 ≤ 64 * CQ * K₁ * P := by positivity
    nlinarith
  have e4 : CA * (s * bondExpMass Tb.δ₁ ^ 2 * (K₁ * (R : ℝ) ^ 6 * δ ^ 2)) / 6 =
      CA * K₁ ^ 2 * bondExpMass Tb.δ₁ ^ 2 / 6 * P := by
    rw [hP, hs]
    ring
  rw [e4] at htay
  have hdiff : |G W - 1 / 2 * hessianForm Tb.coupling Tb.side k S u u| ≤
      (CA * K₁ ^ 2 * bondExpMass Tb.δ₁ ^ 2 / 6 + C₀ / 2 + 64 * CQ * K₁) * P := by
    have h1 := abs_le.mp htay
    have h2 := abs_le.mp hps
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, e1, e2, e3]
  have hax : x * (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
  have hδ3 : x * δ ^ 3 = 8 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by
    rw [hδdef]
    unfold boxScale
    calc _ = 8 * (x * (x ^ (-(1 / 2 : ℝ))) ^ 2) * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by ring
      _ = _ := by rw [hax]; ring
  have hgoal : x * G W - x / 2 * hessianForm Tb.coupling Tb.side k S u u =
      x * (G W - 1 / 2 * hessianForm Tb.coupling Tb.side k S u u) := by ring
  rw [hgoal, abs_mul, abs_of_pos hx0]
  calc x * |G W - 1 / 2 * hessianForm Tb.coupling Tb.side k S u u| ≤
      x * ((CA * K₁ ^ 2 * bondExpMass Tb.δ₁ ^ 2 / 6 + C₀ / 2 + 64 * CQ * K₁) * P) :=
        mul_le_mul_of_nonneg_left hdiff hx0.le
    _ = (CA * K₁ ^ 2 * bondExpMass Tb.δ₁ ^ 2 / 6 + C₀ / 2 + 64 * CQ * K₁) * (R : ℝ) ^ 9 * (x * δ ^ 3) := by
        rw [hP]
        ring
    _ = _ := by
        rw [hδ3]
        ring
end Main
end YangMills.Construction.BoxGaussian
end
