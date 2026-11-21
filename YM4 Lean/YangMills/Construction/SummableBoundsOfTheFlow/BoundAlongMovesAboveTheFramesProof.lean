import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.SummableBoundsOfTheFlow.BoundAlongMovesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Estimates
theorem le_runningMax (e : ℕ → ℝ) {i p : ℕ} (hi : 1 ≤ i) (hp : i ≤ p) : e i ≤ runningMax e p := by
  induction p with
  | zero => omega
  | succ p ih =>
    rw [runningMax]
    rcases Nat.lt_or_ge i (p + 1) with h | h
    · exact (ih (by omega)).trans (le_max_left _ _)
    · have : i = p + 1 := by omega
      subst this
      exact le_max_right _ _
theorem runningMax_nonneg {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (p : ℕ) : 0 ≤ runningMax e p := by
  induction p with
  | zero => exact le_rfl
  | succ p ih => exact ih.trans (le_max_left _ _)
variable {F : BlockFrame}
theorem Perturbation.decayWeight_le_exp (w : Perturbation F) (r : ℝ) (x : F.Site F.depth) (i : Fin 4)
    (hz : ∀ z : F.Cell, cellSupDist z z = 0) :
    w.decayWeight r x i ≤ Real.exp (-(r * cellSupDist (enclosingCell x) w.cell)) := by
  classical
  cases w with
  | top c X => exact le_rfl
  | bulk b u =>
    simp only [Perturbation.decayWeight, Perturbation.cell]
    split_ifs with h
    · rw [h, hz]
      simp
    · exact (Real.exp_pos _).le
theorem inv_decayWeight_le_exp (L : ℕ) {δ : ℝ} (u : ℝ) :
    (torusDecayFactor L δ u)⁻¹ ≤ Real.exp (-(δ * u)) := by
  have h1 : Real.exp (δ * u) ≤ torusDecayFactor L δ u := by
    rw [torusDecayFactor]
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) h1
theorem sum_partition_slots_le {L p : ℕ} {κ r Cg : ℝ} {M : ℕ → ℝ} {e : ℕ → ℝ} {F : BlockFrame}
    (hκ : 0 < κ) (hr : 2 ^ 9 * κ ≤ r) (hL : 2 ^ 40 ≤ L) (hFL : F.blockSide = L) (hM : ∀ q, 0 ≤ M q)
    (hgeo : (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧
      (∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) ∧
      ∀ x y : F.Site F.depth,
        F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (hsite : ∀ x y : F.Site F.depth, siteSupDist x y = siteSupDist y x)
    (hsum : ∀ z : F.Cell, ∑ b ∈ fineBonds F,
      Real.exp (-(r / 2 * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (L : ℝ) ^ 4)
    {w : Fin p → Perturbation F} {y : F.Site F.depth} (c : OrderedFinpartition p) (hc6 : c.length ≤ 6)
    (he : 0 ≤ e c.length)
    {A : ∀ m : Fin c.length, F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hA : ∀ (m : Fin c.length) (x : F.Site F.depth) (i : Fin 4) (q : Fin (c.partSize m)),
      ‖A m x i‖ ≤ M (c.partSize m) * Real.exp (-(r * cellSupDist (enclosingCell x) (w (c.emb m q)).cell))) :
    ∑ b ∈ Fintype.piFinset fun _ : Fin c.length => fineBonds F,
        (e c.length / torusDecayFactor L (κ / 2 ^ 10) (bondSpan y b)) * ∏ m, ‖A m (b m).1 (b m).2‖ ≤
      e c.length * (Real.exp (κ / 2 ^ 10 * L) * (∏ m, M (c.partSize m)) * (Cg * (L : ℝ) ^ 4) ^ c.length) *
        Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))) := by
  classical
  obtain ⟨hsym, htri, hls⟩ := hgeo
  have hL1 : (2 : ℝ) ^ 40 ≤ L := by exact_mod_cast hL
  have hr2 : 2 ^ 8 * κ ≤ r / 2 := by linarith
  have hr0 : 0 ≤ r / 2 := by nlinarith
  set δ : ℝ := κ / 2 ^ 10 with hδ
  have hδ0 : 0 < δ := by positivity
  set D : ℕ := cellSetDiameter (insert (enclosingCell y) (perturbationCells w)) with hD
  let l₀ : ∀ m : Fin c.length, Fin (c.partSize m) := fun m => ⟨0, c.partSize_pos m⟩
  let g : Fin c.length → F.Site F.depth × Fin 4 → ℝ := fun m β =>
    Real.exp (-(r / 2 * cellSupDist (enclosingCell β.1) (w (c.emb m (l₀ m))).cell))
  have hg0 : ∀ m β, 0 ≤ g m β := fun m β => (Real.exp_pos _).le
  have hpt : ∀ b : Fin c.length → F.Site F.depth × Fin 4,
      (e c.length / torusDecayFactor L δ (bondSpan y b)) * ∏ m, ‖A m (b m).1 (b m).2‖ ≤
        (e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) *
          Real.exp (-(2 ^ 7 * κ * D))) * ∏ m, g m (b m) := by
    intro b
    let E : Fin c.length → ℕ := fun m => Finset.univ.sup fun q : Fin (c.partSize m) =>
      cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell
    let d : Fin c.length → ℕ := fun m => cellSupDist (enclosingCell (b m).1) (enclosingCell y)
    have hslot : ∀ m, ‖A m (b m).1 (b m).2‖ ≤
        M (c.partSize m) * Real.exp (-(2 ^ 8 * κ * E m)) * g m (b m) := by
      intro m
      have hne : (Finset.univ : Finset (Fin (c.partSize m))).Nonempty := ⟨l₀ m, Finset.mem_univ _⟩
      obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup Finset.univ hne
        (fun q : Fin (c.partSize m) => cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell)
      have hEq : (E m : ℝ) = cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell := by
        simp only [E]
        rw [hq]
      have h1 := hA m (b m).1 (b m).2 q
      refine h1.trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hM _)
      simp only [g]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [← hEq]
      have h2 : ((cellSupDist (enclosingCell (b m).1) (w (c.emb m (l₀ m))).cell : ℕ) : ℝ) ≤ E m := by
        have : cellSupDist (enclosingCell (b m).1) (w (c.emb m (l₀ m))).cell ≤ E m :=
          Finset.le_sup (f := fun q : Fin (c.partSize m) =>
            cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell) (Finset.mem_univ (l₀ m))
        exact_mod_cast this
      have hE0 : (0 : ℝ) ≤ E m := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2 hr0, mul_le_mul_of_nonneg_right hr2 hE0]
    have hdiam : ∀ u ∈ insert (enclosingCell y) (perturbationCells w),
        cellSupDist u (enclosingCell y) ≤ ∑ m, (E m + d m) := by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · have h0 : cellSupDist (enclosingCell y) (enclosingCell y) = 0 := by simp [cellSupDist]
        omega
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hu
        have hl : c.emb (c.index l) (c.invEmbedding l) = l := c.emb_invEmbedding l
        have h1 : cellSupDist (enclosingCell (b (c.index l)).1) (w l).cell ≤ E (c.index l) := by
          have := Finset.le_sup (f := fun q : Fin (c.partSize (c.index l)) =>
            cellSupDist (enclosingCell (b (c.index l)).1) (w (c.emb (c.index l) q)).cell)
            (Finset.mem_univ (c.invEmbedding l))
          simpa [hl] using this
        have h2 := htri (w l).cell (enclosingCell (b (c.index l)).1) (enclosingCell y)
        rw [hsym (w l).cell (enclosingCell (b (c.index l)).1)] at h2
        have h3 : E (c.index l) + d (c.index l) ≤ ∑ m, (E m + d m) :=
          Finset.single_le_sum (f := fun m => E m + d m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        exact h2.trans ((Nat.add_le_add_right h1 _).trans h3)
    have hDle : D ≤ 2 * ∑ m, (E m + d m) := by
      simp only [hD, cellSetDiameter]
      refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
      have h1 := htri u (enclosingCell y) v
      rw [hsym (enclosingCell y) v] at h1
      have h2 := hdiam u hu
      have h3 := hdiam v hv
      omega
    have hG : (torusDecayFactor L δ (bondSpan y b))⁻¹ ≤
        Real.exp (δ * L) * Real.exp (-(2 ^ 8 * κ * ∑ m, (d m : ℝ))) := by
      refine (inv_decayWeight_le_exp L _).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hu : ∀ m, L * d m ≤ bondSpan y b + L := by
        intro m
        have h1 := hls (b m).1 y
        rw [hFL] at h1
        have h2 : siteSupDist y (b m).1 ≤ bondSpan y b :=
          le_max_of_le_left (Finset.le_sup (f := fun l : Fin c.length => siteSupDist y (b l).1)
            (Finset.mem_univ m))
        rw [hsite] at h1
        show L * cellSupDist (enclosingCell (b m).1) (enclosingCell y) ≤ _
        omega
      have hs : (L : ℝ) * ∑ m, (d m : ℝ) ≤ 6 * ((bondSpan y b : ℝ) + L) := by
        rw [Finset.mul_sum]
        have h1 : ∑ m : Fin c.length, (L : ℝ) * (d m : ℝ) ≤
            ∑ _m : Fin c.length, ((bondSpan y b : ℝ) + L) := by
          refine Finset.sum_le_sum fun m _ => ?_
          exact_mod_cast hu m
        refine h1.trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h6 : (c.length : ℝ) ≤ 6 := by exact_mod_cast hc6
        have hn : (0 : ℝ) ≤ (bondSpan y b : ℝ) + L := by positivity
        exact mul_le_mul_of_nonneg_right h6 hn
      have hsd : (0 : ℝ) ≤ ∑ m, (d m : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hb : (2 : ℝ) ^ 18 * ∑ m, (d m : ℝ) ≤ (bondSpan y b : ℝ) + L := by
        have : (6 * 2 ^ 18 : ℝ) ≤ L := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this hsd]
      have hfin : 2 ^ 8 * κ * ∑ m, (d m : ℝ) ≤ δ * ((bondSpan y b : ℝ) + L) := by
        have h2 := mul_le_mul_of_nonneg_left hb hδ0.le
        calc 2 ^ 8 * κ * ∑ m, (d m : ℝ) = δ * (2 ^ 18 * ∑ m, (d m : ℝ)) := by
              rw [hδ]; ring
          _ ≤ _ := h2
      nlinarith
    have hW0 : 0 < torusDecayFactor L δ (bondSpan y b) := by
      rw [torusDecayFactor]
      exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
    have hprod : ∏ m, ‖A m (b m).1 (b m).2‖ ≤
        (∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 8 * κ * ∑ m, (E m : ℝ))) * ∏ m, g m (b m) := by
      calc ∏ m, ‖A m (b m).1 (b m).2‖ ≤
            ∏ m, (M (c.partSize m) * Real.exp (-(2 ^ 8 * κ * E m)) * g m (b m)) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ => hslot m
        _ = _ := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            congr 2
            rw [← Real.exp_sum]
            congr 1
            rw [Finset.mul_sum, Finset.sum_neg_distrib]
    have hgprod : 0 ≤ ∏ m, g m (b m) := Finset.prod_nonneg fun m _ => hg0 m _
    have hMprod : 0 ≤ ∏ m, M (c.partSize m) := Finset.prod_nonneg fun m _ => hM _
    have hexp : Real.exp (-(2 ^ 8 * κ * ∑ m, (d m : ℝ))) * Real.exp (-(2 ^ 8 * κ * ∑ m, (E m : ℝ))) ≤
        Real.exp (-(2 ^ 7 * κ * D)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (D : ℝ) ≤ 2 * ∑ m, ((E m : ℝ) + d m) := by
        have := hDle
        have h2 : ((∑ m, (E m + d m) : ℕ) : ℝ) = ∑ m, ((E m : ℝ) + d m) := by push_cast; rfl
        rw [← h2]
        exact_mod_cast this
      rw [Finset.sum_add_distrib] at h1
      nlinarith [mul_le_mul_of_nonneg_left h1 hκ.le]
    calc (e c.length / torusDecayFactor L δ (bondSpan y b)) * ∏ m, ‖A m (b m).1 (b m).2‖
        = e c.length * (torusDecayFactor L δ (bondSpan y b))⁻¹ * ∏ m, ‖A m (b m).1 (b m).2‖ := by
          rw [div_eq_mul_inv]
      _ ≤ e c.length * (Real.exp (δ * L) * Real.exp (-(2 ^ 8 * κ * ∑ m, (d m : ℝ)))) *
            ((∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 8 * κ * ∑ m, (E m : ℝ))) * ∏ m, g m (b m)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hG he) hprod
            (Finset.prod_nonneg fun _ _ => norm_nonneg _) (mul_nonneg he (by positivity))
      _ = e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) *
            (Real.exp (-(2 ^ 8 * κ * ∑ m, (d m : ℝ))) * Real.exp (-(2 ^ 8 * κ * ∑ m, (E m : ℝ)))) *
            ∏ m, g m (b m) := by ring
      _ ≤ e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 7 * κ * D)) *
            ∏ m, g m (b m) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp ?_) hgprod
          exact mul_nonneg (mul_nonneg he (Real.exp_pos _).le) hMprod
  have hsumg : ∑ b ∈ Fintype.piFinset (fun _ : Fin c.length => fineBonds F), ∏ m, g m (b m) ≤
      (Cg * (L : ℝ) ^ 4) ^ c.length := by
    rw [← Finset.prod_univ_sum]
    calc ∏ m, ∑ β ∈ fineBonds F, g m β ≤ ∏ _m : Fin c.length, (Cg * (L : ℝ) ^ 4) :=
          Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun β _ => hg0 m β) fun m _ => hsum _
      _ = _ := by simp
  have hpre : 0 ≤ e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) *
      Real.exp (-(2 ^ 7 * κ * D)) :=
    mul_nonneg (mul_nonneg (mul_nonneg he (Real.exp_pos _).le)
      (Finset.prod_nonneg fun m _ => hM _)) (Real.exp_pos _).le
  calc _ ≤ ∑ b ∈ Fintype.piFinset (fun _ : Fin c.length => fineBonds F),
        (e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 7 * κ * D))) *
          ∏ m, g m (b m) := Finset.sum_le_sum fun b _ => hpt b
    _ = (e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 7 * κ * D))) *
          ∑ b ∈ Fintype.piFinset (fun _ : Fin c.length => fineBonds F), ∏ m, g m (b m) := by
        rw [Finset.mul_sum]
    _ ≤ (e c.length * Real.exp (δ * L) * (∏ m, M (c.partSize m)) * Real.exp (-(2 ^ 7 * κ * D))) *
          (Cg * (L : ℝ) ^ 4) ^ c.length := mul_le_mul_of_nonneg_left hsumg hpre
    _ = _ := by ring
theorem bondDeriv_subtractTrivial {F : BlockFrame} {N i : ℕ} {f : LocalFamily} {y : F.Site F.depth}
    {W : F.GaugeField F.depth} {c : Fin i → F.Site F.depth × Fin 4} {X : Fin i → imaginaryQuaternions}
    (hi : i ≠ 0) (hN : i ≤ N)
    (h : ContDiffAt ℝ N (fun τ : Fin i → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by
  simp only [bondDeriv, subtractTrivial]
  have h1 : (fun τ : Fin i → ℝ =>
        f F y (leftTranslate (bondSpread c X τ) W) - f F y (uniformField F F.depth)) =
      (fun τ => f F y (leftTranslate (bondSpread c X τ) W)) + fun _ => -f F y (uniformField F F.depth) := by
    funext τ
    simp [sub_eq_add_neg]
  have hN' : ((i : ℕ) : WithTop ℕ∞) ≤ N := by exact_mod_cast hN
  rw [h1, iteratedFDeriv_add_apply (h.of_le hN') contDiffAt_const, iteratedFDeriv_const_of_ne hi]
  simp
theorem boundAlongPerturbations_holds (hmot : motionAboveFrameStatement)
    (hexp : expansionAlongMotionStatement) (hsm : SmoothAlongMotion)
    (hcov : BlocksCoverLowerLevel) (hgeo : CubicTorusCellGeometry) :
    boundAlongPerturbationsStatement := by
  intro K r κ L hK hκ hr hLodd hL
  obtain ⟨M, hM, hmo⟩ := hmot 6 K hK
  have hr0 : 0 < r := by nlinarith
  obtain ⟨Cg, hCg, hsum⟩ := hgeo.2 (r / 2) (by linarith)
  have hL0 : 0 < L := by omega
  let Cp : ℕ → ℝ := fun p => ∑ c : OrderedFinpartition p,
    Real.exp (κ / 2 ^ 10 * L) * (∏ m, M (c.partSize m)) * (Cg * (L : ℝ) ^ 4) ^ c.length
  have hCp : ∀ p, 0 ≤ Cp p := fun p => Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => hM _))
      (pow_nonneg (by positivity) _)
  let C : ℝ := ∑ p ∈ Finset.range 7, Cp p + 1
  have hC : 0 < C := by
    have : 0 ≤ ∑ p ∈ Finset.range 7, Cp p := Finset.sum_nonneg fun p _ => hCp p
    linarith
  refine ⟨C, hC, ?_⟩
  intro F n₀ k p m σ s a ρA e f V η w y hFL hcub hlow hk6 he hf hcold hsmall hana hdec hunit
  have hodd : Odd F.blockSide := hFL ▸ hLodd
  obtain ⟨n, hn64, hside⟩ := hcub
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hper : ∀ i, F.period F.depth i ≠ 0 := fun i => by
    have : 0 < F.blockSide := by rw [hFL]; exact hL0
    simp only [BlockFrame.period]
    exact mul_ne_zero (hpos i).ne' (pow_ne_zero _ this.ne')
  have hall := hcov F hodd hpos
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b => by
    simp [fineBonds, hall]
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    simp [chordBonds, innerBonds, hall, hd]
  obtain ⟨α, hα0, hαs, -, hαe, hαp, -⟩ :=
    hmo F s a ρA r m p V η w hper hr0.le hchart hsmall hana hdec hunit
  set W₀ := interpolatedField s a ρA m V η with hW₀
  set G : F.GaugeField F.depth → ℝ := subtractTrivial f F y with hGdef
  have hGf : ∀ (q : ℕ) (c : Fin q → F.Site F.depth × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => f F y (leftTranslate (bondSpread c X τ) W₀)) 0 :=
    hf.smooth F hlow y W₀ hcold
  have hG : ∀ (q : ℕ) (c : Fin q → F.Site F.depth × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W₀)) 0 := fun q c X =>
    (hGf q c X).sub contDiffAt_const
  have hev : (fun τ => G (perturbedField s a ρA m V η w τ)) =ᶠ[𝓝 0]
      fun τ => G (leftTranslate (α τ) W₀) :=
    hαe.mono fun τ h => by
      simp only [perturbedField]
      rw [h]
  have hk6' : ((k : ℕ) : WithTop ℕ∞) ≤ (6 : ℕ) := by exact_mod_cast hk6
  refine ⟨?_, ?_⟩
  · have h1 := hsm F F.depth k p G W₀ α hper hG (fun x b => (hαs x b).of_le hk6') hα0
    exact h1.congr_of_eventuallyEq hev
  · intro hp1 hpk
    have hp6 : p ≤ 6 := hpk.trans hk6
    have hpk' : ((p : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast hpk
    have hp6' : ((p : ℕ) : WithTop ℕ∞) ≤ (6 : ℕ) := by exact_mod_cast hp6
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev p).eq_of_nhds]
    obtain ⟨-, hex⟩ := hexp.1 F F.depth p G W₀ α hper (fun q c X => (hG q c X).of_le hpk')
      (fun x b => (hαs x b).of_le hp6') hα0
    rw [hex]
    set D := cellSetDiameter (insert (enclosingCell y) (perturbationCells w)) with hD
    have hterm : ∀ c : OrderedFinpartition p,
        |mixedDerivAlong G W₀ fun m => motionComponent α (c.emb m)| ≤
          runningMax e p * (Real.exp (κ / 2 ^ 10 * L) * (∏ m, M (c.partSize m)) *
            (Cg * (L : ℝ) ^ 4) ^ c.length) * Real.exp (-(2 ^ 7 * κ * D)) := by
      intro c
      have hlen : c.length ≤ p := c.length_le
      have hlen0 : c.length ≠ 0 := fun h => by
        have := c.length_pos hp1
        omega
      have hlenk : ((c.length : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast hlen.trans hpk
      have h1 := hexp.2 F F.depth c.length G W₀ (fun m => motionComponent α (c.emb m)) (fineBonds F)
        (fun b => e c.length / torusDecayFactor L (κ / 2 ^ 10) (bondSpan y b)) hper hbond
        (fun q c' X => (hG q c' X).of_le hlenk) (fun b X hX => by
          rw [hGdef, bondDeriv_subtractTrivial hlen0 (hlen.trans hpk) (hGf _ b X)]
          exact hf.decay F hlow y W₀ c.length b X hcold (Nat.one_le_iff_ne_zero.2 hlen0)
            (hlen.trans hpk) hX)
      refine h1.trans ?_
      have hgeo1 := hgeo.1 F hodd ⟨n, hn64, hside⟩
      have h2 := sum_partition_slots_le (L := L) (κ := κ) (r := r) (Cg := Cg) (M := M) (e := e) (F := F)
        (w := w) (y := y) hκ hr hL hFL hM ⟨hgeo1.2.2.1, hgeo1.2.2.2.1, hgeo1.2.2.2.2⟩
        (hgeo1.1 F.depth) (fun z => by
          have := hsum F hodd ⟨n, hn64, hside⟩ z
          rwa [hFL] at this) c ((hlen.trans hpk).trans hk6) (he _)
        (A := fun m => motionComponent α (c.emb m)) (fun m x i q => by
          refine (hαp _ (c.emb m) x i q ((c.partSize_le m).trans hp6)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (hM _)
          exact Perturbation.decayWeight_le_exp _ r x i (fun z => by simp [cellSupDist]))
      refine h2.trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (Real.exp_pos _).le
      · exact le_runningMax e (Nat.one_le_iff_ne_zero.2 hlen0) hlen
      · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => hM _))
          (pow_nonneg (by positivity) _)
    have hlE := runningMax_nonneg he p
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hterm c).trans ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hlE
    have h3 : Cp p ≤ ∑ q ∈ Finset.range 7, Cp q :=
      Finset.single_le_sum (f := Cp) (fun q _ => hCp q) (Finset.mem_range.2 (by omega))
    show Cp p ≤ _
    simp only [C]
    linarith
end Estimates
end YangMills.Construction
end
