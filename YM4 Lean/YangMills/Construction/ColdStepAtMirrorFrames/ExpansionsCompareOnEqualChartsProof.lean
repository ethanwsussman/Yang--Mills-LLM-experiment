import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsCompareOnEqualCharts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeThroughTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.FamilyNorms
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChartComparison
variable {F : BlockFrame}
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem period_depth (F : BlockFrame) (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem siteOfCoords_add {j : ℕ} (u v : Fin 4 → ℤ) :
    _root_.YangMills.Construction.BlockAverages.siteOfCoords (F := F) j (u + v) = _root_.YangMills.Construction.BlockAverages.siteOfCoords j u + _root_.YangMills.Construction.BlockAverages.siteOfCoords j v := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem cellCentre_add_siteOfCoords (hs : ∀ i, 0 < F.extent i) (z : F.Cell) (g : Fin 4 → ℤ) :
    cellCentre F.depth (z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) =
      cellCentre F.depth z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * g i) := by
  funext i
  have e1 : F.top - F.depth = 1 := by simp [BlockFrame.top]
  have hpn := period_top F i
  have : NeZero (F.period F.top i) := ⟨by rw [hpn]; exact (hs i).ne'⟩
  have c1 : ∀ z' : F.Cell, cellCentre F.depth z' i =
      (((F.blockSide : ℤ) * siteCoords z' i : ℤ) : ZMod (F.period F.depth i)) := fun z' => by
    simp [cellCentre, _root_.YangMills.Construction.BlockAverages.siteOfCoords, e1]
  have h1 : ((siteCoords (z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) i - (siteCoords z i + g i) : ℤ) :
      ZMod (F.period F.top i)) = 0 := by
    have a1 : ((siteCoords (z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) i : ℤ) : ZMod (F.period F.top i)) =
        z i + (g i : ZMod (F.period F.top i)) := by
      simp [siteCoords, _root_.YangMills.Construction.BlockAverages.siteOfCoords]
    have a2 : ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := by
      simp [siteCoords]
    rw [Int.cast_sub, Int.cast_add, a1, a2]
    ring
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [hpn] at hm
  have h2 : (((F.blockSide : ℤ) * siteCoords (z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) i -
      ((F.blockSide : ℤ) * siteCoords z i + (F.blockSide : ℤ) * g i) : ℤ) :
      ZMod (F.period F.depth i)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, period_depth]
    refine ⟨m, ?_⟩
    push_cast
    linear_combination (F.blockSide : ℤ) * hm
  rw [Pi.add_apply, c1, c1]
  show _ = _ + (((F.blockSide : ℤ) * g i : ℤ) : ZMod (F.period F.depth i))
  rw [← Int.cast_add]
  rw [Int.cast_sub, sub_eq_zero] at h2
  exact h2
theorem fineBondAt_fst (hs : ∀ i, 0 < F.extent i) (Y : F.Cell) (h o : Fin 4 → ℤ) (i : Fin 4) :
    (fineBondAt Y h o i).1 =
      cellCentre F.depth Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth (fun l => (F.blockSide : ℤ) * h l + o l) := by
  unfold fineBondAt
  simp only
  rw [cellCentre_add_siteOfCoords hs, add_assoc, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartComparison.siteOfCoords_add]
  rfl
theorem exists_blockDecomposition (hodd : Odd F.blockSide) (p : Fin 4 → ℤ) :
    ∃ q o₂ : Fin 4 → ℤ, o₂ ∈ centredCube F.blockSide ∧ ∀ l, p l = (F.blockSide : ℤ) * q l + o₂ l := by
  obtain ⟨k, hk⟩ := hodd
  have hLk : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hpos : (0 : ℤ) < F.blockSide := by rw [hLk]; positivity
  refine ⟨fun l => (p l + k) / (F.blockSide : ℤ),
    fun l => p l - (F.blockSide : ℤ) * ((p l + k) / (F.blockSide : ℤ)), ?_, fun l => by ring⟩
  unfold centredCube
  rw [Fintype.mem_piFinset]
  intro l
  rw [Finset.mem_Icc]
  have e1 := Int.emod_add_mul_ediv (p l + k) (F.blockSide : ℤ)
  have e2 := Int.emod_nonneg (p l + k) hpos.ne'
  have e3 := Int.emod_lt_of_pos (p l + k) hpos
  have e4 : ((F.blockSide : ℤ) - 1) / 2 = k := by rw [hLk]; omega
  rw [e4]
  constructor <;> nlinarith
theorem isCrossingBond_iff_of_cellOffset_eq {F F' : BlockFrame} (hS : SiteDecomposition)
    (hL : F.blockSide = F'.blockSide) (hodd : Odd F.blockSide)
    (h2 : ∀ i, 2 ≤ F.extent i) (h2' : ∀ i, 2 ≤ F'.extent i) {x : F.Site F.depth} {x' : F'.Site F'.depth}
    (ho : cellOffset x = cellOffset x') (i : Fin 4) : IsCrossingBond (x, i) ↔ IsCrossingBond (x', i) := by
  have a := (hS F hodd h2).2.2.1 x i
  have a' := (hS F' (hL ▸ hodd) h2').2.2.1 x' i
  rw [a, a', ho, hL]
theorem isAxialTreeBond_iff_of_cellOffset_eq {F F' : BlockFrame} (hS : SiteDecomposition)
    (hL : F.blockSide = F'.blockSide) (hodd : Odd F.blockSide)
    (h2 : ∀ i, 2 ≤ F.extent i) (h2' : ∀ i, 2 ≤ F'.extent i) {x : F.Site F.depth} {x' : F'.Site F'.depth}
    (ho : cellOffset x = cellOffset x') (i : Fin 4) : IsAxialTreeBond (x, i) ↔ IsAxialTreeBond (x', i) := by
  unfold IsAxialTreeBond
  simp only
  rw [isCrossingBond_iff_of_cellOffset_eq hS hL hodd h2 h2' ho i, ho]
theorem chartedField_eq_of_agreeOnBall {F F' : BlockFrame} (hS : SiteDecomposition) (hO : TorusOffsetsAboutCell)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hL : F.blockSide = F'.blockSide) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 * r + 2 < F.extent i) (hs' : ∀ i, 2 * r + 2 < F'.extent i)
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r)
    (heq : ∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h₁ → o₁ ∈ centredCube F.blockSide →
      fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y h₁ o₁ i).1 i = w' (fineBondAt Y' h₁ o₁ i).1 i)
    {g o₂ : Fin 4 → ℤ} (i : Fin 4) (hg : ∀ l, |g l| + 1 ≤ (r : ℤ)) (ho : o₂ ∈ centredCube F.blockSide) :
    chartedField w V (fineBondAt Y g o₂ i).1 i = chartedField w' V' (fineBondAt Y' g o₂ i).1 i := by
  have hodd' : Odd F'.blockSide := hL ▸ hodd
  have ho' : o₂ ∈ centredCube F'.blockSide := hL ▸ ho
  obtain ⟨c1, _, _, k1, _⟩ := hO F r Y hodd hs
  obtain ⟨c2, _, _, _⟩ := hO F' r Y' hodd' hs'
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have h2' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hs' i; omega
  obtain ⟨d1, e1⟩ := c1 g o₂ i ho
  obtain ⟨d2, e2⟩ := c2 g o₂ i ho'
  have eo : cellOffset (fineBondAt Y g o₂ i).1 = cellOffset (fineBondAt Y' g o₂ i).1 := e1.trans e2.symm
  have hcr := isCrossingBond_iff_of_cellOffset_eq hS hL hodd h2 h2' eo i
  have htr := isAxialTreeBond_iff_of_cellOffset_eq hS hL hodd h2 h2' eo i
  have hgr : WithinRadius r g := fun l => by have := hg l; linarith
  have hch : ¬ IsAxialTreeBond ((fineBondAt Y g o₂ i).1, i) →
      fineBondAt Y g o₂ i ∈ chordBonds (finiteCells F) := fun ht => by
    have hk := (k1 (fineBondAt Y g o₂ i).1 i).2
    refine hk fun htc => ht ?_
    have a := (hS F hodd h2).2.2.1 (fineBondAt Y g o₂ i).1 i
    refine ⟨fun hc => htc.1 (a.1 hc), htc.2⟩
  unfold chartedField
  by_cases hc : IsCrossingBond ((fineBondAt Y g o₂ i).1, i)
  · have hnt : ¬ IsAxialTreeBond ((fineBondAt Y g o₂ i).1, i) := fun ht => ht.1 hc
    rw [if_pos hc, if_pos (hcr.1 hc), heq g o₂ i hgr ho (hch hnt), d1, d2]
    congr 1
    have := hag.2.2.2 (g, i) ⟨hgr, fun l => by
      have h3 := hg l
      have h4 : |(g + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |g l| + 1 := by
        refine (abs_add_le _ _).trans ?_
        have : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
          by_cases hl : l = i
          · subst hl
            simp
          · simp [Pi.single_apply, hl]
        linarith
      show |(g + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ (r : ℤ)
      linarith⟩
    exact this
  · have hc' : ¬ IsCrossingBond ((fineBondAt Y' g o₂ i).1, i) := fun h => hc (hcr.2 h)
    by_cases ht : IsAxialTreeBond ((fineBondAt Y g o₂ i).1, i)
    · rw [if_neg hc, if_neg hc', if_pos ht, if_pos (htr.1 ht)]
    · have ht' : ¬ IsAxialTreeBond ((fineBondAt Y' g o₂ i).1, i) := fun h => ht (htr.2 h)
      rw [if_neg hc, if_neg hc', if_neg ht, if_neg ht', heq g o₂ i hgr ho (hch ht)]
theorem agreeOnBox_chartedField {F F' : BlockFrame} (hS : SiteDecomposition) (hO : TorusOffsetsAboutCell)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r s : ℕ} {h o : Fin 4 → ℤ} (hL : F.blockSide = F'.blockSide)
    (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 * r + 2 < F.extent i) (hs' : ∀ i, 2 * r + 2 < F'.extent i)
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r)
    (heq : ∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h₁ → o₁ ∈ centredCube F.blockSide →
      fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y h₁ o₁ i).1 i = w' (fineBondAt Y' h₁ o₁ i).1 i)
    (hh : WithinRadius s h) (hsr : s + 2 ≤ r) (ho : o ∈ centredCube F.blockSide) :
    AgreeOnBox (chartedField w V) (chartedField w' V') (fineBondAt Y h o 0).1 (fineBondAt Y' h o 0).1
      (F.blockSide * (r - s - 2)) := by
  have hp : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hp' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
  have hLpos : 0 < F.blockSide := hodd.pos
  obtain ⟨d, hd⟩ : ∃ d, r = d + s + 2 := ⟨r - s - 2, by omega⟩
  have hrd : r - s - 2 = d := by omega
  rw [hrd]
  have hper : ∀ (G : BlockFrame), G.blockSide = F.blockSide → (∀ i, 2 * r + 2 < G.extent i) →
      ∀ i, 2 * (F.blockSide * d) + 2 < G.period G.depth i := by
    intro G hG hsG i
    rw [period_depth, hG]
    have h1 := hsG i
    have h2 : (2 * r + 3) * F.blockSide ≤ G.extent i * F.blockSide := Nat.mul_le_mul_right _ (by omega)
    subst hd
    nlinarith
  refine ⟨hper F rfl hs, hper F' hL.symm hs', fun b hb => ?_⟩
  obtain ⟨v, i⟩ := b
  obtain ⟨hb1, _⟩ := hb
  obtain ⟨q, o₂, ho₂, hq⟩ := exists_blockDecomposition (F := F) hodd (fun l => o l + v l)
  obtain ⟨k, hk⟩ := id hodd
  have hLk : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hLpos
  have hko : ∀ {u : Fin 4 → ℤ}, u ∈ centredCube F.blockSide → ∀ l, |u l| ≤ k := fun {u} hu l => by
    have h1 := (Fintype.mem_piFinset.1 hu) l
    have e4 : ((F.blockSide : ℤ) - 1) / 2 = k := by rw [hLk]; omega
    rw [Finset.mem_Icc, e4] at h1
    exact abs_le.2 ⟨h1.1, h1.2⟩
  have hqb : ∀ l, |q l| ≤ (d : ℤ) := fun l => by
    have h1 : (F.blockSide : ℤ) * |q l| ≤ |o l| + |v l| + |o₂ l| := by
      have e1 : |(F.blockSide : ℤ) * q l| = (F.blockSide : ℤ) * |q l| := by rw [abs_mul, Nat.abs_cast]
      rw [← e1]
      have e2 : (F.blockSide : ℤ) * q l = o l + v l - o₂ l := by linarith [hq l]
      rw [e2]
      refine (abs_sub _ _).trans ?_
      have := abs_add_le (o l) (v l)
      linarith
    have h2 := hko ho l
    have h3 := hko ho₂ l
    have h4 : |v l| ≤ ((F.blockSide * d : ℕ) : ℤ) := hb1 l
    push_cast at h4
    by_contra hcon
    rw [not_le] at hcon
    have h5 : (F.blockSide : ℤ) * (d + 1) ≤ (F.blockSide : ℤ) * |q l| := by
      apply mul_le_mul_of_nonneg_left _ hLz.le
      linarith
    nlinarith
  have hg : ∀ l, |(h + q) l| + 1 ≤ (r : ℤ) := fun l => by
    have h1 : |(h + q) l| ≤ |h l| + |q l| := abs_add_le _ _
    have h2 := hh l
    have h3 := hqb l
    subst hd
    push_cast
    linarith
  have hsite : ∀ (G : BlockFrame) (Z : G.Cell), G.blockSide = F.blockSide → (∀ i, 0 < G.extent i) →
      (fineBondAt Z h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords G.depth v = (fineBondAt Z (h + q) o₂ i).1 := by
    intro G Z hG hpG
    rw [fineBondAt_fst hpG, fineBondAt_fst hpG, add_assoc, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartComparison.siteOfCoords_add]
    congr 2
    funext l
    have := hq l
    simp only [Pi.add_apply, hG]
    linarith
  show chartedField w V ((fineBondAt Y h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth v) i =
    chartedField w' V' ((fineBondAt Y' h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.depth v) i
  rw [hsite F Y rfl hp, hsite F' Y' hL.symm hp']
  exact chartedField_eq_of_agreeOnBall hS hO hL hodd hs hs' hag heq i hg ho₂
theorem bondDeriv_zero {F : BlockFrame} (G : F.GaugeField F.depth → ℝ) (W : F.GaugeField F.depth)
    (c : Fin 0 → F.Site F.depth × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.bondDeriv_zero_order <;> assumption
theorem bondDeriv_smul {F : BlockFrame} {G : F.GaugeField F.depth → ℝ} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W)
    (b : F.Site F.depth × Fin 4) (c : ℝ) (X : imaginaryQuaternions) :
    bondDeriv G W ![b] ![c • X] = c * bondDeriv G W ![b] ![X] := by
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
  have hd : DifferentiableAt ℝ (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![X] τ) W)) 0 :=
    (hG 1 ![b] ![X]).differentiableAt (by norm_num)
  have e : (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![c • X] τ) W)) =
      (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![X] τ) W)) ∘
        (c • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) := by
    funext τ
    simp only [Function.comp]
    congr 2
    funext y i
    simp [bondSpread, smul_smul, mul_comm]
  have h0 : (c • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0 = 0 := by simp
  have h1 : HasFDerivAt (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![X] τ) W))
      (fderiv ℝ (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b] ![X] τ) W)) 0)
      ((c • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have h2 := (h1.comp 0 (c • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).hasFDerivAt).fderiv
  rw [e, h2]
  simp
end ChartComparison
open ChartComparison in
theorem expansionDifferenceBoundOnAgreeingCharts_holds (hS : SiteDecomposition) (hO : TorusOffsetsAboutCell)
    (hSl : DerivThroughChart) (hLC : ImaginaryCoordinatesIsometric) :
    ExpansionDifferenceBoundOnAgreeingCharts := by
  obtain ⟨C₀, T, hC₀, hT⟩ := hSl
  refine ⟨C₀, hC₀, ?_⟩
  intro L t n₀ σ δ E E₃ f hodd hE hfam F F' w w' V V' Y Y' r s s₂ h o hTF hTF' hs hs' hc hc' hw1 hw1' hag heq hh hsr ho
  have hLT := hTF
  have hLT' := hTF'
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hTF
  obtain ⟨hFL', hFt', n', hside', hn'⟩ := hTF'
  have hLpos : 0 < L := hodd.pos
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have heq' : ∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h₁ → o₁ ∈ centredCube F.blockSide →
      fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y h₁ o₁ i).1 i = w' (fineBondAt Y' h₁ o₁ i).1 i :=
    fun h₁ o₁ i a b c => heq h₁ o₁ i a (by rw [← hFL]; exact b) c
  have hoF : o ∈ centredCube F.blockSide := by rw [hFL]; exact ho
  have hAB := agreeOnBox_chartedField hS hO hLL hoddF hs hs' hag heq' hh hsr hoF
  rw [hFL] at hAB
  have hcast : (((L * (r - s - 2) : ℕ)) : ℝ) = (L : ℝ) * ((r : ℝ) - s - 2) := by
    have : ((r - s - 2 : ℕ) : ℝ) = (r : ℝ) - s - 2 := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    push_cast
    rw [this]
  refine ⟨?_, ?_⟩
  · have hv := hfam.locality F F' hLT hLT' _ _ _ _ (L * (r - s - 2)) 0 Fin.elim0 Fin.elim0 hc hc' hAB (by norm_num)
      (fun l => l.elim0) (fun l => l.elim0)
    rw [bondDeriv_zero, bondDeriv_zero, hcast, abs_sub_comm] at hv
    exact hv
  · intro h₂ o₂ i k k' e hh₂ ho₂ hs₂ hk hk'
    have hp : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
    have hp' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
    have hsm := fun (y : F.Site F.depth) => hfam.smooth F hLT y _ hc
    have hsm' := fun (y : F'.Site F'.depth) => hfam.smooth F' hLT' y _ hc'
    have hG : ContDiffThreeAlongBonds (subtractTrivial f F (fineBondAt Y h o 0).1) (chartedField w V) :=
      fun m c X => (hsm _ m c X).sub contDiffAt_const
    have hG' : ContDiffThreeAlongBonds (subtractTrivial f F' (fineBondAt Y' h o 0).1) (chartedField w' V') :=
      fun m c X => (hsm' _ m c X).sub contDiffAt_const
    obtain ⟨a1, a2⟩ := hT F V w _ hw1 hG k e
    obtain ⟨b1, b2⟩ := hT F' V' w' _ hw1' hG' k' e
    have hkc : fineBondAt Y h₂ o₂ i ∈ chordBonds (finiteCells F) := hk ▸ k.2
    have hh₂r : WithinRadius r h₂ := fun l => (hh₂ l).trans (by
      have : (s₂ : ℤ) ≤ r := by exact_mod_cast (by omega : s₂ ≤ r)
      exact this)
    have hcoord : w k.1.1 k.1.2 = w' k'.1.1 k'.1.2 := by
      have := heq h₂ o₂ i hh₂r ho₂ hkc
      rw [hk, hk']
      exact this
    rw [← hcoord] at b1 b2
    rw [a2, b2]
    set X := T (w k.1.1 k.1.2) e with hX
    obtain ⟨Xh, hXh, hXs⟩ : ∃ Z : imaginaryQuaternions, ‖Z‖ = 1 ∧ X = ‖X‖ • Z := by
      by_cases h0 : X = 0
      · refine ⟨toImaginary (EuclideanSpace.single 0 1), ?_, ?_⟩
        · rw [hLC.2.2.1]
          simp
        · simp [h0]
      · have hn0 : ‖X‖ ≠ 0 := norm_ne_zero_iff.2 h0
        refine ⟨‖X‖⁻¹ • X, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm]
          field_simp
        · rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]
    have sc := bondDeriv_smul hG k.1 ‖X‖ Xh
    have sc' := bondDeriv_smul hG' k'.1 ‖X‖ Xh
    rw [← hXs] at sc sc'
    rw [sc, sc', ← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg X)]
    obtain ⟨d, hd⟩ : ∃ d, r = d + s + 2 := ⟨r - s - 2, by omega⟩
    have hrd : r - s - 2 = d := by omega
    obtain ⟨m, hm⟩ := id hodd
    have hLm : (L : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    have hLz : (0 : ℤ) < L := by exact_mod_cast hLpos
    have hkm : ∀ {u : Fin 4 → ℤ}, u ∈ centredCube L → ∀ l, |u l| ≤ m := fun {u} hu l => by
      have h1 := (Fintype.mem_piFinset.1 hu) l
      have e4 : ((L : ℤ) - 1) / 2 = m := by rw [hLm]; omega
      rw [Finset.mem_Icc, e4] at h1
      exact abs_le.2 ⟨h1.1, h1.2⟩
    set v : Fin 4 → ℤ := fun l => (L : ℤ) * (h₂ l - h l) + (o₂ l - o l) with hv
    have hvb : ∀ l, |v l| + 1 ≤ ((L * d : ℕ) : ℤ) := fun l => by
      have h1 : |v l| ≤ (L : ℤ) * (|h₂ l| + |h l|) + (|o₂ l| + |o l|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sub _ _))
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) hLz.le
      have h2 := hh₂ l
      have h3 := hh l
      have h4 := hkm ho₂ l
      have h5 := hkm ho l
      have h6 : (s₂ : ℤ) + s + 2 ≤ d := by
        have : s₂ + s + 2 ≤ d := by omega
        exact_mod_cast this
      have h7 : (L : ℤ) * (|h₂ l| + |h l|) ≤ (L : ℤ) * (s₂ + s) :=
        mul_le_mul_of_nonneg_left (by linarith) hLz.le
      have h8 : (L : ℤ) * (s₂ + s + 2) ≤ (L : ℤ) * d := mul_le_mul_of_nonneg_left h6 hLz.le
      push_cast
      nlinarith
    have hbox : YangMills.Construction.BlockAverages.BondWithinRadius (L * d) (v, i) := by
      refine ⟨fun l => by have := hvb l; linarith, fun l => ?_⟩
      have h4 : |(v + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |v l| + 1 := by
        refine (abs_add_le _ _).trans ?_
        have : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
          by_cases hl : l = i
          · subst hl
            simp
          · simp [Pi.single_apply, hl]
        linarith
      have := hvb l
      show |(v + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ ((L * d : ℕ) : ℤ)
      linarith
    have hsite : ∀ (G : BlockFrame) (Z : G.Cell), G.blockSide = L → (∀ i, 0 < G.extent i) →
        (fineBondAt Z h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords G.depth v = (fineBondAt Z h₂ o₂ i).1 := by
      intro G Z hG hpG
      rw [fineBondAt_fst hpG, fineBondAt_fst hpG, add_assoc, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartComparison.siteOfCoords_add]
      congr 2
      funext l
      simp only [Pi.add_apply, hG, hv]
      ring
    have hb1 : bondsAt (fineBondAt Y h o 0).1 ![(v, i)] = ![k.1] := by
      funext l
      fin_cases l
      show ((fineBondAt Y h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth v, i) = k.1
      rw [hsite F Y hFL hp, hk]
      rfl
    have hb2 : bondsAt (fineBondAt Y' h o 0).1 ![(v, i)] = ![k'.1] := by
      funext l
      fin_cases l
      show ((fineBondAt Y' h o 0).1 + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.depth v, i) = k'.1
      rw [hsite F' Y' hFL' hp', hk']
      rfl
    rw [hrd] at hAB hcast
    have hl := hfam.locality F F' hLT hLT' _ _ _ _ (L * d) 1 ![(v, i)] ![Xh] hc hc' hAB (by norm_num)
      (fun l => by
        fin_cases l
        exact hbox)
      (fun l => by
        fin_cases l
        exact hXh)
    rw [hb1, hb2, abs_sub_comm] at hl
    have hq0 : 0 ≤ E / torusDecayFactor L δ ((L * d : ℕ) : ℝ) := (abs_nonneg _).trans hl
    have hcast2 : (L : ℝ) * ((r : ℝ) - s - 2) = ((L * d : ℕ) : ℝ) := by
      rw [hd]
      push_cast
      ring
    rw [hcast2]
    calc ‖X‖ * _ ≤ ‖X‖ * (E / torusDecayFactor L δ ((L * d : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      _ ≤ (C₀ * ‖e‖) * (E / torusDecayFactor L δ ((L * d : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right a1 hq0
      _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
