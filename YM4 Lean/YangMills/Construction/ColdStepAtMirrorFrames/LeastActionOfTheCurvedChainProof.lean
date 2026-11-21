import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.CriticalAtAFieldWithAZeroFit
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionOfTheCurvedChain
import YangMills.Construction.ColdStepAtMirrorFrames.LeastFieldFromACriticalJet
import YangMills.Construction.ColdStepAtMirrorFrames.LinearFieldInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private abbrev LatticePoint : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem re_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : Quaternion ℝ).re = Real.cos ‖w‖ := by apply _root_.YangMills.SharedProofs.p42298 <;> assumption
private theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
private theorem plaquetteDefect_le_add {j : ℕ} {Y Y' : F.GaugeField j} {d : ℝ}
    (h : ∀ x i, ‖((Y x i : UnitQuaternion) : Quaternion ℝ) - (Y' x i : UnitQuaternion)‖ ≤ d) (hd : 0 ≤ d)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect Y p ≤ plaquetteDefect Y' p + 4 * d := by apply _root_.YangMills.Construction.DerivativeInterpolation.HolonomyPerturbation.plaquetteDefect_le_add <;> assumption
private theorem chartedField_dist_le {V : F.GaugeField F.top} {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hw : ∀ x i, ‖w x i‖ ≤ b) (hw' : ∀ x i, ‖w' x i‖ ≤ b') (x : F.Site F.depth) (i : Fin 4) :
    ‖((chartedField w V x i : UnitQuaternion) : Quaternion ℝ) - (chartedField w' V x i : UnitQuaternion)‖ ≤
      b + b' := by
  classical
  have hexp : ‖((expUnit (w x i) : UnitQuaternion) : Quaternion ℝ) - (expUnit (w' x i) : UnitQuaternion)‖ ≤
      b + b' := by
    have h1 := norm_expUnit_sub_one_le (w x i)
    have h2 := norm_expUnit_sub_one_le (w' x i)
    have e : ((expUnit (w x i) : UnitQuaternion) : Quaternion ℝ) - (expUnit (w' x i) : UnitQuaternion) =
        (((expUnit (w x i) : UnitQuaternion) : Quaternion ℝ) - 1) -
          (((expUnit (w' x i) : UnitQuaternion) : Quaternion ℝ) - 1) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith [hw x i, hw' x i]
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc]
    show ‖((expUnit (w x i) : UnitQuaternion) : Quaternion ℝ) *
        ((V (enclosingCell x) i : UnitQuaternion) : Quaternion ℝ) -
      ((expUnit (w' x i) : UnitQuaternion) : Quaternion ℝ) *
        ((V (enclosingCell x) i : UnitQuaternion) : Quaternion ℝ)‖ ≤ _
    rw [← sub_mul, norm_mul, norm_unitQuaternion, mul_one]
    exact hexp
  · rw [if_neg hc, if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ht]
      simp only [sub_self, norm_zero]
      linarith
    · rw [if_neg ht, if_neg ht]
      exact hexp
private theorem norm_expUnit_smul_sub_one_le (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    ‖((expUnit (s • X) : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ |s| := by
  have := norm_expUnit_sub_one_le (s • X)
  rwa [norm_smul, hX, mul_one, Real.norm_eq_abs] at this
private theorem siteOfCoords_add {H : BlockFrame} (j : ℕ) (a b : LatticePoint) :
    (siteOfCoords j (a + b) : H.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem siteOfCoords_siteCoords {H : BlockFrame} {k : ℕ} (y : H.Site k) :
    siteOfCoords k (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private theorem plaquetteHolonomy_of_linear {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions} {g : ℝ}
    {μ ν : Fin 4} {φ : LatticePoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    (z : LatticePoint) (α β : Fin 4) (hαβ : α < β) :
    plaquetteHolonomy U (siteOfCoords j z, α, β) = expUnit ((if α = μ ∧ β = ν then g else 0) • X) := by
  have s2 : (siteOfCoords j z : F.Site j) + unitStep j α = siteOfCoords j (z + Pi.single α 1) := by
    rw [siteOfCoords_add]; rfl
  have s3 : (siteOfCoords j z : F.Site j) + unitStep j α + unitStep j β - unitStep j α =
      siteOfCoords j (z + Pi.single β 1) := by
    rw [siteOfCoords_add]
    show _ = (siteOfCoords j z : F.Site j) + unitStep j β
    abel
  have s4 : (siteOfCoords j z : F.Site j) + unitStep j α + unitStep j β + - unitStep j α - unitStep j β =
      siteOfCoords j z := by
    abel
  unfold plaquetteHolonomy
  simp only [pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false, mul_one]
  rw [s3, s4, s2, hU, hU, hU, hU, expUnit_smul_inv, expUnit_smul_inv, ← expUnit_add_smul,
    ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
  have hcomm : z + Pi.single α 1 + Pi.single β 1 = z + Pi.single β 1 + Pi.single α 1 := by abel
  unfold linearFluxAngle
  rw [hcomm]
  have hne : α ≠ β := hαβ.ne
  have e1 : (((z + Pi.single α 1 : LatticePoint) μ : ℤ) : ℝ) = (z μ : ℝ) + if α = μ then 1 else 0 := by
    by_cases h : α = μ
    · subst h; simp
    · simp [h, Ne.symm h]
  have e2 : (((z + Pi.single β 1 : LatticePoint) μ : ℤ) : ℝ) = (z μ : ℝ) + if β = μ then 1 else 0 := by
    by_cases h : β = μ
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e1, e2]
  by_cases hαν : α = ν
  · have hβν : β ≠ ν := by rw [← hαν]; exact Ne.symm hne
    have hαμ : α ≠ μ := by rw [hαν]; exact hμν.ne'
    have hβμ : β ≠ μ := by
      intro h
      rw [hαν, h] at hαβ
      exact absurd hαβ (not_lt.mpr hμν.le)
    have hp : (if α = μ ∧ β = ν then g else 0) = 0 := by rw [if_neg (fun h => hαμ h.1)]
    rw [hp]
    simp only [if_pos hαν, if_neg hβν, if_neg hαμ, if_neg hβμ]
    ring
  · by_cases hβν : β = ν
    · by_cases hαμ : α = μ
      · have hβμ : β ≠ μ := by rw [hαμ] at hne; exact Ne.symm hne
        have hp : (if α = μ ∧ β = ν then g else 0) = g := by rw [if_pos ⟨hαμ, hβν⟩]
        rw [hp]
        simp only [if_neg hαν, if_pos hβν, if_pos hαμ, if_neg hβμ]
        ring
      · have hp : (if α = μ ∧ β = ν then g else 0) = 0 := by rw [if_neg (fun h => hαμ h.1)]
        rw [hp]
        simp only [if_neg hαν, if_pos hβν, if_neg hαμ]
        ring
    · have hp : (if α = μ ∧ β = ν then g else 0) = 0 := by rw [if_neg (fun h => hβν h.2)]
      rw [hp]
      simp only [if_neg hαν, if_neg hβν]
      ring
abbrev _root_.YangMills.DeltaSharedProofs.p502334 := @plaquetteHolonomy_of_linear
private theorem plaquetteDefect_of_linear_le {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) {g : ℝ} {μ ν : Fin 4} {φ : LatticePoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) : plaquetteDefect U p ≤ |g| := by
  obtain ⟨x, α, β⟩ := p
  unfold plaquetteDefect
  conv_lhs => rw [← siteOfCoords_siteCoords x]
  rw [plaquetteHolonomy_of_linear hU hμν _ α β hp]
  refine (norm_expUnit_smul_sub_one_le X hX _).trans ?_
  split_ifs
  · exact le_rfl
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p502391 := @plaquetteDefect_of_linear_le
private theorem mem_innerBonds_finiteCells {H : BlockFrame} (hodd : Odd H.blockSide) (hs : ∀ i, 0 < H.extent i)
    {k : ℕ} (hk : k ≤ H.top) (b : H.Site k × Fin 4) : b ∈ innerBonds (finiteCells H) k := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨_root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _, Finset.mem_univ _⟩,
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _⟩
private theorem mem_innerPlaquettes_finiteCells_iff {H : BlockFrame} (hodd : Odd H.blockSide)
    (hs : ∀ i, 0 < H.extent i) {k : ℕ} (hk : k ≤ H.top)
    (p : H.Site k × Fin 4 × Fin 4) : p ∈ innerPlaquettes (finiteCells H) k ↔ p.2.1 < p.2.2 := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨⟨_root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _, Finset.mem_univ _, Finset.mem_univ _⟩, h,
      fun x _ => _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk x⟩
private theorem refineSite_eq_cellCentre (H : BlockFrame) (y : H.Cell) :
    (_root_.YangMills.Construction.BlockAverages.refineSite y : H.Site H.depth) = cellCentre H.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
private theorem plaquetteDefect_gaugeTransform {j : ℕ} (hcov : gaugeCovarianceStatement) (hj : j < F.top)
    (hL : 0 < F.blockSide) (γ : F.Site j → UnitQuaternion) (U : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) p = plaquetteDefect U p := by
  unfold plaquetteDefect
  obtain ⟨_, _, h3, _⟩ := hcov F j hj hL
  rw [h3]
  have e : ((γ p.1 * plaquetteHolonomy U p * (γ p.1)⁻¹ : UnitQuaternion) : Quaternion ℝ) - 1 =
      ((γ p.1 : UnitQuaternion) : Quaternion ℝ) * (((plaquetteHolonomy U p : UnitQuaternion) : Quaternion ℝ) - 1) *
        (((γ p.1)⁻¹ : UnitQuaternion) : Quaternion ℝ) := by
    have hone : ((γ p.1 : UnitQuaternion) : Quaternion ℝ) * (((γ p.1)⁻¹ : UnitQuaternion) : Quaternion ℝ) = 1 := by
      show ((γ p.1 * (γ p.1)⁻¹ : UnitQuaternion) : Quaternion ℝ) = 1
      rw [mul_inv_cancel]; rfl
    show ((γ p.1 : UnitQuaternion) : Quaternion ℝ) * ((plaquetteHolonomy U p : UnitQuaternion) : Quaternion ℝ) *
      (((γ p.1)⁻¹ : UnitQuaternion) : Quaternion ℝ) - 1 = _
    rw [mul_sub, sub_mul, mul_one, hone]
  rw [e, norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
private theorem minimal_of_critical_chart (hjet : MinimalOfCriticalJet) (hchart : LinearFieldChartGauge)
    (hgauge : MinimalActionGaugeInvariant) (hcov : gaugeCovarianceStatement)
    (hleast : minimalChainExistenceStatement)
    {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hc : c.Admissible a L) {s₁ γ₀ : ℝ} (hs₁ : 0 < s₁)
    (hs₁σ : s₁ ≤ c.σA) (hγ₀ : 0 < γ₀) (hγs : γ₀ < s₁) (hγρ : γ₀ ≤ c.ρA)
    (hbig : 9 * γ₀ + 4 * (c.N 0 * s₁) < c.σA) (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n : ℕ)
    (hodd : Odd F.blockSide)
    (hFL : F.blockSide = L) (hn : ∀ i, F.extent i = n) (h64 : 64 ≤ n) (hX : ‖X‖ = 1) (hμν : μ < ν) {g : ℝ}
    (hg : (F.blockSide : ℝ) ^ 2 * |g| ≤ γ₀) (U : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (hpair : IsAbelianLinearPair X g μ ν U V)
    (hfit : ∀ c, blockFit U V c = 0)
    (hcr : ∀ (γ : F.Site F.depth → UnitQuaternion) (w₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions),
      (∀ z, γ (cellCentre F.depth z) = 1) →
      (∀ x, ∃ β : ℝ, γ x = expUnit (β • X)) → (∀ x i, _root_.YangMills.Construction.BlockAverages.gaugeTransform γ U x i = chartedField w₀ V x i) →
      HasFDerivAt (formComposition (innerBonds (finiteCells F) F.depth)
          (minimalAction a (finiteCells F) F.depth) (chartedField w₀ V))
        (0 : (↥(innerBonds (finiteCells F) F.depth) → imaginaryQuaternions) →L[ℝ] ℝ) 0) :
    (∀ W' : F.GaugeField F.depth,
        blockEnergy a (finiteCells F) F.depth U V ≤ blockEnergy a (finiteCells F) F.depth W' V) ∧
      minimalAction a (finiteCells F) F.top V = minimalAction a (finiteCells F) F.depth U := by
  classical
  set S := finiteCells F with hS
  have hLpos : 0 < F.blockSide := hodd.pos
  have hnpos : 0 < n := by omega
  have hside : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact hnpos
  have hL1 : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hLpos
  have hg1 : |g| ≤ γ₀ := by
    have : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
    have h0 := abs_nonneg g
    nlinarith
  obtain ⟨φ, hU, hV⟩ := hpair
  obtain ⟨γ, w₀, hγ1, hγb, hgeq, htree, hw₀⟩ := hchart F X g μ ν n hodd hn (by omega) hX hμν U V ⟨φ, hU, hV⟩
  have hw₀' : ∀ x i, ‖w₀ x i‖ ≤ γ₀ := fun x i => (hw₀ x i).trans hg
  have hcoldV : IsSmallCurvature s₁ V := by
    intro p hp
    have h1 := plaquetteDefect_of_linear_le hX hV hμν p hp
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2)] at h1
    linarith
  have hchain : IsBlockTorus L F := ⟨hFL, n, h64, hn⟩
  have cl := hc.estimates F s₁ V hchain hs₁ hs₁σ hcoldV
  obtain ⟨w₁, hw₁, _, _⟩ := cl.minimizer
  have hN : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ innerBonds S F.depth :=
    mem_innerBonds_finiteCells hodd hside (by simp [BlockFrame.top])
  have hoff₀ : ∀ b, b ∉ chordBonds S → w₀ b.1 b.2 = 0 := by
    intro b hb
    apply htree
    by_contra ht
    exact hb (Finset.mem_filter.2 ⟨hbond b, ht⟩)
  have hoff₁ := hw₁.1
  have hw₁b : ∀ x i, ‖w₁ x i‖ ≤ c.N 0 * s₁ := by
    intro x i
    by_cases hb : (x, i) ∈ chordBonds S
    · exact (hw₁.2.1 _ hb).trans (min_le_right _ _)
    · have := hoff₁ _ hb
      simp only at this
      rw [this, norm_zero]
      positivity
  have hwτ : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∀ x i,
      ‖w₀ x i + τ • (w₁ x i - w₀ x i)‖ ≤ (1 - τ) * ‖w₀ x i‖ + τ * ‖w₁ x i‖ := by
    intro τ h0 h1 x i
    have e : w₀ x i + τ • (w₁ x i - w₀ x i) = (1 - τ) • w₀ x i + τ • w₁ x i := by module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
      abs_of_nonneg (by linarith)]
  have hseg : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      (∀ b ∈ chordBonds S, ‖w₀ b.1 b.2 + τ • (w₁ b.1 b.2 - w₀ b.1 b.2)‖ ≤ c.ρA) ∧
      IsCold S F.depth c.σA (chartedField (fun x i => w₀ x i + τ • (w₁ x i - w₀ x i)) V) := by
    intro τ h0 h1
    constructor
    · intro b hb
      have e1 := hwτ τ h0 h1 b.1 b.2
      have e2 := (hw₁.2.1 b hb).trans (min_le_left _ _)
      have e3 := (hw₀' b.1 b.2).trans hγρ
      nlinarith [mul_le_mul_of_nonneg_left e3 (by linarith : 0 ≤ 1 - τ), mul_le_mul_of_nonneg_left e2 h0]
    · intro p hp
      have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp).2.1
      have hbτ : ∀ x i, ‖w₀ x i + τ • (w₁ x i - w₀ x i)‖ ≤ γ₀ + c.N 0 * s₁ := by
        intro x i
        have e1 := hwτ τ h0 h1 x i
        have e2 := hw₁b x i
        have e3 := hw₀' x i
        have e4 : 0 ≤ c.N 0 * s₁ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left e3 (by linarith : 0 ≤ 1 - τ), mul_le_mul_of_nonneg_left e2 h0]
      have hclose := plaquetteDefect_le_add
        (fun x i => chartedField_dist_le (V := V) (by positivity) hγ₀.le hbτ hw₀' x i) (by positivity) p
      have hfield : chartedField w₀ V = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ U := by
        funext x i
        exact (hgeq x i).symm
      rw [hfield, plaquetteDefect_gaugeTransform hcov (by simp [BlockFrame.top]) hLpos] at hclose
      have hcU := plaquetteDefect_of_linear_le hX hU hμν p hlt
      nlinarith
  have hfits : ∀ c' ∈ innerBonds S F.top, blockFit (chartedField w₀ V) V c' = 0 := by
    intro c' _
    have hfield : chartedField w₀ V = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ U := by
      funext x i
      exact (hgeq x i).symm
    obtain ⟨_, _, _, h4⟩ := hcov F F.depth (by simp [BlockFrame.top]) hLpos
    have hV1 : _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun _ => (1 : UnitQuaternion)) V = V := by
      funext x i
      simp [_root_.YangMills.Construction.BlockAverages.gaugeTransform]
    have := h4 γ (fun _ => 1) U V c' (by rw [refineSite_eq_cellCentre, hγ1]) (by rw [refineSite_eq_cellCentre, hγ1])
    rw [hV1] at this
    rw [hfield, this, hfit]
  have hcrit := hcr γ w₀ hγ1 hγb hgeq
  have hlam : 0 < c.lam := hc.positivity.2.2.1
  have ha0 : 0 ≤ a := by linarith
  have hkey := hjet F a c.lam c.ρA c.σA S V w₀ w₁ ha0 hlam hbond cl.hessian hoff₀ hoff₁ hseg hfits hcrit
  have hfield : chartedField w₀ V = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ U := by
    funext x i
    exact (hgeq x i).symm
  have hEU : blockEnergy a S F.depth U V = minimalAction a S F.depth U := by
    unfold blockEnergy
    rw [Finset.sum_eq_zero (fun c' _ => hfit c'), mul_zero, add_zero]
  have hE0 : blockEnergy a S F.depth (chartedField w₀ V) V = minimalAction a S F.depth U := by
    unfold blockEnergy
    rw [Finset.sum_eq_zero hfits, mul_zero, add_zero, hfield]
    exact hgauge F a S F.depth (by simp [BlockFrame.top]) hLpos γ U
  have hmin : ∀ W' : F.GaugeField F.depth, blockEnergy a S F.depth U V ≤ blockEnergy a S F.depth W' V := by
    intro W'
    rw [hEU, ← hE0]
    exact hkey.trans (hw₁.2.2 W')
  refine ⟨hmin, ?_⟩
  rw [← hEU]
  obtain ⟨hf0, hnn, _, _⟩ := hleast F a S ha0
  show (⨅ W : F.GaugeField F.depth,
    (minimalAction a S F.depth W + a * ∑ c' ∈ innerBonds S (F.depth + 1), blockFit W V c')) = _
  apply le_antisymm
  · apply ciInf_le ⟨0, ?_⟩ U
    rintro _ ⟨W', rfl⟩
    exact add_nonneg (hnn _ W') (mul_nonneg ha0 (Finset.sum_nonneg fun c' _ => hf0 _ W' _ c'))
  · exact le_ciInf hmin
private theorem transferField_constantCurvatureChain (hA : MinimalActionTransfer) {F G : BlockFrame} {K : ℕ}
    (h : SharePeriods F G K) (X : imaginaryQuaternions) (μ ν : Fin 4) (l : ℕ) :
    ∀ j, j ≤ K → transferField G (constantCurvatureChain F X μ ν l j) = constantCurvatureChain G X μ ν l j := by
  obtain ⟨_, _, hmean, _, _, _, hrt', hcoord⟩ := hA F G K 0 h
  intro j
  induction j with
  | zero =>
    intro _
    funext x i
    have hc : ∀ k, siteCoords (transferSite F x) k = siteCoords x k := by
      intro k
      have h1 := hcoord 0 (transferSite F x) (Nat.zero_le _)
      rw [hrt' 0 x (Nat.zero_le _)] at h1
      exact (congrFun h1 k).symm
    have hp : F.period 0 μ = G.period 0 μ := h.period_eq 0 (Nat.zero_le _) μ
    show constantCurvatureField F X μ ν l (transferSite F x) i = constantCurvatureField G X μ ν l x i
    unfold constantCurvatureField finestSide
    dsimp only
    simp only [hc, hp]
  | succ j ih =>
    intro hj
    funext x i
    show quaternionUnitPart (_root_.YangMills.Construction.BlockAverages.contourAverage (constantCurvatureChain F X μ ν l j) (transferSite F x, i)) =
      quaternionUnitPart (_root_.YangMills.Construction.BlockAverages.contourAverage (constantCurvatureChain G X μ ν l j) (x, i))
    rw [← ih (by omega)]
    congr 1
    conv_rhs => rw [← siteOfCoords_siteCoords x]
    exact (hmean j _ (siteCoords x) i (by omega)).symm
private theorem isAbelianWithFlux_gaugeTransform (hcov : gaugeCovarianceStatement) {j : ℕ} (hj : j < F.top)
    (hL : 0 < F.blockSide) {U : F.GaugeField j} {X : imaginaryQuaternions} {g : ℝ} {μ ν : Fin 4}
    {φ : LatticePoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    {γ : F.Site j → UnitQuaternion}
    (hγ : ∀ x, ∃ β : ℝ, γ x = expUnit (β • X)) : IsAbelianWithFlux X g μ ν (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) := by
  choose β hβ using hγ
  constructor
  · refine ⟨fun x i => β x + linearFluxAngle g μ ν φ (siteCoords x) i + - β (x + unitStep j i), ?_⟩
    intro x i
    unfold _root_.YangMills.Construction.BlockAverages.gaugeTransform
    have hx : U x i = expUnit (linearFluxAngle g μ ν φ (siteCoords x) i • X) := by
      conv_lhs => rw [← siteOfCoords_siteCoords x]
      exact hU _ i
    rw [hx, hβ, hβ, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul]
  · intro x α α' hα
    obtain ⟨_, _, h3, _⟩ := hcov F j hj hL
    rw [h3]
    dsimp only
    have hP : plaquetteHolonomy U (x, α, α') = expUnit ((if α = μ ∧ α' = ν then g else 0) • X) := by
      conv_lhs => rw [← siteOfCoords_siteCoords x]
      exact plaquetteHolonomy_of_linear hU hμν _ α α' hα
    rw [hP, hβ, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul]
    congr 2
    ring
private theorem sharePeriods_coarser (F : BlockFrame) (k n : ℕ) (hk : F.depth = k + 1) (hodd : Odd F.blockSide)
    (hn : ∀ i, F.extent i = n) (hn0 : 0 < n) :
    SharePeriods F ⟨F.blockSide, k, fun _ => n * F.blockSide⟩ (k + 1) := by
  refine ⟨rfl, hodd, fun i => by rw [hn]; exact hn0, fun _ => Nat.mul_pos hn0 hodd.pos, ?_, ?_, ?_⟩
  · simp [BlockFrame.top, hk]
  · simp [BlockFrame.top]
  · intro j hj i
    unfold BlockFrame.period
    have h1 : F.top - j = (k + 1 - j) + 1 := by simp only [BlockFrame.top, hk]; omega
    have h2 : (⟨F.blockSide, k, fun _ => n * F.blockSide⟩ : BlockFrame).top - j = k + 1 - j := by
      simp [BlockFrame.top]
    rw [hn, h1, h2, pow_succ]
    ring
private theorem contDiffThree_of_transfer {a : ℝ} {F G : BlockFrame} {K : ℕ} (hA : MinimalActionTransfer)
    (h : SharePeriods F G K) (hK : K = G.top) (W : F.GaugeField K)
    (hG : IsBondAnalyticAt (minimalAction a (finiteCells G) G.top) (hK ▸ transferField G W)) :
    ContDiffThreeAlongBonds (minimalAction a (finiteCells F) K) W := by
  subst hK
  obtain ⟨hleast, _, _, _, _, hrt, hrt', _⟩ := hA F G G.top a h
  intro k c X
  have hfun : (fun τ : Fin k → ℝ =>
      minimalAction a (finiteCells F) G.top (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) =
      fun τ => minimalAction a (finiteCells G) G.top
        (rotatedField (BlockAverages.bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ)
          (transferField G W)) := by
    funext τ
    rw [hleast G.top _ le_rfl]
    congr 1
    funext x i
    show expUnit (ColdStepAtMirrorFrames.bondSpread c X τ (transferSite F x) i) * W (transferSite F x) i =
      expUnit (BlockAverages.bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ x i) *
        W (transferSite F x) i
    congr 2
    unfold ColdStepAtMirrorFrames.bondSpread BlockAverages.bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have hiff : c l = (transferSite F x, i) ↔ (transferSite G (c l).1, (c l).2) = (x, i) := by
      constructor
      · intro e
        rw [e]
        exact Prod.ext (hrt' G.top x le_rfl) rfl
      · intro e
        have e1 := (Prod.ext_iff.1 e).1
        have e2 := (Prod.ext_iff.1 e).2
        refine Prod.ext ?_ e2
        have := hrt G.top (c l).1 le_rfl
        dsimp only at e1
        rw [e1] at this
        exact this.symm
    by_cases hb : c l = (transferSite F x, i)
    · rw [if_pos hb, if_pos (hiff.1 hb)]
    · rw [if_neg hb, if_neg (fun e => hb (hiff.2 e))]
  rw [hfun]
  exact (hG k _ X).contDiffAt
private theorem wilsonAction_of_linear {U : F.GaugeField 0} {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {g : ℝ}
    {μ ν : Fin 4} {φ : LatticePoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords 0 z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    (hodd : Odd F.blockSide)
    {M : ℕ} (hM : ∀ i, F.period 0 i = M) (hM0 : 0 < M) (hs : ∀ i, 0 < F.extent i) :
    wilsonAction (finiteCells F) U = (M : ℝ) ^ 4 * (1 - Real.cos g) := by
  classical
  set S := finiteCells F with hS
  have hT : ∀ x : F.Site 0, x ∈ sitesOfCells S 0 :=
    fun x => _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs (Nat.zero_le _) x
  have hP : ∀ p : F.Site 0 × Fin 4 × Fin 4, p ∈ innerPlaquettes S 0 ↔ p.2.1 < p.2.2 :=
    fun p => mem_innerPlaquettes_finiteCells_iff hodd hs (Nat.zero_le _) p
  have hval : ∀ p ∈ innerPlaquettes S 0, 1 - ((plaquetteHolonomy U p : UnitQuaternion) : Quaternion ℝ).re =
      if p.2.1 = μ ∧ p.2.2 = ν then 1 - Real.cos g else 0 := by
    rintro ⟨x, α, β⟩ hp
    have hlt : α < β := (hP _).1 hp
    have hq : plaquetteHolonomy U (x, α, β) = expUnit ((if α = μ ∧ β = ν then g else 0) • X) := by
      conv_lhs => rw [← siteOfCoords_siteCoords x]
      exact plaquetteHolonomy_of_linear hU hμν _ α β hlt
    rw [hq, re_expUnit, norm_smul, hX, mul_one, Real.norm_eq_abs, Real.cos_abs]
    dsimp only
    split_ifs <;> simp
  unfold wilsonAction
  rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
  have hfil : (innerPlaquettes S 0).filter (fun p => p.2.1 = μ ∧ p.2.2 = ν) =
      (sitesOfCells S 0).image (fun x => ((x, μ, ν) : F.Site 0 × Fin 4 × Fin 4)) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨p.1, hT _, by rw [← h1, ← h2]⟩
    · rintro ⟨x, _, rfl⟩
      exact ⟨(hP _).2 hμν, rfl, rfl⟩
  rw [hfil, Finset.sum_const, Finset.card_image_of_injective _
    (by intro x y h; exact (Prod.ext_iff.1 h).1), nsmul_eq_mul]
  congr 1
  have hne : ∀ i, NeZero (F.period 0 i) := fun i => ⟨by rw [hM]; exact hM0.ne'⟩
  have huniv : sitesOfCells S 0 = Finset.univ := by
    ext x
    simp [hT x]
  rw [huniv, Finset.card_univ, Fintype.card_pi]
  simp only [ZMod.card, hM, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl
private theorem critical_gaugeTransform_succ (habel : ConstantCurvatureChainAbelian)
    (hA : MinimalActionTransfer) (hgauge : MinimalActionGaugeInvariant)
    (hzero : CriticalAtExactFit)
    (hcov : gaugeCovarianceStatement)
    {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha0 : 0 ≤ a) (hc : c.Admissible a L) {s₁ γ₀ : ℝ} (hs₁ : 0 < s₁)
    (hs₁σ : s₁ ≤ c.σA) (hγs : γ₀ < s₁) (Fr : BlockFrame) (k : ℕ) (hk : Fr.depth = k + 1)
    (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ)
    (hoddF : Odd Fr.blockSide) (hFL : Fr.blockSide = L) (hn : ∀ i, Fr.extent i = n) (h64 : 64 ≤ n) (hn0 : 0 < n)
    (hLpos : 0 < Fr.blockSide)
    (hX : ‖X‖ = 1) (hμν : μ < ν) (hl1 : 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1)
    {g : ℝ} (hg : |g| ≤ γ₀) {φ : LatticePoint → ℝ}
    (hU : ∀ z i, constantCurvatureChain Fr X μ ν l (k + 1) (siteOfCoords (k + 1) z) i =
      expUnit (linearFluxAngle g μ ν φ z i • X))
    (γ : Fr.Site (k + 1) → UnitQuaternion)
    (htop : ∀ (Fm : BlockFrame), Fm = ⟨Fr.blockSide, k, fun _ => n * Fr.blockSide⟩ →
      minimalAction a (finiteCells Fm) (k + 1) (constantCurvatureChain Fm X μ ν l (k + 1)) =
        minimalAction a (finiteCells Fm) k (constantCurvatureChain Fm X μ ν l k)) :
    HasFDerivAt (formComposition (innerBonds (finiteCells Fr) (k + 1)) (minimalAction a (finiteCells Fr) (k + 1))
        (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ (constantCurvatureChain Fr X μ ν l (k + 1))))
      (0 : (↥(innerBonds (finiteCells Fr) (k + 1)) → imaginaryQuaternions) →L[ℝ] ℝ) 0 := by
  classical
  have hper := sharePeriods_coarser Fr k n hk hoddF hn hn0
  set Fm : BlockFrame := ⟨Fr.blockSide, k, fun _ => n * Fr.blockSide⟩ with hFm
  have hacr := transferField_constantCurvatureChain hA hper X μ ν l
  obtain ⟨hle, _, _, _, hhol, _, _, _⟩ := hA Fr Fm (k + 1) a hper
  have h64' : 64 ≤ n * Fr.blockSide := le_trans h64 (Nat.le_mul_of_pos_right n hLpos)
  have htop' := htop Fm rfl
  have hab0 := habel Fr X μ ν n l hoddF hn hn0 hX hμν hl1 k (by simp only [BlockFrame.top, hk]; omega)
  obtain ⟨_, _, hmean0⟩ := hab0.2 (by simp only [BlockFrame.top, hk]; omega)
  obtain ⟨hinj, hcm, _, _⟩ := hcov Fr k (by simp only [BlockFrame.top, hk]; omega) hLpos
  let γ' : Fr.Site k → UnitQuaternion := Function.extend (_root_.YangMills.Construction.BlockAverages.refineSite (F := Fr) (j := k)) γ 1
  have hγ' : ∀ y, γ' (_root_.YangMills.Construction.BlockAverages.refineSite y) = γ y := fun y => hinj.extend_apply _ _ _
  set W₀ : Fr.GaugeField (k + 1) := _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (constantCurvatureChain Fr X μ ν l (k + 1)) with hW₀
  have hval : minimalAction a (finiteCells Fr) (k + 1) W₀ =
      minimalAction a (finiteCells Fr) k (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ' (constantCurvatureChain Fr X μ ν l k)) := by
    rw [hW₀, hgauge Fr a _ (k + 1) (by simp only [BlockFrame.top, hk]; omega) hLpos,
      hgauge Fr a _ k (by simp only [BlockFrame.top, hk]; omega) hLpos, hle (k + 1) _ le_rfl,
      hle k _ (Nat.le_succ k), hacr (k + 1) le_rfl, hacr k (Nat.le_succ k)]
    exact htop'
  have hmean : ∀ c' : Fr.Site (k + 1) × Fin 4, ∃ ρ : ℝ, 0 < ρ ∧
      _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform γ' (constantCurvatureChain Fr X μ ν l k)) c' =
        ρ • ((W₀ c'.1 c'.2 : UnitQuaternion) : Quaternion ℝ) := by
    intro c'
    obtain ⟨ρ, hρ', hm⟩ := hmean0 c'
    refine ⟨ρ, hρ', ?_⟩
    rw [hcm, hm, hγ', hγ']
    show _ = ρ • (((γ c'.1 : UnitQuaternion) : Quaternion ℝ) *
      ((constantCurvatureChain Fr X μ ν l (k + 1) c'.1 c'.2 : UnitQuaternion) : Quaternion ℝ) *
      (((γ (c'.1 + unitStep (k + 1) c'.2))⁻¹ : UnitQuaternion) : Quaternion ℝ))
    rw [mul_smul_comm, smul_mul_assoc]
  have hcold : IsSmallCurvature s₁ (transferField Fm W₀) := by
    rintro ⟨x, α, β⟩ hlt
    have hc1 : plaquetteDefect (transferField Fm W₀) (x, α, β) =
        plaquetteDefect W₀ (siteOfCoords (k + 1) (siteCoords x), α, β) := by
      unfold plaquetteDefect plaquetteHolonomy
      dsimp only
      conv_lhs => rw [← siteOfCoords_siteCoords x]
      rw [hhol (k + 1) W₀ _ (siteCoords x) le_rfl]
    rw [hc1, hW₀, plaquetteDefect_gaugeTransform hcov (by simp only [BlockFrame.top, hk]; omega) hLpos]
    have hc2 := plaquetteDefect_of_linear_le hX hU hμν (siteOfCoords (k + 1) (siteCoords x), α, β) hlt
    linarith
  have hchainT : IsBlockTorus L Fm := ⟨hFL, n * Fr.blockSide, h64', fun _ => rfl⟩
  have clm := hc.estimates Fm s₁ (transferField Fm W₀) hchainT hs₁ hs₁σ hcold
  have hsm : ContDiffThreeAlongBonds (minimalAction a (finiteCells Fr) (k + 1)) W₀ :=
    contDiffThree_of_transfer hA hper rfl W₀ clm.cellShares.1
  exact hzero Fr a (finiteCells Fr) k (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ' (constantCurvatureChain Fr X μ ν l k)) W₀ ha0 hsm hval hmean
theorem constantCurvatureMinimalAction_holds (habel : ConstantCurvatureChainAbelian)
    (hA : MinimalActionTransfer) (hgauge : MinimalActionGaugeInvariant)
    (hchart : LinearFieldChartGauge) (hjet : MinimalOfCriticalJet)
    (hbare : BareActionCriticalAtAbelianField) (hzero : CriticalAtExactFit)
    (hcov : gaugeCovarianceStatement) (hleast : minimalChainExistenceStatement) :
    ConstantCurvatureMinimalAction := by
  classical
  intro a L c ha hodd hc
  have hρ : 0 < c.ρA := hc.classical.1.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hN : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  set s₁ : ℝ := c.σA / (8 * (c.N 0 + 1)) with hs₁def
  have hs₁ : 0 < s₁ := by positivity
  have hs₁σ : s₁ ≤ c.σA := by
    rw [hs₁def, div_le_iff₀ (by positivity)]
    nlinarith
  have hNs : 4 * (c.N 0 * s₁) ≤ c.σA / 2 := by
    have : c.N 0 * s₁ = c.σA * (c.N 0 / (8 * (c.N 0 + 1))) := by
      rw [hs₁def]; field_simp
    rw [this]
    have h2 : c.N 0 / (8 * (c.N 0 + 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    nlinarith
  set γ₀ : ℝ := min (min 1 c.ρA) (min (s₁ / 2) (c.σA / 32)) with hγdef
  have hγ₀ : 0 < γ₀ := by
    apply lt_min (lt_min one_pos hρ) (lt_min (by positivity) (by positivity))
  have hγ1 : γ₀ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hγρ : γ₀ ≤ c.ρA := (min_le_left _ _).trans (min_le_right _ _)
  have hγs : γ₀ < s₁ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hγσ : γ₀ ≤ c.σA / 32 := (min_le_right _ _).trans (min_le_right _ _)
  have hbig : 9 * γ₀ + 4 * (c.N 0 * s₁) < c.σA := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hflux : ∀ (F : BlockFrame) (μ : Fin 4) (n l : ℕ), (∀ i, F.extent i = n) → 0 < n → 0 < F.blockSide →
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      (F.blockSide : ℝ) ^ 2 * |levelFlux F μ l F.depth| ≤ γ₀ := by
    intro F μ n l hn h0 hL hl
    have hper : F.period F.depth μ = n * F.blockSide := by
      have : F.top - F.depth = 1 := by simp [BlockFrame.top]
      simp [BlockFrame.period, this, hn]
    unfold levelFlux
    rw [hper, abs_of_nonneg (by positivity)]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hL' : (F.blockSide : ℝ) ≠ 0 := by positivity
    have e : (F.blockSide : ℝ) ^ 2 * (2 * Real.pi * l / (((n * F.blockSide : ℕ) : ℝ)) ^ 2) =
        2 * Real.pi * l / (n : ℝ) ^ 2 := by
      push_cast
      field_simp
    rw [e]
    exact hl
  have key : ∀ (t : ℕ) (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ), F.depth = t →
      F.blockSide = L → (∀ i, F.extent i = n) →
      64 ≤ n → ‖X‖ = 1 → μ < ν → 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      (∀ W' : F.GaugeField F.depth,
        blockEnergy a (finiteCells F) F.depth (constantCurvatureChain F X μ ν l F.depth)
            (constantCurvatureChain F X μ ν l F.top) ≤
          blockEnergy a (finiteCells F) F.depth W' (constantCurvatureChain F X μ ν l F.top)) ∧
      minimalAction a (finiteCells F) F.top (constantCurvatureChain F X μ ν l F.top) =
        minimalAction a (finiteCells F) F.depth (constantCurvatureChain F X μ ν l F.depth) := by
    intro t
    induction t with
    | zero =>
      intro F X μ ν n l ht hFL hn h64 hX hμν hl
      have hoddF : Odd F.blockSide := hFL ▸ hodd
      have hn0 : 0 < n := by omega
      have hab := habel F X μ ν n l hoddF hn hn0 hX hμν (hl.trans hγ1) F.depth (by simp [BlockFrame.top])
      obtain ⟨hfit, hpair, _⟩ := hab.2 (by simp [BlockFrame.top])
      refine minimal_of_critical_chart hjet hchart hgauge hcov hleast ha hc hs₁ hs₁σ hγ₀ hγs hγρ hbig F X μ ν n
        hoddF hFL hn h64 hX hμν (hflux F μ n l hn hn0 hoddF.pos hl) _ _ hpair hfit ?_
      intro γ w₀ _ hγb hgeq
      obtain ⟨φ, hU, _⟩ := hpair
      have hfield : chartedField w₀ (constantCurvatureChain F X μ ν l F.top) =
          gaugeTransform γ (constantCurvatureChain F X μ ν l F.depth) := by
        funext x i
        exact (hgeq x i).symm
      rw [hfield]
      have hFab := isAbelianWithFlux_gaugeTransform hcov (by simp [BlockFrame.top]) hoddF.pos hU hμν hγb
      obtain ⟨L', t', side⟩ := F
      dsimp only at ht
      subst ht
      exact (hbare _ X _ μ ν hoddF (fun i => by rw [hn]; exact hn0) hX hμν _ hFab).2
    | succ k ih =>
      intro F X μ ν n l ht hFL hn h64 hX hμν hl
      have hoddF : Odd F.blockSide := hFL ▸ hodd
      have hn0 : 0 < n := by omega
      have hLpos : 0 < F.blockSide := hoddF.pos
      have hab := habel F X μ ν n l hoddF hn hn0 hX hμν (hl.trans hγ1) F.depth (by simp [BlockFrame.top])
      obtain ⟨hfit, hpair, _⟩ := hab.2 (by simp [BlockFrame.top])
      refine minimal_of_critical_chart hjet hchart hgauge hcov hleast ha hc hs₁ hs₁σ hγ₀ hγs hγρ hbig F X μ ν n
        hoddF hFL hn h64 hX hμν (hflux F μ n l hn hn0 hoddF.pos hl) _ _ hpair hfit ?_
      intro γ w₀ hγ1' hγb hgeq
      obtain ⟨φ, hU, _⟩ := hpair
      have hfield : chartedField w₀ (constantCurvatureChain F X μ ν l F.top) =
          gaugeTransform γ (constantCurvatureChain F X μ ν l F.depth) := by
        funext x i
        exact (hgeq x i).symm
      rw [hfield]
      have hL1 : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hLpos
      have h64' : 64 ≤ n * F.blockSide := le_trans h64 (Nat.le_mul_of_pos_right n hLpos)
      have hl' : 2 * Real.pi * l / ((n * F.blockSide : ℕ) : ℝ) ^ 2 ≤ γ₀ := by
        refine le_trans ?_ hl
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : (n : ℝ) ≤ ((n * F.blockSide : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_right n hLpos
        have h0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
      have hgF : |levelFlux F μ l F.depth| ≤ γ₀ := by
        have hfl := hflux F μ n l hn hn0 hLpos hl
        have h0 := abs_nonneg (levelFlux F μ l F.depth)
        have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
        nlinarith
      have htopm : ∀ Fm : BlockFrame, Fm = ⟨F.blockSide, k, fun _ => n * F.blockSide⟩ →
          minimalAction a (finiteCells Fm) (k + 1) (constantCurvatureChain Fm X μ ν l (k + 1)) =
            minimalAction a (finiteCells Fm) k (constantCurvatureChain Fm X μ ν l k) := by
        intro Fm hFm
        subst hFm
        exact (ih ⟨F.blockSide, k, fun _ => n * F.blockSide⟩ X μ ν (n * F.blockSide) l rfl hFL (fun _ => rfl)
          h64' hX hμν hl').2
      obtain ⟨L', t', side⟩ := F
      dsimp only at ht
      subst ht
      exact critical_gaugeTransform_succ habel hA hgauge hzero hcov ha0 hc hs₁ hs₁σ hγs _ k rfl X μ ν n l hoddF
        hFL hn h64 hn0 hLpos hX hμν (hl.trans hγ1) hgF hU γ htopm
  refine ⟨γ₀, hγ₀, ?_⟩
  intro F X μ ν n l hFL hn h64 hX hμν hl
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hn0 : 0 < n := by omega
  have hLpos : 0 < F.blockSide := hoddF.pos
  have hstep : ∀ j, j < F.top →
      (∀ W' : F.GaugeField j,
        blockEnergy a (finiteCells F) j (constantCurvatureChain F X μ ν l j)
            (constantCurvatureChain F X μ ν l (j + 1)) ≤
          blockEnergy a (finiteCells F) j W' (constantCurvatureChain F X μ ν l (j + 1))) ∧
      minimalAction a (finiteCells F) (j + 1) (constantCurvatureChain F X μ ν l (j + 1)) =
        minimalAction a (finiteCells F) j (constantCurvatureChain F X μ ν l j) := by
    intro j hj
    set nG : ℕ := F.period (j + 1) 0 with hnG
    have hnGe : nG = n * F.blockSide ^ (F.top - (j + 1)) := by
      rw [hnG]; unfold BlockFrame.period; rw [hn]
    have hnle : n ≤ nG := by
      rw [hnGe]
      exact Nat.le_mul_of_pos_right n (by positivity)
    have hper : SharePeriods F ⟨F.blockSide, j, fun _ => nG⟩ (j + 1) := by
      refine ⟨rfl, hoddF, fun i => by rw [hn]; exact hn0, fun _ => lt_of_lt_of_le hn0 hnle, hj,
        by simp [BlockFrame.top], ?_⟩
      intro k hk i
      unfold BlockFrame.period
      have h1 : F.top - k = (F.top - (j + 1)) + (j + 1 - k) := by omega
      have h2 : (⟨F.blockSide, j, fun _ => nG⟩ : BlockFrame).top - k = j + 1 - k := by simp [BlockFrame.top]
      rw [hn, h1, h2, pow_add, hnGe]
      ring
    set G : BlockFrame := ⟨F.blockSide, j, fun _ => nG⟩ with hG
    have hlG : 2 * Real.pi * l / (nG : ℝ) ^ 2 ≤ γ₀ := by
      refine le_trans ?_ hl
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : (n : ℝ) ≤ (nG : ℝ) := by exact_mod_cast hnle
      have h0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    have htop := key j G X μ ν nG l rfl hFL (fun _ => rfl) (le_trans h64 hnle) hX hμν hlG
    have hacr := transferField_constantCurvatureChain hA hper X μ ν l
    obtain ⟨hle, hen, _⟩ := hA F G (j + 1) a hper
    constructor
    · intro W'
      rw [hen j _ _ (Nat.lt_succ_self j), hen j W' _ (Nat.lt_succ_self j), hacr j (Nat.le_succ j),
        hacr (j + 1) le_rfl]
      exact htop.1 (transferField G W')
    · rw [hle (j + 1) _ le_rfl, hle j _ (Nat.le_succ j), hacr j (Nat.le_succ j), hacr (j + 1) le_rfl]
      exact htop.2
  refine ⟨hstep, ?_⟩
  have hchainEq : ∀ j, j ≤ F.top → minimalAction a (finiteCells F) j (constantCurvatureChain F X μ ν l j) =
      minimalAction a (finiteCells F) 0 (constantCurvatureChain F X μ ν l 0) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [(hstep j (by omega)).2, ih (by omega)]
  rw [hchainEq F.top le_rfl]
  obtain ⟨φ, hU⟩ := (habel F X μ ν n l hoddF hn hn0 hX hμν (hl.trans hγ1) 0 (Nat.zero_le _)).1
  have hM : ∀ i, F.period 0 i = n * F.blockSide ^ F.top := by
    intro i
    unfold BlockFrame.period
    rw [hn]
    simp
  have hM0 : 0 < n * F.blockSide ^ F.top := by positivity
  have hv := wilsonAction_of_linear hX hU hμν hoddF hM hM0 (fun i => by rw [hn]; exact hn0)
  show wilsonAction (finiteCells F) (constantCurvatureChain F X μ ν l 0) = _
  rw [hv]
  unfold levelFlux
  rw [hM μ, hFL]
  push_cast
  rfl
end YangMills.Construction.ColdStepAtMirrorFrames
end
