import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTermsOfTheExponentProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsInValueOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.GapPartOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpotsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace ExpansionsOnTwoTori
open BlockOffsets
variable {F F' : BlockFrame}
theorem bondDeriv_zero_order {j : ℕ} (G : F.GaugeField j → ℝ) (U : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G U c X = G U := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem one_le_torusDecayFactor {L : ℕ} {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem exp_le_torusDecayFactor {L : ℕ} {δ x : ℝ} : Real.exp (δ * x) ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SeriesExpansionTerms.exp_le_torusDecayFactor <;> assumption
theorem expFlow_near {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (U : F.GaugeField j) (ε u : ℝ)
    (hB : ∀ z i, ‖B z i‖ ≤ ε) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z : F.Site j) (i : Fin 4) :
    ‖((expFlow B U u z i : UnitQuaternion) : ℍ[ℝ]) - ((U z i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  have e : ((expFlow B U u z i : UnitQuaternion) : ℍ[ℝ]) - ((U z i : UnitQuaternion) : ℍ[ℝ]) =
      (((expUnit (u • B z i) : UnitQuaternion) : ℍ[ℝ]) - 1) * ((U z i : UnitQuaternion) : ℍ[ℝ]) := by
    simp [expFlow, leftTranslate, sub_mul]
  rw [e, norm_mul, YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one]
  have h1 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (u • B z i)) ≤ ‖u • B z i‖ := distFromOne_expUnit_le _
  have h2 : ‖u • B z i‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0]
    have := hB z i
    have h3 := norm_nonneg (B z i)
    nlinarith
  exact h1.trans h2
theorem plaquetteDefect_le_of_near (hH : PathHolonomyLipschitz) {j : ℕ} (X X' : F.GaugeField j) (ε : ℝ)
    (h : ∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect X p ≤ plaquetteDefect X' p + 4 * ε := by
  have h1 := hH F j X X' ε h p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
  have h2 : ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy X' p : UnitQuaternion) : ℍ[ℝ])‖ ≤ 4 * ε := by
    simpa [plaquetteHolonomy] using h1
  unfold plaquetteDefect
  have h3 : ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - ((plaquetteHolonomy X' p : UnitQuaternion) : ℍ[ℝ])) +
        (((plaquetteHolonomy X' p : UnitQuaternion) : ℍ[ℝ]) - 1) := by abel
  rw [h3]
  have := norm_add_le (((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) -
    ((plaquetteHolonomy X' p : UnitQuaternion) : ℍ[ℝ])) (((plaquetteHolonomy X' p : UnitQuaternion) : ℍ[ℝ]) - 1)
  linarith
def minimalOffset {j : ℕ} (y z : F.Site j) : Fin 4 → ℤ := fun i => ((z - y) i).valMinAbs
theorem add_minimalOffset {j : ℕ} [∀ i, NeZero (F.period j i)] (y z : F.Site j) :
    y + siteOfCoords j (minimalOffset y z) = z := by
  funext i
  simp [minimalOffset, siteOfCoords]
theorem minimalOffset_add {j : ℕ} [∀ i, NeZero (F.period j i)] (y : F.Site j) (h : Fin 4 → ℤ)
    (hh : ∀ i, 2 * |h i| < F.period j i) : minimalOffset y (y + siteOfCoords j h) = h := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.minimalOffset_centre_add <;> assumption
theorem card_centredCube_odd (R : ℕ) : (centredCube (2 * R + 1)).card = (2 * R + 1) ^ 4 := by apply _root_.YangMills.Construction.HoleSavings.card_centredCube_odd <;> assumption
theorem mem_centredCube_odd (R : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (2 * R + 1) ↔ ∀ i, |h i| ≤ (R : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
def ExpansionCloseOfNearFields (C₀ : ℝ) : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F F' : BlockFrame)
      (y : F.Site F.depth) (y' : F'.Site F'.depth) (U : F.GaugeField F.depth) (U' : F'.GaugeField F'.depth)
      (R : ℕ) (ε σ₁ : ℝ),
      IsRegularFamily L t n₀ σ δ E E₃ f → IsCubicTorusAbove L t n₀ F → IsCubicTorusAbove L t n₀ F' →
      0 ≤ δ → 0 ≤ E → E ≤ E₃ → 0 ≤ ε → ε ≤ 1 / 2 → σ₁ + 8 * ε < σ →
      (∀ i, 2 * R + 2 < F.period F.depth i) → (∀ i, 2 * R + 2 < F'.period F'.depth i) →
      IsSmallCurvature σ₁ U → IsSmallCurvature σ U' →
      (∀ b, BondWithinRadius R b → ‖((U (y + siteOfCoords F.depth b.1) b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((U' (y' + siteOfCoords F'.depth b.1) b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) →
      |subtractTrivial f F y U - subtractTrivial f F' y' U'| ≤
        E / torusDecayFactor L δ R + C₀ * (3 * E₃) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε))
theorem exists_expansionCloseOfNearFields (hD : DerivBoundAlongFlow) (hLog : LogNearOne)
    (hH : PathHolonomyLipschitz) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ExpansionCloseOfNearFields C₀ := by
  classical
  obtain ⟨C₀, hC₀, hDf⟩ := hD
  refine ⟨C₀, hC₀, ?_⟩
  unfold ExpansionCloseOfNearFields
  intro L t n₀ σ δ E E₃ f F F' y y' U U' R ε σ₁ hrow hT hT' hδ hE hEE hε hε2 hσ hper hper' hc hc' hnear
  haveI hz : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by have := hper i; omega⟩
  have hlog : ∀ (z : F.Site F.depth) (i : Fin 4), ∃ A : imaginaryQuaternions, ‖A‖ ≤ 2 * ε ∧
      (BondWithinRadius R (minimalOffset y z, i) →
        expUnit A * U z i = U' (y' + siteOfCoords F'.depth (minimalOffset y z)) i) ∧
      (¬ BondWithinRadius R (minimalOffset y z, i) → A = 0) := by
    intro z i
    by_cases hb : BondWithinRadius R (minimalOffset y z, i)
    · have hn := hnear (minimalOffset y z, i) hb
      simp only [add_minimalOffset] at hn
      set g : UnitQuaternion := U' (y' + siteOfCoords F'.depth (minimalOffset y z)) i * (U z i)⁻¹ with hg
      have hgap : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g ≤ ε := by
        have e : ((g : UnitQuaternion) : ℍ[ℝ]) - 1 =
            (((U' (y' + siteOfCoords F'.depth (minimalOffset y z)) i : UnitQuaternion) : ℍ[ℝ]) -
              ((U z i : UnitQuaternion) : ℍ[ℝ])) * (((U z i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          have e1 : ((U z i : UnitQuaternion) : ℍ[ℝ]) * (((U z i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
            have e2 : (U z i * (U z i)⁻¹ : UnitQuaternion) = 1 := mul_inv_cancel _
            exact congrArg Subtype.val e2
          rw [sub_mul, e1]
          rfl
        unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne
        rw [e, norm_mul, YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one, norm_sub_rev]
        exact hn
      obtain ⟨A, hA, hAn⟩ := hLog g (by linarith)
      refine ⟨A, by linarith, fun _ => ?_, fun h => absurd hb h⟩
      rw [hA, hg]
      group
    · exact ⟨0, by simp; linarith, fun h => absurd h hb, fun _ => rfl⟩
  choose B hB1 hB2 hB3 using hlog
  obtain ⟨T, hTall⟩ : ∃ T : Finset (F.Site F.depth × Fin 4), ∀ b, b ∈ T := ⟨Finset.univ, Finset.mem_univ⟩
  have hnearflow : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ z i,
      ‖((expFlow B U u z i : UnitQuaternion) : ℍ[ℝ]) - ((U z i : UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * ε :=
    fun u h0 h1 z i => expFlow_near B U (2 * ε) u hB1 h0 h1 z i
  have hcold : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B U u) := by
    intro u h0 h1 p hp
    have h2 := plaquetteDefect_le_of_near hH (expFlow B U u) U (2 * ε) (hnearflow u h0 h1) p
    have h3 := hc p hp
    linarith
  set Ux : F.GaugeField F.depth := expFlow B U 1 with hUx
  have hsame : ∀ b, BondWithinRadius R b →
      Ux (y + siteOfCoords F.depth b.1) b.2 = U' (y' + siteOfCoords F'.depth b.1) b.2 := by
    intro b hb
    have ho : minimalOffset y (y + siteOfCoords F.depth b.1) = b.1 := by
      apply minimalOffset_add
      intro i
      have h1 := hb.1 i
      have h2 := hper i
      omega
    have h3 := hB2 (y + siteOfCoords F.depth b.1) b.2 (by rw [ho]; exact hb)
    rw [ho] at h3
    rw [← h3]
    simp [hUx, expFlow, leftTranslate]
  have hagree : AgreeOnBox Ux U' y y' R := ⟨hper, hper', hsame⟩
  have hl := hrow.locality F F' hT hT' y y' Ux U' R 0 Fin.elim0 Fin.elim0 (hcold 1 zero_le_one le_rfl) hc'
    hagree (Nat.zero_le _) (fun l => l.elim0) (fun l => l.elim0)
  rw [bondDeriv_zero_order, bondDeriv_zero_order] at hl
  have hM : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site F.depth × Fin 4)
      (X : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors X → ‖bondDeriv (f F y) (expFlow B U u) c X‖ ≤ E₃ := by
    intro u h0 h1 l c X hl1 hl3 hX
    have h2 := hrow.decay F hT y (expFlow B U u) l c X (hcold u h0 h1) hl1 hl3 hX
    rw [Real.norm_eq_abs]
    refine h2.trans ?_
    have hE₃ : 0 ≤ E₃ := hE.trans hEE
    have hw := one_le_torusDecayFactor (L := L) (x := (bondSpan y c : ℝ)) hδ (Nat.cast_nonneg _)
    have hnum : (if l = 3 then E₃ else E) ≤ E₃ := by
      split_ifs
      · exact le_rfl
      · exact hEE
    have hnum0 : 0 ≤ (if l = 3 then E₃ else E) := by
      split_ifs
      · exact hE₃
      · exact hE
    exact (div_le_self hnum0 hw).trans hnum
  have hmove := hDf ℝ F F.depth T (f F y) U B (fun _ => E₃) hTall
    (fun _ => hE.trans hEE) (fun u h0 h1 => hrow.smooth F hT y _ (hcold u h0 h1)) hM 0 Fin.elim0 Fin.elim0
    (Nat.zero_le _) (fun l => l.elim0)
  rw [bondDeriv_zero_order, bondDeriv_zero_order, Real.norm_eq_abs] at hmove
  set S : Finset (F.Site F.depth × Fin 4) :=
    (centredCube (2 * R + 1) ×ˢ (Finset.univ : Finset (Fin 4))).image
      (fun q => (y + siteOfCoords F.depth q.1, q.2)) with hS
  have hsum : ∑ b ∈ T, ‖B b.1 b.2‖ ≤ 4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε) := by
    have h1 : ∑ b ∈ T, ‖B b.1 b.2‖ = ∑ b ∈ S, ‖B b.1 b.2‖ := by
      symm
      apply Finset.sum_subset (fun b _ => hTall b)
      intro b _ hb
      have : ¬ BondWithinRadius R (minimalOffset y b.1, b.2) := by
        intro hbb
        apply hb
        rw [hS, Finset.mem_image]
        refine ⟨(minimalOffset y b.1, b.2), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_univ, and_true]
          exact (mem_centredCube_odd R _).2 hbb.1
        · simp [add_minimalOffset]
      rw [hB3 b.1 b.2 this, norm_zero]
    rw [h1]
    have h2 : ∑ b ∈ S, ‖B b.1 b.2‖ ≤ S.card • (2 * ε) :=
      Finset.sum_le_card_nsmul _ _ _ (fun b _ => hB1 b.1 b.2)
    have h3 : (S.card : ℝ) ≤ 4 * (2 * (R : ℝ) + 1) ^ 4 := by
      have h4 : S.card ≤ (2 * R + 1) ^ 4 * 4 := by
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, card_centredCube_odd]
        simp
      have h5 : ((S.card : ℕ) : ℝ) ≤ (((2 * R + 1) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      linarith
    rw [nsmul_eq_mul] at h2
    have h6 : (S.card : ℝ) * (2 * ε) ≤ 4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    exact h2.trans h6
  have hcen : |subtractTrivial f F y U - subtractTrivial f F y Ux| ≤
      C₀ * (3 * E₃) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε)) := by
    have e : subtractTrivial f F y U - subtractTrivial f F y Ux = -(f F y (expFlow B U 1) - f F y U) := by
      simp only [subtractTrivial, hUx]
      ring
    rw [e, abs_neg]
    refine hmove.trans ?_
    have hc3 : 0 ≤ C₀ * (E₃ + E₃ + E₃) := mul_nonneg hC₀ (by linarith)
    have := mul_le_mul_of_nonneg_left hsum hc3
    calc C₀ * (E₃ + E₃ + E₃) * ∑ b ∈ T, ‖B b.1 b.2‖
        ≤ C₀ * (E₃ + E₃ + E₃) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε)) := this
      _ = C₀ * (3 * E₃) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε)) := by ring
  have htri : |subtractTrivial f F y U - subtractTrivial f F' y' U'| ≤
      |subtractTrivial f F y U - subtractTrivial f F y Ux| + |subtractTrivial f F y Ux - subtractTrivial f F' y' U'| :=
    abs_sub_le _ _ _
  linarith
abbrev LatticeOffset : Type := Fin 4 → ℤ
def siteAtOffset (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + siteOfCoords F.depth p
def WithinBlockRadius (L r : ℕ) (p : LatticeOffset) : Prop := ∀ i, |p i| ≤ (L : ℤ) * r + halfSide L
theorem exists_block_decomposition {L : ℕ} (hL : Odd L) (p : LatticeOffset) :
    ∃ g q : LatticeOffset, q ∈ centredCube L ∧ ∀ i, p i = (L : ℤ) * g i + q i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.exists_block_decomposition <;> assumption
theorem abs_le_of_withinBlockRadius {L : ℕ} (hL : Odd L) {r : ℕ} {x g q : ℤ} (hx : x = L * g + q)
    (hq1 : -halfSide L ≤ q) (hq2 : q ≤ halfSide L) (hn : |x| ≤ (L : ℤ) * r + halfSide L) :
    |g| ≤ (r : ℤ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.abs_quotient_le_of_nearBox <;> assumption
theorem siteAtOffset_decomp (Y : F.Cell) (g q : LatticeOffset) :
    siteAtOffset Y (fun i => (F.blockSide : ℤ) * g i + q i) =
      cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.siteAtOffset_blockSplit <;> assumption
theorem mem_sitesOfCells_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4) (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) :
    fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.fineBondAt_mem_chordBonds <;> assumption
theorem not_isAxialTreeBond_of_mem_chordBonds {b : F.Site F.depth × Fin 4}
    (h : b ∈ chordBonds (finiteCells F)) : ¬ IsAxialTreeBond b := by
  simp only [chordBonds, Finset.mem_filter] at h
  exact h.2
theorem isAxialTreeBond_fineBondAt_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (hq : q ∈ centredCube F.blockSide) (j : Fin 4) :
    IsAxialTreeBond (fineBondAt Y g q j) ↔ (q j ≠ halfSide F.blockSide ∧ ∀ l, j < l → q l = 0) := by
  have c1 := isCrossingBond_iff hL hs (Y + siteOfCoords F.top g) q hq j
  have o1 := cellOffset_offset hL hs (Y + siteOfCoords F.top g) q hq
  constructor
  · intro h
    refine ⟨fun hc => h.1 (c1.2 hc), fun l hl => ?_⟩
    have := h.2 l hl
    simp only [fineBondAt] at this
    rwa [o1] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun hc => h1 (c1.1 hc), fun l hl => ?_⟩
    simp only [fineBondAt]
    rw [o1]
    exact h2 l hl
theorem withinRadius_add_single {L r : ℕ} (hL : Odd L) {p g q : LatticeOffset} {j : Fin 4}
    (hp : ∀ i, p i = (L : ℤ) * g i + q i) (hq : q ∈ centredCube L) (hg : WithinRadius r g)
    (hp' : WithinBlockRadius L r (p + Pi.single j 1)) (hqj : q j = halfSide L) :
    WithinRadius r (g + Pi.single j 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.withinRadius_add_single <;> assumption
theorem expUnit_near (hE : QuaternionExp.ExpUnitLipschitzInjective) (A A' : imaginaryQuaternions) :
    ‖((expUnit A : UnitQuaternion) : ℍ[ℝ]) - ((expUnit A' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(A : ℍ[ℝ]) - (A' : ℍ[ℝ])‖ := by
  have := hE.1 A A'
  simpa using this
theorem expUnit_mul_near (hE : QuaternionExp.ExpUnitLipschitzInjective) (A A' : imaginaryQuaternions)
    (v : UnitQuaternion) :
    ‖((expUnit A * v : UnitQuaternion) : ℍ[ℝ]) - ((expUnit A' * v : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(A : ℍ[ℝ]) - (A' : ℍ[ℝ])‖ := by
  have e : ((expUnit A * v : UnitQuaternion) : ℍ[ℝ]) - ((expUnit A' * v : UnitQuaternion) : ℍ[ℝ]) =
      (((expUnit A : UnitQuaternion) : ℍ[ℝ]) - ((expUnit A' : UnitQuaternion) : ℍ[ℝ])) *
        ((v : UnitQuaternion) : ℍ[ℝ]) := by
    rw [sub_mul]
    rfl
  rw [e, norm_mul, YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one]
  exact expUnit_near hE A A'
theorem chartedField_near (hE : QuaternionExp.ExpUnitLipschitzInjective) {L r : ℕ} (hF : F.blockSide = L)
    (hF' : F'.blockSide = L) (hL : Odd L) (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {ε : ℝ} (hε : 0 ≤ ε)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
      ‖((w (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε)
    (p : LatticeOffset) (j : Fin 4) (hp : WithinBlockRadius L r p)
    (hp' : WithinBlockRadius L r (p + Pi.single j 1)) :
    ‖((chartedField w V (siteAtOffset Y p) j : UnitQuaternion) : ℍ[ℝ]) -
      ((chartedField w' V' (siteAtOffset Y' p) j : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  obtain ⟨g, q, hq, hpq⟩ := exists_block_decomposition hL p
  have hg : WithinRadius r g := by
    intro i
    have := (YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff q).1 hq i
    exact abs_le_of_withinBlockRadius hL (hpq i) this.1 this.2 (hp i)
  have hpe : p = fun i => (L : ℤ) * g i + q i := funext hpq
  have hx : siteAtOffset Y p = cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by
    rw [hpe, ← hF]
    exact siteAtOffset_decomp Y g q
  have hx' : siteAtOffset Y' p =
      cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q := by
    rw [hpe, ← hF']
    exact siteAtOffset_decomp Y' g q
  have hqF : q ∈ centredCube F.blockSide := by rw [hF]; exact hq
  have hqF' : q ∈ centredCube F'.blockSide := by rw [hF']; exact hq
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hL
  rw [hx, hx']
  have c1 := isCrossingBond_iff hLF hs (Y + siteOfCoords F.top g) q hqF j
  have c2 := isCrossingBond_iff hLF' hs' (Y' + siteOfCoords F'.top g) q hqF' j
  rw [hF] at c1
  rw [hF'] at c2
  have t1 := isAxialTreeBond_fineBondAt_iff hLF hs Y g q hqF j
  have t2 := isAxialTreeBond_fineBondAt_iff hLF' hs' Y' g q hqF' j
  rw [hF] at t1
  rw [hF'] at t2
  have e1 := enclosingCell_offset hLF hs (Y + siteOfCoords F.top g) q hqF
  have e2 := enclosingCell_offset hLF' hs' (Y' + siteOfCoords F'.top g) q hqF'
  have hwq : ¬ IsAxialTreeBond (fineBondAt Y g q j) →
      ‖((w (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε :=
    fun ht => hw g q j hg hq (fineBondAt_mem_chordBonds hLF hs Y g q j ht)
  simp only [fineBondAt] at hwq t1 t2
  unfold chartedField
  by_cases hc : q j = halfSide L
  · rw [if_pos (c1.2 hc), if_pos (c2.2 hc), e1, e2]
    have := hV (g, j) ⟨hg, withinRadius_add_single hL hpq hq hg hp' hc⟩
    simp only at this
    rw [this]
    exact (expUnit_mul_near hE _ _ _).trans (hwq (fun ht => (t1.1 ht).1 hc))
  · have n1 : ¬ IsCrossingBond
        ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q : F.Site F.depth), j) :=
      fun h => hc (c1.1 h)
    have n2 : ¬ IsCrossingBond
        ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q : F'.Site F'.depth), j) :=
      fun h => hc (c2.1 h)
    rw [if_neg n1, if_neg n2]
    by_cases ht : ∀ l, j < l → q l = 0
    · rw [if_pos (t1.2 ⟨hc, ht⟩), if_pos (t2.2 ⟨hc, ht⟩)]
      simpa using hε
    · have u1 : ¬ IsAxialTreeBond
          ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q : F.Site F.depth), j) :=
        fun h => ht (t1.1 h).2
      have u2 : ¬ IsAxialTreeBond
          ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q : F'.Site F'.depth), j) :=
        fun h => ht (t2.1 h).2
      rw [if_neg u1, if_neg u2]
      exact (expUnit_near hE _ _).trans (hwq u1)
theorem cellSupDist_add_le {n R : ℕ} (hs : ∀ i, F.extent i = n) (hR : 2 * R < n) (Y : F.Cell)
    (g : LatticeOffset) (hg : ∀ i, |g i| ≤ (R : ℤ)) : cellSupDist Y (Y + siteOfCoords F.top g) ≤ R := by
  unfold cellSupDist
  apply Finset.sup_le
  intro i _
  haveI : NeZero (F.period F.top i) := ⟨by rw [period_top, hs]; omega⟩
  have e : (Y i - (Y + siteOfCoords F.top g : F.Cell) i : ZMod (F.period F.top i)) =
      ((- g i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have h1 := hg i
  have h2 := abs_le.mp h1
  have e2 : ((Y i - (Y + siteOfCoords F.top g : F.Cell) i : ZMod (F.period F.top i))).valMinAbs = - g i := by
    rw [e, ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    rw [period_top, hs]
    constructor <;> omega
  rw [e2]
  omega
theorem zeroExtensionL_apply_self {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι] (e : Λ → ι)
    (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) : zeroExtensionL e ζ (e l) = ζ l := by apply _root_.YangMills.SharedProofs.p32108 <;> assumption
theorem norm_zeroExtensionL_le {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι] (e : Λ → ι)
    (ζ : BondField Λ) {s : ℝ} (hs : 0 ≤ s) (hζ : ∀ l, ‖ζ l‖ < s) (b : ι) : ‖zeroExtensionL e ζ b‖ ≤ s := by
  by_cases hx : ∃ l, e l = b
  · simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_pos hx, ContinuousLinearMap.proj_apply]
    exact (hζ _).le
  · simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_neg hx, zero_apply, norm_zero]
    exact hs
theorem fieldAboveFrame_smallCurvature (hMv : ChartShiftLipschitz) (hodd : Odd F.blockSide) {star : Bool}
    {a ρA δ₂ κ₂ Cb σ : ℝ} {Kk : ℕ → ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hsm : FrameSmallness star a ρA δ₂ κ₂ Cb σ Kk m V) (hσ : 0 < σ) (η : StepVariable (finiteCells F))
    (hη : ∀ b, ‖η b‖ ≤ σ / 64) : IsSmallCurvature (45 / 64 * σ) (fieldAboveFrame star a ρA m V η) := by
  intro p hp
  have h1 := hsm.small_curvature p hp
  have h2 := (hMv F V (frameCoordField star a ρA m V) η (σ / 64) hodd hη (by positivity)).2.1 p
  have h3 : (if star then (5 / 8 : ℝ) else 41 / 64) * σ ≤ 41 / 64 * σ := by
    split_ifs
    · nlinarith
    · exact le_rfl
  have h4 : plaquetteDefect (fieldAboveFrame star a ρA m V η) p ≤
      plaquetteDefect (chartedField (frameCoordField star a ρA m V) V) p + 4 * (σ / 64) := h2
  linarith
theorem siteAtOffset_shift {L : ℕ} (hF : F.blockSide = L) (Y : F.Cell) (c o e : LatticeOffset) :
    (cellCentre F.depth (Y + siteOfCoords F.top c) + siteOfCoords F.depth o + siteOfCoords F.depth e :
        F.Site F.depth) =
      siteAtOffset Y (fun i => (L : ℤ) * c i + o i + e i) := by
  rw [← siteAtOffset_decomp, hF]
  unfold siteAtOffset
  rw [add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
  rfl
theorem withinBlockRadius_of_cube {L P Q : ℕ} {c o e : LatticeOffset} (hc : c ∈ centredCube (2 * Q + 1))
    (ho : o ∈ centredCube L) (he : ∀ i, |e i| ≤ (L : ℤ) * Q) (hPQ : 2 * Q ≤ P) :
    WithinBlockRadius L P (fun i => (L : ℤ) * c i + o i + e i) := by
  intro i
  have h1 := (mem_centredCube_odd Q c).1 hc i
  have h2 := (YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff o).1 ho i
  have h3 := he i
  have hL0 : (0 : ℤ) ≤ L := Int.natCast_nonneg L
  have h4 : (L : ℤ) * |c i| ≤ L * Q := mul_le_mul_of_nonneg_left h1 hL0
  have h5 : (L : ℤ) * (2 * Q) ≤ L * P := mul_le_mul_of_nonneg_left (by exact_mod_cast hPQ) hL0
  have h6 : |(L : ℤ) * c i + o i + e i| ≤ |(L : ℤ) * c i| + |o i| + |e i| := abs_add_three _ _ _
  rw [abs_mul, abs_of_nonneg hL0] at h6
  have h7 : |o i| ≤ halfSide L := abs_le.2 h2
  simp only
  nlinarith
theorem stepCoordinates_chord (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.stepCoordinates_of_chordBond <;> assumption
theorem coordsAboveFrame_near (hS : SiteDecomposition) {L : ℕ} {σ a ρA δ₂ C : ℝ} {m r n : ℕ}
    {F F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    {star : Bool} (hFL : F.blockSide = L) (hFL' : F'.blockSide = L) (hL : Odd L) (hn : ∀ i, F.extent i = n)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) (hnr : 2 * r + 2 < n)
    (hloc : FrameLocality star a ρA δ₂ C σ m V V' Y Y' r)
    (hσ : 0 < σ) (hC : 0 ≤ C) (hδ₂ : 0 < δ₂) (hr : 16 ≤ r)
    (ζ : BondField ↥(commonBondOffsets Y Y' (r / 2)))
    (η : StepVariable (finiteCells F)) (η' : StepVariable (finiteCells F'))
    (hat : ∀ l, η (commonBondLeft Y Y' (r / 2) l) = ζ l)
    (hat' : ∀ l, η' (commonBondRight Y Y' (r / 2) l) = ζ l)
    (g q : LatticeOffset) (j : Fin 4) (hg : WithinRadius (r / 2) g) (hq : q ∈ centredCube L)
    (hb : fineBondAt Y g q j ∈ chordBonds (finiteCells F)) :
    ‖((coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      C * σ * Real.exp (-(δ₂ / 8 * r)) := by
  have hLF : Odd F.blockSide := by rw [hFL]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hL
  have hqF : q ∈ centredCube F.blockSide := by rw [hFL]; exact hq
  have hqF' : q ∈ centredCube F'.blockSide := by rw [hFL']; exact hq
  have hgc : g ∈ centredCube (2 * (r / 2) + 1) := (mem_centredCube_odd _ _).2 hg
  have hb' : fineBondAt Y' g q j ∈ chordBonds (finiteCells F') := by
    apply fineBondAt_mem_chordBonds hLF' hs'
    rw [isAxialTreeBond_fineBondAt_iff hLF' hs' Y' g q hqF' j, hFL']
    intro ht
    apply not_isAxialTreeBond_of_mem_chordBonds hb
    rw [isAxialTreeBond_fineBondAt_iff hLF hs Y g q hqF j, hFL]
    exact ht
  have hmem : (g, q, j) ∈ commonBondOffsets Y Y' (r / 2) := by
    unfold commonBondOffsets
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hgc, hqF⟩, hb, hb'⟩
  have e1 : stepCoordinates η (fineBondAt Y g q j).1 j = toImaginary (ζ ⟨(g, q, j), hmem⟩) := by
    have h1 := stepCoordinates_chord η (commonBondLeft Y Y' (r / 2) ⟨(g, q, j), hmem⟩)
    rw [hat] at h1
    exact h1
  have e2 : stepCoordinates η' (fineBondAt Y' g q j).1 j = toImaginary (ζ ⟨(g, q, j), hmem⟩) := by
    have h1 := stepCoordinates_chord η' (commonBondRight Y Y' (r / 2) ⟨(g, q, j), hmem⟩)
    rw [hat'] at h1
    exact h1
  have hcell : enclosingCell (fineBondAt Y g q j).1 = Y + siteOfCoords F.top g :=
    enclosingCell_offset hLF hs _ q hqF
  have hdist : cellSupDist Y (Y + siteOfCoords F.top g) ≤ r / 2 :=
    cellSupDist_add_le hn (by omega) Y g hg
  have hbox : WithinRadius r g := fun i => (hg i).trans (by exact_mod_cast Nat.div_le_self r 2)
  have hd1 : cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) ≤ r := by
    rw [hcell]
    exact hdist.trans (Nat.div_le_self r 2)
  have hd2 : cellSupDist Y (enclosingCell ((fineBondAt Y g q j).1 + unitStep F.depth j)) ≤ r := by
    rcases (hS F hLF hs).2.2.2 (fineBondAt Y g q j).1 j with h | h
    · rw [h]
      exact hd1
    · rw [h, hcell]
      have e : (Y + siteOfCoords F.top g + unitStep F.top j : F.Cell) =
          Y + siteOfCoords F.top (g + Pi.single j 1) := by
        rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
        rfl
      rw [e]
      refine (cellSupDist_add_le (R := r / 2 + 1) hn (by omega) Y _ ?_).trans (by omega)
      intro i
      have h1 := hg i
      have h2 : |(Pi.single j 1 : Fin 4 → ℤ) i| ≤ 1 := by
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Pi.single_eq_of_ne hij]
      have h3 := abs_add_le (g i) ((Pi.single j 1 : Fin 4 → ℤ) i)
      simp only [Pi.add_apply]
      push_cast
      omega
  have hval := hloc.value g q j ⟨hqF, hb, hbox, hd1, hd2⟩
  have e3 : ((coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) =
      (stepFrame star a ρA m (fineBondAt Y g q j) V : ℍ[ℝ]) -
        (stepFrame star a ρA m (fineBondAt Y' g q j) V' : ℍ[ℝ]) := by
    have h1 : coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j =
        stepFrame star a ρA m (fineBondAt Y g q j) V + stepCoordinates η (fineBondAt Y g q j).1 j := rfl
    have h2 : coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j =
        stepFrame star a ρA m (fineBondAt Y' g q j) V' + stepCoordinates η' (fineBondAt Y' g q j).1 j := rfl
    rw [h1, h2, e1, e2, Submodule.coe_add, Submodule.coe_add]
    abel
  rw [e3]
  refine hval.trans ?_
  rw [hcell]
  have hCσ : 0 ≤ C * σ := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCσ
  have h4 : ((cellSupDist Y (Y + siteOfCoords F.top g) : ℕ) : ℝ) ≤ (r : ℝ) / 2 :=
    ((Nat.cast_le.2 hdist).trans Nat.cast_div_le).trans (by norm_num)
  nlinarith
theorem centredExpansion_close_at_site (hS : SiteDecomposition) (hE : QuaternionExp.ExpUnitLipschitzInjective)
    (hMv : ChartShiftLipschitz)
    {C₀ : ℝ} (hC₀ : ExpansionCloseOfNearFields C₀) {L t n₀ : ℕ} {σ δ E E₃ a ρA δ₂ κ₂ Cb Cb' C : ℝ} {Kk : ℕ → ℝ}
    {m r : ℕ} {f : LocalFamily} {F F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell}
    {star : Bool} (hrow : IsRegularFamily L t n₀ σ δ E E₃ f) (hL : Odd L) (h64 : 64 ≤ n₀)
    (hT : IsCubicTopTorus L t n₀ F) (hT' : IsCubicTopTorus L t n₀ F')
    (hsm : FrameSmallness star a ρA δ₂ κ₂ Cb σ Kk m V) (hsm' : FrameSmallness star a ρA δ₂ κ₂ Cb' σ Kk m V')
    (hloc : FrameLocality star a ρA δ₂ C σ m V V' Y Y' r)
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 ≤ δ) (hE0 : 0 ≤ E) (hEE : E ≤ E₃) (hC : 0 ≤ C) (hδ₂ : 0 < δ₂)
    (hsmall : C * Real.exp (-(δ₂ / 8 * r)) ≤ 1 / 64) (hr : 16 ≤ r)
    (c o : LatticeOffset) (hc : c ∈ centredCube (2 * (r / 8) + 1)) (ho : o ∈ centredCube L)
    (ζ : BondField ↥(commonBondOffsets Y Y' (r / 2)))
    (η : StepVariable (finiteCells F)) (η' : StepVariable (finiteCells F'))
    (hat : ∀ l, η (commonBondLeft Y Y' (r / 2) l) = ζ l)
    (hat' : ∀ l, η' (commonBondRight Y Y' (r / 2) l) = ζ l)
    (hηs : ∀ b, ‖η b‖ ≤ σ / 64) (hηs' : ∀ b, ‖η' b‖ ≤ σ / 64) :
    |centredExpansion star a ρA m f (cellCentre F.depth (Y + siteOfCoords F.top c) + siteOfCoords F.depth o) η V -
      centredExpansion star a ρA m f (cellCentre F'.depth (Y' + siteOfCoords F'.top c) + siteOfCoords F'.depth o) η' V'| ≤
      E / torusDecayFactor L δ ((L * (r / 8) : ℕ) : ℝ) + C₀ * (3 * E₃) *
        (4 * (2 * (((L * (r / 8) : ℕ) : ℝ)) + 1) ^ 4 * (2 * (C * σ * Real.exp (-(δ₂ / 8 * r))))) := by
  obtain ⟨hFL, hFt, n, hn, hn₀⟩ := hT
  obtain ⟨hFL', hFt', n', hn', hn₀'⟩ := hT'
  obtain ⟨hd, hd', -, hV⟩ := hag
  have hnr : 2 * r + 2 < n := by
    rcases hd 0 with h | h
    · rw [hn] at h
      omega
    · rwa [hn] at h
  have hnr' : 2 * r + 2 < n' := by
    rcases hd' 0 with h | h
    · rw [hn'] at h
      omega
    · rwa [hn'] at h
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hn']; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hL
  obtain ⟨ε, hεd⟩ : ∃ ε, ε = C * σ * Real.exp (-(δ₂ / 8 * r)) := ⟨_, rfl⟩
  rw [← hεd]
  have hε0 : 0 ≤ ε := by rw [hεd]; positivity
  have hε64 : ε ≤ σ / 64 := by
    have : ε = σ * (C * Real.exp (-(δ₂ / 8 * r))) := by rw [hεd]; ring
    rw [this]
    nlinarith
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = L * (r / 8) := ⟨_, rfl⟩
  rw [← hR]
  have hLpos : 0 < L := hL.pos
  have hper : ∀ i, 2 * R + 2 < F.period F.depth i := by
    intro i
    rw [period_depth, hn, hFL, hR]
    have h1 : (2 * (r / 8) + 3) * L ≤ n * L := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hper' : ∀ i, 2 * R + 2 < F'.period F'.depth i := by
    intro i
    rw [period_depth, hn', hFL', hR]
    have h1 : (2 * (r / 8) + 3) * L ≤ n' * L := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hVr : ∀ b, BondWithinRadius (r / 2) b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2 := by
    intro b hb
    refine hV b ⟨fun i => (hb.1 i).trans ?_, fun i => (hb.2 i).trans ?_⟩ <;> exact_mod_cast Nat.div_le_self r 2
  have hw := fun g q j hg hq hb => hεd ▸ coordsAboveFrame_near (star := star) (a := a) (ρA := ρA) (m := m)
    hS hFL hFL' hL hn hs hs' hnr hloc hσ hC hδ₂ hr ζ η η' hat hat' g q j hg hq hb
  have hnearb : ∀ b : (Fin 4 → ℤ) × Fin 4, BondWithinRadius R b →
      ‖((fieldAboveFrame star a ρA m V η (cellCentre F.depth (Y + siteOfCoords F.top c) + siteOfCoords F.depth o +
          siteOfCoords F.depth b.1) b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((fieldAboveFrame star a ρA m V' η' (cellCentre F'.depth (Y' + siteOfCoords F'.top c) +
          siteOfCoords F'.depth o + siteOfCoords F'.depth b.1) b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
    intro b hb
    rw [siteAtOffset_shift hFL, siteAtOffset_shift hFL']
    have hPQ : 2 * (r / 8) ≤ r / 2 := by omega
    have hb1 : ∀ i, |b.1 i| ≤ (L : ℤ) * ((r / 8 : ℕ) : ℤ) := fun i => by
      have := hb.1 i
      rw [hR] at this
      exact_mod_cast this
    have hb2 : ∀ i, |(b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (L : ℤ) * ((r / 8 : ℕ) : ℤ) := fun i => by
      have := hb.2 i
      rw [hR] at this
      exact_mod_cast this
    refine chartedField_near hE hFL hFL' hL hs hs' hε0 hVr hw _ b.2 (withinBlockRadius_of_cube hc ho hb1 hPQ) ?_
    have := withinBlockRadius_of_cube (e := b.1 + Pi.single b.2 1) hc ho hb2 hPQ
    intro i
    have h1 := this i
    simp only [Pi.add_apply] at h1 ⊢
    rwa [add_assoc]
  exact hC₀ L t n₀ σ δ E E₃ f F F' _ _ _ _ R ε (45 / 64 * σ) hrow
    ⟨hFL, hFt, n, hn, hn₀.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
    ⟨hFL', hFt', n', hn', hn₀'.trans (Nat.le_mul_of_pos_right _ hLpos)⟩ hδ hE0 hEE hε0 (by linarith) (by linarith)
    hper hper' (fieldAboveFrame_smallCurvature hMv hLF hsm hσ η hηs)
    (fun p hp => (fieldAboveFrame_smallCurvature hMv hLF' hsm' hσ η' hηs' p hp).trans (by nlinarith)) hnearb
theorem sum_sites_of_cell (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Z : F.Cell) (G : F.Site F.depth → ℝ) [DecidablePred fun y : F.Site F.depth => enclosingCell y = Z] :
    ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Z), G y =
      ∑ o ∈ centredCube F.blockSide, G (cellCentre F.depth Z + siteOfCoords F.depth o) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.sum_cell_sites <;> assumption
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem exists_radius_floor {C δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    ∃ N : ℕ, 16 ≤ N ∧ ∀ r : ℕ, N ≤ r → C * Real.exp (-(δ₂ / 8 * r)) ≤ 1 / 64 := by
  refine ⟨max 16 ⌈512 * C / δ₂⌉₊, le_max_left _ _, fun r hr => ?_⟩
  have h1 : 512 * C / δ₂ ≤ r := by
    have h2 : (⌈512 * C / δ₂⌉₊ : ℝ) ≤ r := by exact_mod_cast (le_max_right _ _).trans hr
    exact (Nat.le_ceil _).trans h2
  have h3 : 64 * C ≤ δ₂ / 8 * r := by
    rw [div_le_iff₀ hδ₂] at h1
    nlinarith
  have h4 : 64 * C ≤ Real.exp (δ₂ / 8 * r) := by
    have := Real.add_one_le_exp (δ₂ / 8 * (r : ℝ))
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith
theorem final_bound {L r : ℕ} {C₀ C σ δ₂ κ E E₃ Ct : ℝ} (hL : 2 ^ 15 ≤ L) (hr : 16 ≤ r) (hκ : 0 < κ)
    (hκ₂ : κ ≤ δ₂ / 2 ^ 14) (hδ₂ : 0 < δ₂) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hE : 0 ≤ E) (hEE : E ≤ E₃)
    (hCt : 8 * ((L : ℝ) ^ 4 + 576 * C₀ * C * (16 / δ₂) ^ 4 * (L : ℝ) ^ 8) ≤ Ct) :
    (L : ℝ) ^ 4 * (E / torusDecayFactor L (κ / 2 ^ 10) ((L * (r / 8) : ℕ) : ℝ) + C₀ * (3 * E₃) *
        (4 * (2 * (((L * (r / 8) : ℕ) : ℝ)) + 1) ^ 4 * (2 * (C * σ * Real.exp (-(δ₂ / 8 * r)))))) ≤
      Ct * (1 + E₃) / 4 * Real.exp (-(2 * κ * r)) := by
  have hLr : (2 : ℝ) ^ 15 ≤ L := by exact_mod_cast hL
  have hr16 : (16 : ℝ) ≤ r := by exact_mod_cast hr
  have hR1 : (r : ℝ) ≤ 16 * ((r / 8 : ℕ) : ℝ) := by
    have : r ≤ 16 * (r / 8) := by omega
    exact_mod_cast this
  have hR2 : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / 8 := by
    have h0 : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / ((8 : ℕ) : ℝ) := Nat.cast_div_le
    simpa using h0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((L * (r / 8) : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hR]
  have hRe : R = (L : ℝ) * ((r / 8 : ℕ) : ℝ) := by rw [hR]; push_cast; ring
  have hRlow : 2 ^ 11 * (r : ℝ) ≤ R := by
    rw [hRe]
    have h0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hRhigh : R ≤ (L : ℝ) * r / 8 := by
    rw [hRe]
    nlinarith
  have hR0 : 0 ≤ R := by rw [hRe]; positivity
  obtain ⟨q, hqd⟩ : ∃ q, q = Real.exp (-(2 * κ * r)) := ⟨_, rfl⟩
  rw [← hqd]
  have hq : 0 < q := by rw [hqd]; exact Real.exp_pos _
  have hE₃ : 0 ≤ E₃ := hE.trans hEE
  have hA : E / torusDecayFactor L (κ / 2 ^ 10) R ≤ E * q := by
    have h1 : Real.exp (κ / 2 ^ 10 * R) ≤ torusDecayFactor L (κ / 2 ^ 10) R := exp_le_torusDecayFactor
    have h2 : 2 * κ * r ≤ κ / 2 ^ 10 * R := by nlinarith
    have h3 : Real.exp (2 * κ * r) ≤ torusDecayFactor L (κ / 2 ^ 10) R := (Real.exp_le_exp.2 h2).trans h1
    have h4 : E / torusDecayFactor L (κ / 2 ^ 10) R ≤ E / Real.exp (2 * κ * r) :=
      div_le_div_of_nonneg_left hE (Real.exp_pos _) h3
    refine h4.trans (le_of_eq ?_)
    rw [hqd, Real.exp_neg, div_eq_mul_inv]
  obtain ⟨M, hM⟩ : ∃ M, M = (16 / δ₂) ^ 4 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨e, hed⟩ : ∃ e, e = Real.exp (-(δ₂ / 8 * r)) := ⟨_, rfl⟩
  rw [← hed]
  have he0 : 0 < e := by rw [hed]; exact Real.exp_pos _
  have hB : (2 * R + 1) ^ 4 ≤ (L : ℝ) ^ 4 * (r : ℝ) ^ 4 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith) ?_ 4
    have : (2 : ℝ) ^ 15 * 16 ≤ (L : ℝ) * r := by nlinarith
    linarith [show (2 : ℝ) ^ 15 * 16 = 524288 by norm_num]
  have hP : (r : ℝ) ^ 4 ≤ 24 * M * Real.exp (δ₂ / 16 * r) := by
    have h1 := Real.pow_div_factorial_le_exp (δ₂ / 16 * (r : ℝ)) (by positivity) 4
    have h2 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h2, div_le_iff₀ (by norm_num)] at h1
    have h3 : (r : ℝ) ^ 4 = M * (δ₂ / 16 * r) ^ 4 := by
      rw [hM, ← mul_pow]
      congr 1
      field_simp
    rw [h3]
    nlinarith
  have hD : Real.exp (δ₂ / 16 * r) * e ≤ q := by
    rw [hed, hqd, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : 2 * κ ≤ δ₂ / 16 := by
      have : δ₂ / 2 ^ 14 ≤ δ₂ / 2 ^ 5 := by
        apply div_le_div_of_nonneg_left hδ₂.le <;> norm_num
      linarith [show δ₂ / 2 ^ 5 * 2 = δ₂ / 16 by ring]
    nlinarith
  have hs1 : (2 * R + 1) ^ 4 * e ≤ (L : ℝ) ^ 4 * (24 * M * q) := by
    have h1 : (2 * R + 1) ^ 4 * e ≤ (L : ℝ) ^ 4 * (r : ℝ) ^ 4 * e :=
      mul_le_mul_of_nonneg_right hB he0.le
    have h2 : (L : ℝ) ^ 4 * (r : ℝ) ^ 4 * e ≤ (L : ℝ) ^ 4 * (24 * M * Real.exp (δ₂ / 16 * r)) * e := by
      apply mul_le_mul_of_nonneg_right _ he0.le
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    have h3 : (L : ℝ) ^ 4 * (24 * M * Real.exp (δ₂ / 16 * r)) * e =
        (L : ℝ) ^ 4 * (24 * M) * (Real.exp (δ₂ / 16 * r) * e) := by ring
    have h4 : (L : ℝ) ^ 4 * (24 * M) * (Real.exp (δ₂ / 16 * r) * e) ≤ (L : ℝ) ^ 4 * (24 * M) * q :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h5 : (L : ℝ) ^ 4 * (24 * M) * q = (L : ℝ) ^ 4 * (24 * M * q) := by ring
    linarith
  have hT2 : C₀ * (3 * E₃) * (4 * (2 * R + 1) ^ 4 * (2 * (C * σ * e))) ≤
      576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q := by
    have h1 : C₀ * (3 * E₃) * (4 * (2 * R + 1) ^ 4 * (2 * (C * σ * e))) =
        24 * C₀ * C * σ * E₃ * ((2 * R + 1) ^ 4 * e) := by ring
    have h2 : 24 * C₀ * C * σ * E₃ * ((2 * R + 1) ^ 4 * e) ≤
        24 * C₀ * C * σ * E₃ * ((L : ℝ) ^ 4 * (24 * M * q)) :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have h3 : 24 * C₀ * C * σ * E₃ * ((L : ℝ) ^ 4 * (24 * M * q)) =
        σ * (576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q) := by ring
    have h4 : 0 ≤ 576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q := by positivity
    have h5 : σ * (576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q) ≤
        1 * (576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q) := mul_le_mul_of_nonneg_right hσ1 h4
    linarith
  have hsum : E / torusDecayFactor L (κ / 2 ^ 10) R + C₀ * (3 * E₃) * (4 * (2 * R + 1) ^ 4 * (2 * (C * σ * e))) ≤
      E₃ * q + 576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q := by
    have : E * q ≤ E₃ * q := mul_le_mul_of_nonneg_right hEE hq.le
    linarith
  have hL4 : (0 : ℝ) ≤ (L : ℝ) ^ 4 := by positivity
  have h6 := mul_le_mul_of_nonneg_left hsum hL4
  refine h6.trans ?_
  rw [← hM] at hCt
  have hCt0 : 0 ≤ Ct := by
    refine le_trans ?_ hCt
    positivity
  have e7 : (L : ℝ) ^ 4 * (E₃ * q + 576 * C₀ * C * M * E₃ * (L : ℝ) ^ 4 * q) =
      E₃ * q * ((L : ℝ) ^ 4 + 576 * C₀ * C * M * (L : ℝ) ^ 8) := by ring
  rw [e7]
  have h8 : E₃ * q * ((L : ℝ) ^ 4 + 576 * C₀ * C * M * (L : ℝ) ^ 8) ≤ E₃ * q * (Ct / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h9 : E₃ * q * (Ct / 8) ≤ Ct * (1 + E₃) / 4 * q := by
    have : 0 ≤ Ct * q := by positivity
    have := mul_nonneg hE₃ this
    linarith
  linarith
theorem nearCellsClose_of_params (hS : SiteDecomposition) (hE : QuaternionExp.ExpUnitLipschitzInjective)
    (hMv : ChartShiftLipschitz) (hCB : commonBondsOfTwoTori)
    {C₀ : ℝ} (hC₀ : ExpansionCloseOfNearFields C₀) {L t n₀ : ℕ} {σ δ E E₃ a ρA δ₂ κ₂ Cb Cb' C x κ ε : ℝ}
    {Kk : ℕ → ℝ} {m r : ℕ} {f : LocalFamily} {F F' : BlockFrame} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell}
    {Y' : F'.Cell} {star : Bool} (hrow : IsRegularFamily L t n₀ σ δ E E₃ f) (hL : Odd L) (h64 : 64 ≤ n₀)
    (hT : IsCubicTopTorus L t n₀ F) (hT' : IsCubicTopTorus L t n₀ F')
    (hsm : FrameSmallness star a ρA δ₂ κ₂ Cb σ Kk m V) (hsm' : FrameSmallness star a ρA δ₂ κ₂ Cb' σ Kk m V')
    (hloc : FrameLocality star a ρA δ₂ C σ m V V' Y Y' r)
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 ≤ δ) (hE0 : 0 ≤ E) (hEE : E ≤ E₃) (hC : 0 ≤ C) (hδ₂ : 0 < δ₂)
    (hsmall : C * Real.exp (-(δ₂ / 8 * r)) ≤ 1 / 64) (hr : 16 ≤ r) (hx : 0 ≤ x) (hε : 0 ≤ ε)
    (hnum : (L : ℝ) ^ 4 * (E / torusDecayFactor L δ ((L * (r / 8) : ℕ) : ℝ) + C₀ * (3 * E₃) *
        (4 * (2 * (((L * (r / 8) : ℕ) : ℝ)) + 1) ^ 4 * (2 * (C * σ * Real.exp (-(δ₂ / 8 * r)))))) ≤ ε) :
    NearCellsClose (σ / 64) x κ ε Y Y' r
      (fun Z η => cellCentredExpansion star a ρA m f Z η V)
      (fun Z η => cellCentredExpansion star a ρA m f Z η V') := by
  intro c ζ hζ
  have hT₀ := hT
  have hT₀' := hT'
  obtain ⟨hFL, hFt, n, hn, hn₀⟩ := hT
  obtain ⟨hFL', hFt', n', hn', hn₀'⟩ := hT'
  have hag₀ := hag
  obtain ⟨hd, hd', -, -⟩ := hag
  have hnr : 2 * r + 2 < n := by
    rcases hd 0 with h | h
    · rw [hn] at h
      omega
    · rwa [hn] at h
  have hnr' : 2 * r + 2 < n' := by
    rcases hd' 0 with h | h
    · rw [hn'] at h
      omega
    · rwa [hn'] at h
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hn']; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hL
  have hcom := (hCB L hL).2 F F' Y Y' r n n' hFL hFL' hn hn' hnr hnr'
  have hρ : 0 ≤ σ / 64 := by positivity
  have hb := fun o (ho : o ∈ centredCube L) => centredExpansion_close_at_site (star := star) (a := a) (ρA := ρA)
    (m := m) hS hE hMv hC₀ hrow hL h64 hT₀ hT₀' hsm hsm' hloc hag₀ hσ hσ1 hδ hE0
    hEE hC hδ₂ hsmall hr c.1 o c.2 ho ζ (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ)
    (fun l => zeroExtensionL_apply_self _ hcom.injective_left ζ l)
    (fun l => zeroExtensionL_apply_self _ hcom.injective_right ζ l)
    (fun b => norm_zeroExtensionL_le _ ζ hρ hζ b) (fun b => norm_zeroExtensionL_le _ ζ hρ hζ b)
  simp only
  unfold cellCentredExpansion
  rw [sum_sites_of_cell hS hLF hs, sum_sites_of_cell hS hLF' hs', hFL, hFL', ← Finset.sum_sub_distrib]
  have h1 := Finset.abs_sum_le_sum_abs (fun o =>
    centredExpansion star a ρA m f (cellCentre F.depth (offsetCell Y (r / 8) c) + siteOfCoords F.depth o)
      (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) V -
    centredExpansion star a ρA m f (cellCentre F'.depth (offsetCell Y' (r / 8) c) + siteOfCoords F'.depth o)
      (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) V') (centredCube L)
  refine h1.trans ?_
  have h2 := Finset.sum_le_card_nsmul (centredCube L) _ _ (fun o ho => hb o ho)
  refine h2.trans ?_
  rw [card_centredCube hL, nsmul_eq_mul]
  push_cast
  push_cast at hnum
  refine hnum.trans ?_
  have hsq : 0 ≤ weightedSqNormAt κ (chordBondCell F) (cellDistReal F) (offsetCell Y (r / 8) c)
      (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [mul_nonneg hx hsq, mul_nonneg hε (mul_nonneg hx hsq)]
end ExpansionsOnTwoTori
open ExpansionsOnTwoTori in
theorem ExpansionsOnTwoTori.cellExpansionsCloseInValueOnTwoTori_proof (hSm : framesSmallStatement)
    (hLc : framesLocalStatement) (hCp : CouplingThreshold) (hD : DerivBoundAlongFlow)
    (hLog : LogNearOne) (hH : PathHolonomyLipschitz)
    (hE : QuaternionExp.ExpUnitLipschitzInjective) (hMv : ChartShiftLipschitz)
    (hS : SiteDecomposition) (hCB : commonBondsOfTwoTori) :
    CellExpansionsCloseInValueOnTwoTori := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_expansionCloseOfNearFields hD hLog hH
  intro a ha
  refine ⟨2 ^ 15, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨C, hC1, hloc⟩ := hLc a L c ha hL hc
  obtain ⟨Cb, σ₁, hCb, hσ₁, hsmall⟩ := hSm a L c ha hL hc
  obtain ⟨⟨-, -, hs₀, hδ₂, -⟩, -⟩ := hc.classical
  have hC0 : 0 < C := by linarith
  refine ⟨8 * ((L : ℝ) ^ 4 + 576 * C₀ * C * (16 / c.δ₂) ^ 4 * (L : ℝ) ^ 8), fun Ct hCt => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ₀ => ?_⟩
  refine ⟨1, one_pos, fun η₃ hη hη1 _ => ?_⟩
  obtain ⟨N₀, hN16, hN⟩ := exists_radius_floor (C := C) hδ₂
  refine ⟨N₀, fun nss hnss => ?_⟩
  refine ⟨min σ₁ (min (4 / 5 * c.s₀) 1), lt_min hσ₁ (lt_min (by positivity) one_pos), fun σ hσ hσ₀ p hp => ?_⟩
  have hσa : σ ≤ σ₁ := hσ₀.trans (min_le_left _ _)
  have hσb : σ ≤ 4 / 5 * c.s₀ := hσ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσc : σ ≤ 1 := hσ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨0, fun Cs _ E hE1 => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hCp (frameBoundConstant c) 1 c.δ₂ κ σ 0 hδ₂ hκ hκ₀ hσ
  refine ⟨max y₀ 1, fun y₁ hy₁ => ?_⟩
  intro t x f F F' V V' Y Y' r star h hrow
  have hxy : y₁ ≤ x := h.coupling_le
  have hx1 : 1 ≤ x := ((le_max_right _ _).trans hy₁).trans hxy
  obtain ⟨-, h16, hgap, -⟩ := hy₀ x (((le_max_left _ _).trans hy₁).trans hxy)
  have hr : nss ≤ r := h.radius_le
  have hr16 : 16 ≤ r := (hN16.trans hnss).trans hr
  have hE₃ : E ≤ E / η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  have htop : IsCubicTopTorus L t n₀ F := h.top
  have htop' : IsCubicTopTorus L t n₀ F' := h.top'
  have hcold : IsSmallCurvature (5 / 4 * σ) V := h.small
  have hcold' : IsSmallCurvature (5 / 4 * σ) V' := h.small'
  have hchain : ∀ {G : BlockFrame}, IsCubicTopTorus L t n₀ G → IsBlockTorus L G := by
    rintro G ⟨h1, -, n, h3, h4⟩
    exact ⟨h1, n, hn₀.trans h4, h3⟩
  have hFt : F'.depth = F.depth := htop'.2.1.trans htop.2.1.symm
  have hg : frameDecayBound (frameBoundConstant c) c.δ₂ (frameRadius x) ≤ 2⁻¹ ^ 10 * σ := hgap
  have hsm := (hsmall σ (frameRadius x) F V hσ hσa h16 hg (hchain htop) hcold).1 star
  have hsm' := (hsmall σ (frameRadius x) F' V' hσ hσa h16 hg (hchain htop') hcold').1 star
  have hl := hloc σ (frameRadius x) F F' V V' Y Y' r hσ (by linarith) h16 (hchain htop) (hchain htop') hFt
    hcold hcold' h.agree star
  have hnum := final_bound (L := L) (r := r) (C₀ := C₀) (C := C) (σ := σ) (δ₂ := c.δ₂) (κ := κ) (E := E)
    (E₃ := E / η₃) (Ct := Ct) hL₀ hr16 hκ hκ₀ hδ₂ hC₀0 hC0.le hσ hσc (by linarith) hE₃ hCt
  have hCtpos : 0 ≤ Ct := by
    refine le_trans ?_ hCt
    positivity
  have hε : 0 ≤ Ct * (1 + E / η₃) / 4 * Real.exp (-(2 * κ * r)) := by
    have : 0 ≤ E / η₃ := by positivity
    positivity
  have hrow' : IsRegularFamily L t n₀ σ (κ / 2 ^ 10) E (E / η₃) f := hrow
  exact nearCellsClose_of_params hS hE hMv hCB hC₀ hrow' hL hn₀ htop htop' hsm hsm' hl h.agree hσ hσc
    (by positivity) (by linarith) hE₃ hC0.le hδ₂ (hN r (hnss.trans hr)) hr16 (by linarith) hε hnum
end ColdStepAtMirrorFrames
end YangMills.Construction
end
