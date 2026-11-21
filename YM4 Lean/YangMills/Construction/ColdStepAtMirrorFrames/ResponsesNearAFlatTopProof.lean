import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PowerWeightsThroughTheKernelProof
import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.FlowOfACutField
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace NearUniformTop
open BlockOffsets
variable {F : BlockFrame}
def offsetSupNorm (o : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun l => (o l).natAbs
theorem natAbs_le_offsetSupNorm (o : Fin 4 → ℤ) (l : Fin 4) : (o l).natAbs ≤ offsetSupNorm o := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem withinRadius_offsetSupNorm (o : Fin 4 → ℤ) : WithinRadius (offsetSupNorm o) o := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.PowerWeightKernel.abs_apply_le_supNorm <;> assumption
theorem offsetSupNorm_le_of_withinRadius {r : ℕ} {o : Fin 4 → ℤ} (h : WithinRadius r o) : offsetSupNorm o ≤ r :=
  Finset.sup_le fun l _ => by
    have := abs_le.mp (h l)
    omega
theorem withinRadius_mono {r r' : ℕ} {o : Fin 4 → ℤ} (h : r ≤ r') (ho : WithinRadius r o) : WithinRadius r' o := by apply _root_.YangMills.Construction.InBoxTransfer.offsetInBox_mono <;> assumption
theorem offsetSupNorm_add_single_le (o : Fin 4 → ℤ) (i : Fin 4) : offsetSupNorm (o + Pi.single i 1) ≤ offsetSupNorm o + 1 := by
  refine Finset.sup_le fun l _ => ?_
  have := natAbs_le_offsetSupNorm o l
  by_cases h : l = i
  · subst h
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
    omega
theorem offsetSupNorm_le_add_single (o : Fin 4 → ℤ) (i : Fin 4) : offsetSupNorm o ≤ offsetSupNorm (o + Pi.single i 1) + 1 := by
  refine Finset.sup_le fun l _ => ?_
  have := natAbs_le_offsetSupNorm (o + Pi.single i 1) l
  by_cases h : l = i
  · subst h
    simp only [Pi.add_apply, Pi.single_eq_same] at this
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero] at this
    omega
def bondRadius (o : Fin 4 → ℤ) (i : Fin 4) : ℕ := max (offsetSupNorm o) (offsetSupNorm (o + Pi.single i 1))
theorem bondWithinRadius_bondRadius (o : Fin 4 → ℤ) (i : Fin 4) : BondWithinRadius (bondRadius o i) (o, i) :=
  ⟨withinRadius_mono (le_max_left _ _) (withinRadius_offsetSupNorm o), withinRadius_mono (le_max_right _ _) (withinRadius_offsetSupNorm _)⟩
theorem bondRadius_le {r : ℕ} {o : Fin 4 → ℤ} {i : Fin 4} (h : BondWithinRadius r (o, i)) : bondRadius o i ≤ r :=
  max_le (offsetSupNorm_le_of_withinRadius h.1) (offsetSupNorm_le_of_withinRadius h.2)
def radialCutoff (R r : ℕ) : ℝ := min 1 (max 0 (2 - 2 * (r : ℝ) / R))
theorem radialCutoff_nonneg (R r : ℕ) : 0 ≤ radialCutoff R r := le_min zero_le_one (le_max_left _ _)
theorem radialCutoff_le_one (R r : ℕ) : radialCutoff R r ≤ 1 := min_le_left _ _
theorem radialCutoff_eq_one {R r : ℕ} (hR : 0 < R) (h : 2 * r ≤ R) : radialCutoff R r = 1 := by
  unfold radialCutoff
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have h' : 2 * (r : ℝ) ≤ R := by exact_mod_cast h
  have : 1 ≤ 2 - 2 * (r : ℝ) / R := by
    have : 2 * (r : ℝ) / R ≤ 1 := by rw [div_le_one hR']; exact h'
    linarith
  rw [min_eq_left (this.trans (le_max_right _ _))]
theorem radialCutoff_eq_zero {R r : ℕ} (hR : 0 < R) (h : R ≤ r) : radialCutoff R r = 0 := by
  unfold radialCutoff
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have h' : (R : ℝ) ≤ r := by exact_mod_cast h
  have : 2 - 2 * (r : ℝ) / R ≤ 0 := by
    have : 1 ≤ (r : ℝ) / R := by rw [le_div_iff₀ hR']; linarith
    have e : 2 * (r : ℝ) / R = 2 * ((r : ℝ) / R) := by ring
    rw [e]; linarith
  rw [max_eq_left this]
  simp
theorem abs_radialCutoff_sub_le {R r r' : ℕ} (hR : 0 < R) (h : r ≤ r' + 2) (h' : r' ≤ r + 2) :
    |radialCutoff R r - radialCutoff R r'| ≤ 4 / R := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hd : |(2 - 2 * (r : ℝ) / R) - (2 - 2 * (r' : ℝ) / R)| ≤ 4 / R := by
    have e : (2 - 2 * (r : ℝ) / R) - (2 - 2 * (r' : ℝ) / R) = 2 * ((r' : ℝ) - r) / R := by ring
    rw [e, abs_div, abs_of_pos hR', abs_mul]
    have h1 : (r : ℝ) ≤ r' + 2 := by exact_mod_cast h
    have h2 : (r' : ℝ) ≤ r + 2 := by exact_mod_cast h'
    have h3 : |(r' : ℝ) - r| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    gcongr
    simp only [abs_two]
    linarith
  unfold radialCutoff
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le (by positivity) ?_
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) hd)
theorem add_siteOfCoords_minimalOffset (hs : ∀ i, 0 < F.extent i) (Y z : F.Cell) : Y + siteOfCoords F.top (minimalOffset Y z) = z := by
  funext i
  have : NeZero (F.period F.top i) := ⟨by rw [period_top]; have := hs i; omega⟩
  show Y i + (((((z - Y : F.Cell)) i).valMinAbs : ℤ) : ZMod (F.period F.top i)) = z i
  rw [ZMod.coe_valMinAbs]
  simp
theorem minimalOffset_add_siteOfCoords {r : ℕ} (z : F.Cell) (h : Fin 4 → ℤ) (hb : WithinRadius r h)
    (hs : ∀ i, 2 * r + 2 < F.extent i) : minimalOffset z (z + siteOfCoords F.top h) = h := by
  funext i
  have hp : F.period F.top i = F.extent i := period_top i
  have : NeZero (F.period F.top i) := ⟨by rw [hp]; have := hs i; omega⟩
  show (((z + siteOfCoords F.top h - z : F.Cell)) i).valMinAbs = h i
  have e : ((z + siteOfCoords F.top h - z : F.Cell)) i = ((h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e, ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have a := abs_le.mp (hb i)
  have b := hs i
  rw [hp]
  constructor <;> omega
theorem siteOfCoords_add (a b : Fin 4 → ℤ) : (siteOfCoords F.top (a + b) : F.Site F.top) = siteOfCoords F.top a + siteOfCoords F.top b := by
  funext i
  simp [siteOfCoords]
theorem minimalOffset_add_shift {r : ℕ} (hs : ∀ i, 2 * r + 2 < F.extent i) (Y x : F.Cell) (w : Fin 4 → ℤ)
    (hb : WithinRadius r (minimalOffset Y x + w)) :
    minimalOffset Y (x + siteOfCoords F.top w) = minimalOffset Y x + w := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have e : x + siteOfCoords F.top w = Y + siteOfCoords F.top (minimalOffset Y x + w) := by
    rw [siteOfCoords_add, ← add_assoc, add_siteOfCoords_minimalOffset hpos]
  rw [e, minimalOffset_add_siteOfCoords Y _ hb hs]
def bondCutoff (R : ℕ) (Y z : F.Cell) (i : Fin 4) : ℝ := radialCutoff R (bondRadius (minimalOffset Y z) i)
theorem offsetSupNorm_le_bondRadius_le (o : Fin 4 → ℤ) (i : Fin 4) : offsetSupNorm o ≤ bondRadius o i ∧ bondRadius o i ≤ offsetSupNorm o + 1 :=
  ⟨le_max_left _ _, max_le (Nat.le_succ _) (offsetSupNorm_add_single_le o i)⟩
theorem withinRadius_add_single_add_single {r : ℕ} (o : Fin 4 → ℤ) (μ ν : Fin 4) (h : μ ≠ ν) (ho : WithinRadius r o) :
    WithinRadius (r + 1) (o + Pi.single μ 1 + Pi.single ν 1) := by
  intro l
  have a := abs_le.mp (ho l)
  rw [abs_le]
  by_cases e1 : l = μ
  · subst e1
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h]
    push_cast
    omega
  · by_cases e2 : l = ν
    · subst e2
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne e1]
      push_cast
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2]
      push_cast
      omega
theorem withinRadius_add_single {r : ℕ} (o : Fin 4 → ℤ) (μ : Fin 4) (ho : WithinRadius r o) :
    WithinRadius (r + 1) (o + Pi.single μ 1) := by
  intro l
  have a := abs_le.mp (ho l)
  rw [abs_le]
  by_cases e1 : l = μ
  · subst e1
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne e1]
    push_cast
    omega
theorem plaquette_cutoff_cases {R : ℕ} (hR : 0 < R) (hs : ∀ i, 2 * (R + 2) + 2 < F.extent i) (Y : F.Cell)
    (p : F.Cell × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) :
    (∀ l, bondCutoff R Y (plaquetteBondList p l).1 (plaquetteBondList p l).2 = 0) ∨
    ((∀ l, BondWithinRadius (R + 2) (minimalOffset Y (plaquetteBondList p l).1, (plaquetteBondList p l).2)) ∧
      ∀ l, |bondCutoff R Y (plaquetteBondList p l).1 (plaquetteBondList p l).2 - bondCutoff R Y p.1 p.2.1| ≤ 4 / R) := by
  obtain ⟨x, μ, ν⟩ := p
  have hμν : μ ≠ ν := hp.ne
  set o := minimalOffset Y x with ho
  have hs1 : ∀ i, 2 * (R + 1) + 2 < F.extent i := fun i => by have := hs i; omega
  by_cases hI : WithinRadius (R + 1) o
  · right
    have e1 : minimalOffset Y (x + unitStep F.top μ) = o + Pi.single μ 1 :=
      minimalOffset_add_shift hs Y x _ (withinRadius_add_single o μ hI)
    have e2 : minimalOffset Y (x + unitStep F.top ν) = o + Pi.single ν 1 :=
      minimalOffset_add_shift hs Y x _ (withinRadius_add_single o ν hI)
    have b1 : BondWithinRadius (R + 2) (o, μ) := ⟨withinRadius_mono (by omega) hI, withinRadius_add_single o μ hI⟩
    have b2 : BondWithinRadius (R + 2) (o, ν) := ⟨withinRadius_mono (by omega) hI, withinRadius_add_single o ν hI⟩
    have hb : ∀ l, BondWithinRadius (R + 2) (minimalOffset Y (plaquetteBondList (x, μ, ν) l).1, (plaquetteBondList (x, μ, ν) l).2) := by
      intro l
      fin_cases l
      · exact b1
      · show BondWithinRadius (R + 2) (minimalOffset Y (x + unitStep F.top μ), ν)
        rw [e1]
        exact ⟨withinRadius_add_single o μ hI, withinRadius_add_single_add_single o μ ν hμν hI⟩
      · show BondWithinRadius (R + 2) (minimalOffset Y (x + unitStep F.top ν), μ)
        rw [e2]
        exact ⟨withinRadius_add_single o ν hI, withinRadius_add_single_add_single o ν μ hμν.symm hI⟩
      · exact b2
    refine ⟨hb, fun l => ?_⟩
    have r0 := offsetSupNorm_le_bondRadius_le o μ
    have s1 := offsetSupNorm_add_single_le o μ
    have s1' := offsetSupNorm_le_add_single o μ
    have s2 := offsetSupNorm_add_single_le o ν
    have s2' := offsetSupNorm_le_add_single o ν
    have r1 := offsetSupNorm_le_bondRadius_le (o + Pi.single μ 1) ν
    have r2 := offsetSupNorm_le_bondRadius_le (o + Pi.single ν 1) μ
    have r3 := offsetSupNorm_le_bondRadius_le o ν
    fin_cases l
    · simp [plaquetteBondList, bondCutoff]
      positivity
    · show |radialCutoff R (bondRadius (minimalOffset Y (x + unitStep F.top μ)) ν) - radialCutoff R (bondRadius o μ)| ≤ 4 / R
      rw [e1]
      exact abs_radialCutoff_sub_le hR (by omega) (by omega)
    · show |radialCutoff R (bondRadius (minimalOffset Y (x + unitStep F.top ν)) μ) - radialCutoff R (bondRadius o μ)| ≤ 4 / R
      rw [e2]
      exact abs_radialCutoff_sub_le hR (by omega) (by omega)
    · show |radialCutoff R (bondRadius o ν) - radialCutoff R (bondRadius o μ)| ≤ 4 / R
      exact abs_radialCutoff_sub_le hR (by omega) (by omega)
  · left
    have key : ∀ (w : Fin 4 → ℤ) (i : Fin 4), WithinRadius 1 w → bondCutoff R Y (x + siteOfCoords F.top w) i = 0 := by
      intro w i hw
      refine radialCutoff_eq_zero hR ?_
      by_contra hlt
      have hb : WithinRadius R (minimalOffset Y (x + siteOfCoords F.top w)) :=
        withinRadius_mono (by have := (offsetSupNorm_le_bondRadius_le (minimalOffset Y (x + siteOfCoords F.top w)) i).1; omega) (withinRadius_offsetSupNorm _)
      apply hI
      have hneg : WithinRadius (R + 1) (minimalOffset Y (x + siteOfCoords F.top w) + (-w)) := by
        intro l
        have a := abs_le.mp (hb l)
        have c := abs_le.mp (hw l)
        rw [abs_le]
        simp only [Pi.add_apply, Pi.neg_apply]
        push_cast at a c ⊢
        omega
      have h2 := minimalOffset_add_shift hs1 Y (x + siteOfCoords F.top w) (-w) hneg
      have h3 : x + siteOfCoords F.top w + siteOfCoords F.top (-w) = x := by
        have z0 : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by funext i; simp [siteOfCoords]
        rw [add_assoc, ← siteOfCoords_add, add_neg_cancel, z0, add_zero]
      rw [h3] at h2
      rw [ho, h2]
      exact hneg
    have w0 : WithinRadius 1 (0 : Fin 4 → ℤ) := fun l => by simp
    have wu : ∀ i : Fin 4, WithinRadius 1 (Pi.single i 1 : Fin 4 → ℤ) := fun i l => by
      by_cases e : l = i
      · subst e; simp
      · simp [Pi.single_eq_of_ne e]
    have z0 : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by funext i; simp [siteOfCoords]
    intro l
    fin_cases l
    · have := key 0 μ w0
      rwa [z0, add_zero] at this
    · exact key _ ν (wu μ)
    · exact key _ μ (wu ν)
    · have := key 0 ν w0
      rwa [z0, add_zero] at this
theorem enclosingCell_next_of_crossing (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide)
    (i : Fin 4) (hc : IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i)) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) = z + unitStep F.top i := by
  have hi := (isCrossingBond_iff hL hs z h hh i).mp hc
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hhalf : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  let h' : Fin 4 → ℤ := h + Pi.single i 1 - Pi.single i (F.blockSide : ℤ)
  have hh' : h' ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff]
    intro l
    have hl := (mem_centredCube_iff h).mp hh l
    by_cases e : l = i
    · subst e
      simp only [h', Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
      rw [hi] at hl ⊢
      omega
    · simpa [h', Pi.single_eq_of_ne e] using hl
  have e1 : (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth (z + unitStep F.top i) + siteOfCoords F.depth h' := by
    rw [offset_add_unitStep, cellCentre_add_unitStep hs]
    have : (siteOfCoords F.depth (h + Pi.single i 1) : F.Site F.depth) =
        siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) + siteOfCoords F.depth h' := by
      funext l
      simp [siteOfCoords, h']
    rw [this, add_assoc]
  rw [e1, enclosingCell_offset ⟨k, hk⟩ hs _ h' hh']
theorem cellSupDist_eq_offsetSupNorm (hs : ∀ i, 0 < F.extent i) (Y z : F.Cell) : cellSupDist Y z = offsetSupNorm (minimalOffset Y z) := by
  unfold cellSupDist offsetSupNorm
  congr 1
  funext i
  have : NeZero (F.period F.top i) := ⟨by rw [period_top]; have := hs i; omega⟩
  show (((Y - z : F.Cell)) i).valMinAbs.natAbs = (((z - Y : F.Cell)) i).valMinAbs.natAbs
  have e : ((Y - z : F.Cell)) i = -(((z - Y : F.Cell)) i) := by simp
  rw [e, ZMod.natAbs_valMinAbs_neg]
open Classical in
def bondLog (V : F.GaugeField F.top) : F.Site F.top → Fin 4 → imaginaryQuaternions := fun z i =>
  if h : ∃ A : imaginaryQuaternions, expUnit A = V z i ∧ ‖A‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (V z i) then h.choose else 0
theorem bondLog_spec (hlog : LogNearOne) (V : F.GaugeField F.top) (z : F.Site F.top) (i : Fin 4)
    (h : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (V z i) ≤ 1) : expUnit (bondLog V z i) = V z i ∧ ‖bondLog V z i‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (V z i) := by
  have hx := hlog (V z i) h
  unfold bondLog
  rw [dif_pos hx]
  exact hx.choose_spec
theorem bondLog_bound (hlog : LogNearOne) {R : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : 3 * R * s ≤ 1)
    (hpos : ∀ i, 0 < F.extent i) (V : F.GaugeField F.top) (Y : F.Cell)
    (hn : IsNearUniformAbout s R V Y) (z : F.Cell) (i : Fin 4) (hb : BondWithinRadius R (minimalOffset Y z, i)) :
    expUnit (bondLog V z i) = V z i ∧ ‖bondLog V z i‖ ≤ 6 * R * s := by
  have hz := add_siteOfCoords_minimalOffset hpos Y z
  have h1 := hn R (minimalOffset Y z, i) le_rfl hb
  simp only [hz] at h1
  obtain ⟨a, b⟩ := bondLog_spec hlog V z i (h1.trans hs1)
  exact ⟨a, b.trans (by nlinarith)⟩
theorem cutoffFlow_smallCurvature (hcf : CutoffFlowSmallCurvature) (hlog : LogNearOne)
    {R : ℕ} {s s₁ : ℝ} (hR : 16 ≤ R) (hs0 : 0 < s) (hsm : 300 * s ≤ s₁) (hs2 : 2400 * ((R : ℝ) + 1) ^ 2 * s ≤ 1)
    (hs : ∀ i, 2 * R + 2 < F.extent i) (V : F.GaugeField F.top) (Y : F.Cell) (hV : IsSmallCurvature s V)
    (hn : IsNearUniformAbout s R V Y) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    IsSmallCurvature s₁ (expFlow (fun y i => bondCutoff (R - 2) Y y i • bondLog V y i) (uniformField F F.top) u) := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hRr : (16 : ℝ) ≤ R := by exact_mod_cast hR
  have hs1 : 3 * (R : ℝ) * s ≤ 1 := by nlinarith
  have hR2 : (R - 2 : ℕ) + 2 = R := by omega
  have hRp : 0 < R - 2 := by omega
  have hs' : ∀ i, 2 * ((R - 2) + 2) + 2 < F.extent i := fun i => by rw [hR2]; exact hs i
  refine hcf F F.top V (bondLog V) (bondCutoff (R - 2) Y) s₁ (by linarith) (fun y i => ⟨radialCutoff_nonneg _ _, radialCutoff_le_one _ _⟩)
    (fun p hp => ?_) u h0 h1
  rcases plaquette_cutoff_cases hRp hs' Y p hp with hz | ⟨hb, hl⟩
  · exact Or.inl hz
  · right
    rw [hR2] at hb
    have hA := fun l => bondLog_bound hlog hs0.le hs1 hpos V Y hn _ _ (hb l)
    refine ⟨fun l => (hA l).1.symm, ?_, ?_⟩
    · have : ∑ l, ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤ ∑ _l : Fin 4, 6 * (R : ℝ) * s :=
        Finset.sum_le_sum fun l _ => (hA l).2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      push_cast at this
      nlinarith
    · have hc := hV p hp
      have hq : ∑ l, ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤ 24 * (R : ℝ) * s := by
        have : ∑ l, ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤ ∑ _l : Fin 4, 6 * (R : ℝ) * s :=
          Finset.sum_le_sum fun l _ => (hA l).2
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        push_cast at this
        nlinarith
      have hq0 : 0 ≤ ∑ l, ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hsq := pow_le_pow_left₀ hq0 hq 2
      have hRm : (R : ℝ) ≤ 2 * ((R - 2 : ℕ) : ℝ) := by
        have : R ≤ 2 * (R - 2) := by omega
        exact_mod_cast this
      have hRm0 : (0 : ℝ) < ((R - 2 : ℕ) : ℝ) := by exact_mod_cast hRp
      have hlip : ∑ l, |bondCutoff (R - 2) Y (plaquetteBondList p l).1 (plaquetteBondList p l).2 -
            bondCutoff (R - 2) Y p.1 p.2.1| * ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤
          192 * s := by
        have each : ∀ l, |bondCutoff (R - 2) Y (plaquetteBondList p l).1 (plaquetteBondList p l).2 -
            bondCutoff (R - 2) Y p.1 p.2.1| * ‖bondLog V (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤ 48 * s := by
          intro l
          have a1 := mul_le_mul (hl l) (hA l).2 (norm_nonneg _) (by positivity)
          refine a1.trans ?_
          have e : 4 / ((R - 2 : ℕ) : ℝ) * (6 * R * s) = 24 * s * ((R : ℝ) / ((R - 2 : ℕ) : ℝ)) := by
            field_simp
            ring
          rw [e]
          have : (R : ℝ) / ((R - 2 : ℕ) : ℝ) ≤ 2 := by
            rw [div_le_iff₀ hRm0]; linarith
          nlinarith
        have := Finset.sum_le_sum (s := Finset.univ) fun l _ => each l
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        push_cast at this
        nlinarith
      have hsq2 : 4 * (24 * (R : ℝ) * s) ^ 2 ≤ s := by
        have a1 : (R : ℝ) ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := by nlinarith
        have a2 : 2304 * (R : ℝ) ^ 2 * s ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right a2 hs0.le]
      linarith
theorem eq_cutoffFlow_of_near (hlog : LogNearOne) {R r : ℕ} {s : ℝ} (hR : 16 ≤ R) (hs0 : 0 ≤ s)
    (hs1 : 3 * R * s ≤ 1) (hs : ∀ i, 2 * R + 2 < F.extent i) (V : F.GaugeField F.top) (Y : F.Cell)
    (hn : IsNearUniformAbout s R V Y) (hr : 2 * r ≤ R - 2) (b : (Fin 4 → ℤ) × Fin 4) (hb : BondWithinRadius r b) :
    V (Y + siteOfCoords F.top b.1) b.2 =
      expFlow (fun y i => bondCutoff (R - 2) Y y i • bondLog V y i) (uniformField F F.top) 1
        (Y + siteOfCoords F.top b.1) b.2 := by
  obtain ⟨o, i⟩ := b
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hrR : r ≤ R := by omega
  have hs' : ∀ i, 2 * r + 2 < F.extent i := fun i => by have := hs i; omega
  have ho : minimalOffset Y (Y + siteOfCoords F.top o) = o := minimalOffset_add_siteOfCoords Y o hb.1 hs'
  have hbR : BondWithinRadius R (minimalOffset Y (Y + siteOfCoords F.top o), i) := by
    rw [ho]
    exact ⟨withinRadius_mono hrR hb.1, withinRadius_mono hrR hb.2⟩
  have hA := bondLog_bound hlog hs0 hs1 hpos V Y hn _ i hbR
  have hc : bondCutoff (R - 2) Y (Y + siteOfCoords F.top o) i = 1 := by
    unfold bondCutoff
    rw [ho]
    have := bondRadius_le hb
    exact radialCutoff_eq_one (by omega) (by omega)
  simp only [expFlow, leftTranslate, uniformField, hc, one_smul, mul_one]
  exact hA.1.symm
theorem sum_norm_cutoffLog_le (hlog : LogNearOne) {R : ℕ} {s : ℝ} (hR : 16 ≤ R) (hs0 : 0 ≤ s)
    (hs1 : 3 * R * s ≤ 1) (hs : ∀ i, 2 * R + 2 < F.extent i) (V : F.GaugeField F.top) (Y : F.Cell)
    (hn : IsNearUniformAbout s R V Y) :
    ∑ b ∈ finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)), ‖bondCutoff (R - 2) Y b.1 b.2 • bondLog V b.1 b.2‖ ≤
      4 * (2 * (R : ℝ) + 1) ^ 4 * (6 * R * s) := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set T := finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)) with hT
  set q := 6 * (R : ℝ) * s with hq
  have hq0 : 0 ≤ q := by positivity
  let P : (F.Cell × Fin 4) → Prop := fun b => bondRadius (minimalOffset Y b.1) b.2 < R - 2
  rw [← Finset.sum_filter_add_sum_filter_not T P]
  have h2 : ∑ b ∈ T.filter (fun b => ¬ P b), ‖bondCutoff (R - 2) Y b.1 b.2 • bondLog V b.1 b.2‖ = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have hnP : ¬ P b := (Finset.mem_filter.mp hb).2
    have : bondCutoff (R - 2) Y b.1 b.2 = 0 := radialCutoff_eq_zero (by omega) (not_lt.mp hnP)
    simp [this]
  have hbox : ∀ b, P b → BondWithinRadius R (minimalOffset Y b.1, b.2) := fun b hb => by
    have h := bondWithinRadius_bondRadius (minimalOffset Y b.1) b.2
    exact ⟨withinRadius_mono (by have : bondRadius (minimalOffset Y b.1) b.2 < R - 2 := hb; omega) h.1,
      withinRadius_mono (by have : bondRadius (minimalOffset Y b.1) b.2 < R - 2 := hb; omega) h.2⟩
  have h1 : ∑ b ∈ T.filter P, ‖bondCutoff (R - 2) Y b.1 b.2 • bondLog V b.1 b.2‖ ≤
      ((T.filter P).card : ℝ) * q := by
    have := Finset.sum_le_card_nsmul (T.filter P) (fun b => ‖bondCutoff (R - 2) Y b.1 b.2 • bondLog V b.1 b.2‖) q
      (fun b hb => by
        have hP : P b := (Finset.mem_filter.mp hb).2
        have hA := (bondLog_bound hlog hs0 hs1 hpos V Y hn b.1 b.2 (hbox b hP)).2
        have hc : ‖bondCutoff (R - 2) Y b.1 b.2‖ ≤ 1 := by
          rw [Real.norm_of_nonneg (show 0 ≤ bondCutoff (R - 2) Y b.1 b.2 from radialCutoff_nonneg _ _)]
          exact radialCutoff_le_one _ _
        rw [norm_smul]
        calc _ ≤ 1 * ‖bondLog V b.1 b.2‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ ≤ q := by rw [one_mul]; exact hA)
    simpa using this
  let Q : Finset ((Fin 4 → ℤ) × Fin 4) :=
    (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)) ×ˢ Finset.univ
  have hcard : (T.filter P).card ≤ Q.card := by
    refine Finset.card_le_card_of_injOn (fun b => (minimalOffset Y b.1, b.2)) ?_ ?_
    · intro b hb
      have hP : P b := (Finset.mem_filter.mp hb).2
      have h := hbox b hP
      simp only [Q, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc,
        Finset.coe_univ, Set.mem_univ, and_true]
      exact fun l => abs_le.mp (h.1 l)
    · intro b _ b' _ h
      have h0 := Prod.mk.inj h
      have h1 : minimalOffset Y b.1 = minimalOffset Y b'.1 := h0.1
      have h2 : b.2 = b'.2 := h0.2
      have h3 : b.1 = b'.1 := by
        rw [← add_siteOfCoords_minimalOffset hpos Y b.1, ← add_siteOfCoords_minimalOffset hpos Y b'.1, h1]
      exact Prod.ext h3 h2
  have hQ : (Q.card : ℝ) = 4 * (2 * (R : ℝ) + 1) ^ 4 := by
    simp only [Q, Finset.card_product, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [h2, add_zero]
  refine h1.trans ?_
  rw [← hQ]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hq0
theorem three_mul_le_one_of_sq {R s : ℝ} (hR : 16 ≤ R) (hs : 0 < s) (h : 2400 * (R + 1) ^ 2 * s ≤ 1) : 3 * R * s ≤ 1 := by
  nlinarith [mul_pos hs (by linarith : 0 < R)]
theorem neg_decay_le {δ R r d : ℝ} (hδ : 0 < δ) (hR : 16 ≤ R) (hr : R ≤ 2 * r + 3) (hd : 4 * d ≤ R) :
    -(δ / 2 * (r - d)) ≤ -(δ / 16 * R) := by
  have : R / 8 ≤ r - d := by linarith
  nlinarith
theorem mul_le_half_of_scaled {N s ε : ℝ} (hs : 0 < s) (h : 2 * (N + 1) * s ≤ ε) : N * s ≤ ε / 2 := by
  have e : 2 * (N + 1) * s = 2 * (N * s) + 2 * s := by ring
  rw [e] at h
  linarith
end NearUniformTop
open NearUniformTop
open BlockOffsets
set_option maxHeartbeats 1000000 in
theorem derivsNearUniformTop (hflow : DerivBoundAlongFlow)
    (hcf : CutoffFlowSmallCurvature) (hlog : LogNearOne) :
    DerivsNearUniformTop := by
  intro a L c ha hLo hc ε hε
  obtain ⟨C₀, hC₀, hfl⟩ := hflow
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, hall⟩ := hc.classical
  have hten : Filter.Tendsto (fun R : ℕ => c.Kk 3 * Real.exp (-(c.δ₂ / 16 * (R : ℝ)))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.exp (-(c.δ₂ / 16 * x))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_id.const_mul_atTop (by positivity)))
    simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul (c.Kk 3)
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (hten.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max R₁ 16, fun R hR => ?_⟩
  have hR16 : 16 ≤ R := le_trans (le_max_right _ _) hR
  have hRR₁ : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hMs : 0 ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := by
    have := hKk 1
    have := hKk 2
    have := hKk 3
    positivity
  set N₀ : ℝ := C₀ * (c.Kk 1 + c.Kk 2 + c.Kk 3) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (6 * R)) with hN₀
  have hN₀0 : 0 ≤ N₀ := by positivity
  set sb : ℝ := min (min (c.s₀ / 300) (1 / (2400 * ((R : ℝ) + 1) ^ 2))) (ε / (2 * (N₀ + 1))) with hsb
  have hsb0 : 0 < sb := by
    refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨4 / 5 * sb, by positivity, ?_⟩
  intro σ F V Y hσ hσ0 hF hs hV hn b e X hb hbd hed hX
  set s := 5 / 4 * σ with hsdef
  have hs0 : 0 < s := by positivity
  have hsl : s ≤ sb := by rw [hsdef]; linarith
  have c1 : 300 * s ≤ c.s₀ := by
    have := hsl.trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have c2 : 2400 * ((R : ℝ) + 1) ^ 2 * s ≤ 1 := by
    have h := hsl.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have c3 : 2 * (N₀ + 1) * s ≤ ε := by
    have h := hsl.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hRr : (16 : ℝ) ≤ R := by exact_mod_cast hR16
  have hs1 : 3 * (R : ℝ) * s ≤ 1 := three_mul_le_one_of_sq hRr hs0 c2
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hflowc := cutoffFlow_smallCurvature (s₁ := c.s₀) hcf hlog hR16 hs0 c1 c2 hs V Y hV hn
  set Bf : F.Site F.top → Fin 4 → imaginaryQuaternions := fun y i => bondCutoff (R - 2) Y y i • bondLog V y i with hBf
  have hV1 : IsSmallCurvature c.s₀ (expFlow Bf (uniformField F F.top) 1) := hflowc 1 zero_le_one le_rfl
  have hV0 : IsSmallCurvature c.s₀ V := fun p hp => (hV p hp).trans (by linarith)
  have hside2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have hLF : Odd F.blockSide := by rw [hF.1]; exact hLo
  set r := (R - 2) / 2 with hr
  have h2r : 2 * r ≤ R - 2 := by omega
  have hag : AgreeOnBall (finiteCells F) V (finiteCells F) (expFlow Bf (uniformField F F.top) 1) Y Y r :=
    ⟨fun i => Or.inr (by have := hs i; omega), fun i => Or.inr (by have := hs i; omega),
      fun _ _ => Iff.rfl, fun b hb => eq_cutoffFlow_of_near hlog hR16 hs0.le hs1 hs V Y hn h2r b hb⟩
  have hcmp := (hall F c.s₀ V hF hs₀ le_rfl hV0).2.2.2 F _ Y Y r hF rfl hV1 hag
  obtain ⟨x, i⟩ := b
  obtain ⟨ez, ei⟩ := e
  have hxs : x ∈ sitesOfCells (finiteCells F) F.depth := by
    have hb2 := hb
    simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product] at hb2
    exact hb2.1.1.1
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image, top_sub_depth, pow_one] at hxs
  obtain ⟨z, -, h₀, hh₀, rfl⟩ := hxs
  have hcell : enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth) = z := enclosingCell_offset hLF hside2 z h₀ hh₀
  rw [hcell] at hbd
  set hY := minimalOffset Y z with hhY
  have hzY : Y + siteOfCoords F.top hY = z := add_siteOfCoords_minimalOffset hpos Y z
  have hd : offsetSupNorm hY = cellSupDist Y z := (cellSupDist_eq_offsetSupNorm hpos Y z).symm
  have hlb : fineBondAt Y hY h₀ i = ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i) := by
    simp only [fineBondAt, hzY]
  have hnext : cellSupDist Y (enclosingCell ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth) + unitStep F.depth i)) ≤ r := by
    by_cases hcr : IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i)
    · rw [enclosingCell_next_of_crossing hLF hside2 z h₀ hh₀ i hcr, cellSupDist_eq_offsetSupNorm hpos]
      have hu := offsetSupNorm_add_single_le hY i
      have hbx : WithinRadius R (minimalOffset Y z + Pi.single i 1) :=
        withinRadius_mono (by omega) (withinRadius_offsetSupNorm (hY + Pi.single i 1))
      have h9 := minimalOffset_add_shift hs Y z (Pi.single i 1) hbx
      have e3 : (unitStep F.top i : F.Cell) = siteOfCoords F.top (Pi.single i 1) := rfl
      rw [e3, h9]
      show offsetSupNorm (hY + Pi.single i 1) ≤ r
      omega
    · have hsame : enclosingCell ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth) + unitStep F.depth i) =
          enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth) := not_not.mp hcr
      rw [hsame, hcell]
      omega
  have hbox : IsFineBondWithinRadius Y r hY h₀ i := by
    refine ⟨hh₀, by rw [hlb]; exact hb, withinRadius_mono (by omega) (withinRadius_offsetSupNorm hY), ?_, ?_⟩
    · rw [hlb]; simp only [hcell]; omega
    · rw [hlb]; exact hnext
  set he := minimalOffset Y ez with hhe
  have hed' : offsetSupNorm he = cellSupDist Y ez := (cellSupDist_eq_offsetSupNorm hpos Y ez).symm
  have hezY : Y + siteOfCoords F.top he = ez := add_siteOfCoords_minimalOffset hpos Y ez
  have hed2 : 4 * cellSupDist Y ez ≤ R := hed
  have hue := offsetSupNorm_add_single_le he ei
  have hue2 : offsetSupNorm (he + Pi.single ei 1) ≤ r := by omega
  have hbe : BondWithinRadius r (he, ei) :=
    ⟨withinRadius_mono (by omega) (withinRadius_offsetSupNorm he), withinRadius_mono hue2 (withinRadius_offsetSupNorm _)⟩
  have hbf : bondsAt Y ![(he, ei)] = ![(ez, ei)] := by
    funext l
    fin_cases l
    simp [bondsAt, hezY]
  have hX1 : AreUnitVectors ![X] := fun l => by
    fin_cases l
    exact hX
  have h1 := hcmp.coordinateDerivatives hY h₀ i 1 ![(he, ei)] ![X] hbox le_rfl (by norm_num)
    (fun l => by fin_cases l; exact hbe) hX1
  rw [hbf, hlb] at h1
  have h1' : ‖bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i)) V ![(ez, ei)] ![X] -
      bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i))
        (expFlow Bf (uniformField F F.top) 1) ![(ez, ei)] ![X]‖ ≤ ε / 2 := by
    simp only [hcell] at h1
    refine h1.trans (le_trans ?_ (hR₁ R hRR₁).le)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hKk 3).le
    have hr2 : (R : ℝ) ≤ 2 * r + 3 := by
      have : R ≤ 2 * r + 3 := by omega
      exact_mod_cast this
    have hd4 : 4 * (cellSupDist Y z : ℝ) ≤ R := by exact_mod_cast hbd
    exact neg_decay_le hδ₂ hRr hr2 hd4
  have hmem : ∀ b, b ∈ finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)) := fun b =>
    Finset.mem_product.mpr ⟨mem_finiteCells hside2 _, Finset.mem_univ _⟩
  have hsA : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  have hsm : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ContDiffThreeAlongBonds
      (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i))
      (expFlow Bf (uniformField F F.top) u) := by
    intro u h0 h1u k' c' X'
    have cl := hc.estimates F c.s₀ _ hF hs₀ hsA (hflowc u h0 h1u)
    exact ((cl.coordinates _ hb).1 k' c' X').contDiffAt
  have hbd' : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c' : Fin l → F.Site F.top × Fin 4) (X' : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors X' →
      ‖bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i))
        (expFlow Bf (uniformField F F.top) u) c' X'‖ ≤ c.Kk l := by
    intro u h0 h1u l c' X' hl1 _ hX'
    have hd := (hall F c.s₀ _ hF hs₀ le_rfl (hflowc u h0 h1u)).2.2.1 _ hb l c' X' hl1 hX'
    refine hd.trans ?_
    have hκ0 : 0 ≤ c.κ₂ := by linarith
    have he1 : Real.exp (-(c.κ₂ * (bondListDistance (enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth)) c' : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ c.κ₂ * (bondListDistance (enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth)) c' : ℝ) := by positivity
        linarith)
    exact mul_le_of_le_one_right (hKk l).le he1
  have h3 := hfl imaginaryQuaternions F F.top (finiteCells F ×ˢ Finset.univ)
    (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i)) (uniformField F F.top) Bf c.Kk hmem
    (fun l => (hKk l).le) hsm hbd' 1 ![(ez, ei)] ![X] (by norm_num) hX1
  have h4 := sum_norm_cutoffLog_le hlog hR16 hs0.le hs1 hs V Y hn
  have h5 : C₀ * (c.Kk 1 + c.Kk 2 + c.Kk 3) * ∑ b ∈ finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)), ‖Bf b.1 b.2‖ ≤ ε / 2 := by
    have h6 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC₀ hMs)
    refine h6.trans ?_
    have e : C₀ * (c.Kk 1 + c.Kk 2 + c.Kk 3) * (4 * (2 * (R : ℝ) + 1) ^ 4 * (6 * R * s)) = N₀ * s := by
      rw [hN₀]; ring
    rw [e]
    exact mul_le_half_of_scaled hs0 c3
  have h7 := norm_sub_le_norm_sub_add_norm_sub
    (bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i)) V ![(ez, ei)] ![X])
    (bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i))
      (expFlow Bf (uniformField F F.top) 1) ![(ez, ei)] ![X])
    (bondDeriv (torusCoordinate a c.ρA ((cellCentre F.depth z + siteOfCoords F.depth h₀ : F.Site F.depth), i)) (uniformField F F.top)
      ![(ez, ei)] ![X])
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
