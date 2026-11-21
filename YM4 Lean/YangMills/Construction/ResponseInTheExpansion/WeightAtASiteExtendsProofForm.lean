import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.ResponseInTheExpansion.WeightAtASiteExtends
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings BlockOffsets BlockAverages
namespace WeightExtension
def blockOffsets (L : ℕ) : ℕ → Finset (Fin 4 → ℤ)
  | 0 => {0}
  | t + 1 => (centredCube L ×ˢ blockOffsets L t).image fun p => (fun i => (L : ℤ) ^ t * p.1 i) + p.2
theorem two_mul_abs_le_of_mem_centredCube {L : ℕ} (hL : Odd L) {a : Fin 4 → ℤ} (ha : a ∈ centredCube L) (i : Fin 4) :
    2 * |a i| ≤ (L : ℤ) - 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellSums.two_mul_abs_le_of_mem_centredCube <;> assumption
theorem two_mul_abs_le_of_mem_blockOffsets {L : ℕ} (hL : Odd L) (hL1 : 1 ≤ L) : ∀ (t : ℕ) {v : Fin 4 → ℤ},
    v ∈ blockOffsets L t → ∀ i, 2 * |v i| ≤ (L : ℤ) ^ t - 1
  | 0, v, hv, i => by
    have : v = 0 := Finset.mem_singleton.mp hv
    simp [this]
  | t + 1, v, hv, i => by
    obtain ⟨⟨a, w⟩, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ha, hw⟩ := Finset.mem_product.mp hp
    have h1 := two_mul_abs_le_of_mem_centredCube hL ha i
    have h2 := two_mul_abs_le_of_mem_blockOffsets hL hL1 t hw i
    have hpow : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    have h3 : |(L : ℤ) ^ t * a i + w i| ≤ (L : ℤ) ^ t * |a i| + |w i| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hpow]
    have h4 : (L : ℤ) ^ t * (2 * |a i|) ≤ (L : ℤ) ^ t * ((L : ℤ) - 1) := mul_le_mul_of_nonneg_left h1 hpow
    change 2 * |(L : ℤ) ^ t * a i + w i| ≤ _
    rw [pow_succ]
    nlinarith
variable {L : ℕ} [NeZero L]
theorem mem_sitesInBlocks_iff {n : ℕ} [NeZero n] (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.SharedProofs.p74636 <;> assumption
theorem intCast_pow_mul_cast (t N : ℕ) [NeZero N] (a : ℤ) :
    (((L : ℤ) ^ t * (((a : ZMod N)).cast : ℤ) : ℤ) : ZMod (N * L ^ t)) = (((L : ℤ) ^ t * a : ℤ) : ZMod (N * L ^ t)) := by
  have h : (((((a : ZMod N)).cast : ℤ) : ℤ) : ZMod N) = (a : ZMod N) := by simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨k, ?_⟩
  push_cast
  have : (L : ℤ) ^ t * a - (L : ℤ) ^ t * (((a : ZMod N)).cast : ℤ) = (L : ℤ) ^ t * (a - (((a : ZMod N)).cast : ℤ)) := by
    ring
  rw [this, hk]
  ring
theorem fineCentre_fineSite (t n : ℕ) [NeZero n] (Y : TorusSite n) (a : Fin 4 → ℤ) :
    fineCentre L t (fineSite L Y 0 a : TorusSite (n * L)) =
      ((fineCentre L (t + 1) Y : TorusSite (fineSide L (t + 1) n)) : TorusSite (fineSide L t (n * L))) +
        siteOfInt (fun i => (L : ℤ) ^ t * a i) := by
  funext i
  have hs : fineSide L t (n * L) = (n * L) * L ^ t := fineSide_eq L t (n * L)
  have transfer : ∀ (S : ℕ) (e : S = (n * L) * L ^ t) (a b : ℤ),
      ((a : ZMod ((n * L) * L ^ t)) = (b : ZMod ((n * L) * L ^ t))) → ((a : ZMod S) = (b : ZMod S)) := by
    intro S e a b h
    subst e
    exact h
  change ((((L : ℤ) ^ t * (((fineSite L Y 0 a i : ZMod (n * L))).cast : ℤ) : ℤ)) : ZMod (fineSide L t (n * L))) =
    (((L : ℤ) ^ (t + 1) * (((Y i)).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) +
      (((L : ℤ) ^ t * a i : ℤ) : ZMod (fineSide L t (n * L)))
  rw [← Int.cast_add]
  refine transfer _ hs _ _ ?_
  have e : (fineSite L Y 0 a i : ZMod (n * L)) = (((L : ℤ) * (((Y i).cast : ℤ) + 0) + a i : ℤ) : ZMod (n * L)) := rfl
  rw [e, intCast_pow_mul_cast t (n * L)]
  congr 1
  ring
theorem fineBlock_eq_image (hL : Odd L) : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n),
    fineBlock L t n y = (blockOffsets L t).image fun v => fineCentre L t y + siteOfInt v
  | 0, n, _, y => by
    have h0 : fineCentre L 0 y = y := by
      funext i
      change (((L : ℤ) ^ 0 * (((y i)).cast : ℤ) : ℤ) : ZMod n) = y i
      simp
    change ({y} : Finset (TorusSite n)) = _
    simp only [blockOffsets, Finset.image_singleton]
    have : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (fineSide L 0 n)) = 0 := siteOfInt_zero_offset
    rw [this, add_zero, h0]
    rfl
  | t + 1, n, _, Y => by
    classical
    have hmem : ∀ x : TorusSite (fineSide L t (n * L)),
        x ∈ (sitesInBlocks L {Y}).biUnion (fun y => fineBlock L t (n * L) y) ↔
          ∃ v ∈ blockOffsets L (t + 1),
            ((fineCentre L (t + 1) Y : TorusSite (fineSide L (t + 1) n)) : TorusSite (fineSide L t (n * L))) +
              siteOfInt v = x := by
      intro x
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨y, hy, hx⟩
        have hb : parentBlock L y = Y := Finset.mem_singleton.mp ((mem_sitesInBlocks_iff _ _).mp hy)
        obtain ⟨a, ha, rfl⟩ := exists_fineSite_of_parentBlock hL Y y hb
        rw [fineBlock_eq_image hL t (n * L)] at hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        refine ⟨(fun i => (L : ℤ) ^ t * a i) + w, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(a, w), Finset.mem_product.mpr ⟨ha, hw⟩, rfl⟩
        · rw [fineCentre_fineSite, BlockOffsets.siteOfInt_add]
          exact (add_assoc _ _ _).symm
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨⟨a, w⟩, hp, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨ha, hw⟩ := Finset.mem_product.mp hp
        refine ⟨fineSite L Y 0 a, (mem_sitesInBlocks_iff _ _).mpr (Finset.mem_singleton.mpr ?_), ?_⟩
        · rw [parentBlock_fineSite hL Y 0 a ha, siteOfInt_zero_offset, add_zero]
        · rw [fineBlock_eq_image hL t (n * L)]
          refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
          rw [fineCentre_fineSite, BlockOffsets.siteOfInt_add]
          exact add_assoc _ _ _
    refine Finset.ext fun x => ?_
    rw [Finset.mem_image]
    exact hmem x
def plaquetteShift (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
theorem doubledBarycentre_siteOfInt {m : ℕ} [NeZero m] (u : Fin 4 → ℤ) (μ ν i : Fin 4) :
    doubledBarycentre ((siteOfInt u : TorusSite m), μ, ν) i = ((2 * u i + plaquetteShift μ ν i : ℤ) : ZMod (2 * m)) := by
  have h : ((((siteOfInt u : TorusSite m) i).val : ℤ) : ZMod m) = (u i : ZMod m) := by
    simp [siteOfInt]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  change (((2 * ((siteOfInt u : TorusSite m) i).val + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ)) :
    ZMod (2 * m)) = _
  rw [← Int.cast_natCast]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨k, ?_⟩
  unfold plaquetteShift
  push_cast
  linear_combination 2 * hk
def doubledGap (z₁ z₂ : Fin 4 → ℤ) (μ₁ ν₁ μ₂ ν₂ i : Fin 4) : ℤ :=
  2 * (z₁ i - z₂ i) + plaquetteShift μ₁ ν₁ i - plaquetteShift μ₂ ν₂ i
theorem supDist_doubledBarycentre_eq_sup {m : ℕ} [NeZero m] (C z₁ z₂ : Fin 4 → ℤ) (μ₁ ν₁ μ₂ ν₂ : Fin 4)
    (hs : ∀ i, |doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i| < m) :
    supDist (doubledBarycentre ((siteOfInt C + siteOfInt z₁ : TorusSite m), μ₁, ν₁))
        (doubledBarycentre ((siteOfInt C + siteOfInt z₂ : TorusSite m), μ₂, ν₂)) =
      Finset.univ.sup fun i => (doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i).natAbs := by
  unfold supDist
  congr 1
  funext i
  rw [← siteOfInt_add, ← siteOfInt_add, doubledBarycentre_siteOfInt, doubledBarycentre_siteOfInt]
  have e : (((2 * (C + z₁) i + plaquetteShift μ₁ ν₁ i : ℤ) : ZMod (2 * m)) -
      ((2 * (C + z₂) i + plaquetteShift μ₂ ν₂ i : ℤ) : ZMod (2 * m))) =
      ((doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i : ℤ) : ZMod (2 * m)) := by
    rw [← Int.cast_sub]
    congr 1
    unfold doubledGap
    simp only [Pi.add_apply]
    ring
  rw [e]
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hb := abs_lt.mp (hs i)
  have : (((doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i : ℤ) : ZMod (2 * m))).valMinAbs = doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i := by
    refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_⟩
    push_cast
    constructor <;> linarith [hb.1, hb.2]
  rw [this]
theorem eq_of_plaquetteShift_sub_even : ∀ μ₁ ν₁ μ₂ ν₂ : Fin 4, μ₁ < ν₁ → μ₂ < ν₂ →
    (∀ i, (plaquetteShift μ₁ ν₁ i - plaquetteShift μ₂ ν₂ i) % 2 = 0) → μ₁ = μ₂ ∧ ν₁ = ν₂ := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.axes_eq_of_parity <;> assumption
theorem plaquetteShift_bounds (μ ν i : Fin 4) : 0 ≤ plaquetteShift μ ν i ∧ plaquetteShift μ ν i ≤ 2 := by
  unfold plaquetteShift
  split_ifs <;> simp
theorem eq_of_doubledGap_eq_zero {z₁ z₂ : Fin 4 → ℤ} {μ₁ ν₁ μ₂ ν₂ : Fin 4}
    (h : ∀ i, doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i = 0) (h₁ : μ₁ < ν₁) (h₂ : μ₂ < ν₂) :
    z₁ = z₂ ∧ μ₁ = μ₂ ∧ ν₁ = ν₂ := by
  have hb : ∀ i, (plaquetteShift μ₁ ν₁ i - plaquetteShift μ₂ ν₂ i) % 2 = 0 := by
    intro i
    have := h i
    unfold doubledGap at this
    omega
  obtain ⟨rfl, rfl⟩ := eq_of_plaquetteShift_sub_even _ _ _ _ h₁ h₂ hb
  refine ⟨funext fun i => ?_, rfl, rfl⟩
  have := h i
  unfold doubledGap at this
  omega
section Pair
variable {t n n' : ℕ} [NeZero n] [NeZero n']
theorem exists_offset_of_isPlaquetteAt (hL : Odd L) (y : TorusSite n) (y' : TorusSite n')
    (p : TorusPlaquette (fineSide L t n')) (hp : IsPlaquetteAt L t y' p) :
    ∃ z : Fin 4 → ℤ, p.1 = fineCentre L t y' + siteOfInt z ∧ (∀ i, 2 * |z i| ≤ (L : ℤ) ^ t + 1) ∧
      IsPlaquetteAt L t y (fineCentre L t y + siteOfInt z, p.2.1, p.2.2) := by
  classical
  obtain ⟨x, μ, ν⟩ := p
  obtain ⟨hlt, c, hc, hb⟩ := hp
  rw [fineBlock_eq_image hL] at hb
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  have hbd := two_mul_abs_le_of_mem_blockOffsets hL (Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)) t hv
  have main : ∀ ε : Fin 4 → ℤ, (∀ i, |ε i| ≤ 1) → x + siteOfInt ε = fineCentre L t y' + siteOfInt v →
      (∀ w : TorusSite (fineSide L t n), w + siteOfInt ε ∈ plaquetteVertices w μ ν) →
      ∃ z : Fin 4 → ℤ, x = fineCentre L t y' + siteOfInt z ∧ (∀ i, 2 * |z i| ≤ (L : ℤ) ^ t + 1) ∧
        IsPlaquetteAt L t y (fineCentre L t y + siteOfInt z, μ, ν) := by
    intro ε hε e hmem
    have hsplit : ∀ {m : ℕ} [NeZero m] (a : TorusSite m), a + siteOfInt (v - ε) + siteOfInt ε = a + siteOfInt v := by
      intro m _ a
      rw [add_assoc, ← siteOfInt_add, sub_add_cancel]
    refine ⟨v - ε, ?_, fun i => ?_, hlt, _, hmem _, ?_⟩
    · have h1 := hsplit (fineCentre L t y')
      rw [← e] at h1
      exact (add_right_cancel h1).symm
    · have h1 := hbd i
      have h2 := hε i
      have h3 : |(v - ε) i| ≤ |v i| + |ε i| := by
        simpa using abs_sub (v i) (ε i)
      linarith
    · rw [hsplit, fineBlock_eq_image hL]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hone : ∀ a : Fin 4, ∀ i, |(Pi.single a 1 : Fin 4 → ℤ) i| ≤ 1 := by
    intro a i
    by_cases h : i = a
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with e | e | e | e
  · refine main 0 (fun i => by simp) ?_ ?_
    · rw [siteOfInt_zero_offset, add_zero]
      exact e.symm
    · intro w
      rw [siteOfInt_zero_offset, add_zero]
      simp [plaquetteVertices]
  · refine main (Pi.single μ 1) (hone μ) ?_ ?_
    · rw [← unitStep_eq_siteOfInt]
      exact e.symm
    · intro w
      rw [← unitStep_eq_siteOfInt]
      simp [plaquetteVertices]
  · refine main (Pi.single ν 1) (hone ν) ?_ ?_
    · rw [← unitStep_eq_siteOfInt]
      exact e.symm
    · intro w
      rw [← unitStep_eq_siteOfInt]
      simp [plaquetteVertices]
  · refine main (Pi.single μ 1 + Pi.single ν 1) (fun i => ?_) ?_ ?_
    · by_cases h1 : i = μ
      · subst h1
        have : i ≠ ν := hlt.ne
        simp [Pi.single_eq_of_ne this]
      · by_cases h2 : i = ν
        · subst h2
          simp [Pi.single_eq_of_ne h1]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    · rw [siteOfInt_add, ← unitStep_eq_siteOfInt, ← unitStep_eq_siteOfInt, ← add_assoc]
      exact e.symm
    · intro w
      rw [siteOfInt_add, ← unitStep_eq_siteOfInt, ← unitStep_eq_siteOfInt, ← add_assoc]
      simp [plaquetteVertices]
theorem abs_doubledGap_lt (hn : 8 ≤ n) {z₁ z₂ : Fin 4 → ℤ} (μ₁ ν₁ μ₂ ν₂ : Fin 4)
    (b₁ : ∀ i, 2 * |z₁ i| ≤ (L : ℤ) ^ t + 1) (b₂ : ∀ i, 2 * |z₂ i| ≤ (L : ℤ) ^ t + 1) (i : Fin 4) :
    |doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i| < (fineSide L t n : ℤ) := by
  rw [fineSide_eq]
  push_cast
  have hL1 : (1 : ℤ) ≤ (L : ℤ) ^ t := by
    have : 1 ≤ L ^ t := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
    exact_mod_cast this
  have hn8 : (8 : ℤ) ≤ n := by exact_mod_cast hn
  have h1 := b₁ i
  have h2 := b₂ i
  have c1 := plaquetteShift_bounds μ₁ ν₁ i
  have c2 := plaquetteShift_bounds μ₂ ν₂ i
  have a1 := abs_le.mp (le_refl |z₁ i|)
  have a2 := abs_le.mp (le_refl |z₂ i|)
  have hm : 8 * (L : ℤ) ^ t ≤ (n : ℤ) * (L : ℤ) ^ t := mul_le_mul_of_nonneg_right hn8 (by positivity)
  unfold doubledGap
  rw [abs_lt]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, c1.1, c1.2, c2.1, c2.2]
theorem barycentreDist_translate (hn : 8 ≤ n) (hn' : 8 ≤ n') (y : TorusSite n) (y' : TorusSite n')
    {z₁ z₂ : Fin 4 → ℤ} (μ₁ ν₁ μ₂ ν₂ : Fin 4)
    (b₁ : ∀ i, 2 * |z₁ i| ≤ (L : ℤ) ^ t + 1) (b₂ : ∀ i, 2 * |z₂ i| ≤ (L : ℤ) ^ t + 1) :
    barycentreDist L t ((fineCentre L t y + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n))
        (fineCentre L t y + siteOfInt z₂, μ₂, ν₂) =
      barycentreDist L t ((fineCentre L t y' + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n'))
        (fineCentre L t y' + siteOfInt z₂, μ₂, ν₂) := by
  unfold barycentreDist
  have e₁ := supDist_doubledBarycentre_eq_sup (m := fineSide L t n) (fun i => (L : ℤ) ^ t * ((y i).cast : ℤ))
    z₁ z₂ μ₁ ν₁ μ₂ ν₂ (abs_doubledGap_lt hn _ _ _ _ b₁ b₂)
  have e₂ := supDist_doubledBarycentre_eq_sup (m := fineSide L t n') (fun i => (L : ℤ) ^ t * ((y' i).cast : ℤ))
    z₁ z₂ μ₁ ν₁ μ₂ ν₂ (abs_doubledGap_lt hn' _ _ _ _ b₁ b₂)
  have e₃ : supDist (doubledBarycentre ((fineCentre L t y + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n)))
      (doubledBarycentre ((fineCentre L t y + siteOfInt z₂, μ₂, ν₂) : TorusPlaquette (fineSide L t n))) =
    supDist (doubledBarycentre ((fineCentre L t y' + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n')))
      (doubledBarycentre ((fineCentre L t y' + siteOfInt z₂, μ₂, ν₂) : TorusPlaquette (fineSide L t n'))) :=
    e₁.trans e₂.symm
  rw [e₃]
theorem eq_of_barycentreDist_eq_zero (hn : 8 ≤ n) (y : TorusSite n) {z₁ z₂ : Fin 4 → ℤ} {μ₁ ν₁ μ₂ ν₂ : Fin 4}
    (h₁ : μ₁ < ν₁) (h₂ : μ₂ < ν₂)
    (b₁ : ∀ i, 2 * |z₁ i| ≤ (L : ℤ) ^ t + 1) (b₂ : ∀ i, 2 * |z₂ i| ≤ (L : ℤ) ^ t + 1)
    (hd : barycentreDist L t ((fineCentre L t y + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n))
        (fineCentre L t y + siteOfInt z₂, μ₂, ν₂) = 0) : z₁ = z₂ ∧ μ₁ = μ₂ ∧ ν₁ = ν₂ := by
  refine eq_of_doubledGap_eq_zero (fun i => ?_) h₁ h₂
  unfold barycentreDist at hd
  have hL : (0 : ℝ) < 2 * (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h0 : supDist (doubledBarycentre ((fineCentre L t y + siteOfInt z₁, μ₁, ν₁) : TorusPlaquette (fineSide L t n)))
      (doubledBarycentre ((fineCentre L t y + siteOfInt z₂, μ₂, ν₂) : TorusPlaquette (fineSide L t n))) = 0 := by
    rcases div_eq_zero_iff.mp hd with h | h
    · exact_mod_cast h
    · exact absurd h hL.ne'
  have e₁ := supDist_doubledBarycentre_eq_sup (m := fineSide L t n) (fun i => (L : ℤ) ^ t * ((y i).cast : ℤ))
    z₁ z₂ μ₁ ν₁ μ₂ ν₂ (abs_doubledGap_lt hn _ _ _ _ b₁ b₂)
  have e₂ : (Finset.univ.sup fun i => (doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i).natAbs) = 0 := e₁.symm.trans h0
  have h3 : (doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i).natAbs ≤ 0 := by
    rw [← e₂]
    exact Finset.le_sup (f := fun i => (doubledGap z₁ z₂ μ₁ ν₁ μ₂ ν₂ i).natAbs) (Finset.mem_univ i)
  omega
end Pair
section Norm
variable {t : ℕ} {m : ℕ} [NeZero m]
theorem weightNorm_nonneg (w : PlaquetteWeight m) : 0 ≤ weightNorm L t w :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
theorem abs_le_weightNorm (w : PlaquetteWeight m) (p : TorusPlaquette m) (hp : p.2.1 < p.2.2) :
    |w p| ≤ weightNorm L t w := by
  refine le_trans ?_ (le_max_left _ _)
  exact le_ciSup (f := fun p : OrientedPlaquette m => |w p.1|) (Set.finite_range _).bddAbove ⟨p, hp⟩
theorem lipschitz_quotient_le_weightNorm (w : PlaquetteWeight m) (p q : TorusPlaquette m) (hp : p.2.1 < p.2.2)
    (hq : q.2.1 < q.2.2) : |w p - w q| / barycentreDist L t p q ≤ weightNorm L t w := by
  refine le_trans ?_ (le_max_right _ _)
  exact le_ciSup (f := fun pp : OrientedPlaquette m × OrientedPlaquette m =>
      |w pp.1.1 - w pp.2.1| / barycentreDist L t pp.1.1 pp.2.1)
    (Set.finite_range _).bddAbove (⟨p, hp⟩, ⟨q, hq⟩)
theorem barycentreDist_nonneg (p q : TorusPlaquette m) : 0 ≤ barycentreDist L t p q := by
  unfold barycentreDist
  positivity
theorem barycentreDist_self (p : TorusPlaquette m) : barycentreDist L t p p = 0 := by
  unfold barycentreDist
  rw [supDist_self]
  simp
theorem barycentreDist_comm (p q : TorusPlaquette m) : barycentreDist L t p q = barycentreDist L t q p := by
  unfold barycentreDist
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
theorem barycentreDist_triangle (p q r : TorusPlaquette m) :
    barycentreDist L t p r ≤ barycentreDist L t p q + barycentreDist L t q r := by
  unfold barycentreDist
  rw [← add_div]
  have hL : (0 : ℝ) < 2 * (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine div_le_div_of_nonneg_right ?_ hL.le
  exact_mod_cast supDist_triangle _ _ _
theorem abs_clamp_sub_le {M a b : ℝ} (hM : 0 ≤ M) :
    |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith
end Norm
end WeightExtension
open WeightExtension in
theorem agreeingWeightExtension : agreeingWeightExtensionStatement := by
  intro L t _ n n' _ _ y y' w w' hL hn hn' hW
  classical
  set M := weightNorm L t w with hMdef
  have hM0 : 0 ≤ M := weightNorm_nonneg w
  set A' : Finset (TorusPlaquette (fineSide L t n')) := Finset.univ.filter (IsPlaquetteAt L t y') with hA'
  have hT : ∀ p ∈ A', p.2.1 < p.2.2 ∧ ∃ z : Fin 4 → ℤ, p = (fineCentre L t y' + siteOfInt z, p.2.1, p.2.2) ∧
      (∀ i, 2 * |z i| ≤ (L : ℤ) ^ t + 1) ∧
      w' p = w (fineCentre L t y + siteOfInt z, p.2.1, p.2.2) := by
    intro p hp
    have hat : IsPlaquetteAt L t y' p := (Finset.mem_filter.mp hp).2
    obtain ⟨z, e, b, ha⟩ := exists_offset_of_isPlaquetteAt hL y y' p hat
    refine ⟨hat.1, z, Prod.ext e rfl, b, ?_⟩
    have hpow : (1 : ℤ) ≤ (L : ℤ) ^ t := by
      have : 1 ≤ L ^ t := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
      exact_mod_cast this
    have hw := hW z p.2.1 p.2.2 (fun i => by have := b i; omega) ha
    have e' : ((fineCentre L t y' + siteOfInt z, p.2.1, p.2.2) : TorusPlaquette (fineSide L t n')) = p :=
      Prod.ext e.symm rfl
    rw [hw, e']
  have hsz : ∀ p ∈ A', |w' p| ≤ M := by
    intro p hp
    obtain ⟨hlt, z, -, -, e⟩ := hT p hp
    rw [e]
    exact abs_le_weightNorm w _ hlt
  have hlip : ∀ p ∈ A', ∀ q ∈ A', |w' p - w' q| ≤ M * barycentreDist L t p q := by
    intro p hp q hq
    obtain ⟨hlt, z, e₁, b₁, v₁⟩ := hT p hp
    obtain ⟨hlt', z', e₂, b₂, v₂⟩ := hT q hq
    have hd := barycentreDist_translate hn hn' y y' p.2.1 p.2.2 q.2.1 q.2.2 b₁ b₂
    rw [← e₁, ← e₂] at hd
    rw [← hd, v₁, v₂]
    set a : TorusPlaquette (fineSide L t n) := (fineCentre L t y + siteOfInt z, p.2.1, p.2.2) with ha
    set b : TorusPlaquette (fineSide L t n) := (fineCentre L t y + siteOfInt z', q.2.1, q.2.2) with hb
    by_cases h0 : barycentreDist L t a b = 0
    · obtain ⟨rfl, e3, e4⟩ := eq_of_barycentreDist_eq_zero hn y hlt hlt' b₁ b₂ h0
      have : a = b := by
        rw [ha, hb, e3, e4]
      rw [this, sub_self, abs_zero]
      exact mul_nonneg hM0 (barycentreDist_nonneg _ _)
    · have hpos : 0 < barycentreDist L t a b := lt_of_le_of_ne (barycentreDist_nonneg _ _) (Ne.symm h0)
      exact (div_le_iff₀ hpos).mp (lipschitz_quotient_le_weightNorm w a b hlt hlt')
  by_cases hne : A'.Nonempty
  · let g : TorusPlaquette (fineSide L t n') → ℝ :=
      fun p => A'.inf' hne fun a => w' a + M * barycentreDist L t p a
    have hg : ∀ p q, g p ≤ g q + M * barycentreDist L t p q := by
      intro p q
      have : g p - M * barycentreDist L t p q ≤ g q := by
        refine Finset.le_inf' _ _ fun a ha => ?_
        have h1 : g p ≤ w' a + M * barycentreDist L t p a := Finset.inf'_le _ ha
        have h2 := barycentreDist_triangle (L := L) (t := t) p q a
        have h3 := mul_le_mul_of_nonneg_left h2 hM0
        have e : barycentreDist L t q a = barycentreDist L t q a := rfl
        linarith
      linarith
    refine ⟨fun p => max (-M) (min M (g p)), fun p hp => ?_, max_le ?_ ?_⟩
    · have hpA : p ∈ A' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      have e : g p = w' p := by
        refine le_antisymm ?_ (Finset.le_inf' _ _ fun a ha => ?_)
        · have : g p ≤ w' p + M * barycentreDist L t p p := Finset.inf'_le _ hpA
          rw [barycentreDist_self, mul_zero, add_zero] at this
          exact this
        · have := abs_le.mp (hlip p hpA a ha)
          linarith [this.2]
      have hb := abs_le.mp (hsz p hpA)
      dsimp only
      rw [e, min_eq_right hb.2, max_eq_right hb.1]
    · refine Real.iSup_le (fun p => ?_) hM0
      rw [abs_le]
      refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    · refine Real.iSup_le (fun pp => ?_) hM0
      refine div_le_of_le_mul₀ (barycentreDist_nonneg _ _) hM0 ?_
      refine (abs_clamp_sub_le hM0).trans ?_
      rw [abs_le]
      have h1 := hg pp.1.1 pp.2.1
      have h2 := hg pp.2.1 pp.1.1
      rw [barycentreDist_comm (L := L) (t := t) pp.2.1 pp.1.1] at h2
      constructor <;> linarith
  · refine ⟨fun _ => 0, fun p hp => absurd ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩ hne, max_le ?_ ?_⟩
    · refine Real.iSup_le (fun p => ?_) hM0
      simpa using hM0
    · refine Real.iSup_le (fun pp => ?_) hM0
      simpa using hM0
end YangMills.Construction.WeightedResponses
end
