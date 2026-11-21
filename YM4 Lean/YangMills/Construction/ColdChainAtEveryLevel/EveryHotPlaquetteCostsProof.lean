import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastActionProof
import YangMills.Construction.ColdChainAtEveryLevel.EveryHotPlaquetteCosts
import YangMills.Construction.ColdChainAtEveryLevel.PlaquetteUnderAFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.HotPlaquetteCost
variable {F : BlockFrame}
def partialChainAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (j : ℕ) : ℝ :=
  wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c
theorem exists_chain_below (hV : minimalChainExistenceStatement) (F : BlockFrame) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) : ∀ (j : ℕ) (W : F.GaugeField j), ∃ X : F.FieldChain, X j = W ∧
      partialChainAction a S X j = minimalAction a S j W := by
  intro j
  induction j with
  | zero =>
    intro W
    refine ⟨fun i => if h : i = 0 then h ▸ W else fun _ _ => 1, by simp, ?_⟩
    simp [partialChainAction, minimalAction]
  | succ j ih =>
    intro W
    obtain ⟨W', hW', -⟩ := (hV F a S ha).2.2.1 j W
    obtain ⟨X, hX, htot⟩ := ih W'
    refine ⟨Function.update X (j + 1) W, by simp, ?_⟩
    have e0 : Function.update X (j + 1) W 0 = X 0 := by
      rw [Function.update_of_ne (by omega)]
    have e1 : Function.update X (j + 1) W j = W' := by
      rw [Function.update_of_ne (by omega), hX]
    have e2 : Function.update X (j + 1) W (j + 1) = W := by simp
    have e3 : ∀ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
        blockFit (Function.update X (j + 1) W i) (Function.update X (j + 1) W (i + 1)) c =
        ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    unfold partialChainAction
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e3, e0, e1, e2, ← hW']
    unfold blockEnergy
    rw [← htot, mul_add]
    unfold partialChainAction
    ring
theorem exists_chain_through (hV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) : ∃ X : F.FieldChain, X F.depth = W ∧ X F.top = V ∧
      chainAction a S X = blockEnergy a S F.depth W V := by
  obtain ⟨X, hX, htot⟩ := exists_chain_below hV F a ha S F.depth W
  have hn : F.top = F.depth + 1 := rfl
  refine ⟨Function.update X F.top V, ?_, by simp, ?_⟩
  · rw [Function.update_of_ne (by omega), hX]
  · have e0 : Function.update X F.top V 0 = X 0 := by
      rw [Function.update_of_ne (by omega)]
    have e1 : Function.update X F.top V F.depth = W := by
      rw [Function.update_of_ne (by omega), hX]
    have e2 : Function.update X F.top V (F.depth + 1) = V := by
      show Function.update X F.top V F.top = V
      simp
    have e3 : ∀ i ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (i + 1),
        blockFit (Function.update X F.top V i) (Function.update X F.top V (i + 1)) c =
        ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    unfold chainAction blockEnergy
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e3, e0, e1, e2, ← htot]
    unfold partialChainAction
    ring
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
theorem plaquetteDefect_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (gaugeTransform γ X) p = plaquetteDefect X p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
theorem card_le_of_cellSupDist_le (b : F.Cell) (r : ℕ) [DecidableEq F.Cell] (A : Finset F.Cell)
    (hA : ∀ z ∈ A, cellSupDist z b ≤ r) : A.card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.card_le_of_cellSupDist_le <;> assumption
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_mem {S : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem fst_mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S j) : p.1 ∈ sitesOfCells S j := by
  have := (Finset.mem_filter.1 hp).1
  exact (Finset.mem_product.1 this).1
theorem card_plaquettes_at_cell_le (hL : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell)
    [DecidableEq (F.Site F.depth × Fin 4 × Fin 4)]
    (H : Finset (F.Site F.depth × Fin 4 × Fin 4)) (hH : H ⊆ innerPlaquettes S F.depth)
    (hz : ∀ p ∈ H, enclosingCell p.1 = z) : H.card ≤ (centredCube F.blockSide).card * 16 := by
  classical
  have hsub : H ⊆ ((centredCube F.blockSide) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).image
      (fun q => ((cellCentre F.depth z + siteOfCoords F.depth q.1 : F.Site F.depth), q.2.1, q.2.2)) := by
    intro p hp
    have h1 := fst_mem_sitesOfCells (hH hp)
    obtain ⟨z', hz', hxz⟩ := Finset.mem_biUnion.1 h1
    obtain ⟨h, hh, hpe⟩ := Finset.mem_image.1 hxz
    have e1 : F.top - F.depth = 1 := by
      show F.depth + 1 - F.depth = 1
      omega
    have hc : z' = z := by
      have := hz p hp
      rw [← hpe, enclosingCell_cellCentre_add hL z' h hh] at this
      exact this
    subst hc
    refine Finset.mem_image.2 ⟨(h, p.2.1, p.2.2), Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · rw [e1, pow_one] at hh
      exact hh
    · obtain ⟨x, μ, ν⟩ := p
      simp only at hpe ⊢
      rw [hpe]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Finset.card_product]
theorem relativeEnergy_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) : 0 ≤ relativeEnergy a S z W kW X k Γ := by apply _root_.YangMills.Construction.BlockAverages.relativeEnergy_nonneg_of_nonneg <;> assumption
theorem hot_count_bound_arith (cg c P σ b A B2 Hc E Δ : ℝ) (hcg : 0 ≤ cg) (hP : 0 ≤ P) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hb : 0 ≤ b) (hB2 : 0 ≤ B2) (hH : Hc ≤ P * (A + B2)) (hA : A ≤ 201 ^ 4 * b) (κ : ℝ)
    (hκ : 0 < κ) (hE : B2 * (κ * σ ^ 2) ≤ E) (hex : c * (b + E) ≤ Δ) (hc : 0 ≤ c)
    (h1 : cg * (P * 201 ^ 4) ≤ c) (h2 : cg * P ≤ c * κ) : cg * σ ^ 2 * Hc ≤ Δ := by
  have hs2 : σ ^ 2 ≤ 1 := by nlinarith
  have t0 : cg * σ ^ 2 * Hc ≤ cg * σ ^ 2 * (P * (A + B2)) := mul_le_mul_of_nonneg_left hH (by positivity)
  have t1 : P * (A + B2) ≤ P * (201 ^ 4 * b + B2) :=
    mul_le_mul_of_nonneg_left (by linarith) hP
  have t2 : cg * σ ^ 2 * (P * (A + B2)) ≤ cg * σ ^ 2 * (P * (201 ^ 4 * b + B2)) :=
    mul_le_mul_of_nonneg_left t1 (by positivity)
  have t3 : cg * σ ^ 2 * (P * 201 ^ 4 * b) ≤ c * b := by
    have u1 : cg * σ ^ 2 * (P * 201 ^ 4) ≤ cg * (P * 201 ^ 4) := by
      have : 0 ≤ cg * (P * 201 ^ 4) := by positivity
      nlinarith
    have u2 := mul_le_mul_of_nonneg_right (u1.trans h1) hb
    nlinarith
  have t4 : cg * P * (B2 * σ ^ 2) ≤ c * E := by
    have u1 : cg * P * (B2 * σ ^ 2) ≤ c * κ * (B2 * σ ^ 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have u2 : c * (B2 * (κ * σ ^ 2)) ≤ c * E := mul_le_mul_of_nonneg_left hE hc
    nlinarith
  nlinarith
theorem hotPlaquetteCost (hC : coldTopCriticalChainStatement)
    (hT : criticalChainMinimalityStatement) (hVal : criticalValueEqMinimalActionStatement)
    (hP : pinnedGaugePlaquetteBoundStatement) (hLV : minimalChainExistenceStatement)
    (hFr : gaugedChainLowerBoundStatement) : hotPlaquetteCostStatement := by
  classical
  intro a ha
  obtain ⟨θ, del, Ca, hθ, hθ8, hd, hd8, hCa, L₁, hC'⟩ := hC a ha
  obtain ⟨L₂, hT'⟩ := hT a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₃, hV'⟩ := hVal a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₄, hP'⟩ := hP a θ del Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨max L₁ (max L₂ (max L₃ L₄)), fun L hL hge => ?_⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hge))
  have g4 : L₄ ≤ L := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge))
  obtain ⟨rL, sL, CL, hr, hsL, hCL, hc⟩ := hC' L hL g1
  obtain ⟨e0, σ8, C, c, he0, hσ8, hCc, hcpos, h8⟩ := hT' L hL g2 CL hCL
  obtain ⟨σ3, hσ3, hv⟩ := hV' L hL g3 CL hCL
  obtain ⟨σ4, C₂, hσ4, hC₂, hplq⟩ := hP' L hL g4 CL C hCL hCc
  set Pn : ℕ := (centredCube L).card * 16 with hPn
  set κ : ℝ := (7 / (8 * C₂)) ^ 2 with hκd
  have hκ : 0 < κ := by positivity
  have hPr : (0 : ℝ) ≤ (Pn : ℝ) := by positivity
  set cg : ℝ := c / ((Pn : ℝ) * 201 ^ 4 + (Pn : ℝ) / κ + 1) with hcgd
  have hden : 0 < (Pn : ℝ) * 201 ^ 4 + (Pn : ℝ) / κ + 1 := by positivity
  have hcg : 0 < cg := by positivity
  have c1 : cg * ((Pn : ℝ) * 201 ^ 4) ≤ c := by
    rw [hcgd, div_mul_eq_mul_div, div_le_iff₀ hden]
    have : 0 ≤ (Pn : ℝ) / κ := by positivity
    nlinarith
  have c2 : cg * (Pn : ℝ) ≤ c * κ := by
    rw [hcgd, div_mul_eq_mul_div, div_le_iff₀ hden]
    have e : (Pn : ℝ) / κ * κ = Pn := div_mul_cancel₀ _ hκ.ne'
    have h0 : 0 ≤ c * κ := by positivity
    have h1 : 0 ≤ (Pn : ℝ) * 201 ^ 4 := by positivity
    have : c * κ * ((Pn : ℝ) * 201 ^ 4 + (Pn : ℝ) / κ + 1) =
        c * κ * ((Pn : ℝ) * 201 ^ 4) + c * ((Pn : ℝ) / κ * κ) + c * κ := by ring
    rw [this, e]
    nlinarith
  set σA : ℝ := min (min sL σ8) (min σ3 (min σ4 1)) with hσAd
  have hσA : 0 < σA := lt_min (lt_min hsL hσ8) (lt_min hσ3 (lt_min hσ4 one_pos))
  have e1 : σA ≤ sL := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : σA ≤ σ8 := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : σA ≤ σ3 := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : σA ≤ σ4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : σA ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨σA, cg, hσA, hcg, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hLpos : 0 < F.blockSide := hLF.pos
  obtain ⟨U, -, -, hcrit, -, hsplit, -, hcold8, hq, hcm, hmis⟩ :=
    hc F m S hFL hamb hm hreg s V hs (hsσ.trans e1) hcold
  have hU : IsCriticalChainOverTop a θ del Ca CL s S V V U :=
    ⟨hcrit, hsplit, hq, hcm, fun j z hj => by rw [hFL]; exact hmis j z hj⟩
  have hU' : IsCriticalChainOverTop a θ del Ca CL s S V
      (rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V) U := by
    rw [rotatedField_zero]
    exact hU
  have hv0 : ∀ (y : F.Site F.top) (i : Fin 4), ‖(0 : imaginaryQuaternions)‖ ≤ s :=
    fun _ _ => by simpa using hs.le
  have hleast := (hv F m S hFL hamb hm hreg s V (fun _ _ => 0) hs (hsσ.trans e3) hcold hv0 U hU').1
  rw [rotatedField_zero] at hleast
  intro σ' h1 h2 W
  have hσ'0 : 0 < σ' := hs.trans_le h1
  obtain ⟨X, hXt, hXn, htot⟩ := exists_chain_through hLV a ha.le S W V
  have hXn' : X F.top = rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V := by
    rw [rotatedField_zero]; exact hXn
  obtain ⟨Γ, hfr, hex⟩ := h8 F m S hFL hamb hm hreg s V (fun _ _ => 0) hs (hsσ.trans e2) hcold hv0 U hU'
    X (fun _ _ => 1) hXn'
  rw [rotatedField_zero] at hfr hex
  have hft : gaugedChainAction a S X (fun _ _ => 1) = blockEnergy a S F.depth W V := by
    rw [(hFr F a S ha.le hLpos).2 X, htot]
  rw [hft, ← hleast] at hex
  set Bd := highEnergyCells a e0 S X (fun _ _ => 1) with hBd
  set Fr := cellsFarFromHighEnergy a e0 S X (fun _ _ => 1) with hFrd
  set D : F.Cell → ℝ := fun z => relativeEnergy a S z (chartChain (referenceFieldChain S V) U V)
    (chartGauge (referenceFieldChain S V) U) X (fun _ _ => 1) (Γ z) with hD
  set H := (innerPlaquettes S F.depth).filter fun p => σ' ≤ plaquetteDefect W p with hH
  have hcount : hotPlaquetteCount S F.depth σ' W = H.card := rfl
  set A := S.filter fun z => ∃ b ∈ Bd, cellSupDist z b ≤ 100 with hA
  set B2 := Fr.filter fun z => ∃ p ∈ H, enclosingCell p.1 = z with hB2
  have hcover : ∀ p ∈ H, enclosingCell p.1 ∈ A ∪ B2 := by
    intro p hp
    have hpS : p ∈ innerPlaquettes S F.depth := (Finset.mem_filter.1 hp).1
    have hz : enclosingCell p.1 ∈ S := enclosingCell_mem hLF (fst_mem_sitesOfCells hpS)
    by_cases hz' : enclosingCell p.1 ∈ Fr
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz', p, hp, rfl⟩)
    · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hz, ?_⟩)
      by_contra hno
      push Not at hno
      exact hz' (Finset.mem_filter.2 ⟨hz, fun y hy => hno y hy⟩)
  have hHcard : H.card ≤ Pn * (A ∪ B2).card := by
    refine Finset.card_le_mul_card_image_of_maps_to hcover Pn ?_
    intro z _
    have := card_plaquettes_at_cell_le hLF S z (H.filter fun p => enclosingCell p.1 = z)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 hp).2)
    rwa [hFL] at this
  have hAcard : A.card ≤ 201 ^ 4 * Bd.card := by
    have hsub : A ⊆ Bd.biUnion fun b => A.filter fun z => cellSupDist z b ≤ 100 := by
      intro z hz
      obtain ⟨b, hb, hzb⟩ := (Finset.mem_filter.1 hz).2
      exact Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_filter.2 ⟨hz, hzb⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ b ∈ Bd, (A.filter fun z => cellSupDist z b ≤ 100).card
        ≤ ∑ _b ∈ Bd, 201 ^ 4 := Finset.sum_le_sum fun b _ => by
          have := card_le_of_cellSupDist_le b 100 (A.filter fun z => cellSupDist z b ≤ 100)
            (fun z hz => (Finset.mem_filter.1 hz).2)
          simpa using this
      _ = 201 ^ 4 * Bd.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hDnn : ∀ z, 0 ≤ D z := fun z => relativeEnergy_nonneg a ha.le S z _ _ X _ _
  have hDhot : ∀ z ∈ B2, κ * σ' ^ 2 ≤ D z := by
    intro z hz
    obtain ⟨hzF, p, hp, hpz⟩ := Finset.mem_filter.1 hz
    have hpS : p ∈ innerPlaquettes S F.depth := (Finset.mem_filter.1 hp).1
    have hσp : σ' ≤ plaquetteDefect W p := (Finset.mem_filter.1 hp).2
    have hzS : z ∈ S := (Finset.mem_filter.1 hzF).1
    have hb := hplq F m S hFL hamb hm hreg s V hs (hsσ.trans e4) hcold U hU X (fun _ _ => 1) (Γ z) z hXn hzS
      (hfr z hzF) p hpS hpz
    have hcW : plaquetteDefect (gaugedChainFields X (Γ z) F.depth) p = plaquetteDefect W p := by
      unfold gaugedChainFields
      rw [plaquetteDefect_gaugeTransform, hXt]
    have hc8 : plaquetteDefect (chartField (referenceFieldChain S V) U F.depth) p < s / 8 := hcold8 p hpS
    have htri : plaquetteDefect (gaugedChainFields X (Γ z) F.depth) p ≤
        ‖((plaquetteHolonomy (gaugedChainFields X (Γ z) F.depth) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (chartField (referenceFieldChain S V) U F.depth) p : UnitQuaternion) : ℍ[ℝ])‖ +
        plaquetteDefect (chartField (referenceFieldChain S V) U F.depth) p := by
      unfold plaquetteDefect
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hroot : 7 / 8 * σ' ≤ C₂ * Real.sqrt (D z) := by
      have : plaquetteDefect W p ≤ C₂ * Real.sqrt (D z) + s / 8 := by
        rw [← hcW]
        exact htri.trans (add_le_add hb hc8.le)
      linarith
    have h7 : 7 / (8 * C₂) * σ' ≤ Real.sqrt (D z) := by
      have e : 7 / (8 * C₂) * σ' = (7 / 8 * σ') / C₂ := by
        field_simp
      rw [e, div_le_iff₀ hC₂]
      linarith
    have h8' := pow_le_pow_left₀ (by positivity) h7 2
    rw [Real.sq_sqrt (hDnn z), mul_pow] at h8'
    exact h8'
  have hE : (B2.card : ℝ) * (κ * σ' ^ 2) ≤ ∑ z ∈ Fr, D z := by
    have t1 : (B2.card : ℝ) * (κ * σ' ^ 2) ≤ ∑ z ∈ B2, D z := by
      have := Finset.card_nsmul_le_sum B2 D (κ * σ' ^ 2) hDhot
      simpa [nsmul_eq_mul] using this
    exact t1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun z _ _ => hDnn z)
  have hHr : (H.card : ℝ) ≤ (Pn : ℝ) * ((A.card : ℝ) + (B2.card : ℝ)) := by
    have t1 : H.card ≤ Pn * (A.card + B2.card) :=
      hHcard.trans (Nat.mul_le_mul_left _ (Finset.card_union_le _ _))
    exact_mod_cast t1
  have hAr : (A.card : ℝ) ≤ 201 ^ 4 * (Bd.card : ℝ) := by exact_mod_cast hAcard
  have hfin := hot_count_bound_arith cg c (Pn : ℝ) σ' (Bd.card : ℝ) (A.card : ℝ) (B2.card : ℝ)
    (H.card : ℝ) (∑ z ∈ Fr, D z) (blockEnergy a S F.depth W V - minimalAction a S F.top V) hcg.le hPr hσ'0.le
    (h2.trans e5) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hHr hAr κ hκ hE hex hcpos.le c1 c2
  rw [hcount]
  linarith
end YangMills.Construction.BlockAverages.HotPlaquetteCost
end
