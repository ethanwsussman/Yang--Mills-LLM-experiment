import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchCurls
open BlockAverages BlockAverages.PatchLocality PatchForms PatchLatticeChart PatchLatticeChart.Framing GaugeMap
  LatticeFractionalIntegration
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem patchSite_add_smul_basisVector (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (w : Lattice4)
    (i : Fin 4) :
    patchSite S z (w + (closedOrthant S z i) • basisVector i) = patchSite S z w + unitStep 0 i := by
  rw [unitStep_eq]
  unfold patchSite
  rw [add_assoc, ← siteOfCoords_add]
  congr 2
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector, Pi.single_apply]
  by_cases hk : k = i
  · subst hk
    have : closedOrthant S z k * closedOrthant S z k = 1 := closedOrthant_mul_self hs k
    simp only [if_true, mul_one]
    linear_combination this
  · simp [hk]
theorem patchSite_add_basisVector_of_pos (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (w : Lattice4) {i : Fin 4} (h : closedOrthant S z i = 1) :
    patchSite S z (w + basisVector i) = patchSite S z w + unitStep 0 i := by
  have := patchSite_add_smul_basisVector hs w i
  rwa [h, one_smul] at this
theorem patchSite_eq_add_basisVector_of_neg (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (w : Lattice4) {i : Fin 4} (h : closedOrthant S z i = -1) :
    patchSite S z w = patchSite S z (w + basisVector i) + unitStep 0 i := by
  have := patchSite_add_smul_basisVector hs (w + basisVector i) i
  rw [h] at this
  have e : w + basisVector i + (-1 : ℤ) • basisVector i = w := by
    simp
  rwa [e] at this
theorem plaquetteHolonomy_eq (X : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep 0 μ) ν * (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹ := by
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    sub_eq_add_neg, add_neg_cancel_right, mul_one, mul_assoc]
  have e3 : x + unitStep 0 μ + unitStep 0 ν + -unitStep 0 μ = x + unitStep 0 ν := by abel
  rw [e3]
  simp [mul_assoc]
def lowCorner (S : Finset F.Cell) (z : F.Cell) (u : Lattice4) (μ ν : Fin 4) : Lattice4 :=
  u + (if closedOrthant S z μ = 1 then 0 else basisVector μ) + (if closedOrthant S z ν = 1 then 0 else basisVector ν)
theorem plaquetteHolonomy_swap (X : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, ν, μ) = (plaquetteHolonomy X (x, μ, ν))⁻¹ := by
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  group
theorem patchChart_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {w : Lattice4} (hw : ∀ i, |w i - (cellSideLength F - 1) / 2| < 32 * cellSideLength F) :
    patchChart S z (patchSite S z w) = w := by
  funext i
  have hL : 0 < F.blockSide := hodd.pos
  unfold patchChart
  have e : (patchSite S z w - cellCentre 0 z) i =
      ((closedOrthant S z i * (w i - (cellSideLength F - 1) / 2) : ℤ) : ZMod (F.period 0 i)) := by
    simp [patchSite, siteOfCoords]
  rw [e, valMinAbs_of_abs_lt hamb hL i (by
    rcases hs i with h | h <;> rw [h]
    · rw [one_mul]
      exact hw i
    · rw [neg_one_mul, abs_neg]
      exact hw i)]
  have := closedOrthant_mul_self hs i
  linear_combination (w i - (cellSideLength F - 1) / 2) * this
theorem abs_sub_half_lt_of_mem_patchDomain (hodd : Odd F.blockSide) {w : Lattice4} (hw : w ∈ patchDomain S z)
    (i : Fin 4) :
    |w i - (cellSideLength F - 1) / 2| < 32 * cellSideLength F := by
  have hL : 0 < F.blockSide := hodd.pos
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hw).1 i)
  rw [abs_lt]
  constructor <;> omega
theorem patchSite_mem_sitesOfCells {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hm : 32 ≤ m)
    (hreg : IsOrthantRegular S m) {w : Lattice4}
    (hw : w ∈ patchDomain S z) : patchSite S z w ∈ sitesOfCells S 0 := by
  classical
  obtain ⟨hs, hcl⟩ := closedOrthant_spec hreg hm z
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  obtain ⟨hbox, a, ha, hax⟩ := Finset.mem_filter.1 hw
  have hbox' := Fintype.mem_piFinset.1 hbox
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨hy₀S, hy₀d⟩ := Finset.mem_filter.1 hy₀
  set o := cellDisplacement z y₀ with ho
  set σ := closedOrthant S z with hσ
  set N := cellSideLength F with hNdef
  set mm := (N - 1) / 2 with hmm
  have hob : ∀ i, |o i| ≤ 10 := by
    intro i
    have h1 : |o i| ≤ cellSupDist y₀ z := abs_cellDisplacement_le i
    rw [cellSupDist_comm] at h1
    have h2 : ((cellSupDist z y₀ : ℕ) : ℤ) ≤ 10 := by exact_mod_cast hy₀d
    exact h1.trans h2
  set v : Lattice4 := fun i => w i / N with hv
  set r : Lattice4 := fun i => w i % N with hr
  have hdecomp : ∀ i, w i = N * v i + r i := fun i => (Int.mul_ediv_add_emod (w i) N).symm
  have hr0 : ∀ i, 0 ≤ r i ∧ r i < N := fun i =>
    ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
  have hvlo : ∀ i, σ i * o i ≤ v i := by
    intro i
    by_contra hc
    have hc' : v i + 1 ≤ σ i * o i := by omega
    have h1 := hax i
    have h2 : N * (v i + 1) ≤ N * (σ i * o i) := mul_le_mul_of_nonneg_left hc' hN.le
    have h3 := hdecomp i
    have h4 := hr0 i
    simp only [] at h1
    nlinarith
  have hvhi : ∀ i, v i ≤ 20 := by
    intro i
    by_contra hc
    have hc' : 21 ≤ v i := by omega
    have h1 := Finset.mem_Icc.1 (hbox' i)
    have h2 : N * 21 ≤ N * v i := mul_le_mul_of_nonneg_left hc' hN.le
    have h3 := hdecomp i
    have h4 := hr0 i
    nlinarith
  set d : Lattice4 := fun i => v i - σ i * o i with hd
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    have := hvlo i
    simp only [hd]
    omega
  have hd1 : ∀ i, d i ≤ 30 := fun i => by
    have h1 := hvhi i
    have h2 : -10 ≤ σ i * o i := by
      have := abs_le.1 (hob i)
      rcases hs i with h | h <;> rw [h] <;> omega
    simp only [hd]
    omega
  have hee : ∀ i, σ i * σ i = 1 := closedOrthant_mul_self hs
  obtain ⟨y, hy⟩ : ∃ y : F.Cell, y = y₀ + siteOfCoords F.top (fun i => σ i * d i) := ⟨_, rfl⟩
  have hyS : y ∈ S := by
    rw [hy]
    refine hcl y₀ hy₀S ?_ (fun i => σ i * d i) (fun i => ?_) (fun i => ?_)
    · rw [cellSupDist_comm]
      omega
    · have : σ i * (σ i * d i) = d i := by
        rw [← mul_assoc, hee i, one_mul]
      rw [this]
      exact hd0 i
    · rcases hs i with h | h <;> rw [h] <;> rw [abs_le] <;> have := hd0 i <;> have := hd1 i <;>
        constructor <;> omega
  have hcy₀ : cellCentre 0 y₀ =
      cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * o i) := by
    conv_lhs => rw [← add_siteOfCoords_cellDisplacement z y₀]
    exact cellCentre_add 0 (Nat.zero_le _) z o
  have hcy : cellCentre 0 y =
      cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * (o i + σ i * d i)) := by
    rw [hy, cellCentre_add 0 (Nat.zero_le _) y₀, hcy₀, add_assoc, ← siteOfCoords_add]
    congr 2
    funext i
    simp only [Pi.add_apply]
    ring
  refine mem_sitesOfCells.2 ⟨y, hyS, fun i => σ i * (r i - mm), ?_, ?_⟩
  · refine Fintype.mem_piFinset.2 fun i => ?_
    have hcs : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = N := by
      simp [hNdef, cellSideLength]
    rw [Finset.mem_Icc, hcs]
    have h4 := hr0 i
    rcases hs i with h | h <;> rw [h] <;> constructor <;> omega
  · unfold patchSite
    rw [hcy, add_assoc, ← siteOfCoords_add]
    congr 2
    funext i
    have e1 : (F.blockSide : ℤ) ^ (F.top - 0) = N := by simp [hNdef, cellSideLength]
    simp only [Pi.add_apply, e1]
    rw [hdecomp i]
    show σ i * (N * v i + r i - mm) = _
    have h5 : d i = v i - σ i * o i := rfl
    rw [h5]
    linear_combination (N * o i) * hee i
theorem exists_eq_patchSite_of_mem_plaquetteCorners (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (u : Lattice4) (μ ν : Fin 4) {c : F.Site 0}
    (hc : c ∈ plaquetteCorners (patchSite S z (lowCorner S z u μ ν), μ, ν)) :
    ∃ w, (w = u ∨ w = u + basisVector μ ∨ w = u + basisVector ν ∨ w = u + basisVector μ + basisVector ν) ∧
      c = patchSite S z w := by
  classical
  have c1 : u + basisVector μ + basisVector ν = u + basisVector ν + basisVector μ := by abel
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hs μ with h1 | h1 <;> rcases hs ν with h2 | h2
  · have a1 : lowCorner S z u μ ν = u := by simp [lowCorner, h1, h2]
    rw [a1] at hc
    have b1 := patchSite_add_basisVector_of_pos hs u h1
    have b2 := patchSite_add_basisVector_of_pos hs u h2
    have b3 := patchSite_add_basisVector_of_pos hs (u + basisVector μ) h2
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, rfl⟩
    · exact ⟨u + basisVector μ, by simp, b1.symm⟩
    · exact ⟨u + basisVector ν, by simp, b2.symm⟩
    · exact ⟨u + basisVector μ + basisVector ν, by simp, by rw [b3, b1]⟩
  · have a1 : lowCorner S z u μ ν = u + basisVector ν := by simp [lowCorner, h1, h2]
    rw [a1] at hc
    have b1 := patchSite_eq_add_basisVector_of_neg hs u h2
    have b2 := patchSite_add_basisVector_of_pos hs (u + basisVector ν) h1
    have b3 := patchSite_add_basisVector_of_pos hs u h1
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨u + basisVector ν, by simp, rfl⟩
    · exact ⟨u + basisVector μ + basisVector ν, by simp, by rw [c1, b2]⟩
    · exact ⟨u, by simp, b1.symm⟩
    · refine ⟨u + basisVector μ, by simp, ?_⟩
      rw [b3, b1]
      abel
  · have a1 : lowCorner S z u μ ν = u + basisVector μ := by simp [lowCorner, h1, h2]
    rw [a1] at hc
    have b1 := patchSite_eq_add_basisVector_of_neg hs u h1
    have b2 := patchSite_add_basisVector_of_pos hs (u + basisVector μ) h2
    have b3 := patchSite_add_basisVector_of_pos hs u h2
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨u + basisVector μ, by simp, rfl⟩
    · exact ⟨u, by simp, b1.symm⟩
    · exact ⟨u + basisVector μ + basisVector ν, by simp, b2.symm⟩
    · exact ⟨u + basisVector ν, by simp, by rw [b3, b1]⟩
  · have a1 : lowCorner S z u μ ν = u + basisVector μ + basisVector ν := by simp [lowCorner, h1, h2]
    rw [a1] at hc
    have b1 := patchSite_eq_add_basisVector_of_neg hs (u + basisVector μ) h2
    have b2 := patchSite_eq_add_basisVector_of_neg hs (u + basisVector ν) h1
    have b3 := patchSite_eq_add_basisVector_of_neg hs u h1
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨u + basisVector μ + basisVector ν, by simp, rfl⟩
    · exact ⟨u + basisVector ν, by simp, by rw [b2, c1]⟩
    · exact ⟨u + basisVector μ, by simp, b1.symm⟩
    · refine ⟨u, by simp, ?_⟩
      rw [b3, b1]
      abel
theorem lowCorner_cases (u : Lattice4) (μ ν : Fin 4) :
    lowCorner S z u μ ν = u ∨ lowCorner S z u μ ν = u + basisVector μ ∨ lowCorner S z u μ ν = u + basisVector ν ∨
      lowCorner S z u μ ν = u + basisVector μ + basisVector ν := by
  unfold lowCorner
  split_ifs <;> simp
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] (A : Finset α) (Q : Finset β) (φ : α → β) (f : β → ℝ)
    (hf : ∀ q, 0 ≤ f q) (hm : ∀ a ∈ A, φ a ∈ Q) (hi : Set.InjOn φ A) :
    ∑ a ∈ A, f (φ a) ≤ ∑ q ∈ Q, f q := by
  rw [← Finset.sum_image (f := f) hi]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.2 hm) fun q _ _ => hf q
def sitePlaquette (S : Finset F.Cell) (z : F.Cell) (p : Lattice4 × Fin 4 × Fin 4) : F.Site 0 × Fin 4 × Fin 4 :=
  (patchSite S z (lowCorner S z p.1 p.2.1 p.2.2), min p.2.1 p.2.2, max p.2.1 p.2.2)
theorem sitePlaquette_mem_patchPlaquettes {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hm : 32 ≤ m) (hreg : IsOrthantRegular S m)
    {p : Lattice4 × Fin 4 × Fin 4} (hp : p ∈ orientedPlaquettesOf (patchDomain S z)) :
    sitePlaquette S z p ∈ patchPlaquettes S z := by
  classical
  have hs := (closedOrthant_spec hreg hm z).1
  obtain ⟨u, μ, ν⟩ := p
  obtain ⟨h0, h1, h2, h3, h4⟩ : u ∈ patchDomain S z ∧ μ ≠ ν ∧ u + basisVector μ ∈ patchDomain S z ∧
      u + basisVector ν ∈ patchDomain S z ∧ u + basisVector μ + basisVector ν ∈ patchDomain S z := by
    have := Finset.mem_filter.1 hp
    exact ⟨(Finset.mem_product.1 this.1).1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
  have hfour : ∀ w, (w = u ∨ w = u + basisVector μ ∨ w = u + basisVector ν ∨
      w = u + basisVector μ + basisVector ν) → w ∈ patchDomain S z := by
    rintro w (rfl | rfl | rfl | rfl) <;> assumption
  have hcorn : ∀ c ∈ plaquetteCorners (patchSite S z (lowCorner S z u μ ν), μ, ν),
      c ∈ patchBaseSites S z ∧ c ∈ sitesOfCells S 0 := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := exists_eq_patchSite_of_mem_plaquetteCorners hs u μ ν hc
    exact ⟨Finset.mem_image.2 ⟨w, hfour w hw, rfl⟩, patchSite_mem_sitesOfCells hamb hodd hm hreg (hfour w hw)⟩
  have hfirst : patchSite S z (lowCorner S z u μ ν) ∈ sitesOfCells S 0 :=
    patchSite_mem_sitesOfCells hamb hodd hm hreg (hfour _ (lowCorner_cases u μ ν))
  have hswap : ∀ c ∈ plaquetteCorners (patchSite S z (lowCorner S z u μ ν), min μ ν, max μ ν),
      c ∈ plaquetteCorners (patchSite S z (lowCorner S z u μ ν), μ, ν) := by
    intro c hc
    rcases le_total μ ν with h | h
    · rwa [min_eq_left h, max_eq_right h] at hc
    · rw [min_eq_right h, max_eq_left h] at hc
      simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · right; right; right
        abel
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hfirst, by simp⟩, ?_, ?_⟩, ?_⟩
  · show min μ ν < max μ ν
    exact min_lt_max.2 h1
  · intro c hc
    exact (hcorn c (hswap c hc)).2
  · intro c hc
    exact (hcorn c (hswap c hc)).1
theorem sitePlaquette_injOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (A : Finset (Lattice4 × Fin 4 × Fin 4)) (hA : A ⊆ orientedPlaquettesOf (patchDomain S z))
    (hord : (∀ p ∈ A, p.2.1 < p.2.2) ∨ ∀ p ∈ A, p.2.2 < p.2.1) :
    Set.InjOn (sitePlaquette S z) A := by
  classical
  intro p hp q hq he
  have hlow : ∀ p ∈ orientedPlaquettesOf (patchDomain S z), lowCorner S z p.1 p.2.1 p.2.2 ∈ patchDomain S z := by
    rintro ⟨u, μ, ν⟩ hp
    have := Finset.mem_filter.1 hp
    have h0 := (Finset.mem_product.1 this.1).1
    rcases lowCorner_cases (S := S) (z := z) u μ ν with h | h | h | h <;> rw [h]
    · exact h0
    · exact this.2.2.1
    · exact this.2.2.2.1
    · exact this.2.2.2.2
  have e1 : patchSite S z (lowCorner S z p.1 p.2.1 p.2.2) = patchSite S z (lowCorner S z q.1 q.2.1 q.2.2) :=
    congrArg Prod.fst he
  have e2 : lowCorner S z p.1 p.2.1 p.2.2 = lowCorner S z q.1 q.2.1 q.2.2 := by
    rw [← patchChart_patchSite hamb hodd hs (abs_sub_half_lt_of_mem_patchDomain hodd (hlow p (hA hp))), e1,
      patchChart_patchSite hamb hodd hs (abs_sub_half_lt_of_mem_patchDomain hodd (hlow q (hA hq)))]
  have e3 : min p.2.1 p.2.2 = min q.2.1 q.2.2 := congrArg (fun x => x.2.1) he
  have e4 : max p.2.1 p.2.2 = max q.2.1 q.2.2 := congrArg (fun x => x.2.2) he
  have e5 : p.2 = q.2 := by
    rcases hord with h | h
    · have a1 := h p hp
      have a2 := h q hq
      rw [min_eq_left a1.le, min_eq_left a2.le] at e3
      rw [max_eq_right a1.le, max_eq_right a2.le] at e4
      exact Prod.ext e3 e4
    · have a1 := h p hp
      have a2 := h q hq
      rw [min_eq_right a1.le, min_eq_right a2.le] at e3
      rw [max_eq_left a1.le, max_eq_left a2.le] at e4
      exact Prod.ext e4 e3
  have e6 : p.1 = q.1 := by
    have : lowCorner S z p.1 p.2.1 p.2.2 = lowCorner S z q.1 p.2.1 p.2.2 := by rw [e2, e5]
    unfold lowCorner at this
    exact add_right_cancel (add_right_cancel this)
  exact Prod.ext e6 e5
def cornerTransport (S : Finset F.Cell) (z : F.Cell) (X : F.GaugeField 0) (u : Lattice4) (μ ν : Fin 4) :
    UnitQuaternion :=
  (if closedOrthant S z μ = 1 then 1 else latticeField S z X u μ) *
    (if closedOrthant S z ν = 1 then 1 else
      latticeField S z X (u + if closedOrthant S z μ = 1 then 0 else basisVector μ) ν)
theorem latticePlaquette_latticeField_eq (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X : F.GaugeField 0) (u : Lattice4) (μ ν : Fin 4) :
    latticePlaquette (latticeField S z X) u μ ν = cornerTransport S z X u μ ν *
      (if closedOrthant S z μ * closedOrthant S z ν = 1 then
          plaquetteHolonomy X (patchSite S z (lowCorner S z u μ ν), μ, ν)
        else (plaquetteHolonomy X (patchSite S z (lowCorner S z u μ ν), μ, ν))⁻¹) *
      (cornerTransport S z X u μ ν)⁻¹ := by
  rw [plaquetteHolonomy_eq]
  have hne : (-1 : ℤ) ≠ 1 := by norm_num
  have c1 : u + basisVector μ + basisVector ν = u + basisVector ν + basisVector μ := by abel
  rcases hs μ with h1 | h1 <;> rcases hs ν with h2 | h2
  · have a1 : lowCorner S z u μ ν = u := by simp [lowCorner, h1, h2]
    have b1 := patchSite_add_basisVector_of_pos hs u h1
    have b2 := patchSite_add_basisVector_of_pos hs u h2
    have hc : cornerTransport S z X u μ ν = 1 := by simp [cornerTransport, h1, h2]
    rw [a1, hc, h1, h2]
    simp only [latticePlaquette, latticeField, h1, h2, if_true, b1, b2]
    simp
  · have a1 : lowCorner S z u μ ν = u + basisVector ν := by simp [lowCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector ν) := ⟨_, rfl⟩
    have e1 : patchSite S z u = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs u h2
    have e2 : patchSite S z (u + basisVector ν + basisVector μ) = x + unitStep 0 μ := by
      rw [hx]; exact patchSite_add_basisVector_of_pos hs _ h1
    have hc : cornerTransport S z X u μ ν = (X x ν)⁻¹ := by
      simp [cornerTransport, latticeField, h1, h2, hx]
    rw [hc, h1, h2, ← hx]
    have hif : ¬ ((1 : ℤ) * (-1 : ℤ) = 1) := by norm_num
    rw [if_neg hif]
    simp only [latticePlaquette, latticeField, h1, h2, if_true, hne, if_false, c1, ← hx, e1, e2]
    group
  · have a1 : lowCorner S z u μ ν = u + basisVector μ := by simp [lowCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector μ) := ⟨_, rfl⟩
    have e1 : patchSite S z u = x + unitStep 0 μ := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs u h1
    have e2 : patchSite S z (u + basisVector μ + basisVector ν) = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_add_basisVector_of_pos hs _ h2
    have hc : cornerTransport S z X u μ ν = (X x μ)⁻¹ := by
      simp [cornerTransport, latticeField, h1, h2, hx]
    rw [hc, h1, h2, ← hx]
    have hif : ¬ ((-1 : ℤ) * (1 : ℤ) = 1) := by norm_num
    rw [if_neg hif]
    simp only [latticePlaquette, latticeField, h1, h2, if_true, hne, if_false, ← c1, ← hx, e1, e2]
    group
  · have a1 : lowCorner S z u μ ν = u + basisVector μ + basisVector ν := by simp [lowCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector μ + basisVector ν) := ⟨_, rfl⟩
    have e1 : patchSite S z (u + basisVector μ) = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs _ h2
    have e2 : patchSite S z (u + basisVector ν) = x + unitStep 0 μ := by
      rw [hx, c1]; exact patchSite_eq_add_basisVector_of_neg hs _ h1
    have hc : cornerTransport S z X u μ ν = (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹ := by
      simp [cornerTransport, latticeField, h1, h2, e1, ← hx]
    rw [hc, h1, h2, ← hx]
    have hif : ((-1 : ℤ) * (-1 : ℤ) = 1) := by norm_num
    rw [if_pos hif]
    simp only [latticePlaquette, latticeField, h1, h2, if_true, hne, if_false, ← c1, ← hx, e1, e2]
    group
section QuaternionBounds
theorem normSubOne_mul_le (a b : UnitQuaternion) : normSubOne (a * b) ≤ normSubOne a + normSubOne b := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_mul_le <;> assumption
theorem normSubOne_conj (a b : UnitQuaternion) : normSubOne (a * b * a⁻¹) = normSubOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem normSubOne_inv (a : UnitQuaternion) : normSubOne a⁻¹ = normSubOne a := norm_coe_inv_sub_one a
theorem normSubOne_nonneg (a : UnitQuaternion) : 0 ≤ normSubOne a := norm_nonneg _
theorem norm_pureComponent_coe_le (g : UnitQuaternion) : ‖pureComponent (g : ℍ[ℝ])‖ ≤ normSubOne g := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_coe_le <;> assumption
theorem norm_pureComponent_mul_sub_le (x y : UnitQuaternion) :
    ‖pureComponent ((x * y : UnitQuaternion) : ℍ[ℝ]) - pureComponent (x : ℍ[ℝ]) - pureComponent (y : ℍ[ℝ])‖ ≤
      normSubOne x * normSubOne y := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_mul_sub_le <;> assumption
theorem pureComponent_coe_inv (g : UnitQuaternion) :
    pureComponent ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - pureComponent (g : ℍ[ℝ]) := by
  rw [coe_unitQuaternion_inv, pureComponent_star]
theorem pureComponent_coe_conj (a b : UnitQuaternion) :
    pureComponent ((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = adjointAction a (pureComponent (b : ℍ[ℝ])) := by
  rw [coe_conj_eq_adjointAction, pureComponent_adjointAction]
theorem norm_coe_mul_inv_sub_one (p q : UnitQuaternion) :
    ‖((p * q⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(p : ℍ[ℝ]) - (q : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem norm_pure_curl_le (g1 g2 g3 g4 W1 W2 W3 W4 : UnitQuaternion) :
    ‖pureComponent (g1 : ℍ[ℝ]) + pureComponent (g2 : ℍ[ℝ]) - pureComponent (g3 : ℍ[ℝ]) -
        pureComponent (g4 : ℍ[ℝ])‖ ≤
      ‖(((g1 * W1) * (g2 * W2) * (g3 * W3)⁻¹ * (g4 * W4)⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          ((W1 * W2 * W3⁻¹ * W4⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ +
        ((normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4) ^ 2 +
          2 * (normSubOne W1 + normSubOne W2 + normSubOne W3 + normSubOne W4) *
            (normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4)) := by
  set a1 := normSubOne g1
  set a2 := normSubOne g2
  set a3 := normSubOne g3
  set a4 := normSubOne g4
  set w1 := normSubOne W1
  set w2 := normSubOne W2
  set w3 := normSubOne W3
  set w4 := normSubOne W4
  have ha1 : 0 ≤ a1 := normSubOne_nonneg _
  have ha2 : 0 ≤ a2 := normSubOne_nonneg _
  have ha3 : 0 ≤ a3 := normSubOne_nonneg _
  have ha4 : 0 ≤ a4 := normSubOne_nonneg _
  have hw1 : 0 ≤ w1 := normSubOne_nonneg _
  have hw2 : 0 ≤ w2 := normSubOne_nonneg _
  have hw3 : 0 ≤ w3 := normSubOne_nonneg _
  have hw4 : 0 ≤ w4 := normSubOne_nonneg _
  set PT := (g1 * W1) * (g2 * W2) * (g3 * W3)⁻¹ * (g4 * W4)⁻¹ with hPT
  set PW := W1 * W2 * W3⁻¹ * W4⁻¹ with hPW
  set c3 := W1 * W2 * W3⁻¹ with hc3
  set c4 := c3 * W4⁻¹ with hc4
  set B2 := W1 * g2 * W1⁻¹ with hB2
  set B3 := c3 * g3⁻¹ * c3⁻¹ with hB3
  set B4 := c4 * g4⁻¹ * c4⁻¹ with hB4
  have hprod : PT * PW⁻¹ = g1 * (B2 * (B3 * B4)) := by
    simp only [hPT, hPW, hB2, hB3, hB4, hc3, hc4]
    group
  have hc3s : normSubOne c3 ≤ w1 + w2 + w3 := by
    have h1 := normSubOne_mul_le (W1 * W2) W3⁻¹
    have h2 := normSubOne_mul_le W1 W2
    rw [normSubOne_inv] at h1
    linarith
  have hc4s : normSubOne c4 ≤ w1 + w2 + w3 + w4 := by
    have h1 := normSubOne_mul_le c3 W4⁻¹
    rw [normSubOne_inv] at h1
    linarith
  have s2 : normSubOne B2 = a2 := normSubOne_conj _ _
  have s3 : normSubOne B3 = a3 := by rw [hB3, normSubOne_conj, normSubOne_inv]
  have s4 : normSubOne B4 = a4 := by rw [hB4, normSubOne_conj, normSubOne_inv]
  have hm34 := normSubOne_mul_le B3 B4
  have hm234 := normSubOne_mul_le B2 (B3 * B4)
  rw [s3, s4] at hm34
  rw [s2] at hm234
  have t34 := norm_pureComponent_mul_sub_le B3 B4
  have t2 := norm_pureComponent_mul_sub_le B2 (B3 * B4)
  have t1 := norm_pureComponent_mul_sub_le g1 (B2 * (B3 * B4))
  rw [s3, s4] at t34
  rw [s2] at t2
  have u2 : ‖pureComponent (B2 : ℍ[ℝ]) - pureComponent (g2 : ℍ[ℝ])‖ ≤ 2 * w1 * a2 := by
    rw [hB2, pureComponent_coe_conj]
    refine (norm_adjointAction_apply_sub_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_pureComponent_coe_le g2) (by positivity)
  have u3 : ‖pureComponent (B3 : ℍ[ℝ]) + pureComponent (g3 : ℍ[ℝ])‖ ≤ 2 * (w1 + w2 + w3) * a3 := by
    have e : pureComponent (B3 : ℍ[ℝ]) + pureComponent (g3 : ℍ[ℝ]) =
        -(adjointAction c3 (pureComponent (g3 : ℍ[ℝ])) - pureComponent (g3 : ℍ[ℝ])) := by
      rw [hB3, pureComponent_coe_conj, pureComponent_coe_inv, adjointAction_apply_neg]
      abel
    rw [e, norm_neg]
    refine (norm_adjointAction_apply_sub_le _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc3s (by norm_num)) (norm_pureComponent_coe_le g3)
      (norm_nonneg _) (by positivity)
  have u4 : ‖pureComponent (B4 : ℍ[ℝ]) + pureComponent (g4 : ℍ[ℝ])‖ ≤ 2 * (w1 + w2 + w3 + w4) * a4 := by
    have e : pureComponent (B4 : ℍ[ℝ]) + pureComponent (g4 : ℍ[ℝ]) =
        -(adjointAction c4 (pureComponent (g4 : ℍ[ℝ])) - pureComponent (g4 : ℍ[ℝ])) := by
      rw [hB4, pureComponent_coe_conj, pureComponent_coe_inv, adjointAction_apply_neg]
      abel
    rw [e, norm_neg]
    refine (norm_adjointAction_apply_sub_le _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc4s (by norm_num)) (norm_pureComponent_coe_le g4)
      (norm_nonneg _) (by positivity)
  have h0 : ‖pureComponent ((PT * PW⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖(PT : ℍ[ℝ]) - (PW : ℍ[ℝ])‖ := by
    rw [← norm_coe_mul_inv_sub_one]
    exact norm_pureComponent_coe_le _
  rw [hprod] at h0
  set v0 := pureComponent ((g1 * (B2 * (B3 * B4)) : UnitQuaternion) : ℍ[ℝ]) with hv0
  set p1 := pureComponent (g1 : ℍ[ℝ])
  set p2 := pureComponent (g2 : ℍ[ℝ])
  set p3 := pureComponent (g3 : ℍ[ℝ])
  set p4 := pureComponent (g4 : ℍ[ℝ])
  set q2 := pureComponent (B2 : ℍ[ℝ])
  set q3 := pureComponent (B3 : ℍ[ℝ])
  set q4 := pureComponent (B4 : ℍ[ℝ])
  set q34 := pureComponent ((B3 * B4 : UnitQuaternion) : ℍ[ℝ])
  set q234 := pureComponent ((B2 * (B3 * B4) : UnitQuaternion) : ℍ[ℝ])
  have e : p1 + p2 - p3 - p4 = v0 - (v0 - p1 - q234) - (q234 - q2 - q34) - (q34 - q3 - q4) - (q2 - p2) -
      (q3 + p3) - (q4 + p4) := by abel
  rw [e]
  have n1 := norm_sub_le (v0 - (v0 - p1 - q234) - (q234 - q2 - q34) - (q34 - q3 - q4) - (q2 - p2) - (q3 + p3))
    (q4 + p4)
  have n2 := norm_sub_le (v0 - (v0 - p1 - q234) - (q234 - q2 - q34) - (q34 - q3 - q4) - (q2 - p2)) (q3 + p3)
  have n3 := norm_sub_le (v0 - (v0 - p1 - q234) - (q234 - q2 - q34) - (q34 - q3 - q4)) (q2 - p2)
  have n4 := norm_sub_le (v0 - (v0 - p1 - q234) - (q234 - q2 - q34)) (q34 - q3 - q4)
  have n5 := norm_sub_le (v0 - (v0 - p1 - q234)) (q234 - q2 - q34)
  have n6 := norm_sub_le v0 (v0 - p1 - q234)
  have b1 : ‖v0 - p1 - q234‖ ≤ a1 * (a2 + (a3 + a4)) :=
    t1.trans (mul_le_mul_of_nonneg_left (hm234.trans (by linarith)) ha1)
  have b2 : ‖q234 - q2 - q34‖ ≤ a2 * (a3 + a4) :=
    t2.trans (mul_le_mul_of_nonneg_left hm34 ha2)
  have k1 : 2 * w1 * a2 ≤ 2 * (w1 + w2 + w3 + w4) * a2 := by
    apply mul_le_mul_of_nonneg_right _ ha2
    linarith
  have k2 : 2 * (w1 + w2 + w3) * a3 ≤ 2 * (w1 + w2 + w3 + w4) * a3 := by
    apply mul_le_mul_of_nonneg_right _ ha3
    linarith
  have k3 : 0 ≤ 2 * (w1 + w2 + w3 + w4) * a1 := by positivity
  have k4 : a1 * (a2 + (a3 + a4)) + a2 * (a3 + a4) + a3 * a4 ≤ (a1 + a2 + a3 + a4) ^ 2 := by
    nlinarith [mul_nonneg ha1 ha2, mul_nonneg ha1 ha3, mul_nonneg ha1 ha4, mul_nonneg ha2 ha3, mul_nonneg ha2 ha4,
      mul_nonneg ha3 ha4, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3, sq_nonneg a4]
  linarith
theorem norm_coe_conj_sub_coe_conj_le (c1 c2 P Q : UnitQuaternion) :
    ‖((c1 * P * c1⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((c2 * Q * c2⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(P : ℍ[ℝ]) - (Q : ℍ[ℝ])‖ + 2 * normSubOne (c2⁻¹ * c1) * normSubOne Q := by
  set h := c2⁻¹ * c1 with hh
  have e1 : ‖((c1 * P * c1⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((c2 * Q * c2⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ =
      ‖((h * P * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (Q : ℍ[ℝ])‖ := by
    have e2 : c1 * P * c1⁻¹ = c2 * (h * P * h⁻¹) * c2⁻¹ := by
      rw [hh]
      group
    rw [e2, coe_conj_eq_adjointAction c2 (h * P * h⁻¹), coe_conj_eq_adjointAction c2 Q, ← adjointAction_sub,
      norm_adjointAction]
  rw [e1]
  have e3 : ((h * P * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (Q : ℍ[ℝ]) =
      adjointAction h ((P : ℍ[ℝ]) - (Q : ℍ[ℝ])) +
        (adjointAction h ((Q : ℍ[ℝ]) - 1) - ((Q : ℍ[ℝ]) - 1)) := by
    have e4 : adjointAction h 1 = 1 := by
      have := coe_conj_eq_adjointAction h (1 : UnitQuaternion)
      simpa using this.symm
    rw [coe_conj_eq_adjointAction, adjointAction_sub, adjointAction_sub, e4]
    abel
  rw [e3]
  refine (norm_add_le _ _).trans ?_
  rw [norm_adjointAction]
  exact add_le_add le_rfl (norm_adjointAction_apply_sub_le _ _)
theorem normSubOne_mul_mul_inv_le (x1 x2 y1 y2 : UnitQuaternion) :
    normSubOne ((x1 * x2) * (y1 * y2)⁻¹) ≤ normSubOne (x1 * y1⁻¹) + normSubOne (x2 * y2⁻¹) := by
  have e : (x1 * x2) * (y1 * y2)⁻¹ = (x1 * y1⁻¹) * (y1 * (x2 * y2⁻¹) * y1⁻¹) := by group
  rw [e]
  refine (normSubOne_mul_le _ _).trans ?_
  rw [normSubOne_conj]
theorem norm_coe_inv_sub_coe_inv (p q : UnitQuaternion) :
    ‖((p⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((q⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(p : ℍ[ℝ]) - (q : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
end QuaternionBounds
theorem add_pow_four_le (u v : ℝ) : (u + v) ^ 4 ≤ 8 * (u ^ 4 + v ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem add_add_add_pow_four_le (x1 x2 x3 x4 : ℝ) :
    (x1 + x2 + x3 + x4) ^ 4 ≤ 64 * (x1 ^ 4 + x2 ^ 4 + x3 ^ 4 + x4 ^ 4) := by
  have a4 : ∀ u v : ℝ, (u + v) ^ 4 ≤ 8 * (u ^ 4 + v ^ 4) := by
    intro u v
    have h : 0 ≤ 7 * u ^ 2 + 10 * u * v + 7 * v ^ 2 := by nlinarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]
    have e : 8 * (u ^ 4 + v ^ 4) - (u + v) ^ 4 = (u - v) ^ 2 * (7 * u ^ 2 + 10 * u * v + 7 * v ^ 2) := by ring
    have := mul_nonneg (sq_nonneg (u - v)) h
    linarith
  have h1 := a4 (x1 + x2) (x3 + x4)
  have h2 := a4 x1 x2
  have h3 := a4 x3 x4
  have e : x1 + x2 + x3 + x4 = (x1 + x2) + (x3 + x4) := by ring
  rw [e]
  linarith
theorem norm_conj_ite_sub_le (cT cW p q : UnitQuaternion) (b : Prop) [Decidable b] :
    ‖((cT * (if b then p else p⁻¹) * cT⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        ((cW * (if b then q else q⁻¹) * cW⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(p : ℍ[ℝ]) - (q : ℍ[ℝ])‖ + 2 * normSubOne (cW⁻¹ * cT) * normSubOne (if b then q else q⁻¹) := by
  by_cases hb : b
  · simp only [if_pos hb]
    exact norm_coe_conj_sub_coe_conj_le _ _ _ _
  · simp only [if_neg hb]
    exact (norm_coe_conj_sub_coe_conj_le _ _ _ _).trans
      (add_le_add (le_of_eq (norm_coe_inv_sub_coe_inv p q)) le_rfl)
theorem norm_latticePlaquette_sub_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (T W : F.GaugeField 0) (u : Lattice4) (μ ν : Fin 4) (A Wt : ℝ)
    (hA0 : 0 ≤ A) (hW0 : 0 ≤ Wt)
    (hcA : normSubOne ((cornerTransport S z W u μ ν)⁻¹ * cornerTransport S z T u μ ν) ≤ A)
    (hW : normSubOne (latticePlaquette (latticeField S z W) u μ ν) ≤ Wt) :
    ‖((latticePlaquette (latticeField S z T) u μ ν : UnitQuaternion) : ℍ[ℝ]) -
        ((latticePlaquette (latticeField S z W) u μ ν : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖((plaquetteHolonomy T (patchSite S z (lowCorner S z u μ ν), μ, ν) : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy W (patchSite S z (lowCorner S z u μ ν), μ, ν) : UnitQuaternion) : ℍ[ℝ])‖ +
        2 * A * Wt := by
  have fT := latticePlaquette_latticeField_eq he T u μ ν
  have fW := latticePlaquette_latticeField_eq he W u μ ν
  rw [fW, normSubOne_conj] at hW
  rw [fT, fW]
  refine (norm_conj_ite_sub_le _ _ _ _ _).trans (add_le_add le_rfl ?_)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hcA (by norm_num)) hW (normSubOne_nonneg _) (by positivity)
theorem normSubOne_four_le (a b c d : UnitQuaternion) :
    normSubOne (a * b * c⁻¹ * d⁻¹) ≤ normSubOne a + normSubOne b + normSubOne c + normSubOne d := by
  have a1 := normSubOne_mul_le (a * b * c⁻¹) d⁻¹
  have a2 := normSubOne_mul_le (a * b) c⁻¹
  have a3 := normSubOne_mul_le a b
  rw [normSubOne_inv] at a1 a2
  linarith
theorem normSubOne_four_nonneg (a b c d : UnitQuaternion) :
    0 ≤ normSubOne a + normSubOne b + normSubOne c + normSubOne d := by
  have := normSubOne_nonneg a
  have := normSubOne_nonneg b
  have := normSubOne_nonneg c
  have := normSubOne_nonneg d
  positivity
theorem sq_sum_sq_le_of_pointwise {ι : Type} (s : Finset ι) (d c A B : ι → ℝ) (D0 E Y : ℝ)
    (hc : ∀ p ∈ s, c p ≤ d p + 4 * A p * B p)
    (hc0 : ∀ p, 0 ≤ c p) (hd : ∑ p ∈ s, d p ^ 2 ≤ 2 * D0) (hA : ∑ p ∈ s, A p ^ 4 ≤ 4096 * E)
    (hB : ∑ p ∈ s, B p ^ 4 ≤ 32768 * Y) (hA0 : ∀ p, 0 ≤ A p) (hB0 : ∀ p, 0 ≤ B p) (hE : 0 ≤ E) (hY : 0 ≤ Y) :
    (∑ p ∈ s, c p ^ 2) ^ 2 ≤ 32 * D0 ^ 2 + 2048 * 4096 * 32768 * E * Y := by
  have hX : (∑ p ∈ s, A p ^ 2 * B p ^ 2) ^ 2 ≤ (∑ p ∈ s, A p ^ 4) * ∑ p ∈ s, B p ^ 4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun p => A p ^ 2) (fun p => B p ^ 2)
    have e1 : ∀ p, (A p ^ 2) ^ 2 = A p ^ 4 := fun p => by ring
    have e2 : ∀ p, (B p ^ 2) ^ 2 = B p ^ 4 := fun p => by ring
    simp only [e1, e2] at h
    exact h
  have hS : ∑ p ∈ s, c p ^ 2 ≤ 2 * ∑ p ∈ s, d p ^ 2 + 32 * ∑ p ∈ s, A p ^ 2 * B p ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have c2 : c p ^ 2 ≤ (d p + 4 * A p * B p) ^ 2 := pow_le_pow_left₀ (hc0 p) (hc p hp) 2
    have c3 := sq_nonneg (d p - 4 * A p * B p)
    nlinarith only [c2, c3]
  have hS0 : 0 ≤ ∑ p ∈ s, c p ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hSB0' : 0 ≤ ∑ p ∈ s, B p ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  generalize (∑ p ∈ s, c p ^ 2) = Sc at *
  generalize (∑ p ∈ s, A p ^ 2 * B p ^ 2) = Xs at *
  generalize (∑ p ∈ s, d p ^ 2) = Sd at *
  generalize (∑ p ∈ s, A p ^ 4) = SA at *
  generalize (∑ p ∈ s, B p ^ 4) = SB at *
  have hS' : Sc ≤ 4 * D0 + 32 * Xs := by linarith
  have h1 : Sc ^ 2 ≤ (4 * D0 + 32 * Xs) ^ 2 := pow_le_pow_left₀ hS0 hS' 2
  have h2 := sq_nonneg (4 * D0 - 32 * Xs)
  have h3 : Xs ^ 2 ≤ (4096 * E) * (32768 * Y) :=
    hX.trans (mul_le_mul hA hB hSB0' (by positivity))
  nlinarith only [h1, h2, h3]
section PatchEstimates
variable {V : F.GaugeField F.top}
theorem gaugedGap_mul_framedLatticeField (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion) (a : Lattice4)
    (i : Fin 4) :
    gaugedGap S V z X W γ a i * framedLatticeField S V z W a i =
      latticeGaugeTransform γ (latticeField S z X) a i := by
  unfold gaugedGap
  group
theorem latticeGaugeTransform_eq_frameChange (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (γ : Lattice4 → UnitQuaternion) (X : F.GaugeField 0) {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z)
    (ha' : a + basisVector i ∈ patchDomain S z) :
    latticeGaugeTransform γ (latticeField S z X) a i = (frameChange S V z (patchSite S z a))⁻¹ *
      latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i *
        frameChange S V z (patchSite S z (a + basisVector i)) := by
  rw [latticeField_gaugeTransform (V := V) hamb hodd he γ X ha ha']
  group
theorem latticePlaquette_of_frame (f : Lattice4 → UnitQuaternion) (T : Lattice4 → Fin 4 → UnitQuaternion)
    (T' : Lattice4 → Fin 4 → UnitQuaternion) (u : Lattice4) (μ ν : Fin 4)
    (h1 : T' u μ = (f u)⁻¹ * T u μ * f (u + basisVector μ))
    (h2 : T' (u + basisVector μ) ν =
      (f (u + basisVector μ))⁻¹ * T (u + basisVector μ) ν * f (u + basisVector μ + basisVector ν))
    (h3 : T' (u + basisVector ν) μ =
      (f (u + basisVector ν))⁻¹ * T (u + basisVector ν) μ * f (u + basisVector ν + basisVector μ))
    (h4 : T' u ν = (f u)⁻¹ * T u ν * f (u + basisVector ν)) :
    latticePlaquette T' u μ ν = (f u)⁻¹ * latticePlaquette T u μ ν * ((f u)⁻¹)⁻¹ := by
  unfold latticePlaquette
  have c : u + basisVector ν + basisVector μ = u + basisVector μ + basisVector ν := by abel
  rw [h1, h2, h3, h4, c]
  group
theorem normSubOne_gaugedGap (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion) {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z)
    (ha' : a + basisVector i ∈ patchDomain S z) :
    normSubOne (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i *
        (latticeField S z W a i)⁻¹) =
      normSubOne (gaugedGap S V z X W γ a i) := by
  unfold gaugedGap
  rw [latticeGaugeTransform_mul_inv_framed (V := V) hamb hodd he γ X W ha ha']
  have e : (frameChange S V z (patchSite S z a))⁻¹ *
      (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i * (latticeField S z W a i)⁻¹) *
      frameChange S V z (patchSite S z a) = (frameChange S V z (patchSite S z a))⁻¹ *
        (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i * (latticeField S z W a i)⁻¹) *
          ((frameChange S V z (patchSite S z a))⁻¹)⁻¹ := by
    group
  rw [e, normSubOne_conj]
theorem normSubOne_cornerTransport_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion) {u : Lattice4} {μ ν : Fin 4}
    (h0 : u ∈ patchDomain S z) (h1 : u + basisVector μ ∈ patchDomain S z)
    (h2 : u + basisVector ν ∈ patchDomain S z) (h3 : u + basisVector μ + basisVector ν ∈ patchDomain S z) :
    normSubOne ((cornerTransport S z W u μ ν)⁻¹ *
        cornerTransport S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) u μ ν) ≤
      normSubOne (gaugedGap S V z X W γ u μ) + normSubOne (gaugedGap S V z X W γ (u + basisVector μ) ν) +
        normSubOne (gaugedGap S V z X W γ u ν) := by
  set cT := cornerTransport S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) u μ ν with hcT
  set cW := cornerTransport S z W u μ ν with hcW
  have e : cW⁻¹ * cT = cW⁻¹ * (cT * cW⁻¹) * (cW⁻¹)⁻¹ := by group
  rw [e, normSubOne_conj]
  have hsz0 : normSubOne (1 : UnitQuaternion) = 0 := by simp [normSubOne]
  have n1 := normSubOne_nonneg (gaugedGap S V z X W γ u μ)
  have n2 := normSubOne_nonneg (gaugedGap S V z X W γ (u + basisVector μ) ν)
  have n3 := normSubOne_nonneg (gaugedGap S V z X W γ u ν)
  have g1 := normSubOne_gaugedGap (V := V) hamb hodd he X W γ h0 h1
  have g2 := normSubOne_gaugedGap (V := V) hamb hodd he X W γ h1 h3
  have g4 := normSubOne_gaugedGap (V := V) hamb hodd he X W γ h0 h2
  unfold cornerTransport at hcT hcW
  rw [hcT, hcW]
  refine (normSubOne_mul_mul_inv_le _ _ _ _).trans ?_
  by_cases s1 : closedOrthant S z μ = 1 <;> by_cases s2 : closedOrthant S z ν = 1
  · simp only [s1, s2, if_true, inv_one, mul_one, hsz0]
    linarith
  · simp only [s1, s2, if_true, if_false, inv_one, mul_one, hsz0, add_zero, zero_add]
    rw [g4]
    linarith
  · simp only [s1, s2, if_true, if_false, inv_one, mul_one, hsz0, add_zero]
    rw [g1]
    linarith
  · simp only [s1, s2, if_false]
    rw [g1, g2]
    linarith
theorem norm_pure_curl_le_of_conj (g1 g2 g3 g4 W1 W2 W3 W4 f LT LW : UnitQuaternion) (pq : ℝ)
    (eT : (g1 * W1) * (g2 * W2) * (g3 * W3)⁻¹ * (g4 * W4)⁻¹ = f * LT * f⁻¹)
    (eW : W1 * W2 * W3⁻¹ * W4⁻¹ = f * LW * f⁻¹)
    (hmain : ‖(LT : ℍ[ℝ]) - (LW : ℍ[ℝ])‖ ≤
      pq + 2 * (normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4) *
        (normSubOne W1 + normSubOne W2 + normSubOne W3 + normSubOne W4)) :
    ‖pureComponent (g1 : ℍ[ℝ]) + pureComponent (g2 : ℍ[ℝ]) - pureComponent (g3 : ℍ[ℝ]) -
        pureComponent (g4 : ℍ[ℝ])‖ ≤
      pq + 4 * (normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4) *
        (normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4 +
          (normSubOne W1 + normSubOne W2 + normSubOne W3 + normSubOne W4)) := by
  have hc := norm_pure_curl_le g1 g2 g3 g4 W1 W2 W3 W4
  rw [eT, eW, coe_conj_eq_adjointAction f LT, coe_conj_eq_adjointAction f LW, ← adjointAction_sub,
    norm_adjointAction] at hc
  have hA0 := normSubOne_four_nonneg g1 g2 g3 g4
  have hW0 := normSubOne_four_nonneg W1 W2 W3 W4
  generalize normSubOne g1 + normSubOne g2 + normSubOne g3 + normSubOne g4 = A at hc hmain hA0 ⊢
  generalize normSubOne W1 + normSubOne W2 + normSubOne W3 + normSubOne W4 = Wt at hc hmain hW0 ⊢
  nlinarith
theorem norm_plaquetteCurl_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion) {u : Lattice4} {μ ν : Fin 4}
    (h0 : u ∈ patchDomain S z) (h1 : u + basisVector μ ∈ patchDomain S z)
    (h2 : u + basisVector ν ∈ patchDomain S z) (h3 : u + basisVector μ + basisVector ν ∈ patchDomain S z) :
    ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W γ a i : UnitQuaternion) : ℍ[ℝ])) u μ ν‖ ≤
      ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X)
            (patchSite S z (lowCorner S z u μ ν), μ, ν) : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy W (patchSite S z (lowCorner S z u μ ν), μ, ν) : UnitQuaternion) : ℍ[ℝ])‖ +
      4 * (normSubOne (gaugedGap S V z X W γ u μ) + normSubOne (gaugedGap S V z X W γ (u + basisVector μ) ν) +
          normSubOne (gaugedGap S V z X W γ (u + basisVector ν) μ) + normSubOne (gaugedGap S V z X W γ u ν)) *
        (normSubOne (gaugedGap S V z X W γ u μ) + normSubOne (gaugedGap S V z X W γ (u + basisVector μ) ν) +
          normSubOne (gaugedGap S V z X W γ (u + basisVector ν) μ) + normSubOne (gaugedGap S V z X W γ u ν) +
          (normSubOne (framedLatticeField S V z W u μ) +
            normSubOne (framedLatticeField S V z W (u + basisVector μ) ν) +
            normSubOne (framedLatticeField S V z W (u + basisVector ν) μ) +
            normSubOne (framedLatticeField S V z W u ν))) := by
  have h3' : u + basisVector ν + basisVector μ ∈ patchDomain S z := by
    have c : u + basisVector ν + basisVector μ = u + basisVector μ + basisVector ν := by abel
    rw [c]
    exact h3
  let f : Lattice4 → UnitQuaternion := fun a => frameChange S V z (patchSite S z a)
  have eT : (gaugedGap S V z X W γ u μ * framedLatticeField S V z W u μ) *
      (gaugedGap S V z X W γ (u + basisVector μ) ν * framedLatticeField S V z W (u + basisVector μ) ν) *
      (gaugedGap S V z X W γ (u + basisVector ν) μ * framedLatticeField S V z W (u + basisVector ν) μ)⁻¹ *
      (gaugedGap S V z X W γ u ν * framedLatticeField S V z W u ν)⁻¹ =
      (f u)⁻¹ * latticePlaquette (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X)) u μ ν *
        ((f u)⁻¹)⁻¹ := by
    rw [gaugedGap_mul_framedLatticeField, gaugedGap_mul_framedLatticeField, gaugedGap_mul_framedLatticeField,
      gaugedGap_mul_framedLatticeField]
    exact latticePlaquette_of_frame f (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X))
      (latticeGaugeTransform γ (latticeField S z X)) u μ ν
      (latticeGaugeTransform_eq_frameChange hamb hodd he γ X h0 h1)
      (latticeGaugeTransform_eq_frameChange hamb hodd he γ X h1 h3)
      (latticeGaugeTransform_eq_frameChange hamb hodd he γ X h2 h3')
      (latticeGaugeTransform_eq_frameChange hamb hodd he γ X h0 h2)
  have eW : framedLatticeField S V z W u μ * framedLatticeField S V z W (u + basisVector μ) ν *
      (framedLatticeField S V z W (u + basisVector ν) μ)⁻¹ * (framedLatticeField S V z W u ν)⁻¹ =
      (f u)⁻¹ * latticePlaquette (latticeField S z W) u μ ν * ((f u)⁻¹)⁻¹ :=
    latticePlaquette_of_frame f (latticeField S z W) (framedLatticeField S V z W) u μ ν rfl rfl rfl rfl
  have hcs := normSubOne_cornerTransport_le (V := V) hamb hodd he X W γ h0 h1 h2 h3
  have hPW : normSubOne (latticePlaquette (latticeField S z W) u μ ν) ≤
      normSubOne (framedLatticeField S V z W u μ) +
      normSubOne (framedLatticeField S V z W (u + basisVector μ) ν) +
      normSubOne (framedLatticeField S V z W (u + basisVector ν) μ) +
      normSubOne (framedLatticeField S V z W u ν) := by
    have e := normSubOne_conj (f u)⁻¹ (latticePlaquette (latticeField S z W) u μ ν)
    rw [← eW] at e
    rw [← e]
    exact normSubOne_four_le _ _ _ _
  have hcA : normSubOne ((cornerTransport S z W u μ ν)⁻¹ *
        cornerTransport S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) u μ ν) ≤
      normSubOne (gaugedGap S V z X W γ u μ) + normSubOne (gaugedGap S V z X W γ (u + basisVector μ) ν) +
        normSubOne (gaugedGap S V z X W γ (u + basisVector ν) μ) + normSubOne (gaugedGap S V z X W γ u ν) := by
    have := normSubOne_nonneg (gaugedGap S V z X W γ (u + basisVector ν) μ)
    linarith
  have hmain := norm_latticePlaquette_sub_le he (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) W u μ ν _ _
    (normSubOne_four_nonneg _ _ _ _) (normSubOne_four_nonneg _ _ _ _) hcA hPW
  exact norm_pure_curl_le_of_conj _ _ _ _ _ _ _ _ _ _ _ _ eT eW hmain
theorem mem_orientedPlaquettesOf {P : Finset Lattice4} {p : Lattice4 × Fin 4 × Fin 4}
    (hp : p ∈ orientedPlaquettesOf P) :
    p.1 ∈ P ∧ p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧ p.1 + basisVector p.2.2 ∈ P ∧
      p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P := by
  have := Finset.mem_filter.1 hp
  exact ⟨(Finset.mem_product.1 this.1).1, this.2⟩
theorem sum_comp_bond_le {P : Finset Lattice4} (f : Lattice4 × Fin 4 → ℝ) (hf : ∀ b, 0 ≤ f b)
    (φ : Lattice4 × Fin 4 × Fin 4 → Lattice4 × Fin 4)
    (hφ : ∀ p ∈ orientedPlaquettesOf P, φ p ∈ bondsOf P)
    (hinj : ∀ p ∈ orientedPlaquettesOf P, ∀ p' ∈ orientedPlaquettesOf P, p.2 = p'.2 → φ p = φ p' → p = p') :
    ∑ p ∈ orientedPlaquettesOf P, f (φ p) ≤ 16 * ∑ b ∈ bondsOf P, f b := by
  classical
  have h1 : ∑ p ∈ orientedPlaquettesOf P, f (φ p) =
      ∑ q : Fin 4 × Fin 4, ∑ p ∈ (orientedPlaquettesOf P).filter (fun p => p.2 = q), f (φ p) :=
    (Finset.sum_fiberwise _ _ _).symm
  rw [h1]
  calc ∑ q : Fin 4 × Fin 4, ∑ p ∈ (orientedPlaquettesOf P).filter (fun p => p.2 = q), f (φ p)
      ≤ ∑ _q : Fin 4 × Fin 4, ∑ b ∈ bondsOf P, f b := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine sum_comp_le_of_injOn _ _ φ f hf (fun p hp => hφ p (Finset.mem_filter.1 hp).1) ?_
        intro p hp p' hp' e
        have a1 := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
        have a2 := Finset.mem_filter.1 (Finset.mem_coe.1 hp')
        exact hinj p a1.1 p' a2.1 (a1.2.trans a2.2.symm) e
    _ = 16 * ∑ b ∈ bondsOf P, f b := by simp
end PatchEstimates
def firstBond (p : Lattice4 × Fin 4 × Fin 4) : Lattice4 × Fin 4 := (p.1, p.2.1)
def secondBond (p : Lattice4 × Fin 4 × Fin 4) : Lattice4 × Fin 4 := (p.1 + basisVector p.2.1, p.2.2)
def thirdBond (p : Lattice4 × Fin 4 × Fin 4) : Lattice4 × Fin 4 := (p.1 + basisVector p.2.2, p.2.1)
def fourthBond (p : Lattice4 × Fin 4 × Fin 4) : Lattice4 × Fin 4 := (p.1, p.2.2)
def boundarySum (f : Lattice4 × Fin 4 → ℝ) (p : Lattice4 × Fin 4 × Fin 4) : ℝ :=
  f (firstBond p) + f (secondBond p) + f (thirdBond p) + f (fourthBond p)
theorem boundarySum_nonneg {f : Lattice4 × Fin 4 → ℝ} (hf : ∀ b, 0 ≤ f b) (p : Lattice4 × Fin 4 × Fin 4) :
    0 ≤ boundarySum f p := by
  unfold boundarySum
  have := hf (firstBond p)
  have := hf (secondBond p)
  have := hf (thirdBond p)
  have := hf (fourthBond p)
  positivity
theorem bonds_mem_bondsOf {P : Finset Lattice4} {p : Lattice4 × Fin 4 × Fin 4} (hp : p ∈ orientedPlaquettesOf P) :
    firstBond p ∈ bondsOf P ∧ secondBond p ∈ bondsOf P ∧ thirdBond p ∈ bondsOf P ∧ fourthBond p ∈ bondsOf P := by
  obtain ⟨h0, -, h1, h2, h3⟩ := mem_orientedPlaquettesOf hp
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h0, Finset.mem_univ _⟩, h1⟩,
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, h3⟩,
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2, Finset.mem_univ _⟩, ?_⟩,
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h0, Finset.mem_univ _⟩, h2⟩⟩
  show p.1 + basisVector p.2.2 + basisVector p.2.1 ∈ P
  have c : p.1 + basisVector p.2.2 + basisVector p.2.1 = p.1 + basisVector p.2.1 + basisVector p.2.2 := by abel
  rw [c]
  exact h3
theorem sum_boundarySum_le {P : Finset Lattice4} (f : Lattice4 × Fin 4 → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ p ∈ orientedPlaquettesOf P, boundarySum f p ≤ 64 * ∑ b ∈ bondsOf P, f b := by
  have s1 := sum_comp_bond_le (P := P) f hf firstBond (fun p hp => (bonds_mem_bondsOf hp).1)
    (fun p _ p' _ e1 e2 =>
      Prod.ext (show p.1 = p'.1 from congrArg (Prod.fst : Lattice4 × Fin 4 → Lattice4) e2) e1)
  have s2 := sum_comp_bond_le (P := P) f hf secondBond (fun p hp => (bonds_mem_bondsOf hp).2.1)
    (fun p _ p' _ e1 e2 => by
      have h := congrArg Prod.fst e2
      simp only [secondBond] at h
      rw [e1] at h
      exact Prod.ext (add_right_cancel h) e1)
  have s3 := sum_comp_bond_le (P := P) f hf thirdBond (fun p hp => (bonds_mem_bondsOf hp).2.2.1)
    (fun p _ p' _ e1 e2 => by
      have h := congrArg Prod.fst e2
      simp only [thirdBond] at h
      rw [e1] at h
      exact Prod.ext (add_right_cancel h) e1)
  have s4 := sum_comp_bond_le (P := P) f hf fourthBond (fun p hp => (bonds_mem_bondsOf hp).2.2.2)
    (fun p _ p' _ e1 e2 =>
      Prod.ext (show p.1 = p'.1 from congrArg (Prod.fst : Lattice4 × Fin 4 → Lattice4) e2) e1)
  unfold boundarySum
  simp only [Finset.sum_add_distrib]
  linarith only [s1, s2, s3, s4]
theorem sum_boundarySum_pow_four_le {P : Finset Lattice4} (f : Lattice4 × Fin 4 → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ p ∈ orientedPlaquettesOf P, boundarySum f p ^ 4 ≤ 4096 * ∑ b ∈ bondsOf P, f b ^ 4 := by
  have h1 : ∑ p ∈ orientedPlaquettesOf P, boundarySum f p ^ 4 ≤
      ∑ p ∈ orientedPlaquettesOf P, 64 * boundarySum (fun b => f b ^ 4) p :=
    Finset.sum_le_sum fun p _ => add_add_add_pow_four_le _ _ _ _
  have h2 := sum_boundarySum_le (P := P) (fun b => f b ^ 4) (fun b => by positivity)
  rw [← Finset.mul_sum] at h1
  linarith only [h1, h2]
theorem sum_add_boundarySum_pow_four_le {P : Finset Lattice4} (f g : Lattice4 × Fin 4 → ℝ) (hf : ∀ b, 0 ≤ f b)
    (hg : ∀ b, 0 ≤ g b) :
    ∑ p ∈ orientedPlaquettesOf P, (boundarySum f p + boundarySum g p) ^ 4 ≤
      32768 * ∑ b ∈ bondsOf P, (f b ^ 4 + g b ^ 4) := by
  have h1 : ∑ p ∈ orientedPlaquettesOf P, (boundarySum f p + boundarySum g p) ^ 4 ≤
      ∑ p ∈ orientedPlaquettesOf P, 512 * boundarySum (fun b => f b ^ 4 + g b ^ 4) p := by
    refine Finset.sum_le_sum fun p _ => ?_
    have b1 := add_pow_four_le (boundarySum f p) (boundarySum g p)
    have b2 : boundarySum f p ^ 4 ≤
        64 * (f (firstBond p) ^ 4 + f (secondBond p) ^ 4 + f (thirdBond p) ^ 4 + f (fourthBond p) ^ 4) :=
      add_add_add_pow_four_le _ _ _ _
    have b3 : boundarySum g p ^ 4 ≤
        64 * (g (firstBond p) ^ 4 + g (secondBond p) ^ 4 + g (thirdBond p) ^ 4 + g (fourthBond p) ^ 4) :=
      add_add_add_pow_four_le _ _ _ _
    unfold boundarySum at b1 b2 b3 ⊢
    linarith only [b1, b2, b3]
  have h2 := sum_boundarySum_le (P := P) (fun b => f b ^ 4 + g b ^ 4) (fun b => by positivity)
  rw [← Finset.mul_sum] at h1
  linarith only [h1, h2]
def plaquetteDistance (T W : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  ‖((plaquetteHolonomy T q : UnitQuaternion) : ℍ[ℝ]) - ((plaquetteHolonomy W q : UnitQuaternion) : ℍ[ℝ])‖
theorem plaquetteDistance_swap (T W : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteDistance T W (x, ν, μ) = plaquetteDistance T W (x, μ, ν) := by
  unfold plaquetteDistance
  rw [plaquetteHolonomy_swap T, plaquetteHolonomy_swap W, norm_coe_inv_sub_coe_inv]
theorem plaquetteDistance_sitePlaquette (T W : F.GaugeField 0) (u : Lattice4) (μ ν : Fin 4) :
    plaquetteDistance T W (sitePlaquette S z (u, μ, ν)) =
      plaquetteDistance T W (patchSite S z (lowCorner S z u μ ν), μ, ν) := by
  simp only [sitePlaquette]
  rcases le_total μ ν with hl | hl
  · rw [min_eq_left hl, max_eq_right hl]
  · rw [min_eq_right hl, max_eq_left hl, plaquetteDistance_swap]
theorem sum_plaquetteDistance_sq_le {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hm : 32 ≤ m) (hreg : IsOrthantRegular S m)
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (T W : F.GaugeField 0) :
    ∑ p ∈ orientedPlaquettesOf (patchDomain S z), plaquetteDistance T W (sitePlaquette S z p) ^ 2 ≤
      2 * ∑ q ∈ patchPlaquettes S z, plaquetteDistance T W q ^ 2 := by
  classical
  have hf : ∀ q, 0 ≤ plaquetteDistance T W q ^ 2 := fun q => sq_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not (orientedPlaquettesOf (patchDomain S z)) (fun p => p.2.1 < p.2.2)]
  have hsub1 : (orientedPlaquettesOf (patchDomain S z)).filter (fun p => p.2.1 < p.2.2) ⊆
      orientedPlaquettesOf (patchDomain S z) :=
    Finset.filter_subset _ _
  have hsub2 : (orientedPlaquettesOf (patchDomain S z)).filter (fun p => ¬ p.2.1 < p.2.2) ⊆
      orientedPlaquettesOf (patchDomain S z) :=
    Finset.filter_subset _ _
  have a1 := sum_comp_le_of_injOn _ (patchPlaquettes S z) (sitePlaquette S z)
    (fun q => plaquetteDistance T W q ^ 2) hf
    (fun p hp => sitePlaquette_mem_patchPlaquettes hamb hodd hm hreg (hsub1 hp))
    (sitePlaquette_injOn hamb hodd hs _ hsub1 (Or.inl fun p hp => (Finset.mem_filter.1 hp).2))
  have a2 := sum_comp_le_of_injOn _ (patchPlaquettes S z) (sitePlaquette S z)
    (fun q => plaquetteDistance T W q ^ 2) hf
    (fun p hp => sitePlaquette_mem_patchPlaquettes hamb hodd hm hreg (hsub2 hp))
    (sitePlaquette_injOn hamb hodd hs _ hsub2 (Or.inr fun p hp => by
      have h1 := (Finset.mem_filter.1 hp).2
      have h2 := hsub2 hp
      have h3 : p.2.1 ≠ p.2.2 := (Finset.mem_filter.1 h2).2.1
      exact lt_of_le_of_ne (not_lt.1 h1) h3.symm))
  linarith only [a1, a2]
theorem norm_plaquetteCurl_le_boundarySum {V : F.GaugeField F.top} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion) {p : Lattice4 × Fin 4 × Fin 4}
    (hp : p ∈ orientedPlaquettesOf (patchDomain S z)) :
    ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W γ a i : UnitQuaternion) : ℍ[ℝ]))
        p.1 p.2.1 p.2.2‖ ≤
      plaquetteDistance (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) W (sitePlaquette S z p) +
        4 * boundarySum (fun b => normSubOne (gaugedGap S V z X W γ b.1 b.2)) p *
          (boundarySum (fun b => normSubOne (gaugedGap S V z X W γ b.1 b.2)) p +
            boundarySum (fun b => normSubOne (framedLatticeField S V z W b.1 b.2)) p) := by
  obtain ⟨u, μ, ν⟩ := p
  obtain ⟨h0, -, h1, h2, h3⟩ := mem_orientedPlaquettesOf hp
  rw [plaquetteDistance_sitePlaquette]
  exact norm_plaquetteCurl_le (V := V) hamb hodd hs X W γ h0 h1 h2 h3
theorem curlGapBound : curlGapBoundStatement := by
  classical
  refine ⟨2048 * 4096 * 32768, by norm_num, ?_⟩
  intro F m S V z X W γ hodd hamb hm hreg
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have ha0 : ∀ b : Lattice4 × Fin 4, 0 ≤ normSubOne (gaugedGap S V z X W γ b.1 b.2) :=
    fun b => normSubOne_nonneg _
  have hw0 : ∀ b : Lattice4 × Fin 4, 0 ≤ normSubOne (framedLatticeField S V z W b.1 b.2) :=
    fun b => normSubOne_nonneg _
  exact sq_sum_sq_le_of_pointwise (orientedPlaquettesOf (patchDomain S z))
    (fun p => plaquetteDistance (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) W (sitePlaquette S z p))
    (fun p => ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W γ a i : UnitQuaternion) : ℍ[ℝ]))
      p.1 p.2.1 p.2.2‖)
    (boundarySum fun b => normSubOne (gaugedGap S V z X W γ b.1 b.2))
    (fun p => boundarySum (fun b => normSubOne (gaugedGap S V z X W γ b.1 b.2)) p +
      boundarySum (fun b => normSubOne (framedLatticeField S V z W b.1 b.2)) p)
    (∑ q ∈ patchPlaquettes S z, plaquetteDistance (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) W q ^ 2)
    (∑ b ∈ bondsOf (patchDomain S z), normSubOne (gaugedGap S V z X W γ b.1 b.2) ^ 4)
    (∑ b ∈ bondsOf (patchDomain S z), (normSubOne (gaugedGap S V z X W γ b.1 b.2) ^ 4 +
      normSubOne (framedLatticeField S V z W b.1 b.2) ^ 4))
    (fun p hp => norm_plaquetteCurl_le_boundarySum hamb hodd hs X W γ hp) (fun p => norm_nonneg _)
    (sum_plaquetteDistance_sq_le hamb hodd (by omega : 32 ≤ m) hreg hs _ W)
    (sum_boundarySum_pow_four_le _ ha0) (sum_add_boundarySum_pow_four_le _ _ ha0 hw0)
    (boundarySum_nonneg ha0) (fun p => add_nonneg (boundarySum_nonneg ha0 p) (boundarySum_nonneg hw0 p))
    (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
end PatchCurls
end YangMills.Construction
end
