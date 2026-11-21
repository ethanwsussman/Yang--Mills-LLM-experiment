import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatchProof
import YangMills.Construction.ColdChainAtEveryLevel.QuarticGaugeOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchQuarticGauge
open BlockAverages LatticeFractionalIntegration GaugeMap BlockAverages.PatchLocality
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem patchSite_add_smul_basisVector (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (w : Lattice4) (i : Fin 4) :
    patchSite S z (w + (closedOrthant S z i) • basisVector i) = patchSite S z w + unitStep 0 i := by apply _root_.YangMills.Construction.PatchCurls.patchSite_add_smul_basisVector <;> assumption
theorem patchSite_add_basisVector_of_pos (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (w : Lattice4) {i : Fin 4} (h : closedOrthant S z i = 1) :
    patchSite S z (w + basisVector i) = patchSite S z w + unitStep 0 i := by apply _root_.YangMills.Construction.PatchCurls.patchSite_add_basisVector_of_pos <;> assumption
theorem patchSite_eq_add_basisVector_of_neg (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (w : Lattice4) {i : Fin 4} (h : closedOrthant S z i = -1) :
    patchSite S z w = patchSite S z (w + basisVector i) + unitStep 0 i := by apply _root_.YangMills.Construction.PatchCurls.patchSite_eq_add_basisVector_of_neg <;> assumption
theorem plaquetteHolonomy_eq (X : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep 0 μ) ν * (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹ := by apply _root_.YangMills.Construction.PatchCurls.plaquetteHolonomy_eq <;> assumption
def chartField (S : Finset F.Cell) (z : F.Cell) (X : F.GaugeField 0) : Lattice4 → Fin 4 → UnitQuaternion :=
  fun u i => if closedOrthant S z i = 1 then X (patchSite S z u) i
    else (X (patchSite S z (u + basisVector i)) i)⁻¹
def baseCorner (S : Finset F.Cell) (z : F.Cell) (u : Lattice4) (μ ν : Fin 4) : Lattice4 :=
  u + (if closedOrthant S z μ = 1 then 0 else basisVector μ) +
    (if closedOrthant S z ν = 1 then 0 else basisVector ν)
theorem normSubOne_latticePlaquette_chartField
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (X : F.GaugeField 0) (u : Lattice4)
    (μ ν : Fin 4) :
    normSubOne (latticePlaquette (chartField S z X) u μ ν) =
      normSubOne (plaquetteHolonomy X (patchSite S z (baseCorner S z u μ ν), μ, ν)) := by
  unfold normSubOne
  rw [plaquetteHolonomy_eq]
  have hne : (-1 : ℤ) ≠ 1 := by norm_num
  have c1 : u + basisVector μ + basisVector ν = u + basisVector ν + basisVector μ := by abel
  rcases hs μ with h1 | h1 <;> rcases hs ν with h2 | h2
  · have a1 : baseCorner S z u μ ν = u := by simp [baseCorner, h1, h2]
    have b1 := patchSite_add_basisVector_of_pos hs u h1
    have b2 := patchSite_add_basisVector_of_pos hs u h2
    rw [a1]
    simp only [latticePlaquette, chartField, h1, h2, if_true, b1, b2]
  · have a1 : baseCorner S z u μ ν = u + basisVector ν := by simp [baseCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector ν) := ⟨_, rfl⟩
    have e1 : patchSite S z u = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs u h2
    have e2 : patchSite S z (u + basisVector ν + basisVector μ) = x + unitStep 0 μ := by
      rw [hx]; exact patchSite_add_basisVector_of_pos hs _ h1
    have e3 : patchSite S z (u + basisVector μ) =
        patchSite S z (u + basisVector ν + basisVector μ) + unitStep 0 ν := by
      rw [patchSite_eq_add_basisVector_of_neg hs (u + basisVector μ) h2, c1]
    rw [← hx]
    have hk : latticePlaquette (chartField S z X) u μ ν = (X x ν)⁻¹ *
        (X x μ * X (x + unitStep 0 μ) ν * (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹)⁻¹ * ((X x ν)⁻¹)⁻¹ := by
      simp only [latticePlaquette, chartField, h1, h2, if_true, hne, if_false, c1, ← hx, e1, e2]
      group
    rw [hk, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
  · have a1 : baseCorner S z u μ ν = u + basisVector μ := by simp [baseCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector μ) := ⟨_, rfl⟩
    have e1 : patchSite S z u = x + unitStep 0 μ := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs u h1
    have e2 : patchSite S z (u + basisVector μ + basisVector ν) = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_add_basisVector_of_pos hs _ h2
    rw [← hx]
    have hk : latticePlaquette (chartField S z X) u μ ν = (X x μ)⁻¹ *
        (X x μ * X (x + unitStep 0 μ) ν * (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹)⁻¹ * ((X x μ)⁻¹)⁻¹ := by
      simp only [latticePlaquette, chartField, h1, h2, if_true, hne, if_false, ← c1, ← hx, e1, e2]
      group
    rw [hk, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
  · have a1 : baseCorner S z u μ ν = u + basisVector μ + basisVector ν := by simp [baseCorner, h1, h2]
    rw [a1]
    obtain ⟨x, hx⟩ : ∃ x, x = patchSite S z (u + basisVector μ + basisVector ν) := ⟨_, rfl⟩
    have e1 : patchSite S z (u + basisVector μ) = x + unitStep 0 ν := by
      rw [hx]; exact patchSite_eq_add_basisVector_of_neg hs _ h2
    have e2 : patchSite S z (u + basisVector ν) = x + unitStep 0 μ := by
      rw [hx, c1]; exact patchSite_eq_add_basisVector_of_neg hs _ h1
    rw [← hx]
    have hk : latticePlaquette (chartField S z X) u μ ν = ((X x ν) * (X (x + unitStep 0 ν) μ))⁻¹ *
        (X x μ * X (x + unitStep 0 μ) ν * (X (x + unitStep 0 ν) μ)⁻¹ * (X x ν)⁻¹) *
        (((X x ν) * (X (x + unitStep 0 ν) μ))⁻¹)⁻¹ := by
      simp only [latticePlaquette, chartField, h1, h2, if_true, hne, if_false, ← c1, ← hx, e1, e2]
      group
    rw [hk, norm_coe_conj_sub_one]
theorem plaquetteHolonomy_swap (X : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, ν, μ) = (plaquetteHolonomy X (x, μ, ν))⁻¹ := by apply _root_.YangMills.Construction.PatchCurls.plaquetteHolonomy_swap <;> assumption
theorem baseCorner_comm (u : Lattice4) (μ ν : Fin 4) : baseCorner S z u μ ν = baseCorner S z u ν μ := by
  unfold baseCorner
  abel
theorem patchChart_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {w : Lattice4} (hw : ∀ i, |w i - (cellSideLength F - 1) / 2| < 32 * cellSideLength F) :
    patchChart S z (patchSite S z w) = w := by apply _root_.YangMills.Construction.PatchCurls.patchChart_patchSite <;> assumption
theorem abs_sub_half_lt_of_mem_patchDomain (hodd : Odd F.blockSide) {w : Lattice4} (hw : w ∈ patchDomain S z)
    (i : Fin 4) : |w i - (cellSideLength F - 1) / 2| < 32 * cellSideLength F := by apply _root_.YangMills.Construction.PatchCurls.abs_sub_half_lt_of_mem_patchDomain <;> assumption
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem patchSite_mem_sitesOfCells {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hm : 32 ≤ m)
    (hreg : IsOrthantRegular S m) {w : Lattice4} (hw : w ∈ patchDomain S z) :
    patchSite S z w ∈ sitesOfCells S 0 := by apply _root_.YangMills.Construction.PatchCurls.patchSite_mem_sitesOfCells <;> assumption
theorem sum_comp_le_of_injOn {α β : Type} [DecidableEq β] (A : Finset α) (Q : Finset β) (φ : α → β)
    (f : β → ℝ) (hf : ∀ q, 0 ≤ f q) (hm : ∀ a ∈ A, φ a ∈ Q) (hi : Set.InjOn φ A) :
    ∑ a ∈ A, f (φ a) ≤ ∑ q ∈ Q, f q := by apply _root_.YangMills.Construction.PatchCurls.sum_comp_le_of_injOn <;> assumption
def sitePlaquette (S : Finset F.Cell) (z : F.Cell) (p : Lattice4 × Fin 4 × Fin 4) : F.Site 0 × Fin 4 × Fin 4 :=
  (patchSite S z (baseCorner S z p.1 p.2.1 p.2.2), min p.2.1 p.2.2, max p.2.1 p.2.2)
theorem sitePlaquette_mem_patchPlaquettes {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hm : 32 ≤ m) (hreg : IsOrthantRegular S m) {p : Lattice4 × Fin 4 × Fin 4}
    (hp : p ∈ orientedPlaquettesOf (patchDomain S z)) :
    sitePlaquette S z p ∈ patchPlaquettes S z := by apply _root_.YangMills.Construction.PatchCurls.sitePlaquette_mem_patchPlaquettes <;> assumption
theorem normSubOne_sitePlaquette (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (X : F.GaugeField 0) (p : Lattice4 × Fin 4 × Fin 4) :
    normSubOne (latticePlaquette (chartField S z X) p.1 p.2.1 p.2.2) =
      normSubOne (plaquetteHolonomy X (sitePlaquette S z p)) := by
  obtain ⟨u, μ, ν⟩ := p
  rw [normSubOne_latticePlaquette_chartField hs]
  simp only [sitePlaquette]
  rcases le_total μ ν with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, baseCorner_comm u μ ν, plaquetteHolonomy_swap]
    unfold normSubOne
    rw [norm_coe_inv_sub_one, baseCorner_comm u ν μ]
theorem sitePlaquette_injOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (A : Finset (Lattice4 × Fin 4 × Fin 4)) (hA : A ⊆ orientedPlaquettesOf (patchDomain S z))
    (hord : (∀ p ∈ A, p.2.1 < p.2.2) ∨ ∀ p ∈ A, p.2.2 < p.2.1) :
    Set.InjOn (sitePlaquette S z) A := by apply _root_.YangMills.Construction.PatchCurls.sitePlaquette_injOn <;> assumption
theorem patchQuarticGauge (hquartic : quarticGaugeStatement) : patchQuarticGaugeStatement := by
  classical
  obtain ⟨C, c, hC, hc, h⟩ := hquartic
  refine ⟨2 * C, c / 2, by positivity, by positivity, ?_⟩
  intro F m S hodd hamb hm hreg z X ε hz hε0 hεc hsum
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have hL : 0 < F.blockSide := hodd.pos
  have hNp := cellSideLength_pos (F := F) hL
  have hNz : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hNpos : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
  have hplaq : ∑ p ∈ orientedPlaquettesOf (patchDomain S z),
      ‖((latticePlaquette (chartField S z X) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤
        (2 * ε) ^ 2 := by
    have hf : ∀ q : F.Site 0 × Fin 4 × Fin 4, 0 ≤ normSubOne (plaquetteHolonomy X q) ^ 2 :=
      fun q => sq_nonneg _
    have e1 : ∀ p ∈ orientedPlaquettesOf (patchDomain S z),
        ‖((latticePlaquette (chartField S z X) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 =
          normSubOne (plaquetteHolonomy X (sitePlaquette S z p)) ^ 2 := by
      intro p _
      rw [← normSubOne_sitePlaquette hs]
      rfl
    rw [Finset.sum_congr rfl e1,
      ← Finset.sum_filter_add_sum_filter_not (orientedPlaquettesOf (patchDomain S z)) (fun p => p.2.1 < p.2.2)]
    have hsub1 : (orientedPlaquettesOf (patchDomain S z)).filter (fun p => p.2.1 < p.2.2) ⊆
        orientedPlaquettesOf (patchDomain S z) :=
      Finset.filter_subset _ _
    have hsub2 : (orientedPlaquettesOf (patchDomain S z)).filter (fun p => ¬ p.2.1 < p.2.2) ⊆
        orientedPlaquettesOf (patchDomain S z) :=
      Finset.filter_subset _ _
    have a1 := sum_comp_le_of_injOn _ (patchPlaquettes S z) (sitePlaquette S z)
      (fun q => normSubOne (plaquetteHolonomy X q) ^ 2) hf
      (fun p hp => sitePlaquette_mem_patchPlaquettes hamb hodd (by omega : 32 ≤ m) hreg (hsub1 hp))
      (sitePlaquette_injOn hamb hodd hs _ hsub1 (Or.inl fun p hp => (Finset.mem_filter.1 hp).2))
    have a2 := sum_comp_le_of_injOn _ (patchPlaquettes S z) (sitePlaquette S z)
      (fun q => normSubOne (plaquetteHolonomy X q) ^ 2) hf
      (fun p hp => sitePlaquette_mem_patchPlaquettes hamb hodd (by omega : 32 ≤ m) hreg (hsub2 hp))
      (sitePlaquette_injOn hamb hodd hs _ hsub2 (Or.inr fun p hp => by
        have h1 := (Finset.mem_filter.1 hp).2
        have h2 := hsub2 hp
        have h3 : p.2.1 ≠ p.2.2 := (Finset.mem_filter.1 h2).2.1
        exact lt_of_le_of_ne (not_lt.1 h1) h3.symm))
    have hsum' : ∑ q ∈ patchPlaquettes S z, normSubOne (plaquetteHolonomy X q) ^ 2 ≤ ε ^ 2 := hsum
    nlinarith [sq_nonneg ε]
  have hz10 : z ∈ cellBall S z 10 := Finset.mem_filter.2 ⟨hz, by rw [cellSupDist_self]; omega⟩
  have hcorner : ∀ a ∈ patchCorners S z, ∀ i, -(10 * ((F.blockSide ^ F.top : ℕ) : ℤ)) ≤ a i ∧
      a i ≤ 12 * ((F.blockSide ^ F.top : ℕ) : ℤ) := by
    intro a ha i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    have hd := (Finset.mem_filter.1 hy).2
    have h1 : |cellDisplacement z y i| ≤ cellSupDist y z := abs_cellDisplacement_le i
    rw [cellSupDist_comm] at h1
    have h2 : ((cellSupDist z y : ℕ) : ℤ) ≤ 10 := by exact_mod_cast hd
    have h3 := abs_le.1 (h1.trans h2)
    rw [hNz]
    simp only []
    rcases hs i with h | h <;> rw [h] <;> constructor <;> nlinarith [h3.1, h3.2]
  have hmemP : ∀ x, x ∈ patchDomain S z ↔ (∀ i, x i ≤ 21 * ((F.blockSide ^ F.top : ℕ) : ℤ) - 1) ∧
      ∃ a ∈ patchCorners S z, ∀ i, a i ≤ x i := by
    intro x
    rw [hNz]
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact ⟨fun i => (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 h1 i)).2, h2⟩
    · rintro ⟨h1, a, ha, hax⟩
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, h1 i⟩, a, ha, hax⟩
      have := (hcorner a ha i).1
      rw [hNz] at this
      exact this.trans (hax i)
  obtain ⟨γ, hγ⟩ := h (F.blockSide ^ F.top) (patchCorners S z) (patchDomain S z) (chartField S z X) (2 * ε) hNpos
    ⟨_, Finset.mem_image.2 ⟨z, hz10, rfl⟩⟩ hcorner hmemP (by positivity) (by linarith) hplaq
  refine ⟨fun s => γ (patchChart S z s), ?_⟩
  have hlocal : ∀ b ∈ patchInnerBonds S z 0, ∃ u ∈ patchDomain S z, b.1 = patchSite S z u ∧
      patchChart S z b.1 = u ∧ u + (closedOrthant S z b.2) • basisVector b.2 ∈ patchDomain S z ∧
      patchChart S z (b.1 + unitStep 0 b.2) = u + (closedOrthant S z b.2) • basisVector b.2 := by
    intro b hb
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hb
    rw [baseSite_zero] at h1 h2
    obtain ⟨u, hu, e⟩ := Finset.mem_image.1 h1
    obtain ⟨u', hu', e'⟩ := Finset.mem_image.1 h2
    have c1 : patchChart S z b.1 = u := by
      rw [← e]
      exact patchChart_patchSite hamb hodd hs (abs_sub_half_lt_of_mem_patchDomain hodd hu)
    have c2 : patchChart S z (b.1 + unitStep 0 b.2) = u' := by
      rw [← e']
      exact patchChart_patchSite hamb hodd hs (abs_sub_half_lt_of_mem_patchDomain hodd hu')
    have c3 : patchSite S z u' = patchSite S z (u + (closedOrthant S z b.2) • basisVector b.2) := by
      rw [e', patchSite_add_smul_basisVector hs, e]
    have hb2 : ∀ i, |(u + (closedOrthant S z b.2) • basisVector b.2) i - (cellSideLength F - 1) / 2| <
        32 * cellSideLength F := by
      intro i
      have hN := cellSideLength_pos (F := F) hL
      obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
      have h3 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hu).1 i)
      have h4 := abs_basisVector_le b.2 i
      have h5 := abs_le.1 h4
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [abs_lt]
      rcases hs b.2 with h | h <;> rw [h] <;> constructor <;> omega
    have c4 : u' = u + (closedOrthant S z b.2) • basisVector b.2 := by
      have := congrArg (patchChart S z) c3
      rwa [patchChart_patchSite hamb hodd hs (abs_sub_half_lt_of_mem_patchDomain hodd hu'),
        patchChart_patchSite hamb hodd hs hb2] at this
    exact ⟨u, hu, e.symm, c1, c4 ▸ hu', c2.trans c4⟩
  have hfB : ∀ b : Lattice4 × Fin 4,
      0 ≤ ‖((latticeGaugeTransform γ (chartField S z X) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 :=
    fun b => by positivity
  obtain ⟨ψ, hψ⟩ : ∃ ψ : F.Site 0 × Fin 4 → Lattice4 × Fin 4, ψ = fun b =>
    (if closedOrthant S z b.2 = 1 then patchChart S z b.1 else patchChart S z (b.1 + unitStep 0 b.2), b.2) :=
    ⟨_, rfl⟩
  have hψmem : ∀ b ∈ patchInnerBonds S z 0, ψ b ∈ bondsOf (patchDomain S z) := by
    intro b hb
    obtain ⟨u, hu, e, c1, hu', c2⟩ := hlocal b hb
    rw [hψ]
    simp only [bondsOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    rcases hs b.2 with h | h
    · rw [if_pos h, c1]
      rw [h, one_smul] at hu'
      exact ⟨hu, hu'⟩
    · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
      rw [if_neg hne, c2]
      rw [h] at hu' ⊢
      refine ⟨hu', ?_⟩
      have : u + (-1 : ℤ) • basisVector b.2 + basisVector b.2 = u := by simp
      rw [this]
      exact hu
  have hψval : ∀ b ∈ patchInnerBonds S z 0,
      normSubOne (gaugeTransform (fun s => γ (patchChart S z s)) X b.1 b.2) ^ 4 =
        ‖((latticeGaugeTransform γ (chartField S z X) (ψ b).1 (ψ b).2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 := by
    intro b hb
    obtain ⟨u, hu, e, c1, hu', c2⟩ := hlocal b hb
    rw [hψ]
    rcases hs b.2 with h | h
    · simp only [if_pos h, c1]
      rw [h, one_smul] at c2
      congr 2
      simp only [latticeGaugeTransform, chartField, if_pos h, gaugeTransform]
      rw [c1, c2, ← e]
    · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
      simp only [if_neg hne, c2]
      rw [h] at c2 ⊢
      have e3 : u + (-1 : ℤ) • basisVector b.2 + basisVector b.2 = u := by simp
      have e4 : gaugeTransform (fun s => γ (patchChart S z s)) X b.1 b.2 =
          (latticeGaugeTransform γ (chartField S z X) (u + (-1 : ℤ) • basisVector b.2) b.2)⁻¹ := by
        simp only [latticeGaugeTransform, chartField, if_neg hne, gaugeTransform, e3, c1, c2]
        rw [← e]
        group
      rw [e4]
      unfold normSubOne
      rw [norm_coe_inv_sub_one]
  have hψinj : Set.InjOn ψ (patchInnerBonds S z 0 : Finset _) := by
    intro b hb b' hb' he
    obtain ⟨u, hu, e, c1, hu', c2⟩ := hlocal b hb
    obtain ⟨v, hv, e', d1, hv', d2⟩ := hlocal b' hb'
    have hdir : b.2 = b'.2 := by
      have := congrArg Prod.snd he
      rw [hψ] at this
      exact this
    have hcoord := congrArg Prod.fst he
    rw [hψ] at hcoord
    simp only at hcoord
    have huv : u = v := by
      rw [← hdir] at hcoord d2
      rcases hs b.2 with h | h
      · rw [if_pos h, if_pos h, c1, d1] at hcoord
        exact hcoord
      · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
        rw [if_neg hne, if_neg hne, c2, d2] at hcoord
        exact add_right_cancel hcoord
    exact Prod.ext (by rw [e, e', huv]) hdir
  have hsumB := sum_comp_le_of_injOn (patchInnerBonds S z 0) (bondsOf (patchDomain S z)) ψ
    (fun b => ‖((latticeGaugeTransform γ (chartField S z X) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
    hfB hψmem hψinj
  refine (Finset.sum_congr rfl hψval).trans_le (hsumB.trans (hγ.trans (le_of_eq ?_)))
  ring
end YangMills.Construction.PatchQuarticGauge
end
