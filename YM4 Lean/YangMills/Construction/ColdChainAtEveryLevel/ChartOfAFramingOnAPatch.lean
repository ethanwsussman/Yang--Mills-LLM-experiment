import YangMills.Construction.ColdChainAtEveryLevel.FormsInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGauge
import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchLatticeChart
open BlockAverages GaugeMap LatticeFractionalIntegration PatchPoints PatchForms
variable {F : BlockFrame}
def latticeField (S : Finset F.Cell) (z : F.Cell) (X : F.GaugeField 0) : Lattice4 → Fin 4 → UnitQuaternion :=
  fun u i => if closedOrthant S z i = 1 then X (patchSite S z u) i
    else (X (patchSite S z (u + basisVector i)) i)⁻¹
def framedLatticeField (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (X : F.GaugeField 0) :
    Lattice4 → Fin 4 → UnitQuaternion :=
  fun u i => (frameChange S V z (patchSite S z u))⁻¹ * latticeField S z X u i *
    frameChange S V z (patchSite S z (u + basisVector i))
def siteGaugeOfLatticeGauge (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (γ : Lattice4 → UnitQuaternion) : F.Site 0 → UnitQuaternion :=
  fun s => frameChange S V z s * γ (patchChart S z s)
def siteBond (S : Finset F.Cell) (z : F.Cell) (b : Lattice4 × Fin 4) : F.Site 0 × Fin 4 :=
  if closedOrthant S z b.2 = 1 then (patchSite S z b.1, b.2)
  else (patchSite S z (b.1 + basisVector b.2), b.2)
namespace Framing
variable {S : Finset F.Cell} {z : F.Cell} {V : F.GaugeField F.top}
theorem baseSite_eq_self (x : F.Site 0) : baseSite x = x := baseSite_depth_zero x
theorem siteBond_mem_patchInnerBonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hm : 32 ≤ m) (hreg : IsOrthantRegular S m)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {b : Lattice4 × Fin 4} (hb : b ∈ bondsOf (patchDomain S z)) : siteBond S z b ∈ patchInnerBonds S z 0 := by
  classical
  have hb' := Finset.mem_filter.1 hb
  have h1 : b.1 ∈ patchDomain S z := (Finset.mem_product.1 hb'.1).1
  have h2 : b.1 + basisVector b.2 ∈ patchDomain S z := hb'.2
  have s1 : patchSite S z b.1 ∈ patchBaseSites S z := Finset.mem_image_of_mem _ h1
  have s2 : patchSite S z (b.1 + basisVector b.2) ∈ patchBaseSites S z := Finset.mem_image_of_mem _ h2
  have t1 := patchSite_mem_sitesOfCells hamb hodd hreg hm h1
  have t2 := patchSite_mem_sitesOfCells hamb hodd hreg hm h2
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases hsign b.1 b.2
  unfold siteBond
  rcases hsign b.2 with h | h
  · rw [if_pos h]
    have e := k1 h
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨t1, Finset.mem_univ _⟩, ?_⟩, ?_, ?_⟩
    · show patchSite S z b.1 + unitStep 0 b.2 ∈ _
      rw [← e]
      exact t2
    · rw [baseSite_eq_self]
      exact s1
    · rw [baseSite_eq_self]
      show patchSite S z b.1 + unitStep 0 b.2 ∈ _
      rw [← e]
      exact s2
  · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
    rw [if_neg hne]
    have e := k2 h
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨t2, Finset.mem_univ _⟩, ?_⟩, ?_, ?_⟩
    · show patchSite S z (b.1 + basisVector b.2) + unitStep 0 b.2 ∈ _
      rw [← e]
      exact t1
    · rw [baseSite_eq_self]
      exact s2
    · rw [baseSite_eq_self]
      show patchSite S z (b.1 + basisVector b.2) + unitStep 0 b.2 ∈ _
      rw [← e]
      exact s1
theorem siteBond_injOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    Set.InjOn (siteBond S z) (bondsOf (patchDomain S z) : Set (Lattice4 × Fin 4)) := by
  classical
  intro b hb c hc e
  have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
  have hc' := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
  have b1 : b.1 ∈ patchDomain S z := (Finset.mem_product.1 hb'.1).1
  have c1 : c.1 ∈ patchDomain S z := (Finset.mem_product.1 hc'.1).1
  have h2 : b.2 = c.2 := by
    have := congrArg Prod.snd e
    unfold siteBond at this
    split_ifs at this <;> exact this
  have hinj := patchSite_injOn hamb hodd hsign
  have h3 : b.1 = c.1 := by
    have e1 := congrArg Prod.fst e
    unfold siteBond at e1
    rw [← h2] at e1
    split_ifs at e1 with hs
    · exact hinj b1 c1 e1
    · have hc2 : c.1 + basisVector b.2 ∈ patchDomain S z := by
        rw [h2]
        exact hc'.2
      have := hinj (Finset.mem_coe.2 hb'.2) (Finset.mem_coe.2 hc2) e1
      exact add_right_cancel this
  exact Prod.ext h3 h2
theorem siteBond_surjOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    Set.SurjOn (siteBond S z) (bondsOf (patchDomain S z) : Set (Lattice4 × Fin 4))
      (patchInnerBonds S z 0 : Set (F.Site 0 × Fin 4)) := by
  classical
  intro c hc
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
  rw [baseSite_eq_self] at h1 h2
  obtain ⟨a, ha, ha', hcase⟩ := exists_bond_in_patchChart hamb hodd hsign h1 h2
  refine ⟨(a, c.2), Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, Finset.mem_univ _⟩, ha'⟩), ?_⟩
  unfold siteBond
  rcases hcase with ⟨hs, e1, e2⟩ | ⟨hs, e1, e2⟩
  · simp only [hs, if_true]
    exact Prod.ext e1 rfl
  · have hne : closedOrthant S z c.2 ≠ 1 := by rw [hs]; norm_num
    simp only [if_neg hne]
    exact Prod.ext e2 rfl
theorem sum_bondsOf_siteBond {M : Type} [AddCommMonoid M] (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {m : ℕ} (hm : 32 ≤ m) (hreg : IsOrthantRegular S m)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (g : F.Site 0 × Fin 4 → M) :
    ∑ b ∈ bondsOf (patchDomain S z), g (siteBond S z b) = ∑ c ∈ patchInnerBonds S z 0, g c :=
  Finset.sum_nbij (siteBond S z) (fun _ hb => siteBond_mem_patchInnerBonds hamb hodd hm hreg hsign hb)
    (siteBond_injOn hamb hodd hsign) (siteBond_surjOn hamb hodd hsign) (fun _ _ => rfl)
theorem siteGaugeOfLatticeGauge_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (γ : Lattice4 → UnitQuaternion) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    siteGaugeOfLatticeGauge S V z γ (patchSite S z a) = frameChange S V z (patchSite S z a) * γ a := by
  unfold siteGaugeOfLatticeGauge
  rw [patchChart_patchSite hamb hodd hsign (patchDomain_coord_bounds ha)]
theorem latticeField_gaugeTransform (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (γ : Lattice4 → UnitQuaternion) (X : F.GaugeField 0) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i =
      frameChange S V z (patchSite S z a) * latticeGaugeTransform γ (latticeField S z X) a i *
        (frameChange S V z (patchSite S z (a + basisVector i)))⁻¹ := by
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases hsign a i
  have g1 := siteGaugeOfLatticeGauge_patchSite (V := V) hamb hodd hsign γ ha
  have g2 := siteGaugeOfLatticeGauge_patchSite (V := V) hamb hodd hsign γ ha'
  unfold latticeField latticeGaugeTransform
  rcases hsign i with h | h
  · simp only [h, if_true]
    unfold gaugeTransform
    rw [← k1 h, g1, g2]
    group
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    simp only [if_neg hne]
    unfold gaugeTransform
    rw [← k2 h, g1, g2]
    group
theorem latticeGaugeTransform_mul_inv_framed (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (γ : Lattice4 → UnitQuaternion) (X W : F.GaugeField 0) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    latticeGaugeTransform γ (latticeField S z X) a i * (framedLatticeField S V z W a i)⁻¹ =
      (frameChange S V z (patchSite S z a))⁻¹ *
        (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) a i * (latticeField S z W a i)⁻¹) *
          frameChange S V z (patchSite S z a) := by
  rw [latticeField_gaugeTransform (V := V) hamb hodd hsign γ X ha ha']
  unfold framedLatticeField
  group
theorem norm_latticeField_mul_inv_sub_one (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (T W : F.GaugeField 0) (b : Lattice4 × Fin 4) :
    ‖((latticeField S z T b.1 b.2 * (latticeField S z W b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      ‖((T (siteBond S z b).1 (siteBond S z b).2 * (W (siteBond S z b).1 (siteBond S z b).2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  unfold latticeField siteBond
  rcases hsign b.2 with h | h
  · simp only [h, if_true]
  · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
    simp only [if_neg hne]
    set t := T (patchSite S z (b.1 + basisVector b.2)) b.2
    set w := W (patchSite S z (b.1 + basisVector b.2)) b.2
    have e : t⁻¹ * (w⁻¹)⁻¹ = w⁻¹ * (t * w⁻¹)⁻¹ * (w⁻¹)⁻¹ := by group
    rw [e, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
end Framing
end PatchLatticeChart
end YangMills.Construction
end
