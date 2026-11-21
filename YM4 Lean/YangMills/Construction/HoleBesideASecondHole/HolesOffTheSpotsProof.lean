import YangMills.Construction.HoleBesideASecondHole.ChainChangedAtTheBottom
import YangMills.Construction.HoleBesideASecondHole.ComponentsOfLumps
import YangMills.Construction.HoleBesideASecondHole.CurvatureAtAQuietCellProof
import YangMills.Construction.HoleBesideASecondHole.EachHoleIsFilled
import YangMills.Construction.HoleBesideASecondHole.HolesStandOffTheSpots
import YangMills.Construction.HoleBesideASecondHole.SitesUnderSites
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours Holes HoleSavings
namespace HoleFilling
namespace AwayFromBadCells
variable {F : BlockFrame}
theorem mem_cutBelow {i j : ℕ} {X : Finset (F.Site j)} {z : F.Site i} :
    z ∈ cutBelow i X ↔ ∃ x ∈ X, z ∈ sitesBelow i x := by
  unfold cutBelow
  exact Finset.mem_biUnion
theorem mem_cutPlaquettes {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4} :
    p ∈ cutPlaquettes X ↔ p.1 ∈ X ∧ p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X := by
  classical
  simp [cutPlaquettes]
theorem mem_cutBonds {j : ℕ} {X : Finset (F.Site j)} {c : F.Site j × Fin 4} :
    c ∈ cutBonds X ↔ c.1 ∈ X ∧ c.1 + unitStep j c.2 ∈ X := by
  classical
  simp [cutBonds]
theorem cutBelow_mono {i j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) : cutBelow i X ⊆ cutBelow i Y := by apply _root_.YangMills.Construction.HoleSavings.QuietCell.cutBelow_subset_cutBelow <;> assumption
theorem cutPlaquettes_mono {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) :
    cutPlaquettes X ⊆ cutPlaquettes Y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutPlaquettes_mono <;> assumption
theorem cutBonds_mono {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) : cutBonds X ⊆ cutBonds Y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutBonds_mono <;> assumption
theorem sum_biUnion_le_sum_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι)
    (t : ι → Finset κ) (f : κ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    calc _ ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
          linarith
      _ ≤ _ := by linarith
theorem sum_sum_le_of_bounded_multiplicity {ι κ φ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq φ]
    (P : Finset ι) (Q : Finset κ) (Qp : ι → Finset κ)
    (w : κ → ℝ) (hw : ∀ q, 0 ≤ w q) (R : κ → φ → Prop) (c : ι → Finset φ)
    (hR : ∀ q f f', R q f → R q f' → f = f')
    (hsub : ∀ p ∈ P, ∀ q ∈ Qp p, q ∈ Q ∧ ∃ f ∈ c p, R q f)
    (hcnt : ∀ f, (P.filter fun p => f ∈ c p).card ≤ 64) :
    ∑ p ∈ P, ∑ q ∈ Qp p, w q ≤ 64 * ∑ q ∈ Q, w q := by
  classical
  have e1 : ∑ p ∈ P, ∑ q ∈ Qp p, w q = ∑ p ∈ P, ∑ q ∈ Q, if q ∈ Qp p then w q else 0 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨(hsub p hp q h).1, h⟩, fun h => h.2⟩
  rw [e1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hw q)
  by_cases hne : ∃ p ∈ P, q ∈ Qp p
  · obtain ⟨p₀, hp₀, hq₀⟩ := hne
    obtain ⟨_, f, _, hf⟩ := hsub p₀ hp₀ q hq₀
    have : (P.filter fun p => q ∈ Qp p).card ≤ (P.filter fun p => f ∈ c p).card := by
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      obtain ⟨_, f', hf', hR'⟩ := hsub p h1 q h2
      rw [hR q f f' hf hR']
      exact Finset.mem_filter.2 ⟨h1, hf'⟩
    have h3 := hcnt f
    have : ((P.filter fun p => q ∈ Qp p).card : ℝ) ≤ 64 := by exact_mod_cast this.trans h3
    exact this
  · push_neg at hne
    have : (P.filter fun p => q ∈ Qp p) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun p hp => hne p hp
    rw [this]
    norm_num
theorem card_filter_mem_plaquetteCorners_le {j : ℕ} (f : F.Site j) (P : Finset (F.Site j × Fin 4 × Fin 4)) :
    (P.filter fun p => f ∈ plaquetteCorners p).card ≤ 64 := by
  classical
  have hsub : (P.filter fun p => f ∈ plaquetteCorners p) ⊆
      (Finset.univ : Finset (Fin 4 × Fin 4 × Bool × Bool)).image fun m =>
        (f - (if m.2.2.1 then unitStep j m.1 else 0) - (if m.2.2.2 then unitStep j m.2.1 else 0), m.1, m.2.1) := by
    rintro ⟨x, μ, ν⟩ hp
    have h1 := (Finset.mem_filter.1 hp).2
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at h1
    refine Finset.mem_image.2 ?_
    rcases h1 with rfl | rfl | rfl | rfl
    · exact ⟨(μ, ν, false, false), Finset.mem_univ _, by simp⟩
    · exact ⟨(μ, ν, true, false), Finset.mem_univ _, by simp⟩
    · exact ⟨(μ, ν, false, true), Finset.mem_univ _, by simp⟩
    · exact ⟨(μ, ν, true, true), Finset.mem_univ _, by simp; abel⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp
section Totals
variable (henergy : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p)
  (hterm : ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re)
include hterm in
theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ blockFit X X' c :=
  hterm _ _
include henergy hterm in
theorem cutChainEnergy_mono {a : ℝ} (ha : 0 ≤ a) {t : ℕ} {X Y : Finset (F.Site t)} (h : X ⊆ Y)
    (U : F.FieldChain) :
    cutChainEnergy a t X U ≤ cutChainEnergy a t Y U := by
  unfold cutChainEnergy
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (cutPlaquettes_mono (cutBelow_mono h))
    fun p _ _ => henergy _ _) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) ha
  exact Finset.sum_le_sum_of_subset_of_nonneg (cutBonds_mono (cutBelow_mono h))
    fun c _ _ => blockFit_nonneg hterm _ _ _
include henergy hterm in
theorem sum_cutChainEnergy_plaquetteCorners_le {a : ℝ} (ha : 0 ≤ a) {t : ℕ} (ht : t ≤ F.top)
    (huniq : ∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
      z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x')
    (Y : Finset (F.Site t)) (U : F.FieldChain) :
    ∑ p ∈ cutPlaquettes Y, cutChainEnergy a t (plaquetteCorners p) U ≤ 64 * cutChainEnergy a t Y U := by
  classical
  unfold cutChainEnergy
  have e2 : ∑ p ∈ cutPlaquettes Y, a * ∑ i ∈ Finset.range t,
      ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
      blockFit (U i) (U (i + 1)) c = a * ∑ i ∈ Finset.range t, ∑ p ∈ cutPlaquettes Y,
        ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)), blockFit (U i) (U (i + 1)) c := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_add_distrib, e2, mul_add]
  refine add_le_add ?_ ?_
  · refine sum_sum_le_of_bounded_multiplicity (cutPlaquettes Y) (cutPlaquettes (cutBelow 0 Y))
      (fun p => cutPlaquettes (cutBelow 0 (plaquetteCorners p))) (plaquetteEnergy (U 0)) (henergy _)
      (fun q f => q.1 ∈ sitesBelow 0 f) plaquetteCorners
      (fun q f f' h1 h2 => huniq 0 t (Nat.zero_le _) ht f f' _ h1 h2) ?_
      (fun f => card_filter_mem_plaquetteCorners_le f _)
    intro p hp q hq
    refine ⟨cutPlaquettes_mono (cutBelow_mono (mem_cutPlaquettes.1 hp).2.2) hq, ?_⟩
    obtain ⟨f, hf, hz⟩ := mem_cutBelow.1 (mem_cutPlaquettes.1 hq).1
    exact ⟨f, hf, hz⟩
  · rw [mul_left_comm (64 : ℝ) a]
    refine mul_le_mul_of_nonneg_left ?_ ha
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i + 1 ≤ t := Finset.mem_range.1 hi
    refine sum_sum_le_of_bounded_multiplicity (cutPlaquettes Y) (cutBonds (cutBelow (i + 1) Y))
      (fun p => cutBonds (cutBelow (i + 1) (plaquetteCorners p))) (blockFit (U i) (U (i + 1)))
      (blockFit_nonneg hterm _ _)
      (fun q f => q.1 ∈ sitesBelow (i + 1) f) plaquetteCorners
      (fun q f f' h1 h2 => huniq (i + 1) t hi' ht f f' _ h1 h2) ?_
      (fun f => card_filter_mem_plaquetteCorners_le f _)
    intro p hp q hq
    refine ⟨cutBonds_mono (cutBelow_mono (mem_cutPlaquettes.1 hp).2.2) hq, ?_⟩
    obtain ⟨f, hf, hz⟩ := mem_cutBelow.1 (mem_cutBonds.1 hq).1
    exact ⟨f, hf, hz⟩
end Totals
section Data
variable {a s θ : ℝ} {J₀ : ℕ} {g : LumpGrid F.blockSide} {D : HoleData F g a s θ J₀} {C CS : ℝ}
  {idx : Finset (Finset (F.Site F.depth)) → ℕ} {o : Finset (Finset (F.Site F.depth)) → F.Site F.depth}
  {U' : F.GaugeField 0} {P : Hole F → Finset (F.Site 0 × Fin 4 × Fin 4)}
structure FillingData (D : HoleData F g a s θ J₀) (C CS : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) (U' : F.GaugeField 0)
    (P : Hole F → Finset (F.Site 0 × Fin 4 × Fin 4)) : Prop where
  isHoleFamily : D.IsHoleFamily C idx o
  corners_subset_outer : ∀ H ∈ D.holesAt C idx o, ∀ p ∈ P H, plaquetteCorners p ⊆ cutBelow 0 H.outerBox
  mem_of_meets_inner : ∀ H ∈ D.holesAt C idx o, ∀ p : F.Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 →
    (∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 H.innerBox) → p ∈ P H
  energy_eq_off_holes : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 → (∀ H ∈ D.holesAt C idx o, p ∉ P H) →
    plaquetteEnergy U' p = plaquetteEnergy (D.chain 0) p
  energy_le_annulus : ∀ H ∈ D.holesAt C idx o,
    ∑ p ∈ P H, plaquetteEnergy U' p ≤ CS * H.annulusEnergy (D.chain 0)
  link_eq_off_outer : ∀ (b : F.Site 0 × Fin 4), (∀ H ∈ D.holesAt C idx o,
    ¬ (b.1 ∈ cutBelow 0 H.outerBox ∧ b.1 + unitStep 0 b.2 ∈ cutBelow 0 H.outerBox)) →
    U' b.1 b.2 = D.chain 0 b.1 b.2
  sitesBelow_unique : ∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
    z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x'
  energy_nonneg : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p
  fit_term_nonneg : ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re
  neighbourhood_subset_collar : ∀ (l : Finset (F.Site F.depth)), lumpNeighbourhood l ⊆ lumpCollar l
  inner_subset_outer : ∀ H : Hole F, H.innerBox ⊆ H.outerBox
  const_nonneg : 0 ≤ CS
theorem exists_hole_of_mem_neighbourhood (X : FillingData D C CS idx o U' P) {f : F.Site F.depth}
    (hf : f ∈ cutBelow F.depth (D.coreCells C 4))
    (hn : f ∈ lumpsNeighbourhood D.hotFineLumps) : ∃ H ∈ D.holesAt C idx o, f ∈ H.innerBox := by
  classical
  obtain ⟨l, hl, hfl⟩ := Finset.mem_biUnion.1 hn
  obtain ⟨y, hy, hfy⟩ := mem_cutBelow.1 hf
  obtain ⟨H, hH, hlH⟩ := X.isHoleFamily.exists_hole_of_meets l hl y hy ⟨f, Finset.mem_inter.2 ⟨hfl, hfy⟩⟩
  exact ⟨H, hH, X.isHoleFamily.collar_subset H hH l hlH (X.neighbourhood_subset_collar l hfl)⟩
open Classical in
theorem sum_plaquetteEnergy_filled_le (X : FillingData D C CS idx o U' P) {Y : Finset (F.Site F.depth)}
    (hY : Y ⊆ cutBelow F.depth (D.coreCells C 4)) :
    ∑ p ∈ cutPlaquettes (cutBelow 0 Y), plaquetteEnergy U' p ≤
      ∑ p ∈ cutPlaquettes (cutBelow 0 (Y \ lumpsNeighbourhood D.hotFineLumps)), plaquetteEnergy (D.chain 0) p +
        ∑ H ∈ (D.holesAt C idx o).filter (fun H => (H.outerBox ∩ Y).Nonempty),
          CS * H.annulusEnergy (D.chain 0) := by
  have hn : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p := X.energy_nonneg
  rw [← Finset.sum_filter_add_sum_filter_not (cutPlaquettes (cutBelow 0 Y))
    (fun p => ∃ H ∈ D.holesAt C idx o, p ∈ P H), add_comm]
  refine add_le_add ?_ ?_
  · calc _ = ∑ p ∈ (cutPlaquettes (cutBelow 0 Y)).filter (fun p => ¬ ∃ H ∈ D.holesAt C idx o, p ∈ P H),
          plaquetteEnergy (D.chain 0) p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
          exact X.energy_eq_off_holes p (mem_cutPlaquettes.1 h1).2.1 fun H hH hpH => h2 ⟨H, hH, hpH⟩
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => hn _ p
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
          obtain ⟨a1, a2, a3⟩ := mem_cutPlaquettes.1 h1
          have key : ∀ x ∈ plaquetteCorners p, x ∈ cutBelow 0 (Y \ lumpsNeighbourhood D.hotFineLumps) := by
            intro x hx
            obtain ⟨f, hf, hxf⟩ := mem_cutBelow.1 (a3 hx)
            refine mem_cutBelow.2 ⟨f, Finset.mem_sdiff.2 ⟨hf, fun hnf => ?_⟩, hxf⟩
            obtain ⟨H, hH, hin⟩ := exists_hole_of_mem_neighbourhood X (hY hf) hnf
            exact h2 ⟨H, hH, X.mem_of_meets_inner H hH p a2 ⟨x, hx, mem_cutBelow.2 ⟨f, hin, hxf⟩⟩⟩
          exact mem_cutPlaquettes.2 ⟨key _ (show p.1 ∈ plaquetteCorners p by simp [plaquetteCorners]), a2, key⟩
  · calc _ ≤ ∑ p ∈ ((D.holesAt C idx o).filter (fun H => (H.outerBox ∩ Y).Nonempty)).biUnion P,
          plaquetteEnergy U' p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => hn _ p
          obtain ⟨h1, H, hH, hpH⟩ := Finset.mem_filter.1 hp
          refine Finset.mem_biUnion.2 ⟨H, Finset.mem_filter.2 ⟨hH, ?_⟩, hpH⟩
          obtain ⟨a1, a2, a3⟩ := mem_cutPlaquettes.1 h1
          obtain ⟨f, hf, hxf⟩ := mem_cutBelow.1 a1
          obtain ⟨f', hf', hxf'⟩ := mem_cutBelow.1
            (X.corners_subset_outer H hH p hpH (show p.1 ∈ plaquetteCorners p by simp [plaquetteCorners]))
          have e := X.sitesBelow_unique 0 F.depth (Nat.zero_le _) (by simp [BlockFrame.top]) f f' _ hxf hxf'
          subst e
          exact ⟨f, Finset.mem_inter.2 ⟨hf', hf⟩⟩
      _ ≤ ∑ H ∈ (D.holesAt C idx o).filter (fun H => (H.outerBox ∩ Y).Nonempty),
          ∑ p ∈ P H, plaquetteEnergy U' p :=
          sum_biUnion_le_sum_sum _ _ _ (hn U')
      _ ≤ _ := by
          refine Finset.sum_le_sum fun H hH => X.energy_le_annulus H (Finset.mem_filter.1 hH).1
open Classical in
theorem sum_blockFit_kept_le (X : FillingData D C CS idx o U' P) {Y : Finset (F.Site F.depth)}
    (hY : Y ⊆ cutBelow F.depth (D.coreCells C 4))
    {G : Finset (F.Site F.depth)}
    (hG : G = cutBelow F.depth (D.coreCells C 4) \ holeSupport (D.holesAt C idx o))
    {i : ℕ} (hi : i + 1 ≤ F.depth) (f : F.Site (i + 1) × Fin 4 → ℝ) (hf : ∀ c, 0 ≤ f c) :
    ∑ c ∈ cutBonds (cutBelow (i + 1) Y), (if c ∈ cutBonds (cutBelow (i + 1) G) then f c else 0) ≤
      ∑ c ∈ cutBonds (cutBelow (i + 1) (Y \ lumpsNeighbourhood D.hotFineLumps)), f c := by
  rw [Finset.sum_ite_mem]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) fun c _ _ => hf c
  obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hc
  have key : ∀ z : F.Site (i + 1), z ∈ cutBelow (i + 1) Y → z ∈ cutBelow (i + 1) G →
      z ∈ cutBelow (i + 1) (Y \ lumpsNeighbourhood D.hotFineLumps) := by
    intro z hz hz'
    obtain ⟨x, hx, hzx⟩ := mem_cutBelow.1 hz
    obtain ⟨x', hx', hzx'⟩ := mem_cutBelow.1 hz'
    have e := X.sitesBelow_unique (i + 1) F.depth hi (by simp [BlockFrame.top]) x x' _ hzx hzx'
    subst e
    refine mem_cutBelow.2 ⟨x, Finset.mem_sdiff.2 ⟨hx, fun hn => ?_⟩, hzx⟩
    obtain ⟨H, hH, hin⟩ := exists_hole_of_mem_neighbourhood X (hY hx) hn
    rw [hG] at hx'
    refine (Finset.mem_sdiff.1 hx').2 ?_
    exact Finset.mem_biUnion.2 ⟨H, hH, X.inner_subset_outer H hin⟩
  exact mem_cutBonds.2 ⟨key _ (mem_cutBonds.1 h1).1 (mem_cutBonds.1 h2).1,
    key _ (mem_cutBonds.1 h1).2 (mem_cutBonds.1 h2).2⟩
open Classical in
theorem sum_annulusEnergy_meeting_le (X : FillingData D C CS idx o U' P)
    (hpos : 0 < (topScaleIndex J₀ F.blockSide : ℝ) - J₀) {Y : Finset (F.Site F.depth)}
    (hen : ∀ k ∈ D.componentsAtCore C,
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0)) *
      ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2) :
    ∑ H ∈ (D.holesAt C idx o).filter (fun H => (H.outerBox ∩ Y).Nonempty), H.annulusEnergy (D.chain 0) ≤
      C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
        ((D.componentsAtCore C).filter fun k =>
          ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty).card := by
  have hE : ∀ H : Hole F, 0 ≤ H.annulusEnergy (D.chain 0) :=
    fun H => Finset.sum_nonneg fun p _ => X.energy_nonneg _ p
  calc _ ≤ ∑ H ∈ ((D.componentsAtCore C).filter fun k =>
        ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty).biUnion
        (fun k => componentHoles J₀ D.hotFineLumps k (idx k) o), H.annulusEnergy (D.chain 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun H hH => ?_) fun H _ _ => hE H
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hH
        unfold HoleData.holesAt allHoles at h1
        obtain ⟨k, hk, hHk⟩ := Finset.mem_biUnion.1 h1
        exact Finset.mem_biUnion.2 ⟨k, Finset.mem_filter.2 ⟨hk, H, hHk, h2⟩, hHk⟩
    _ ≤ ∑ k ∈ (D.componentsAtCore C).filter (fun k =>
          ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty),
        ∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0) :=
        sum_biUnion_le_sum_sum _ _ _ hE
    _ ≤ ∑ k ∈ (D.componentsAtCore C).filter (fun k =>
          ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty),
        C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [le_div_iff₀ hpos]
        exact hen k (Finset.mem_filter.1 hk).1
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
open Classical in
theorem cutChainEnergy_modified_le (X : FillingData D C CS idx o U' P)
    (hpos : 0 < (topScaleIndex J₀ F.blockSide : ℝ) - J₀) (ha : 0 ≤ a)
    (hen : ∀ k ∈ D.componentsAtCore C,
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0)) *
      ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2)
    {G : Finset (F.Site F.depth)}
    (hG : G = cutBelow F.depth (D.coreCells C 4) \ holeSupport (D.holesAt C idx o))
    (hfit : ∀ i < F.depth, ∀ c : F.Site (i + 1) × Fin 4,
      blockFit (bottomModifiedField G D.chain U' i) (bottomModifiedField G D.chain U' (i + 1)) c =
        if c ∈ cutBonds (cutBelow (i + 1) G) then blockFit (D.chain i) (D.chain (i + 1)) c else 0)
    {Y : Finset (F.Site F.depth)} (hY : Y ⊆ cutBelow F.depth (D.coreCells C 4)) :
    cutChainEnergy a F.depth Y (bottomModifiedField G D.chain U') ≤
      cutChainEnergy a F.depth (Y \ lumpsNeighbourhood D.hotFineLumps) D.chain +
      CS * (C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
        ((D.componentsAtCore C).filter fun k =>
          ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty).card) := by
  have h1 := sum_plaquetteEnergy_filled_le X hY
  have h2 := sum_annulusEnergy_meeting_le X hpos (Y := Y) hen
  have h3 := mul_le_mul_of_nonneg_left h2 X.const_nonneg
  rw [Finset.mul_sum] at h3
  have h4 : a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Y),
      blockFit (bottomModifiedField G D.chain U' i) (bottomModifiedField G D.chain U' (i + 1)) c ≤
      a * ∑ i ∈ Finset.range F.depth,
        ∑ c ∈ cutBonds (cutBelow (i + 1) (Y \ lumpsNeighbourhood D.hotFineLumps)),
          blockFit (D.chain i) (D.chain (i + 1)) c := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) ha
    have hi' := Finset.mem_range.1 hi
    calc _ = ∑ c ∈ cutBonds (cutBelow (i + 1) Y), (if c ∈ cutBonds (cutBelow (i + 1) G)
          then blockFit (D.chain i) (D.chain (i + 1)) c else 0) :=
          Finset.sum_congr rfl fun c _ => hfit i hi' c
      _ ≤ _ := sum_blockFit_kept_le X hY hG hi' _ fun c => X.fit_term_nonneg _ _
  unfold cutChainEnergy
  have e0 : bottomModifiedField G D.chain U' 0 = U' := rfl
  rw [e0]
  linarith
theorem cutChainEnergy_off_neighbourhood_le (X : FillingData D C CS idx o U' P) (ha : 0 ≤ a)
    (htrans : ∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x)
    {B B₃ : Finset F.Cell} (hBS : B ⊆ D.cells) (hB : B ⊆ B₃) :
    cutChainEnergy a F.depth (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps) D.chain ≤
      D.energyOver B₃ := by
  classical
  have hsub : cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps ⊆ D.chainSites :=
    Finset.sdiff_subset_sdiff (cutBelow_mono hBS) (Finset.Subset.refl _)
  have lift : ∀ (i : ℕ) (hi : i ≤ F.depth) (z : F.Site i),
      z ∈ cutBelow i (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps) →
      z ∈ cutBelow i B₃ := by
    intro i hi z hz
    obtain ⟨f, hf, hzf⟩ := mem_cutBelow.1 hz
    obtain ⟨c, hc, hfc⟩ := mem_cutBelow.1 (Finset.mem_sdiff.1 hf).1
    exact mem_cutBelow.2 ⟨c, hB hc, htrans i F.depth F.top hi (by simp [BlockFrame.top]) le_rfl c f z hfc hzf⟩
  unfold cutChainEnergy HoleData.energyOver
  have s3 : 0 ≤ a * ∑ c ∈ cutBonds D.cells,
      (if c.1 ∈ B₃ ∨ c.1 + unitStep F.top c.2 ∈ B₃ then D.topBondFit c else 0) := by
    refine mul_nonneg ha (Finset.sum_nonneg fun c _ => ?_)
    split_ifs
    · exact X.fit_term_nonneg _ _
    · exact le_rfl
  have s1 : ∑ p ∈ cutPlaquettes (cutBelow 0 (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps)),
      plaquetteEnergy (D.chain 0) p ≤
      ∑ p ∈ cutPlaquettes (cutBelow 0 D.chainSites),
        (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ then plaquetteEnergy (D.chain 0) p else 0) := by
    calc _ = ∑ p ∈ cutPlaquettes (cutBelow 0 (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps)),
          (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ then plaquetteEnergy (D.chain 0) p else 0) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          refine (if_pos ⟨p.1, by simp [plaquetteCorners],
            lift 0 (Nat.zero_le _) _ (mem_cutPlaquettes.1 hp).1⟩).symm
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (cutPlaquettes_mono (cutBelow_mono hsub))
            fun p _ _ => ?_
          split_ifs
          · exact X.energy_nonneg _ _
          · exact le_rfl
  have s2 : a * ∑ i ∈ Finset.range F.depth,
      ∑ c ∈ cutBonds (cutBelow (i + 1) (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps)),
      blockFit (D.chain i) (D.chain (i + 1)) c ≤
      a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) D.chainSites),
      (if c.1 ∈ cutBelow (i + 1) B₃ ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B₃
        then blockFit (D.chain i) (D.chain (i + 1)) c else 0) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) ha
    have hi' := Finset.mem_range.1 hi
    calc _ = ∑ c ∈ cutBonds (cutBelow (i + 1) (cutBelow F.depth B \ lumpsNeighbourhood D.hotFineLumps)),
          (if c.1 ∈ cutBelow (i + 1) B₃ ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B₃
            then blockFit (D.chain i) (D.chain (i + 1)) c else 0) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          exact (if_pos (Or.inl (lift (i + 1) hi' _ (mem_cutBonds.1 hc).1))).symm
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (cutBonds_mono (cutBelow_mono hsub)) fun c _ _ => ?_
          split_ifs
          · exact X.fit_term_nonneg _ _
          · exact le_rfl
  linarith
theorem sum_plaquetteDefect_sq_le_of_energy {cK : ℝ} (hcK : 0 < cK) {Λ : ℝ}
    (X : FillingData D C CS idx o U' P) (ha : 0 ≤ a)
    (hco : ∀ (p : F.Site F.depth × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
      cK * min (plaquetteDefect (U F.depth) p ^ 2) Λ ≤ cutChainEnergy a F.depth (plaquetteCorners p) U)
    {U2 : F.FieldChain} {Y : Finset (F.Site F.depth)} {Eb : ℝ}
    (hE : cutChainEnergy a F.depth Y U2 ≤ Eb) (hEb : Eb < cK * Λ) :
    ∑ p ∈ cutPlaquettes Y, plaquetteDefect (U2 F.depth) p ^ 2 ≤ 64 / cK * Eb := by
  have hsum := sum_cutChainEnergy_plaquetteCorners_le X.energy_nonneg X.fit_term_nonneg ha
    (t := F.depth) (by simp [BlockFrame.top]) X.sitesBelow_unique Y U2
  have hpt : ∀ p ∈ cutPlaquettes Y,
      plaquetteDefect (U2 F.depth) p ^ 2 ≤ cutChainEnergy a F.depth (plaquetteCorners p) U2 / cK := by
    intro p hp
    obtain ⟨_, h2, h3⟩ := mem_cutPlaquettes.1 hp
    have h4 := hco p U2 h2
    have h5 := cutChainEnergy_mono X.energy_nonneg X.fit_term_nonneg ha h3 U2
    rw [le_div_iff₀ hcK]
    rcases min_choice (plaquetteDefect (U2 F.depth) p ^ 2) Λ with e | e
    · rw [e] at h4
      linarith
    · rw [e] at h4
      linarith
  calc _ ≤ ∑ p ∈ cutPlaquettes Y, cutChainEnergy a F.depth (plaquetteCorners p) U2 / cK :=
        Finset.sum_le_sum hpt
    _ = (∑ p ∈ cutPlaquettes Y, cutChainEnergy a F.depth (plaquetteCorners p) U2) / cK := by
        rw [Finset.sum_div]
    _ ≤ (64 * Eb) / cK := by
        refine div_le_div_of_nonneg_right ?_ hcK.le
        linarith
    _ = _ := by ring
open Classical in
theorem card_components_meeting_lt (X : FillingData D C CS idx o U' P)
    (hself : ∀ (r : ℕ) (l : Finset (F.Site F.depth)), l ∈ D.hotFineLumps →
      l ∈ linkComponent r D.hotFineLumps l)
    (heq : ∀ (r : ℕ) (l l' : Finset (F.Site F.depth)), l' ∈ linkComponent r D.hotFineLumps l →
      linkComponent r D.hotFineLumps l' = linkComponent r D.hotFineLumps l)
    {Bb : Finset F.Cell} {Y : Finset (F.Site F.depth)} (hY : Y ⊆ cutBelow F.depth Bb)
    (hfew : ((D.holesAt C idx o).filter fun H => (H.outerBox ∩ cutBelow F.depth Bb).Nonempty).card < J₀) :
    ((D.componentsAtCore C).filter fun k =>
      ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty).card < J₀ := by
  have hch : ∀ k : Finset (Finset (F.Site F.depth)), ∃ H : Hole F,
      (∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty) →
        H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o ∧ (H.outerBox ∩ Y).Nonempty := by
    intro k
    by_cases h : ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty
    · obtain ⟨H, h1, h2⟩ := h
      exact ⟨H, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨⟨∅, 0, 0⟩, fun h' => absurd h' h⟩
  choose φ hφ using hch
  have hlump : ∀ {k : Finset (Finset (F.Site F.depth))} {i : ℕ} {H : Hole F},
      H ∈ componentHoles J₀ D.hotFineLumps k i o →
      ∃ l ∈ H.lumps, l ∈ k ∧ l ∈ D.hotFineLumps := by
    intro k i H hH
    unfold componentHoles at hH
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hH
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hk'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h1
    exact ⟨l, hself _ _ hl, h2 (hself _ _ hl), hl⟩
  have hsubk : ∀ {k : Finset (Finset (F.Site F.depth))} {i : ℕ} {H : Hole F},
      H ∈ componentHoles J₀ D.hotFineLumps k i o → H.lumps ⊆ k := by
    intro k i H hH
    unfold componentHoles at hH
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hH
    exact (Finset.mem_filter.1 hk').2
  refine lt_of_le_of_lt (Finset.card_le_card_of_injOn φ ?_ ?_) hfew
  · intro k hk
    have hk' : k ∈ (D.componentsAtCore C).filter fun k =>
        ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty := hk
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hk'
    obtain ⟨a1, x, hx⟩ := hφ k h2
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, x, ?_⟩)
    · unfold HoleData.holesAt allHoles
      exact Finset.mem_biUnion.2 ⟨k, h1, a1⟩
    · obtain ⟨b1, b2⟩ := Finset.mem_inter.1 hx
      exact Finset.mem_inter.2 ⟨b1, hY b2⟩
  · intro k hk k' hk' e
    have hk1 : k ∈ (D.componentsAtCore C).filter fun k =>
        ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty := hk
    have hk2 : k' ∈ (D.componentsAtCore C).filter fun k =>
        ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty := hk'
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hk1
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hk2
    have a1 := (hφ k h2).1
    have a2 := (hφ k' h4).1
    rw [← e] at a2
    obtain ⟨l, hl, hlk, hlh⟩ := hlump a1
    have hlk' := hsubk a2 hl
    have c1 := (Finset.mem_filter.1 h1).1
    have c2 := (Finset.mem_filter.1 h3).1
    obtain ⟨l₁, _, e₁⟩ := Finset.mem_image.1 c1
    obtain ⟨l₂, _, e₂⟩ := Finset.mem_image.1 c2
    subst e₁ e₂
    rw [← heq _ _ _ hlk, ← heq _ _ _ hlk']
open Classical in
theorem sum_plaquetteDefect_sq_modified_le {cK Λ : ℝ} (hcK : 0 < cK) (X : FillingData D C CS idx o U' P)
    (hpos : 0 < (topScaleIndex J₀ F.blockSide : ℝ) - J₀)
    (hJI : (J₀ : ℝ) ≤ (topScaleIndex J₀ F.blockSide : ℝ) - J₀) (ha : 0 ≤ a) (hCs : 0 ≤ C * s ^ 2)
    (hen : ∀ k ∈ D.componentsAtCore C,
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0)) *
      ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2)
    {G : Finset (F.Site F.depth)}
    (hG : G = cutBelow F.depth (D.coreCells C 4) \ holeSupport (D.holesAt C idx o))
    (hfit : ∀ i < F.depth, ∀ c : F.Site (i + 1) × Fin 4,
      blockFit (bottomModifiedField G D.chain U' i) (bottomModifiedField G D.chain U' (i + 1)) c =
        if c ∈ cutBonds (cutBelow (i + 1) G) then blockFit (D.chain i) (D.chain (i + 1)) c else 0)
    (htrans : ∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x)
    (hself : ∀ (r : ℕ) (l : Finset (F.Site F.depth)), l ∈ D.hotFineLumps →
      l ∈ linkComponent r D.hotFineLumps l)
    (heq : ∀ (r : ℕ) (l l' : Finset (F.Site F.depth)), l' ∈ linkComponent r D.hotFineLumps l →
      linkComponent r D.hotFineLumps l' = linkComponent r D.hotFineLumps l)
    (hco : ∀ (p : F.Site F.depth × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
      cK * min (plaquetteDefect (U F.depth) p ^ 2) Λ ≤ cutChainEnergy a F.depth (plaquetteCorners p) U)
    {B Bb B₃ : Finset F.Cell} (hB4 : B ⊆ D.coreCells C 4) (hBS : B ⊆ D.cells) (hBb : B ⊆ Bb) (hB3 : B ⊆ B₃)
    (hfew : ((D.holesAt C idx o).filter fun H => (H.outerBox ∩ cutBelow F.depth Bb).Nonempty).card < J₀)
    (hexc : D.energyOver B₃ < C * s ^ 2) (hsmall : (1 + CS) * (C * s ^ 2) < cK * Λ) :
    ∑ p ∈ cutPlaquettes (cutBelow F.depth B), plaquetteDefect (bottomModifiedField G D.chain U' F.depth) p ^ 2 ≤
      64 / cK * ((1 + CS) * (C * s ^ 2)) := by
  have h1 := cutChainEnergy_modified_le X hpos ha hen hG hfit
    (cutBelow_mono hB4 : cutBelow F.depth B ⊆ cutBelow F.depth (D.coreCells C 4))
  have h2 := cutChainEnergy_off_neighbourhood_le X ha htrans hBS hB3
  have h3 := card_components_meeting_lt X hself heq
    (cutBelow_mono hBb : cutBelow F.depth B ⊆ cutBelow F.depth Bb) hfew
  have h4 : (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
      (H.outerBox ∩ cutBelow F.depth B).Nonempty).card : ℝ) ≤ (topScaleIndex J₀ F.blockSide : ℝ) - J₀ := by
    have : (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
      (H.outerBox ∩ cutBelow F.depth B).Nonempty).card : ℝ) ≤ J₀ := by exact_mod_cast h3.le
    linarith
  have h5 : C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
      (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
        (H.outerBox ∩ cutBelow F.depth B).Nonempty).card : ℝ) ≤ C * s ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left h4 hCs
  have h6 := mul_le_mul_of_nonneg_left h5 X.const_nonneg
  have hE : cutChainEnergy a F.depth (cutBelow F.depth B) (bottomModifiedField G D.chain U') ≤
      (1 + CS) * (C * s ^ 2) := by
    nlinarith
  exact sum_plaquetteDefect_sq_le_of_energy hcK X ha hco hE hsmall
end Data
end AwayFromBadCells
theorem holesAwayFromBadCells (hS : holeFamilyExistsStatement) (hEach : eachHoleFilledStatement)
    (hChain : BottomModifiedChainIdentity) (hCoer : ChainCoercivity)
    (hd : TorusDistanceBlockLumpFacts) (hsu : NestedSiteFacts) (hcp : LinkComponentProperties) :
    holesAwayFromBadCellsStatement := by
  open AwayFromBadCells in
  obtain ⟨cS, CS, hcS, hCS, hfill⟩ := hEach
  obtain ⟨cK, hcK, _, LK, hK⟩ := hCoer
  refine ⟨CS + 64 / cK * (1 + CS), by positivity, ?_⟩
  intro J₀ hJ
  refine ⟨?_, ?_⟩
  · intro m
    refine ⟨holeScale J₀ m ^ 2, fun L hL => ?_⟩
    have h1 : m < (40 * J₀) ^ m := Nat.lt_pow_self (by omega : 1 < 40 * J₀)
    have h2 : (40 * J₀) ^ m ≤ holeScale J₀ m := by
      unfold holeScale lumpRange
      nlinarith
    have h3 : holeScale J₀ m ≤ holeScale J₀ m ^ 2 := by
      have : 1 ≤ holeScale J₀ m := by omega
      nlinarith
    exact Nat.le_findGreatest (by omega) hL
  obtain ⟨LS, hLS⟩ := hS J₀ hJ
  refine ⟨max LS LK, fun L hLo hLL => ?_⟩
  obtain ⟨t1, ht⟩ := hLS L hLo ((le_max_left _ _).trans hLL)
  refine ⟨t1, fun g a C ha hC => ?_⟩
  have hLp : (0 : ℝ) < L := by exact_mod_cast hLo.pos
  have hΛ : (0 : ℝ) < (L : ℝ) ^ (-4 : ℤ) := zpow_pos hLp _
  have hτ : 0 < min (cS / (4 * C)) (cK * (L : ℝ) ^ (-4 : ℤ) / (2 * (1 + CS) * C)) := by
    refine lt_min (by positivity) (by positivity)
  refine ⟨Real.sqrt (min (cS / (4 * C)) (cK * (L : ℝ) ^ (-4 : ℤ) / (2 * (1 + CS) * C))), Real.sqrt_pos.2 hτ,
    fun s hs hss θ F D hFL hcub => ?_⟩
  have hs2 : s ^ 2 ≤ min (cS / (4 * C)) (cK * (L : ℝ) ^ (-4 : ℤ) / (2 * (1 + CS) * C)) := by
    have := pow_le_pow_left₀ hs.le hss 2
    rwa [Real.sq_sqrt hτ.le] at this
  have hs2a : 4 * C * s ^ 2 ≤ cS := by
    have h := (hs2.trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hs2b : (1 + CS) * (C * s ^ 2) < cK * (L : ℝ) ^ (-4 : ℤ) := by
    have h := (hs2.trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    have : 0 < cK * (L : ℝ) ^ (-4 : ℤ) := by positivity
    nlinarith
  subst hFL
  classical
  have hs64 : ∀ i, 64 ≤ F.extent i := fun i => by
    have a1 := hcub.1 i
    have a2 := hcub.2
    omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs64 i; omega
  obtain ⟨idx, o, S⟩ := ht g a C s θ F D (by linarith) rfl hs64
  obtain ⟨_, _, enl, _⟩ := hd F hLo.pos hs'
  obtain ⟨su1, hterm⟩ := hsu
  obtain ⟨htrans, huniq, henergy⟩ := su1 F hLo hs'
  obtain ⟨c1, c2, _, _, _⟩ := hcp F D.hotFineLumps
  have hJ2 : (2 * J₀ : ℝ) ≤ topScaleIndex J₀ F.blockSide := by exact_mod_cast t1
  have hJ1 : (1 : ℝ) ≤ J₀ := by exact_mod_cast hJ
  have hpos : 0 < (topScaleIndex J₀ F.blockSide : ℝ) - J₀ := by linarith
  have hE0 : ∀ H : Hole F, 0 ≤ H.annulusEnergy (D.chain 0) :=
    fun H => Finset.sum_nonneg fun p _ => henergy _ p
  have hCs : 0 ≤ C * s ^ 2 := by positivity
  have h4E : ∀ H ∈ D.holesAt C idx o, 4 * H.annulusEnergy (D.chain 0) ≤ cS := by
    intro H hH
    unfold HoleData.holesAt allHoles at hH
    obtain ⟨k, hk, hHk⟩ := Finset.mem_biUnion.1 hH
    have h1 := S.annulus_energy_le k hk
    have h2 : H.annulusEnergy (D.chain 0) ≤
        ∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0) :=
      Finset.single_le_sum (f := fun H : Hole F => H.annulusEnergy (D.chain 0)) (fun H _ => hE0 H) hHk
    have h3 : 0 ≤ ∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0) :=
      Finset.sum_nonneg fun H _ => hE0 H
    nlinarith
  obtain ⟨U', P, p1, p2, p3, p4, p5⟩ := hfill F hLo hs64 (D.holesAt C idx o) (D.chain 0)
    (fun H hH => ⟨(S.radius_bounds H hH).1, (S.radius_bounds H hH).2, h4E H hH⟩)
    (fun H hH H' hH' hne hw => by
      obtain ⟨x, hx, y, hy, d⟩ := hw
      refine S.pairwise_apart H hH H' hH' hne ⟨x, hx, y, hy, d.trans ?_⟩
      have := (S.radius_bounds H hH).1
      have := le_max_left H.radius H'.radius
      omega)
  have X : FillingData D C CS idx o U' P :=
    { isHoleFamily := S, corners_subset_outer := p1, mem_of_meets_inner := p2, energy_eq_off_holes := p3,
      energy_le_annulus := p4, link_eq_off_outer := p5, sitesBelow_unique := huniq,
      energy_nonneg := henergy, fit_term_nonneg := hterm
      neighbourhood_subset_collar := fun l x hx => by
        obtain ⟨v, hv, dv⟩ := (enl _ _ _ _).1 hx
        exact (enl _ _ _ _).2 ⟨v, hv, by unfold lumpRange at dv ⊢; omega⟩
      inner_subset_outer := fun H x hx => by
        obtain ⟨v, hv, dv⟩ := (enl _ _ _ _).1 hx
        exact (enl _ _ _ _).2 ⟨v, hv, by omega⟩
      const_nonneg := hCS.le }
  obtain ⟨G, hG⟩ : ∃ G, G = cutBelow F.depth (D.coreCells C 4) \ holeSupport (D.holesAt C idx o) := ⟨_, rfl⟩
  have hyp : ∀ b ∈ cutBonds (cutBelow 0 G), U' b.1 b.2 = D.chain 0 b.1 b.2 := by
    intro b hb
    refine p5 b fun H hH hin => ?_
    obtain ⟨f, hf, hzf⟩ := mem_cutBelow.1 (mem_cutBonds.1 hb).1
    obtain ⟨f', hf', hzf'⟩ := mem_cutBelow.1 hin.1
    have e := huniq 0 F.depth (Nat.zero_le _) (by simp [BlockFrame.top]) f f' _ hzf hzf'
    subst e
    rw [hG] at hf
    exact (Finset.mem_sdiff.1 hf).2 (Finset.mem_biUnion.2 ⟨H, hH, hf'⟩)
  obtain ⟨k1, k2, _⟩ := hChain F F.depth (by simp [BlockFrame.top]) hLo G D.chain U' hyp
  have hen := S.annulus_energy_le
  refine ⟨idx, o, bottomModifiedField G D.chain U', S, ?_, ?_, ?_⟩
  · intro b hb h1 h2
    have hself : ∀ x : F.Site F.depth, x ∈ sitesBelow F.depth x := fun x => by
      refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
      · simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
        intro i
        simp
      · funext k
        simp [siteOfCoords, siteCoords]
    have hbG : b ∈ cutBonds (cutBelow F.depth G) := by
      obtain ⟨a1, a2⟩ := mem_cutBonds.1 hb
      refine mem_cutBonds.2 ⟨mem_cutBelow.2 ⟨_, ?_, hself _⟩, mem_cutBelow.2 ⟨_, ?_, hself _⟩⟩
      · rw [hG]
        exact Finset.mem_sdiff.2 ⟨a1, h1⟩
      · rw [hG]
        exact Finset.mem_sdiff.2 ⟨a2, h2⟩
    rw [k1 F.depth le_rfl b hbG, D.chain_top]
  · intro Y hY
    have h1 := cutChainEnergy_modified_le X hpos (by linarith) hen hG k2 hY
    have hA : 0 ≤ C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
        (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
          (H.outerBox ∩ Y).Nonempty).card : ℝ) := by
      positivity
    have hC2 : 0 ≤ 64 / cK * (1 + CS) := by positivity
    have e : (CS + 64 / cK * (1 + CS)) * C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
        (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
          (H.outerBox ∩ Y).Nonempty).card : ℝ) =
        (CS + 64 / cK * (1 + CS)) * (C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) *
          (((D.componentsAtCore C).filter fun k => ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
            (H.outerBox ∩ Y).Nonempty).card : ℝ)) := by
      ring
    rw [e]
    nlinarith
  · intro y hy
    obtain ⟨hyS, hyz⟩ : y ∈ D.cells ∧ ∀ z ∈ D.badCells C, 5 ≤ cellSupDist y z := by
      simpa [HoleData.coreCells] using hy
    have hyy : cellSupDist y y = 0 := by simp [cellSupDist]
    have hnc : ¬ IsCrowded J₀ D.hotFineLumps y := fun hc => by
      have := hyz y (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hyS, hc⟩))
      omega
    have hexc : D.energyOver (cellBall y 3) < C * s ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have := hyz y (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hyS, hcon⟩))
      omega
    have h4S : D.coreCells C 4 ⊆ D.cells := Finset.filter_subset _ _
    have hb13 : cellBall y 1 ⊆ cellBall y 3 := by
      obtain ⟨_, _, _, _, _, _, _, hball, _⟩ := hd F hLo.pos hs'
      intro z hz
      have := (hball y 1 z).1 hz
      exact (hball y 3 z).2 (by omega)
    have hco : ∀ (p : F.Site F.depth × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
        cK * min (plaquetteDefect (U F.depth) p ^ 2) ((F.blockSide : ℝ) ^ (-4 : ℤ)) ≤
          cutChainEnergy a F.depth (plaquetteCorners p) U :=
      (hK a F.blockSide ha hLo ((le_max_right _ _).trans hLL) F rfl (Or.inr hs64) F.depth
        (by simp [BlockFrame.top])).1
    have hfin := sum_plaquetteDefect_sq_modified_le hcK X hpos (by linarith) (by linarith) hCs hen hG k2
      htrans c1 c2 hco
      (B := cellBall y 1 ∩ D.coreCells C 4) (Bb := cellBall y 1) (B₃ := cellBall y 3) Finset.inter_subset_right
      (Finset.inter_subset_right.trans h4S) Finset.inter_subset_left (Finset.inter_subset_left.trans hb13)
      (S.few_near_uncrowded y hnc) hexc hs2b
    have hC2 : 0 ≤ CS * (C * s ^ 2) := by positivity
    calc _ ≤ _ := hfin
      _ ≤ _ := by
        have e : (CS + 64 / cK * (1 + CS)) * C * s ^ 2 =
            64 / cK * ((1 + CS) * (C * s ^ 2)) + CS * (C * s ^ 2) := by
          ring
        rw [e]
        linarith
end HoleFilling
end YangMills.Construction
end
