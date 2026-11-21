import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayer
import YangMills.Construction.InfiniteLattice.ContinuousFunctionsOfFinitelyManyBondsAndPlaquetteEnergies
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.SurfaceBoundBetweenBoxAndTorus
import YangMills.Construction.InfiniteLattice.TermsLieInTheirBoxes
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.BoxTorusSurfaceBound
open NormalFamilies BoxTorusComparisonData
def intPoint (n : Fin 4 → ℤ) : LatticePoint 1 := ⟨fun μ => (n μ : ℝ), n, fun μ => by simp⟩
theorem cubeAnchors_eq_range (ϱ : ℕ+) (x : LatticePoint 1) :
    {z : LatticePoint 1 | x ∈ siteCube z ϱ} =
      range fun k : Fin 4 → Fin ((ϱ : ℕ) + 1) =>
        x - intPoint fun μ => ((k μ : ℕ) : ℤ) := by
  ext z
  constructor
  · rintro ⟨k, hk, hx⟩
    refine ⟨fun μ => ⟨k μ, Nat.lt_succ_of_le (hk μ)⟩, Subtype.ext (funext fun μ => ?_)⟩
    have h := hx μ
    simp [intPoint, h]
  · rintro ⟨k, rfl⟩
    refine ⟨fun μ => (k μ : ℕ), fun μ => Nat.le_of_lt_succ (k μ).2, fun μ => ?_⟩
    simp [intPoint]
theorem cubeAnchors_finite (ϱ : ℕ+) (x : LatticePoint 1) :
    {z : LatticePoint 1 | x ∈ siteCube z ϱ}.Finite := by
  rw [cubeAnchors_eq_range]
  exact finite_range _
theorem ncard_cubeAnchors (ϱ : ℕ+) (x : LatticePoint 1) :
    {z : LatticePoint 1 | x ∈ siteCube z ϱ}.ncard = ((ϱ : ℕ) + 1) ^ 4 := by
  have hinj : Function.Injective fun k : Fin 4 → Fin ((ϱ : ℕ) + 1) =>
      x - intPoint fun μ => ((k μ : ℕ) : ℤ) := by
    intro k k' h
    funext μ
    have h1 := congrFun (congrArg Subtype.val h) μ
    simp only [intPoint, AddSubgroupClass.coe_sub, Pi.sub_apply, sub_right_inj] at h1
    exact Fin.ext (by exact_mod_cast h1)
  rw [cubeAnchors_eq_range, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ]
  simp
theorem self_mem_siteCube (z : LatticePoint 1) (ϱ : ℕ+) : z ∈ siteCube z ϱ :=
  ⟨fun _ => 0, fun _ => Nat.zero_le _, fun μ => by simp⟩
theorem norm_sub_le_of_mem_siteCube {z x y : LatticePoint 1} {ϱ : ℕ+} (hx : x ∈ siteCube z ϱ)
    (hy : y ∈ siteCube z ϱ) : ‖(y : AmbientSpace) - (x : AmbientSpace)‖ ≤ ((ϱ : ℕ) : ℝ) := by
  obtain ⟨k, hk, hx⟩ := hx
  obtain ⟨l, hl, hy⟩ := hy
  refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr fun μ => ?_
  have h1 : (k μ : ℝ) ≤ ((ϱ : ℕ) : ℝ) := by exact_mod_cast hk μ
  have h2 : (l μ : ℝ) ≤ ((ϱ : ℕ) : ℝ) := by exact_mod_cast hl μ
  rw [Pi.sub_apply, hx μ, hy μ, Real.norm_eq_abs, abs_le]
  constructor <;> linarith
theorem faces_cornered_in {Z : Set (LatticePoint 1)} (hZ : Z.Finite) :
    {p : ElementaryPlaquette 1 | p.corner ∈ Z}.Finite ∧
      {p : ElementaryPlaquette 1 | p.corner ∈ Z}.ncard ≤ 6 * Z.ncard := by
  have hT : ((Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2 :
      Finset (Fin 4 × Fin 4)) : Set (Fin 4 × Fin 4)).ncard = 6 := by
    rw [ncard_coe_finset]
    decide
  set T : Set (Fin 4 × Fin 4) :=
    ((Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2 : Finset (Fin 4 × Fin 4)) :
      Set (Fin 4 × Fin 4)) with hTdef
  let f : ElementaryPlaquette 1 → LatticePoint 1 × Fin 4 × Fin 4 :=
    fun p => (p.corner, p.lowAxis, p.highAxis)
  have hf : Function.Injective f := by
    intro p p' h
    simp only [f, Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
  have hmaps : f '' {p : ElementaryPlaquette 1 | p.corner ∈ Z} ⊆ Z ×ˢ T := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨hp, ?_⟩
    simp only [hTdef, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
    exact p.lowAxis_lt_highAxis
  have hfin : (Z ×ˢ T).Finite := hZ.prod (toFinite T)
  refine ⟨Finite.of_finite_image (hfin.subset hmaps) hf.injOn, ?_⟩
  calc {p : ElementaryPlaquette 1 | p.corner ∈ Z}.ncard =
        (f '' {p : ElementaryPlaquette 1 | p.corner ∈ Z}).ncard :=
        (ncard_image_of_injective _ hf).symm
    _ ≤ (Z ×ˢ T).ncard := ncard_le_ncard hmaps hfin
    _ = 6 * Z.ncard := by rw [ncard_prod, hT, mul_comm]
theorem abs_finsum_sub_finsum_le {α : Type*} {S₁ S₂ S₀ : Set α} (h₁ : S₁.Finite)
    (h₂ : S₂.Finite) (h01 : S₀ ⊆ S₁) (h02 : S₀ ⊆ S₂) {f g : α → ℝ}
    (hfg : ∀ x ∈ S₀, f x = g x) {M : ℝ}
    (hf : ∀ x ∈ S₁ \ S₀, |f x| ≤ M) (hg : ∀ x ∈ S₂ \ S₀, |g x| ≤ M) :
    |∑ᶠ x ∈ S₁, f x - ∑ᶠ x ∈ S₂, g x| ≤
      M * (((S₁ \ S₀).ncard : ℝ) + ((S₂ \ S₀).ncard : ℝ)) := by
  have h0 : S₀.Finite := h₁.subset h01
  have hbound : ∀ {S : Set α} {u : α → ℝ}, S.Finite → (∀ x ∈ S, |u x| ≤ M) →
      |∑ᶠ x ∈ S, u x| ≤ M * (S.ncard : ℝ) := by
    intro S u hS hu
    rw [finsum_mem_eq_finite_toFinset_sum u hS, ncard_eq_toFinset_card S hS]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul hS.toFinset (fun x => |u x|) M
      (fun x hx => hu x (hS.mem_toFinset.mp hx))
    simpa [mul_comm] using this
  have hsplit : ∀ {S : Set α} {u : α → ℝ}, S.Finite → S₀ ⊆ S →
      ∑ᶠ x ∈ S, u x = ∑ᶠ x ∈ S₀, u x + ∑ᶠ x ∈ S \ S₀, u x := by
    intro S u hS h
    conv_lhs => rw [← union_sdiff_cancel h]
    exact finsum_mem_union disjoint_sdiff_right h0 (hS.subset sdiff_subset)
  have hsame : ∑ᶠ x ∈ S₀, f x = ∑ᶠ x ∈ S₀, g x := finsum_mem_congr rfl hfg
  rw [hsplit h₁ h01, hsplit h₂ h02, hsame]
  have e1 := hbound (h₁.subset sdiff_subset) hf
  have e2 := hbound (h₂.subset sdiff_subset) hg
  have e3 := abs_sub (∑ᶠ x ∈ S₁ \ S₀, f x) (∑ᶠ x ∈ S₂ \ S₀, g x)
  have e4 : ∑ᶠ x ∈ S₀, g x + ∑ᶠ x ∈ S₁ \ S₀, f x - (∑ᶠ x ∈ S₀, g x + ∑ᶠ x ∈ S₂ \ S₀, g x) =
      ∑ᶠ x ∈ S₁ \ S₀, f x - ∑ᶠ x ∈ S₂ \ S₀, g x := by ring
  rw [e4, mul_add]
  linarith
theorem abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} {S : ℝ} (hf : 0 < ∫ ω, Real.exp (-f ω) ∂μ)
    (hg : 0 < ∫ ω, Real.exp (-g ω) ∂μ) (h : ∀ ω, |f ω - g ω| ≤ S) :
    |Real.log (∫ ω, Real.exp (-f ω) ∂μ) - Real.log (∫ ω, Real.exp (-g ω) ∂μ)| ≤ S := by
  have hfi : Integrable (fun ω => Real.exp (-f ω)) μ := by
    by_contra hn
    rw [integral_undef hn] at hf
    exact lt_irrefl _ hf
  have hgi : Integrable (fun ω => Real.exp (-g ω)) μ := by
    by_contra hn
    rw [integral_undef hn] at hg
    exact lt_irrefl _ hg
  have key : ∀ {u v : Ω → ℝ}, Integrable (fun ω => Real.exp (-u ω)) μ →
      Integrable (fun ω => Real.exp (-v ω)) μ → 0 < ∫ ω, Real.exp (-u ω) ∂μ →
      0 < ∫ ω, Real.exp (-v ω) ∂μ → (∀ ω, |u ω - v ω| ≤ S) →
      Real.log (∫ ω, Real.exp (-u ω) ∂μ) ≤ S + Real.log (∫ ω, Real.exp (-v ω) ∂μ) := by
    intro u v hu hv hu0 hv0 huv
    have hle : ∫ ω, Real.exp (-u ω) ∂μ ≤ ∫ ω, Real.exp S * Real.exp (-v ω) ∂μ := by
      refine integral_mono hu (hv.const_mul _) fun ω => ?_
      change Real.exp (-u ω) ≤ Real.exp S * Real.exp (-v ω)
      rw [← Real.exp_add, Real.exp_le_exp]
      have := (abs_le.mp (huv ω)).2
      have := (abs_le.mp (huv ω)).1
      linarith
    rw [integral_const_mul] at hle
    calc Real.log (∫ ω, Real.exp (-u ω) ∂μ)
        ≤ Real.log (Real.exp S * ∫ ω, Real.exp (-v ω) ∂μ) := Real.log_le_log hu0 hle
      _ = S + Real.log (∫ ω, Real.exp (-v ω) ∂μ) := by
          rw [Real.log_mul (Real.exp_pos S).ne' hv0.ne', Real.log_exp]
  have h1 := key hfi hgi hf hg h
  have h2 := key hgi hfi hg hf fun ω => by rw [abs_sub_comm]; exact h ω
  rw [abs_le]
  constructor <;> linarith
section Terms
variable (d : BoxTorusComparisonData)
def shellAnchors : Set (LatticePoint 1) :=
  {z | ∃ x ∈ d.normalFrame.boundaryShell d.sideLengths d.boxWidth, x ∈ siteCube z d.boxWidth}
def boxFaces : Set (ElementaryPlaquette 1) :=
  {p | p.corner ∈ d.normalFrame.fundamentalBox d.sideLengths}
def interiorFaces : Set (ElementaryPlaquette 1) := {p | (Term.plaquette p : d.Term).IsInner}
def boxLabels : Set d.obsArray.Label :=
  {i | d.obsAnchor + (i.1 : LatticePoint 1) ∈ d.normalFrame.fundamentalBox d.sideLengths}
def interiorLabels : Set d.obsArray.Label := {i | (Term.shifted i.1 : d.Term).IsInner}
theorem shellAnchors_finite_and_card
    (hL : (d.normalFrame.boundaryShell d.sideLengths d.boxWidth).Finite) :
    (shellAnchors d).Finite ∧
      (shellAnchors d).ncard ≤
        ((d.boxWidth : ℕ) + 1) ^ 4 *
          (d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard := by
  classical
  let f : LatticePoint 1 → Finset (LatticePoint 1) :=
    fun x => (cubeAnchors_finite d.boxWidth x).toFinset
  have heq : shellAnchors d =
      ((hL.toFinset.biUnion f : Finset (LatticePoint 1)) : Set (LatticePoint 1)) := by
    ext z
    simp [shellAnchors, f]
  rw [heq]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [ncard_coe_finset, ncard_eq_toFinset_card _ hL]
  have h := Finset.card_biUnion_le_card_mul hL.toFinset f (((d.boxWidth : ℕ) + 1) ^ 4)
    fun x _ => by
      have := ncard_cubeAnchors d.boxWidth x
      rw [ncard_eq_toFinset_card _ (cubeAnchors_finite d.boxWidth x)] at this
      exact this.le
  rwa [mul_comm] at h
variable {d}
theorem label_ext {i j : d.obsArray.Label} (h : (i.1 : LatticePoint 1) = (j.1 : LatticePoint 1)) :
    i = j :=
  Prod.ext (Subtype.ext h) (Subsingleton.elim (α := Fin 1) _ _)
variable (d) in
theorem labels_anchored_in {Z : Set (LatticePoint 1)} (hZ : Z.Finite) :
    {i : d.obsArray.Label | d.obsAnchor + (i.1 : LatticePoint 1) ∈ Z}.Finite ∧
      {i : d.obsArray.Label | d.obsAnchor + (i.1 : LatticePoint 1) ∈ Z}.ncard ≤ Z.ncard := by
  let f : d.obsArray.Label → LatticePoint 1 := fun i => d.obsAnchor + (i.1 : LatticePoint 1)
  have hf : Function.Injective f := fun i j h => label_ext (add_left_cancel h)
  have hmaps : f '' {i : d.obsArray.Label | d.obsAnchor + (i.1 : LatticePoint 1) ∈ Z} ⊆ Z := by
    rintro _ ⟨i, hi, rfl⟩
    exact hi
  refine ⟨Finite.of_finite_image (hZ.subset hmaps) hf.injOn, ?_⟩
  calc _ = (f '' {i : d.obsArray.Label | d.obsAnchor + (i.1 : LatticePoint 1) ∈ Z}).ncard :=
        (ncard_image_of_injective _ hf).symm
    _ ≤ Z.ncard := ncard_le_ncard hmaps hZ
theorem anchor_mem_siteBox (T : d.Term) : T.anchor ∈ T.siteBox := self_mem_siteCube _ _
theorem mem_shell_of_mem_siteBox {T : d.Term} (hin : ¬T.IsInner) {x : LatticePoint 1}
    (hx : x ∈ T.siteBox) (hD : x ∈ d.normalFrame.fundamentalBox d.sideLengths) :
    x ∈ d.normalFrame.boundaryShell d.sideLengths d.boxWidth := by
  obtain ⟨y, hy, hyD⟩ := not_subset.mp hin
  exact ⟨hD, y, hyD, norm_sub_le_of_mem_siteCube hx hy⟩
theorem anchor_mem_shellAnchors (hT : TermsInBoxes.Statement) {T : d.Term}
    (hin : ¬T.IsInner) {b : Link 1} (hb : b ∈ T.links)
    (hbD : b ∈ d.normalFrame.boxLinks d.sideLengths) :
    T.anchor ∈ shellAnchors d := by
  obtain ⟨x, hx, μ, rfl⟩ := hbD
  have hbox : x ∈ T.siteBox := ((hT d).2.1 T _ hb).1
  exact ⟨x, mem_shell_of_mem_siteBox hin hbox hx, hbox⟩
theorem link_mem_boxLinks_of_isInner (hT : TermsInBoxes.Statement) {T : d.Term}
    (hin : T.IsInner) {b : Link 1} (hb : b ∈ T.links) :
    b ∈ d.normalFrame.boxLinks d.sideLengths := by
  obtain ⟨-, -, x, hx, μ, rfl⟩ := (hT d).2.1 T b hb
  exact ⟨x, hin hx, μ, rfl⟩
theorem obs_support_nonempty (hL : LocalFunctionProperties 1) :
    (observableSupport d.obs).Nonempty := by
  by_contra hne
  have hdep := (hL.2.2.2.2.2.2.2 d.obs d.obs_mem.1 d.obs_mem.2.1).1
  rw [not_nonempty_iff_eq_empty.mp hne] at hdep
  let U₀ : GaugeField 1 := ⟨fun _ => 1, fun _ => by simp⟩
  exact d.obs_nonconst ⟨d.obs U₀, fun U => hdep U U₀ (by simp)⟩
theorem shifted_links_nonempty (hT : TermsInBoxes.Statement)
    (hL : LocalFunctionProperties 1) (v : d.translationGroup) :
    (Term.shifted v : d.Term).links.Nonempty := by
  rw [(hT d).1 v]
  exact (obs_support_nonempty hL).image _
theorem interiorFaces_subset_facesMeeting (hT : TermsInBoxes.Statement) {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) :
    interiorFaces d ⊆ facesMeeting (W.links : Set (Link 1)) := by
  intro p hp
  have hb : Link.forwardFrom p.corner p.lowAxis ∈ p.linkSet := by
    simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
  refine ⟨_, hb, ?_⟩
  rw [hW]
  exact link_mem_boxLinks_of_isInner hT (T := .plaquette p) hp hb
theorem interiorFaces_subset_boxFaces : interiorFaces d ⊆ boxFaces d :=
  fun p hp => hp (anchor_mem_siteBox (Term.plaquette p : d.Term))
theorem interiorLabels_subset_labelsTouching (hT : TermsInBoxes.Statement)
    (hL : LocalFunctionProperties 1) {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) :
    interiorLabels d ⊆ d.obsArray.labelsTouching W := by
  intro i hi
  obtain ⟨b, hb⟩ := shifted_links_nonempty hT hL (d := d) i.1
  refine ⟨b, hb, ?_⟩
  rw [hW]
  exact link_mem_boxLinks_of_isInner hT hi hb
theorem interiorLabels_subset_boxLabels : interiorLabels d ⊆ boxLabels d :=
  fun i hi => hi (anchor_mem_siteBox (Term.shifted i.1 : d.Term))
theorem facesMeeting_diff_subset (hT : TermsInBoxes.Statement) {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) :
    facesMeeting (W.links : Set (Link 1)) \ interiorFaces d ⊆
      {p : ElementaryPlaquette 1 | p.corner ∈ shellAnchors d} := by
  rintro p ⟨⟨b, hb, hbW⟩, hn⟩
  rw [hW] at hbW
  exact anchor_mem_shellAnchors hT (T := .plaquette p) hn hb hbW
theorem boxFaces_diff_subset :
    boxFaces d \ interiorFaces d ⊆
      {p : ElementaryPlaquette 1 |
        p.corner ∈ d.normalFrame.boundaryShell d.sideLengths d.boxWidth} := by
  rintro p ⟨hp, hn⟩
  exact mem_shell_of_mem_siteBox (T := .plaquette p) hn (anchor_mem_siteBox _) hp
theorem labelsTouching_diff_subset (hT : TermsInBoxes.Statement) {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) :
    d.obsArray.labelsTouching W \ interiorLabels d ⊆
      {i : d.obsArray.Label | d.obsAnchor + (i.1 : LatticePoint 1) ∈ shellAnchors d} := by
  rintro i ⟨⟨b, hb, hbW⟩, hn⟩
  have hbW' : b ∈ (W.links : Set (Link 1)) := hbW
  rw [hW] at hbW'
  exact anchor_mem_shellAnchors hT (T := .shifted i.1) hn hb hbW'
theorem boxLabels_diff_subset :
    boxLabels d \ interiorLabels d ⊆
      {i : d.obsArray.Label |
        d.obsAnchor + (i.1 : LatticePoint 1) ∈
          d.normalFrame.boundaryShell d.sideLengths d.boxWidth} := by
  rintro i ⟨hi, hn⟩
  exact mem_shell_of_mem_siteBox (T := .shifted i.1) hn (anchor_mem_siteBox _) hi
theorem translate_mem (hI : LatticeSymmetryProperties 1) (i : d.obsArray.Label) :
    d.obsArray.translate i ∈ continuousLocalFunctions 1 := by
  have h := (hI (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))).2.2.2.2.1
  rw [← h]
  exact ⟨_, d.obs_mem, rfl⟩
theorem abs_translate_re_le (i : d.obsArray.Label) (X : GaugeField 1) :
    |(d.obsArray.translate i X).re| ≤ observableSupNorm d.obs := by
  obtain ⟨C, hC⟩ := d.obs_mem.1.2
  refine (Complex.abs_re_le_norm _).trans ?_
  exact le_ciSup (f := fun U => ‖d.obs U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ _
theorem supNorm_obs_nonneg : 0 ≤ observableSupNorm d.obs :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_energy_sub_le (hT : TermsInBoxes.Statement) (hL : LocalFunctionProperties 1)
    (hI : LatticeSymmetryProperties 1)
    (hP : ContinuousLocalAndFaceEnergies.Statement)
    (hS : d.obsArray.SupportsLocallyFinite)
    (hD : (d.normalFrame.fundamentalBox d.sideLengths).Finite) {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) {β : ℝ} (hβ : 0 < β)
    (t : ℝ) {X Y : GaugeField 1}
    (hXY : ∀ b ∈ d.normalFrame.boxLinks d.sideLengths, X b = Y b) :
    |(β * ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy X p -
          t * ∑ᶠ i ∈ d.obsArray.labelsTouching W, (d.obsArray.translate i X).re) -
        (β * ∑ᶠ p ∈ boxFaces d, faceEnergy Y p -
          t * ∑ᶠ i ∈ boxLabels d, (d.obsArray.translate i Y).re)| ≤
      (12 * β + |t| * observableSupNorm d.obs) *
        (((shellAnchors d).ncard : ℝ) +
          ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ)) := by
  have hLfin : (d.normalFrame.boundaryShell d.sideLengths d.boxWidth).Finite :=
    hD.subset fun x hx => hx.1
  have hZfin := (shellAnchors_finite_and_card d hLfin).1
  have hP1 : (facesMeeting (W.links : Set (Link 1))).Finite :=
    hP.2.2 _ (fun b hb => W.isPositive b hb) W.links.finite_toSet
  have hP2 : (boxFaces d).Finite := (faces_cornered_in hD).1
  have hI1 : (d.obsArray.labelsTouching W).Finite := hS.finite_labelsTouching W
  have hI2 : (boxLabels d).Finite := (labels_anchored_in d hD).1
  have hact : ∀ (p : ElementaryPlaquette 1) (U : GaugeField 1), |faceEnergy U p| ≤ 2 := by
    intro p U
    have h := (hP.2.1 p).2.2 U
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hPsum := abs_finsum_sub_finsum_le (f := fun p => faceEnergy X p)
    (g := fun p => faceEnergy Y p) (M := 2) hP1 hP2 (interiorFaces_subset_facesMeeting hT hW)
    interiorFaces_subset_boxFaces
    (fun p hp => by
      have hdep := (hP.2.1 p).2.1 X Y fun b hb =>
        hXY b (link_mem_boxLinks_of_isInner hT (T := .plaquette p) hp hb)
      exact Complex.ofReal_injective hdep)
    (fun p _ => hact p X) (fun p _ => hact p Y)
  have hIsum := abs_finsum_sub_finsum_le (f := fun i => (d.obsArray.translate i X).re)
    (g := fun i => (d.obsArray.translate i Y).re) (M := observableSupNorm d.obs) hI1 hI2
    (interiorLabels_subset_labelsTouching hT hL hW) interiorLabels_subset_boxLabels
    (fun i hi => by
      have hm := translate_mem hI i
      have hdep := (hL.2.2.2.2.2.2.2 _ hm.1 hm.2.1).1 X Y fun b hb =>
        hXY b (link_mem_boxLinks_of_isInner hT (T := .shifted i.1) hi hb)
      rw [hdep])
    (fun i _ => abs_translate_re_le i X) (fun i _ => abs_translate_re_le i Y)
  have hn1 : (((facesMeeting (W.links : Set (Link 1)) \ interiorFaces d).ncard : ℕ) : ℝ) ≤
      6 * ((shellAnchors d).ncard : ℝ) := by
    have h := faces_cornered_in hZfin
    have h' := (ncard_le_ncard (facesMeeting_diff_subset hT hW) h.1).trans h.2
    exact_mod_cast h'
  have hn2 : (((boxFaces d \ interiorFaces d).ncard : ℕ) : ℝ) ≤
      6 * ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) := by
    have h := faces_cornered_in hLfin
    have h' := (ncard_le_ncard boxFaces_diff_subset h.1).trans h.2
    exact_mod_cast h'
  have hm1 : (((d.obsArray.labelsTouching W \ interiorLabels d).ncard : ℕ) : ℝ) ≤
      ((shellAnchors d).ncard : ℝ) := by
    have h := labels_anchored_in d hZfin
    have h' := (ncard_le_ncard (labelsTouching_diff_subset hT hW) h.1).trans h.2
    exact_mod_cast h'
  have hm2 : (((boxLabels d \ interiorLabels d).ncard : ℕ) : ℝ) ≤
      ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) := by
    have h := labels_anchored_in d hLfin
    have h' := (ncard_le_ncard boxLabels_diff_subset h.1).trans h.2
    exact_mod_cast h'
  have hN := supNorm_obs_nonneg (d := d)
  set z : ℝ := ((shellAnchors d).ncard : ℝ)
  set l : ℝ := ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ)
  set N := observableSupNorm d.obs
  set p₁ := ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy X p
  set p₂ := ∑ᶠ p ∈ boxFaces d, faceEnergy Y p
  set i₁ := ∑ᶠ i ∈ d.obsArray.labelsTouching W, (d.obsArray.translate i X).re
  set i₂ := ∑ᶠ i ∈ boxLabels d, (d.obsArray.translate i Y).re
  have hA : |p₁ - p₂| ≤ 12 * (z + l) := hPsum.trans (by linarith)
  have hC : |i₁ - i₂| ≤ N * (z + l) :=
    hIsum.trans (mul_le_mul_of_nonneg_left (by linarith) hN)
  calc |(β * p₁ - t * i₁) - (β * p₂ - t * i₂)| = |β * (p₁ - p₂) - t * (i₁ - i₂)| := by
        congr 1
        ring
    _ ≤ |β * (p₁ - p₂)| + |t * (i₁ - i₂)| := abs_sub _ _
    _ = β * |p₁ - p₂| + |t| * |i₁ - i₂| := by rw [abs_mul, abs_mul, abs_of_pos hβ]
    _ ≤ β * (12 * (z + l)) + |t| * (N * (z + l)) := by
        have h1 := mul_le_mul_of_nonneg_left hA hβ.le
        have h2 := mul_le_mul_of_nonneg_left hC (abs_nonneg t)
        linarith
    _ = (12 * β + |t| * N) * (z + l) := by ring
end Terms
section Torus
variable {d : BoxTorusComparisonData}
theorem mem_faceClass_self (hF : d.periodSublattice.IsFaithfulQuotient) (q : ElementaryPlaquette 1) :
    q ∈ (d.periodSublattice.faceClass q : Set (ElementaryPlaquette 1)) := by
  have hmem : (shift (0 : LatticePoint 1)).plaquetteMap q ∈ d.periodSublattice.plaquetteOrbit q :=
    ⟨0, zero_mem _, rfl⟩
  refine ⟨0, zero_mem _, (hF.plaquette_eq_of_shared_corner q _ hmem ?_).symm⟩
  have hq : q.corner ∈ q.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  unfold LatticeSymmetry.plaquetteMap
  split_ifs with h
  · refine ⟨q.corner, hq, ?_⟩
    rw [h.choose_spec]
    exact ⟨q.corner, hq, Subtype.ext (by simp [LatticeSymmetry.pointMap, shift])⟩
  · exact ⟨q.corner, hq, hq⟩
theorem faceClass_bijOn (hF : d.periodSublattice.IsFaithfulQuotient)
    (hrep : ∀ c : d.periodSublattice.QuotientTorus, ∃! x : LatticePoint 1,
      x ∈ d.normalFrame.fundamentalBox d.sideLengths ∧ d.periodSublattice.quotientMap x = c) :
    BijOn d.periodSublattice.faceClass (boxFaces d) univ := by
  obtain ⟨e, he⟩ := hF.plaquette_equiv
  refine ⟨fun _ _ => mem_univ _, fun p hp p' hp' h => ?_, fun c _ => ?_⟩
  · have h1 := congrArg e h
    rw [he, he] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Prod.mk.injEq] at h2
    exact ElementaryPlaquette.ext ((hrep _).unique ⟨hp, rfl⟩ ⟨hp', h2.1.symm⟩) h2.2.1 h2.2.2
  · rcases hc : e c with ⟨⟨c₀, μ, ν⟩, hlt⟩
    obtain ⟨x, ⟨hxD, hx⟩, -⟩ := hrep c₀
    refine ⟨⟨x, μ, ν, hlt⟩, hxD, e.injective ?_⟩
    rw [he, hc]
    exact Subtype.ext (by simp [hx])
theorem finsum_quotientFaceEnergy_eq (hF : d.periodSublattice.IsFaithfulQuotient)
    (hE : d.periodSublattice.LiftIsFaithful)
    (hrep : ∀ c : d.periodSublattice.QuotientTorus, ∃! x : LatticePoint 1,
      x ∈ d.normalFrame.fundamentalBox d.sideLengths ∧ d.periodSublattice.quotientMap x = c)
    (U : d.periodSublattice.QuotientField) :
    ∑ᶠ p : d.periodSublattice.QuotientPlaquette, d.periodSublattice.quotientFaceEnergy U p =
      ∑ᶠ p ∈ boxFaces d, faceEnergy (d.periodSublattice.lift U) p := by
  rw [← finsum_mem_univ]
  exact (finsum_mem_eq_of_bijOn _ (faceClass_bijOn hF hrep)
    fun p _ => hE.faceEnergy_lift U _ p (mem_faceClass_self hF p)).symm
theorem labelCoset_bijOn
    (hrep : ∀ c : d.periodSublattice.QuotientTorus, ∃! x : LatticePoint 1,
      x ∈ d.normalFrame.fundamentalBox d.sideLengths ∧ d.periodSublattice.quotientMap x = c) :
    BijOn (fun i : d.obsArray.Label =>
        ((QuotientAddGroup.mk i.1 : d.obsArray.Cosets d.periodSublattice), i.2))
      (boxLabels d) univ := by
  refine ⟨fun _ _ => mem_univ _, fun i hi j hj h => ?_, fun c _ => ?_⟩
  · have h1 : (QuotientAddGroup.mk i.1 : d.obsArray.Cosets d.periodSublattice) =
        QuotientAddGroup.mk j.1 :=
      congrArg Prod.fst h
    have h2 : -(i.1 : LatticePoint 1) + (j.1 : LatticePoint 1) ∈ d.periodSublattice.periods := by
      have := QuotientAddGroup.eq.mp h1
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    have h3 : d.periodSublattice.quotientMap (d.obsAnchor + (j.1 : LatticePoint 1)) =
        d.periodSublattice.quotientMap (d.obsAnchor + (i.1 : LatticePoint 1)) := by
      refine (QuotientAddGroup.eq.mpr ?_).symm
      have e : -(d.obsAnchor + (i.1 : LatticePoint 1)) + (d.obsAnchor + (j.1 : LatticePoint 1)) =
          -(i.1 : LatticePoint 1) + (j.1 : LatticePoint 1) := by abel
      rw [e]
      exact h2
    have h4 := (hrep _).unique ⟨hi, rfl⟩ ⟨hj, h3⟩
    exact label_ext (add_left_cancel h4)
  · obtain ⟨q, ι⟩ := c
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, ⟨hxD, hx⟩, -⟩ :=
      hrep (d.periodSublattice.quotientMap (d.obsAnchor + (w : LatticePoint 1)))
    have hΓ : -x + (d.obsAnchor + (w : LatticePoint 1)) ∈ d.periodSublattice.periods :=
      QuotientAddGroup.eq.mp hx
    have hv : x - d.obsAnchor ∈ d.translationGroup := by
      have e : x - d.obsAnchor =
          (w : LatticePoint 1) - (-x + (d.obsAnchor + (w : LatticePoint 1))) := by abel
      rw [e]
      exact sub_mem w.2 (d.periods_le_translationGroup hΓ)
    refine ⟨(⟨_, hv⟩, ι), ?_, ?_⟩
    · change d.obsAnchor + (x - d.obsAnchor) ∈ d.normalFrame.fundamentalBox d.sideLengths
      simpa using hxD
    · refine Prod.ext (QuotientAddGroup.eq.mpr ?_) rfl
      have e : -(x - d.obsAnchor) + (w : LatticePoint 1) =
          -x + (d.obsAnchor + (w : LatticePoint 1)) := by abel
      rw [AddSubgroup.mem_addSubgroupOf]
      change -(x - d.obsAnchor) + (w : LatticePoint 1) ∈ d.periodSublattice.periods
      rw [e]
      exact hΓ
theorem periodicSum_eq {β t : ℝ}
    (hDesc : d.obsArray.PeriodicDescentWellDefined d.periodSublattice β t)
    (hrep : ∀ c : d.periodSublattice.QuotientTorus, ∃! x : LatticePoint 1,
      x ∈ d.normalFrame.fundamentalBox d.sideLengths ∧ d.periodSublattice.quotientMap x = c)
    (U : d.periodSublattice.QuotientField) :
    d.obsArray.periodicSum d.periodSublattice U =
      ∑ᶠ i ∈ boxLabels d, (d.obsArray.translate i (d.periodSublattice.lift U)).re := by
  rw [LocalObservableArray.periodicSum, ← finsum_mem_univ]
  refine (finsum_mem_eq_of_bijOn _ (labelCoset_bijOn hrep) fun i _ => ?_).symm
  have h := hDesc.periodize_translate (d.obsArray.cosetRep d.periodSublattice
    (QuotientAddGroup.mk i.1)) i.1 i.2 (QuotientAddGroup.out_eq' _)
  exact congrArg Complex.re (congrFun h U).symm
def windowLinkClass (W : LinkWindow 1) (b : W.links) : d.periodSublattice.QuotientLink :=
  d.periodSublattice.linkClass ⟨b.1, W.isPositive b.1 b.2⟩
theorem windowLinkClass_bijective (hF : d.periodSublattice.IsFaithfulQuotient)
    (hrep : ∀ c : d.periodSublattice.QuotientTorus, ∃! x : LatticePoint 1,
      x ∈ d.normalFrame.fundamentalBox d.sideLengths ∧ d.periodSublattice.quotientMap x = c)
    {W : LinkWindow 1}
    (hW : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths) :
    Function.Bijective (windowLinkClass (d := d) W) := by
  obtain ⟨e, he⟩ := hF.link_equiv
  have hform : ∀ b : W.links, ∃ x ∈ d.normalFrame.fundamentalBox d.sideLengths, ∃ μ : Fin 4,
      (⟨b.1, W.isPositive b.1 b.2⟩ : PositiveLink 1) = PositiveLink.forwardAt x μ := by
    intro b
    have hb : b.1 ∈ (W.links : Set (Link 1)) := b.2
    rw [hW] at hb
    obtain ⟨x, hx, μ, h⟩ := hb
    exact ⟨x, hx, μ, Subtype.ext h⟩
  constructor
  · intro b b' h
    obtain ⟨x, hx, μ, h₁⟩ := hform b
    obtain ⟨x', hx', μ', h₂⟩ := hform b'
    have h₃ := congrArg e h
    simp only [windowLinkClass, h₁, h₂, he, Prod.mk.injEq] at h₃
    have h₄ : x = x' := (hrep _).unique ⟨hx, rfl⟩ ⟨hx', h₃.1.symm⟩
    have h₅ := h₁.trans ((congrArg₂ PositiveLink.forwardAt h₄ h₃.2).trans h₂.symm)
    have h₆ : (b : Link 1) = b' := congrArg (fun z : PositiveLink 1 => z.1) h₅
    exact Subtype.ext h₆
  · intro c
    rcases hc : e c with ⟨c₀, μ⟩
    obtain ⟨x, ⟨hxD, hx⟩, -⟩ := hrep c₀
    have hmem : (PositiveLink.forwardAt x μ).1 ∈ (W.links : Set (Link 1)) := by
      rw [hW]
      exact ⟨x, hxD, μ, rfl⟩
    refine ⟨⟨_, hmem⟩, e.injective ?_⟩
    have h₁ : windowLinkClass (d := d) W ⟨_, hmem⟩ =
        d.periodSublattice.linkClass (PositiveLink.forwardAt x μ) := rfl
    rw [h₁, he, hc, hx]
theorem glue_apply_of_mem (W : LinkWindow 1) (V : W.Assignments) (U : GaugeField 1) {b : Link 1}
    (hb : b ∈ W.links) : (W.glue one_pos V U) b = V ⟨b, hb⟩ :=
  dif_pos hb
end Torus
theorem allData_holds (hE : ElementaryLatticeFacts)
    (hTori : ToriArraysAndTiltedMeasuresFacts)
    (hBox : FundamentalBox.RepresentsQuotientWithThinShell)
    (hFin : FiniteTorusPartitionsAndLifts)
    (hP : ContinuousLocalAndFaceEnergies.Statement)
    (hT : TermsInBoxes.Statement) : AllData := by
  intro d β hβ
  obtain ⟨-, -, -, hL, -, -, -, hI, -⟩ := hE 1 β one_pos hβ
  obtain ⟨hA, hB, -, -⟩ := hTori β hβ
  have hF := (hA 1 one_pos d.periodSublattice).1
  have hX := (hA 1 one_pos d.periodSublattice).2.1
  have hRect := hBox d.normalFrame d.sideLengths d.periodSublattice d.periodSublattice_isBoxShaped
  have hrep := hRect.1
  have hD : (d.normalFrame.fundamentalBox d.sideLengths).Finite :=
    finite_of_encard_eq_coe hRect.2.1
  have hLfin : (d.normalFrame.boundaryShell d.sideLengths d.boxWidth).Finite :=
    hD.subset fun x hx => hx.1
  have hZ := shellAnchors_finite_and_card d hLfin
  have hdesc : d.obsArray.FitsPeriods d.periodSublattice := d.periods_le_translationGroup
  have hbl : (((shellAnchors d).ncard : ℕ) : ℝ) +
      ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) ≤
      (boxCoverNumber d.boxWidth : ℝ) *
        ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) := by
    have h : (((shellAnchors d).ncard : ℕ) : ℝ) ≤
        ((((d.boxWidth : ℕ) + 1) ^ 4 : ℕ) : ℝ) *
          ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) := by
      exact_mod_cast hZ.2
    have hs : (boxCoverNumber d.boxWidth : ℝ) = ((((d.boxWidth : ℕ) + 1) ^ 4 : ℕ) : ℝ) + 1 := by
      simp [boxCoverNumber]
    rw [hs, add_mul, one_mul]
    linarith
  refine ⟨fun x => ?_, ?_, fun W hW => ⟨fun t U' => ?_, ?_⟩⟩
  · rw [ncard_cubeAnchors]
    rfl
  · have h1 : (1 : ℝ) ≤ ((d.boxWidth : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt d.boxWidth.pos
    have h2 : (((d.boxWidth : ℕ) : ℝ) + 1) ^ 4 ≤ (2 * ((d.boxWidth : ℕ) : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h3 : (1 : ℝ) ≤ ((d.boxWidth : ℕ) : ℝ) ^ 4 := one_le_pow₀ h1
    simp only [boxCoverNumber, Constants.BoxTorus.anchorNumber]
    push_cast
    linarith
  · have hpos := ((hFin β hβ d.periodSublattice).2 d.obsArray hdesc t).1
    have hDesc := (hB d.obsArray t).2.2 d.periodSublattice hdesc
    let e : W.links ≃ d.periodSublattice.QuotientLink :=
      Equiv.ofBijective _ (windowLinkClass_bijective hF hrep hW)
    let R : W.Assignments ≃ᵐ d.periodSublattice.QuotientField :=
      MeasurableEquiv.piCongrLeft
        (fun _ : d.periodSublattice.QuotientLink => Matrices.ComplexMatrix2.specialUnitary) e
    have hRapp : ∀ (V : W.Assignments) (b : W.links), R V (e b) = V b := by
      intro V b
      simp [R, MeasurableEquiv.coe_piCongrLeft]
    have hmap : W.haarProd.map R = d.periodSublattice.quotientHaar :=
      Measure.infinitePi_map_piCongrLeft
        (μ := fun _ : d.periodSublattice.QuotientLink => Matrices.ComplexMatrix2.haarProb) e
    have hagree : ∀ (V : W.Assignments), ∀ b ∈ d.normalFrame.boxLinks d.sideLengths,
        (W.glue one_pos V U') b = d.periodSublattice.lift (R V) b := by
      intro V b hb
      have hbW : b ∈ W.links := by
        have : b ∈ (W.links : Set (Link 1)) := by rw [hW]; exact hb
        exact this
      rw [glue_apply_of_mem W V U' hbW,
        PeriodSublattice.lift_apply_positive d.periodSublattice (R V) ⟨b, W.isPositive b hbW⟩]
      exact (hRapp V ⟨b, hbW⟩).symm
    let g : W.Assignments → ℝ := fun V =>
      β * ∑ᶠ p ∈ boxFaces d, faceEnergy (d.periodSublattice.lift (R V)) p -
        t * ∑ᶠ i ∈ boxLabels d, (d.obsArray.translate i (d.periodSublattice.lift (R V))).re
    have hZΓ : d.obsArray.tiltedPartition d.periodSublattice β t =
        ∫ V, Real.exp (-g V) ∂W.haarProd := by
      rw [LocalObservableArray.tiltedPartition, ← hmap, integral_map_equiv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      change Real.exp _ = Real.exp _
      rw [finsum_quotientFaceEnergy_eq hF hX hrep, periodicSum_eq hDesc hrep]
      congr 1
      simp only [g]
      ring
    have hbound := abs_log_integral_exp_sub_le W.haarProd
      (f := fun V => d.obsArray.windowEnergy β t W (W.glue one_pos V U')) (g := g)
      (hpos.windowPartition_pos W U') (hZΓ ▸ hpos.tiltedPartition_pos)
      (fun V => abs_energy_sub_le hT hL hI hP (hB d.obsArray t).1 hD hW hβ t (hagree V))
    refine (hZΓ ▸ hbound : _).trans ?_
    have hN := supNorm_obs_nonneg (d := d)
    have ht : 0 ≤ |t| * observableSupNorm d.obs := mul_nonneg (abs_nonneg t) hN
    have hc : (Constants.BoxTorus.surfaceNumber : ℝ) = 12 := by
      norm_num [Constants.BoxTorus.surfaceNumber]
    rw [hc, mul_assoc ((12 : ℝ) * _)]
    exact mul_le_mul (by linarith) hbl (by positivity) (by linarith)
  · have hS := (hB d.obsArray (0 : ℝ)).1
    have hI1 := hS.finite_labelsTouching W
    have hI2 : (boxLabels d).Finite := (labels_anchored_in d hD).1
    have hin1 := interiorLabels_subset_labelsTouching hT hL hW
    have hin2 : interiorLabels d ⊆ boxLabels d := interiorLabels_subset_boxLabels
    have c1 := ncard_sdiff_add_ncard_of_subset hin1 hI1
    have c2 := ncard_sdiff_add_ncard_of_subset hin2 hI2
    have hm1 : (d.obsArray.labelsTouching W \ interiorLabels d).ncard ≤ (shellAnchors d).ncard := by
      have h := labels_anchored_in d hZ.1
      exact (ncard_le_ncard (labelsTouching_diff_subset hT hW) h.1).trans h.2
    have hm2 : (boxLabels d \ interiorLabels d).ncard ≤
        (d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard := by
      have h := labels_anchored_in d hLfin
      exact (ncard_le_ncard boxLabels_diff_subset h.1).trans h.2
    have hcard : (boxLabels d).ncard =
        (d.periodSublattice.periods.addSubgroupOf d.translationGroup).index := by
      have hb := labelCoset_bijOn (d := d) hrep
      have h1 := hb.injOn.ncard_image
      rw [hb.image_eq, ncard_univ, Nat.card_prod] at h1
      have h2 : Nat.card (Fin d.obsArray.size) = 1 :=
        (Nat.card_eq_fintype_card.trans (Fintype.card_fin _)).trans rfl
      rw [h2, mul_one] at h1
      exact h1.symm
    have hfu := (hFin β hβ d.periodSublattice).1 d.translationGroup d.periods_le_translationGroup
    have hDcard : (d.normalFrame.fundamentalBox d.sideLengths).ncard =
        d.periodSublattice.periods.index := by
      rw [ncard_def, hRect.2.1]
      rfl
    have hQ : ((d.translationGroup.index : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast d.translationGroup_finiteIndex.index_ne_zero
    have hκ : d.obsArray.invIndex * ((d.normalFrame.fundamentalBox d.sideLengths).ncard : ℝ) =
        ((boxLabels d).ncard : ℝ) := by
      rw [hDcard, hfu.index_mul, hcard]
      change ((d.translationGroup.index : ℕ) : ℝ)⁻¹ * _ = _
      push_cast
      field_simp
    rw [hκ]
    have r1 : ((d.obsArray.labelsTouching W).ncard : ℝ) =
        ((d.obsArray.labelsTouching W \ interiorLabels d).ncard : ℝ) +
          ((interiorLabels d).ncard : ℝ) := by
      exact_mod_cast c1.symm
    have r2 : ((boxLabels d).ncard : ℝ) =
        ((boxLabels d \ interiorLabels d).ncard : ℝ) + ((interiorLabels d).ncard : ℝ) := by
      exact_mod_cast c2.symm
    have m1 : ((d.obsArray.labelsTouching W \ interiorLabels d).ncard : ℝ) ≤
        ((shellAnchors d).ncard : ℝ) := by exact_mod_cast hm1
    have m2 : ((boxLabels d \ interiorLabels d).ncard : ℝ) ≤
        ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) := by
      exact_mod_cast hm2
    rw [r1, r2, abs_le]
    constructor <;> linarith
end YangMills.Construction.InfiniteLattice.BoxTorusSurfaceBound
