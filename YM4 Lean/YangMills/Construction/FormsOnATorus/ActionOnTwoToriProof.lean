import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMovesProof
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCubeProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusComparison
open TorusFields TorusLumps TorusChain TorusContours StepCosts LevelAction ColdChain
open BlockAverages hiding unitStep wilsonAction
section
variable {n : ℕ} [NeZero n]
private theorem siteOfInt_injOn_box {u v : Fin 4 → ℤ} {q : ℕ} (hu : OffsetInBox q u) (hv : OffsetInBox q v)
    (hq : 2 * q < n) (h : (siteOfInt u : TorusSite n) = siteOfInt v) : u = v := by
  funext i
  have h1 : ((u i : ℤ) : ZMod n) = ((v i : ℤ) : ZMod n) := congrFun h i
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have h3 : |v i - u i| < (n : ℤ) := by
    have a1 := abs_le.mp (hu i)
    have a2 := abs_le.mp (hv i)
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h2 h3
  omega
abbrev _root_.YangMills.SharedProofs.p64386 := @siteOfInt_injOn_box
private theorem isColdOn_trivialField {s : ℝ} (hs : 0 < s) (X : Finset (TorusSite n)) :
    IsColdOn s X (trivialField n) := by apply _root_.YangMills.SharedProofs.p25190 <;> assumption
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
end
section
variable {n k : ℕ} [NeZero n]
private def perturbedValue (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (u : Fin 4 → ℤ) (i : Fin 4) : UnitQuaternion :=
  open Classical in expUnit (∑ l, if c l = (u, i) then σ l • Xs l else 0)
private theorem perturb_trivialField_siteOfInt {c : Fin k → (Fin 4 → ℤ) × Fin 4} (Xs : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (z : TorusSite n) {q : ℕ} (hq : 2 * q < n) (hc : ∀ l, OffsetInBox q (c l).1)
    {u : Fin 4 → ℤ} (hu : OffsetInBox q u) (i : Fin 4) :
    perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n) (z + siteOfInt u) i = perturbedValue c Xs σ u i := by
  classical
  show expUnit (∑ l, if bondFrom z (c l) = (z + siteOfInt u, i) then σ l • Xs l else 0) * 1 = _
  rw [mul_one]
  unfold perturbedValue
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (u, i)
  · have : bondFrom z (c l) = (z + siteOfInt u, i) := by rw [h]; rfl
    rw [if_pos this, if_pos h]
  · have : ¬ bondFrom z (c l) = (z + siteOfInt u, i) := by
      intro he
      apply h
      have h1 : z + siteOfInt (c l).1 = z + siteOfInt u := congrArg Prod.fst he
      have h2 : (c l).2 = i := congrArg Prod.snd he
      exact Prod.ext (siteOfInt_injOn_box (hc l) hu hq (add_left_cancel h1)) h2
    rw [if_neg this, if_neg h]
private theorem perturb_trivialField_of_ne {c : Fin k → TorusBond n} (Xs : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) {x : TorusSite n} {i : Fin 4} (h : ∀ l, c l ≠ (x, i)) :
    perturb c Xs σ (trivialField n) x i = 1 := by
  classical
  show expUnit (∑ l, if c l = (x, i) then σ l • Xs l else 0) * 1 = 1
  simp only [h, if_false, Finset.sum_const_zero, mul_one]
  exact expUnit_zero
private def offsetPlaquetteEnergy (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (h : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  1 - ((perturbedValue c Xs σ h μ * perturbedValue c Xs σ (h + Pi.single μ 1) ν *
    (perturbedValue c Xs σ (h + Pi.single ν 1) μ)⁻¹ * (perturbedValue c Xs σ h ν)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re
private theorem siteOfInt_add_unitStep (z : TorusSite n) (h : Fin 4 → ℤ) (μ : Fin 4) :
    z + siteOfInt h + unitStep n μ = z + siteOfInt (h + Pi.single μ 1) := by apply _root_.YangMills.Construction.AbelianSecondOrder.add_siteOfInt_unitStep <;> assumption
private theorem plaquetteEnergy_perturb_siteOfInt {c : Fin k → (Fin 4 → ℤ) × Fin 4}
    (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) (z : TorusSite n) {q : ℕ} (hq : 2 * q < n)
    (hc : ∀ l, OffsetInBox q (c l).1) {h : Fin 4 → ℤ} (hh : OffsetInBox (q - 1) h) (hq1 : 1 ≤ q) (μ ν : Fin 4) :
    plaquetteEnergy (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n)) (z + siteOfInt h) μ ν =
      offsetPlaquetteEnergy c Xs σ h μ ν := by
  have h0 : OffsetInBox q h := fun i => (hh i).trans (by omega)
  have h1 : ∀ μ : Fin 4, OffsetInBox q (h + Pi.single μ 1) := by
    intro μ i
    have a := abs_le.mp (hh i)
    by_cases hi : i = μ
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [abs_le]
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
      exact h0 i
  unfold plaquetteEnergy holonomy offsetPlaquetteEnergy
  rw [siteOfInt_add_unitStep, siteOfInt_add_unitStep, perturb_trivialField_siteOfInt Xs σ z hq hc h0,
    perturb_trivialField_siteOfInt Xs σ z hq hc (h1 μ), perturb_trivialField_siteOfInt Xs σ z hq hc (h1 ν),
    perturb_trivialField_siteOfInt Xs σ z hq hc h0]
private def cornerOffsets (h : Fin 4 → ℤ) (μ ν : Fin 4) : List (Fin 4 → ℤ) :=
  [h, h + Pi.single μ 1, h + Pi.single ν 1, h + Pi.single μ 1 + Pi.single ν 1]
private theorem mem_plaquetteVertices_iff_offsets (z : TorusSite n) (h : Fin 4 → ℤ) (μ ν : Fin 4) {w : TorusSite n} :
    w ∈ plaquetteVertices (z + siteOfInt h) μ ν ↔ ∃ u ∈ cornerOffsets h μ ν, w = z + siteOfInt u := by
  simp only [plaquetteVertices, cornerOffsets, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  rw [siteOfInt_add_unitStep, siteOfInt_add_unitStep, siteOfInt_add_unitStep]
private theorem cornerOffsets_inBox {h : Fin 4 → ℤ} {q : ℕ} (hh : OffsetInBox q h) (μ ν : Fin 4) {u : Fin 4 → ℤ}
    (hu : u ∈ cornerOffsets h μ ν) : OffsetInBox (q + 2) u := by
  have key : ∀ (e : Fin 4 → ℤ) (p : ℕ) (μ : Fin 4), OffsetInBox p e → OffsetInBox (p + 1) (e + Pi.single μ 1) := by
    intro e p μ he i
    have a := abs_le.mp (he i)
    by_cases hi : i = μ
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [abs_le]
      push_cast
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
      rw [abs_le]
      push_cast
      constructor <;> omega
  have mono : ∀ {e : Fin 4 → ℤ} {p p' : ℕ}, p ≤ p' → OffsetInBox p e → OffsetInBox p' e := by
    intro e p p' hp he i
    exact (he i).trans (by exact_mod_cast hp)
  simp only [cornerOffsets, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact mono (by omega) hh
  · exact mono (by omega) (key _ _ _ hh)
  · exact mono (by omega) (key _ _ _ hh)
  · exact key _ _ _ (key _ _ _ hh)
abbrev _root_.YangMills.DeltaSharedProofs.p501882 := @cornerOffsets_inBox
open Classical in
private def nearOffsetPlaquettes (q : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(q : ℤ)) (q : ℤ)) ×ˢ
    (Finset.univ : Finset (Fin 4 × Fin 4))).filter fun τ => τ.2.1 < τ.2.2
private theorem mem_nearOffsetPlaquettes {q : ℕ} {τ : (Fin 4 → ℤ) × Fin 4 × Fin 4} :
    τ ∈ nearOffsetPlaquettes q ↔ OffsetInBox q τ.1 ∧ τ.2.1 < τ.2.2 := by
  classical
  simp only [nearOffsetPlaquettes, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc,
    Finset.mem_univ, and_true, OffsetInBox, abs_le]
abbrev _root_.YangMills.DeltaSharedProofs.p502338 := @mem_nearOffsetPlaquettes
private theorem mem_plaquettesIn {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ w ∈ plaquetteVertices p.1 p.2.1 p.2.2, w ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
open Classical in
private theorem wilsonAction_perturb_eq_sum {c : Fin k → (Fin 4 → ℤ) × Fin 4} (Xs : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (X : Finset (TorusSite n)) (z : TorusSite n) {r : ℕ} (hc : ∀ l, OffsetInBox r (c l).1)
    (hn : 2 * (r + 2) < n) :
    wilsonAction X (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n)) =
      ∑ τ ∈ nearOffsetPlaquettes (r + 1), if ∀ u ∈ cornerOffsets τ.1 τ.2.1 τ.2.2, z + siteOfInt u ∈ X then
        offsetPlaquetteEnergy c Xs σ τ.1 τ.2.1 τ.2.2 else 0 := by
  set W := perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n) with hW
  have hcq : ∀ l, OffsetInBox (r + 2) (c l).1 := fun l i => (hc l i).trans (by push_cast; omega)
  rw [← Finset.sum_filter]
  set T := (nearOffsetPlaquettes (r + 1)).filter fun τ => ∀ u ∈ cornerOffsets τ.1 τ.2.1 τ.2.2, z + siteOfInt u ∈ X
    with hT
  set ι : (Fin 4 → ℤ) × Fin 4 × Fin 4 → TorusPlaquette n := fun τ => (z + siteOfInt τ.1, τ.2.1, τ.2.2) with hι
  have hbox : ∀ τ ∈ T, OffsetInBox (r + 1) τ.1 := fun τ hτ =>
    (mem_nearOffsetPlaquettes.mp (Finset.mem_filter.mp hτ).1).1
  have hinj : Set.InjOn ι T := by
    rintro ⟨h, μ, ν⟩ h1 ⟨h', μ', ν'⟩ h2 he
    have e1 : z + siteOfInt h = z + siteOfInt h' := congrArg Prod.fst he
    have e2 : (μ, ν) = (μ', ν') := congrArg Prod.snd he
    have e3 : h = h' := siteOfInt_injOn_box (q := r + 2) (fun i => ((hbox _ h1) i).trans (by push_cast; omega))
      (fun i => ((hbox _ h2) i).trans (by push_cast; omega)) hn (add_left_cancel e1)
    rw [e3, e2]
  have hE : ∀ τ ∈ T, plaquetteEnergy W (ι τ).1 (ι τ).2.1 (ι τ).2.2 = offsetPlaquetteEnergy c Xs σ τ.1 τ.2.1 τ.2.2 := by
    intro τ hτ
    exact plaquetteEnergy_perturb_siteOfInt Xs σ z hn hcq (by simpa using hbox τ hτ) (by omega) _ _
  have hsub : T.image ι ⊆ plaquettesIn X := by
    intro p hp
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hp
    have h1 := Finset.mem_filter.mp hτ
    refine mem_plaquettesIn.mpr ⟨(mem_nearOffsetPlaquettes.mp h1.1).2, fun w hw => ?_⟩
    obtain ⟨u, hu, rfl⟩ := (mem_plaquetteVertices_iff_offsets z τ.1 τ.2.1 τ.2.2).mp hw
    exact h1.2 u hu
  have hzero : ∀ p ∈ plaquettesIn X, p ∉ T.image ι → plaquetteEnergy W p.1 p.2.1 p.2.2 = 0 := by
    rintro ⟨x, μ, ν⟩ hp hnot
    by_contra hne
    have hlt : μ < ν := (mem_plaquettesIn.mp hp).1
    have hex : ∃ h : Fin 4 → ℤ, OffsetInBox (r + 1) h ∧ x = z + siteOfInt h := by
      by_contra hno
      push_neg at hno
      apply hne
      have off : ∀ (y : TorusSite n) (i : Fin 4), (∀ l, bondFrom z (c l) ≠ (y, i)) → W y i = 1 := fun y i h =>
        perturb_trivialField_of_ne Xs σ h
      have key : ∀ e : Fin 4 → ℤ, OffsetInBox 1 e → ∀ l i, bondFrom z (c l) ≠ (x + siteOfInt e, i) := by
        intro e he l i hb
        have h1 : z + siteOfInt (c l).1 = x + siteOfInt e := congrArg Prod.fst hb
        refine hno ((c l).1 - e) (fun j => ?_) ?_
        · have a1 := abs_le.mp (hc l j)
          have a2 := abs_le.mp (he j)
          simp only [Pi.sub_apply]
          rw [abs_le]
          push_cast at a1 a2 ⊢
          constructor <;> omega
        · have : (c l).1 = ((c l).1 - e) + e := by abel
          rw [this, siteOfInt_add, ← add_assoc] at h1
          exact (add_right_cancel h1).symm
      have z0 : (x : TorusSite n) = x + siteOfInt 0 := by
        funext i
        simp [siteOfInt]
      have b0 : OffsetInBox 1 (0 : Fin 4 → ℤ) := fun i => by simp
      have b1 : ∀ μ : Fin 4, OffsetInBox 1 (Pi.single μ 1 : Fin 4 → ℤ) := by
        intro μ i
        by_cases hi : i = μ
        · subst hi
          simp
        · simp [Pi.single_eq_of_ne hi]
      have o1 : W x μ = 1 := off _ _ fun l => by
        have := key 0 b0 l μ
        rwa [← z0] at this
      have o4 : W x ν = 1 := off _ _ fun l => by
        have := key 0 b0 l ν
        rwa [← z0] at this
      have o2 : W (x + unitStep n μ) ν = 1 := off _ _ fun l => by
        have := key _ (b1 μ) l ν
        rwa [siteOfInt_single] at this
      have o3 : W (x + unitStep n ν) μ = 1 := off _ _ fun l => by
        have := key _ (b1 ν) l μ
        rwa [siteOfInt_single] at this
      simp [plaquetteEnergy, holonomy, o1, o2, o3, o4]
    obtain ⟨h, hh, rfl⟩ := hex
    apply hnot
    refine Finset.mem_image.mpr ⟨(h, μ, ν), Finset.mem_filter.mpr ⟨mem_nearOffsetPlaquettes.mpr ⟨hh, hlt⟩,
      fun u hu => ?_⟩, rfl⟩
    exact (mem_plaquettesIn.mp hp).2 _ ((mem_plaquetteVertices_iff_offsets z h μ ν).mpr ⟨u, hu, rfl⟩)
  unfold wilsonAction
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  exact Finset.sum_congr rfl hE
private theorem mixedDeriv_levelZero_eq {n n' k : ℕ} [NeZero n] [NeZero n'] (a : ℝ) (L : ℕ)
    {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} {z : TorusSite n} {z' : TorusSite n'} {m r : ℕ}
    (hn : 64 ≤ n) (hm : 4 * m + 2 < n) (hm' : 4 * m + 2 < n') (hr : 4 * r + 4 ≤ m)
    (hXX : ∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X'))
    {c : Fin k → (Fin 4 → ℤ) × Fin 4} (Xs : Fin k → imaginaryQuaternions) (hc : ∀ l, OffsetInBox r (c l).1) :
    mixedDeriv (actionAtLevel a L 0 X) (trivialField n) (fun l => bondFrom z (c l)) Xs =
      mixedDeriv (actionAtLevel a L 0 X') (trivialField n') (fun l => bondFrom z' (c l)) Xs := by
  classical
  unfold mixedDeriv
  have hf : (fun σ : Fin k → ℝ => actionAtLevel a L 0 X (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n))) =
      fun σ => actionAtLevel a L 0 X' (perturb (fun l => bondFrom z' (c l)) Xs σ (trivialField n')) := by
    funext σ
    show wilsonAction X _ = wilsonAction X' _
    rw [wilsonAction_perturb_eq_sum Xs σ X z hc (by omega), wilsonAction_perturb_eq_sum Xs σ X' z' hc (by omega)]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    have hb := (mem_nearOffsetPlaquettes.mp hτ).1
    have hiff : (∀ u ∈ cornerOffsets τ.1 τ.2.1 τ.2.2, z + siteOfInt u ∈ X) ↔
        ∀ u ∈ cornerOffsets τ.1 τ.2.1 τ.2.2, z' + siteOfInt u ∈ X' :=
      forall₂_congr fun u hu => hXX u fun i => ((cornerOffsets_inBox hb _ _ hu) i).trans (by push_cast; omega)
    by_cases h : ∀ u ∈ cornerOffsets τ.1 τ.2.1 τ.2.2, z + siteOfInt u ∈ X
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  rw [hf]
end
section
private theorem period_torusFrame_top (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
private theorem period_torusFrame_neZero (L t n : ℕ) [NeZero L] [NeZero n] (j : ℕ) (i : Fin 4) :
    NeZero ((torusFrame L t n).period j i) := by apply _root_.YangMills.Construction.LevelAction.torusFrame_period_neZero <;> assumption
private theorem levelSucc_properties {n : ℕ} [NeZero n] (hSA : SharesSumToAction) {a δ lam ρ σA cg : ℝ} {L : ℕ}
    {N : ℕ → ℝ} (ha : 0 < a) (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n)
    {X : Finset (TorusSite n)} (hreg : IsRegularRegion X 1024) :
    (actionAtLevel a L (t + 1) X = fun W'' => ∑ y, levelShare a L (t + 1) X y W'') ∧
    (∀ y, ContDiffThreeAt (levelShare a L (t + 1) X y) (trivialField n)) ∧
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (l₀ : Fin k) (y : TorusSite n),
      1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
      |mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) c Xs| ≤
        (N 1 + N 2 + N 3) * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y (c l₀).1) := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  haveI : NeZero L := ⟨hL.pos.ne'⟩
  haveI hinst : ∀ j i, NeZero ((torusFrame L t n).period j i) := fun j i => period_torusFrame_neZero L t n j i
  have hp := period_torusFrame_top L t n
  have hamb : IsAdmissibleAmbient (torusFrame L t n) := Or.inr fun _ => hn
  have hreg' : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 :=
    isOrthantRegular_of_isRegularRegion hp hreg
  have hcold' := isCold_of_isColdOn (F := torusFrame L t n) hp (isColdOn_trivialField hσ X)
  obtain ⟨-, -, H3, -⟩ := hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) X) rfl hamb le_rfl hreg' σA _ hσ
    le_rfl hcold'
  obtain ⟨hAn, hSn, -, hG, -, hTot, hShare, -, -⟩ := H3
  have hNk : ∀ k, 1 ≤ k → k ≤ 3 → N k ≤ N 1 + N 2 + N 3 := by
    intro k a1 a2
    have n1 := hN 1
    have n2 := hN 2
    have n3 := hN 3
    interval_cases k <;> linarith
  have hsum : actionAtLevel a L (t + 1) X = fun W'' => ∑ y, levelShare a L (t + 1) X y W'' := by
    funext W''
    exact (hSA a L t n X W'' ha.le hL.pos (by omega)).symm
  refine ⟨hsum, fun y => contDiffThreeAt_of_isBondAnalyticAt hp (hSn _), ?_⟩
  intro k c Xs l₀ y a1 a2 a3
  have e : mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) c Xs =
      mixedBondDerivative
        (minimalCellShare a (cellsOfSites (torusFrame L t n) X) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n))
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) Xs :=
    mixedDeriv_readAtLevel hp
      (minimalCellShare a (cellsOfSites (torusFrame L t n) X) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y))
      (trivialField n) c Xs
  rw [e]
  refine (hShare _ k _ Xs a1 a3).trans ?_
  have hd : (_root_.YangMills.Construction.TorusFields.supDist y (c l₀).1 : ℝ) ≤
      (bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) : ℝ) := by
    have h2 : cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l₀).1) ≤
        bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) :=
      Finset.le_sup (f := fun l : Fin k => cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1)) (Finset.mem_univ l₀)
    rw [cellSupDist_torusSiteInFrame hp] at h2
    exact_mod_cast h2
  have he : Real.exp (-δ * (bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) : ℝ)) ≤
      Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y (c l₀).1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul (hNk k a1 a2) he (Real.exp_pos _).le (by have := hN 1; have := hN 2; have := hN 3; linarith)
abbrev _root_.YangMills.SharedProofs.p19727 := @levelSucc_properties
private theorem offsetInBox_mono {e : Fin 4 → ℤ} {p p' : ℕ} (hp : p ≤ p') (he : OffsetInBox p e) :
    OffsetInBox p' e :=
  fun i => (he i).trans (by exact_mod_cast hp)
private theorem offsetInBox_add {e e' : Fin 4 → ℤ} {p p' : ℕ} (he : OffsetInBox p e) (he' : OffsetInBox p' e') :
    OffsetInBox (p + p') (e + e') := by apply _root_.YangMills.SharedProofs.p43430 <;> assumption
private theorem offsetInBox_sub {e e' : Fin 4 → ℤ} {p p' : ℕ} (he : OffsetInBox p e) (he' : OffsetInBox p' e') :
    OffsetInBox (p + p') (e - e') := by
  intro i
  have a := abs_le.mp (he i)
  have b := abs_le.mp (he' i)
  simp only [Pi.sub_apply]
  rw [abs_le]
  push_cast
  constructor <;> omega
private theorem offsetInBox_single (μ : Fin 4) : OffsetInBox 1 (Pi.single μ 1 : Fin 4 → ℤ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.offsetInBox_single <;> assumption
private theorem mixedDeriv_levelShare_near {n n' : ℕ} [NeZero n] [NeZero n'] {a δ lam ρ σA cg : ℝ} {L : ℕ}
    {N : ℕ → ℝ} (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n) (hn' : 64 ≤ n')
    {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} (hreg : IsRegularRegion X 1024)
    (hreg' : IsRegularRegion X' 1024) {z : TorusSite n} {z' : TorusSite n'} {m r : ℕ} (hm : 2 * m + 2 < n)
    (hm' : 2 * m + 2 < n') (hr : 4 * r + 4 ≤ m)
    (hXX : ∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X'))
    (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions) (hk : k ≤ 2) (hk1 : 1 ≤ k)
    (hX : AreUnitVectors Xs) (hcz : ∀ l, OffsetInBox r (c l).1) (u : Fin 4 → ℤ) (hu : OffsetInBox (m / 2) u) :
    |mixedDeriv (levelShare a L (t + 1) X (z + siteOfInt u)) (trivialField n) (fun l => bondFrom z (c l)) Xs -
      mixedDeriv (levelShare a L (t + 1) X' (z' + siteOfInt u)) (trivialField n') (fun l => bondFrom z' (c l)) Xs| ≤
      (1 + σA) * (N 1 + N 2 + N 3) * Real.exp (-δ * m) := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  haveI : NeZero L := ⟨hL.pos.ne'⟩
  haveI hinst : ∀ j i, NeZero ((torusFrame L t n).period j i) := fun j i => period_torusFrame_neZero L t n j i
  haveI hinst' : ∀ j i, NeZero ((torusFrame L t n').period j i) := fun j i => period_torusFrame_neZero L t n' j i
  have hp := period_torusFrame_top L t n
  have hp' := period_torusFrame_top L t n'
  have hamb : IsAdmissibleAmbient (torusFrame L t n) := Or.inr fun _ => hn
  have hamb' : IsAdmissibleAmbient (torusFrame L t n') := Or.inr fun _ => hn'
  have hR : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 := isOrthantRegular_of_isRegularRegion hp hreg
  have hR' : IsOrthantRegular (cellsOfSites (torusFrame L t n') X') 1024 :=
    isOrthantRegular_of_isRegularRegion hp' hreg'
  have hC := isCold_of_isColdOn (F := torusFrame L t n) hp (isColdOn_trivialField hσ X)
  have hC' := isCold_of_isColdOn (F := torusFrame L t n') hp' (isColdOn_trivialField hσ X')
  obtain ⟨-, -, -, -, -, H⟩ := hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) X) rfl hamb le_rfl hR σA _
    hσ le_rfl hC
  set y := z + siteOfInt u with hy
  set y' := z' + siteOfInt u with hy'
  set Y := torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y with hYdef
  set Y' := torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top y' with hYdef'
  have hshift : ∀ h : Fin 4 → ℤ, Y + siteOfCoords (torusFrame L t n).top h =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (y + siteOfInt h) := by
    intro h
    rw [torusSiteInFrame_add hp, torusSiteInFrame_siteOfInt hp]
  have hshift' : ∀ h : Fin 4 → ℤ, Y' + siteOfCoords (torusFrame L t n').top h =
      torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top (y' + siteOfInt h) := by
    intro h
    rw [torusSiteInFrame_add hp', torusSiteInFrame_siteOfInt hp']
  have hagree : AgreeOnBall (cellsOfSites (torusFrame L t n) X)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n))
      (cellsOfSites (torusFrame L t n') X') (readAtLevel (torusFrame L t n') (torusFrame L t n').top (trivialField n'))
      Y Y' m := by
    refine ⟨fun _ => Or.inr hm, fun _ => Or.inr hm', fun h hh => ?_, fun b hb => rfl⟩
    rw [hshift, hshift', mem_cellsOfSites_iff hp, mem_cellsOfSites_iff hp', toTorusSite_torusSiteInFrame hp,
      toTorusSite_torusSiteInFrame hp', hy, hy', add_assoc, add_assoc, ← siteOfInt_add, ← siteOfInt_add]
    exact hXX _ (offsetInBox_mono (by omega) (offsetInBox_add hu hh))
  have HL := (H (torusFrame L t n') (cellsOfSites (torusFrame L t n') X') _ Y Y' m rfl rfl hamb' hR' hC' hagree).1
  set e : Fin k → (Fin 4 → ℤ) × Fin 4 := fun l => ((c l).1 - u, (c l).2) with he
  have hoffn : ∀ l, (siteOfInt (c l).1 : TorusSite n) = siteOfInt u + siteOfInt (e l).1 := by
    intro l
    rw [← siteOfInt_add]
    congr 1
    simp [he]
  have hoffn' : ∀ l, (siteOfInt (c l).1 : TorusSite n') = siteOfInt u + siteOfInt (e l).1 := by
    intro l
    rw [← siteOfInt_add]
    congr 1
    simp [he]
  have hbonds : offsetBonds Y e = fun l =>
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (bondFrom z (c l)).1, (bondFrom z (c l)).2) := by
    funext l
    refine Prod.ext ?_ rfl
    show Y + siteOfCoords (torusFrame L t n).top (e l).1 =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (z + siteOfInt (c l).1)
    rw [hshift, hy, add_assoc, ← hoffn l]
  have hbonds' : offsetBonds Y' e = fun l =>
      (torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top (bondFrom z' (c l)).1, (bondFrom z' (c l)).2) := by
    funext l
    refine Prod.ext ?_ rfl
    show Y' + siteOfCoords (torusFrame L t n').top (e l).1 =
      torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top (z' + siteOfInt (c l).1)
    rw [hshift', hy', add_assoc, ← hoffn' l]
  have hbox : ∀ l, BondWithinRadius m (e l) := by
    intro l
    have h1 : OffsetInBox (r + m / 2) (e l).1 := offsetInBox_sub (hcz l) hu
    refine ⟨offsetInBox_mono (by omega) h1, ?_⟩
    exact offsetInBox_mono (by omega) (offsetInBox_add h1 (offsetInBox_single (c l).2))
  have hfin := HL k e Xs hbox hX
  rw [hbonds, hbonds'] at hfin
  have e1 : mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) (fun l => bondFrom z (c l)) Xs =
      mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n) X) Y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n))
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (bondFrom z (c l)).1,
          (bondFrom z (c l)).2)) Xs :=
    mixedDeriv_readAtLevel hp (minimalCellShare a (cellsOfSites (torusFrame L t n) X) Y) (trivialField n) _ Xs
  have e2 : mixedDeriv (levelShare a L (t + 1) X' y') (trivialField n') (fun l => bondFrom z' (c l)) Xs =
      mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n') X') Y')
        (readAtLevel (torusFrame L t n') (torusFrame L t n').top (trivialField n'))
        (fun l => (torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top (bondFrom z' (c l)).1,
          (bondFrom z' (c l)).2)) Xs :=
    mixedDeriv_readAtLevel hp' (minimalCellShare a (cellsOfSites (torusFrame L t n') X') Y') (trivialField n') _ Xs
  rw [e1, e2]
  refine hfin.trans ?_
  have hcf : derivativeScale σA k ≤ 1 + σA := by
    unfold derivativeScale
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0]
    split_ifs <;> linarith
  have hNk : N k ≤ N 1 + N 2 + N 3 := by
    have n1 := hN 1
    have n2 := hN 2
    have n3 := hN 3
    interval_cases k <;> linarith
  have hNk0 : 0 ≤ N k := (hN k).le
  have h1 : derivativeScale σA k * N k ≤ (1 + σA) * (N 1 + N 2 + N 3) :=
    mul_le_mul hcf hNk hNk0 (by linarith)
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
abbrev _root_.YangMills.SharedProofs.p46974 := @mixedDeriv_levelShare_near
end
section
variable {n n' : ℕ} [NeZero n] [NeZero n']
private theorem mixedDeriv_sum {k : ℕ} {sh : TorusSite n → TorusField n → ℝ} {W : TorusField n}
    (hs : ∀ y, ContDiffThreeAt (sh y) W) (hk : k ≤ 3) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W'' => ∑ y, sh y W'') W c Xs = ∑ y, mixedDeriv (sh y) W c Xs := by
  unfold mixedDeriv
  have hc : ∀ y ∈ (Finset.univ : Finset (TorusSite n)),
      ContDiffAt ℝ k (fun σ : Fin k → ℝ => sh y (perturb c Xs σ W)) 0 := fun y _ =>
    (hs y k c Xs).of_le (by exact_mod_cast hk)
  rw [iteratedFDeriv_fun_sum_apply hc, ContinuousMultilinearMap.sum_apply]
abbrev _root_.YangMills.SharedProofs.p19279 := @mixedDeriv_sum
private def offsetBox (q : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) (q : ℤ)
private theorem mem_offsetBox {q : ℕ} {u : Fin 4 → ℤ} : u ∈ offsetBox q ↔ OffsetInBox q u := by
  simp only [offsetBox, Fintype.mem_piFinset, Finset.mem_Icc, OffsetInBox, abs_le]
private theorem card_offsetBox (q : ℕ) : (offsetBox q).card = (2 * q + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
private theorem sum_eq_offsetBox_add_far (f : TorusSite n → ℝ) (z : TorusSite n) (q : ℕ) (hq : 2 * q < n) :
    ∑ y, f y = ∑ u ∈ offsetBox q, f (z + siteOfInt u) +
      ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => q < _root_.YangMills.Construction.TorusFields.supDist y z), f y := by
  classical
  have himg : (Finset.univ.filter fun y : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist y z ≤ q) =
      (offsetBox q).image fun u => z + siteOfInt u := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      obtain ⟨e, he, hb⟩ := exists_offset_of_supDist z y
      refine ⟨e, mem_offsetBox.mpr fun i => ?_, he.symm⟩
      have h1 := hb i
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
      rw [Int.abs_eq_natAbs]
      omega
    · rintro ⟨u, hu, rfl⟩
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le z u q fun i => ?_
      have := mem_offsetBox.mp hu i
      rw [Int.abs_eq_natAbs] at this
      omega
  have hinj : Set.InjOn (fun u : Fin 4 → ℤ => (z + siteOfInt u : TorusSite n)) (offsetBox q) := by
    intro u hu v hv he
    exact siteOfInt_injOn_box (mem_offsetBox.mp hu) (mem_offsetBox.mp hv) hq (add_left_cancel he)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist y z ≤ q), himg,
    Finset.sum_image hinj]
  simp only [not_le]
private def farConstant (δ : ℝ) : ℝ := (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4
private theorem farConstant_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ farConstant δ := by
  unfold farConstant
  have h : Real.exp (-(δ / 4) / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have : 0 < 1 - Real.exp (-(δ / 4) / 4) := by linarith
  positivity
private theorem abs_sum_far_le {f : TorusSite n → ℝ} {z : TorusSite n} {m : ℕ} {D δ : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hfar : ∀ y, m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z → |f y| ≤ D * Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist y z)) :
    |∑ y ∈ Finset.univ.filter (fun y : TorusSite n => m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z), f y| ≤
      D * farConstant δ * Real.exp (-δ * m / 8) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n => m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z),
      |f y| ≤ D * Real.exp (-δ * m / 8) * Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist y z) := by
    intro y hy
    have hm := (Finset.mem_filter.mp hy).2
    refine (hfar y hm).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
    have : (m : ℝ) ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y z := by
      have : m ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y z := by omega
      exact_mod_cast this
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hs := sum_exp_neg_mul_supDist_le (n := n) (show 0 < δ / 4 by linarith) z
  have hsub : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z),
      Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist y z) ≤ ∑ y : TorusSite n, Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist y z) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
  have h0 : 0 ≤ D * Real.exp (-δ * m / 8) := by positivity
  calc _ ≤ D * Real.exp (-δ * m / 8) * farConstant δ := mul_le_mul_of_nonneg_left (hsub.trans hs) h0
    _ = _ := by ring
private theorem abs_sum_sub_sum_le {f : TorusSite n → ℝ} {g : TorusSite n' → ℝ} {z : TorusSite n}
    {z' : TorusSite n'} {m : ℕ} {e D δ : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) (he : 0 ≤ e) (hq : 2 * (m / 2) < n)
    (hq' : 2 * (m / 2) < n')
    (hnear : ∀ u, OffsetInBox (m / 2) u → |f (z + siteOfInt u) - g (z' + siteOfInt u)| ≤ e)
    (hfar : ∀ y, m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z → |f y| ≤ D * Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist y z))
    (hfar' : ∀ y, m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z' → |g y| ≤ D * Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist y z')) :
    |∑ y, f y - ∑ y, g y| ≤ ((m : ℝ) + 1) ^ 4 * e + 2 * (D * farConstant δ * Real.exp (-δ * m / 8)) := by
  rw [sum_eq_offsetBox_add_far f z (m / 2) hq, sum_eq_offsetBox_add_far g z' (m / 2) hq']
  set A := ∑ u ∈ offsetBox (m / 2), f (z + siteOfInt u)
  set A' := ∑ u ∈ offsetBox (m / 2), g (z' + siteOfInt u)
  set B := ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z), f y with hB
  set B' := ∑ y ∈ Finset.univ.filter (fun y : TorusSite n' => m / 2 < _root_.YangMills.Construction.TorusFields.supDist y z'), g y with hB'
  have h1 : |A - A'| ≤ ((m : ℝ) + 1) ^ 4 * e := by
    show |∑ u ∈ offsetBox (m / 2), f (z + siteOfInt u) - ∑ u ∈ offsetBox (m / 2), g (z' + siteOfInt u)| ≤ _
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ e fun u hu => hnear u (mem_offsetBox.mp hu)).trans ?_
    rw [nsmul_eq_mul, card_offsetBox]
    refine mul_le_mul_of_nonneg_right ?_ he
    push_cast
    have h4 : ((2 * (m / 2) : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (by omega : 2 * (m / 2) ≤ m)
    push_cast at h4
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have h2 := abs_sum_far_le hδ hD hfar
  have h3 := abs_sum_far_le hδ hD hfar'
  rw [← hB] at h2
  rw [← hB'] at h3
  have e1 : A + B - (A' + B') = (A - A') + B - B' := by ring
  rw [e1]
  calc |A - A' + B - B'| ≤ |A - A' + B| + |B'| := abs_sub _ _
    _ ≤ |A - A'| + |B| + |B'| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith
end
theorem flatActionDerivativesAgree_holds (hSA : SharesSumToAction) : FlatActionDerivativesAgree := by
  intro a δ L lam ρ σA cg N ha hL hc
  have hc0 := hc
  obtain ⟨hδ, hδ8, -, -, -, hσ, -, hN, -⟩ := hc
  have hN1 := hN 1
  have hN2 := hN 2
  have hN3 := hN 3
  set D := N 1 + N 2 + N 3 with hDdef
  have hD : 0 ≤ D := by positivity
  have hK := farConstant_nonneg hδ
  set C := 1 + (1 + σA) * D + 2 * (D * farConstant δ) with hCdef
  have hCpos : 0 < C := by positivity
  refine ⟨C, hCpos, fun t n n' _ _ X X' z z' m r hn hn' hreg hreg' hm hm' hr hXX k c Xs hk1 hk hX hcz => ?_⟩
  cases t with
  | zero =>
    rw [mixedDeriv_levelZero_eq a L hn hm hm' hr hXX Xs hcz, sub_self, abs_zero]
    positivity
  | succ t =>
    obtain ⟨s1, s2, s3⟩ := levelSucc_properties hSA ha hL hc0 t hn hreg (N := N)
    obtain ⟨s1', s2', s3'⟩ := levelSucc_properties hSA ha hL hc0 t hn' hreg' (N := N)
    rw [s1, s1', mixedDeriv_sum s2 (by omega), mixedDeriv_sum s2' (by omega)]
    set l₀ : Fin k := ⟨0, hk1⟩
    have hfar : ∀ {p : ℕ} [NeZero p] {Y : Finset (TorusSite p)} (w : TorusSite p),
        (∀ (k : ℕ) (c : Fin k → TorusBond p) (Xs : Fin k → imaginaryQuaternions) (l₀ : Fin k) (y : TorusSite p),
          1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
          |mixedDeriv (levelShare a L (t + 1) Y y) (trivialField p) c Xs| ≤ D * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist y (c l₀).1)) →
        ∀ y, m / 2 < _root_.YangMills.Construction.TorusFields.supDist y w →
          |mixedDeriv (levelShare a L (t + 1) Y y) (trivialField p) (fun l => bondFrom w (c l)) Xs| ≤
            D * Real.exp (-(δ / 2) * _root_.YangMills.Construction.TorusFields.supDist y w) := by
      intro p _ Y w h3 y hy
      refine (h3 k _ Xs l₀ y hk1 (by omega) hX).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
      have h1 : _root_.YangMills.Construction.TorusFields.supDist w (w + siteOfInt (c l₀).1) ≤ r := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le w _ r fun i => by
        have := hcz l₀ i
        rw [Int.abs_eq_natAbs] at this
        omega
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y (w + siteOfInt (c l₀).1) w
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm (w + siteOfInt (c l₀).1) w] at h2
      have h4 : (_root_.YangMills.Construction.TorusFields.supDist y w : ℝ) ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y (bondFrom w (c l₀)).1 := by
        have : _root_.YangMills.Construction.TorusFields.supDist y w ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y (bondFrom w (c l₀)).1 := by
          show _root_.YangMills.Construction.TorusFields.supDist y w ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y (w + siteOfInt (c l₀).1)
          omega
        exact_mod_cast this
      nlinarith
    have hres := abs_sum_sub_sum_le (e := (1 + σA) * D * Real.exp (-δ * m)) hδ hD (by positivity) (by omega)
      (by omega)
      (fun u hu => mixedDeriv_levelShare_near hL hc0 t hn hn' hreg hreg' (by omega) (by omega) hr hXX k c Xs hk hk1 hX
        hcz u hu)
      (hfar z s3) (hfar z' s3')
    refine hres.trans ?_
    have he1 : Real.exp (-δ * m) ≤ Real.exp (-δ * m / 8) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ δ * m := by positivity
      nlinarith
    have hp1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := one_le_pow₀ (by
      have : (0 : ℝ) ≤ m := by positivity
      linarith)
    set P := ((m : ℝ) + 1) ^ 4
    set e8 := Real.exp (-δ * m / 8)
    have he8 : 0 < e8 := Real.exp_pos _
    have hDs : 0 ≤ (1 + σA) * D := by positivity
    have t1 : P * ((1 + σA) * D * Real.exp (-δ * m)) ≤ P * ((1 + σA) * D * e8) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he1 hDs) (by positivity)
    have t2 : 2 * (D * farConstant δ * e8) ≤ 2 * (D * farConstant δ) * P * e8 := by
      have : 0 ≤ 2 * (D * farConstant δ) * e8 := by positivity
      nlinarith
    have t3 : 0 ≤ P * e8 := by positivity
    rw [hCdef]
    nlinarith
end YangMills.Construction.TorusComparison
end
