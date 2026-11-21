import YangMills.Construction.CellOfTheFlow.HullsThatMeetCellsAreRareProof
import YangMills.Construction.FormsOnATorus.HotPlaquettesAtFarPlacesAreRare
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters StepSettings BlockAverages LumpContours FrameTransfer HaarBalls
  ColdFieldAction WeightedResponses StageDensity FieldMoves
section Membership
private theorem mem_torusHotSites {m : ℕ} {ℓ : StepParameters} {W : TorusField m} {z : TorusSite m} :
    z ∈ torusHotSites ℓ W ↔ ∃ l ∈ torusHotLumps ℓ W, z ∈ l := by
  simp only [torusHotSites, Finset.mem_biUnion, id_eq]
private theorem mem_plaquettesIn {m : ℕ} [NeZero m] {S : Finset (TorusSite m)} {p : TorusPlaquette m} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
end Membership
section CutAction
private abbrev levelFrame (L t m : ℕ) : BlockFrame := ⟨L, t, fun _ => m⟩
private theorem coercive_sum_le_actionAtLevel {Tb : ParameterAssignment} (hD : Tb.Admissible)
    (hAC : ActionAtLevelIsCutAction) (t m : ℕ)
    [NeZero m] [NeZero (m * Tb.side)] (hm : 64 ≤ m) (S : Finset (TorusSite (m * Tb.side)))
    (W : TorusField (m * Tb.side))
    (A : Finset (TorusPlaquette (m * Tb.side))) (hA : A ⊆ plaquettesIn S) :
    Tb.coercivity * ∑ p ∈ A, min (curvature W p.1 p.2.1 p.2.2 ^ 2) ((Tb.side : ℝ) ^ (-4 : ℤ)) ≤
      actionAtLevel Tb.coupling Tb.side t S W := by
  classical
  have hper : ∀ k, (levelFrame Tb.side t m).period t k = m * Tb.side := by
    intro k
    simp [BlockFrame.period, levelFrame]
  have hact : cutEffectiveAction Tb.coupling t (sitesOfTorus (levelFrame Tb.side t m) t S)
      (readAtLevel (levelFrame Tb.side t m) t W) =
      actionAtLevel Tb.coupling Tb.side t S W :=
    (hAC Tb.coupling (by linarith [hD.a_ge]) Tb.side hD.L_odd m (levelFrame Tb.side t m) rfl
      (fun _ => rfl)).2 S W
  have hco := (hD.coercive (levelFrame Tb.side t m) rfl (Or.inr fun _ => hm) t (Nat.le_succ t)).2
    (sitesOfTorus (levelFrame Tb.side t m) t S) (readAtLevel (levelFrame Tb.side t m) t W)
  rw [← hact]
  refine le_trans ?_ hco
  refine mul_le_mul_of_nonneg_left ?_ hD.cK_pos.le
  let f : TorusPlaquette (m * Tb.side) → (levelFrame Tb.side t m).Site t × Fin 4 × Fin 4 :=
    fun p => (torusToFrame (levelFrame Tb.side t m) t p.1, p.2.1, p.2.2)
  have hinj : Function.Injective f := by
    rintro ⟨x, a, b⟩ ⟨x', a', b'⟩ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h1, rfl, rfl⟩ := h
    rw [torusToFrame_injective hper h1]
  have hsub : A.image f ⊆ cutPlaquettes (sitesOfTorus (levelFrame Tb.side t m) t S) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (torusToFrame_mem_cutPlaquettes hper S p.1 p.2.1 p.2.2).mpr (hA hp)
  have hval : ∀ p : TorusPlaquette (m * Tb.side),
      plaquetteDefect (readAtLevel (levelFrame Tb.side t m) t W) (f p) =
      curvature W p.1 p.2.1 p.2.2 := by
    intro p
    unfold plaquetteDefect curvature
    rw [plaquetteHolonomy_readAtLevel hper]
  calc ∑ p ∈ A, min (curvature W p.1 p.2.1 p.2.2 ^ 2) ((Tb.side : ℝ) ^ (-4 : ℤ))
      = ∑ q ∈ A.image f, min (plaquetteDefect (readAtLevel (levelFrame Tb.side t m) t W) q ^ 2)
          ((Tb.side : ℝ) ^ (-4 : ℤ)) := by
        rw [Finset.sum_image fun a _ b _ h => hinj h]
        exact Finset.sum_congr rfl fun p _ => by rw [hval]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
        le_min (sq_nonneg _) (by positivity)
end CutAction
section HotLumps
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
open Classical in
private theorem card_le_card_far_add_card_hot (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (W : TorusField n) {ι : Type} [Fintype ι] (P : ι → TorusPlaquette n)
    (hfar : ∀ i i', i ≠ i' → ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      ∀ z' ∈ plaquetteVertices (P i').1 (P i').2.1 (P i').2.2, 2 ^ 17 ≤ _root_.YangMills.Construction.TorusFields.supDist z z') :
    Fintype.card ι ≤ (Finset.univ.filter fun i => ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      z ∉ thickening lumpRange (torusHotSites ℓ W)).card + (torusHotLumps ℓ W).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      z ∉ thickening lumpRange (torusHotSites ℓ W))
  rw [Finset.card_univ] at hsplit
  have hbad : ∀ i ∈ Finset.univ.filter (fun i => ¬ ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      z ∉ thickening lumpRange (torusHotSites ℓ W)), ∃ l ∈ torusHotLumps ℓ W,
      ∃ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2, ∃ x ∈ l, _root_.YangMills.Construction.TorusFields.supDist z x ≤ lumpRange := by
    intro i hi
    have h1 := (Finset.mem_filter.mp hi).2
    push Not at h1
    obtain ⟨z, hz, hzw⟩ := h1
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hzw
    obtain ⟨l, hl, hxl⟩ := mem_torusHotSites.mp hx
    exact ⟨l, hl, z, hz, x, hxl, hd⟩
  choose! lump hlump using hbad
  have hcard : (Finset.univ.filter (fun i => ¬ ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      z ∉ thickening lumpRange (torusHotSites ℓ W))).card ≤ (torusHotLumps ℓ W).card := by
    refine Finset.card_le_card_of_injOn lump (fun i hi => (hlump i hi).1) ?_
    intro i hi i' hi' he
    by_contra hne
    obtain ⟨hl, z, hz, x, hx, hd⟩ := hlump i hi
    obtain ⟨hl', z', hz', x', hx', hd'⟩ := hlump i' hi'
    have h1 := hfar i i' hne z hz z' hz'
    have hxx : x' ∈ lump i := by rw [he]; exact hx'
    have h2 := _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps hfit hLn hl hx hxx
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle z x z'
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle x x' z'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm x' z'] at h4
    unfold lumpRange at hd hd'
    omega
  omega
end HotLumps
section HullStates
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {n : ℕ} [NeZero n]
  {Λ : LabelSpace} {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
private theorem lintegral_glueLabel_of_eq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {Y Y' : Finset (TorusSite n)} (h : Y' = Y) (G : (Y → Ω) → ENNReal) (ω₀ : Y → Ω) :
    ∫⁻ ν, G (glueLabel Y Y' ω₀ ν) ∂(Measure.pi fun _ : Y' => μ) =
      ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => μ) := by apply _root_.YangMills.SharedProofs.p29218 <;> assumption
open Classical in
private theorem lintegral_labelWeight_le (h3 : ExpansionBasicBounds) (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E)
    (hx : 0 < x) (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x) (hc : ColdExpansion ℓ t x D f)
    (hh : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (hs : IsBlockTorusSide ℓ n) (W : TorusField n) (Y : Finset (TorusSite n))
    (hY : IsHullState ℓ (clusterRange x) W Y) :
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≤
      ENNReal.ofReal (D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) -
        x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W -
        x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ))) := by
  have hfacts := h3 ℓ t x D f Λ Dq Φ φ hfit hE hx hfl hc hh
  have hflat : IsCold ℓ.threshold (trivialField n) := fun z μ ν _ => by
    simp only [curvature, holonomy_trivialField]
    simpa using hfit.σ_pos
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < D n (trivialField n) := hc.positive n hn₀ _ hflat
  set A := actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W
    with hA
  set c : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) with hcdef
  have hc0 : 0 ≤ c := by positivity
  by_cases hne : Nonempty (Y → Λ.Ω)
  · obtain ⟨ω₀⟩ := hne
    set P := chainComponents (clusterRange x) Y with hP
    have hU : P.biUnion id = Y := biUnion_chainComponents
    have hp := hh.price n hs W Y ω₀ P hY subset_rfl
      (fun X hX => absurd (Finset.mem_sdiff.mp hX).1 (Finset.mem_sdiff.mp hX).2)
    let G : (Y → Λ.Ω) → ENNReal := fun ω =>
      if ∃ X ∈ P, Φ n W Y ω X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y W Y ω))
    have hfilter : (torusHotLumps ℓ W).filter (· ⊆ P.biUnion id) = torusHotLumps ℓ W := by
      refine Finset.filter_true_of_mem fun l hl z hz => ?_
      rw [hU]
      exact hY.1 ((mem_thickening _ _ _).mpr
        ⟨z, mem_torusHotSites.mpr ⟨l, hl, hz⟩, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    have hG : ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) ≤
        ENNReal.ofReal (Real.exp (-(x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)))) := by
      rw [← lintegral_glueLabel_of_eq Λ.μ hU G ω₀]
      refine hp.trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hfilter]
      apply Real.exp_le_exp.mpr
      have h2 := hfit.κ₁_pos
      have h4 : 0 ≤ ℓ.κ₁ * x * ℓ.threshold ^ 2 *
          (excessLength ℓ (clusterRange x) (P.biUnion id) W : ℝ) := by
        positivity
      linarith
    have hpt : ∀ ω, ENNReal.ofReal (Dq n W Y ω) ≤ ENNReal.ofReal c * G ω := by
      intro ω
      by_cases hz : ∃ X ∈ P, Φ n W Y ω X = 0
      · obtain ⟨X, hX, h0⟩ := hz
        rw [hh.form n hs W Y ω hY, Finset.prod_eq_zero hX h0, mul_zero]
        simp
      · have hGω : G ω = ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω)) := by
          simp only [G]
          rw [if_neg hz]
        push Not at hz
        rw [hGω, ← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        rw [hh.form n hs W Y ω hY]
        set near := Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4) with hnear
        have hsplit : ∑ y, φ n y W Y ω = ∑ y ∈ near, φ n y W Y ω +
            ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hfarsum : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω ≤
            2 * ℓ.E * Fintype.card (TorusSite n) := by
          have h1 : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
              φ n y W Y ω ≤ 2 * ℓ.E := by
            intro y hy
            have hy2 := (Finset.mem_filter.mp hy).2
            push Not at hy2
            rw [hU] at hy2
            exact (le_abs_self _).trans (hfacts.2.1 n hs W Y ω y hY hz hy2)
          have h2 := Finset.sum_le_card_nsmul _ _ _ h1
          rw [nsmul_eq_mul] at h2
          have h3 : ((Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4)).card : ℝ) ≤
              Fintype.card (TorusSite n) := by
            exact_mod_cast Finset.card_le_univ _
          have h4 : 0 ≤ 2 * ℓ.E := by linarith
          nlinarith
        have hprod : 0 ≤ ∏ X ∈ P, Φ n W Y ω X :=
          Finset.prod_nonneg fun X _ => hh.factor_nonneg n hs W Y ω X
        have hexp : Real.exp (-x * A + ∑ y, φ n y W Y ω) ≤
            Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) *
              Real.exp (∑ y ∈ near, φ n y W Y ω) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [hsplit]
          linarith
        calc D n (trivialField n) * _ * _ ≤ D n (trivialField n) *
              (Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) *
              Real.exp (∑ y ∈ near, φ n y W Y ω)) * ∏ X ∈ P, Φ n W Y ω X := by gcongr
          _ = c * ((∏ X ∈ P, Φ n W Y ω X) * Real.exp (∑ y ∈ near, φ n y W Y ω)) := by
            rw [hcdef]
            ring
    calc ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)
        ≤ ∫⁻ ω, ENNReal.ofReal c * G ω ∂(Measure.pi fun _ : Y => Λ.μ) := lintegral_mono hpt
      _ = ENNReal.ofReal c * ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c *
          ENNReal.ofReal (Real.exp (-(x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)))) := by
        gcongr
      _ = ENNReal.ofReal (c * Real.exp (-(x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)))) :=
        (ENNReal.ofReal_mul hc0).symm
      _ = _ := by
        congr 1
        rw [hcdef, mul_assoc, ← Real.exp_add]
        congr 2
  · have : IsEmpty (Y → Λ.Ω) := not_nonempty_iff.mp hne
    simp
end HullStates
section Rarity
variable {ℓ : StepParameters}
private theorem topField_measurable (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stageState_fst_eq (T : StageTower ℓ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) :
    (stageState T s n u).1 = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem card_torusSite_eq (n : ℕ) [NeZero n] : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
  simp [ZMod.card]
private theorem ofReal_le_fieldHaar_ballPi (n : ℕ) [NeZero n] {e q : ℝ} (hq : 0 ≤ q)
    (hb : q ≤ (haarUnit (closedBallAtOne e)).toReal) :
    ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite n)) ≤
      fieldHaar n (Set.pi Set.univ fun _ : TorusSite n =>
        Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e) := by apply _root_.YangMills.SharedProofs.p69150 <;> assumption
private theorem measurableSet_ballPi (n : ℕ) [NeZero n] (e : ℝ) :
    MeasurableSet (Set.pi Set.univ fun _ : TorusSite n =>
      Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e) := by apply _root_.YangMills.SharedProofs.p68411 <;> assumption
private theorem functional_ge_near_one {Tb : ParameterAssignment} {y : ℝ} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity}
    (hfacts : ∀ (n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → ∀ (z : TorusSite n) (W : TorusField n),
      IsCold (Tb.stepParameters y).threshold W → |centered f n z W| ≤ (Tb.stepParameters y).E)
    (hσ : 0 < Tb.threshold) {Nc : ℝ} (_hNc0 : 0 ≤ Nc)
    (hNc : ∀ (t n : ℕ) [NeZero n], Tb.n₀ ≤ n → ∀ (s : ℝ) (W : TorusField n), 0 < s → s ≤ Tb.threshold →
      IsCold s W → actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ Nc * s ^ 2 * (n : ℝ) ^ 4)
    (hc : ColdExpansion (Tb.stepParameters y) t x D f) (hx : 1 ≤ x) (n : ℕ) [NeZero n] (hn : Tb.n₀ ≤ n)
    (W : TorusField n)
    (hW : ∀ z i, ((W z i : UnitQuaternion) : ℍ[ℝ]) - 1 ∈
      Metric.closedBall (0 : ℍ[ℝ]) (Tb.threshold / (8 * Real.sqrt x))) :
    D n (trivialField n) * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * (n : ℝ) ^ 4)) ≤ D n W := by apply _root_.YangMills.SharedProofs.p2065 <;> assumption
open Classical in
private theorem count_far_le_actionAtLevel {Tb : ParameterAssignment} {y : ℝ} (hD : Tb.Admissible)
    (hAC : ActionAtLevelIsCutAction) (t m : ℕ)
    [NeZero m] [NeZero (m * Tb.side)] (hm : 64 ≤ m) (W : TorusField (m * Tb.side)) {ι : Type} [Fintype ι]
    (P : ι → TorusPlaquette (m * Tb.side))
    (hpl : ∀ i, P i ∈ plaquettesIn (Finset.univ : Finset (TorusSite (m * Tb.side))))
    (hfar : ∀ i i', i ≠ i' → ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      ∀ z' ∈ plaquetteVertices (P i').1 (P i').2.1 (P i').2.2, 2 ^ 17 ≤ _root_.YangMills.Construction.TorusFields.supDist z z')
    {τ : ℝ} (hτ : 2 * τ ≤ (Tb.side : ℝ) ^ (-4 : ℤ))
    (hhot : ∀ i, τ < plaquetteEnergy W (P i).1 (P i).2.1 (P i).2.2) :
    2 * Tb.coercivity * τ * ((Finset.univ.filter fun i => ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
        z ∉ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)).card : ℝ) ≤
      actionAtLevel Tb.coupling Tb.side t
        (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W := by
  set good := Finset.univ.filter fun i => ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
      z ∉ thickening lumpRange (torusHotSites (Tb.stepParameters y) W) with hgood
  have hsub : good.image P ⊆
      plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    refine mem_plaquettesIn.mpr ⟨(mem_plaquettesIn.mp (hpl i)).1, fun z hz => ?_⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2 z hz⟩
  have hinj : Set.InjOn P good := by
    intro i _ i' _ he
    by_contra hne
    have hz : (P i).1 ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2 := base_mem_plaquetteVertices _ _ _
    have hz' : (P i).1 ∈ plaquetteVertices (P i').1 (P i').2.1 (P i').2.2 := by
      rw [← he]
      exact hz
    have h1 := hfar i i' hne _ hz _ hz'
    rw [_root_.YangMills.Construction.TorusFields.supDist_self] at h1
    omega
  have hb := coercive_sum_le_actionAtLevel hD hAC t m hm _ W (good.image P) hsub
  refine le_trans ?_ hb
  rw [Finset.sum_image hinj]
  have hmin : ∀ i ∈ good, 2 * τ ≤
      min (curvature W (P i).1 (P i).2.1 (P i).2.2 ^ 2) ((Tb.side : ℝ) ^ (-4 : ℤ)) := by
    intro i _
    refine le_min ?_ hτ
    have h1 := hhot i
    rw [plaquetteEnergy_eq_curvature_sq] at h1
    linarith
  have hsum := Finset.card_nsmul_le_sum _ _ _ hmin
  rw [nsmul_eq_mul] at hsum
  have hc := hD.cK_pos
  calc 2 * Tb.coercivity * τ * (good.card : ℝ) = Tb.coercivity * ((good.card : ℝ) * (2 * τ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hc.le
set_option maxHeartbeats 1000000 in
private theorem separated_hot_bound {Tb : ParameterAssignment} {y : ℝ} (hD : Tb.Admissible)
    (hfit : (Tb.stepParameters y).Admissible)
    (h3 : ExpansionBasicBounds) (hAC : ActionAtLevelIsCutAction) (hAct : ColdActionBound)
    (hHaar : HaarMassCubicLowerBound)
    (hDen : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n],
      IsTowerAtParameters Tb y T β k → T.MarksMeasurable → IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ G : StageState T k n → ENNReal, Measurable G →
        ENNReal.ofReal (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side k n) W
            ∂(fieldHaar (fineSide (Tb.stepParameters y).side k n))) *
          ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) =
        ∫⁻ W, (open Classical in
          ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
            ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
              ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(fieldHaar n))
    (hProb : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n],
      IsTowerAtParameters Tb y T β k → T.MarksMeasurable → IsProbabilityMeasure (markedSampleLaw T β k n)) :
    ∃ c t₀ yP : ℝ, 0 < t₀ ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j n : ℕ) [NeZero n], IsTowerAtParameters Tb y T β j →
      T.MarksMeasurable →
      yP ≤ (couplingFlow (Tb.stepParameters y) β j).1 → IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (ι : Type) [Fintype ι] (P : ι → TorusPlaquette n),
        (∀ i, P i ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) →
        (∀ i i', i ≠ i' → ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
          ∀ z' ∈ plaquetteVertices (P i').1 (P i').2.1 (P i').2.2, 2 ^ 17 ≤ _root_.YangMills.Construction.TorusFields.supDist z z') →
        ∀ t : ℝ, 0 < t → t ≤ t₀ →
          (markedSampleLaw T β j n).real {u | ∀ i, t < plaquetteEnergy
              (topField (Tb.stepParameters y) j n u) (P i).1 (P i).2.1 (P i).2.2} ≤
            Real.exp (c * (Real.log (couplingFlow (Tb.stepParameters y) β j).1 + 1) * (n : ℝ) ^ 4 -
              2 * Tb.coercivity * (couplingFlow (Tb.stepParameters y) β j).1 * t * (Fintype.card ι : ℝ)) := by
  classical
  obtain ⟨Nc, hNc0, hNc⟩ := hAct Tb hD
  obtain ⟨cH, hcH, hHb⟩ := hHaar
  have hσ : 0 < Tb.threshold := hD.σ_pos
  have hκ : 0 < Tb.κ := hD.κ_pos
  have hcK := hD.cK_pos
  have hE : 1 ≤ Tb.E := hfit.E_ge
  have hLpos : (0 : ℝ) < (Tb.side : ℝ) ^ (-4 : ℤ) := by
    have : (0 : ℝ) < Tb.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Tb.side)
    positivity
  set b : ℝ := -(Real.log cH + 3 * Real.log (Tb.threshold / 8)) with hb
  set c : ℝ := Real.log 2 + 3 * Tb.E + Nc * Tb.threshold ^ 2 + 4 * |b| + 6 with hcdef
  set t₀ : ℝ := min ((Tb.side : ℝ) ^ (-4 : ℤ) / 2) (Tb.κ * Tb.threshold ^ 2 / (2 * Tb.coercivity)) with ht₀
  have ht₀pos : 0 < t₀ := lt_min (by positivity) (by positivity)
  refine ⟨c, t₀, max 1 (((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100), ht₀pos, ?_⟩
  intro T β j n _ hS hCo hy hs ι _ P hpl hfar t ht htt
  obtain ⟨m, hm⟩ := hs.1
  have hn : n = m * Tb.side := by
    rw [hm]
    show Tb.side * m = m * Tb.side
    ring
  subst hn
  have : NeZero m := ⟨by
    rintro rfl
    exact NeZero.ne (0 * Tb.side) (zero_mul _)⟩
  have hLpos' : 0 < Tb.side := Nat.pos_of_ne_zero (NeZero.ne Tb.side)
  have hmn : Tb.n₀ ≤ m := by
    have h1 : Tb.side * Tb.n₀ ≤ m * Tb.side := hs.2
    rw [mul_comm m] at h1
    exact Nat.le_of_mul_le_mul_left h1 hLpos'
  have hn₀ : 4096 ≤ Tb.n₀ := hD.n₀_ge
  have hm64 : 64 ≤ m := by omega
  have hbig : Tb.n₀ ≤ m * Tb.side := hmn.trans (Nat.le_mul_of_pos_right _ hLpos')
  have hxr : (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 := hS.coupling_eq j (Nat.le_succ j)
  rw [← hxr] at hy ⊢
  set x := (T.stage j).coupling with hxdef
  have hrow : (T.stage j).toStepSetup.HasExpansions := (hS.onFamily j le_rfl).isStep.1
  have hC : ColdExpansion (Tb.stepParameters y) (T.stage j).depth x (T.stage j).functional (T.stage j).density :=
    hrow.1
  have hH : HullExpansion (Tb.stepParameters y) (T.stage j).depth x (T.stage j).functional (T.stage j).density
      (T.stage j).labels (T.stage j).labelWeight (T.stage j).clusterFactor (T.stage j).siteDensity := hrow.2
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hy
  have hx0 : 0 < x := by linarith
  have hrange : 4 * (Tb.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange x := by
    have h1 : (((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ)) ^ 100 ≤ x := (le_max_right _ _).trans hy
    have h2 : (((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ)) ≤ x ^ ((1 : ℝ) / 100) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((100 : ℕ) : ℝ) * (1 / 100) = 1 by norm_num, Real.rpow_one] at h3
    exact Nat.cast_le.mp (h2.trans (Nat.le_ceil _))
  have hfacts := h3 _ _ _ _ _ _ _ _ _ hfit hE hx0 hrange hC hH
  have hP : IsProbabilityMeasure (markedSampleLaw T β j (m * Tb.side)) := hProb T β j _ hS hCo
  set H : Set (TorusField (m * Tb.side)) := {W | ∀ i, t < plaquetteEnergy W (P i).1 (P i).2.1 (P i).2.2}
    with hHdef
  have hHm : MeasurableSet H := by
    have e : H = ⋂ i, {W | t < plaquetteEnergy W (P i).1 (P i).2.1 (P i).2.2} := by
      ext W
      simp [hHdef]
    rw [e]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (continuous_plaquetteEnergy _ _ _).measurable
  set S : Set (MarkedSample (Tb.stepParameters y) j (m * Tb.side)) :=
    {u | ∀ i, t < plaquetteEnergy (topField (Tb.stepParameters y) j (m * Tb.side) u) (P i).1 (P i).2.1 (P i).2.2}
    with hSdef
  have hSm : MeasurableSet S := topField_measurable j (m * Tb.side) hHm
  let G : StageState T j (m * Tb.side) → ENNReal := fun q => H.indicator 1 q.1
  have hG : Measurable G := (measurable_one.indicator hHm).comp measurable_fst
  have hd1 := hDen T β j (m * Tb.side) hS hCo hs G hG
  have hd2 := hDen T β j (m * Tb.side) hS hCo hs (fun _ => 1) measurable_const
  set zr : ℝ := ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side j (m * Tb.side)) W
    ∂(fieldHaar (fineSide (Tb.stepParameters y).side j (m * Tb.side))) with hzr
  have hl1 : ∫⁻ u, G (stageState T j (m * Tb.side) u) ∂(markedSampleLaw T β j (m * Tb.side)) =
      markedSampleLaw T β j (m * Tb.side) S := by
    have e : (fun u => G (stageState T j (m * Tb.side) u)) = S.indicator 1 := by
      funext u
      simp only [G, stageState_fst_eq]
      rfl
    rw [e]
    exact lintegral_indicator_one hSm
  rw [hl1] at hd1
  simp only [lintegral_const, one_mul, measure_univ, mul_one] at hd2
  set C' : ℝ := (Fintype.card (TorusSite (m * Tb.side)) : ℝ) with hC'
  set K' : ℝ := 2 * Tb.coercivity * x * t * (Fintype.card ι : ℝ) with hK'
  set D1 : ℝ := (T.stage j).functional (m * Tb.side) (trivialField (m * Tb.side)) with hD1def
  have hflat : IsCold (Tb.stepParameters y).threshold (trivialField (m * Tb.side)) := fun z μ ν _ => by
    have h2 : curvature (trivialField (m * Tb.side)) z μ ν = 0 := by simp [curvature, holonomy_trivialField]
    rw [h2]
    exact hσ
  have hD1 : 0 < D1 := hC.positive _ hbig _ hflat
  set cU : ℝ := D1 * Real.exp (2 * Tb.E * C' - K') with hcU
  have hupper : ∀ W, (∑ Y ∈ Finset.univ.filter
      (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W),
      ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage j).labelWeight (m * Tb.side) W Y ω)
        ∂(Measure.pi fun _ : Y => (T.stage j).labels.μ)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side))) * ENNReal.ofReal cU := by
    intro W
    by_cases hW : W ∈ H
    · have hG1 : ∀ (Y : Finset (TorusSite (m * Tb.side))) (ω : Y → (T.stage j).labels.Ω),
          G (W, ⟨Y, ω⟩) = 1 := fun Y ω => by
        simp only [G]
        exact Set.indicator_of_mem hW _
      have key : ∀ Y ∈ Finset.univ.filter
          (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage j).labelWeight (m * Tb.side) W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage j).labels.μ) ≤ ENNReal.ofReal cU := by
        intro Y hY
        simp only [hG1, one_mul]
        refine (lintegral_labelWeight_le h3 hfit hE hx0 hrange hC hH hs W Y
          (Finset.mem_filter.mp hY).2).trans ?_
        apply ENNReal.ofReal_le_ofReal
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD1.le
        have hτ : 2 * t ≤ (Tb.side : ℝ) ^ (-4 : ℤ) := by
          have := htt.trans (min_le_left _ _)
          linarith
        have hgood := count_far_le_actionAtLevel (y := y) hD hAC (T.stage j).depth m hm64 W P hpl hfar hτ hW
        have hcount := card_le_card_far_add_card_hot hfit hs.1 W P hfar
        set g : ℕ := (Finset.univ.filter fun i => ∀ z ∈ plaquetteVertices (P i).1 (P i).2.1 (P i).2.2,
          z ∉ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)).card with hgdef
        have hcountR : (Fintype.card ι : ℝ) ≤
            (g : ℝ) + ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) := by
          exact_mod_cast hcount
        have hκt : 2 * Tb.coercivity * t ≤ Tb.κ * Tb.threshold ^ 2 := by
          have h1 := htt.trans (min_le_right _ _)
          rw [le_div_iff₀ (by positivity)] at h1
          linarith
        have hh0 : (0 : ℝ) ≤ ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) := by positivity
        have hcoef : 0 ≤ 2 * Tb.coercivity * t := by positivity
        have hmain : 2 * Tb.coercivity * t * (Fintype.card ι : ℝ) ≤
            actionAtLevel Tb.coupling Tb.side (T.stage j).depth
                (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W +
              Tb.κ * Tb.threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) := by
          have h1 := mul_le_mul_of_nonneg_left hcountR hcoef
          have h2 := mul_le_mul_of_nonneg_right hκt hh0
          have e : 2 * Tb.coercivity * t * ((g : ℝ) + ((torusHotLumps (Tb.stepParameters y) W).card : ℝ)) =
              2 * Tb.coercivity * t * (g : ℝ) +
                2 * Tb.coercivity * t * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) := by ring
          linarith
        have hmul := mul_le_mul_of_nonneg_left hmain hx0.le
        show 2 * Tb.E * (Fintype.card (TorusSite (m * Tb.side)) : ℝ) -
            x * actionAtLevel Tb.coupling Tb.side (T.stage j).depth
              (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W -
            x * Tb.κ * Tb.threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) ≤
              2 * Tb.E * C' - K'
        rw [hK']
        linarith
      refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
      rw [nsmul_eq_mul]
      have hcard : (Finset.univ.filter
          (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W)).card ≤
          2 ^ Fintype.card (TorusSite (m * Tb.side)) := by
        refine (Finset.card_le_univ _).trans ?_
        rw [Fintype.card_finset]
      have h1 : ((Finset.univ.filter
          (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W)).card : ENNReal) ≤
          ((2 ^ Fintype.card (TorusSite (m * Tb.side)) : ℕ) : ENNReal) := by exact_mod_cast hcard
      have h2e : ((2 ^ Fintype.card (TorusSite (m * Tb.side)) : ℕ) : ENNReal) =
          ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side))) := by
        rw [show ((2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side))) =
            ((2 ^ Fintype.card (TorusSite (m * Tb.side)) : ℕ) : ℝ) by
          push_cast; rfl, ENNReal.ofReal_natCast]
      rw [h2e] at h1
      exact mul_le_mul' h1 (le_refl _)
    · have hG0 : ∀ (Y : Finset (TorusSite (m * Tb.side))) (ω : Y → (T.stage j).labels.Ω),
          G (W, ⟨Y, ω⟩) = 0 := fun Y ω => by
        simp only [G]
        exact Set.indicator_of_notMem hW _
      simp [hG0]
  have hnum : ENNReal.ofReal zr * markedSampleLaw T β j (m * Tb.side) S ≤
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side))) * ENNReal.ofReal cU := by
    rw [hd1]
    refine (lintegral_mono hupper).trans ?_
    simp
  have hsq1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hsq0 : 0 < Real.sqrt x := by linarith
  set e : ℝ := Tb.threshold / (8 * Real.sqrt x) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]
    have := hD.σ_one
    linarith
  set q : ℝ := cH * e ^ 3 with hq
  have hq0 : 0 < q := by positivity
  have hqb : q ≤ (haarUnit (closedBallAtOne e)).toReal := hHb e he0 he1
  set c0 : ℝ := D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * ((m * Tb.side : ℕ) : ℝ) ^ 4)) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hlow : ENNReal.ofReal c0 * ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side))) ≤
      ENNReal.ofReal zr := by
    rw [hd2]
    have hsum : ∀ W, (∑ Y ∈ Finset.univ.filter
        (IsHullState (Tb.stepParameters y) (clusterRange (T.stage j).coupling) W),
        ∫⁻ ω, ENNReal.ofReal ((T.stage j).labelWeight (m * Tb.side) W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage j).labels.μ)) =
        ENNReal.ofReal ((T.stage j).functional (m * Tb.side) W) := fun W => hH.sum _ hs W
    simp only [hsum]
    set B : Set (TorusField (m * Tb.side)) := Set.pi Set.univ fun _ : TorusSite (m * Tb.side) =>
      Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e with hB
    have hBm : MeasurableSet B := measurableSet_ballPi _ e
    calc ENNReal.ofReal c0 * ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)))
        ≤ ENNReal.ofReal c0 * fieldHaar (m * Tb.side) B := by
          gcongr
          exact ofReal_le_fieldHaar_ballPi _ hq0.le hqb
      _ = ∫⁻ _ in B, ENNReal.ofReal c0 ∂(fieldHaar (m * Tb.side)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ W in B, ENNReal.ofReal ((T.stage j).functional (m * Tb.side) W) ∂(fieldHaar (m * Tb.side)) := by
          refine setLIntegral_mono' hBm fun W hW => ENNReal.ofReal_le_ofReal ?_
          refine functional_ge_near_one (y := y) (hfacts.1) hσ hNc0 hNc hC hx1 _ hbig W fun z i => ?_
          have h1 : W z i ∈ closedBallAtOne e := hW z (Set.mem_univ _) i (Set.mem_univ _)
          simpa [closedBallAtOne, dist_zero_right] using h1
      _ ≤ _ := setLIntegral_le_lintegral _ _
  set a : ℝ := (markedSampleLaw T β j (m * Tb.side)).real S with ha
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hLw : 0 < c0 * (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) := by positivity
  have hzLw : c0 * (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) ≤ zr := by
    rw [← ENNReal.ofReal_mul hc00] at hlow
    rcases (ENNReal.ofReal_le_ofReal_iff').mp hlow with h | h
    · exact h
    · exact absurd h (not_le.mpr hLw)
  have hzr0 : 0 ≤ zr := hLw.le.trans hzLw
  have hza : zr * a ≤ (2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side)) * cU := by
    have e1 : markedSampleLaw T β j (m * Tb.side) S = ENNReal.ofReal a :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    rw [e1, ← ENNReal.ofReal_mul hzr0, ← ENNReal.ofReal_mul (by positivity)] at hnum
    rcases (ENNReal.ofReal_le_ofReal_iff').mp hnum with h | h
    · exact h
    · exact h.trans (by positivity)
  have hC'n : C' = ((m * Tb.side : ℕ) : ℝ) ^ 4 := card_torusSite_eq _
  have hC'0 : 0 ≤ C' := by positivity
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogq : Real.log q = -b - 3 / 2 * Real.log x := by
    rw [hq, Real.log_mul hcH.ne' (by positivity), Real.log_pow, he,
      show Tb.threshold / (8 * Real.sqrt x) = (Tb.threshold / 8) / Real.sqrt x by field_simp,
      Real.log_div (by positivity) hsq0.ne', Real.log_sqrt (by linarith), hb]
    push_cast
    ring
  have hpow2 : (2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side)) = Real.exp (C' * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hpowq : (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) = Real.exp (C' * (4 * Real.log q)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    push_cast
    ring
  set Ex : ℝ := c * (Real.log x + 1) * ((m * Tb.side : ℕ) : ℝ) ^ 4 - K' with hEx
  have hU : (2 : ℝ) ^ Fintype.card (TorusSite (m * Tb.side)) * cU ≤
      c0 * (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) * Real.exp Ex := by
    rw [hpow2, hpowq, hcU, hc0, ← hC'n]
    have e1 : Real.exp (C' * Real.log 2) * (D1 * Real.exp (2 * Tb.E * C' - K')) =
        D1 * Real.exp (C' * Real.log 2 + (2 * Tb.E * C' - K')) := by
      rw [Real.exp_add]
      ring
    have e2 : D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * C')) * Real.exp (C' * (4 * Real.log q)) *
        Real.exp Ex =
        D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * C') + C' * (4 * Real.log q) + Ex) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD1.le
    rw [hEx, ← hC'n, hlogq]
    have hb' := le_abs_self b
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hNs : 0 ≤ Nc * Tb.threshold ^ 2 := by positivity
    have hc6 : 6 ≤ c := by
      rw [hcdef]
      have := abs_nonneg b
      linarith
    have hbr : 0 ≤ -Real.log 2 - 3 * Tb.E - Nc * Tb.threshold ^ 2 + 4 * (-b - 3 / 2 * Real.log x) +
        c * (Real.log x + 1) := by
      have h1 : 6 * Real.log x ≤ c * Real.log x := mul_le_mul_of_nonneg_right hc6 hlogx
      have h2 : c = Real.log 2 + 3 * Tb.E + Nc * Tb.threshold ^ 2 + 4 * |b| + 6 := hcdef
      linarith
    have := mul_nonneg hC'0 hbr
    linarith
  have hfin : c0 * (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) * a ≤
      c0 * (q ^ 4) ^ Fintype.card (TorusSite (m * Tb.side)) * Real.exp Ex :=
    (mul_le_mul_of_nonneg_right hzLw ha0).trans (hza.trans hU)
  exact le_of_mul_le_mul_left hfin hLw
theorem separatedHotPlaquettesRare (hDen : stageStateDensityStatement)
    (hTP : TwoPointByTotalCovarianceStatement) (h3 : ExpansionBasicBounds)
    (hAC : ActionAtLevelIsCutAction) (hAct : ColdActionBound)
    (hHaar : HaarMassCubicLowerBound) : separatedHotPlaquettesRareStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := hDen a ha
  refine ⟨L₁, r₁, hr₁, ?_⟩
  intro L hodd hLe Tb hTa hTL hD hrt
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd hLe Tb hTa hTL hD hrt
  refine ⟨max y₁ Tb.floorMin, fun y hy hR hW => ?_⟩
  have A₁ := Y₁ y ((le_max_left _ _).trans hy) hR hW
  have hfit := hD.fits y ((le_max_right _ _).trans hy)
  have hLam : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  refine separated_hot_bound hD hfit h3 hAC hAct hHaar A₁ fun T β k n _ hS hC => ?_
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h0 : T.base.barrierFn = Tb.cutoff := (hS.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    rw [h0]
    exact hD.cut
  exact (hTP (Tb.stepParameters y) hfit hLam T hcut hC β (fun _ => 0) k n).1
end Rarity
end YangMills.Construction.ResponseInTheExpansion
end
