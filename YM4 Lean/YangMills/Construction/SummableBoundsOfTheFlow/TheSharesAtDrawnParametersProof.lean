import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFinite
import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.ClusterExpansionOfAStep.TopOfACurvedChainIsAbelian
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ColdStepAtMirrorFrames.FieldsOfConstantCurvature
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsCarriedProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ShareFamilies
namespace AlongParameters
open TopLevelSites
variable {L t n : ℕ}
private theorem period_eq (i : Fin 4) :
    (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n := period_top i
private def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusFields.TorusBond n) :
    Fin k → (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).top × Fin 4 :=
  fun l => (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top (c l).1,
    (c l).2)
private theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) (V : TorusFields.TorusField n) :
    TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
        (TorusFields.perturb c X σ V) =
      BlockAverages.rotatedField (BlockAverages.bondSpread (frameBonds L t c) X σ)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) := by
  funext x i
  have e : (∑ l, if c l = (TorusLumps.toTorusSite n x, i) then σ l • X l else 0) =
      BlockAverages.bondSpread (frameBonds L t c) X σ x i := by
    unfold BlockAverages.bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have : c l = (TorusLumps.toTorusSite n x, i) ↔ frameBonds L t c l = (x, i) := by
      constructor
      · intro h
        simp only [frameBonds, h, torusSiteInFrame_toTorusSite period_eq]
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [frameBonds] at h1 h2
        refine Prod.ext ?_ h2
        rw [← h1, toTorusSite_torusSiteInFrame period_eq]
    simp only [this]
  show BlockAverages.expUnit (∑ l, if c l = (TorusLumps.toTorusSite n x, i) then σ l • X l else 0) *
      V (TorusLumps.toTorusSite n x) i = _
  rw [e]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501447 := @readAtLevel_perturb
private theorem mixedDeriv_frame [NeZero n]
    (g : (TorusFields.torusFrame L t n).GaugeField (TorusFields.torusFrame L t n).top → ℝ) {k : ℕ}
    (V : TorusFields.TorusField n) (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    TorusFields.mixedDeriv
        (fun W => g (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W))
        V c X =
      BlockAverages.mixedBondDerivative g
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)
        (frameBonds L t c) X := by
  unfold TorusFields.mixedDeriv BlockAverages.mixedBondDerivative
  have e : (fun σ : Fin k → ℝ => g (TorusFields.readAtLevel (TorusFields.torusFrame L t n)
        (TorusFields.torusFrame L t n).top (TorusFields.perturb c X σ V))) =
      fun σ => g (BlockAverages.rotatedField (BlockAverages.bondSpread (frameBonds L t c) X σ)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)) := by
    funext σ
    rw [readAtLevel_perturb]
  rw [e]
abbrev _root_.YangMills.DeltaSharedProofs.p501924 := @mixedDeriv_frame
private theorem cellSupDist_frame [NeZero n] (y z : TorusFields.TorusSite n) :
    BlockAverages.cellSupDist (F := TorusFields.torusFrame L t n)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z) =
      TorusFields.supDist y z := by apply _root_.YangMills.Construction.TopFamilyEvaluations.siteSupDist_torusSiteInFrame <;> assumption
private theorem levelShareFamily_eq (a : ℝ) (L t : ℕ) [NeZero n] (y : TorusFields.TorusSite n)
    (V : TorusFields.TorusField n) :
    ShareFamilies.levelShareFamily a L (t + 1) n y V =
      BlockAverages.minimalCellShare a
        (TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n)))
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) := by
  unfold ShareFamilies.levelShareFamily
  rw [dif_neg (NeZero.ne n)]
  rfl
private theorem expansionWeight_nonneg (rt n₁ : ℝ) (m : ℕ) : 0 ≤ TorusLumps.expansionWeight rt n₁ m :=
  mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
private theorem actSite_torusSiteInFrame [NeZero n] (g : TorusFields.TorusIsometry) (y : TorusFields.TorusSite n) :
    BlockAverages.CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (TorusFields.torusFrame L t n).top
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y) =
      StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top (g.mapSite y) := by apply _root_.YangMills.SharedProofs.p75600 <;> assumption
private theorem transportsField_of_transports [NeZero n] (g : TorusFields.TorusIsometry)
    {W W' : TorusFields.TorusField n} (h : g.Transports W W') :
    BlockAverages.CubicSymmetry.TransportsField (F := TorusFields.torusFrame L t n) ⟨g.axisPerm, g.axisSign, g.offset⟩
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W)
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W') := by apply _root_.YangMills.SharedProofs.p26341 <;> assumption
private theorem isCold_translate [NeZero n] {s : ℝ} {W : TorusFields.TorusField n} (hW : TorusFields.IsCold s W)
    (u : TorusFields.TorusSite n) : TorusFields.IsCold s (TorusFields.translate u W) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.isCold_translate <;> assumption
private def translation (u : TorusFields.TorusSite n) : TorusFields.TorusIsometry :=
  ⟨1, fun _ => 1, fun i => ((u i).cast : ℤ), fun _ => Or.inl rfl⟩
private theorem mapSite_translation [NeZero n] (u x : TorusFields.TorusSite n) :
    (translation u).mapSite x = x + u := by
  funext i
  simp [TorusFields.TorusIsometry.mapSite, translation]
private theorem translation_transports [NeZero n] (u : TorusFields.TorusSite n) (W : TorusFields.TorusField n) :
    (translation u).Transports (TorusFields.translate u W) W := by
  intro x k
  have hs : (translation u).axisSign ((translation u).axisPerm.symm k) = 1 := rfl
  rw [if_pos hs]
  show W ((translation u).mapSite x) k = W (x + u) k
  rw [mapSite_translation]
private theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem centered_levelShareFamily (h4 : BlockAverages.flatTopVanishingStatement) (a : ℝ) (ha : 0 ≤ a)
    (hL : Odd L) [NeZero n] (y : TorusFields.TorusSite n) :
    TorusLumps.centered (ShareFamilies.levelShareFamily a L (t + 1)) n y =
      ShareFamilies.levelShareFamily a L (t + 1) n y := by
  funext V
  have e : TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
      (TorusFields.trivialField n) =
        BlockAverages.flatField (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top := rfl
  have h0 := (h4 (TorusFields.torusFrame L t n) a
    (TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n)))
    ha hL).2.2
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y)
  unfold TorusLumps.centered
  rw [levelShareFamily_eq a L t y (TorusFields.trivialField n), e, h0, sub_zero]
abbrev _root_.YangMills.SharedProofs.p17512 := @centered_levelShareFamily
private theorem le_maxOfFirstFour (N : ℕ → ℝ) (k : ℕ) (hk : k ≤ 3) : N k ≤ TorusLumps.maxOfFirstFour N := by
  unfold TorusLumps.maxOfFirstFour
  interval_cases k
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
abbrev _root_.YangMills.SharedProofs.p3581 := @le_maxOfFirstFour
private theorem norm_quaternionI : ‖TorusLumps.quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem curvatureAlong_quaternionI :
    TorusLumps.curvatureAlong TorusLumps.quaternionI (PlaneFields.planeForm 0 1) = TorusLumps.unitPlaneCurvature := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [TorusLumps.curvatureAlong, PlaneFields.planeForm, TorusLumps.unitPlaneCurvature, TorusLumps.planeCurvature]
  exact neg_one_smul ℝ TorusLumps.quaternionI
private theorem planeForm_antisymm (i j : Fin 4) : PlaneFields.planeForm 0 1 i j = - PlaneFields.planeForm 0 1 j i := by
  fin_cases i <;> fin_cases j <;> simp [PlaneFields.planeForm]
private theorem planeForm_integral (i j : Fin 4) : ∃ k : ℤ, ((1 : ℕ) : ℝ) * PlaneFields.planeForm 0 1 i j = k := by
  unfold PlaneFields.planeForm
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp⟩
abbrev _root_.YangMills.SharedProofs.p6658 := @planeForm_integral
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    TorusLumps.unitPlaneCurvature μ ν = - TorusLumps.unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem curvaturePairing_unit :
    TorusLumps.curvaturePairing TorusLumps.unitPlaneCurvature TorusLumps.unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
private theorem eventually_expUnit_near_one (X : BlockAverages.imaginaryQuaternions) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ τ : ℝ in 𝓝 0, ‖((BlockAverages.expUnit (τ • X) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ < s := by
  have hc : Continuous fun τ : ℝ => ‖((BlockAverages.expUnit (τ • X) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    have he : Continuous BlockAverages.expUnit := by
      refine Continuous.subtype_mk ?_ _
      have h : Continuous (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
        continuous_iff_continuousAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
      exact h.comp continuous_subtype_val
    have h1 : Continuous fun τ : ℝ => BlockAverages.expUnit (τ • X) :=
      he.comp (continuous_id.smul continuous_const)
    exact ((continuous_subtype_val.comp h1).sub continuous_const).norm
  have h0 : ‖((BlockAverages.expUnit ((0 : ℝ) • X) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0 := by
    rw [zero_smul, TorusFields.expUnit_zero]
    simp
  have := hc.tendsto 0
  rw [h0] at this
  exact this.eventually (gt_mem_nhds hs)
abbrev _root_.YangMills.SharedProofs.p49248 := @eventually_expUnit_near_one
private theorem tendsto_plane_angle :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  exact h1.const_div_atTop _
private theorem abs_one_sub_le_of_action {M n θ γ ε v A : ℝ} (hMθ : M ^ 2 * θ = 2 * Real.pi)
    (hnγ : n ^ 2 * γ = 2 * Real.pi) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθγ : θ ≤ γ) (hγε : γ ^ 2 ≤ ε)
    (hA : A = M ^ 4 * (1 - Real.cos θ))
    (hS : |A - n ^ 4 * (γ ^ 2 / 2 * v)| ≤ n ^ 4 * (ε * γ ^ 2)) : |1 - v| ≤ 3 * ε := by
  have hb := Real.cos_bound (x := θ) (by rwa [abs_of_nonneg hθ0])
  rw [abs_of_nonneg hθ0] at hb
  set D := 1 - Real.cos θ - θ ^ 2 / 2 with hD
  have hDb : |D| ≤ θ ^ 4 * (5 / 96) := by
    have : D = -(Real.cos θ - (1 - θ ^ 2 / 2)) := by rw [hD]; ring
    rw [this, abs_neg]
    exact hb
  have e1 : M ^ 4 * θ ^ 2 = 4 * Real.pi ^ 2 := by
    have : M ^ 4 * θ ^ 2 = (M ^ 2 * θ) ^ 2 := by ring
    rw [this, hMθ]
    ring
  have e2 : n ^ 4 * γ ^ 2 = 4 * Real.pi ^ 2 := by
    have : n ^ 4 * γ ^ 2 = (n ^ 2 * γ) ^ 2 := by ring
    rw [this, hnγ]
    ring
  have hA' : A = M ^ 4 * D + 2 * Real.pi ^ 2 := by
    rw [hA, hD]
    linear_combination (1 / 2) * e1
  have hM4 : 0 ≤ M ^ 4 := by positivity
  have hMD : |M ^ 4 * D| ≤ 4 * Real.pi ^ 2 * θ ^ 2 * (5 / 96) := by
    rw [abs_mul, abs_of_nonneg hM4]
    calc M ^ 4 * |D| ≤ M ^ 4 * (θ ^ 4 * (5 / 96)) := mul_le_mul_of_nonneg_left hDb hM4
      _ = (M ^ 4 * θ ^ 2) * θ ^ 2 * (5 / 96) := by ring
      _ = _ := by rw [e1]
  have eS : n ^ 4 * (γ ^ 2 / 2 * v) = 2 * Real.pi ^ 2 * v := by
    linear_combination (v / 2) * e2
  have eR : n ^ 4 * (ε * γ ^ 2) = 4 * Real.pi ^ 2 * ε := by
    linear_combination ε * e2
  rw [eS, eR] at hS
  have h1 : 2 * Real.pi ^ 2 * (1 - v) = (A - 2 * Real.pi ^ 2 * v) - M ^ 4 * D := by
    rw [hA']
    ring
  have h2 : 2 * Real.pi ^ 2 * |1 - v| ≤ 4 * Real.pi ^ 2 * ε + 4 * Real.pi ^ 2 * θ ^ 2 * (5 / 96) := by
    have h3 : |2 * Real.pi ^ 2 * (1 - v)| = 2 * Real.pi ^ 2 * |1 - v| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    rw [← h3, h1]
    exact (abs_sub _ _).trans (add_le_add hS hMD)
  have hθ2 : θ ^ 2 ≤ ε := le_trans (pow_le_pow_left₀ hθ0 hθγ 2) hγε
  have h4 : 2 * Real.pi ^ 2 * |1 - v| ≤ 2 * Real.pi ^ 2 * (3 * ε) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 (by positivity)
abbrev _root_.YangMills.SharedProofs.p38896 := @abs_one_sub_le_of_action
private theorem cellsOfSites_univ {L t n : ℕ} [NeZero n] :
    TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n)) =
      ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n) := by
  ext z
  constructor
  · intro _
    exact mem_finiteCells (fun i => Nat.pos_of_ne_zero (NeZero.ne n)) z
  · intro _
    exact Finset.mem_image.mpr ⟨TorusLumps.toTorusSite n z, Finset.mem_univ _, torusSiteInFrame_toTorusSite period_eq z⟩
abbrev _root_.YangMills.SharedProofs.p810 := @cellsOfSites_univ
private theorem readAtLevel_restrictToTorus {L t n : ℕ} [NeZero n]
    (W : (TorusFields.torusFrame L t n).GaugeField (TorusFields.torusFrame L t n).top) :
    TorusFields.readAtLevel (TorusFields.torusFrame L t n) (t + 1) (ColdStepAtMirrorFrames.restrictToTorus n W) = W := by
  funext x i
  have h := torusSiteInFrame_toTorusSite (period_eq (L := L) (t := t) (n := n)) x
  exact congrArg (fun z => W z i) h
private theorem isSmallCurvature_readAtLevel {L t n : ℕ} [NeZero n] {s : ℝ} {V : TorusFields.TorusField n}
    (hV : TorusFields.IsCold s V) :
    ColdStepAtMirrorFrames.IsSmallCurvature (F := TorusFields.torusFrame L t n) s
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
private theorem exp_le_weightGrowthSup_div (h2 : TorusLumps.PotentialSumsFinite) (ℓ : TorusLumps.StepParameters)
    (hF : ℓ.Admissible) {δ : ℝ} (hr : ℓ.rt / 2 ^ 9 ≤ δ / 2) (D m : ℕ) (hm : m ≤ 2 * D) :
    Real.exp (-δ * D) ≤ TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m := by
  obtain ⟨-, -, -, hle, -, -, -⟩ := h2 ℓ.rt ℓ.n₁ hF.rt_pos hF.n₁_pos
  rw [le_div_iff₀ (weight_pos _ m)]
  refine le_trans ?_ (hle m)
  have e : ℓ.weight m = TorusLumps.expansionWeight ℓ.rt ℓ.n₁ m := rfl
  rw [e, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (expansionWeight_nonneg _ _ _)
  rw [Real.exp_le_exp]
  have hrt := hF.rt_pos
  have hm' : (m : ℝ) ≤ 2 * D := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e2 : 2 * (ℓ.rt / 2 ^ 10) * (m : ℝ) = ℓ.rt / 2 ^ 9 * m := by ring
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_right hr hm0]
private theorem eventually_ceilings : ColdStepAtMirrorFrames.EventuallyInParameters fun T =>
    T.κ ≤ T.chainParams.δ₁ / 2 ^ 8 ∧ T.σ ≤ T.chainParams.σA ∧ T.σ ≤ 1 := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct _ => ⟨c.δ₁ / 2 ^ 8, ?_, fun κ _ hκ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨min c.σA 1, lt_min hc.positivity.2.2.2.1 one_pos, fun σ _ hσ p _ =>
      ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ =>
        ⟨hκ, hσ.trans (min_le_left _ _), hσ.trans (min_le_right _ _)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have := hc.positivity.1
  positivity
private theorem share_bounds (h2 : TorusLumps.PotentialSumsFinite) (h3 : ColdStepAtMirrorFrames.sumCellSharesEqAction)
    (h4 : BlockAverages.flatTopVanishingStatement) (T : ColdStepAtMirrorFrames.StepParameters) (hdr : T.IsOrdered)
    (hκ : T.κ ≤ T.chainParams.δ₁ / 2 ^ 8) (hσA : T.σ ≤ T.chainParams.σA) (hσ1 : T.σ ≤ 1)
    (ℓ : TorusLumps.StepParameters) (hm : T.Compatible ℓ) (hfits : ℓ.Admissible) (t : ℕ) :
    TorusLumps.IsCurvatureFamily ℓ (TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ * TorusLumps.maxOfFirstFour T.chainParams.N)
      (ShareFamilies.levelShareFamily T.a T.L (t + 1)) ∧
    TorusLumps.SumInvariantUnderIsometries ℓ (ShareFamilies.levelShareFamily T.a T.L (t + 1)) ∧
    (∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n),
      TorusFields.IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          ShareFamilies.levelShareFamily T.a T.L (t + 1) n y (TorusFields.perturb c X τ W)) 0) ∧
    (∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n),
      TorusFields.IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions), 1 ≤ k →
        BlockAverages.AreUnitVectors X →
        |TorusFields.mixedDeriv (ShareFamilies.levelShareFamily T.a T.L (t + 1) n y) W c X| ≤
          TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ * T.chainParams.N k / ℓ.weight (TorusFields.supportDiam y c)) ∧
    ∀ n [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold T.σ V →
      ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V =
        TorusFields.actionAtLevel T.a T.L (t + 1) Finset.univ V := by
  have hσ := hdr.σ_pos
  have hN : ∀ k, 0 < T.chainParams.N k := hdr.chain_admissible.positivity.2.2.2.2.2.1
  have ha0 : 0 ≤ T.a := by linarith [hdr.one_le_a]
  have hodd := hdr.odd_L
  have hn₀ : 4096 ≤ T.n₀ := by
    have h := hfits.n₀_ge
    rwa [hm.n₀_eq] at h
  have hr : ℓ.rt / 2 ^ 9 ≤ T.chainParams.δ₁ / 2 := by
    rw [hm.rt_eq]
    have := hdr.κ_pos
    norm_num at hκ ⊢
    linarith
  have hG0 : 0 ≤ TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ := by
    obtain ⟨-, -, -, -, -, -, hG⟩ := h2 ℓ.rt ℓ.n₁ hfits.rt_pos hfits.n₁_pos
    linarith
  have hNa : 0 ≤ TorusLumps.maxOfFirstFour T.chainParams.N :=
    (hN 0).le.trans (le_maxOfFirstFour T.chainParams.N 0 (by norm_num))
  obtain ⟨a, ha⟩ : ∃ a, a = T.a := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = T.L := ⟨_, rfl⟩
  rw [← ha, ← hLdef]
  rw [← ha] at ha0
  rw [← hLdef] at hodd
  have main := fun (n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (W : TorusFields.TorusField n)
      (hW : TorusFields.IsCold T.σ W) =>
    hdr.chain_admissible.estimates (TorusFields.torusFrame T.L t n) T.σ
      (TorusFields.readAtLevel (TorusFields.torusFrame T.L t n) (TorusFields.torusFrame T.L t n).top W)
      ⟨rfl, n, by omega, fun _ => rfl⟩ hσ hσA (isSmallCurvature_readAtLevel hW)
  have hcl : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ W : TorusFields.TorusField n, TorusFields.IsCold T.σ W →
      BlockAverages.HasRegularCellShares a T.chainParams.δ₁ T.σ T.chainParams.N
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W) := by
    intro n _ hn W hW
    rw [ha, hLdef]
    exact (main n hn W hW).cellShares
  have hall : ∀ (n : ℕ) [NeZero n] (z : (TorusFields.torusFrame L t n).Cell),
      z ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n) :=
    fun n _ z => mem_finiteCells (fun i => Nat.pos_of_ne_zero (NeZero.ne n)) z
  have hfun : ∀ (n : ℕ) [NeZero n] (z : TorusFields.TorusSite n), ShareFamilies.levelShareFamily a L (t + 1) n z =
      fun V => BlockAverages.minimalCellShare a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) :=
    fun n _ z => funext fun V => by
      rw [levelShareFamily_eq, cellsOfSites_univ]
  have hcar : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (g : TorusFields.TorusIsometry) (W W' : TorusFields.TorusField n),
      TorusFields.IsCold T.σ W → g.Transports W W' →
      ∀ z, ShareFamilies.levelShareFamily a L (t + 1) n (g.mapSite z) W' =
        ShareFamilies.levelShareFamily a L (t + 1) n z W := by
    intro n _ hn g W W' hW hC z
    obtain ⟨-, -, -, -, hIso, -⟩ := hcl n hn W hW
    have := hIso ⟨g.axisPerm, g.axisSign, g.offset⟩ (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W')
      ⟨g.axisSign_unit, fun _ _ => rfl⟩ (fun _ => ⟨fun _ => hall n _, fun _ => hall n _⟩)
      (transportsField_of_transports g hC)
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
    rw [actSite_torusSiteInFrame] at this
    rw [hfun n, hfun n]
    exact this
  have hanal : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n),
      TorusFields.IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          ShareFamilies.levelShareFamily a L (t + 1) n y (TorusFields.perturb c X τ W)) 0 := by
    intro n _ hn z W hW k c X
    have hA := (hcl n hn W hW).2.1
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z) k
      (frameBonds L t c) X
    have e : (fun σ : Fin k → ℝ => ShareFamilies.levelShareFamily a L (t + 1) n z (TorusFields.perturb c X σ W)) =
        fun σ => BlockAverages.minimalCellShare a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
          (BlockAverages.rotatedField (BlockAverages.bondSpread (frameBonds L t c) X σ)
            (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W)) := by
      funext σ
      rw [hfun n]
      beta_reduce
      rw [readAtLevel_perturb]
    rw [e]
    exact hA
  have hdec : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n),
      TorusFields.IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions), 1 ≤ k →
        BlockAverages.AreUnitVectors X →
        |TorusFields.mixedDeriv (ShareFamilies.levelShareFamily a L (t + 1) n y) W c X| ≤
          TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ * T.chainParams.N k / ℓ.weight (TorusFields.supportDiam y c) := by
    intro n _ hn z W hW k c X hk1 hX
    obtain ⟨-, -, -, -, -, -, hDec, -⟩ := hcl n hn W hW
    have hb := hDec (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
      k (frameBonds L t c) X hk1 hX
    rw [hfun n z, mixedDeriv_frame (fun V => BlockAverages.minimalCellShare a
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z) V)]
    have hD' : BlockAverages.bondListDistance
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
        (frameBonds L t c) = Finset.univ.sup fun l => TorusFields.supDist z (c l).1 := by
      unfold BlockAverages.bondListDistance
      congr 1
      funext l
      exact cellSupDist_frame z (c l).1
    rw [hD'] at hb
    set D := Finset.univ.sup fun l => TorusFields.supDist z (c l).1 with hDdef
    have hlz : ∀ l, TorusFields.supDist z (c l).1 ≤ D := fun l =>
      Finset.le_sup (f := fun l => TorusFields.supDist z (c l).1) (Finset.mem_univ l)
    have hms : TorusFields.supportDiam z c ≤ 2 * D := by
      unfold TorusFields.supportDiam
      refine max_le ((Finset.sup_le fun l _ => hlz l).trans (by omega)) (Finset.sup_le fun l _ =>
        Finset.sup_le fun l' _ => ?_)
      have h1 := TorusFields.supDist_triangle (c l).1 z (c l').1
      rw [TorusFields.supDist_comm (c l).1 z] at h1
      have := hlz l
      have := hlz l'
      omega
    have he := exp_le_weightGrowthSup_div h2 ℓ hfits hr D (TorusFields.supportDiam z c) hms
    refine hb.trans ?_
    calc T.chainParams.N k * Real.exp (-T.chainParams.δ₁ * D) ≤
          T.chainParams.N k * (TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight (TorusFields.supportDiam z c)) :=
          mul_le_mul_of_nonneg_left he (hN k).le
      _ = _ := by ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hanal, hdec, ?_⟩
  · intro n _ hn z W hW k c X
    rw [hm.n₀_eq] at hn
    rw [hm.threshold_eq] at hW
    exact (hanal n hn z W hW k c X).contDiffAt
  · intro n _ hn z g W hW
    rw [hm.n₀_eq] at hn
    rw [hm.threshold_eq] at hW
    obtain ⟨-, -, -, hGa, -⟩ := hcl n hn W hW
    have e : TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
        (TorusFields.gaugeTransform g W) =
        BlockAverages.gaugeTransform (fun x => g (TorusLumps.toTorusSite n x))
          (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W) := by
      funext x i
      show g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
          (g (TorusLumps.toTorusSite n x + TorusFields.unitStep n i))⁻¹ =
        g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
          (g (TorusLumps.toTorusSite n (x + BlockAverages.unitStep (TorusFields.torusFrame L t n).top i)))⁻¹
      rw [toTorusSite_add period_eq, toTorusSite_unitStep period_eq]
    rw [hfun n]
    beta_reduce
    rw [e]
    exact hGa _ _
  · intro n _ hn z u W hW
    rw [hm.n₀_eq] at hn
    rw [hm.threshold_eq] at hW
    have := hcar n hn (translation u) (TorusFields.translate u W) W (isCold_translate hW u)
      (translation_transports u W) z
    rw [mapSite_translation] at this
    exact this.symm
  · intro n _ hn z W hW k c X hk1 hk3 hX
    rw [hm.n₀_eq] at hn
    rw [hm.threshold_eq] at hW
    refine (hdec n hn z W hW k c X hk1 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (weight_pos _ _).le
    exact mul_le_mul_of_nonneg_left (le_maxOfFirstFour T.chainParams.N k hk3) hG0
  · intro n n' _ _ hn hn' z z' W W' r h1 h1' hW hW' hA k b X hk hb hX
    rw [hm.n₀_eq] at hn hn'
    rw [hm.threshold_eq] at hW hW'
    have e1 : TorusLumps.centered (ShareFamilies.levelShareFamily a L (t + 1)) n z =
        ShareFamilies.levelShareFamily a L (t + 1) n z := centered_levelShareFamily h4 a ha0 hodd z
    have e2 : TorusLumps.centered (ShareFamilies.levelShareFamily a L (t + 1)) n' z' =
        ShareFamilies.levelShareFamily a L (t + 1) n' z' :=
      centered_levelShareFamily h4 a ha0 hodd z'
    rw [e1, e2, hfun n z, hfun n' z',
      mixedDeriv_frame (fun V => BlockAverages.minimalCellShare a
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z) V),
      mixedDeriv_frame (fun V => BlockAverages.minimalCellShare a
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n'))
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n') (TorusFields.torusFrame L t n').top z') V)]
    have hag : BlockAverages.AgreeOnBall (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W)
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n'))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n') (TorusFields.torusFrame L t n').top W')
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n') (TorusFields.torusFrame L t n').top z') r := by
      refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h1', fun _ _ => ⟨fun _ => hall n' _, fun _ => hall n _⟩,
        fun c hc => ?_⟩
      have := hA c hc
      show W (TorusLumps.toTorusSite n _) c.2 = W' (TorusLumps.toTorusSite n' _) c.2
      rw [toTorusSite_add period_eq, toTorusSite_add period_eq, toTorusSite_torusSiteInFrame period_eq,
        toTorusSite_torusSiteInFrame period_eq, toTorusSite_siteOfCoords period_eq,
        toTorusSite_siteOfCoords period_eq]
      exact this
    have hcl' := main n hn W hW
    rw [← ha, ← hLdef] at hcl'
    have hl := (hcl'.locality (TorusFields.torusFrame L t n')
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n') (TorusFields.torusFrame L t n').top W') _ _ r rfl rfl
      ⟨n', by omega, fun _ => rfl⟩ (isSmallCurvature_readAtLevel hW') hag).1 k b X hb hX
    have eb : ∀ (N : ℕ) [NeZero N] (v : TorusFields.TorusSite N),
        (frameBonds L t fun l => TorusLumps.bondFrom v (b l)) =
          BlockAverages.offsetBonds
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t N) (TorusFields.torusFrame L t N).top v) b := by
      intro N _ v
      funext l
      refine Prod.ext ?_ rfl
      show StepCosts.torusSiteInFrame (TorusFields.torusFrame L t N) (TorusFields.torusFrame L t N).top
          (v + TorusFields.siteOfInt (b l).1) = _ + BlockAverages.siteOfCoords _ (b l).1
      rw [torusSiteInFrame_add period_eq, torusSiteInFrame_siteOfInt period_eq]
    rw [eb n z, eb n' z']
    refine hl.trans ?_
    have he := exp_le_weightGrowthSup_div h2 ℓ hfits hr r r (by omega)
    have hNk : T.chainParams.N k ≤ TorusLumps.maxOfFirstFour T.chainParams.N :=
      le_maxOfFirstFour T.chainParams.N k (by omega)
    have hf : BlockAverages.derivativeScale T.σ k ≤ 1 := by
      unfold BlockAverages.derivativeScale
      split_ifs
      · nlinarith
      · exact hσ1
      · exact le_rfl
    have hf0 : 0 ≤ BlockAverages.derivativeScale T.σ k := by
      unfold BlockAverages.derivativeScale
      split_ifs <;> positivity
    have hp : BlockAverages.derivativeScale T.σ k * T.chainParams.N k ≤ TorusLumps.maxOfFirstFour T.chainParams.N := by
      nlinarith [hN k]
    calc BlockAverages.derivativeScale T.σ k * T.chainParams.N k * Real.exp (-T.chainParams.δ₁ * r)
        ≤ TorusLumps.maxOfFirstFour T.chainParams.N * (TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight r) :=
          mul_le_mul hp he (Real.exp_pos _).le hNa
      _ = _ := by ring
  · intro n _ hn g W W' hW hW' hC
    rw [hm.n₀_eq] at hn
    rw [hm.threshold_eq] at hW hW'
    have e1 : ∀ V : TorusFields.TorusField n,
        ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily a L (t + 1)) n z V =
          ∑ z, ShareFamilies.levelShareFamily a L (t + 1) n z V := by
      intro V
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [centered_levelShareFamily h4 a ha0 hodd z]
    rw [e1, e1]
    have hbij : Function.Bijective (g.mapSite (n := n)) :=
      Finite.injective_iff_bijective.mp (TorusFields.mapSite_injective g)
    rw [← (Equiv.ofBijective _ hbij).sum_comp (fun z => ShareFamilies.levelShareFamily a L (t + 1) n z W')]
    exact Finset.sum_congr rfl fun z _ => hcar n hn g W W' hW hC z
  · intro n _ hn V hV
    have hs : ∀ i, 2 ≤ (TorusFields.torusFrame L t n).extent i := fun i => by
      show 2 ≤ n
      omega
    have h5 := (h3 (TorusFields.torusFrame L t n) a (fun _ _ => 0)
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) ha0 hodd hs).1
    have e1 : ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily a L (t + 1)) n z V =
        ∑ z, ShareFamilies.levelShareFamily a L (t + 1) n z V :=
      Finset.sum_congr rfl fun z _ => by rw [centered_levelShareFamily h4 a ha0 hodd z]
    rw [e1]
    show _ = BlockAverages.minimalAction a
      (TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n))) (t + 1)
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (t + 1) V)
    rw [cellsOfSites_univ]
    have h6 : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n),
          BlockAverages.minimalCellShare a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n)) Y
            (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) =
        BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n)) (t + 1)
          (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (t + 1) V) := h5
    rw [← h6]
    refine Finset.sum_bij
      (fun z _ => StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
      (fun z _ => hall n _) ?_ ?_ ?_
    · intro z _ z' _ h
      have := congrArg (TorusLumps.toTorusSite n) h
      rwa [toTorusSite_torusSiteInFrame period_eq, toTorusSite_torusSiteInFrame period_eq] at this
    · intro w _
      exact ⟨TorusLumps.toTorusSite n w, Finset.mem_univ _, torusSiteInFrame_toTorusSite period_eq w⟩
    · intro z _
      rw [hfun n]
private theorem curvature_form_one (h5 : TorusLumps.InvariantFamilyCurvatureForm)
    (h6 : TorusLumps.SecondOrderAtAbelianFields)
    (h7 : ColdStepAtMirrorFrames.constantCurvatureMinimalActionStatement)
    (h8 : TorusLumps.TopOfConstantCurvatureChainIsAbelian) (T : ColdStepAtMirrorFrames.StepParameters)
    (hdr : T.IsOrdered) (ℓ : TorusLumps.StepParameters) (hfits : ℓ.Admissible) (t : ℕ) {C : ℝ}
    (hfam : TorusLumps.IsCurvatureFamily ℓ C (ShareFamilies.levelShareFamily T.a T.L (t + 1)))
    (hcar : TorusLumps.SumInvariantUnderIsometries ℓ (ShareFamilies.levelShareFamily T.a T.L (t + 1)))
    (hsum : ∀ n [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold T.σ V →
      ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V =
        TorusFields.actionAtLevel T.a T.L (t + 1) Finset.univ V) :
    TorusLumps.HasCurvatureForm (ShareFamilies.levelShareFamily T.a T.L (t + 1)) 1 := by
  obtain ⟨γ₂, hγ₂, hLA₂⟩ := h7 T.a T.L T.chainParams hdr.one_le_a hdr.odd_L hdr.chain_admissible
  obtain ⟨γ₁, hγ₁, hAb⟩ := h8 T.L hdr.odd_L
  obtain ⟨γ₀, hγ₀, hγe⟩ : ∃ γ₀, 0 < γ₀ ∧ γ₀ = min γ₂ γ₁ := ⟨_, lt_min hγ₂ hγ₁, rfl⟩
  have hLA : ∀ (t n l : ℕ) [NeZero n] (X : BlockAverages.imaginaryQuaternions) (μ ν : Fin 4), 64 ≤ n → ‖X‖ = 1 →
      μ < ν → 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      ∃ V : TorusFields.TorusField n,
        TorusLumps.IsAbelianWithCurvature X (PlaneFields.planeForm μ ν) (2 * Real.pi * l / (n : ℝ) ^ 2) V ∧
        TorusFields.actionAtLevel T.a T.L (t + 1) Finset.univ V =
          ((n : ℝ) * (T.L : ℝ) ^ (t + 1)) ^ 4 *
            (1 - Real.cos (2 * Real.pi * l / ((n : ℝ) * (T.L : ℝ) ^ (t + 1)) ^ 2)) := by
    intro t n l _ X μ ν hn hX hμν hg
    rw [hγe] at hg
    refine ⟨ColdStepAtMirrorFrames.restrictToTorus n
        (ColdStepAtMirrorFrames.constantCurvatureChain (TorusFields.torusFrame T.L t n) X μ ν l
          (TorusFields.torusFrame T.L t n).top),
      hAb (TorusFields.torusFrame T.L t n) X μ ν n l rfl (fun _ => rfl) hn hX hμν (hg.trans (min_le_right _ _)), ?_⟩
    have h := (hLA₂ (TorusFields.torusFrame T.L t n) X μ ν n l rfl (fun _ => rfl) hn hX hμν
      (hg.trans (min_le_left _ _))).2
    show BlockAverages.minimalAction T.a
      (TorusFields.cellsOfSites (TorusFields.torusFrame T.L t n) (Finset.univ : Finset (TorusFields.TorusSite n)))
      (t + 1) (TorusFields.readAtLevel (TorusFields.torusFrame T.L t n) (t + 1) _) = _
    rw [cellsOfSites_univ, readAtLevel_restrictToTorus]
    exact h
  obtain ⟨hT, b, hb⟩ := h5 ℓ hfits _ _ hfam hcar
  have hLim : TorusLumps.HasLimitSecondDeriv (ShareFamilies.levelShareFamily T.a T.L (t + 1)) :=
    fun c c' X X' => ⟨_, hT c c' X X'⟩
  obtain ⟨-, -, -, -, -, -, -, hE⟩ := h6 ℓ hfits _ _ hfam
  obtain ⟨v, hv, hvε⟩ := hE (PlaneFields.planeForm 0 1) 1 TorusLumps.quaternionI planeForm_antisymm one_pos
    planeForm_integral norm_quaternionI
  rw [curvatureAlong_quaternionI] at hv
  have hb1 := hb TorusLumps.unitPlaneCurvature TorusLumps.unitPlaneCurvature unitPlaneCurvature_antisymm
    unitPlaneCurvature_antisymm
  rw [curvaturePairing_unit, mul_one] at hb1
  have hvb : v = b := hv.unique hb1
  have hv1 : v = 1 := by
    by_contra hne
    have hpos : 0 < |1 - v| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
    set ε := |1 - v| / 4 with hεdef
    have hε0 : 0 < ε := by positivity
    obtain ⟨n₁, hn₁⟩ := hvε ε hε0
    have hc : 0 < min γ₀ (min 1 ε) := lt_min hγ₀ (lt_min one_pos hε0)
    obtain ⟨n, hg, hcold1, hnn, hn1, hn64⟩ :=
      ((tendsto_plane_angle.eventually (gt_mem_nhds hc)).and
        ((tendsto_plane_angle.eventually (eventually_expUnit_near_one TorusLumps.quaternionI hdr.σ_pos)).and
          ((Filter.eventually_ge_atTop T.n₀).and
            ((Filter.eventually_ge_atTop n₁).and (Filter.eventually_ge_atTop 64))))).exists
    have : NeZero n := ⟨by omega⟩
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγdef
    have hγ0 : 0 ≤ γ := by positivity
    have hg0 : γ ≤ γ₀ := le_of_lt (lt_of_lt_of_le hg (min_le_left _ _))
    have hg2 : γ < 1 := lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_left _ _))
    have hg3 : γ < ε := lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨V, hV, hact⟩ := hLA t n 1 TorusLumps.quaternionI 0 1 hn64 norm_quaternionI (by decide) hg0
    have hcold : TorusFields.IsCold T.σ V := by
      intro x μ ν hμν
      unfold TorusFields.curvature
      rw [hV.2 x μ ν hμν]
      by_cases h01 : μ = 0 ∧ ν = 1
      · have e : γ * PlaneFields.planeForm 0 1 μ ν = γ := by simp [PlaneFields.planeForm, h01.1, h01.2]
        rw [e]
        exact hcold1
      · have e : PlaneFields.planeForm 0 1 μ ν = 0 := by
          unfold PlaneFields.planeForm
          rw [if_neg h01, if_neg]
          rintro ⟨rfl, rfl⟩
          exact absurd hμν (by decide)
        rw [e, mul_zero, zero_smul]
        simpa [BlockAverages.expUnit] using hdr.σ_pos
    have hs := hsum n hnn V hcold
    rw [hact] at hs
    have hY := fun Y => hn₁ n hn1 V hV Y
    have hcard : (Fintype.card (TorusFields.TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
      simp [ZMod.card]
    have hsumb : |∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V -
        (n : ℝ) ^ 4 * (γ ^ 2 / 2 * v)| ≤ (n : ℝ) ^ 4 * (ε * γ ^ 2) := by
      have e1 : ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V -
          (n : ℝ) ^ 4 * (γ ^ 2 / 2 * v) =
          ∑ z : TorusFields.TorusSite n,
            (TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V - γ ^ 2 / 2 * v) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun z _ => hY z).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    set N : ℝ := (T.L : ℝ) ^ (t + 1) with hN
    have hN1 : 1 ≤ N := one_le_pow₀ (by exact_mod_cast (hdr.odd_L.pos : 1 ≤ T.L))
    set θ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / ((n : ℝ) * N) ^ 2 with hθdef
    have hθ0 : 0 ≤ θ := by positivity
    have hθγ : θ ≤ γ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : (n : ℝ) ≤ (n : ℝ) * N := le_mul_of_one_le_right hnpos.le hN1
      exact pow_le_pow_left₀ hnpos.le this 2
    have hNpos : 0 < N := by linarith
    have hMθ : ((n : ℝ) * N) ^ 2 * θ = 2 * Real.pi := by
      rw [hθdef, Nat.cast_one]
      field_simp
    have hnγ : (n : ℝ) ^ 2 * γ = 2 * Real.pi := by
      rw [hγdef, Nat.cast_one]
      field_simp
    have hfin := abs_one_sub_le_of_action (M := (n : ℝ) * N) (n := (n : ℝ)) (θ := θ) (γ := γ) (ε := ε) (v := v)
      (A := ∑ z, TorusLumps.centered (ShareFamilies.levelShareFamily T.a T.L (t + 1)) n z V)
      hMθ hnγ hθ0 (by linarith) hθγ (by nlinarith) hs hsumb
    have : |1 - v| ≤ 3 / 4 * |1 - v| := by
      rw [hεdef] at hfin
      linarith
    linarith
  rw [hv1] at hvb
  refine ⟨hLim, fun A A' hA hA' => ?_⟩
  rw [hvb]
  exact hb A A' hA hA'
end AlongParameters
open AlongParameters in
theorem sharesBoundedAlongParameters_holds (h2 : TorusLumps.PotentialSumsFinite)
    (h3 : ColdStepAtMirrorFrames.sumCellSharesEqAction) (h4 : BlockAverages.flatTopVanishingStatement)
    (h5 : TorusLumps.InvariantFamilyCurvatureForm) (h6 : TorusLumps.SecondOrderAtAbelianFields)
    (h7 : ColdStepAtMirrorFrames.constantCurvatureMinimalActionStatement)
    (h8 : TorusLumps.TopOfConstantCurvatureChainIsAbelian) : ShareFamilies.SharesBoundedAlongParameters := by
  unfold ShareFamilies.SharesBoundedAlongParameters ColdStepAtMirrorFrames.EventuallyOrdered
  refine ColdStepAtMirrorFrames.EventuallyInParameters.mono eventually_ceilings ?_
  rintro T ⟨hκ, hσA, hσ1⟩ hdr _ ℓ hm hfits t
  obtain ⟨hfam, hcar, han, hdec, hsum⟩ := share_bounds h2 h3 h4 T hdr hκ hσA hσ1 ℓ hm hfits t
  exact ⟨hfam, hcar, curvature_form_one h5 h6 h7 h8 T hdr ℓ hfits t hfam hcar hsum, han,
    fun n _ hn y W hW k c X h4' _ hX => hdec n hn y W hW k c X (by omega) hX⟩
end YangMills.Construction.ShareFamilies
end
