import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShareFamilies.CurvatureFamilyProof
open TorusFields TorusLumps StepCosts RenormalizationStepParameters ColdStepAtMirrorFrames TopLevelSites
variable {L t n : ℕ}
theorem torusFrame_period_top (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (s : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X s V) =
      BlockAverages.rotatedField (BlockAverages.bondSpread (frameBonds L t c) X s)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.DeltaSharedProofs.p501447 <;> assumption
theorem mixedDeriv_readAtLevel [NeZero n]
    (g : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ) {k : ℕ}
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv (fun W => g (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V c X =
      BlockAverages.mixedBondDerivative g (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
        (frameBonds L t c) X := by apply _root_.YangMills.DeltaSharedProofs.p501924 <;> assumption
theorem natAbs_valMinAbs_cast_sub {m : ℕ} [NeZero n] (h : m = n) (u v : ZMod n) :
    (((((u.cast : ℤ) : ZMod m) - ((v.cast : ℤ) : ZMod m))).valMinAbs).natAbs =
      ((u - v).valMinAbs).natAbs := by apply _root_.YangMills.Construction.TopFamilyEvaluations.natAbs_valMinAbs_cast_sub <;> assumption
theorem cellSupDist_torusSiteInFrame [NeZero n] (y z : TorusSite n) :
    BlockAverages.cellSupDist (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) = supDist y z := by apply _root_.YangMills.Construction.TopFamilyEvaluations.siteSupDist_torusSiteInFrame <;> assumption
theorem mem_cellsOfSites_univ [NeZero n] (z : (torusFrame L t n).Cell) :
    z ∈ cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)) := by
  unfold cellsOfSites
  refine Finset.mem_image.mpr ⟨toTorusSite n z, Finset.mem_univ _, ?_⟩
  exact torusSiteInFrame_toTorusSite torusFrame_period_top z
theorem isOrthantRegular_of_forall_mem {F : BlockAverages.BlockFrame} (S : Finset F.Cell)
    (hS : ∀ z, z ∈ S) (m : ℕ) : BlockAverages.IsOrthantRegular S m := by
  intro z
  exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => hS _⟩
theorem isCold_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : TorusFields.IsCold s V) :
    BlockAverages.IsCold (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
      (torusFrame L t n).top s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  rintro ⟨x, μ, ν⟩ hp
  have hlt : μ < ν := (Finset.mem_filter.mp hp).2.1
  rw [TopLevelSites.plaquetteDefect_readAtLevel_eq torusFrame_period_top]
  exact hV _ μ ν hlt
theorem levelShareFamily_eq (a : ℝ) (L t : ℕ) [NeZero n] (y : TorusSite n) (V : TorusField n) :
    levelShareFamily a L (t + 1) n y V =
      BlockAverages.minimalCellShare a
        (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  unfold levelShareFamily
  rw [dif_neg (NeZero.ne n)]
  rfl
theorem expansionWeight_nonneg (rt n₁ : ℝ) (m : ℕ) : 0 ≤ expansionWeight rt n₁ m :=
  mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
theorem actSite_torusSiteInFrame [NeZero n] (g : TorusIsometry) (y : TorusSite n) :
    BlockAverages.CubicSymmetry.actSite ⟨g.axisPerm, g.axisSign, g.offset⟩ (torusFrame L t n).top
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (g.mapSite y) := by apply _root_.YangMills.SharedProofs.p75600 <;> assumption
theorem transportsField_readAtLevel [NeZero n] (g : TorusIsometry) {W W' : TorusField n}
    (h : g.Transports W W') :
    BlockAverages.CubicSymmetry.TransportsField (F := torusFrame L t n)
      ⟨g.axisPerm, g.axisSign, g.offset⟩
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W') := by apply _root_.YangMills.SharedProofs.p26341 <;> assumption
theorem isCold_translate [NeZero n] {s : ℝ} {W : TorusField n} (hW : TorusFields.IsCold s W)
    (u : TorusSite n) : TorusFields.IsCold s (TorusFields.translate u W) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.isCold_translate <;> assumption
def translationIsometry (u : TorusSite n) : TorusIsometry :=
  ⟨1, fun _ => 1, fun i => ((u i).cast : ℤ), fun _ => Or.inl rfl⟩
theorem translationIsometry_mapSite [NeZero n] (u x : TorusSite n) :
    (translationIsometry u).mapSite x = x + u := by
  funext i
  simp [TorusIsometry.mapSite, translationIsometry]
theorem translationIsometry_transports [NeZero n] (u : TorusSite n) (W : TorusField n) :
    (translationIsometry u).Transports (TorusFields.translate u W) W := by
  intro x k
  have hs : (translationIsometry u).axisSign ((translationIsometry u).axisPerm.symm k) = 1 := rfl
  rw [if_pos hs]
  show W ((translationIsometry u).mapSite x) k = W (x + u) k
  rw [translationIsometry_mapSite]
theorem rt_div_le_δ₁_div (T : ParameterAssignment) (hD : T.Admissible) : T.rt / 2 ^ 9 ≤ T.δ₁ / 2 := by
  have h1 := hD.rt_le
  have h2 := hD.δc_le
  have h3 := hD.rt_pos
  have h5 : T.rt ≤ T.δ₁ / 2 ^ 20 := by
    calc T.rt ≤ T.δc / 2 ^ 14 := h1
      _ ≤ (T.δ₁ / 2 ^ 6) / 2 ^ 14 := by gcongr
      _ = T.δ₁ / 2 ^ 20 := by ring
  norm_num at h5 ⊢
  linarith
theorem weight_pos (p : _root_.YangMills.Construction.TorusLumps.StepParameters) (m : ℕ) : 0 < p.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem exp_le_weightGrowthSup_div_weight (h2 : PotentialSumsFinite) (T : ParameterAssignment)
    (hD : T.Admissible) (y : ℝ) (hF : (T.stepParameters y).Admissible) (D m : ℕ) (hm : m ≤ 2 * D) :
    Real.exp (-T.δ₁ * D) ≤ weightGrowthSup T.rt T.n₁ / (T.stepParameters y).weight m := by
  obtain ⟨-, -, -, hle, -, -, -⟩ := h2 T.rt T.n₁ hD.rt_pos hF.n₁_pos
  rw [le_div_iff₀ (weight_pos _ m)]
  refine le_trans ?_ (hle m)
  have e : (T.stepParameters y).weight m = expansionWeight T.rt T.n₁ m := rfl
  rw [e, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (expansionWeight_nonneg _ _ _)
  rw [Real.exp_le_exp]
  have hr := rt_div_le_δ₁_div T hD
  have hδ := hD.δ₁_pos
  have hm' : (m : ℝ) ≤ 2 * D := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e2 : 2 * (T.rt / 2 ^ 10) * (m : ℝ) = T.rt / 2 ^ 9 * m := by ring
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_right hr hm0]
theorem centered_levelShareFamily (h4 : BlockAverages.flatTopVanishingStatement) (a : ℝ) (ha : 0 ≤ a)
    (hL : Odd L) [NeZero n] (y : TorusSite n) :
    centered (levelShareFamily a L (t + 1)) n y = levelShareFamily a L (t + 1) n y := by apply _root_.YangMills.SharedProofs.p17512 <;> assumption
theorem le_maxOfFirstFour (N : ℕ → ℝ) (k : ℕ) (hk : k ≤ 3) : N k ≤ maxOfFirstFour N := by apply _root_.YangMills.SharedProofs.p3581 <;> assumption
theorem levelSharesFormCurvatureFamily_proof (h2 : PotentialSumsFinite)
    (h3 : sumCellSharesEqAction) (h4 : BlockAverages.flatTopVanishingStatement) :
    LevelSharesFormCurvatureFamily := by
  intro T hD y hy t
  have hF := hD.fits y hy
  obtain ⟨-, -, -, -, -, hσA, -, hN, hch⟩ := hD.chain
  have hσ := hD.σ_pos
  have hσ1 := hD.σ_one
  have hσle : T.threshold ≤ T.σA := by linarith [hD.σ_le]
  have ha0 : 0 ≤ T.coupling := by linarith [hD.a_ge]
  have hodd := hD.L_odd
  have hn₀ := hD.n₀_ge
  have hG0 : 0 ≤ weightGrowthSup T.rt T.n₁ := by
    obtain ⟨-, -, -, -, -, -, hG⟩ := h2 T.rt T.n₁ hD.rt_pos hF.n₁_pos
    linarith
  have hNa : 0 ≤ maxOfFirstFour T.N := (hN 0).le.trans (le_maxOfFirstFour T.N 0 (by norm_num))
  set a := T.coupling with ha
  set L := T.side with hLdef
  have hall : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ z, z ∈ cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)) :=
    fun n _ _ z => mem_cellsOfSites_univ z
  have hamb : ∀ n : ℕ, T.n₀ ≤ n → BlockAverages.IsAdmissibleAmbient (torusFrame L t n) :=
    fun n hn => Or.inr fun i => by
      show 64 ≤ n
      omega
  have main := fun (n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (W : TorusField n)
      (hW : TorusFields.IsCold T.threshold W) =>
    hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
      rfl (hamb n hn) le_rfl (isOrthantRegular_of_forall_mem _ (hall n hn) _) T.threshold
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W) hσ hσle (isCold_readAtLevel hW)
  have hfun : ∀ (n : ℕ) [NeZero n] (z : TorusSite n), levelShareFamily a L (t + 1) n z = fun V =>
      BlockAverages.minimalCellShare a
        (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) :=
    fun n _ z => funext fun V => levelShareFamily_eq a L t z V
  have hcar : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (g : TorusIsometry) (W W' : TorusField n),
      TorusFields.IsCold T.threshold W → g.Transports W W' →
      ∀ z, levelShareFamily a L (t + 1) n (g.mapSite z) W' = levelShareFamily a L (t + 1) n z W := by
    intro n _ hn g W W' hW hC z
    obtain ⟨-, -, hAS, -, -, -⟩ := main n hn W hW
    obtain ⟨-, -, -, -, hIso, -⟩ := hAS
    have := hIso ⟨g.axisPerm, g.axisSign, g.offset⟩
      (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W')
      ⟨g.axisSign_unit, fun _ _ => rfl⟩ (fun _ => ⟨fun _ => hall n hn _, fun _ => hall n hn _⟩)
      (transportsField_readAtLevel g hC) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
    rw [actSite_torusSiteInFrame] at this
    rw [levelShareFamily_eq, levelShareFamily_eq]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn z W hW k c X
    obtain ⟨-, -, hAS, -, -, -⟩ := main n hn W hW
    have hA := hAS.2.1 (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) k
      (frameBonds L t c) X
    have e : (fun s : Fin k → ℝ => levelShareFamily a L (t + 1) n z (perturb c X s W)) =
        fun s => BlockAverages.minimalCellShare a
          (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
          (BlockAverages.rotatedField (BlockAverages.bondSpread (frameBonds L t c) X s)
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) := by
      funext s
      rw [levelShareFamily_eq, readAtLevel_perturb]
    show ContDiffAt ℝ 3 (fun s : Fin k → ℝ => levelShareFamily a L (t + 1) n z (perturb c X s W)) 0
    rw [e]
    exact hA.contDiffAt
  · intro n _ hn z g W hW
    obtain ⟨-, -, hAS, -, -, -⟩ := main n hn W hW
    obtain ⟨-, -, -, hGa, -⟩ := hAS
    have e : readAtLevel (torusFrame L t n) (torusFrame L t n).top (TorusFields.gaugeTransform g W) =
        BlockAverages.gaugeTransform (fun x => g (toTorusSite n x))
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top W) := by
      funext x i
      show g (toTorusSite n x) * W (toTorusSite n x) i * (g (toTorusSite n x + unitStep n i))⁻¹ =
        g (toTorusSite n x) * W (toTorusSite n x) i *
          (g (toTorusSite n (x + BlockAverages.unitStep (torusFrame L t n).top i)))⁻¹
      rw [toTorusSite_add torusFrame_period_top, toTorusSite_unitStep torusFrame_period_top]
    rw [levelShareFamily_eq, levelShareFamily_eq, e]
    exact hGa _ _
  · intro n _ hn z u W hW
    have := hcar n hn (translationIsometry u) (TorusFields.translate u W) W (isCold_translate hW u)
      (translationIsometry_transports u W) z
    rw [translationIsometry_mapSite] at this
    exact this.symm
  · intro n _ hn z W hW k c X hk1 hk3 hX
    obtain ⟨-, -, hAS, -, -, -⟩ := main n hn W hW
    obtain ⟨-, -, -, -, -, -, hDec, -⟩ := hAS
    have hb := hDec (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) k
      (frameBonds L t c) X hk1 hX
    rw [hfun n z, mixedDeriv_readAtLevel (fun V => BlockAverages.minimalCellShare a
        (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) V)]
    have hD' : BlockAverages.bondListDistance
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) (frameBonds L t c) =
        Finset.univ.sup fun l => supDist z (c l).1 := by
      unfold BlockAverages.bondListDistance
      congr 1
      funext l
      exact cellSupDist_torusSiteInFrame z (c l).1
    rw [hD'] at hb
    set D := Finset.univ.sup fun l => supDist z (c l).1 with hDdef
    have hlz : ∀ l, supDist z (c l).1 ≤ D := fun l =>
      Finset.le_sup (f := fun l => supDist z (c l).1) (Finset.mem_univ l)
    have hm : supportDiam z c ≤ 2 * D := by
      unfold supportDiam
      refine max_le ((Finset.sup_le fun l _ => hlz l).trans (by omega)) (Finset.sup_le fun l _ =>
        Finset.sup_le fun l' _ => ?_)
      have h1 := supDist_triangle (c l).1 z (c l').1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm (c l).1 z] at h1
      have := hlz l
      have := hlz l'
      omega
    have he := exp_le_weightGrowthSup_div_weight h2 T hD y hF D (supportDiam z c) hm
    refine hb.trans ?_
    have hNk : T.N k ≤ maxOfFirstFour T.N := le_maxOfFirstFour T.N k hk3
    calc T.N k * Real.exp (-T.δ₁ * D)
        ≤ maxOfFirstFour T.N *
          (weightGrowthSup T.rt T.n₁ / (T.stepParameters y).weight (supportDiam z c)) :=
          mul_le_mul hNk he (Real.exp_pos _).le hNa
      _ = _ := by ring
  · intro n n' _ _ hn hn' z z' W W' m h1 h1' hW hW' hA k b X hk hb hX
    have e1 : centered (levelShareFamily a L (t + 1)) n z = levelShareFamily a L (t + 1) n z :=
      centered_levelShareFamily h4 a ha0 hodd z
    have e2 : centered (levelShareFamily a L (t + 1)) n' z' = levelShareFamily a L (t + 1) n' z' :=
      centered_levelShareFamily h4 a ha0 hodd z'
    rw [e1, e2, hfun n z, hfun n' z',
      mixedDeriv_readAtLevel (fun V => BlockAverages.minimalCellShare a
        (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) V),
      mixedDeriv_readAtLevel (fun V => BlockAverages.minimalCellShare a
        (cellsOfSites (torusFrame L t n') (Finset.univ : Finset (TorusSite n')))
        (torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top z') V)]
    obtain ⟨-, -, -, -, -, hloc⟩ := main n hn W hW
    have hag : BlockAverages.AgreeOnBall
        (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
        (cellsOfSites (torusFrame L t n') (Finset.univ : Finset (TorusSite n')))
        (readAtLevel (torusFrame L t n') (torusFrame L t n').top W')
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
        (torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top z') m := by
      refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h1',
        fun _ _ => ⟨fun _ => hall n' hn' _, fun _ => hall n hn _⟩, fun c hc => ?_⟩
      have := hA c hc
      show W (toTorusSite n _) c.2 = W' (toTorusSite n' _) c.2
      rw [toTorusSite_add torusFrame_period_top, toTorusSite_add torusFrame_period_top,
        toTorusSite_torusSiteInFrame torusFrame_period_top,
        toTorusSite_torusSiteInFrame torusFrame_period_top,
        toTorusSite_siteOfCoords torusFrame_period_top, toTorusSite_siteOfCoords torusFrame_period_top]
      exact this
    have hl := (hloc (torusFrame L t n')
      (cellsOfSites (torusFrame L t n') (Finset.univ : Finset (TorusSite n')))
      (readAtLevel (torusFrame L t n') (torusFrame L t n').top W') _ _ m rfl rfl (hamb n' hn')
      (isOrthantRegular_of_forall_mem _ (hall n' hn') _) (isCold_readAtLevel hW') hag).1 k b X hb hX
    have eb : ∀ (N : ℕ) [NeZero N] (v : TorusSite N),
        (frameBonds L t fun l => bondFrom v (b l)) =
          BlockAverages.offsetBonds (torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top v) b := by
      intro N _ v
      funext l
      refine Prod.ext ?_ rfl
      show torusSiteInFrame (torusFrame L t N) (torusFrame L t N).top (v + siteOfInt (b l).1) =
        _ + BlockAverages.siteOfCoords _ (b l).1
      rw [torusSiteInFrame_add torusFrame_period_top, torusSiteInFrame_siteOfInt torusFrame_period_top]
    rw [eb n z, eb n' z']
    refine hl.trans ?_
    have he := exp_le_weightGrowthSup_div_weight h2 T hD y hF m m (by omega)
    have hNk : T.N k ≤ maxOfFirstFour T.N := le_maxOfFirstFour T.N k (by omega)
    have hf : BlockAverages.derivativeScale T.threshold k ≤ 1 := by
      unfold BlockAverages.derivativeScale
      split_ifs
      · nlinarith
      · exact hσ1
      · exact le_rfl
    have hf0 : 0 ≤ BlockAverages.derivativeScale T.threshold k := by
      unfold BlockAverages.derivativeScale
      split_ifs <;> positivity
    have hp : BlockAverages.derivativeScale T.threshold k * T.N k ≤ maxOfFirstFour T.N := by
      nlinarith [hN k]
    calc BlockAverages.derivativeScale T.threshold k * T.N k * Real.exp (-T.δ₁ * m)
        ≤ maxOfFirstFour T.N * (weightGrowthSup T.rt T.n₁ / (T.stepParameters y).weight m) :=
          mul_le_mul hp he (Real.exp_pos _).le hNa
      _ = _ := by ring
  · intro n _ hn g W W' hW hW' hC
    have e1 : ∀ V : TorusField n, ∑ z, centered (levelShareFamily a L (t + 1)) n z V =
        ∑ z, levelShareFamily a L (t + 1) n z V := by
      intro V
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [centered_levelShareFamily h4 a ha0 hodd z]
    rw [e1, e1]
    have hbij : Function.Bijective (g.mapSite (n := n)) :=
      Finite.injective_iff_bijective.mp (mapSite_injective g)
    rw [← (Equiv.ofBijective _ hbij).sum_comp (fun z => levelShareFamily a L (t + 1) n z W')]
    exact Finset.sum_congr rfl fun z _ => hcar n hn g W W' hW hC z
  · intro n _ hn V hV
    have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun i => by
      show 2 ≤ n
      omega
    have hw : cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)) =
        finiteCells (torusFrame L t n) := by
      ext z
      exact ⟨fun _ => TopLevelSites.mem_finiteCells (fun i => by have := hs i; omega) z,
        fun _ => hall n hn z⟩
    have h5 := (h3 (torusFrame L t n) a (fun _ _ => 0)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ha0 hodd hs).1
    have e1 : ∑ z, centered (levelShareFamily a L (t + 1)) n z V =
        ∑ z, levelShareFamily a L (t + 1) n z V :=
      Finset.sum_congr rfl fun z _ => by rw [centered_levelShareFamily h4 a ha0 hodd z]
    rw [e1]
    show _ = BlockAverages.minimalAction a
      (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n))) (t + 1)
      (readAtLevel (torusFrame L t n) (t + 1) V)
    rw [hw]
    have h6 : ∑ Y ∈ finiteCells (torusFrame L t n),
          BlockAverages.minimalCellShare a (finiteCells (torusFrame L t n)) Y
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) =
        BlockAverages.minimalAction a (finiteCells (torusFrame L t n)) (t + 1)
          (readAtLevel (torusFrame L t n) (t + 1) V) := h5
    rw [← h6]
    refine Finset.sum_bij (fun z _ => torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z)
      (fun z _ => TopLevelSites.mem_finiteCells (fun i => by have := hs i; omega) _) ?_ ?_ ?_
    · intro z _ z' _ h
      have := congrArg (toTorusSite n) h
      rwa [toTorusSite_torusSiteInFrame torusFrame_period_top,
        toTorusSite_torusSiteInFrame torusFrame_period_top] at this
    · intro w _
      exact ⟨toTorusSite n w, Finset.mem_univ _, torusSiteInFrame_toTorusSite torusFrame_period_top w⟩
    · intro z _
      rw [levelShareFamily_eq, hw]
end YangMills.Construction.ShareFamilies.CurvatureFamilyProof
end
