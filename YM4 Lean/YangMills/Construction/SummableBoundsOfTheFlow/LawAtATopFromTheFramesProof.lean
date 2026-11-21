import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSizedSumsProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.LawAtATopFromTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation Estimates FamilyNorms SmoothSlices
  ConvexObservables
namespace LawAtTop
variable {F : BlockFrame}
section Sizes
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem ballDensity_congr_on_ball {ρ : ℝ} {p : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = Ψ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by apply _root_.YangMills.Construction.Cumulants.SizedSums.ballDensity_congr <;> assumption
theorem pow_le_pow_of_abs_le {B B' : ℝ} (q : ℕ) (h : |B| ≤ B') : B ^ q ≤ B' ^ q :=
  (le_abs_self _).trans ((abs_pow B q).le.trans (pow_le_pow_left₀ (abs_nonneg _) h q))
theorem hasLocalSize_mono {ρ x κ h h' : ℝ} {r : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ} {Cz : ℕ → ℝ} {dZ : ι → ℝ}
    {H : BondField ι → ℝ} (hd : ballDensity r Φ = ballDensity r Ψ) (h0 : 0 ≤ h) (hle : h ≤ h')
    (hs : HasLocalSize ρ r Φ Cz x κ h dZ H) : HasLocalSize ρ r Ψ (fun q => |Cz q|) x κ h' dZ H := by
  obtain ⟨hd1, H₀, hm⟩ := hs
  refine ⟨hd1, H₀, fun q hq => ?_⟩
  obtain ⟨⟨i1, m1⟩, hg⟩ := hm q hq
  have hmean : ∀ u : BondField ι → ℝ, ballExpectation r Φ u = ballExpectation r Ψ u := fun u => by
    simp only [ballExpectation, hd]
  refine ⟨⟨by rw [← hd]; exact i1, ?_⟩, fun b => ?_⟩
  · rw [← hmean]
    refine m1.trans (pow_le_pow_of_abs_le q ?_)
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  · obtain ⟨i2, m2⟩ := hg b
    refine ⟨by rw [← hd]; exact i2, ?_⟩
    rw [← hmean]
    refine m2.trans (pow_le_pow_of_abs_le q ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg h0,
      abs_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hle (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg x))
theorem hasLocalSize_neg {ρ x κ h : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Cz : ℕ → ℝ} {dZ : ι → ℝ}
    {H : BondField ι → ℝ} (hs : HasLocalSize ρ r Ψ Cz x κ h dZ H) :
    HasLocalSize ρ r Ψ Cz x κ h dZ (fun η => - H η) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.hasLocalSize_neg <;> assumption
end Sizes
theorem hasBoundedDerivatives_of_isNormBoundedLocalFamily {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
theorem extendByZero_id (ζ : StepVariable (finiteCells F)) :
    _root_.YangMills.Construction.Interpolation.extendByZero (F := F) (id : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F))) Finset.univ ζ = ζ := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
set_option maxHeartbeats 1600000 in
theorem lawAtTopFromInterpolatedFrames_holds (hS : IteratedFDerivSlices)
    (hEnds : interpolationAtEndpoints) (hJ : JointlyContDiffOnBallsOfDisplacements)
    (hBonds : cellBondsCardStatement) (hLaw : normalizedBallLawIsProbabilityStatement)
    (hSites : SiteDecomposition) : lawAtTopFromInterpolatedFrames := by
  classical
  intro T Cq Cz Cr C Ck hT t x ε φ h star F V hx hε hφ hh hF hV
  have hD := hT.ordered
  have hκ := hD.κ_pos
  have hσ := hD.σ_pos
  have hη₃ := hD.η₃_pos
  have hη₁ := hD.η₃_le_one
  have hE1 : 1 ≤ T.E := hD.one_le_E
  have hCs : 1 ≤ T.Cs := hT.one_le_Cs
  have hCs0 : 0 ≤ T.Cs := by linarith
  have hx1 : 1 ≤ x := hT.one_le_coupling.trans hx
  have hx0 : 0 < x := by linarith
  have hρ : 0 < T.σ / 64 := by positivity
  have hlam : 0 < T.chainParams.lam := hD.chain_admissible.positivity.2.2.1
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
  have hn2 : 2 ≤ n := hT.two_le.trans hn
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    exact hn2
  have hodd : Odd F.blockSide := by
    rw [hFL]
    exact hD.odd_L
  have hfin : Finite F.Cell := by
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have hmem : ∀ Y : F.Cell, Y ∈ finiteCells F := fun Y => by
    unfold finiteCells
    rw [dif_pos hfin]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) Y
  set s : ℝ := segmentEnd star with hs
  have hs0 : 0 ≤ s := by
    simp only [hs, segmentEnd]
    split_ifs <;> norm_num
  have hs1 : s ≤ 1 := by
    simp only [hs, segmentEnd]
    split_ifs <;> norm_num
  set m := frameRadius x with hm
  have hrow : ∀ (f : LocalFamily) (y : F.Site F.depth),
      interpolatedExpansion s T.a T.chainParams.ρA m f y = centredExpansion star T.a T.chainParams.ρA m f y :=
    fun f y => by
      funext η V'
      exact (hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.1 f y η
  have hblock : ∀ (Y : F.Cell) (V' : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
      interpolatedBlockExponent s T.a T.chainParams.ρA x m Y V' η =
        cellExponent star T.a T.chainParams.ρA x m Y V' η :=
    fun Y V' η => (hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.2.1 Y η
  have hfam : ∀ η, familyLawExponent s T.a T.chainParams.ρA x m φ V η =
      stepExponent star T.a T.chainParams.ρA x m φ 1 V η :=
    fun η => (hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V).2.2.2.2.2.1 φ η
  have expansionJoint : ∀ {ε' ε₃' : ℝ} {f : LocalFamily},
      IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε' ε₃' f → 0 ≤ ε' → 0 ≤ ε₃' →
      ∀ y, JointlyContDiffOnBalls (T.σ / 64) V (centredExpansion star T.a T.chainParams.ρA m f y) := by
    intro ε' ε₃' f hf h0 h3 y
    refine hJ F (T.σ / 64) V _ fun η hη l j b u c X hu hX => ?_
    have tr := hT.transport x t 3 _ f F V s η hx le_rfl (by norm_num)
      (fun j => by split_ifs <;> assumption) (hasBoundedDerivatives_of_isNormBoundedLocalFamily hf) hF hV hs0 hs1 hη
    have h3' := tr.smooth y l j b u c X hu hX
    rw [hrow] at h3'
    exact_mod_cast h3'
  have hε₃ : 0 < ε / T.η₃ := by positivity
  have hE₃ : 0 < T.E / T.η₃ := by positivity
  have hE0 : 0 < T.E := by linarith
  have expansionφ := expansionJoint hφ hE0.le hE₃.le
  have rowh := expansionJoint hh hε.le hε₃.le
  obtain ⟨hBd, hB4⟩ := hT.exponents t x F V star hx hF hV
  have hAdm : (⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x m φ V⟩ :
      LawOnBondVariables ↥(chordBonds (finiteCells F))).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x
        T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ m
        (fun i i' => (cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1) : ℝ)) :=
    ⟨hF, hV, IsIntermediateLaw.ofFamily s φ hs0 hs1 hφ, Function.injective_id, fun _ _ => rfl⟩
  have hw : IsConvexWeights (fun _ : Fin 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
  obtain ⟨hcv, hmom, hobs⟩ := (hT.frames t x hx).laws ↥(chordBonds (finiteCells F))
    (fun i i' => (cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1) : ℝ)) 1 (fun _ => 1) (fun _ => _) hw
    (fun _ => hAdm)
  have obs := hobs _ hAdm
  set Φm := convexCombinationExponent T.chainParams.lam x (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => (⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x m φ V⟩ :
      LawOnBondVariables ↥(chordBonds (finiteCells F)))) with hΦm
  have hΦ : ∀ ζ, Φm ζ = stepExponent star T.a T.chainParams.ρA x m φ 1 V ζ := fun ζ => by
    simp only [hΦm, convexCombinationExponent, LawOnBondVariables.exponent, frozenExponent, extendByZero_id]
    simp [hfam]
  have hag : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.σ / 64) →
      exponentSum star T.a T.chainParams.ρA x m φ η V = Φm η := fun η hη => by
    rw [hΦ]
    have h1 : stepExponent star T.a T.chainParams.ρA x m φ 1 V η =
        stepExponent star T.a T.chainParams.ρA x m (fun _ _ _ => 0) 0 V η -
          ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star T.a T.chainParams.ρA m φ y η V := by
      simp [stepExponent]
    rw [h1, hBd.sum_eq η hη]
    unfold exponentSum
    rw [Fintype.sum_sum_type]
    simp only [exponentTerm, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
    rw [Finset.sum_coe_sort (finiteCells F) (fun Y => cellExponent star T.a T.chainParams.ρA x m Y V η),
      Finset.sum_coe_sort (sitesOfCells (finiteCells F) F.depth)
        (fun y => centredExpansion star T.a T.chainParams.ρA m φ y η V)]
    ring
  have hd : ballDensity (cutoffFactor (T.σ / 64) T.p) Φm =
      ballDensity (cutoffFactor (T.σ / 64) T.p) fun η => exponentSum star T.a T.chainParams.ρA x m φ η V :=
    ballDensity_congr_on_ball fun η hη => (hag η hη).symm
  obtain ⟨Ψ', K, hΨ, hconv, hsl, -⟩ := hcv
  have hSB := hSites F hodd hs2
  have hxw : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hxw0 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hβ : 0 ≤ T.Cs * (1 + T.E / T.η₃) := by positivity
  have hEle : T.E ≤ T.E / T.η₃ := by
    rw [le_div_iff₀ hη₃]
    nlinarith
  have hεle : ε ≤ ε / T.η₃ := by
    rw [le_div_iff₀ hη₃]
    nlinarith
  refine ⟨
    { ρ_pos := hρ
      x_pos := hx0
      κ_pos := hκ
      lam_pos := hlam
      cutoff := hD.cutoff
      α_nonneg := by positivity
      β_nonneg := hβ
      Cq_nonneg := fun q => abs_nonneg _
      convex := ⟨Ψ', K, fun η hη => (hag η hη).trans (hΨ η hη).symm, hconv, hsl⟩
      integrable := ?_
      card_bonds_le := fun z => by
        have := hBonds F hodd hs2 z
        rwa [hFL] at this
      card_places_le := ?_
      mem_cells := hmem
      cell_nonempty := ?_
      smooth_term := ?_
      smooth_expansion := ?_
      third_term := ?_
      size_cell := ?_
      size_site := ?_
      size_expansion := ?_ }, fun b => ?_⟩
  · have hcont : Continuous Ψ' := hconv.smooth.continuous
    have h1 := (hLaw ↥(chordBonds (finiteCells F)) (T.σ / 64) T.p Ψ' hρ hD.cutoff hcont).2.2.2.2.2.2.1
    have h2 : ballDensity (cutoffFactor (T.σ / 64) T.p)
          (fun η => exponentSum star T.a T.chainParams.ρA x m φ η V) =
        ballDensity (cutoffFactor (T.σ / 64) T.p) Ψ' :=
      ballDensity_congr_on_ball fun η hη => (hag η hη).trans (hΨ η hη).symm
    rw [h2]
    exact h1
  · intro u
    rw [← hFL, add_comm, ← Finset.card_insertNone]
    refine Finset.card_le_card_of_injOn
      (fun q => Sum.elim (fun _ => none) (fun y => some (cellOffset y.1)) q) ?_ ?_
    · intro q _
      rcases q with Z | y
      · simp
      · simpa using (hSB.2.1 y.1).2
    · intro q hq q' hq' he
      have hq1 : termCell q = u := by simpa using hq
      have hq2 : termCell q' = u := by simpa using hq'
      rcases q with Z | y <;> rcases q' with Z' | y'
      · have h1 : Z.1 = Z'.1 := hq1.trans hq2.symm
        exact congrArg Sum.inl (Subtype.ext h1)
      · simp at he
      · simp at he
      · have h1 : enclosingCell y.1 = enclosingCell y'.1 := hq1.trans hq2.symm
        have h2 : cellOffset y.1 = cellOffset y'.1 := by simpa using he
        have h3 := (hSB.2.1 y.1).1
        have h4 := (hSB.2.1 y'.1).1
        rw [h1, h2] at h3
        exact congrArg Sum.inr (Subtype.ext (h3.symm.trans h4))
  · intro Y
    have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
      have hL1 : 0 ≤ ((F.blockSide : ℤ) - 1) / 2 := by
        have : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
        omega
      simp only [centredCube, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc]
      intro _
      constructor <;> omega
    have hy := (hSB.1 Y 0 h0).1
    refine ⟨⟨cellCentre F.depth Y + siteOfCoords F.depth 0, ?_⟩, hy⟩
    unfold sitesOfCells
    refine Finset.mem_biUnion.mpr ⟨Y, hmem Y, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
    have : F.top - F.depth = 1 := by simp
    rw [this, pow_one]
    exact h0
  · intro q
    rcases q with Z | y
    · exact fun k c X η hη => hBd.smooth Z.1 η k c X hη
    · exact fun k c X η hη => (expansionφ y.1 k c X η hη).neg
  · intro q
    rcases q with Z | y
    · exact fun k c X η hη => contDiffAt_const
    · exact rowh y.1
  · intro Z c X η hη
    refine ContDiffAt.contDiffWithinAt ?_
    have h4 := hB4 Z.1 3 c X η fun b => (hη b).le
    unfold fieldDeriv bondDeriv
    exact hS.2.1 (Fin 3 → ℝ) (StepVariable (finiteCells F))
      (fun q => cellExponent star T.a T.chainParams.ρA x m Z.1
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2) 3 1
      (fun l => Pi.single l 1) η (by exact_mod_cast h4)
  · intro Z k c X hk hX
    have s1 := obs.exponent_deriv s Z.1 k c X hs0 hs1 hk hX
    have e : (fun ζ : StepVariable (finiteCells F) => bondDeriv (fun V' =>
        interpolatedBlockExponent s T.a T.chainParams.ρA x m Z.1 V' (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ)) V c X) =
        fieldDeriv (exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inl Z)) V c X := by
      funext ζ
      rw [extendByZero_id]
      unfold fieldDeriv
      congr 1
      funext V'
      exact hblock _ _ _
    refine hasLocalSize_mono hd (mul_nonneg hCs0 (Real.exp_pos _).le) ?_ (by rw [← e]; exact s1)
    simp only [termDecayWeight, Sum.elim_inl]
    have e2 : 2 ^ 5 * T.κ * (bondSpan Z.1 c : ℝ) = 2 ^ 4 * T.κ * (2 * (bondSpan Z.1 c : ℝ)) := by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have : 0 ≤ T.E / T.η₃ := hE₃.le
    nlinarith
  · intro y k c X hk hX
    have s1 := obs.expansion_deriv s T.E φ y.1 k c X hs0 hs1 hE0 hφ hk hX
    have e : (fun ζ : StepVariable (finiteCells F) => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA m φ y.1
        (extendByZero id Finset.univ ζ)) V c X) =
        fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y.1) V c X := by
      funext ζ
      rw [extendByZero_id, hrow]
      rfl
    have e3 : fieldDeriv (exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inr y)) V c X =
        fun η => - fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y.1) V c X η := by
      funext η
      unfold fieldDeriv bondDeriv
      have : (fun τ : Fin k → ℝ =>
            exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inr y) η
              (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =
          - fun τ : Fin k → ℝ =>
            centredExpansion star T.a T.chainParams.ρA m φ y.1 η
              (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := rfl
      rw [this, iteratedFDeriv_neg_apply]
      rfl
    rw [e3]
    refine hasLocalSize_neg (hasLocalSize_mono hd ?_ ?_ (by rw [← e]; exact s1))
    · have : 0 ≤ (if k = 2 then T.E / T.η₃ else T.E) := by
        split_ifs
        · exact hE₃.le
        · exact hE0.le
      positivity
    · simp only [termDecayWeight, Sum.elim_inr]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have h1 : (if k = 2 then T.E / T.η₃ else T.E) ≤ 1 + T.E / T.η₃ := by
        split_ifs <;> linarith
      have h0 : 0 ≤ (if k = 2 then T.E / T.η₃ else T.E) := by
        split_ifs
        · exact hE₃.le
        · exact hE0.le
      have h2 : (if k = 2 then T.E / T.η₃ else T.E) * x ^ (-(1 / 2 : ℝ)) ≤ 1 + T.E / T.η₃ := by
        nlinarith
      calc T.Cs * (if k = 2 then T.E / T.η₃ else T.E) * x ^ (-(1 / 2 : ℝ))
          = T.Cs * ((if k = 2 then T.E / T.η₃ else T.E) * x ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ T.Cs * (1 + T.E / T.η₃) := mul_le_mul_of_nonneg_left h2 hCs0
  · intro y k c X hk hX
    have s1 := obs.expansion_deriv s ε h y.1 k c X hs0 hs1 hε hh hk hX
    have e : (fun ζ : StepVariable (finiteCells F) => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA m h y.1
        (extendByZero id Finset.univ ζ)) V c X) =
        fieldDeriv (seriesExpansionTerm star T.a T.chainParams.ρA m h (Sum.inr y)) V c X := by
      funext ζ
      rw [extendByZero_id, hrow]
      rfl
    refine hasLocalSize_mono hd ?_ ?_ (by rw [← e]; exact s1)
    · have : 0 ≤ (if k = 2 then ε / T.η₃ else ε) := by
        split_ifs
        · exact hε₃.le
        · exact hε.le
      positivity
    · refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      refine mul_le_mul_of_nonneg_right ?_ hxw0.le
      refine mul_le_mul_of_nonneg_left ?_ hCs0
      split_ifs
      · exact le_rfl
      · exact hεle
  · have h1 := hmom.moments 1 b
    have e1 : ∀ u : StepVariable (finiteCells F) → ℝ, ballExpectation (cutoffFactor (T.σ / 64) T.p) Φm u =
        ballExpectation (cutoffFactor (T.σ / 64) T.p)
          (fun η => exponentSum star T.a T.chainParams.ρA x m φ η V) u := fun u => by
      simp only [ballExpectation, hd]
    rw [← e1]
    exact show ballExpectation (cutoffFactor T.ballRadius T.p) Φm (fun η => ‖η b‖ ^ 2) ≤ Cq 1 * x⁻¹ from by
      simpa using h1
end LawAtTop
end YangMills.Construction
end
