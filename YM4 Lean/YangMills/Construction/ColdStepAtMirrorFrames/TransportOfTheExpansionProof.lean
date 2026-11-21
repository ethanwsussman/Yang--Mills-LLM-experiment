import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAboveTheFrameIsLocal
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAboveTheFrameIsSmooth
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionFarFromItsBlock
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearAFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfTheExpansionAtAFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.TransportParameters
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import YangMills.Construction.SummableBoundsOfTheFlow.TopOrderNearTheBlock
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ExpansionTransport
variable {F : BlockFrame}
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem torusDecayFactor_mono (L : ℕ) {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ y := by
  unfold torusDecayFactor
  have hn : 0 ≤ (L : ℝ) ^ (1 / 640 : ℝ) := by positivity
  have h1 : (x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ (y / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 :=
    pow_le_pow_left₀ (div_nonneg hx hn) (by gcongr) _
  have h2 : Real.exp (δ * x) ≤ Real.exp (δ * y) := Real.exp_le_exp.mpr (by gcongr)
  have h3 : max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) ≤ max 1 ((y / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
    max_le_max le_rfl h1
  exact mul_le_mul h3 h2 (Real.exp_pos _).le (le_trans zero_le_one (le_max_left _ _))
theorem bondListDistance_le_bondSpan {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondListDistance Y c ≤ bondSpan Y c := le_max_left _ _
theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_zero {G : BlockFrame} {j : ℕ} : (siteOfCoords j (0 : Fin 4 → ℤ) : G.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
theorem axialGaugeRotated_areUnitVectors {k : ℕ} (V : F.GaugeField F.top) (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    AreUnitVectors (axialGaugeRotated V Y c X) := fun l => by
  show ‖adjointAction _ _‖ = 1
  rw [norm_adjointAction]
  exact hX l
theorem far_tail_bound {Ct A Gn E : ℝ} (h : 2 ^ 10 * Ct * Gn * A ≤ 1) (hG : 0 < Gn) (hE : 0 ≤ E) :
    Ct * E * A ≤ 2⁻¹ ^ 10 * E / Gn := by
  rw [le_div_iff₀ hG]
  nlinarith [mul_le_mul_of_nonneg_left h hE]
theorem rpow_neg_quarter_le {L : ℕ} (h : 2 ^ 40 ≤ L) : (L : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2⁻¹ ^ 10 := by
  have h1 : ((2 : ℝ) ^ 40) ≤ L := by exact_mod_cast h
  have h2 : (((2 : ℝ) ^ 40) ^ (1 / 4 : ℝ)) ≤ (L : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h3 : (((2 : ℝ) ^ 40) ^ (1 / 4 : ℝ)) = 2 ^ 10 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h3] at h2
  rw [Real.rpow_neg (Nat.cast_nonneg L)]
  rw [inv_pow]
  exact inv_anti₀ (by positivity) h2
def stepOffset (st : PathStep) : Fin 4 → ℤ := Pi.single st.1 (if st.2 then 1 else -1)
section Agreement
variable {F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem add_stepDisplacement {j : ℕ} (G : BlockFrame) (st : PathStep) (o : Fin 4 → ℤ) (z : G.Site j) :
    z + siteOfCoords j o + stepDisplacement j st = z + siteOfCoords j (o + stepOffset st) := by
  rw [siteOfCoords_add, add_assoc]
  congr 2
  unfold stepDisplacement stepOffset unitStep
  cases st.2
  · simp only [Bool.false_eq_true, if_false]
    funext i
    simp only [siteOfCoords, Pi.neg_apply]
    by_cases h : i = st.1
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · simp only [if_true]
theorem linkValue_eq_of_agree
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (o : Fin 4 → ℤ) (st : PathStep) (hb : WithinRadius r o) (hb' : WithinRadius r (o + stepOffset st)) :
    linkValue V (Y + siteOfCoords F.top o) st = linkValue V' (Y' + siteOfCoords F'.top o) st := by
  obtain ⟨k, s⟩ := st
  cases s
  · have hB : BondWithinRadius r (o + stepOffset (k, false), k) := by
      refine ⟨hb', ?_⟩
      have : o + stepOffset (k, false) + Pi.single k 1 = o := by
        funext i
        by_cases h : i = k
        · subst h; simp [stepOffset]
        · simp [stepOffset, Pi.single_eq_of_ne h]
      show WithinRadius r (o + stepOffset (k, false) + Pi.single k 1)
      rw [this]; exact hb
    have e := hag _ hB
    simp only at e
    have p1 := add_stepDisplacement F (k, false) o Y
    have p2 := add_stepDisplacement F' (k, false) o Y'
    simp only [linkValue, Bool.false_eq_true, if_false]
    have q1 : Y + siteOfCoords F.top o - unitStep F.top k = Y + siteOfCoords F.top (o + stepOffset (k, false)) := by
      rw [← p1]; simp [stepDisplacement, sub_eq_add_neg]
    have q2 : Y' + siteOfCoords F'.top o - unitStep F'.top k =
        Y' + siteOfCoords F'.top (o + stepOffset (k, false)) := by
      rw [← p2]; simp [stepDisplacement, sub_eq_add_neg]
    rw [q1, q2, e]
  · have hB : BondWithinRadius r (o, k) := ⟨hb, by simpa [stepOffset] using hb'⟩
    simpa [linkValue] using hag _ hB
theorem pathHolonomy_replicate_eq
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (st : PathStep) (n : ℕ) : ∀ (o : Fin 4 → ℤ) (rest : List PathStep), WithinRadius r o →
      WithinRadius r (o + (n : ℤ) • stepOffset st) →
      pathHolonomy V (Y + siteOfCoords F.top (o + (n : ℤ) • stepOffset st)) rest =
        pathHolonomy V' (Y' + siteOfCoords F'.top (o + (n : ℤ) • stepOffset st)) rest →
      pathHolonomy V (Y + siteOfCoords F.top o) (List.replicate n st ++ rest) =
        pathHolonomy V' (Y' + siteOfCoords F'.top o) (List.replicate n st ++ rest) := by
  induction n with
  | zero =>
    intro o rest _ _ h
    simpa using h
  | succ n ih =>
    intro o rest h0 h1 h
    have hmid : WithinRadius r (o + stepOffset st) := by
      intro i
      have a0 := h0 i
      have a1 := h1 i
      simp only [abs_le, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a0 a1 ⊢
      have hs : stepOffset st i = 0 ∨ stepOffset st i = 1 ∨ stepOffset st i = -1 := by
        unfold stepOffset
        by_cases hi : i = st.1
        · subst hi
          cases st.2 <;> simp
        · simp [Pi.single_eq_of_ne hi]
      push_cast at a1
      rcases hs with e | e | e <;> rw [e] at a1 ⊢ <;> constructor <;> nlinarith [a0.1, a0.2, a1.1, a1.2]
    have e : o + stepOffset st + (n : ℤ) • stepOffset st = o + ((n + 1 : ℕ) : ℤ) • stepOffset st := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have := ih (o + stepOffset st) rest hmid (by rw [e]; exact h1) (by rw [e]; exact h)
    show pathHolonomy V (Y + siteOfCoords F.top o) (st :: (List.replicate n st ++ rest)) =
      pathHolonomy V' (Y' + siteOfCoords F'.top o) (st :: (List.replicate n st ++ rest))
    simp only [pathHolonomy]
    rw [linkValue_eq_of_agree hag o st h0 hmid, add_stepDisplacement F st o Y, add_stepDisplacement F' st o Y', this]
theorem minimalOffset_add_siteOfCoords {G : BlockFrame} (z : G.Cell) (h : Fin 4 → ℤ) (hb : WithinRadius r h)
    (hs : ∀ i, 2 * r + 2 < G.extent i) : minimalOffset z (z + siteOfCoords G.top h) = h := by
  funext i
  have hp : G.period G.top i = G.extent i := by simp [BlockFrame.period]
  have : NeZero (G.period G.top i) := ⟨by rw [hp]; have := hs i; omega⟩
  show (((z + siteOfCoords G.top h - z : G.Cell)) i).valMinAbs = h i
  have e : ((z + siteOfCoords G.top h - z : G.Cell)) i = ((h i : ℤ) : ZMod (G.period G.top i)) := by
    simp [siteOfCoords]
  rw [e, ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have a := abs_le.mp (hb i)
  have b := hs i
  rw [hp]
  constructor <;> omega
theorem axisPath_eq_replicate (h : Fin 4 → ℤ) : axisPath h 1 =
    List.replicate (h 0).natAbs (0, decide (0 ≤ h 0)) ++
      (List.replicate (h 1).natAbs (1, decide (0 ≤ h 1)) ++
        (List.replicate (h 2).natAbs (2, decide (0 ≤ h 2)) ++
          (List.replicate (h 3).natAbs (3, decide (0 ≤ h 3)) ++ []))) := rfl
theorem natAbs_smul_stepOffset (h : Fin 4 → ℤ) (k : Fin 4) :
    ((h k).natAbs : ℤ) • stepOffset (k, decide (0 ≤ h k)) = Pi.single k (h k) := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp only [stepOffset, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    by_cases h0 : 0 ≤ h i
    · simp [h0, abs_of_nonneg h0]
    · have : h i < 0 := not_le.mp h0
      simp [h0, abs_of_neg this]
  · simp [stepOffset, Pi.single_eq_of_ne hi]
theorem withinRadius_restrict (h : Fin 4 → ℤ) (hb : WithinRadius r h) (S : Finset (Fin 4)) :
    WithinRadius r (fun i => if i ∈ S then h i else 0) := by
  intro i
  by_cases hi : i ∈ S
  · simpa [hi] using hb i
  · simp [hi]
theorem pathHolonomy_axisPath_eq
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (h : Fin 4 → ℤ) (hb : WithinRadius r h) :
    pathHolonomy V Y (axisPath h 1) = pathHolonomy V' Y' (axisPath h 1) := by
  have p0 : (fun i : Fin 4 => if i ∈ (∅ : Finset (Fin 4)) then h i else 0) = 0 := by funext i; simp
  let P : Finset (Fin 4) → Fin 4 → ℤ := fun S i => if i ∈ S then h i else 0
  have step : ∀ (S : Finset (Fin 4)) (k : Fin 4), k ∉ S →
      P S + ((h k).natAbs : ℤ) • stepOffset (k, decide (0 ≤ h k)) = P (insert k S) := by
    intro S k hk
    rw [natAbs_smul_stepOffset]
    funext i
    by_cases hi : i = k
    · subst hi
      simp [P, hk]
    · simp [P, hi, Pi.single_eq_of_ne hi]
  have hP : ∀ S, WithinRadius r (P S) := fun S => withinRadius_restrict h hb S
  have z1 : (Y + siteOfCoords F.top (0 : Fin 4 → ℤ)) = Y := by
    rw [siteOfCoords_zero, add_zero]
  have z2 : (Y' + siteOfCoords F'.top (0 : Fin 4 → ℤ)) = Y' := by
    rw [siteOfCoords_zero, add_zero]
  let S1 : Finset (Fin 4) := insert 0 ∅
  let S2 : Finset (Fin 4) := insert 1 S1
  let S3 : Finset (Fin 4) := insert 2 S2
  have s1 := step ∅ 0 (by decide)
  have s2 := step S1 1 (by decide)
  have s3 := step S2 2 (by decide)
  have s4 := step S3 3 (by decide)
  have e4 := pathHolonomy_replicate_eq (V := V) (V' := V') (Y := Y) (Y' := Y') hag (3, decide (0 ≤ h 3))
    (h 3).natAbs (P S3) [] (hP _) (by rw [s4]; exact hP _) (by simp [pathHolonomy])
  have e3 := pathHolonomy_replicate_eq (V := V) (V' := V') (Y := Y) (Y' := Y') hag (2, decide (0 ≤ h 2))
    (h 2).natAbs (P S2) _ (hP _) (by rw [s3]; exact hP _) (by rw [s3]; exact e4)
  have e2 := pathHolonomy_replicate_eq (V := V) (V' := V') (Y := Y) (Y' := Y') hag (1, decide (0 ≤ h 1))
    (h 1).natAbs (P S1) _ (hP _) (by rw [s2]; exact hP _) (by rw [s2]; exact e3)
  have e1 := pathHolonomy_replicate_eq (V := V) (V' := V') (Y := Y) (Y' := Y') hag (0, decide (0 ≤ h 0))
    (h 0).natAbs (P ∅) _ (hP _) (by rw [s1]; exact hP _) (by rw [s1]; exact e2)
  have hP0 : P ∅ = 0 := p0
  rw [hP0, z1, z2] at e1
  rw [axisPath_eq_replicate]
  exact e1
end Agreement
theorem axialGaugeRotated_eq_of_agree {F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hs : ∀ i, 2 * r + 2 < F.extent i) (hs' : ∀ i, 2 * r + 2 < F'.extent i)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions) (hb : ∀ l, BondWithinRadius r (h l)) :
    axialGaugeRotated V Y (bondsAt Y h) X = axialGaugeRotated V' Y' (bondsAt Y' h) X := by
  funext l
  show adjointAction (axialGaugeHolonomy V Y (Y + siteOfCoords F.top (h l).1)) (X l) =
    adjointAction (axialGaugeHolonomy V' Y' (Y' + siteOfCoords F'.top (h l).1)) (X l)
  unfold axialGaugeHolonomy
  rw [minimalOffset_add_siteOfCoords Y _ (hb l).1 hs, minimalOffset_add_siteOfCoords Y' _ (hb l).1 hs',
    pathHolonomy_axisPath_eq hag _ (hb l).1]
theorem bondListDistance_bondsAt_le {r k : ℕ} (Y : F.Cell) (hs : ∀ i, 2 * r + 2 < F.extent i)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (hb : ∀ l, BondWithinRadius r (h l)) :
    bondListDistance Y (bondsAt Y h) ≤ r := by
  refine Finset.sup_le fun l _ => Finset.sup_le fun i _ => ?_
  have hp : F.period F.top i = F.extent i := by simp [BlockFrame.period]
  have : NeZero (F.period F.top i) := ⟨by rw [hp]; have := hs i; omega⟩
  have a := abs_le.mp ((hb l).1 i)
  have b := hs i
  have e : ((Y - (Y + siteOfCoords F.top (h l).1) : F.Cell)) i =
      ((-(h l).1 i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have hv : (((-(h l).1 i : ℤ) : ZMod (F.period F.top i))).valMinAbs = -(h l).1 i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    rw [hp]
    constructor <;> omega
  show (((Y - (Y + siteOfCoords F.top (h l).1) : F.Cell)) i).valMinAbs.natAbs ≤ r
  rw [e, hv]
  omega
theorem uniformField_isSmallCurvature (G : BlockFrame) (j : ℕ) {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField G j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
theorem mem_finiteCells {G : BlockFrame} (hs : ∀ i, 0 < G.extent i) (z : G.Cell) : z ∈ finiteCells G := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
theorem regularFamily_hasBoundedDerivatives {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hf : IsRegularFamily L t n₀ σ δ E E₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then E₃ else E) f := by
  refine ⟨fun F hF y W hW j c X => ?_, hf.gauge_invariant,
    fun F hF y W j c X hW h1 h3 hX => hf.decay F hF y W j c X hW h1 h3 hX⟩
  have := hf.smooth F hF y W hW j c X
  exact_mod_cast this
theorem interpolatedBlockExpansion_segmentEnd (hends : interpolationAtEndpoints) (star : Bool) (a ρA : ℝ) (m : ℕ)
    (f : LocalFamily) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    interpolatedBlockExpansion (segmentEnd star) a ρA m f Y η = cellCentredExpansion star a ρA m f Y η := by
  funext V
  obtain ⟨_, _, _, h4, _⟩ := hends F star a ρA 0 0 0 m V
  unfold interpolatedBlockExpansion cellCentredExpansion
  exact Finset.sum_congr rfl fun y _ => h4 f y η
theorem expansionTransportAt_of_estimates (hends : interpolationAtEndpoints) (T : StepParameters) {q : ℝ} {Cn : ℕ → ℝ}
    (hqC : q = Cn 3) (hL : TransportConditionsAt T q)
    (h1 : ExpansionNearFlatAt T) (h2 : topOrderNearBlockAt T (decayThresholdIndex (rateParameters T)) Cn)
    (h3 : ExpansionAtFrameLocalityAt T)
    (h4 : ExpansionSecondDerivFlatAt T) (h5 : TopExpansionContDiffAt T)
    (h6 : ExpansionOffBlockDecayAt T) : expansionTransportAt T := by
  intro t x f F V hx hf hF hV star
  obtain ⟨hd, hL40, hCt, hn0, hns, hfar, hη⟩ := hL
  set ns := decayThresholdIndex (rateParameters T) with hnsdef
  have hκ := hd.κ_pos
  have hσ := hd.σ_pos
  have hη0 := hd.η₃_pos
  have hE1 := hd.one_le_E
  have hE0 : 0 < T.E := by linarith
  have hδ : 0 ≤ T.decayRate := by unfold StepParameters.decayRate; positivity
  have hρ : 0 < T.ballRadius := by unfold StepParameters.ballRadius; positivity
  have hE3 : 0 < T.energyRatio := by unfold StepParameters.energyRatio; positivity
  have hEE : T.E = T.η₃ * T.energyRatio := by
    unfold StepParameters.energyRatio
    field_simp
  have hroot := rpow_neg_quarter_le hL40
  have G0 : ∀ y : ℝ, 0 < torusDecayFactor T.L T.decayRate y := torusDecayFactor_pos _ _
  have Gm : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → torusDecayFactor T.L T.decayRate u ≤ torusDecayFactor T.L T.decayRate v :=
    fun hu huv => torusDecayFactor_mono _ hδ hu huv
  have b0 : ∀ (G : BlockFrame), ∀ b, ‖(0 : StepVariable (finiteCells G)) b‖ < T.ballRadius := fun G b => by
    simpa using hρ
  have inv_le : ∀ {u v : ℝ} {A : ℝ}, 0 ≤ A → 0 ≤ u → u ≤ v →
      A / torusDecayFactor T.L T.decayRate v ≤ A / torusDecayFactor T.L T.decayRate u := fun hA hu huv =>
    div_le_div_of_nonneg_left hA (G0 _) (Gm hu huv)
  obtain ⟨Hsize, H1, H2⟩ := h1 t x f F V hx hf hF hV star
  have H6 := h6 t x f F V hx hf hF hV star
  have scale : ∀ {A B u : ℝ}, A ≤ B → 0 ≤ u → 0 < torusDecayFactor T.L T.decayRate u →
      A * T.E / torusDecayFactor T.L T.decayRate u ≤ B * T.E / torusDecayFactor T.L T.decayRate u :=
    fun hAB _ hg => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hE0.le) hg.le
  refine ⟨⟨fun Y η hb => h5 t x f F V hx hf hF hV star Y η hb, ?_, ?_, fun Y η hb => Hsize Y η hb⟩, ?_⟩
  · intro Y k c X hk1 hk2 hX
    have hGn := G0 (bondSpan Y c)
    by_cases hn : ns ≤ bondSpan Y c
    · have a := H6 Y 0 k c X (b0 F) hk1 (by omega) hX
      rw [if_neg (by omega : k ≠ 3)] at a
      have b := far_tail_bound (hfar _ hn) hGn hE0.le
      exact a.trans (b.trans (scale (by norm_num) (by positivity) hGn))
    · have hnlt : bondSpan Y c < ns := not_le.mp hn
      have hld : bondListDistance Y c ≤ T.blockIndex := (bondListDistance_le_bondSpan Y c).trans (by omega)
      have hnn : ((bondSpan Y c : ℕ) : ℝ) ≤ 2 * T.blockIndex := by
        have : bondSpan Y c ≤ 2 * T.blockIndex := by omega
        exact_mod_cast this
      have hG2 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex) ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
        inv_le (by positivity) (by positivity) hnn
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · exact (H1 Y 0 c X (b0 F) hX hld).trans (hG2.trans (scale (by norm_num) (by positivity) hGn))
      · have a := H2 Y 0 c X (b0 F) hX hld
        have b := h4 t (frameRadius x) f F hf hF Y c (axialGaugeRotated V Y c X)
          (axialGaugeRotated_areUnitVectors V Y c X hX)
        have b' : (T.L : ℝ) ^ (-(1 / 4 : ℝ)) * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) ≤
            2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) := scale hroot (by positivity) hGn
        have c1 := abs_sub_abs_le_abs_sub
          (bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0) V c X)
          (bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) f Y 0) (uniformField F F.top) c
            (axialGaugeRotated V Y c X))
        have c2 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
            2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) ≤
            2⁻¹ ^ 6 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
          rw [← add_div, ← add_mul]
          exact scale (by norm_num) (by positivity) hGn
        linarith
  · intro Y η c X hb hX
    have hGn := G0 (bondSpan Y c)
    have hq : 0 ≤ T.energyRatio * (torusDecayFactor T.L T.decayRate (bondSpan Y c))⁻¹ := by positivity
    by_cases hn : ns ≤ bondSpan Y c
    · have a := H6 Y η 3 c X hb (by norm_num) le_rfl hX
      rw [if_pos rfl] at a
      have b := far_tail_bound (hfar _ hn) hGn hE3.le
      refine a.trans (b.trans ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      norm_num
      nlinarith
    · have hnlt : bondSpan Y c < ns := not_le.mp hn
      have hs0 : 0 ≤ segmentEnd star := by unfold segmentEnd; split_ifs <;> norm_num
      have hs1 : segmentEnd star ≤ 1 := by unfold segmentEnd; split_ifs <;> norm_num
      have a := h2 x t 3 (fun j => if j = 3 then T.energyRatio else T.E) f F V (segmentEnd star) η Y c X hx le_rfl
        (by norm_num) (fun j => by split_ifs <;> linarith) (regularFamily_hasBoundedDerivatives hf) hF hV hs0 hs1
        (fun b => (hb b).le) hX hnlt
      rw [interpolatedBlockExpansion_segmentEnd hends] at a
      have hlu : runningMax (fun j => if j = 3 then T.energyRatio else T.E) (3 - 1) = T.E := by
        simp [runningMax, hE0.le]
      rw [hlu, if_pos rfl, ← hqC] at a
      refine a.trans ?_
      have c5 : q * T.E ≤ 2⁻¹ ^ 9 * T.energyRatio := by
        rw [hEE]
        have := mul_le_mul_of_nonneg_right hη hE3.le
        nlinarith
      have c6 : 2⁻¹ ^ 9 * T.energyRatio + q * T.E ≤ 2⁻¹ ^ 6 * T.energyRatio := by nlinarith
      exact div_le_div_of_nonneg_right c6 hGn.le
  · intro F' V' Y Y' r hF' hV' hA k h X hk hb hX
    have hGr := G0 r
    by_cases hr : T.blockIndex ≤ r
    · have a := h3 t x f F V hx hf hF hV star F' V' Y Y' r k h X hF' hV' hA hr hk hb hX
      exact a.trans (scale (by norm_num) (by positivity) hGr)
    · have hrlt : r < T.blockIndex := not_le.mp hr
      obtain ⟨_, _, n, hsn, hnn⟩ := id hF
      obtain ⟨_, _, n', hsn', hnn'⟩ := id hF'
      have hs : ∀ i, 2 * r + 2 < F.extent i := fun i => by
        rcases hA.1 i with e | e
        · have := hsn i; omega
        · exact e
      have hs' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
        rcases hA.2.1 i with e | e
        · have := hsn' i; omega
        · exact e
      obtain ⟨Hs', H1', H2'⟩ := h1 t x f F' V' hx hf hF' hV' star
      have hld : bondListDistance Y (bondsAt Y h) ≤ T.blockIndex :=
        (bondListDistance_bondsAt_le Y hs h hb).trans hrlt.le
      have hld' : bondListDistance Y' (bondsAt Y' h) ≤ T.blockIndex :=
        (bondListDistance_bondsAt_le Y' hs' h hb).trans hrlt.le
      have hrn : (r : ℝ) ≤ T.blockIndex := by exact_mod_cast hrlt.le
      have hr2 : (r : ℝ) ≤ 2 * T.blockIndex := by
        have : r ≤ 2 * T.blockIndex := by omega
        exact_mod_cast this
      have q1 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex) ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate r :=
        inv_le (by positivity) (by positivity) hr2
      have q0 : 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex ≤
          2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate r :=
        inv_le (by positivity) (by positivity) hrn
      have two : ∀ {A B u : ℝ}, 2 * A ≤ B → A * T.E / torusDecayFactor T.L T.decayRate r +
          A * T.E / torusDecayFactor T.L T.decayRate r ≤ B * T.E / torusDecayFactor T.L T.decayRate r :=
        fun h => by
          rw [← add_div, ← add_mul]
          exact scale (by linarith) (by positivity) hGr
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · rw [bondDeriv_zero, bondDeriv_zero]
        have a := abs_le.mp (Hsize Y 0 (b0 F))
        have a' := abs_le.mp (Hs' Y' 0 (b0 F'))
        have c := two (A := 2⁻¹ ^ 8) (B := 2⁻¹ ^ 5) (u := 0) (by norm_num)
        exact abs_le.mpr ⟨by linarith [a.2, a'.1, a.1, a'.2], by linarith [a.2, a'.1, a.1, a'.2]⟩
      · have a := abs_le.mp (H1 Y 0 _ X (b0 F) hX hld)
        have a' := abs_le.mp (H1' Y' 0 _ X (b0 F') hX hld')
        have c := two (A := 2⁻¹ ^ 10) (B := 2⁻¹ ^ 5) (u := 0) (by norm_num)
        exact abs_le.mpr ⟨by linarith [a.2, a'.1, a.1, a'.2], by linarith [a.2, a'.1, a.1, a'.2]⟩
      · have hU := axialGaugeRotated_eq_of_agree hA.2.2.2 hs hs' h X hb
        have a := abs_le.mp (H2 Y 0 _ X (b0 F) hX hld)
        have a' := abs_le.mp (H2' Y' 0 _ X (b0 F') hX hld')
        rw [← hU] at a'
        have hr' : T.blockIndex ≤ T.n₀ / 4 := by omega
        have hbb : ∀ l, BondWithinRadius (T.n₀ / 4) (h l) := fun l => by
          have hre : ((r : ℕ) : ℤ) ≤ ((T.n₀ / 4 : ℕ) : ℤ) := by
            have : r ≤ T.n₀ / 4 := by omega
            exact_mod_cast this
          exact ⟨fun i => ((hb l).1 i).trans hre, fun i => ((hb l).2 i).trans hre⟩
        have hsf : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
        have hsf' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
        have hAg : AgreeOnBall (finiteCells F) (uniformField F F.top) (finiteCells F') (uniformField F' F'.top) Y Y'
            (T.n₀ / 4) := by
          refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun _ _ => ⟨fun _ => mem_finiteCells hsf' _,
            fun _ => mem_finiteCells hsf _⟩, fun _ _ => rfl⟩
          · rw [hsn i]; omega
          · rw [hsn' i]; omega
        have b := abs_le.mp (h3 t x f F (uniformField F F.top) hx hf hF
          (uniformField_isSmallCurvature F F.top (by positivity)) true F'
          (uniformField F' F'.top) Y Y' (T.n₀ / 4) 2 h (axialGaugeRotated V Y (bondsAt Y h) X) hF'
          (uniformField_isSmallCurvature F' F'.top (by positivity)) hAg hr' le_rfl hbb
          (axialGaugeRotated_areUnitVectors V Y _ X hX))
        have hrr : (r : ℝ) ≤ ((T.n₀ / 4 : ℕ) : ℝ) := by
          have : r ≤ T.n₀ / 4 := by omega
          exact_mod_cast this
        have q2 : 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate ((T.n₀ / 4 : ℕ) : ℝ) ≤
            2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate r := inv_le (by positivity) (by positivity) hrr
        have c := two (A := 2⁻¹ ^ 8) (B := 2⁻¹ ^ 5) (u := 0) (by norm_num)
        have c' := two (A := 2⁻¹ ^ 10) (B := 2⁻¹ ^ 8) (u := 0) (by norm_num)
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [a.1, a.2, a'.1, a'.2, b.1, b.2]
end ExpansionTransport
open ExpansionTransport
theorem expansionTransportStatement_holds (hj : EventuallyInParametersCombines) (hL : transportConditionsEventually)
    (hends : interpolationAtEndpoints)
    (h1 : ExpansionNearFlat) (h2 : topOrderNearBlockStatement)
    (h3 : ExpansionAtFrameLocality) (h4 : ExpansionSecondDerivFlat)
    (h5 : topExpansionContDiffEventually) (h6 : ExpansionOffBlockDecay) :
    expansionTransportStatement := by
  obtain ⟨Cn, _, hTop⟩ := h2
  refine hj.2 _ _ (fun T _ h => expansionTransportAt_of_estimates hends T rfl h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2)
    (hj.1 _ _ (hL fun U => Cn U (decayThresholdIndex U) 3) (hj.1 _ _ h1 (hj.1 _ _ (hTop decayThresholdIndex)
      (hj.1 _ _ h3 (hj.1 _ _ h4 (hj.1 _ _ h5 h6))))))
end YangMills.Construction.ColdStepAtMirrorFrames
end
