import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetArgumentLemmas
open JetQuad
section Strips
variable {k k' : Fin 4 → ℂ} {a b : ℝ}
theorem mem_imStrip_of_real (ha : 0 ≤ a) (hk : k ∈ realDualPoints) : k ∈ imStrip a := fun μ => by
  have him : (k μ).im = 0 := hk μ
  rw [him, abs_zero]
  exact ha
theorem neg_mem_imStrip (hk : k ∈ imStrip a) : -k ∈ imStrip a := fun μ => by
  have hμ := hk μ
  simpa [abs_neg] using hμ
theorem neg_mem_realDualPoints (hk : k ∈ realDualPoints) : -k ∈ realDualPoints := fun μ => by
  have him : (k μ).im = 0 := hk μ
  simp [him]
theorem add_mem_imStrip (hk : k ∈ imStrip a) (hk' : k' ∈ imStrip b) :
    k + k' ∈ imStrip (a + b) := fun μ => by
  have ha := abs_le.mp (hk μ)
  have hb := abs_le.mp (hk' μ)
  refine abs_le.mpr ?_
  simp only [Pi.add_apply, Complex.add_im]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
end Strips
section Points
variable {δ : ℝ} {p k : Fin 4 → ℂ}
theorem real_add_mem_wide (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k + p ∈ imStrip (2 * δ) := by
  rw [two_mul]
  exact add_mem_imStrip (mem_imStrip_of_real hδ.le hk) hp
theorem real_sub_mem_wide (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k - p ∈ imStrip (2 * δ) := by
  rw [two_mul, sub_eq_add_neg]
  exact add_mem_imStrip (mem_imStrip_of_real hδ.le hk) (neg_mem_imStrip hp)
theorem real_mem_wideStrip (hδ : 0 < δ) (hk : k ∈ realDualPoints) : k ∈ imStrip (2 * δ) :=
  mem_imStrip_of_real (by linarith) hk
theorem real_mem_stripAddShift (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k ∈ stripAddShift δ p :=
  ⟨real_mem_wideStrip hδ hk, real_add_mem_wide hδ hp hk⟩
theorem real_mem_stripSubShift (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k ∈ stripSubShift δ p :=
  ⟨real_mem_wideStrip hδ hk, real_sub_mem_wide hδ hp hk⟩
theorem real_sub_mem_stripAddShift (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k - p ∈ stripAddShift δ p :=
  ⟨real_sub_mem_wide hδ hp hk, by rw [sub_add_cancel]; exact real_mem_wideStrip hδ hk⟩
theorem real_add_mem_stripSubShift (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hk : k ∈ realDualPoints) :
    k + p ∈ stripSubShift δ p :=
  ⟨real_add_mem_wide hδ hp hk, by rw [add_sub_cancel_right]; exact real_mem_wideStrip hδ hk⟩
theorem neg_sub_mem_stripAddShift (hk : k ∈ stripAddShift δ p) : -k - p ∈ stripAddShift δ p := by
  refine ⟨?_, ?_⟩
  · have hn := neg_mem_imStrip hk.2
    rwa [neg_add, ← sub_eq_neg_add, sub_eq_add_neg, add_comm, ← sub_eq_add_neg] at hn
  · rw [sub_add_cancel]
    exact neg_mem_imStrip hk.1
theorem neg_add_mem_stripSubShift (hk : k ∈ stripSubShift δ p) : -k + p ∈ stripSubShift δ p := by
  refine ⟨?_, ?_⟩
  · have hn := neg_mem_imStrip hk.2
    rwa [neg_sub, sub_eq_add_neg, add_comm] at hn
  · rw [add_sub_cancel_right]
    exact neg_mem_imStrip hk.1
theorem jetDomainSymmetries_of_mem (hδ : 0 < δ) (hp : p ∈ imStrip δ) :
    JetDomainSymmetries δ p where
  mem_addShift := fun _ hk => ⟨hk.1, hk.2, neg_sub_mem_stripAddShift hk⟩
  mem_subShift := fun _ hk => ⟨hk.1, hk.2, neg_add_mem_stripSubShift hk⟩
  mem_real := fun _ hk =>
    ⟨⟨⟨real_mem_wideStrip hδ hk, real_mem_stripAddShift hδ hp hk⟩, real_mem_stripSubShift hδ hp hk⟩,
      real_sub_mem_stripAddShift hδ hp hk, real_add_mem_stripSubShift hδ hp hk⟩
  neg_image_strip := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact neg_mem_imStrip hy
    · intro hx
      exact ⟨-x, neg_mem_imStrip hx, neg_neg x⟩
  neg_image_real := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact neg_mem_realDualPoints hy
    · intro hx
      exact ⟨-x, neg_mem_realDualPoints hx, neg_neg x⟩
theorem productJetArguments_of_mem (hδ : 0 < δ) (hp : p ∈ imStrip δ) :
    ProductJetArguments δ p where
  comp00 := fun _ hk => ⟨hk, hk⟩
  comp10 := fun _ hk => ⟨hk, hk.1, hk.2, hk⟩
  comp01 := fun _ hk => ⟨hk, hk.1, hk.2, hk⟩
  comp11 := fun _ hk =>
    ⟨hk, real_mem_wideStrip hδ hk, real_mem_wideStrip hδ hk, hk, real_sub_mem_stripAddShift hδ hp hk,
      real_mem_stripSubShift hδ hp hk, real_add_mem_stripSubShift hδ hp hk,
      real_mem_stripAddShift hδ hp hk⟩
theorem transposeJetArguments_all : TransposeJetArguments δ p where
  comp00 := fun _ hk => neg_mem_imStrip hk
  comp10 := fun _ hk => neg_sub_mem_stripAddShift hk
  comp01 := fun _ hk => neg_add_mem_stripSubShift hk
  comp11 := fun _ hk => neg_mem_realDualPoints hk
end Points
section Equal
variable {I I' I'' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
theorem eqAsJet_refl (A : JetQuad I I') : EqAsJet δ p A A :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_add {A A' B B' : JetQuad I I'} (hA : EqAsJet δ p A A') (hB : EqAsJet δ p B B') :
    EqAsJet δ p (add A B) (add A' B') := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show A.f00 k + B.f00 k = A'.f00 k + B'.f00 k
    rw [hA.1 hk, hB.1 hk]
  · show A.f10 k + B.f10 k = A'.f10 k + B'.f10 k
    rw [hA.2.1 hk, hB.2.1 hk]
  · show A.f01 k + B.f01 k = A'.f01 k + B'.f01 k
    rw [hA.2.2.1 hk, hB.2.2.1 hk]
  · show A.f11 k + B.f11 k = A'.f11 k + B'.f11 k
    rw [hA.2.2.2 hk, hB.2.2.2 hk]
theorem eqAsJet_smul (z : ℂ) {A A' : JetQuad I I'} (hA : EqAsJet δ p A A') :
    EqAsJet δ p (smul z A) (smul z A') := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show z • A.f00 k = z • A'.f00 k
    rw [hA.1 hk]
  · show z • A.f10 k = z • A'.f10 k
    rw [hA.2.1 hk]
  · show z • A.f01 k = z • A'.f01 k
    rw [hA.2.2.1 hk]
  · show z • A.f11 k = z • A'.f11 k
    rw [hA.2.2.2 hk]
theorem eqAsJet_mul (hδ : 0 < δ) (hp : p ∈ imStrip δ) {A A' : JetQuad I I'}
    {B B' : JetQuad I'' I} (hA : EqAsJet δ p A A') (hB : EqAsJet δ p B B') :
    EqAsJet δ p (mul p A B) (mul p A' B') := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show (A.f00 k).comp (B.f00 k) = (A'.f00 k).comp (B'.f00 k)
    rw [hA.1 hk, hB.1 hk]
  · show (A.f10 k).comp (B.f00 k) + (A.f00 (k + p)).comp (B.f10 k) =
      (A'.f10 k).comp (B'.f00 k) + (A'.f00 (k + p)).comp (B'.f10 k)
    rw [hA.2.1 hk, hB.1 hk.1, hA.1 hk.2, hB.2.1 hk]
  · show (A.f01 k).comp (B.f00 k) + (A.f00 (k - p)).comp (B.f01 k) =
      (A'.f01 k).comp (B'.f00 k) + (A'.f00 (k - p)).comp (B'.f01 k)
    rw [hA.2.2.1 hk, hB.1 hk.1, hA.1 hk.2, hB.2.2.1 hk]
  · show (A.f11 k).comp (B.f00 k) + (A.f00 k).comp (B.f11 k) +
        (A.f10 (k - p)).comp (B.f01 k) + (A.f01 (k + p)).comp (B.f10 k) =
      (A'.f11 k).comp (B'.f00 k) + (A'.f00 k).comp (B'.f11 k) +
        (A'.f10 (k - p)).comp (B'.f01 k) + (A'.f01 (k + p)).comp (B'.f10 k)
    rw [hA.2.2.2 hk, hB.1 (real_mem_wideStrip hδ hk), hA.1 (real_mem_wideStrip hδ hk), hB.2.2.2 hk,
      hA.2.1 (real_sub_mem_stripAddShift hδ hp hk), hB.2.2.1 (real_mem_stripSubShift hδ hp hk),
      hA.2.2.1 (real_add_mem_stripSubShift hδ hp hk), hB.2.1 (real_mem_stripAddShift hδ hp hk)]
theorem eqAsJet_transposeAt {A A' : JetQuad I I'} (hA : EqAsJet δ p A A') :
    EqAsJet δ p (transposeAt p A) (transposeAt p A') := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show quotHomTranspose (A.f00 (-k)) = quotHomTranspose (A'.f00 (-k))
    rw [hA.1 (neg_mem_imStrip hk)]
  · show quotHomTranspose (A.f10 (-k - p)) = quotHomTranspose (A'.f10 (-k - p))
    rw [hA.2.1 (neg_sub_mem_stripAddShift hk)]
  · show quotHomTranspose (A.f01 (-k + p)) = quotHomTranspose (A'.f01 (-k + p))
    rw [hA.2.2.1 (neg_add_mem_stripSubShift hk)]
  · show quotHomTranspose (A.f11 (-k)) = quotHomTranspose (A'.f11 (-k))
    rw [hA.2.2.2 (neg_mem_realDualPoints hk)]
theorem jetNorm_congr {A A' : JetQuad I I'} (hA : EqAsJet δ p A A') :
    jetNorm δ p A = jetNorm δ p A' := by
  have e00 : (⨆ k ∈ imStrip (2 * δ), quotHomNorm (A.f00 k)) =
      ⨆ k ∈ imStrip (2 * δ), quotHomNorm (A'.f00 k) :=
    iSup_congr fun k => iSup_congr fun hk => by rw [hA.1 hk]
  have e10 : (⨆ k ∈ stripAddShift δ p, quotHomNorm (A.f10 k)) =
      ⨆ k ∈ stripAddShift δ p, quotHomNorm (A'.f10 k) :=
    iSup_congr fun k => iSup_congr fun hk => by rw [hA.2.1 hk]
  have e01 : (⨆ k ∈ stripSubShift δ p, quotHomNorm (A.f01 k)) =
      ⨆ k ∈ stripSubShift δ p, quotHomNorm (A'.f01 k) :=
    iSup_congr fun k => iSup_congr fun hk => by rw [hA.2.2.1 hk]
  have e11 : (⨆ k ∈ realDualPoints, quotHomNorm (A.f11 k)) =
      ⨆ k ∈ realDualPoints, quotHomNorm (A'.f11 k) :=
    iSup_congr fun k => iSup_congr fun hk => by rw [hA.2.2.2 hk]
  unfold JetQuad.jetNorm
  rw [e00, e10, e01, e11]
theorem traceNumber_congr {A A' : JetQuad I I} (hA : EqAsJet δ p A A') :
    traceNumber A = traceNumber A' := by
  unfold JetQuad.traceNumber
  refine congrArg torusAverage (funext fun y => ?_)
  have hy : toComplexVec y ∈ realDualPoints := fun μ => Complex.ofReal_im (y μ)
  rw [hA.2.2.2 hy]
theorem eqAsJet_zeroPartInv {A A' : JetQuad I I} (hA : EqAsJet δ p A A') :
    EqAsJet δ p (zeroPartInv A) (zeroPartInv A') := by
  refine ⟨fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  show quotHomInverse (A.f00 k) = quotHomInverse (A'.f00 k)
  rw [hA.1 hk]
theorem eqAsJet_normalize (hδ : 0 < δ) (hp : p ∈ imStrip δ) {A A' : JetQuad I I}
    (hA : EqAsJet δ p A A') : EqAsJet δ p (normalize p A) (normalize p A') :=
  eqAsJet_add (eqAsJet_mul hδ hp (eqAsJet_zeroPartInv hA) hA) (eqAsJet_refl _)
theorem eqAsJet_logSeries (hδ : 0 < δ) (hp : p ∈ imStrip δ) {A A' : JetQuad I I}
    (hA : EqAsJet δ p A A') : EqAsJet δ p (logSeries p A) (logSeries p A') :=
  eqAsJet_add (eqAsJet_normalize hδ hp hA)
    (eqAsJet_smul _ (eqAsJet_mul hδ hp (eqAsJet_normalize hδ hp hA) (eqAsJet_normalize hδ hp hA)))
theorem isInvertibleJet_of_eqAsJet {A A' : JetQuad I I} (hA : EqAsJet δ p A A')
    (hJ : IsJet δ p A') (hi : IsInvertibleJet δ p A) : IsInvertibleJet δ p A' where
  isJet := hJ
  isUnit_f00 := fun k hk => by
    rw [← hA.1 hk]
    exact hi.isUnit_f00 k hk
  bdd_inverse := by
    have hb : (⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (A.f00 k))) =
        ⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (A'.f00 k)) :=
      iSup_congr fun k => iSup_congr fun hk => by rw [hA.1 hk]
    rw [← hb]
    exact hi.bdd_inverse
end Equal
theorem jetArgumentsAndEqualJets_holds : JetArgumentsAndEqualJets := by
  refine ⟨fun δ p hδ hp => ⟨jetDomainSymmetries_of_mem hδ hp, productJetArguments_of_mem hδ hp,
    transposeJetArguments_all⟩, ?_, ?_⟩
  · intro δ p I I' _ _ A A' hA _ h
    have hδ := hA.pos_width
    have hp := hA.mem_imStrip
    exact ⟨jetNorm_congr h, fun z => eqAsJet_smul z h, eqAsJet_transposeAt h,
      fun B B' _ _ hB => eqAsJet_add h hB,
      fun I'' _ B B' _ _ hB => eqAsJet_mul hδ hp h hB⟩
  · intro δ p I _ A A' hA hA' h
    have hδ := hA.pos_width
    have hp := hA.mem_imStrip
    refine ⟨traceNumber_congr h, fun hi => ⟨isInvertibleJet_of_eqAsJet h hA' hi,
      eqAsJet_zeroPartInv h, eqAsJet_normalize hδ hp h, ?_⟩⟩
    exact traceNumber_congr (eqAsJet_logSeries hδ hp h)
end YangMills.Construction.PeriodicOperators.JetArgumentLemmas
end
