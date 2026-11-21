import YangMills.Construction.ForwardTube.LightConeCoordinates
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
open Complex
noncomputable section
namespace YangMills.Construction.ForwardTube
def successiveDomain (n : ℕ) : Set (Fin n → ℂ × ℂ) :=
  {z | (∀ hn : 0 < n, z ⟨0, hn⟩ ∈ forwardTube) ∧
    ∀ (k : ℕ) (hk : k + 1 < n), z ⟨k + 1, hk⟩ - z ⟨k, by omega⟩ ∈ forwardTube}
theorem successiveDomain_zero (z : Fin 0 → ℂ × ℂ) : successiveDomain 0 = {z} := by
  ext w
  simp only [successiveDomain, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨fun hn => absurd hn (lt_irrefl 0),
    fun k hk => absurd hk (by omega)⟩⟩
def imagBoost (t : ℝ) (v : ℂ × ℂ) : ℂ × ℂ := complexBoost (I * (t : ℂ)) v
def imagBoostTuple {n : ℕ} (t : ℝ) (z : Fin n → ℂ × ℂ) : Fin n → ℂ × ℂ :=
  fun k => imagBoost t (z k)
private theorem exp_I_mul_I_mul_ofReal (t : ℝ) :
    exp (I * (I * (t : ℂ))) = ((Real.exp (-t) : ℝ) : ℂ) := by
  rw [← mul_assoc, I_mul_I]
  push_cast
  congr 1
  ring
abbrev _root_.YangMills.SharedProofs.p81843 := @exp_I_mul_I_mul_ofReal
private theorem exp_neg_I_mul_I_mul_ofReal (t : ℝ) :
    exp (-(I * (I * (t : ℂ)))) = ((Real.exp t : ℝ) : ℂ) := by
  rw [← mul_assoc, I_mul_I]
  push_cast
  congr 1
  ring
abbrev _root_.YangMills.SharedProofs.p100365 := @exp_neg_I_mul_I_mul_ofReal
private theorem lightConePlus_sub (u w : ℂ × ℂ) :
    lightConePlus (u - w) = lightConePlus u - lightConePlus w := by
  simp only [lightConePlus, Prod.fst_sub, Prod.snd_sub]
  ring
private theorem lightConeMinus_sub (u w : ℂ × ℂ) :
    lightConeMinus (u - w) = lightConeMinus u - lightConeMinus w := by
  simp only [lightConeMinus, Prod.fst_sub, Prod.snd_sub]
  ring
theorem imagBoost_mem_forwardTube (t : ℝ) {v : ℂ × ℂ} (hv : v ∈ forwardTube) :
    imagBoost t v ∈ forwardTube := by
  refine ⟨?_, ?_⟩
  · rw [imagBoost, lightConePlus_complexBoost, exp_I_mul_I_mul_ofReal, re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) hv.1
  · rw [imagBoost, lightConeMinus_complexBoost, exp_neg_I_mul_I_mul_ofReal, re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) hv.2
theorem imagBoost_sub_mem_forwardTube (t : ℝ) {u w : ℂ × ℂ} (huw : u - w ∈ forwardTube) :
    imagBoost t u - imagBoost t w ∈ forwardTube := by
  have hp := huw.1
  have hm := huw.2
  rw [lightConePlus_sub] at hp
  rw [lightConeMinus_sub] at hm
  refine ⟨?_, ?_⟩
  · rw [lightConePlus_sub, imagBoost, imagBoost, lightConePlus_complexBoost,
      lightConePlus_complexBoost, ← mul_sub, exp_I_mul_I_mul_ofReal, re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) hp
  · rw [lightConeMinus_sub, imagBoost, imagBoost, lightConeMinus_complexBoost,
      lightConeMinus_complexBoost, ← mul_sub, exp_neg_I_mul_I_mul_ofReal, re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) hm
theorem imagBoostTuple_mem {n : ℕ} (t : ℝ) {z : Fin n → ℂ × ℂ}
    (hz : z ∈ successiveDomain n) : imagBoostTuple t z ∈ successiveDomain n :=
  ⟨fun hn => imagBoost_mem_forwardTube t (hz.1 hn),
    fun k hk => imagBoost_sub_mem_forwardTube t (hz.2 k hk)⟩
abbrev PointLabel : Type := ↥RealPlane.realLabels
def LabelledTuple : Type :=
  Σ n : ℕ, ↥(successiveDomain n) × (Fin n → PointLabel)
namespace LabelledTuple
def mk {n : ℕ} (z : ↥(successiveDomain n)) (f : Fin n → PointLabel) : LabelledTuple :=
  ⟨n, z, f⟩
def length (q : LabelledTuple) : ℕ := q.1
def points (q : LabelledTuple) : Fin q.length → ℂ × ℂ := q.2.1.1
def labels (q : LabelledTuple) : Fin q.length → PointLabel := q.2.2
theorem points_mem (q : LabelledTuple) : q.points ∈ successiveDomain q.length :=
  q.2.1.2
def nil : LabelledTuple :=
  mk ⟨Fin.elim0, (successiveDomain_zero Fin.elim0).symm ▸ rfl⟩ Fin.elim0
theorem eq_nil_of_length_eq_zero {q : LabelledTuple} (hq : q.length = 0) :
    q = nil := by
  obtain ⟨n, z, f⟩ := q
  obtain rfl : n = 0 := hq
  have hz : z = ⟨Fin.elim0, (successiveDomain_zero Fin.elim0).symm ▸ rfl⟩ :=
    Subtype.ext (Subsingleton.elim _ _)
  have hf : f = Fin.elim0 := Subsingleton.elim _ _
  rw [hz, hf]
  rfl
def imagBoost (t : ℝ) (q : LabelledTuple) : LabelledTuple :=
  mk ⟨imagBoostTuple t q.2.1.1, imagBoostTuple_mem t q.2.1.2⟩ q.2.2
end LabelledTuple
end YangMills.Construction.ForwardTube
