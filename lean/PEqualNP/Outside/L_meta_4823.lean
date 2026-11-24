import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4823

open PEqualNP.CircuitLowerBounds

lemma operand_length (gs : List Gate) (binary : ∀ g ∈ gs, g.inputs.length = 2) :
    (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := binary g (by simp)
    have ht := ih (fun t ht => binary t (by simp [ht]))
    simp only [List.flatMap_cons, List.length_append, hg, ht, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_4823

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4823 in
theorem PEqualNP.Outside.L_meta_4823 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C hAO hpositive cover
  have len : (C.gates.flatMap Gate.inputs).length = 2 * C.size :=
    operand_length C.gates hAO.2.2
  have distinctLe := List.toFinset_card_le (C.gates.flatMap Gate.inputs)
  rw [cover, Finset.card_range, len] at distinctLe ⊢
  omega
