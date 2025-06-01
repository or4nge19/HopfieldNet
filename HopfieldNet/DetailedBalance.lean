/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.Stochastic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.ENNReal.Basic

open Finset Matrix NeuralNetwork State

lemma sum_univ_eq_tsum_uniform {U : Type} [Fintype U] [DecidableEq U]
  [Nonempty U] :
  Summable (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) ∧
  ∑' (_ : U), (1 : ℝ) / ↑(Fintype.card U) = Finset.sum Finset.univ (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) :=
by
  have h_nonzero : (1 : ℝ) / ↑(Fintype.card U) ≠ 0 :=
    by { apply div_ne_zero; norm_num; simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]}
  have h_support : (Function.support (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U))).Finite := by
    rw [Function.support_const]
    exact Set.finite_univ
    exact h_nonzero
  have h_summable : Summable (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U)) := by
    apply summable_of_finite_support
    · rw [Function.support_const]
      exact Set.finite_univ
      exact h_nonzero
  have h_tsum_eq_sum : ∑' (u : U), (1 : ℝ) / ↑(Fintype.card U) = ∑ (u : U), (1 : ℝ) / ↑(Fintype.card U) := by
    simp_all only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      Function.support_inv, tsum_const, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀, sum_const, card_univ]
  exact ⟨h_summable, h_tsum_eq_sum⟩

lemma mul_div_cancel_of_ne_zero {α : Type*} [Field α] (a b : α) (h : b ≠ 0) : a * b / b = a := by
  rw [div_eq_mul_inv]
  rw [propext (mul_inv_eq_iff_eq_mul₀ h)]

/-- In a tsum over all neurons, only the neuron where s and s' differ contributes --/
lemma gibbs_single_site_tsum {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U]
  [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑' (a : U),
    (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a
    * (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
  1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron s wθ T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere
  have h_card_nonzero : (Fintype.card U : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero U _ ‹Nonempty U›)
  have h_calc : ((Fintype.card U : ℝ)) * (1 / ↑(Fintype.card U)) = 1 := by
    exact mul_one_div_cancel h_card_nonzero
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere

  have h_tsum_to_sum : ∑' (a : U), (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
                      ∑ a ∈ Finset.univ, (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' := by
    apply tsum_eq_sum
    · intro a ha
      simp only [Finset.mem_univ] at ha
      contradiction
  rw [h_tsum_to_sum]
  rw [h_s'_as_update]
  have h_zero_other_sites : ∀ a ∈ Finset.univ, a ≠ u →
                           (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' = 0 := by
    intro a _ ha
    exact gibbs_update_zero_other_sites wθ T s s' u a h_same_elsewhere h_diff_at_u ha
  rw [Finset.sum_eq_single u]
  · simp only [uniform_neuron_selection_prob]
    have h_update_eq : (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' =
                      (NN.State.gibbsUpdateSingleNeuron s wθ T u)
                      (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
      rw [h_s'_as_update]
      congr
    congr
  · intro a h_in h_ne
    have h_eq : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := h_s'_as_update
    rw [h_eq] at h_zero_other_sites
    exact mul_eq_zero_of_right _ (h_zero_other_sites a h_in h_ne)
  · intro h_not_in
    absurd (Finset.mem_univ u)
    exact h_not_in

  /-- Main lemma for Gibbs transition probability with single site update :
    For a state transition involving change at exactly one site u, the Gibbs transition
    probability is the product of the probability of selecting u and the probability
    of updating u to the new value --/--/
lemma gibbs_single_site_transition_prob {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U]
    [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  gibbsTransitionProb wθ T s s' =
  ENNReal.toReal (((1 : ENNReal) / (Fintype.card U : ENNReal)) *
  (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))) := by
  have h_eq := gibbs_single_site_tsum wθ T s s' u h_diff_at_u h_same_elsewhere
  have h_rewrite : ∑' (a : U), (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U))
    (by exact uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
                      1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron s wθ T u)
                      (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := h_eq
  exact
    Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg ENNReal.toReal (id (Eq.symm h_eq)))))

/-- When states differ only at site u, the energy terms that involve pairs of sites other than u are equal --/
lemma energy_terms_without_u_equal {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s'.act v1 * s'.act v2 =
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s.act v1 * s.act v2 := by
    apply Finset.sum_congr rfl
    intro v1 hv1; rw [Finset.mem_erase] at hv1
    apply Finset.sum_congr rfl
    intro v2 hv2;
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_inter, Finset.mem_compl, and_imp] at hv2
    -- hv2 : v2 ≠ v1 ∧ v2 ≠ u
    have h_v1_ne_u : v1 ≠ u := hv1.1
    have hs'_v1_eq_s_v1 : s'.act v1 = s.act v1 := Eq.symm (h v1 h_v1_ne_u)
    have hs'_v2_eq_s_v2 : s'.act v2 = s.act v2 := Eq.symm (h v2 hv2.2.2)
    rw [hs'_v1_eq_s_v1, hs'_v2_eq_s_v2]

/-- The energy difference for terms involving site u when states differ only at u --/
lemma energy_terms_with_u_diff {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s'.act u * s'.act v2 -
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act u * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) := by
  have h_eq_acts : ∀ v2, v2 ≠ u → s'.act v2 = s.act v2 := by
    intro v2 hv2_ne_u
    rw [h v2 hv2_ne_u]
  rw [← Finset.sum_sub_distrib]
  have h_term_eq : ∀ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
    wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    intro v2 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
    rw [h_eq_acts v2 hv2]
    ring
  have h_sum_eq : ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
                    (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                   ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
                    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    apply Finset.sum_congr rfl
    intro v2 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
    have h_act_eq : s'.act v2 = s.act v2 := h_eq_acts v2 hv2
    rw [h_act_eq]
    ring
  rw [h_sum_eq]
  rw [Finset.mul_sum]

lemma weight_energy_diff_term_v1_eq_u {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
  (s'.act u - s.act u) * ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  have h_term_eq : ∀ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
    wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    intro v2 hv2
    simp only [mem_filter, mem_univ, true_and] at hv2
    rw [h v2 hv2]
    ring
  have h_sum_eq : ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
                  (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
                  (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    apply sum_congr rfl
    intro v2 hv2
    exact h_term_eq v2 hv2

  rw [h_sum_eq]
  rw [mul_sum]

lemma weight_energy_diff_term_v1_ne_u {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ,
    (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
  (s'.act u - s.act u) * ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 := by
  simp_rw [filter_ne']
  have h_transform : ∑ v1 ∈ univ.erase u, ∑ v2 ∈ univ.erase v1,
                     (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
                     ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 * (s'.act u - s.act u) := by
    apply sum_congr rfl
    intro v1 hv1
    simp only [mem_erase, mem_univ] at hv1
    rw [h v1 hv1.1]
    have u_mem_erase_v1 : u ∈ univ.erase v1 := by simp [hv1.1.symm]
    rw [sum_eq_sum_diff_singleton_add u_mem_erase_v1]
    simp only [mem_erase, mem_sdiff, mem_singleton, sdiff_singleton_eq_erase] -- Simplify set notation
    have h_v2_eq_u : wθ.w v1 u * s'.act v1 * s'.act u - wθ.w v1 u * s'.act v1 * s.act u =
                      wθ.w v1 u * s'.act v1 * (s'.act u - s.act u) := by ring
    have h_v2_ne_u : ∑ v2 ∈ (univ.erase v1).erase u,
                        (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s'.act v1 * s.act v2) = 0 := by
        apply sum_eq_zero
        intro v2 hv2
        simp only [mem_erase] at hv2
        rw [h v2 hv2.1]
        ring

    rw [h_v2_eq_u, h_v2_ne_u]
    exact AddZeroClass.zero_add (wθ.w v1 u * s'.act v1 * (s'.act u - s.act u))
  rw [h_transform]
  have h_fun_eq : ∀ v ∈ univ.erase u,
                  wθ.w v u * s.act v * (s'.act u - s.act u) =
                  (s'.act u - s.act u) * (wθ.w v u * s.act v) := by
    intro v hv
    ring
  rw [sum_congr rfl h_fun_eq]
  rw [← mul_sum]

lemma weight_sum_symmetry {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State)
  (u : U) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 =
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  simp_rw [filter_ne']
  apply sum_congr rfl
  intro v hv
  simp only [mem_erase] at hv
  rw [h_symm v u]

lemma weight_energy_sum_split {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [DecidableEq R]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s'.act v1 * s'.act v2 -
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s.act v1 * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) * 2 := by
    simp_rw [← sum_sub_distrib]
    have h_u_mem : u ∈ univ := mem_univ u
    rw [sum_eq_sum_diff_singleton_add h_u_mem]
    simp only [singleton_val, sum_singleton, sdiff_singleton_eq_erase]
    have h_term_u : ∑ v2 ∈ univ.erase u,
                    (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                    (s'.act u - s.act u) * (∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2) := by
      rw [← filter_ne']
      apply weight_energy_diff_term_v1_eq_u wθ s s' u h
    have h_sum_not_u : ∑ v1 ∈ univ.erase u, ∑ v2 ∈ univ.erase v1,
                     (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
                     (s'.act u - s.act u) * ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 := by
      have h1 : univ.erase u = filter (fun v1 => v1 ≠ u) univ := by
          exact Eq.symm (filter_erase_equiv u)
      have h2 : ∀ v1, univ.erase v1 = filter (fun v2 => v2 ≠ v1) univ := fun v1 => Eq.symm (@filter_ne' U _ univ v1)
      rw [h1]
      simp_rw [h2]
      apply weight_energy_diff_term_v1_ne_u wθ s s' u h
    have h_filter_erase_u : filter (fun v2 => v2 ≠ u) univ = univ.erase u := by
      apply filter_erase_equiv
    rw [← h_filter_erase_u] at h_term_u
    rw [h_filter_erase_u] at *
    have h_goal_rewrite : ∑ x ∈ univ.erase u,
        ∑ x_1 ∈ filter (fun v2 => v2 ≠ x) univ, (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) +
      ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) =
      ∑ x ∈ univ.erase u,
        ∑ x_1 ∈ univ.erase x, (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) +
      ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) := by
      apply congr_arg₂
      · apply sum_congr rfl
        intro x hx
        rw [@filter_erase_equiv]
      · rfl
    rw [h_goal_rewrite]
    have h_first_term : ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) =
                        (s'.act u - s.act u) * ∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2 := by
      have h_eq : filter (fun v2 => v2 ≠ u) univ = univ.erase u := by exact filter_erase_equiv u
      rw [← h_eq] at *
      exact h_term_u
    have h_second_term : ∑ x ∈ univ.erase u, ∑ x_1 ∈ univ.erase x,
                          (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) =
                          (s'.act u - s.act u) * ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 := by
      exact h_sum_not_u
    rw [h_first_term, h_second_term]
    have h_sym : ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 =
                 ∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2 := by
      apply sum_congr rfl
      intro v hv
      simp only [mem_erase] at hv
      rw [h_symm v u]
    rw [h_sym]
    rw [← two_mul]
    ring

/-- For a Hopfield network with states differing at a single site, the activation
    at that site is related to the weighted sum of other activations --/
lemma local_field_relation {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
  s.net wθ u = ∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act v2 := by
  simp only [NeuralNetwork.State.net, HopfieldNetwork, NeuralNetwork.fnet, HNfnet,
             NeuralNetwork.State.out, NeuralNetwork.fout, HNfout]

/-- When states differ at a single site, the energy difference in the weight component
    is proportional to the local field and activation difference --/
lemma weight_energy_single_site_diff {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Ew wθ - s.Ew wθ = (s.act u - s'.act u) * s.net wθ u := by
  unfold NeuralNetwork.State.Ew NeuralNetwork.State.Wact
  rw [← mul_sub]
  have h_dec_eq_R : DecidableEq R := inferInstance
  have h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1 := by
    exact fun v1 v2 ↦ weight_symmetry wθ v1 v2
  rw [weight_energy_sum_split wθ s s' u h h_symm]
  rw [local_field_relation wθ s u]
  have h_two_ne_zero : (2 : R) ≠ 0 := by norm_num
  dsimp [h_two_ne_zero]
  ring

/-- When states differ at a single site, the energy difference in the bias component
    is proportional to the activation difference --/
lemma bias_energy_single_site_diff {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Eθ wθ - s.Eθ wθ = θ' (wθ.θ u) * (s'.act u - s.act u) := by
  unfold NeuralNetwork.State.Eθ
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ u)]
  have h_sum_zero : ∑ v ∈ Finset.univ.erase u, (θ' (wθ.θ v) * s'.act v - θ' (wθ.θ v) * s.act v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hv
    rw [h v hv.1]
    ring
  rw [Finset.sdiff_singleton_eq_erase]
  rw [h_sum_zero, add_zero]
  ring

/-- Energy difference for single-site updates with specified bias term.
    This is a general formulation that allows different bias configurations. --/
lemma energy_single_site_diff_with_bias {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 1/2 * s.net wθ u) :
  s'.E wθ - s.E wθ = -1/2 * (s'.act u - s.act u) * s.net wθ u := by
    rw [energy_decomposition, energy_decomposition]
    rw [add_sub_add_comm] -- Rearrange to (s'.Ew - s.Ew) + (s'.Eθ - s.Eθ)
    rw [weight_energy_single_site_diff wθ s s' u h]
    rw [bias_energy_single_site_diff wθ s s' u h]
    rw [h_bias]
    ring_nf

lemma energy_single_site_diff {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 0) : -- Added hypothesis for standard Hopfield case
  s'.E wθ - s.E wθ = -(s'.act u - s.act u) * s.net wθ u := by
  -- Decompose energy into weight and bias components
  rw [energy_decomposition, energy_decomposition]
  rw [add_sub_add_comm]
  rw [weight_energy_single_site_diff wθ s s' u h, bias_energy_single_site_diff wθ s s' u h]
  rw [h_bias]
  ring_nf

@[simp]
lemma ENNReal.natCast_eq_ofReal (n : ℕ) : (n : ENNReal) = ENNReal.ofReal n := by
  induction n with
  | zero =>
    simp [ENNReal.ofReal]
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [Nat.cast_succ]
    rw [ENNReal.ofReal_add]
    · rw [ih]
      rw [ENNReal.ofReal_one]
    · exact Nat.cast_nonneg n
    · norm_num

lemma gibbs_transition_sum_single_site {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]
  [Coe R ℝ][Field ℕ] [CommGroup ℕ] [Inv ℕ] [HDiv ℕ ℕ ℝ] -- Removed Field ℕ etc. constraints
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  ∑' (a : U), ((1 : ENNReal) / (Fintype.card U : ENNReal)) * -- Use ENNReal probability
    (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
  ((1 : ENNReal) / (Fintype.card U : ENNReal)) * (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' := by
  have h_tsum := gibbs_single_site_tsum wθ T s s' u h_diff h_same_elsewhere
  have h_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) :=
    single_site_difference_as_update s s' u h_diff h_same_elsewhere
  rw [← h_update] at h_tsum
  exact h_tsum

lemma single_site_update_eq {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s s' : (HopfieldNetwork R U).State) (u : U)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) :=
  single_site_difference_as_update s s' u h_diff h_same_elsewhere

lemma gibbs_update_single_neuron_formula {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State)
  (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u val hval) =
    if val = 1 then ENNReal.ofReal (Real.exp (local_field / T)) / Z
    else ENNReal.ofReal (Real.exp (-local_field / T)) / Z :=
  gibbs_update_single_neuron_prob wθ T s u val hval

lemma gibbs_single_site_transition_explicit {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]--[HDiv ℕ ℕ ℝ] [CommGroup ℕ] [Field ℕ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (_ : θ' (wθ.θ u) = 0) (_ : T > 0) (h_neq : s ≠ s') :
  gibbsTransitionProb wθ T s s' =
    (1 / (Fintype.card U : ℝ)) * ENNReal.toReal (
      let local_field := s.net wθ u
      let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ) :=
by
  have h_diff : s.act u ≠ s'.act u := by
    intro contra; exact h_neq (State.ext (fun v => if hv : v = u then by rw [hv]; exact contra else h_same_elsewhere v hv))
  have h_prob := gibbs_single_site_transition_prob wθ T s s' u h_diff h_same_elsewhere
  rw [h_prob]
  have h_upd := single_site_difference_as_update s s' u h_diff h_same_elsewhere
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  have h_formula : (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) =
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
    apply gibbs_update_single_neuron_formula
  have h_update_act : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = s'.act u := by
    exact congrFun (congrArg act (id (Eq.symm h_upd))) u
  have h_goal : gibbsTransitionProb wθ T s s' =
    (1 / (Fintype.card U : ℝ)) * ENNReal.toReal (
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ) := by
    rw [h_prob]
    have h_eq : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := h_upd
    rw [h_eq] at h_formula ⊢
    rw [h_formula]
    rw [h_update_act]
    have h_real_div_pos : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
                          ENNReal.toReal (ENNReal.ofReal a / ENNReal.ofReal b) = a / b := by
      intros a b ha hb
      rw [ENNReal.toReal_div]
      · rw [ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le]
    have h_exp_pos : ∀ x : ℝ, 0 < Real.exp x := fun x => Real.exp_pos x
    have h_card_div : ENNReal.toReal ((1 : ENNReal) / (Fintype.card U : ENNReal)) = 1 / (Fintype.card U : ℝ) := by
      apply ENNReal.toReal_div
    rw [← h_card_div]
    rw [ENNReal.toReal_mul]
  have h_card_pos : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hZ_ne_top : Z ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hZ_pos : Z > 0 := by
    have h_exp1_pos : Real.exp (local_field / T) > 0 := Real.exp_pos _
    have h_exp2_pos : Real.exp (-local_field / T) > 0 := Real.exp_pos _
    have h1 : ENNReal.ofReal (Real.exp (local_field / T)) > 0 := ENNReal.ofReal_pos.mpr h_exp1_pos
    have h2 : ENNReal.ofReal (Real.exp (-local_field / T)) > 0 := ENNReal.ofReal_pos.mpr h_exp2_pos
    exact Right.add_pos' h1 h2
  have h_toReal_div_ENNReal : ∀ (a b : ENNReal) (ha : a ≠ ⊤) (hb : b ≠ 0) (hb_top : b ≠ ⊤),
      ENNReal.toReal (a / b) = ENNReal.toReal a / ENNReal.toReal b := by
    intros a b ha hb hb_top
    exact ENNReal.toReal_div a b
  have h_formula_direct : (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' =
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
    rw [h_upd]
    have h_update_eq : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = s'.act u := by
      simp only [NN.State.updateNeuron, act]; exact rfl
    have h_formula_raw := gibbs_update_single_neuron_formula wθ T s u (s'.act u) (s'.hp u)
    have h_formula_rewritten : (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) =
      if (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
      rw [h_formula_raw]
      congr
    have h_cond_eq : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = 1 ↔ s'.act u = 1 := by
      rw [h_update_eq]
    exact h_formula_rewritten
  have h_final : (1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))).toReal =
                 1 / ↑(Fintype.card U) * ENNReal.toReal (
                   if s'.act u = 1 then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                   else ENNReal.ofReal (Real.exp (-local_field / T)) / Z
                 ) := by
    have h_card_nonzero : (Fintype.card U : ℝ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero U _ ‹Nonempty U›)
    have h_card_finite : (Fintype.card U : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top (Fintype.card U)
    have h_one_div_card : (1 / (Fintype.card U : ENNReal)).toReal = 1 / (Fintype.card U : ℝ) := by
      rw [ENNReal.toReal_div]
      · rw [ENNReal.toReal_one]
        exact rfl
    rw [ENNReal.toReal_mul]
    congr 1
    · exact congrArg ENNReal.toReal h_formula
  trans (1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))).toReal
  · exact rfl
  · exact h_final

/-- Multi-site transitions have zero probability --/
lemma gibbsUpdateSingleNeuron_support {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (u : U)
  (s' : (HopfieldNetwork R U).State) :
  s' ∈ (NN.State.gibbsUpdateSingleNeuron s wθ T u).support →
  s' = NN.State.updateNeuron s u 1 (by exact Or.inl rfl) ∨
  s' = NN.State.updateNeuron s u (-1) (by exact Or.inr rfl) := by
  intro h_mem_support
  rw [PMF.mem_support_iff] at h_mem_support
  have h_pos : (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' > 0 := by
    exact (PMF.apply_pos_iff (NN.State.gibbsUpdateSingleNeuron s wθ T u) s').mpr h_mem_support
  exact gibbsUpdate_possible_states wθ T s u s' h_pos

lemma gibbsUpdateSingleNeuron_prob_zero_if_not_update {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (u : U)
  (s' : (HopfieldNetwork R U).State) :
  ¬(s' = NN.State.updateNeuron s u 1 (by exact Or.inl rfl) ∨
    s' = NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)) →
  (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' = 0 := by
  intro h_not_update
  -- Use the contrapositive of the support lemma
  rw [PMF.apply_eq_zero_iff]
  contrapose! h_not_update -- This assumes s' is in the support
  exact gibbsUpdateSingleNeuron_support s wθ T u s' h_not_update

lemma gibbsSamplingStep_prob_zero_if_multi_site {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ] [Inv ℕ] [Coe ℕ ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  (NN.State.gibbsSamplingStep wθ T s) s' = 0 := by
  intro h_multi_site
  unfold NN.State.gibbsSamplingStep
  simp only [PMF.bind_apply] -- Use the definition of PMF.bind
  rw [ENNReal.tsum_eq_zero]
  intro u -- Consider an arbitrary neuron u
  have h_s'_not_update_at_u : ¬(s' = NN.State.updateNeuron s u 1 (by exact Or.inl rfl) ∨
                                s' = NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)) := by
    intro h_update_or
    apply h_multi_site
    cases h_update_or with
    | inl h_eq_update_one =>
      exists u
      intro v hv
      rw [h_eq_update_one]
      exact Eq.symm (updateNeuron_preserves s u v 1 (Or.inl rfl) hv)
    | inr h_eq_update_neg_one =>
      exists u
      intro v hv
      rw [h_eq_update_neg_one]
      exact Eq.symm (updateNeuron_preserves s u v (-1) (Or.inr rfl) hv)
  have h_update_prob_zero : (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' = 0 :=
    gibbsUpdateSingleNeuron_prob_zero_if_not_update s wθ T u s' h_s'_not_update_at_u
  exact mul_eq_zero_of_right _ h_update_prob_zero

-- Main lemma
lemma gibbs_multi_site_transition {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U]
    [Nonempty U] [Coe R ℝ] [Inv ℕ] [Coe ℕ ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  gibbsTransitionProb wθ T s s' = 0 := by
  intro h_multi_site
  unfold gibbsTransitionProb
  have h_step_prob_zero : (NN.State.gibbsSamplingStep wθ T s) s' = 0 :=
    gibbsSamplingStep_prob_zero_if_multi_site wθ T s s' h_multi_site
  rw [h_step_prob_zero]
  exact rfl
