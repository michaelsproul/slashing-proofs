theory SlashingProofs
  imports Main MinMaxByKey
begin

record checkpoint =
  epoch :: nat
  root :: nat

record attestation =
  source :: checkpoint
  target :: checkpoint

definition
  "is_double_vote att1 att2 \<equiv>
    att1 \<noteq> att2 \<and>
    epoch (target att1) = epoch (target att2)"

definition
  "surrounds att1 att2 \<equiv>
    epoch (source att1) < epoch (source att2) \<and>
    epoch (target att1) > epoch (target att2)"

definition
  "is_slashable att1 att2 \<equiv>
    is_double_vote att1 att2 \<or>
    surrounds att1 att2 \<or>
    surrounds att2 att1"

lemma double_vote_refl:
  "is_double_vote att1 att2 = is_double_vote att2 att1"
  by (fastforce simp: is_double_vote_def)

definition
  is_slashable_wrt :: "attestation \<Rightarrow> attestation list \<Rightarrow> bool"
where
  "is_slashable_wrt att signed_attestations \<equiv>
    \<exists>prev \<in> set signed_attestations. is_slashable att prev"

definition
  min_source_att :: "attestation list \<Rightarrow> attestation option"
  where
  "min_source_att attestations \<equiv> min_by_key (epoch \<circ> source) attestations"

definition
  min_target_att :: "attestation list \<Rightarrow> attestation option"
  where
  "min_target_att attestations \<equiv> min_by_key (epoch \<circ> target) attestations"

definition
  max_source_att :: "attestation list \<Rightarrow> attestation option"
  where
  "max_source_att attestations \<equiv> max_by_key (epoch \<circ> source) attestations"

definition
  max_target_att :: "attestation list \<Rightarrow> attestation option"
  where
  "max_target_att attestations \<equiv> max_by_key (epoch \<circ> target) attestations"

definition
  not_mutually_slashable :: "attestation list \<Rightarrow> bool"
  where
  "not_mutually_slashable atts \<equiv>
    \<forall>att1 \<in> set atts.
      \<not>(\<exists>att2 \<in> set atts. is_slashable att1 att2)"

(* EIP-3076 signing safety conditions *)
definition
  safe_to_sign1 :: "attestation \<Rightarrow> attestation \<Rightarrow> attestation list \<Rightarrow> bool" where
  "safe_to_sign1 new att atts \<equiv>
    \<not> is_slashable_wrt new (att # atts) \<and>
      epoch (source new) \<ge> epoch (source (the (min_source_att (att # atts)))) \<and>
      epoch (target new) > epoch (target (the (min_target_att (att # atts))))"

primrec
  safe_to_sign :: "attestation \<Rightarrow> attestation list \<Rightarrow> bool"
  where
  "safe_to_sign new [] = True" |
  "safe_to_sign new (att # atts) = safe_to_sign1 new att atts"

lemma max_source_att_le:
  "attestations \<noteq> [] \<Longrightarrow>
   prev \<in> set attestations \<Longrightarrow>
   epoch (source prev) \<le> epoch (source (the (max_source_att attestations)))"
  by (fastforce simp: max_source_att_def
                intro: max_by_key_le[where f="epoch \<circ> source", simplified])

lemma max_target_att_le:
  "attestations \<noteq> [] \<Longrightarrow>
   prev \<in> set attestations \<Longrightarrow>
   epoch (target prev) \<le> epoch (target (the (max_target_att attestations)))"
  by (fastforce simp: max_target_att_def
                intro: max_by_key_le[where f="epoch \<circ> target", simplified])

lemma min_target_att_singleton[simp]:
  "min_target_att [x] = Some x"
  by (fastforce simp: min_target_att_def min_by_key1_def)

lemma min_source_att_singleton[simp]:
  "min_source_att [x] = Some x"
  by (fastforce simp: min_source_att_def min_by_key1_def)

lemma max_target_att_double_vote:
  "attestations \<noteq> [] \<Longrightarrow>
   att_max_target = the (max_target_att attestations) \<Longrightarrow>
   epoch (target witness) = epoch (target att_max_target) \<Longrightarrow>
   safe_to_sign good [witness] \<Longrightarrow>
   epoch (target att_max_target) < epoch (target good)"
  apply (case_tac "attestations")
   apply fastforce
  apply (fastforce simp: max_target_att_def safe_to_sign1_def)
  done

lemma not_double_vote_lt:
  "epoch (target witness) < epoch (target good) \<Longrightarrow>
   is_double_vote good witness \<Longrightarrow>
   False"
  by (fastforce simp: is_double_vote_def)

lemma not_surrounds_le:
  "surrounds good witness \<Longrightarrow>
   epoch (source witness) \<le> epoch (source good) \<Longrightarrow>
   False"
  by (fastforce simp: surrounds_def)

lemma not_surrounded_lt:
  "surrounds witness good \<Longrightarrow>
   epoch (target witness) < epoch (target good) \<Longrightarrow>
   False"
  by (fastforce simp: surrounds_def)

(* General correctness lemma about any slashing protection witness *)
lemma slashing_protection_witness_correct:
  "attestations \<noteq> [] \<Longrightarrow>
   att_max_source = the (max_source_att attestations) \<Longrightarrow>
   att_max_target = the (max_target_att attestations) \<Longrightarrow>
   epoch (source witness) = epoch (source att_max_source) \<Longrightarrow>
   epoch (target witness) = epoch (target att_max_target) \<Longrightarrow>
   safe_to_sign good [witness] \<Longrightarrow>
   \<not> is_slashable_wrt good attestations"
  apply (clarsimp simp: is_slashable_wrt_def is_slashable_def)
  (* Good attestation isn't a double vote *)
  apply (rule conjI)
   apply (clarsimp simp: is_double_vote_def)
   apply (subgoal_tac "epoch (target prev) < epoch (target good)")
    apply fastforce
   apply (rule_tac b="epoch (target (the (max_target_att attestations)))"
                   in dual_order.strict_trans2)
    apply (rule max_target_att_double_vote[where witness=witness])
      apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply (rule max_target_att_le)
    apply fastforce
   apply assumption
  (* Good attestation doesn't surround previous *)
  apply (rule conjI)
   apply clarsimp
   apply (erule not_surrounds_le)
   apply (rule order_trans[where y="epoch (source witness)"])
    apply (fastforce simp: max_source_att_le)
   apply (fastforce simp: safe_to_sign1_def)
  (* Good attestation isn't surrounded by previous *)
  apply clarsimp
  apply (erule not_surrounded_lt)
  apply (rule dual_order.strict_trans2[where b="epoch (target witness)"])
   apply (fastforce simp: safe_to_sign1_def)
  apply (fastforce simp: max_target_att_le)
  done

(* Synthetic minification (oblivious to existing slashings) *)
definition minify_synth :: "attestation list \<Rightarrow> attestation" where
  "minify_synth attestations \<equiv> let
    att_max_source = the (max_source_att attestations);
    att_max_target = the (max_target_att attestations);
    synth_root = 0;
    source = \<lparr> epoch = epoch (source att_max_source), root = synth_root \<rparr>;
    target = \<lparr> epoch = epoch (target att_max_target), root = synth_root \<rparr> in
    \<lparr> source = source, target = target \<rparr>"

lemma minify_synth_correct:
  "attestations \<noteq> [] \<Longrightarrow>
   witness = minify_synth attestations \<Longrightarrow>
   safe_to_sign good [witness] \<Longrightarrow>
   \<not> is_slashable_wrt good attestations"
  by (rule slashing_protection_witness_correct;
      fastforce simp: minify_synth_def)

(* Max-target minification (sensitive to existing slashings) *)
definition minify_max :: "attestation list \<Rightarrow> attestation" where
  "minify_max attestations \<equiv> the (max_target_att attestations)"

lemma max_source_att_elem:
  "attestations \<noteq> [] \<Longrightarrow>
   the (max_source_att attestations) \<in> set attestations"
  by (fastforce simp: max_source_att_def intro: max_by_key_elem)

lemma max_target_att_elem:
  "attestations \<noteq> [] \<Longrightarrow>
   the (max_target_att attestations) \<in> set attestations"
  by (fastforce simp: max_target_att_def intro: max_by_key_elem)

(* If the attestations to summarise are not mutually slashable, then
   the source epochs of the max source attestation & max target attestation
   are equal.
*)
lemma max_source_eq_max_target:
  "attestations \<noteq> [] \<Longrightarrow>
   not_mutually_slashable attestations \<Longrightarrow>
   epoch (source (the (max_source_att attestations))) =
     epoch (source (the (max_target_att attestations)))"
  apply (clarsimp simp: not_mutually_slashable_def)
  apply (subgoal_tac "\<not> is_slashable (the (max_source_att attestations))
                                      (the (max_target_att attestations))")
   apply (clarsimp simp: is_slashable_def is_double_vote_def surrounds_def)
   apply (metis le_neq_trans max_source_att_elem max_target_att_elem
                max_source_att_le max_target_att_le)
  apply (erule ballE, erule ballE, assumption)
  by (auto simp: max_target_att_elem max_source_att_elem)

(* Therefore minify_max is correct under the assumption that the input
   attestations are not mutually slashable. *)
lemma minify_max_correct:
  "attestations \<noteq> [] \<Longrightarrow>
   not_mutually_slashable attestations \<Longrightarrow>
   witness = minify_max attestations \<Longrightarrow>
   safe_to_sign good [witness] \<Longrightarrow>
   \<not> is_slashable_wrt good attestations"
  apply (rule slashing_protection_witness_correct[where witness=witness])
       apply (fastforce+)[3]
  by (auto simp: max_source_eq_max_target minify_max_def)

end