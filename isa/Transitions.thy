theory Transitions imports Main
begin

(*
Module Type TransitionSystem.
  Parameter S : Set.
  Parameter state : S -> Prop.

  Parameter final : S -> Prop.
  Axiom final_state : forall s, final s -> state s.

  Parameter initial : S -> Prop.
  Axiom initial_state : forall s, initial s -> state s.
  
  Parameter step : S -> S -> Prop.
  Axiom step_states : forall s1 s2, step s1 s2 -> state s1 /\ state s2.

  Axiom final_does_not_step : forall s, final s -> not (exists s', step s s').    
  
End TransitionSystem.
*)
locale TransitionSystem =
  fixes state :: "'a \<Rightarrow> bool"
  fixes final :: "'a \<Rightarrow> bool"
  assumes final_state: "final s \<Longrightarrow> state s"
  fixes initial :: "'a \<Rightarrow> bool"
  assumes initial_state: "initial s \<Longrightarrow> state s"
  fixes step :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes step_states: "step s1 s2 \<Longrightarrow> state s1 \<and> state s2"
  assumes final_does_not_step: "final s \<Longrightarrow> \<not>(\<exists> s'. step s s')"
begin

(*
  Definition stuck (s : S) :=
    not (final s) /\ not (exists s', step s s').
*)
definition "stuck s \<longleftrightarrow> \<not> final s \<and> \<not>(\<exists> s'. step s s')"

(*
  Inductive multistep : S -> S -> Prop :=
    | ms_refl : forall s, state s -> multistep s s
    | ms_step : forall s s' s'', step s s' -> multistep s' s'' -> multistep s s''.        
*)
inductive multistep where
  ms_refl : "state s \<Longrightarrow> multistep s s"
| ms_step: "step s s' \<Longrightarrow> multistep s' s'' \<Longrightarrow> multistep s s''"

(*
  Lemma multistep_transitive : forall s s' s'',
      multistep s s' -> multistep s' s'' -> multistep s s''.
*)
lemma multistep_transitive:
  "multistep s s' \<Longrightarrow> multistep s' s'' \<Longrightarrow> multistep s s''"
by (induction rule: multistep.induct) (auto intro: multistep.intros)

(*
  Lemma multistep_states : forall s1 s2, multistep s1 s2 -> state s1 /\ state s2.
*)
lemma multistep_states:
  "multistep s1 s2 \<Longrightarrow> state s1 \<and> state s2"
by (induction rule: multistep.induct) (auto dest: step_states)

(*
  Definition transition_sequence s s' (ms : multistep s s') := initial s.
*)
(* Arg! Dependent types. Are we at the end now? *)
definition "transition_sequence s s' \<longleftrightarrow> multistep s s' \<and> initial s"

(*
  Definition maximal_transition_sequence s s' (ms : multistep s s') :=
    initial s /\ not (exists s'', step s' s'').
*)
definition "maximal_transition_sequence s s' \<longleftrightarrow> initial s \<and> \<not> (\<exists> s''. step s' s'')"

(*
  Definition complete_transition_sequence s s' (ms : multistep s s') :=
    initial s /\ final s'.
*)
definition "complete_transition_sequence s s' \<longleftrightarrow> initial s \<and> final s'"

end


end