theory Ch5
imports Main  Transitions Ch4
begin

(*
Inductive value : exp -> Prop :=
| value_num : forall i,
    value (exp_num i)
| value_str : forall s,
    value (exp_str s).
*)

inductive "value" :: "exp \<Rightarrow> bool" where
  value_num: "value (exp_num i)"
| value_str: "value (exp_str s)"
lemmas value.intros[intro]

(*
Inductive eval : exp -> exp -> Prop :=
| eval_op_plus : forall n1 n2,
    eval (exp_op plus (exp_num n1) (exp_num n2)) (exp_num (n1 + n2))
| eval_op_fst : forall e1 e1' e2 op,
    eval e1 e1' ->
    lc e2 ->
    eval (exp_op op e1 e2) (exp_op op e1' e2)
| eval_op_snd : forall e1 e2 e2' op,
    value e1 -> eval e2 e2' ->
    eval (exp_op op e1 e2) (exp_op op e1 e2')
| eval_let_rhs : forall e1 e1' e2,
    eval e1 e1' ->
    lc (exp_let e1 e2) ->
    eval (exp_let e1 e2) (exp_let e1' e2)
| eval_let_red : forall e1 e2,
    value e1 ->
    lc (exp_let e1 e2) ->
    eval (exp_let e1 e2) (open e2 e1).
*)

inductive eval :: "exp \<Rightarrow> exp \<Rightarrow> bool" where
  eval_op_plus :
    "eval (exp_op plus (exp_num n1) (exp_num n2)) (exp_num (n1 + n2))"
| eval_op_fst : 
    "eval e1 e1' \<Longrightarrow>  lc e2 \<Longrightarrow>
    eval (exp_op opr e1 e2) (exp_op opr e1' e2)"
| eval_op_snd:
    "value e1 \<Longrightarrow> eval e2 e2' \<Longrightarrow>
    eval (exp_op opr e1 e2) (exp_op opr e1 e2')"
| eval_let_rhs : 
    "eval e1 e1' \<Longrightarrow> lc (exp_let e1 e2) \<Longrightarrow>
    eval (exp_let e1 e2) (exp_let e1' e2)"
| eval_let_red :
    "value e1 \<Longrightarrow> lc (exp_let e1 e2) \<Longrightarrow>
    eval (exp_let e1 e2) (open e2 e1)"
lemmas eval.intros[intro]

(*
Module Evaluation.
  Definition S := exp.
  Definition state := lc.
  Definition initial := lc.
  Definition final := value.
  Definition step  := eval.
  Lemma final_state : forall e, value e -> lc e.
  Proof. 
    intros e H. inversion H. auto. auto.
  Qed.
  Lemma initial_state : forall e, initial e -> lc e.
  Proof.
    intros. auto.
  Qed.
  Lemma step_states : forall (e1:exp) (e2:exp), eval e1 e2 -> lc e1 /\ lc e2.
  Proof.
    intros e1 e2 H. induction H.
    - auto.
    - destruct IHeval. auto.
    - destruct IHeval. auto using final_state.
    - destruct IHeval. inversion H0. eauto.
    - inversion H0. split. eauto using final_state.
      pick fresh x.
      rewrite (subst_intro x).
      apply subst_lc. auto. auto. auto.
  Qed.    

  Lemma final_does_not_step : forall (e:exp), final e -> not (exists e', step e e').
  Proof.
    intros e F. unfold not. intros H. inversion F;
    subst; destruct H as [e' S]; inversion S.
  Qed.

End Evaluation.
Export Evaluation.
*)

lemma final_state':
  assumes "value s"
  shows "lc s"
using assms by induction auto

interpretation TransitionSystem lc "value" lc eval
proof
  fix s
  assume "value s"
  thus "lc s" by (rule final_state')
next
  fix s1 s2
  assume "eval s1 s2"
  thus "lc s1 \<and> lc s2"
  proof (induction)
    case (eval_let_red e1 e2)

    obtain y where "y |\<notin>| fv e2" by (rule have_fresh_atom)

    from `lc (exp_let e1 e2)`
    obtain "lc e1" and "lc (open e2 (exp_fvar y))"  by (auto elim: lc_let_inversion)

    from this(2) this(1)
    have "lc ([y \<leadsto> e1](open e2 (exp_fvar y)))" by (rule subst_lc)
    with `y |\<notin>| fv e2`
    have "lc (open e2 e1)"
       by (simp add: subst_intro)
    with `lc (exp_let e1 e2)`
    show "lc (exp_let e1 e2) \<and> lc (open e2 e1)" by simp
  qed (auto intro: final_state' elim: lc_let_inversion)
next
  fix s
  assume "value s"
  thus "\<not> (\<exists>s'. eval s s')"
    by cases (auto elim: eval.cases)
qed


end