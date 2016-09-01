theory Ch4
imports
  Main
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/AList"
  "~~/src/HOL/Eisbach/Eisbach"
begin

section \<open>Atoms (replaces Metalib)\<close>

typedef atom = "UNIV :: nat set" by auto

lemma have_fresh_atom:
  obtains x :: atom where "x |\<notin>| L"
proof-
  from infinite_UNIV_nat finite_fset
  have "\<exists> y . y \<notin> fset (Rep_atom |`| L)"
    by (rule ex_new_if_finite)
  then obtain y where "y \<notin> fset (Rep_atom |`| L)"..
  hence "Abs_atom y |\<notin>| L"
    by (metis Abs_atom_inverse UNIV_I fimage_eqI notin_fset)
  thus ?thesis by (rule that)
qed

lemma exists_fresh_atom: "\<exists> x :: atom . x |\<notin>| L"
  by (rule have_fresh_atom) (rule exI)


section \<open>Terms\<close>

(*
Inductive typ : Set :=
  | typ_num     : typ
  | typ_string  : typ.
*)

datatype type = typ_num | typ_string

(*
Inductive op : Set :=
  | plus
  | times
  | cat.
*)

datatype opr = plus | times | cat

(*
(* expressions of E *)
Inductive exp : Set :=
  (* bound and free variables *)
  | exp_bvar : nat  -> exp
  | exp_fvar : atom -> exp
  (* constants *)                        
  | exp_num  : nat -> exp                     
  | exp_str  : string -> exp
  (* binary operators *)                          
  | exp_op   : op -> exp -> exp -> exp
  (* skip length *)
  (* let expressions *)                                  
  | exp_let  : exp  -> exp -> exp.
*)

datatype exp = exp_bvar nat | exp_fvar atom | exp_num nat | exp_str string
             | exp_op opr exp exp | exp_let exp exp

(*
Parameter Y : atom.
Definition demo_rep1 :=
  exp_let (exp_op plus (exp_fvar Y) (exp_num 1)) (exp_bvar 0).
Definition demo_rep2 :=
  exp_let (exp_num 1) (exp_let (exp_num 2) (exp_op plus (exp_bvar 1) (exp_bvar 0))).

*)

context fixes Y :: atom
begin
definition  "demo_rep1 = exp_let (exp_op plus (exp_fvar Y) (exp_num 1)) (exp_bvar 0)"
definition "demo_rep2 = exp_let (exp_num 1) (exp_let (exp_num 2) (exp_op plus (exp_bvar 1) (exp_bvar 0)))"
end

(*
Fixpoint subst (z : atom) (u : exp) (e : exp)
  {struct e} : exp :=
  match e with
    | exp_bvar i => e
    | exp_fvar x => if x == z then u else e
    | exp_num _ => e
    | exp_str _ => e
    | exp_let e1 e2 => exp_let (subst z u e1) (subst z u e2)
    | exp_op o e1 e2 => exp_op o (subst z u e1) (subst z u e2)
  end.
*)

fun subst :: "atom \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp"  ("[_ \<leadsto> _]_" [100,100,1000] 1000) where
  "subst z u (exp_fvar x) = (if x = z then u else exp_fvar x)"
| "subst z u (exp_op opr e\<^sub>1 e\<^sub>2) = exp_op opr (subst z u e\<^sub>1) (subst z u e\<^sub>2)"
| "subst z u (exp_let e\<^sub>1 e\<^sub>2) = exp_let (subst z u e\<^sub>1) (subst z u e\<^sub>2)"
| "subst z u e = e"

context fixes Y Z :: atom
begin
(*
Lemma demo_subst1:
  [Y ~> exp_fvar Z] (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Y)))
                  = (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Z))).
*)
lemma demo_subst1:
  "[Y \<leadsto> exp_fvar Z] (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Y)))
                   = (exp_let (exp_num 1) (exp_op plus (exp_bvar 0) (exp_fvar Z)))"
by simp
end

(*
Lemma subst_eq_var: forall (x : atom) u,
  [x ~> u](exp_fvar x) = u.
Lemma subst_neq_var : forall (x y : atom) u,
  y <> x -> [x ~> u](exp_fvar y) = exp_fvar y.
*)
lemma subst_eq_var: "[x \<leadsto> u](exp_fvar x) = u" by simp
lemma subst_neq_var: "y \<noteq> x \<Longrightarrow> [x \<leadsto> u](exp_fvar y) = exp_fvar y" by simp

(*
Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | exp_fvar x => singleton x
    | exp_let e1 e2 => fv e1 `union` fv e2
    | exp_op o e1 e2 => fv e1 `union` fv e2
    | _ => empty 
  end.
*)
fun fv :: "exp \<Rightarrow> atom fset" where
  "fv (exp_fvar x) = {|x|}"
| "fv (exp_let e1 e2) = fv e1 |\<union>| fv e2"
| "fv (exp_op opr e1 e2) = fv e1 |\<union>| fv e2"
| "fv _ = {||}"

(*
Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
*)
lemma subst_fresh[simp]: "x |\<notin>| fv e \<Longrightarrow> [x \<leadsto> u] e = e"
  by (induction e) auto

(*
Lemma subst_notin_fv : forall x y u e,
   x `notin` fv e -> x `notin` fv u ->
   x `notin` fv ([y ~> u]e).
*)

lemma subst_notin_fv: "x |\<notin>| fv e \<Longrightarrow> x |\<notin>| fv u \<Longrightarrow> x |\<notin>| fv ([y \<leadsto> u]e)"
  by (induction e) auto

(*
Fixpoint open_rec (k : nat) (u : exp)(e : exp)
  {struct e} : exp :=
  match e with
    | exp_bvar i => if k == i then u else (exp_bvar i)
    | exp_let e1 e2 => exp_let (open_rec k u e1) (open_rec (S k) u e2)
    | exp_op o e1 e2 => exp_op o (open_rec k u e1) (open_rec k u e2)
    | _ => e 
  end.
*)
fun open_rec :: "nat \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" ("{_ \<leadsto> _}_" [100,100,1000] 1000) where
  "open_rec k u (exp_bvar i) = (if k = i then u else exp_bvar i)"
| "open_rec k u (exp_let e\<^sub>1 e\<^sub>2) = exp_let (open_rec k u e\<^sub>1) (open_rec (Suc k) u e\<^sub>2)"
| "open_rec k u (exp_op opr e\<^sub>1 e\<^sub>2) = exp_op opr (open_rec k u e\<^sub>1) (open_rec k u e\<^sub>2)"
| "open_rec k u e = e"

(*
Definition open e u := open_rec 0 u e.
*)
definition "open e u = open_rec 0 u e"

(*
Lemma demo_open :
  open (exp_let (exp_str "a") (exp_op plus (exp_bvar 1) (exp_bvar 0))) (exp_fvar Y) =
       (exp_let (exp_str "a") (exp_op plus (exp_fvar Y) (exp_bvar 0))).
*)

lemma demo_open :
  "open (exp_let (exp_str ''a'') (exp_op plus (exp_bvar 1) (exp_bvar 0))) (exp_fvar Y) =
        (exp_let (exp_str ''a'') (exp_op plus (exp_fvar Y) (exp_bvar 0)))"
by (simp add: open_def)

(*
Inductive lc : exp -> Prop :=
  | lc_var : forall (x:atom), lc (exp_fvar x)
  | lc_num : forall n : nat, lc (exp_num n)
  | lc_str : forall s : string, lc (exp_str s)
  | lc_let : forall L (e1 e2 : exp),
      lc e1 
      -> (forall x, x `notin` L -> lc (open e2 (exp_fvar x)))
      -> lc (exp_let e1 e2)
  | lc_op : forall (e1 e2 : exp) (op : op),
      lc e1
      -> lc e2
      -> lc (exp_op op e1 e2).
*)

inductive lc :: "exp \<Rightarrow> bool" where
  lc_var: "lc (exp_fvar x)"
| lc_num: "lc (exp_num n)"
| lc_str: "lc (exp_str s)"
| lc_let: "lc e\<^sub>1 \<Longrightarrow> (\<And> x. x |\<notin>| L \<Longrightarrow> lc (open e\<^sub>2 (exp_fvar x))) \<Longrightarrow> lc (exp_let e\<^sub>1 e\<^sub>2)"
| lc_app: "lc e\<^sub>1 \<Longrightarrow> lc e\<^sub>2 \<Longrightarrow> lc (exp_op opr e\<^sub>1 e\<^sub>2)"

lemmas lc.intros[intro]
inductive_cases [elim!]: "lc (exp_op opr e\<^sub>1 e\<^sub>2)"
inductive_cases [elim!]: "lc (exp_bvar i)"


(*
Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
*)

lemma open_rec_lc_core:
  "i \<noteq> j \<Longrightarrow> {i \<leadsto> u} ({j \<leadsto> v} e) = {j \<leadsto> v} e \<Longrightarrow> {i \<leadsto> u} e = e"
  apply (induction e arbitrary: i j)
  apply auto
  using nat.inject apply blast
  done

(* The lemma above, for open *)
lemma open_lc_core:
  "i \<noteq> 0 \<Longrightarrow> {i \<leadsto> u} (open e v) = open e v  \<Longrightarrow> {i \<leadsto> u} e = e"
  unfolding open_def by (rule open_rec_lc_core)

(*
Lemma open_rec_lc : forall k u e,
  lc e -> e = {k ~> u} e.
*)

lemma open_rec_lc[simp]: "lc e \<Longrightarrow> {k \<leadsto> u} e = e"
proof (induction arbitrary: k rule: lc.induct)
case (lc_let e\<^sub>1 L e\<^sub>2)
  have "open_rec k u e\<^sub>1 = e\<^sub>1" by fact
  moreover
  obtain x where "x |\<notin>| L" by (rule have_fresh_atom)
  then have "{Suc k \<leadsto> u}(open e\<^sub>2 (exp_fvar x)) = open e\<^sub>2 (exp_fvar x)"  by (rule lc_let.IH)
  hence "{Suc k \<leadsto> u} e\<^sub>2 = e\<^sub>2" by (rule open_lc_core[rotated]) simp
  ultimately
  show ?case by simp
qed auto

(*
Lemma subst_open_rec : forall e1 e2 u (x : atom) k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
*)
lemma subst_open_rec[simp]:
  assumes "lc u"
  shows "[x \<leadsto> u]{k \<leadsto> e\<^sub>1}e\<^sub>2 = {k \<leadsto> [x \<leadsto> u]e\<^sub>1}[x \<leadsto> u]e\<^sub>2"
using assms
by (induction k e\<^sub>1 e\<^sub>2 rule:open_rec.induct) auto

(*
Lemma subst_open : forall (x : atom) u e1 e2,
  lc u ->
  open ([x ~> u] e1) ([x ~> u] e2) = [x ~> u] (open e1 e2).
*)
lemma subst_open[simp]:
  assumes "lc u"
  shows "[x \<leadsto> u](open e\<^sub>1 e\<^sub>2) = open ([x \<leadsto> u] e\<^sub>1) ([x \<leadsto> u] e\<^sub>2)"
using assms by (auto simp add: open_def)

lemma open_subst:
  assumes "lc u" and "x |\<notin>| fv e\<^sub>2"
  shows "open ([x \<leadsto> u] e\<^sub>1) e\<^sub>2 = [x \<leadsto> u](open e\<^sub>1 e\<^sub>2)"
by (simp add: assms)

(*
Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
*)
lemma  subst_lc:
  assumes "lc e" and [simp]: "lc u"
  shows "lc ([x \<leadsto> u] e)"
using `lc e`
proof (induction rule: lc.induct)
  case (lc_let e\<^sub>1 L e\<^sub>2)

  have "lc (exp_let [x \<leadsto> u]e\<^sub>1 [x \<leadsto> u]e\<^sub>2)"
  proof(rule lc.lc_let)
    show "lc [x \<leadsto> u]e\<^sub>1" by fact
  next
    fix y :: atom
    assume "y |\<notin>| L |\<union>| {| x |}"
    hence "y |\<notin>| L" by simp
    hence "lc [x \<leadsto> u](open e\<^sub>2 (exp_fvar y))" by (rule lc_let.IH)
    thus "lc (open [x \<leadsto> u]e\<^sub>2 (exp_fvar y))"
      using `y |\<notin>| L |\<union>| {| x |}` by auto
  qed
  thus ?case by simp
qed auto


(*
Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  open e u = [x ~> u](open e (exp_fvar x)).
*)

lemma subst_open_rec_intro[simp]:
  "x |\<notin>| fv e \<Longrightarrow> [x \<leadsto> u]{k \<leadsto> exp_fvar x}e = {k \<leadsto> u}e"
by (induction k u e rule: open_rec.induct) auto

lemma subst_intro:
  "x |\<notin>| fv e \<Longrightarrow> [x \<leadsto> u](open e (exp_fvar x)) = open e u"
unfolding open_def by (rule subst_open_rec_intro)

(*
Lemma fv_open : forall e1 e2,
    fv (open e1 e2) [<=] fv e2 \u fv e1.
*)

lemma fv_open_rec: "fv (open_rec k e u) |\<subseteq>| fv e |\<union>| fv u"
by (induction rule: open_rec.induct) auto

lemma fv_open: "fv (open e1 e2) |\<subseteq>| fv e2 |\<union>| fv e1"
unfolding open_def by (rule fv_open_rec)


(*
Lemma subst_lc_inverse : forall x u e, lc ([x ~> u] e) -> lc u -> lc e.
Proof.
(* CHALLENGE EXERCISE *) Admitted.
*)
lemma subst_lc_inverse:
  assumes "lc ([x \<leadsto> u] e)"
  assumes "lc u"
  shows "lc e"
using assms(1)
proof(induction "[x \<leadsto> u] e" arbitrary: x e rule: lc.induct)
case (lc_let e\<^sub>1 L e\<^sub>2 x e)
  show ?case
  proof (cases "\<exists>x. e = exp_fvar x")
    case True
    thus "lc e" by auto
  next
    case False
    with `exp_let e\<^sub>1 e\<^sub>2 = [x \<leadsto> u]e`
    obtain e\<^sub>1' e\<^sub>2' where [simp]: "e = exp_let e\<^sub>1' e\<^sub>2'"  "e\<^sub>1 = [x \<leadsto> u]e\<^sub>1'"  "e\<^sub>2 = [x \<leadsto> u]e\<^sub>2'"
      by (auto elim!: subst.elims[OF sym])

    show ?thesis
    unfolding `e = exp_let e\<^sub>1' e\<^sub>2'`
    proof
      show "lc e\<^sub>1'" by (auto intro: lc_let.hyps(2))
    next
      fix y
      assume "y |\<notin>| L |\<union>| {|x|}"
      thus "lc (open e\<^sub>2' (exp_fvar y))" using `lc u` by (auto intro:  lc_let.hyps(4))
    qed
  qed
qed (auto elim!: subst.elims[OF sym])


(* Experiment: The same as above, trying to use tactics *)

method lc_let_with_find_fresh = 
  (match premises in "?H ([x \<leadsto> _]_)" for x \<Rightarrow> \<open>
    match premises in "?H2 (L :: atom fset) \<Longrightarrow> _" for L \<Rightarrow> \<open>
    rule lc_let[where L = "L |\<union>| {|x|}"]
   \<close>
\<close>)

lemma subst_lc_inverse_variant:
  assumes "lc ([x \<leadsto> u] e)"
  assumes [simp]: "lc u"
  notes open_subst[simp] subst_open[simp del]
  shows "lc e"
using assms(1)
apply(induction "[x \<leadsto> u] e" arbitrary: x e rule: lc.induct)
apply(auto elim!: subst.elims[OF sym])
apply(lc_let_with_find_fresh; auto)
done

section \<open>Typing environments\<close>

(*
Notation env := (list (atom * typ)).
*)
type_synonym env  = "(atom \<times> type) list"

abbreviation "binds x T E \<equiv> (x,T) \<in> set E"

abbreviation singleton_env (infix "~" 60) where
  "x ~ T \<equiv> [(x,T)]"

(*
Lemma binds_demo : forall (x:atom) (T:typ) (E F:env),
  binds x T (E ++ (x ~ T) ++ F).
*)
lemma binds_demo: "binds x T (E @ (x ~ T) @ F)" 
  by simp

(*
Lemma dom_demo : forall (x y : atom) (T : typ),
  dom (x ~ T) [=] singleton x.
*)
abbreviation dom where "dom E \<equiv> fst ` set E"

lemma dom_demo: "dom (x ~ T) =  {x}" by simp

abbreviation uniq where "uniq E \<equiv> distinct (map fst E)"
(*
Lemma uniq_demo : forall (x y : atom) (T : typ),
  x <> y -> uniq ((x ~ T) ++ (y ~ T)).
*)
lemma uniq: "x \<noteq> y \<Longrightarrow> uniq ((x ~ T) @ (y ~ T))" by simp

section \<open>Typing rules\<close>

(*
Inductive typing : env -> exp -> typ -> Prop :=
| typing_var : forall E (x : atom) T,
    uniq E ->
    binds x T E ->
    typing E (exp_fvar x) T
| typing_str  : forall s E,
    uniq E ->
    typing E (exp_str s) typ_string
| typing_num  : forall i E,
    uniq E ->
    typing E (exp_num i) typ_num
| typing_let : forall (L : atoms) E e1 e2 T1 T2,
    typing E e1 T1 ->
    (forall (x:atom), x `notin` L ->
                 typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2) ->
    typing E (exp_let e1 e2) T2
| typing_op : forall E e1 e2,
    typing E e1 typ_num ->
    typing E e2 typ_num ->
    typing E (exp_op plus e1 e2) typ_num.
*)

inductive typing where
  typing_var: "uniq E \<Longrightarrow> binds x T E \<Longrightarrow> typing E (exp_fvar x) T"
| typing_str: "uniq E \<Longrightarrow> typing E (exp_str s) typ_string"
| typing_num: "uniq E \<Longrightarrow> typing E (exp_num i) typ_num"
| typing_let :
    "typing E e1 T1 \<Longrightarrow>
    (\<And>x. x |\<notin>| L \<Longrightarrow>
      typing ((x, T1)#E) (open e2 (exp_fvar x)) T2) \<Longrightarrow>
    typing E (exp_let e1 e2) T2"
| typing_op :
    "typing E e1 typ_num \<Longrightarrow>
     typing E e2 typ_num \<Longrightarrow> 
     typing E (exp_op plus e1 e2) typ_num"

inductive_cases typing_elims:
  "typing E (exp_fvar x) T" 
  "typing E (exp_str s) T"
  "typing E (exp_num i) T"
  "typing E (exp_let e1 e2) T"
  "typing E (exp_op plus e1 e2) T"

(*
typing_lc : forall G e T, typing G e T -> lc e.
*)
lemma typing_lc : 
  assumes "typing G e T"
  shows "lc e"
using assms by induction auto

lemma uniq_bind[consumes 3]:
  "uniq E \<Longrightarrow> binds x T1 E \<Longrightarrow> binds x T2 E \<Longrightarrow> T1 = T2"
using map_of_is_SomeI by fastforce

(*
Lemma unicity : forall G e t1, typing G e t1 -> forall t2, typing G e t2 -> t1 = t2.
*)
(* Ugly apply script... *)
lemma unicity: "typing G e t1 \<Longrightarrow> typing G e t2 \<Longrightarrow> t1 = t2"
proof (induction G e t1 arbitrary: t2 rule: typing.induct)
  case (typing_let E e1 T1 L e2 T2 T2')

  from typing_elims(4)[OF `typing E (exp_let e1 e2) T2'`]
  obtain T1' L' where
    "typing E e1 T1'"
    and
    asm: "\<And>x. x |\<notin>| L' \<Longrightarrow> typing ((x, T1') # E) (open e2 (exp_fvar x)) T2'"
  by blast

  obtain x where "x |\<notin>| L |\<union>| L'" by (rule have_fresh_atom)
  hence "x |\<notin>| L" and "x |\<notin>| L'" by simp_all

  from `typing E e1 T1'` have "T1 = T1'" by (rule typing_let.IH(1))
  with asm `x |\<notin>| L'`
  have "typing ((x, T1) # E) (open e2 (exp_fvar x)) T2'" by auto
  with `x |\<notin>| L`
  show "T2 = T2'" by (rule typing_let.IH(2))
qed(auto elim!: typing_elims elim: uniq_bind)
(* The same, as an ugly apply script: *)
(*
apply (induction G e t1 arbitrary: t2 rule: typing.induct)
apply (auto elim!: typing_elims elim: uniq_bind)[1]
apply (auto elim!: typing_elims)[2]
apply (erule typing_elims)
apply (subgoal_tac "\<exists>x. x |\<notin>| L |\<union>| La" )
apply (erule exE)
apply auto[1]
apply (rule exists_fresh_atom)
apply (auto elim!: typing_elims)[1]
done
*)

end