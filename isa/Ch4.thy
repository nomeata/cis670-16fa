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

lemma subst_fvarE[elim]:
  assumes "exp_fvar x = subst z u e"
  obtains "e = exp_fvar x" and "z \<noteq> x"
        | "e = exp_fvar z" and "u = exp_fvar x"
using assms by (auto elim!: subst.elims[OF sym] split: if_splits)

lemma subst_letE[elim]:
  assumes "exp_let e\<^sub>1 e\<^sub>2 = subst z u e"
  obtains e\<^sub>1' e\<^sub>2' where "e = exp_let e\<^sub>1' e\<^sub>2'" and "e\<^sub>1 = subst z u e\<^sub>1'" and "e\<^sub>2 = subst z u e\<^sub>2'"
        | "e = exp_fvar z" and "u = exp_let e\<^sub>1 e\<^sub>2"
using assms by (auto elim!: subst.elims[OF sym] split: if_splits)


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

lemma open_fvar[simp]: "open (exp_fvar x) u = exp_fvar x"
  unfolding open_def by simp

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

lemma fv_open_elim[elim]:
  assumes "x |\<in>| fv (open e1 e2)"
  obtains "x |\<in>|  fv e2" | "x |\<in>| fv e1"
using assms fv_open by blast

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

fun fdom :: "('a \<times> 'b) list \<Rightarrow> 'a fset" where
  "fdom [] = {||}"
 |"fdom ((x,T)#E) = finsert x (fdom E)"

lemma fmember_fdom[simp]: "x |\<in>| fdom E \<longleftrightarrow> x \<in> dom E"
  by (induction E rule: fdom.induct) auto

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

(*
Lemma typing_weakening_strengthened :  forall (E F G : env) e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
*)
lemma typing_weakening_strengthened:
  assumes "typing (G @ E) e T" and "uniq (G @ F @ E)"
  shows "typing (G @ F @ E) e T"
using assms
apply (induction "G @ E" e T arbitrary: G rule: typing.induct )
apply (auto intro: typing.intros)
apply (erule_tac L = "L |\<union>| fdom F |\<union>| fdom E |\<union>| fdom G" in typing_let)
apply auto
apply (fastforce  simp del: append_Cons simp add: append_Cons)
done

lemmas typing_weakening_one =
  typing_weakening_strengthened[where F = "(x ~ T')" for x T', unfolded append.simps]
lemmas typing_weakening_one_from =
  typing_weakening_one[where G = "[]", unfolded append.simps]


(*
Lemma typing_weakening : forall (E F : env) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
*)
lemma typing_weakening:
  assumes "typing E e T" and "uniq (F @ E)"
  shows "typing (F @ E) e T"
using typing_weakening_strengthened[where G = "[]"] assms by simp

(*
Lemma typing_subst : forall (E F : env) e u S T (z : atom),
  typing (F ++ (z ~ S) ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
*)

lemma typing_subst:
  assumes "typing (F @ (z ~ S) @ E) e T"
  and "typing E u S"
  shows "typing (F @ E) ([z \<leadsto> u] e) T"
using assms[unfolded append_Cons append_Nil]
proof(induction "(F @ (z, S) # E)" e T arbitrary: F  rule: typing.induct)
case (typing_let e1 T1 L e2 T2 F)
  from `typing _ u _` have [simp]: "lc u" by (rule typing_lc)
  have "typing (F @ E) (exp_let [z \<leadsto> u]e1 [z \<leadsto> u]e2) T2"
  by (rule typing.typing_let[where L = "L |\<union>| fv e2 |\<union>| {|z|}"])
     (auto intro!: typing_let.hyps(2,4) typing_let.prems
              simp add: open_subst append_Cons[symmetric]
              simp del: subst_open append_Cons
              )
  thus ?case by simp
qed (auto intro: typing_weakening typing.intros simp add: rev_image_eqI)

(*
Lemma typing_subst_simple : forall (E : env) e u S T (z : atom),
  typing ((z ~ S) ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
*)
lemma typing_subst_simple:
  assumes "typing ((z ~ S) @ E) e T"
  and "typing E u S"
  shows "typing E ([z \<leadsto> u] e) T"
using typing_subst[where F = "[]", simplified] assms[simplified].


(*
Lemma exchange : forall G1 G2 x1 x2 T1 T2 e T,
    typing (G1 ++ (x1 ~ T1) ++ (x2 ~ T2) ++ G2) e T ->
    typing (G1 ++ (x2 ~ T2) ++ (x1 ~ T1) ++ G2) e T.
*)
lemma exchange:
  assumes "typing (G1 @ (x1 ~ T1) @ (x2 ~ T2) @ G2) e T"
  shows   "typing (G1 @ (x2 ~ T2) @ (x1 ~ T1) @ G2) e T"
using assms
apply (induction "(G1 @ (x1 ~ T1) @ (x2 ~ T2) @ G2)" e T arbitrary: G1 rule: typing.induct)
apply (auto intro: typing.intros)
apply (rule_tac L = L in typing_let)
apply fastforce+
done

(*
Lemma strengthening : forall G e T,
    typing G e T
    -> forall G1 G2 x U, 
      G = G1 ++ (x ~ U) ++ G2 -> x `notin` fv e -> typing (G1 ++ G2) e T.
*)
lemma strengthening:
assumes "typing (G1 @ (x ~ U) @ G2) e T"
assumes "x |\<notin>| fv e"
shows   "typing (G1 @ G2) e T"
using assms
proof (induction "G1 @ (x ~ U) @ G2" e T arbitrary: G1 rule: typing.induct)
case (typing_let e1 T1 L e2 T2 G1)
  note IH =
    typing_let.hyps(2)
    (* This is annoying, as otherwise it would be so nice.
       Also see http://stackoverflow.com/q/39459854/946226  *)
    typing_let.hyps(4)[of _ "(x, T1) # G1" for x, simplified]
  
  from typing_let.prems
  show ?case by (auto intro!: typing.typing_let IH)
qed (auto intro: typing.intros)

(*
Lemma decomposition : forall e' e G x T',
    typing G ([ x ~> e ] e') T'->
    forall T, uniq ((x ~ T) ++ G) -> typing G e T -> typing ((x ~ T) ++ G) e' T'. 
*)

lemma binds_add_inbetween:
  assumes "x \<noteq> y"
  assumes "binds y T' (G1 @ G2)"
  shows   "binds y T' (G1 @ (x ~ T) @ G2)"
using assms by auto

lemma decomposition_general:
  assumes "typing (G1 @ G2) ([ x \<leadsto> u ] e') T'"
  assumes "uniq (G1 @ (x ~ T) @ G2)"
  assumes "typing (G1 @ G2) u T"
  shows "typing (G1 @ (x ~ T) @ G2) e' T'"
using assms
proof(induction "G1 @ G2" "[ x \<leadsto> u ] e'" T' arbitrary: G1 e' rule:typing.induct)
case (typing_var y T' G1 e')
  from `exp_fvar y = [x \<leadsto> u]e'`
  show "typing (G1 @ (x ~ T) @ G2) e' T'"
  proof(cases rule: subst_fvarE)
    assume "e' = exp_fvar y" and "x \<noteq> y"
    from this(2) and `binds y T' (G1 @ G2)`
    have "binds y T' (G1 @ (x ~ T) @ G2)" by (rule binds_add_inbetween)
    with  `uniq (G1 @ (x ~ T) @ G2)`
    show ?case unfolding `e' = _`  by (rule typing.intros)
  next
    assume "e' = exp_fvar x" and "u = exp_fvar y"

    from `uniq (G1 @ G2)`  `binds y T' (G1 @ G2)`
    have "typing (G1 @ G2) u T'"unfolding `u = _`  by (auto  intro: typing.intros)
    with `typing (G1 @ G2) u T`
    have "T = T'"  by (rule unicity)

    from  `uniq (G1 @ (x ~ T) @ G2)`
    show ?case
      unfolding `e' = _` \<open>T = T'\<close>
      by (rule typing.intros) simp
   qed
next
  case (typing_let e1 T1 L e2 T2 G1 e')
  from `exp_let e1 e2 = [x \<leadsto> u]e'`
  show ?case
  proof(cases rule: subst_letE)
    fix e\<^sub>1' e\<^sub>2'
    assume [simp]: "e' = exp_let e\<^sub>1' e\<^sub>2'" "e1 = [x \<leadsto> u]e\<^sub>1'" "e2 = [x \<leadsto> u]e\<^sub>2'"

    note IH =
      typing_let.hyps(4)[of _ "(x, T1) # G1" "open e\<^sub>2' (exp_fvar x)" for x, simplified]

    from `typing (G1 @ G2) u T`
    have [simp]: "lc u" by (rule typing_lc)
    
    from typing_let.hyps(2) typing_let.prems(1,2)
    show ?case
      apply (auto intro!: typing.typing_let[where L = "L |\<union>| {|x|} |\<union>| fv u |\<union>| fv e\<^sub>2' |\<union>| fdom G1 |\<union>| fdom G2" ])
      apply (auto intro!: IH intro: typing_weakening_one_from)
      done
  next
    assume "e' = exp_fvar x" and "u = exp_let e1 e2"

    from typing_let.hyps(1,3)
    have "typing (G1 @ G2) u T2"
      unfolding `u = _` by (auto intro!:  typing.typing_let)
    with `typing (G1 @ G2) u T`
    have "T = T2" by (rule unicity)

    from  `uniq (G1 @ (x ~ T) @ G2)`
    show ?case
      unfolding `e' = _` \<open>T = T2\<close>
      by (rule typing.intros) simp
  qed
qed (auto intro: typing.intros elim!: typing_elims elim!: subst.elims[OF sym] split: if_splits)


lemma decomposition:
  assumes "typing G ([ x \<leadsto>  e ] e') T'"
  assumes "uniq ((x ~ T) @ G)"
  assumes "typing G e T"
  shows "typing ((x ~ T) @ G) e' T'"
using decomposition_general[of "[]", unfolded append_Nil] assms.

(*
Lemma typing_uniq : forall E e T,
  typing E e T -> uniq E.
*)
lemma typing_uniq:
  assumes "typing E e T"
  shows "uniq E"
using assms by (rule typing.induct)

(*
Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv e -> y `notin` (dom E `union` fv e) ->
  typing ((x ~ T1) ++ E) (open e (exp_fvar x)) T2 ->
  typing ((y ~ T1) ++ E) (open e (exp_fvar y)) T2.
*)
lemma typing_rename:
  assumes "x |\<notin>| fv e"
  assumes "y |\<notin>| fdom E |\<union>| fv e"
  assumes "typing ((x ~ T1) @ E) (open e (exp_fvar x)) T2"
  shows   "typing ((y ~ T1) @ E) (open e (exp_fvar y)) T2"
proof(cases "x = y")
case True
  from assms(3)
  show ?thesis unfolding \<open>x=y\<close>.
next
  assume [simp]: "x\<noteq>y"
  
  from assms(3) have "uniq ((x ~ T1) @ E)" by (rule typing_uniq)
  with assms(2)
  have "uniq ((x ~ T1) @ (y ~ T1) @ E)" by auto

  with \<open>typing ((x ~ T1) @ E) (open e (exp_fvar x)) T2\<close>
  have "typing ((x ~ T1) @ (y ~ T1) @ E) (open e (exp_fvar x)) T2"
    by (rule typing_weakening_strengthened)
  moreover
  have "uniq ((y ~ T1) @ E)" using `uniq ((x ~ T1) @ (y ~ T1) @ E)` by auto
  hence "typing ((y ~ T1) @ E) (exp_fvar y) T1" by rule auto
  ultimately
  have "typing ((y ~ T1) @ E) [x \<leadsto> exp_fvar y](open e (exp_fvar x)) T2"
    by (rule typing_subst_simple)
  also have "[x \<leadsto> exp_fvar y](open e (exp_fvar x)) = open e (exp_fvar y)"
    using assms(1) by (rule subst_intro)
  finally show ?thesis.
qed
    
(*
Lemma typing_let_exists : forall x (E : env) (e1 e2 : exp) (T1 T2 : typ),
       typing E e1 T1 
       -> x `notin` fv e2
       -> typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2 
       -> typing E (exp_let e1 e2) T2.
*)
lemma typing_let_exists:
  assumes "typing E e1 T1"
  assumes "x |\<notin>| fv e2"
  assumes "typing ((x ~ T1) @ E) (open e2 (exp_fvar x)) T2"
  shows "typing E (exp_let e1 e2) T2"
proof(rule typing.typing_let)
  show "typing E e1 T1" by fact
next
  fix y
  assume "y |\<notin>| fdom E |\<union>| fv e2"
  from assms(2) this assms(3)
  have "typing ((y ~ T1) @ E) (open e2 (exp_fvar y)) T2" by (rule typing_rename)
  thus "typing ((y, T1) # E) (open e2 (exp_fvar y)) T2" by simp
qed

(*
Lemma typing_let_inversion : forall (E : env) (e1 e2 : exp) (T2 : typ),
    typing E (exp_let e1 e2) T2
    -> (exists T1, typing E e1 T1 /\
      (forall x,  x `notin` (fv e2 \u dom E)
       -> typing ((x ~ T1) ++ E) (open e2 (exp_fvar x)) T2)).
*)
lemma typing_let_inversion:
  assumes "typing E (exp_let e1 e2) T2"
  obtains T1 where
    "typing E e1 T1" and "\<And>x. x |\<notin>| fdom E |\<union>| fv e2  \<Longrightarrow> typing ((x ~ T1) @ E) (open e2 (exp_fvar x)) T2"
proof-
  from assms
  obtain T1 L where "typing E e1 T1" and hyp: "\<And>x. x |\<notin>| L \<Longrightarrow>  typing ((x, T1)#E) (open e2 (exp_fvar x)) T2"
    by (rule typing_elims) rule
  show ?thesis
  proof(rule that)
    show "typing E e1 T1" by fact
  next
    fix x
    assume "x |\<notin>| fdom E |\<union>| fv e2"
    obtain y where "y |\<notin>| L |\<union>| fv e2" by (rule have_fresh_atom)
    hence "y |\<notin>| L" and "y |\<notin>|  fv e2" by simp_all
    from this(1) 
    have "typing ((y, T1)#E) (open e2 (exp_fvar y)) T2" by (rule hyp)
    hence "typing ((y ~ T1)@E) (open e2 (exp_fvar y)) T2" by simp
    with \<open>y |\<notin>| fv e2\<close> \<open>x |\<notin>| fdom E |\<union>| fv e2\<close>
    show "typing ((x ~ T1)@E) (open e2 (exp_fvar x)) T2" by (rule typing_rename)
  qed
qed

end