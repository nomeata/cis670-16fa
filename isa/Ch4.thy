theory Ch4
imports
  Main
  "~~/src/HOL/Library/FSet"
begin

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
  thm lc_let.IH
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
  open ([x ~> u] e1) e2 = [x ~> u] (open e1 e2).
*)
lemma subst_open[simp]:
  assumes "lc u"
  shows "[x \<leadsto> u](open e\<^sub>1 e\<^sub>2) = open ([x \<leadsto> u] e\<^sub>1) ([x \<leadsto> u] e\<^sub>2)"
using assms by (auto simp add: open_def)


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
  thm lc_let.hyps
  thm lc_let.IH

  have "lc (exp_let [x \<leadsto> u]e\<^sub>1 [x \<leadsto> u]e\<^sub>2)"
  proof(rule lc.lc_let)
    show "lc [x \<leadsto> u]e\<^sub>1" by fact
  next
    fix y :: atom
    assume "y |\<notin>| L |\<union>| {| x |}"
    hence "y |\<notin>| L" by simp
    hence "lc [x \<leadsto> u](open e\<^sub>2 (exp_fvar y))" by (rule lc_let.IH)
    (* This is the step that is not clear to me why Coq does not need it. *)
    thus "lc (open [x \<leadsto> u]e\<^sub>2 (exp_fvar y))"
      using `y |\<notin>| L |\<union>| {| x |}` by auto
  qed
  thus ?case by simp
qed (auto intro!: lc.intros)


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

end