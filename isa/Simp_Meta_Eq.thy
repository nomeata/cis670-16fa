theory Simp_Meta_Eq imports Main
begin

(* Stolen and adapted from induct.ML, as advised by Andreas Lochbihler on
  http://stackoverflow.com/a/39464146/946226 *)

ML \<open>
fun swap_params_conv ctxt i j cv =
  let
    fun conv1 0 ctxt = Conv.forall_conv (cv o snd) ctxt
      | conv1 k ctxt =
          Conv.rewr_conv @{thm swap_params} then_conv
          Conv.forall_conv (conv1 (k - 1) o snd) ctxt;
    fun conv2 0 ctxt = conv1 j ctxt
      | conv2 k ctxt = Conv.forall_conv (conv2 (k - 1) o snd) ctxt;
  in conv2 i ctxt end;

fun swap_prems_conv 0 = Conv.all_conv
  | swap_prems_conv i =
      Conv.implies_concl_conv (swap_prems_conv (i - 1)) then_conv
      Conv.rewr_conv Drule.swap_prems_eq;

fun dest_def (Const (@{const_name HOL.eq}, _) $ t $ u) = SOME (t, u)
  | dest_def _ = NONE

fun find_eq ctxt t =
  let
    val l = length (Logic.strip_params t);
    val Hs = Logic.strip_assums_hyp t;
    fun find (i, t) =
      (case dest_def (Object_Logic.drop_judgment ctxt t) of
        SOME (Bound j, _) => SOME (i, j)
      | SOME (_, Bound j) => SOME (i, j)
      | _ => NONE);
  in
    (case get_first find (map_index I Hs) of
      NONE => NONE
    | SOME (0, 0) => NONE
    | SOME (i, j) => SOME (i, l - j - 1, j))
  end;

fun mk_swap_rrule ctxt ct =
  (case find_eq ctxt (Thm.term_of ct) of
    NONE => NONE
  | SOME (i, k, j) => SOME (swap_params_conv ctxt k j (K (swap_prems_conv i)) ct));
\<close>

simproc_setup rearrange_eqs ("Pure.all(t)") = "fn _ => fn ctxt => fn ct => mk_swap_rrule ctxt ct"

lemma one_point_rule[simp]:
  "(\<And> x. y = x \<Longrightarrow> PROP P x) \<equiv> PROP P y"
  apply (rule)
  apply (auto)
  apply (erule meta_allE)
  apply (erule meta_impE)
  apply (rule refl)
  apply assumption
  done

end