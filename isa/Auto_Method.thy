theory Auto_Method
imports
  Main
  "~~/src/HOL/Eisbach/Eisbach"
keywords "auto_method" :: thy_decl
begin

ML \<open>
  fun auto_method method = (fn ctxt =>
    ctxt addSbefore ("TODO", fn ctxt => fn _ =>
      let 
      in  Method.NO_CONTEXT_TACTIC ctxt (method [])
      end
   ));

  fun auto_method_cmd method_text lthy = 
    let val ctxt = Local_Theory.target_of lthy
        val method = Method.evaluate method_text ctxt
    in Local_Theory.background_theory (map_theory_claset (auto_method method)) lthy
    end;

  Outer_Syntax.local_theory @{command_keyword "auto_method"} 
    "adds a method invocation to the classical reasoner"
    (Method.parse >> (fn (method_text, _) => auto_method_cmd method_text))
\<close>


consts P :: bool 
consts Q :: bool
lemma H1: "P \<Longrightarrow> Q" and H2: P sorry
method Q_method methods m = (match conclusion in "Q" \<Rightarrow> \<open>rule H1; m\<close>)


auto_method (Q_method \<open>rule H\<close>)
auto_method (Q_method \<open>rule H2\<close>)
lemma  "Q \<and> Q" by auto

(*
setup \<open>
let val my_auto_method =
  Scan.lift (Method.parse) >> (fn (method_text, _) => fn ctxt =>
    Method.evaluate method_text ctxt
  )
in  Method.setup @{binding my_auto} my_auto_method "my_auto"
end
\<close>

lemma "Q \<and> Q" by (my_auto (Q_method \<open>rule H2\<close>))
*)

end