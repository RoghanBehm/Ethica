theory Modal
       imports Main
begin

(* isa-afp.org/thys/GoedelGod/GoedelGod.html*)

typedecl i                              \<comment> \<open>worlds\<close>
type_synonym \<sigma> = "i \<Rightarrow> bool"             \<comment> \<open>world-relative propositions\<close>
definition mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box>\<phi> \<equiv> \<lambda>_. \<forall>v. \<phi> v" (* true in all worlds *)
definition valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"
abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr \<open>m\<rightarrow>\<close> 74) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)" 
end
